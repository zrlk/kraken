/-
AArch64 emitter for `scc`.

Instruction selection for the `isaLSE2` target (FEAT_LSE2, `Arch.armv8`): the
helpers below produce Kraken AArch64 `Directive`s (as `Item`s of
`Scc/Emit/A64Print.lean`) in the canonical forms that round-trip through
Kraken's parser, and only in forms that `Program.WCLowerable`
(`Kraken/Promising/Lower/Lowerable.lean`) allows:

* acquire load = `ldar` (never `ldapr`, clause 4); release store = `stlr`;
* read-modify-write only as `casal`/`swpal`/`ld<op>al` with a real result
  register (clauses 2 and 3), at word or doubleword size (clause 6);
* no 64-bit `ldp`/`stp` anywhere (clause 1): frames are saved with single
  `str`/`ldr`;
* no sub-word store (clause 6): a byte or halfword write is a word load, a
  bitfield insert and a word store (`subWordStore`);
* no pair atomics (clause 5).

Register use is AAPCS64-like: arguments and results in `x0`–`x7`, `x8` the
system-call number, `x9`–`x15` caller-saved temporaries, `x16`/`x17` the
emitter's scratch registers, `x18` unused (platform register), `x19`–`x28`
callee-saved, `x29` frame pointer, `x30` link register. No register holds the
thread control block: the thread pointer is `TPIDR_EL0`, read with `mrs` and
set by `clone(CLONE_SETTLS)` or `msr` at start-up.

Obligations where WeakCore's `TermRun` is stricter than herd (keep them when
extending the table):

* a thread that re-reads the value its own RMW wrote and dereferences it needs
  the RMW in an `-al` form (`swpal`/`ldaddal`/`casal`), or a release write
  followed by an `ldar` re-read; never `ldapr` (the IR's `rmw` is always
  `swpal`/`ldaddal`);
* `spawn` is a full barrier on the parent: the lowering puts an IR
  `fence full` (`dmb ish`) before every `clone`;
* not in the fragment yet: a pair store needs `dmb ish` before the `stp` (and
  64-bit `stp` is excluded by clause 1 anyway), and `casPair` would be
  `caspal` (excluded by clause 5 until the pair findings are resolved).

System calls use `svc #0` with the number in `x8`; the thread pointer is
`TPIDR_EL0`, read with `mrs` and set with `msr`. All three are Kraken
instructions (`Operation.SVC`, `MRS`, `MSR`; `Kraken/SYSCALL.md`), so every
instruction of the emitted text is in the re-parsed program and the only raw
lines are assembler directives.

The emitter is not trusted: a certificate re-parses its text.
-/
import Scc.Emit.A64Func

namespace Scc.Emit.A64

section FromIR

/-- `--host raw`: the kernel routine trampolines, one per slot of
`Tcb.kabiSlots` in slot order, between the global labels `Tcb.kabiStartSym`
and `Tcb.kabiEndSym`. The trampoline `scc_rt_X` of slot `n` reads the TCB
(`mrs x16, tpidr_el0`), loads the routine table's address
(`ldr x16, [x16, #96]`, `Tcb.kabi`) and the slot (`ldr x16, [x16, #8n]`), and
branches to it (`br x16`): the routine returns to the trampoline's caller
(`x30`). `x16` (`scratch0`, IP0) is free at every call. -/
def kabiItems : List Item :=
  [.raw s!".globl {IR.Tcb.kabiStartSym}", lbl IR.Tcb.kabiStartSym] ++
  IR.Tcb.kabiSlots.flatMap (fun (f, n) =>
    [.raw s!".type {f}, %function", lbl f, readTp scratch0] ++
    ldrOff .W64 scratch0 (xs scratch0) IR.Tcb.kabi ++
    ldrOff .W64 scratch0 (xs scratch0) (8 * n) ++
    [tailReg scratch0, .raw s!".size {f}, .-{f}"]) ++
  [.raw s!".globl {IR.Tcb.kabiEndSym}", lbl IR.Tcb.kabiEndSym]

/-- **`--host raw`: the trampolines precede every block entry.** Every label of `its` before
`Tcb.kabiEndSym` is `scc_text_start`, `Tcb.kabiStartSym` or a trampoline's symbol: no
function or block label (no block entry of the tables) lies before the end of the
trampolines, which the tables reader's rule for them relies on (no block entry at or below
their addresses). Fails without `Tcb.kabiEndSym`. -/
def kabiFirst (its : List Item) : Except String Unit := do
  let ls := its.filterMap fun | .d (.label l) => some l | _ => none
  unless ls.contains IR.Tcb.kabiEndSym do throw s!"--host raw: no {IR.Tcb.kabiEndSym}"
  let ok := [IR.StackMap.textStartSym, IR.Tcb.kabiStartSym] ++ IR.Tcb.kabiSlots.map (·.1)
  match (ls.takeWhile (· != IR.Tcb.kabiEndSym)).find? (!ok.contains ·) with
  | some l => throw s!"--host raw: label {l} precedes {IR.Tcb.kabiEndSym}"
  | none => pure ()

/-- The items of a whole program from its functions' items and safepoints
`rs`, in order (`emitItemsMaps`): header, `_start` (a jump to
`Program.start`; `--host raw`: the kernel routine trampolines `kabiItems`
instead, the kernel enters `Program.start` itself), the functions, then the
data (and, with `IR.Program.growth`, the trampoline and the stack-map
table), and the safepoints in code order. -/
def emitPost (p : IR.Program) (rs : List (List Item × List Safepoint)) :
    Except String (List Item × List Safepoint) := do
  let fs := rs.flatMap (·.1)
  let sps := rs.flatMap (·.2)
  -- `.data` and `.bss` start 16-aligned (`Data.Secs.ofProgram`).
  let mut ds : List Item := [.raw ".data", .raw ".balign 16", .raw ".bss", .raw ".balign 16"]
  for d in p.data do
    ds := ds ++ (← emitData d)
  let (ms, tab) := match p.growth with
    | some g => (morestack g, mapItems sps)
    | none => ([], [])
  -- `.p2align 4` first in `.text`: it pads nothing (offset 0) but makes the
  -- section 16-aligned, so a linker places the code on a 16-byte boundary
  -- whatever precedes it (the placement check requires one).
  let head : List Item := match p.host with
    | .linux => [.comment "generated by scc (arm: AArch64 FEAT_LSE2, Linux)",
        .raw ".arch armv8.4-a", .raw ".text", .raw ".globl _start", .raw ".p2align 4",
        lbl IR.StackMap.textStartSym, lbl "_start", jmp p.start]
    -- the entry is global (the kernel and the link find it by name); the functions are not
    | .raw => [.comment "generated by scc (arm: AArch64 FEAT_LSE2, raw ABI)",
        .raw ".arch armv8.4-a", .raw ".text", .raw s!".globl {p.start}", .raw ".p2align 4",
        lbl IR.StackMap.textStartSym] ++ kabiItems
  return (head ++ fs ++ ms ++ [lbl IR.StackMap.textEndSym] ++ ds ++ tab, sps)

/-- The items of a whole program and its safepoints in code order: the
checks (`emitPre`), each function (`emitFuncAt`), then the rest
(`emitPost`). A certificate checks the three parts separately
(`emitItemsMaps_of_stages`). -/
def emitItemsMaps (p : IR.Program) : Except String (List Item × List Safepoint) := do
  let areas ← emitPre p
  let rs ← p.funcs.zipIdx.mapM (emitFuncAt p areas)
  emitPost p rs

/-- **`emitItemsMaps` from its stages**: the checks give the argument areas
`areas`, the functions their items and safepoints `rs`, and the rest the
result. A certificate checks the checks, each function and the rest in
their own kernel runs, and chains the functions
(`Scc.Cert.OutLit.mapM_ok_cons`). -/
theorem emitItemsMaps_of_stages {p : IR.Program} {areas : List (IR.Sym × Nat)}
    {rs : List (List Item × List Safepoint)} {r : List Item × List Safepoint}
    (h1 : emitPre p = .ok areas) (h2 : p.funcs.zipIdx.mapM (emitFuncAt p areas) = .ok rs)
    (h3 : emitPost p rs = .ok r) : emitItemsMaps p = .ok r := by
  unfold emitItemsMaps
  rw [h1]
  show (p.funcs.zipIdx.mapM (emitFuncAt p areas) >>= emitPost p) = _
  rw [h2]
  exact h3

/-- The items of a whole program (`emitItemsMaps`). -/
def emitItems (p : IR.Program) : Except String (List Item) :=
  (·.1) <$> emitItemsMaps p

/-- The data sections of a program's assembler text as data images
(`Scc.Emit.Data`): what `emitData` and `mapItems` write. -/
def dataSecs (p : IR.Program) : Except String Data.Secs := do
  let (_, sps) ← emitItemsMaps p
  pure (Data.Secs.ofProgram p.data (if p.growth.isSome then some sps else none))

/-- The assembler text of a whole program. -/
def emitProgram (p : IR.Program) : Except String String := do
  render (← emitItems p)

end FromIR

end Scc.Emit.A64

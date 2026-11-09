import Scc.Lower.Raw
import Scc.Emit.X64
import Scc.Lower.SpecX64
import Scc.Cert.MapsCheckX64
import Scc.Test.Src

/-!
# Tests of the `--host raw` emission, x86-64 (`Scc.Emit.X64.emitKabi`)

On `hello1.w` and `hello.w`, the text of the raw program
(`Lower.lowerIRHost` with `host := .raw`):

* starts with `scc_text_start`, then the kernel routine trampolines, one per slot of
  `Tcb.kabiSlots` in slot order, between `scc_kabi_start` and `scc_kabi_end`; no `_start`, and no
  system call instruction anywhere;
* re-parses with Kraken's parser (every item);
* has the Linux text of every function the raw lowering leaves unchanged (all of `hello1.w`'s
  user functions, and `hello.w`'s but the spawning `wc_main`) and of `scc_rt_morestack`;
* passes the tables check (`MapsX64.checkTables`), and its trampolines
  precede every block entry of the tables (`scc_kabi_end` at or before the first);
* an indirect jump (`jmp *mem`) is classified only between `scc_kabi_start`
  and `scc_kabi_end`: in a function body the tables refuse it.
-/

namespace Scc.Test.RawEmitX64

open Scc.IR

/-- The Linux and the raw IR of a WeakCore source for `arch`. -/
def irs (arch : Arch) (src : String) : Except String (IR.Program × IR.Program) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  let l ← Lower.lowerIRHost { arch } c.prog
  let r ← Lower.lowerIRHost { arch, host := .raw } c.prog
  pure (l.ir, r.ir)

def hello1Src : String := w_src% "Scc/Test/hello1.w"
def helloSrc : String := w_src% "Scc/Test/hello.w"

/-! ## x86-64 -/

namespace X

open Scc.Emit.X64

/-- The IR and the emitted items and safepoints of the Linux and the raw program. -/
def emitted (src : String) :
    Except String ((IR.Program × List Item × List Map) × (IR.Program × List Item × List Map)) := do
  let (l, r) ← irs .x64 src
  let (li, lm) ← emitItemsMaps l
  let (ri, rm) ← emitItemsMaps r
  pure ((l, li, lm), (r, ri, rm))

def hello1 := emitted hello1Src
def hello := emitted helloSrc

/-- The text items: up to `scc_text_end`. -/
def textOf (its : List Item) : List Item :=
  its.takeWhile fun | .d (.label l) => l != StackMap.textEndSym | _ => true

/-- The text's items per routine: from each `.type f, @function` line up to the next. -/
def routines (its : List Item) : List (String × List Item) :=
  (textOf its).foldl (fun acc it => match it with
    | .dir s => match Scc.Cert.MapsX64.typeOf? s with
      | some f => acc ++ [(f, [it])]
      | none => match acc.getLast? with
        | some (g, xs) => acc.dropLast ++ [(g, xs ++ [it])]
        | none => acc
    | _ => match acc.getLast? with
      | some (g, xs) => acc.dropLast ++ [(g, xs ++ [it])]
      | none => acc) []

/-- The labels of the text, in order. -/
def labels (its : List Item) : List String :=
  (textOf its).filterMap fun | .d (.label l) => some l | _ => none

/-- The raw text's head: `scc_text_start`, `scc_kabi_start`, then each trampoline's symbol in slot
order, then `scc_kabi_end`, then the first function. -/
def headOk (its : List Item) (first : String) : Bool :=
  (labels its).take (Tcb.kabiSlots.length + 4) ==
    [StackMap.textStartSym, Tcb.kabiStartSym] ++ Tcb.kabiSlots.map (·.1) ++ [Tcb.kabiEndSym, first]

/-- No `_start` and no `syscall` in the text. -/
def noStartNoSys (its : List Item) : Bool :=
  !(labels its).contains "_start" &&
    (textOf its).all fun | .d (.instr (.regular _ _ .syscall)) => false | _ => true

/-- The routines both texts have but the trampolines (on Linux the runtime's functions), with
the names of those whose items differ. -/
def differing (l r : List Item) : List String :=
  let lr := routines l
  (routines r).filterMap fun (f, xs) => if Tcb.kabiSlots.any (·.1 == f) then none else
    match lr.lookup f with
    | some ys => if xs.map (·.line?) == ys.map (·.line?) then none else some f
    | none => none

/-- The first block entry of the raw text's tables is at or after `scc_kabi_end`. -/
def kabiFirst (p : IR.Program) (its : List Item) : Bool :=
  let sizes := Scc.Cert.MapsX64.unitSizes its
  match Scc.Cert.MapsX64.itemsOf its sizes, Scc.Cert.MapsX64.computeX64 p its sizes with
  | .ok items, .ok t =>
    match Scc.Cert.Maps.labelAddr items Tcb.kabiEndSym,
        (t.maps.filter (·.pt.kind == .blockEntry)).head? with
    | some e, some m => e ≤ m.pt.addr
    | _, _ => false
  | _, _ => false

/-- The facts of the module docstring for one source, `same`: the routines whose items must be
the Linux ones. -/
def allOk (r : Except String ((IR.Program × List Item × List Map) × (IR.Program × List Item × List Map)))
    (same : List String) : Bool :=
  match r with
  | .ok ((_, li, _), (rp, ri, rm)) =>
    headOk ri "scc_rt_main" && noStartNoSys ri && ri.all (·.roundTrips) &&
      same.all (fun f => ((routines ri).lookup f).map (·.map (·.line?)) == ((routines li).lookup f).map (·.map (·.line?)) &&
        ((routines ri).lookup f).isSome) &&
      (Scc.Cert.MapsX64.checkTables { arch := .x64, host := .raw } rp ri rm).toOption.isSome &&
      kabiFirst rp ri
  | .error _ => false

end X

-- The first two trampolines (x86-64).
/--
info: scc_text_start:
scc_kabi_start:
scc_rt_alloc:
	movq %fs:96, %r11
	jmp *(%r11)
scc_rt_alloc_tcb:
	movq %fs:96, %r11
	jmp *8(%r11)
-/
#guard_msgs in
#eval match X.hello1 with
  | .ok (_, (_, ri, _)) =>
    let ds := ((X.textOf ri).filter fun (it : Scc.Emit.X64.Item) => match it with | .d _ => true | _ => false).take 8
    IO.println (String.intercalate "\n" (ds.filterMap Scc.Emit.X64.Item.line?))
  | .error e => IO.println e

-- Every routine but the spawning `wc_main` is the Linux one; the trampolines and `scc_rt_main`
-- and the thread entries are the raw program's own.
/-- info: ["scc_rt_main"] -/
#guard_msgs in
#eval match X.hello1 with
  | .ok ((_, li, _), (_, ri, _)) => X.differing li ri
  | .error e => [e]
/-- info: ["scc_rt_main", "scc_rt_thr_worker", "wc_main"] -/
#guard_msgs in
#eval match X.hello with
  | .ok ((_, li, _), (_, ri, _)) => X.differing li ri
  | .error e => [e]

-- The spawn's fence (the lowering's, `Lower.Raw.rawInsts`): `wc_main` has exactly one `mfence`,
-- and every instruction between it and `call scc_rt_spawn` is one of the call's argument moves:
-- a load of a frame slot or an immediate into `%rax` or an argument register, or a store of
-- `%rax` to the outgoing area (`(%rsp)` offsets). The entry's address is taken before the fence.
-- Anything else fails.
namespace X
/-- The registers an argument move may write. -/
def moveRegs : List String := ["%rax", "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"]
/-- Whether line `l` is one of the spawn call's argument moves. -/
def argMove (l : String) : Bool :=
  (l.startsWith "\tmovq -" && moveRegs.any (fun r => l.endsWith s!"(%rbp), {r}")) ||
  (l.startsWith "\tmovq $" && moveRegs.any (fun r => l.endsWith s!", {r}")) ||
  (l.startsWith "\tmovq %rax, " && l.endsWith "(%rsp)")
/-- The number of `mfence`s of `ls`, the lines between the first and `call scc_rt_spawn` that
are not argument moves, and whether the call follows. -/
def fenceGap (ls : List String) : Nat × List String × Bool :=
  let after := (ls.dropWhile (· != "\tmfence")).drop 1
  let gap := after.takeWhile (· != "\tcall scc_rt_spawn")
  ((ls.filter (· == "\tmfence")).length,
   gap.filter (!argMove ·),
   gap.length < after.length)
/-- The lines of the raw `wc_main` of hello. -/
def mainLines : List String :=
  match hello with
  | .ok (_, (_, ri, _)) =>
    (((routines ri).lookup "wc_main").getD []).filterMap fun (it : Scc.Emit.X64.Item) =>
      match it with
      | .d (.label _) => none
      | it => it.line?
  | .error e => [e]
end X

/-- info: (1, [], true) -/
#guard_msgs in
#eval X.fenceGap X.mainLines
-- Any other instruction between the fence and the call fails: a store through a pointer, the
-- entry's address, or a store to a frame slot.
#guard ["\tmovq %rax, 8(%rbx)", "\tleaq scc_rt_thr_worker(%rip), %rax", "\tmovq %rax, -80(%rbp)"].all
  fun bad => (X.fenceGap (X.mainLines.flatMap fun l =>
    if l == "\tmfence" then [l, bad] else [l])).2.1 == [bad]

-- `--host raw` refuses a text with a block entry before `scc_kabi_end`
-- (`Scc.Emit.X64.kabiFirst`, checked by `Lower.X64.Emitted.listing`, so on every raw compile).
namespace X
/-- `its` with a function's block label right after `scc_kabi_start`. -/
def earlyBlock (its : List Scc.Emit.X64.Item) : List Scc.Emit.X64.Item :=
  its.flatMap fun it => match it with
    | .d (.label l) => if l == IR.Tcb.kabiStartSym then [it, .d (.label ".L0_wc_main.0_entry")] else [it]
    | _ => [it]
/-- The raw `Emitted` of hello1. -/
def hello1E : Except String Lower.X64.Emitted := do
  let c ← match Frontend.run hello1Src with
    | .ok c => pure c
    | .error _ => throw "frontend error"
  Lower.X64.emitAll (← Lower.lowerIRHost { arch := .x64, host := .raw } c.prog)
end X

#guard match X.hello1 with
  | .ok (_, (_, ri, _)) => (Scc.Emit.X64.kabiFirst ri).toOption.isSome
  | .error _ => false
/-- info: "--host raw: label .L0_wc_main.0_entry precedes scc_kabi_end" -/
#guard_msgs in
#eval match X.hello1 with
  | .ok (_, (_, ri, _)) => match Scc.Emit.X64.kabiFirst (X.earlyBlock ri) with
    | .ok _ => "accepted" | .error e => e
  | .error e => e
-- Without `scc_kabi_end` at all: refused.
#guard match X.hello1 with
  | .ok (_, (_, ri, _)) => (Scc.Emit.X64.kabiFirst (ri.filter fun it => match it with
      | .d (.label l) => l != IR.Tcb.kabiEndSym | _ => true)).toOption.isNone
  | .error _ => false
-- The listing: the raw program's is printed; with the early block label it is refused.
#guard match X.hello1E with
  | .ok e => e.listing.toOption.isSome && ({ e with items := X.earlyBlock e.items }).listing.toOption.isNone
  | .error _ => false

#guard X.allOk X.hello1 ["wc_rodata", "wc_main", IR.StackMap.morestackSym]
#guard X.allOk X.hello ["wc_rodata", "wc_worker", "wc_waitLoop", IR.StackMap.morestackSym]

-- The trampolines' `jmp *8n(%r11)` is classified only in `[scc_kabi_start, scc_kabi_end)`: the
-- same jump right after `scc_rt_main`'s symbol leaves the text unclassified.
open Scc.Emit.X64 in
#guard match X.hello1 with
  | .ok (_, (_, ri, _)) =>
    let jm : Item := .d (i64 (.jmp (.mem (mem .r11 8))))
    let ins := ri.flatMap fun it => match it with
      | .d (.label "scc_rt_main") => [it, jm]
      | _ => [it]
    ins.length == ri.length + 1 &&
      (Scc.Cert.MapsX64.itemsOf ri (Scc.Cert.MapsX64.unitSizes ri)).toOption.isSome &&
      (Scc.Cert.MapsX64.itemsOf ins (Scc.Cert.MapsX64.unitSizes ins)).toOption.isNone
  | .error _ => false

end Scc.Test.RawEmitX64

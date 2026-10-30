import Scc.Frontend
import Scc.Lower.Program
import Scc.Emit.A64
import Scc.Test.Src
import Scc.Sem.Test.RunA64

/-!
# Certification through the take site: the limbo promises

This file is evidence for a gap in the certification semantics of the
canonical AArch64 target (`Kernel.certExec`). The emitted programs are
`Spike/Gen/ret0.w` and `Scc/Test/hello1.w`, the one-thread programs of the M1
statement. Their runs are reachable on `target (kernel 2) Entry.linux`.

`Kernel.certExec` is the ISA's `exec` everywhere except at a system call. A
certification run therefore passes the take site (`scc_rt_take_site`, a
`nop`) as an instruction, not as the take. It continues in a state no real
run reaches: the pc is past the `nop`, but the stack range is *not* in the
thread's private memory. From there it returns into `scc_rt_start`, moves
`sp` onto the range, and runs `main`'s prologue. Its frame stores leave
private memory and become shared messages in the stack pool. So a thread at
the take site may promise writes to the stack pool, which no real run makes.

* **Block 1** (the current semantics): at the take mark of each program, the
  deterministic run's thread certifies (Kraken's `certifiedPromisesWith`,
  fuel 60) nine writes. Three of them are in `Λ.stackPool`: two words of
  `main`'s frame record and one spilled pointer.
* **Block 2** (the phase witness): the consumer's take phase
  `Tk s := every aligned word of rS is mapped in dmem` (the private-memory
  half of `Owned`) checked along the real run. `rS` is the range the take
  site names. Before the take, `Tk` is false at every state of the run,
  every one of them is off the stack pool's words, and the site is a `nop`
  naming a nonempty range in the pool. Just after the take `Tk` holds, and
  it holds at every later state to the exit. In particular no instruction
  and no system call of the run changes `Tk` but the take, which is the
  satisfiability check of the consumer's `TakePath` fields (`site`;
  `instr` off the transfer sites; `sys`; `owned`) on a concrete run.

* **Block 3** (the solo projection, `Kernel.certSem`): certification
  takes each kernel step of the thread run alone, so at the take site it
  takes the take itself (`Kernel.soloExec`). At the same take mark thread 0
  certifies six writes (fuel 60), every one in shared memory (`.data`, the
  heap or the pinned region) and none in the stack pool. The set is nonempty,
  so the projection still lets the thread promise (it is not a dead end at
  the site). For `ret0` it is also the whole set: at fuel 120 the search
  ends below the bound with the same six writes. Under the old semantics the
  set grows with the fuel instead: at fuel 120 `ret0` certifies 13 writes,
  7 in the pool, and `hello1` 17, 11 in the pool (not guarded here: the
  search takes minutes).

The x64 counterpart is `Spike/Test/X64TakeLimbo.lean`.
-/

namespace Scc.Test.TakeLimbo

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Test Scc.Sem.Test.RunA64

/-- scc's A64 listing of a source text. -/
def listing (src : String) : String :=
  match (do
      let c ← match Frontend.run src with
        | .ok c => pure c
        | .error _ => throw "frontend"
      let ir ← Lower.lowerProgram { arch := .arm } c
      Emit.A64.emitProgram ir : Except String String) with
  | .ok s => s
  | .error _ => ""

/-- The listings of `ret0.w` and `hello1.w`. -/
def ret0 : String := listing (w_src% "Spike/Gen/ret0.w")
def hello1 : String := listing (w_src% "Scc/Test/hello1.w")

/-- The configuration of the deterministic run of `asm` at its first state
whose thread 0 is at the take mark, with the layout and the marks. -/
def atTake (asm : String) :
    Option (Scc.Sem.Layout × RunMarks × (Kraken.Promising.Config isaLSE2 × Kernel.KState) × Nat) :=
  let prog := progOf asm
  let μ := marksIn prog
  let Λ := (layoutIn asm prog).1
  ((target (kernel slots) Entry.linux).load asm Λ).bind fun c =>
    let r := runUntil abi Arch.armv8 pcOf μ
      (fun c => c.1.threads[0]?.any fun t => some (pcOf t.st) == μ.take) 4000 0 { cfg := c }
    if r.stop == "condition" then some (Λ, μ, r.cfg, r.steps) else none

/-- **Block 1**: the writes thread 0 may promise at the take mark under
`Kernel.certExec` (fuel 60), as (address, value), and those in the stack
pool. -/
def limbo (asm : String) : Option (Nat × List (Nat × Nat)) :=
  (atTake asm).map fun (Λ, _, c, _) =>
    let ps := (certifiedPromisesWith Arch.armv8 (Kernel.certExec abi) {} c.1 0 60).1
    let ws := ps.filterMap fun (c', _) => c'.mem.msgs.back?.map fun m => (m.loc.addr.toNat, m.val.toNat)
    (ws.length, ws.filter fun (a, _) => Λ.stackPool.contains a)

/-- info: (some (9, [(268451824, 0), (268451832, 4194420), (268451792, 134217736)]),
  some (9, [(268451824, 0), (268451832, 4194420), (268451760, 134217736)])) -/
#guard_msgs in
#eval (limbo ret0, limbo hello1)

/-- The take phase of state `s` for range `rS`: every aligned word of `rS`
is mapped in the private memory. -/
def tk (rS : Range) (s : State) : Bool :=
  (List.range (rS.size / 8)).all fun i => (privLoad s (BitVec.ofNat 64 (rS.lo + 8 * i))).isSome

/-- The states of thread 0 along the deterministic run of `asm`, up to the
exit (at most `fuel` steps). -/
def states (asm : String) (fuel : Nat) : List State :=
  let prog := progOf asm
  let μ := marksIn prog
  let Λ := (layoutIn asm prog).1
  match (target (kernel slots) Entry.linux).load asm Λ with
  | none => []
  | some c =>
    let rec go : Nat → (Kraken.Promising.Config isaLSE2 × Kernel.KState) → List State
      | 0, _ => []
      | n + 1, c =>
        match c.1.threads[0]? with
        | none => []
        | some t =>
          if c.2.exited.isSome then [] else
          t.st :: match stepOf abi Arch.armv8 pcOf μ 0 c with
            | .ok (_, c') => go n c'
            | .error _ => []
    go fuel c

/-- **Block 2**: at the take mark (step `k`), the range `rS` the site names,
in the pool and nonempty, at a `nop` off a system call; `Tk` false at
every state of the run up to the take and true at every state after it; the
number of states before and after. -/
def phase (asm : String) : Option (Nat × Range × Bool × Bool × Bool × Nat × Nat) :=
  (atTake asm).bind fun (Λ, _, c, k) =>
    (c.1.threads[0]?).map fun t =>
      let rS := Kernel.siteRange abi t.st
      let ss := states asm 4000
      let pre := ss.take k
      let post := ss.drop (k + 1)
      (k, rS, rS.lo ≥ Λ.stackPool.lo && rS.lo + rS.size ≤ Λ.stackPool.lo + Λ.stackPool.size && 0 < rS.size &&
          atNop t.st && !abi.atSys t.st,
        pre.all (fun s => !tk rS s) && !tk rS t.st,
        post.all (tk rS),
        pre.length, post.length)

/-- info: (some (214, { lo := 268435456, size := 16384 }, true, true, true, 214, 79),
 some (214, { lo := 268435456, size := 16384 }, true, true, true, 214, 302)) -/
#guard_msgs in
#eval (phase ret0, phase hello1)

/-- **Block 3**: the writes thread 0 may promise at the take mark under
`Kernel.certSem` (fuel `fuel`), as (address, value); those outside shared
memory; those in the stack pool; whether the bound was hit. -/
def solo (asm : String) (fuel : Nat) :
    Option (List (Nat × Nat) × List (Nat × Nat) × List (Nat × Nat) × Bool) :=
  (atTake asm).bind fun (Λ, μ, c, _) =>
    (promisable Arch.armv8 (Kernel.certSem abi Arch.armv8 μ.marks c.2 0) c.1 0 fuel).map fun (ws, hit) =>
      (ws, ws.filter (fun (a, _) => !(Λ.data.contains a || Λ.heap.contains a || Λ.pinned.contains a)),
        ws.filter (fun (a, _) => Λ.stackPool.contains a), hit)

/-- info: (some
    ([(134217736, 134217736), (134217744, 268439552), (134217752, 0), (134217760, 0), (134217768, 268435456),
        (134217776, 268451840)],
      [], [], true),
  some
    ([(134217736, 134217736), (134217744, 268439552), (134217752, 0), (134217760, 0), (134217768, 268435456),
        (134217776, 268451840)],
      [], [], true)) -/
#guard_msgs in
#eval (solo ret0 60, solo hello1 60)

-- The projection is not a dead end at the take site: each program
-- certifies some write there.
#guard [ret0, hello1].all fun a => (solo a 60).any (0 < ·.1.length)

-- `ret0` at fuel 120: the same six writes, and the search ends below the
-- bound.
#guard (solo ret0 120).map (fun r => (r.1.length, r.2.2.2)) == some (6, false)

end Scc.Test.TakeLimbo

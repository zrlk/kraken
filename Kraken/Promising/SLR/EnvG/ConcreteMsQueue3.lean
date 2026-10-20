/-
Part 8: **concrete instance of
`MsQueue.msqueue3_envG`** (non-vacuity of its start hypotheses).
- Layouts: the enqueuer is laid out at `0x100000` for thread `0`, the first
  dequeuer at `0x200000` for thread `1`, the second at `0x300000` for thread
  `2`. Each directive gets its `fakeSize`, as the `.kl` runner lays out text.
- Addresses are msqueue2's: `head` at `0x1000`, `tail` at `0x1008`, `d` at
  `0x1100`, `n1` at `0x1200`, `n2` at `0x1300`.
- Every hypothesis is discharged by `decide`, `rfl` or `simp` (no
  `native_decide`).
- `codeMatches`: the `.kl`'s `code` block parses to the `enq` label,
  `enq2Prog`, `nop`, the `deq1` label, `deqProg`, `nop`, the `deq2` label,
  `deqBProg`, `nop`.

-/
import Kraken.Promising.SLR.EnvG.MsQueue3Public
import Kraken.Promising.SLR.EnvG.ConcreteMsQueue2

namespace Kraken.Promising.SLR.EnvG.ConcreteMsQueue3

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.MsQueue
open Kraken.Promising.SLR.EnvG.ConcreteMsQueue2 (layout0 valid0 enq0 enq0_start headAddr tailAddr dAddr n1Addr
  n2Addr msqueue2InitMem)

/-! ## The layouts -/

/-- Thread `1`'s layout: the first dequeuer's text at `0x200000`. -/
@[reducible] def layoutA : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize deqProg

/-- Thread `2`'s layout: the second dequeuer's text at `0x300000`. -/
@[reducible] def layoutB : _root_.Layout := Kraken.Layout.ofSize 0x300000 Directive.fakeSize deqBProg

instance validA : Executable.ValidLayout (layoutA deqProg) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance validB : Executable.ValidLayout (layoutB deqBProg) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The initial configuration -/

/-- Thread `1`'s initial state: `X0 = head`, `X1 = tail`, at the start of
`deqProg`, halting at the end of its text. -/
def deqA : AArch64.State where
  exe := layoutA deqProg
  endPc := 0x200000 + 72
  st := ({ regs := { X0 := 0x1000, X1 := 0x1008 } }, 0x200000)

/-- Thread `2`'s initial state: `X0 = head`, `X1 = tail`, at the start of
`deqBProg`, halting at the end of its text. -/
def deqB : AArch64.State where
  exe := layoutB deqBProg
  endPc := 0x300000 + 72
  st := ({ regs := { X0 := 0x1000, X1 := 0x1008 } }, 0x300000)

section
attribute [local instance] layoutA

theorem deqA_start : StartD headAddr tailAddr deqA := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [deqA, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] layoutB

theorem deqB_start : StartDB headAddr tailAddr deqB := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [deqB, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

theorem initV3 : InitV2 (Config.init [enq0, deqA, deqB] msqueue2InitMem : Config isa).mem
    ⟨⟨headAddr, tailAddr, dAddr, n1Addr⟩, n2Addr⟩ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def msqueue3Kl : String := include_str "../../../Examples/LockFree/AArch64/msqueue3.kl"

/-- The `code` block of the `.kl` parses to the `enq` label, `enq2Prog`,
`nop`, the `deq1` label, `deqProg`, `nop`, the `deq2` label, `deqBProg`,
`nop`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => (prog.drop 1).take enq2Prog.length == enq2Prog &&
        (prog.drop (enq2Prog.length + 3)).take deqProg.length == deqProg &&
        (prog.drop (enq2Prog.length + deqProg.length + 5)).take deqBProg.length == deqBProg &&
        prog.length == enq2Prog.length + deqProg.length + deqBProg.length + 6
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches msqueue3Kl

/-! ## The instance -/

/-- **`(1:X10 = 1 ∧ 2:X10 = 2) ∨ (1:X10 = 2 ∧ 2:X10 = 1)`** for
`msqueue3.kl` under `Arch.armv8`, concrete instance of `msqueue3_envG`. -/
theorem msqueue3_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enq0, deqA, deqB] msqueue2InitMem) c)
    (hf : c.final = true) :
    ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧
      ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
        (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1)) :=
  msqueue3_envG layout0 layoutA layoutB headAddr tailAddr dAddr n1Addr n2Addr (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) enq0_start deqA_start deqB_start initV3 hc hf

end Kraken.Promising.SLR.EnvG.ConcreteMsQueue3

#print axioms Kraken.Promising.SLR.EnvG.ConcreteMsQueue3.msqueue3_envG_concrete

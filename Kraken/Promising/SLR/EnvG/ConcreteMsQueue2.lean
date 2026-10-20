/-
Msqueue2 part 9: **concrete instance of
`MsQueue.msqueue2_envG`** (non-vacuity of its start hypotheses). The
enqueuer laid out at `0x100000` for thread `0`, the dequeuer at `0x200000`
for thread `1` (each directive its `fakeSize`, as the `.kl` runner lays out
text); `head` at `0x1000`, `tail` at `0x1008` (8 bytes each, initially the
dummy `d`), the dummy node `d` at `0x1100`, the enqueued nodes `n1` at
`0x1200` and `n2` at `0x1300` (links initially `0`); thread `0` starts the
enqueuer with `X1 = tail`, `X12 = n1`, `X13 = n2`, thread `1` the dequeuer
with `X0 = head`, `X1 = tail`, both with an empty private memory. Every
hypothesis is discharged by `decide`, `rfl` or `simp` (no `native_decide`).
`codeMatches`: the `.kl`'s `code` block parses to the `enq` label,
`enq2Prog`, `nop`, the `deq1` label, `deq2Prog`, `nop`.
-/
import Kraken.Promising.SLR.EnvG.MsQueue2Public
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.ConcreteMsQueue2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.MsQueue

/-! ## The layouts -/

/-- Thread `0`'s layout: the enqueuer's text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def layout0 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize enq2Prog

/-- Thread `1`'s layout: the dequeuer's text at `0x200000`, each directive
its `fakeSize`. -/
@[reducible] def layout1 : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize deq2Prog

instance valid0 : Executable.ValidLayout (layout0 enq2Prog) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance valid1 : Executable.ValidLayout (layout1 deq2Prog) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- `head`'s address. -/
def headAddr : BitVec 64 := 0x1000
/-- `tail`'s address. -/
def tailAddr : BitVec 64 := 0x1008
/-- The dummy node's address. -/
def dAddr : BitVec 64 := 0x1100
/-- The first enqueued node's address (`n1` of the `.kl`). -/
def n1Addr : BitVec 64 := 0x1200
/-- The second enqueued node's address (`n2` of the `.kl`). -/
def n2Addr : BitVec 64 := 0x1300

/-- Thread `0`'s initial state: `X1 = tail`, `X12 = n1`, `X13 = n2`, at the
start of `enq2Prog`, halting at the end of its text; no declarations, empty
private memory. -/
def enq0 : AArch64.State where
  exe := layout0 enq2Prog
  endPc := 0x100000 + 132
  st := ({ regs := { X1 := 0x1008, X12 := 0x1200, X13 := 0x1300 } }, 0x100000)

/-- Thread `1`'s initial state: `X0 = head`, `X1 = tail`, at the start of
`deq2Prog`, halting at the end of its text. -/
def deq1 : AArch64.State where
  exe := layout1 deq2Prog
  endPc := 0x200000 + 140
  st := ({ regs := { X0 := 0x1000, X1 := 0x1008 } }, 0x200000)

/-- The initial memory: `head = tail = d`, the links `0`. -/
def msqueue2InitMem : List (Loc × Val) :=
  [(⟨headAddr, 8⟩, 0x1100), (⟨tailAddr, 8⟩, 0x1100), (⟨dAddr + 8, 8⟩, 0), (⟨n1Addr + 8, 8⟩, 0),
    (⟨n2Addr + 8, 8⟩, 0)]

section
attribute [local instance] layout0

theorem enq0_start : StartE2 tailAddr n1Addr n2Addr enq0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [enq0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] layout1

theorem deq1_start : StartD2 headAddr tailAddr deq1 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [deq1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

theorem initV2 : InitV2 (Config.init [enq0, deq1] msqueue2InitMem : Config isa).mem
    ⟨⟨headAddr, tailAddr, dAddr, n1Addr⟩, n2Addr⟩ := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def msqueue2Kl : String := include_str "../../../Examples/LockFree/AArch64/msqueue2.kl"

/-- The `code` block of the `.kl` parses to the `enq` label, `enq2Prog`,
`nop`, the `deq1` label, `deq2Prog`, `nop`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => (prog.drop 1).take enq2Prog.length == enq2Prog &&
        (prog.drop (enq2Prog.length + 3)).take deq2Prog.length == deq2Prog &&
        prog.length == enq2Prog.length + deq2Prog.length + 4
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches msqueue2Kl

/-! ## The instance -/

/-- **`1:X10 = 1 ∧ 1:X11 = 2`** for `msqueue2.kl` under `Arch.armv8`,
concrete instance of `msqueue2_envG`. -/
theorem msqueue2_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enq0, deq1] msqueue2InitMem) c)
    (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧
      th1.st.st.1.regs.X11.toBitVec = 2 :=
  msqueue2_envG layout0 layout1 headAddr tailAddr dAddr n1Addr n2Addr (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) enq0_start deq1_start initV2 hc hf

end Kraken.Promising.SLR.EnvG.ConcreteMsQueue2

#print axioms Kraken.Promising.SLR.EnvG.ConcreteMsQueue2.msqueue2_envG_concrete

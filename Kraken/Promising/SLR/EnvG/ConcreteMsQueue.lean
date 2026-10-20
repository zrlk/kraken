/-
Part 9: **concrete instance of
`MsQueue.msqueue1_envG`** (non-vacuity of its start hypotheses). The
enqueuer laid out at `0x100000` for thread `0`, the dequeuer at `0x200000`
for thread `1` (each directive its `fakeSize`, as the `.kl` runner lays out
text); `head` at `0x1000`, `tail` at `0x1008` (8 bytes each, initially the
dummy `d`), the dummy node `d` at `0x1100` and the enqueued node `n1` at
`0x1200` (links initially `0`); thread `0` starts the enqueuer with
`X1 = tail`, `X12 = n1`, thread `1` the dequeuer with `X0 = head`,
`X1 = tail`, both with an empty private memory. Every hypothesis is
discharged by `decide`, `rfl` or `simp` (no `native_decide`); the initial
ghost's `½`/`½` split of `head`/`tail` is the one `erase_init` shows
satisfiable. `codeMatches`: the `.kl`'s `code` block parses to the `enq`
label, `enqProg`, `nop`, the `deq1` label, `deqProg`, `nop`.
-/
import Kraken.Promising.SLR.EnvG.MsQueuePublic
import Kraken.AArch64.WP.LayoutOfSize
import Kraken.Litmus.AArch64

namespace Kraken.Promising.SLR.EnvG.ConcreteMsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.MsQueue

/-! ## The layouts -/

/-- Thread `0`'s layout: the enqueuer's text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def layout0 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize enqProg

/-- Thread `1`'s layout: the dequeuer's text at `0x200000`, each directive
its `fakeSize`. -/
@[reducible] def layout1 : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize deqProg

instance valid0 : Executable.ValidLayout (layout0 enqProg) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

instance valid1 : Executable.ValidLayout (layout1 deqProg) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-! ## The parameters and the initial configuration -/

/-- `head`'s address. -/
def headAddr : BitVec 64 := 0x1000
/-- `tail`'s address. -/
def tailAddr : BitVec 64 := 0x1008
/-- The dummy node's address. -/
def dAddr : BitVec 64 := 0x1100
/-- The enqueued node's address (`n1` of the `.kl`). -/
def n1Addr : BitVec 64 := 0x1200

/-- Thread `0`'s initial state: `X1 = tail`, `X12 = n1`, at `enq1`, halting
at `pdone` (the end of its text); no declarations, empty private memory. -/
def enq0 : AArch64.State where
  exe := layout0 enqProg
  endPc := 0x100000 + 68
  st := ({ regs := { X1 := 0x1008, X12 := 0x1200 } }, 0x100000)

/-- Thread `1`'s initial state: `X0 = head`, `X1 = tail`, at `deq1a`,
halting at `ddone1`. -/
def deq1 : AArch64.State where
  exe := layout1 deqProg
  endPc := 0x200000 + 72
  st := ({ regs := { X0 := 0x1000, X1 := 0x1008 } }, 0x200000)

/-- The initial memory: `head = tail = d`, the links `0`. -/
def msqueue1InitMem : List (Loc × Val) :=
  [(⟨headAddr, 8⟩, 0x1100), (⟨tailAddr, 8⟩, 0x1100), (⟨dAddr + 8, 8⟩, 0), (⟨n1Addr + 8, 8⟩, 0)]

section
attribute [local instance] layout0

theorem enq0_start : StartE tailAddr n1Addr enq0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [enq0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

section
attribute [local instance] layout1

theorem deq1_start : StartD headAddr tailAddr deq1 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [deq1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

theorem initV : InitV (Config.init [enq0, deq1] msqueue1InitMem : Config isa).mem ⟨headAddr, tailAddr, dAddr, n1Addr⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Config.init] <;> decide

/-! ## The `.kl` file runs these threads -/

/-- The `.kl` source. -/
def msqueue1Kl : String := include_str "../../../Examples/LockFree/AArch64/msqueue1.kl"

/-- The `code` block of the `.kl` parses to the `enq` label, `enqProg`
(from `enq1:` to `pdone:`), `nop`, the `deq1` label, `deqProg` (from
`deq1a:` to `ddone1:`), `nop`. -/
def codeMatches (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => (prog.drop 1).take enqProg.length == enqProg &&
        (prog.drop (enqProg.length + 3)).take deqProg.length == deqProg &&
        prog.length == enqProg.length + deqProg.length + 4
    | .error _ => false

/-- info: true -/
#guard_msgs in
#eval codeMatches msqueue1Kl

/-! ## The instance -/

/-- **`1:X10 = 1`** for `msqueue1.kl` under `Arch.armv8`, concrete instance
of `msqueue1_envG`. -/
theorem msqueue1_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enq0, deq1] msqueue1InitMem) c)
    (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 :=
  msqueue1_envG layout0 layout1 headAddr tailAddr dAddr n1Addr (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) enq0_start deq1_start initV hc hf

end Kraken.Promising.SLR.EnvG.ConcreteMsQueue

#print axioms Kraken.Promising.SLR.EnvG.ConcreteMsQueue.msqueue1_envG_concrete

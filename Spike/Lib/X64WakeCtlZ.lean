/-
**Facts of the control at every node of wake.w's worker, x86-64** (the x64
twin of `Spike/Lib/A64WakeCtlZ.lean`): every node's invariant pins the
control to one of the child's controls (`kidC`, after the `split`, the
`store`, the `unpark`), so a fact `P` of the four holds at every node
(`CtlZ P`, `thrZ_ctl`, `cZ_ctl`). At `P :=` "every untagged locative
accessed is the flag" (`FlagPtr cS`) this gives `wakeZX`'s `LabPtr`
conjunct (`childThrZ_flag`, `cZ_flag`): the only access through a locative
is the `store` to `c`, whose word is `.loc cS 0`.

- `CtlZ P`; `nodeZ_ctl`: a node whose invariant pins the control.
- `thrZ_ctl`, `cZ_ctl`: `CtlZ P` at the thread worker's and the stub's nodes.
- `FlagPtr`, `flag_of_term`, `childThrZ_flag`, `cZ_flag`.

**Unlike AArch64** (forced by the x64 shape): `NodeZ` is block-indexed
(`Spike/Lib/X64WakeNN.lean`), so the nodes are closed through `nodeZ_ctl`
(the control's pin) and `Pass.nodeZ_nil` (the call nodes' empty blocks);
the stub is four nodes over `cBlk`; `LabPtr` and the store's locative are
`X64WakeMappedRow`'s and `X64WakeLabMapped`'s.
-/
import Spike.Lib.X64WakePass
import Spike.Lib.X64WakeLabMapped

namespace Spike.Lib.X64.Flow.Worker.Wake.CtlZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZ thrJ thrJE wcJE)
open Spike.Lib.X64.WakePh.Child (cN childN childJ)
open Spike.Lib.X64.Flow.Worker.Wake.Child (kidC cBlk)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerTy workerRest wc1)
open Spike.Lib.X64.Flow.Worker.Wake.Pass (nodeZ_nil)
open Spike.Lib.X64WakeMappedRow (LabPtr)

/-- **A fact of the control** as a fragment. -/
def CtlZ (P : Ctl → Prop) : Frag isa := fun _ c => P c

variable {P : Ctl → Prop} {exe : _root_.Executable}

/-- **A fact of the control at a node** whose invariant pins the control. -/
theorem nodeZ_ctl {n : ND} {blk : List (Directive × Nat)} {c' : Ctl} (hc : ∀ σ c, n.J σ c → c = c')
    (h : P c') : NodeZ (CtlZ P) exe n blk :=
  fun _ σ c _ _ _ _ hJ => (hc σ c hJ) ▸ h

/-- Closes a node's `CtlZ` obligation: the pin, then `P` there. -/
local macro "cz" h:term : tactic =>
  `(tactic| first
    | exact nodeZ_nil
    | exact nodeZ_ctl (fun σ c hJ => by first | exact hJ.1 | exact hJ.1.1 | exact hJ) $h)

/-- **A fact of the four controls at every node of the thread worker's run.** -/
theorem thrZ_ctl {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} (h0 : P c0) (h1 : P c1) (h2 : P c2) (h3 : P c3) :
    ThrZ (CtlZ P) exe c0 c1 c2 c3 A B tp sp0 where
  pro := fun _ _ _ _ _ _ _ hJ => hJ.1 ▸ h0
  head i := by cases i <;> cz h0
  wpro _ _ := fun _ _ _ _ _ _ _ hJ => hJ.1 ▸ h1
  wk _ _ _ i := by
    cases i
    · cz h1
    · cz h1
    · cz h2
    · cz h2
    · cz h3
  unpk _ _ i := by
    cases i
    · cz h2
    · cz h2
    · cz h2
    all_goals cz h3
  tail i := by cases i <;> cz h3

/-- **A fact of the control at the child's stub.** -/
theorem cZ_ctl {cW : Ctl} {A B tp sp0 : BitVec 64} (h0 : P cW) :
    ∀ i, NodeZ (CtlZ P) exe (cN (_root_.Executable.labels exe).label cW A B tp sp0 i) (cBlk i) := by
  intro i; cases i <;> cz h0

/-! ## The flag -/

/-- **Every untagged locative the control accesses is `cS`.** -/
def FlagPtr (cS : WeakMem.Address) (c : Ctl) : Prop := ∀ sa, LabPtr c sa → sa = cS

/-- No access at a control binding no `labOp`. -/
theorem flag_of_term {cS : WeakMem.Address} {c : Ctl}
    (h : ∀ x op e, c.term = .let_ x op e → X64WakeLabMapped.labOp op = false) : FlagPtr cS c :=
  fun sa hp => (X64WakeLabMapped.noPtr_of_term h sa hp).elim

/-- **`FlagPtr` at the child's controls**: the tail call, the `store` to `c`
(its word `w1` the locative `cS`), the `unpark`, the return. -/
theorem childThrZ_flag (T : Ty) (w1 w2 : TermRun.Word) {cS : WeakMem.Address} (hw : w1.val = .loc cS 0)
    (A B tp sp0 : BitVec 64) :
    ThrZ (CtlZ (FlagPtr cS)) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_ctl (flag_of_term fun _ _ _ h => by simp [kidC] at h)
    (X64WakeLabMapped.ptr_of_store (x := "d") (b := .lit 1) (e := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit))
      (ty := .ptr .pub .int) rfl rfl hw)
    (flag_of_term fun _ _ _ h => by simp at h; obtain ⟨-, rfl, -⟩ := h; rfl)
    (flag_of_term fun _ _ _ h => by simp at h)

/-- **`FlagPtr` at the child's stub** (the tail call's control). -/
theorem cZ_flag (T : Ty) (w1 w2 : TermRun.Word) {cS : WeakMem.Address} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (CtlZ (FlagPtr cS)) exe (cN (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i)
      (cBlk i) :=
  cZ_ctl (flag_of_term fun _ _ _ h => by simp [kidC] at h)

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.CtlZ.childThrZ_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms childThrZ_flag

end Spike.Lib.X64.Flow.Worker.Wake.CtlZ

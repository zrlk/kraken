/-
**Facts of the control at every node of wake.w's worker** (AArch64): every node's invariant pins the control to one of the child's
controls (`kidC`, after the `split`, the `store`, the `unpark`), so a fact
`P` of the four holds at every node (`CtlZ P`, `thrZ_ctl`, `cZ_ctl`). At
`P :=` "every untagged locative accessed is the flag" (`FlagPtr cS`) this
gives `wakeZX`'s `LabPtr` conjunct (`childThrZ_flag`, `cZ_flag`): the only
access through a locative is the `store` to `c`, whose word is
`.loc cS 0`. The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).
-/
import Spike.Lib.A64WakePass
import Spike.Lib.WakeLabMapped

namespace Spike.Lib.A64.Flow.Worker.Wake.CtlZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZ thrJ thrJE wcJE)
open Spike.Lib.A64.Flow.Worker.Wake.Child (cN childN childJ cLen pfxM kidC)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy workerRest wc1)
open Spike.Lib.WakeMappedRow (LabPtr)

/-- **A fact of the control** as a fragment. -/
def CtlZ (P : Ctl → Prop) : Frag isaLSE2 := fun _ c => P c

variable {P : Ctl → Prop} {exe : _root_.Executable}

/-- Closes a node's `CtlZ` obligation: the node's invariant pins the
control to one of the given ones, at which `P` holds. -/
local macro "cz" : tactic =>
  `(tactic| (intro s σ c k hk he hpc hJ
             revert hk hJ
             simp only [Unpark.N, Unpark.JI, Unpark.JS, Unpark.JE, Unpark.JX, WkTailW.N, WkTailW.JI, ThrTailW.N,
               ThrHeadW.tN, thrJ, thrJE, wcJE, cN, childN, childJ, Unpark.lenN, WkTailW.lenN, ThrTailW.lenN,
               ThrHeadW.lenN, cLen, and_imp, forall_exists_index]
             intros
             subst_vars
             first | omega | assumption))

/-- **A fact of the four controls at every node of the thread worker's run.** -/
theorem thrZ_ctl {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64} (h0 : P c0) (h1 : P c1) (h2 : P c2) (h3 : P c3) :
    ThrZ (CtlZ P) exe c0 c1 c2 c3 A B tp sp0 where
  pro := fun _ _ _ _ _ _ _ hJ => hJ.1 ▸ h0
  head i := by cases i <;> cz
  wpro _ _ := fun _ _ _ _ _ _ _ hJ => hJ.1 ▸ h1
  wk _ _ i := by cases i <;> cz
  unpk _ _ i := by cases i <;> cz
  tail i := by cases i <;> cz

/-- **A fact of the control at the child's stub.** -/
theorem cZ_ctl {cW : Ctl} {A B tp sp0 : BitVec 64} (h0 : P cW) :
    ∀ i, NodeZ (CtlZ P) exe (cN pfxM (_root_.Executable.labels exe).label cW A B tp sp0 i) (cLen i) := by
  intro i; cases i <;> cz

/-! ## The flag -/

/-- **Every untagged locative the control accesses is `cS`.** -/
def FlagPtr (cS : WeakMem.Address) (c : Ctl) : Prop := ∀ sa, LabPtr c sa → sa = cS

/-- No access at a control binding no `labOp`. -/
theorem flag_of_term {cS : WeakMem.Address} {c : Ctl}
    (h : ∀ x op e, c.term = .let_ x op e → WakeLabMapped.labOp op = false) : FlagPtr cS c :=
  fun sa hp => (WakeLabMapped.noPtr_of_term h sa hp).elim

/-- **`FlagPtr` at the child's controls**: the tail call, the `store` to `c`
(its word `w1` the locative `cS`), the `unpark`, the return. -/
theorem childThrZ_flag (T : Ty) (w1 w2 : TermRun.Word) {cS : WeakMem.Address} (hw : w1.val = .loc cS 0)
    (A B tp sp0 : BitVec 64) :
    ThrZ (CtlZ (FlagPtr cS)) exe (kidC T w1 w2) (wc1 workerTy w1 w2)
      ⟨.let_ "w" (.ext .unpark (.var "j")) (.ret .unit), ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      ⟨.ret .unit, ("w", ExtName.unpark.sig.2, []) :: ("d", .unit, []) :: (wc1 workerTy w1 w2).env, none⟩
      A B tp sp0 :=
  thrZ_ctl (flag_of_term fun _ _ _ h => by simp [kidC] at h)
    (WakeLabMapped.ptr_of_store (x := "d") (b := .lit 1) (e := .let_ "w" (.ext .unpark (.var "j")) (.ret .unit))
      (ty := .ptr .pub .int) rfl rfl hw)
    (flag_of_term fun _ _ _ h => by simp at h; obtain ⟨-, rfl, -⟩ := h; rfl)
    (flag_of_term fun _ _ _ h => by simp at h)

/-- **`FlagPtr` at the child's stub** (the tail call's control). -/
theorem cZ_flag (T : Ty) (w1 w2 : TermRun.Word) {cS : WeakMem.Address} {A B tp sp0 : BitVec 64} :
    ∀ i, NodeZ (CtlZ (FlagPtr cS)) exe (cN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) A B tp sp0 i)
      (cLen i) :=
  cZ_ctl (flag_of_term fun _ _ _ h => by simp [kidC] at h)

end Spike.Lib.A64.Flow.Worker.Wake.CtlZ

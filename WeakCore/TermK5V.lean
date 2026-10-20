import WeakCore.TermOwnG0Defs
import WeakCore.TermStepper

/-!
# TermK5V: a `publish` step keeps `vWr` (S1b, for the producers' provenance invariant)

At a thread step at a `publish` (`TermOwnG0Defs.PubAt`), every result's `vWr` is the thread's: the
step is the release fence `fenceS s .st`, and a fence keeps `vWr` (`TermStepper.stepFence_vWr`).
-/

namespace TermK5V
open CoreLang CoreTerm TermRun TermOwnG0Defs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem fenceS_vWr (s : St) (f : WeakMem.Fence) : (fenceS s f).vs.vWr = s.vs.vWr :=
  TermStepper.stepFence_vWr _ f

/-- **A `publish` step keeps `vWr`.** -/
theorem pub_vWr {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {l : AllocLabel}
    {r : Memory × List Ts × TTh} (h : PubAt th l) (hr : r ∈ tstep g mem pairs th) :
    r.2.2.vs.vWr = th.vs.vWr := by
  obtain ⟨y, a, e, rt, ws, ad, hterm, hea, -, -⟩ := h
  simp only [tstep, hterm, evalOp, hea] at hr
  cases rt <;> simp [ol] at hr
  all_goals first
    | (obtain ⟨-, rfl⟩ := hr; simp [withS, fenceS_vWr, stOf])
    | (rcases hr with ⟨_, _, rfl⟩; simp [withS, fenceS_vWr, stOf])
    | (obtain ⟨a1, a2, a3, hm, rfl⟩ := hr
       split at hm <;> simp at hm
       all_goals (obtain ⟨rfl, -, -⟩ := hm; simp [withS, fenceS_vWr, stOf]))

end TermK5V

#print axioms TermK5V.fenceS_vWr
#print axioms TermK5V.pub_vWr

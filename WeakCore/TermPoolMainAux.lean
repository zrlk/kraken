import WeakCore.TermPoolStaging
import WeakCore.TermOverCr

/-!
# Pool route, TermMain helpers

- `crKeys_right`, `crKeys_dh`: the key-freedom of the transfer's pool part (R2, for `poolKnetT`).
-/

namespace TermPoolMainAux
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCr
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## R2: key-freedom of the pool part -/

theorem crKeys_right {a b : Res} (h : TermPlant.CrKeys (a + b)) : TermPlant.CrKeys b := fun l => by
  have := h l
  simp only [Res.add_apply] at this
  omega

/-- The pool part `δh` of the transfer is key-free (from its tags at post). -/
theorem crKeys_dh (δ : Ts → Res) (cr pl : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat)
    (ho : ∀ j, j ≠ i → c'.ths[j]? = c.ths[j]?) :
    ∀ t, TermPlant.CrKeys (TermPoolStaging.δh δ cr pl c c' Eg' i t) := by
  intro t
  by_cases h0 : TermPoolStaging.δh δ cr pl c c' Eg' i t = .zero
  · rw [h0]; exact TermPlant.CrKeys_zero
  · obtain ⟨j, thj, hji, hj, -, hP⟩ := TermPoolStaging.δh_tag δ cr pl c c' Eg' i t h0
    exact crKeys_right (hP thj (by rw [ho j hji]; exact hj)).2.1

end TermPoolMainAux

#print axioms TermPoolMainAux.crKeys_dh

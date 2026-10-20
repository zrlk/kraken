import WeakCore.TermOverCrT
import WeakCore.TermNPmixW

/-!
# TermOverCrU: `hent_of`'s `hL` from the store's mask export (`TermPiece.GdLT`)

A foreign store's drop list records, per entry, which target words it holds latest (`g.L`).
With `GdLT` (the stepper's view: a word whose mask is off has no newly visible message), a
target unit newly overtaken in the owner's view has its mask on.  The two views agree through
the same memory and the same skip-list membership (`promAt_sh_iff` at a shared label).
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Core of (hL).**  A word with no newly visible message in the stepper's view is not newly
overtaken in the owner's view (same memory, same skip-list membership at `l`). -/
theorem nnv_newOver {E E' Ei : TEnv} {s s' si si' : St} {l : AllocLabel} {o : Nat} {tw : Ts}
    (hN : TermNPmixW.NoNewVis Ei si si' ⟨l, o⟩)
    (hm : si.mem = s.mem) (hm' : si'.mem = s'.mem)
    (hP : ∀ k t, t ∈ PromAt Ei si ⟨l, k⟩ ↔ t ∈ PromAt E s ⟨l, k⟩)
    (hP' : ∀ k t, t ∈ PromAt Ei si' ⟨l, k⟩ ↔ t ∈ PromAt E' s' ⟨l, k⟩)
    (hov : TermPlant.OverT E' s' ⟨l, o⟩ tw) (hno : ¬ TermPlant.OverT E s ⟨l, o⟩ tw) : False := by
  obtain ⟨t, m, hlt, hmt, hml, hnot⟩ := hov
  refine hnot ((hP' o t).1 (hN tw (fun t1 m1 h1 hm1 hl1 => ?_) t m hlt (by rw [hm']; exact hmt) hml))
  exact (hP o t1).2 ((Classical.em _).elim id fun hn => False.elim <|
    hno ⟨t1, m1, h1, by rw [← hm]; exact hm1, hl1, hn⟩)

/-- **(hL) A newly overtaken target unit has its mask on.**  `hLT` is `TermPiece.GdLT` unfolded,
in the stepper's view (`Ei`, `si` → `si'`); the owner's view (`E`, `s` → `E'`, `s'`) shares the
memory and the skip-list membership at `l`. -/
theorem hL_of {E E' Ei : TEnv} {s s' si si' : St} {Gd : List TermPiece.GdE} {l : AllocLabel} {ot n : Nat}
    (hLT : ∀ g ∈ Gd, ∀ k, g.l = l → g.b ≤ k → ot ≤ k → k < ot + n → g.L (k - g.b) = false →
      TermNPmixW.NoNewVis Ei si si' ⟨l, k⟩)
    (hm : si.mem = s.mem) (hm' : si'.mem = s'.mem)
    (hP : ∀ k t, t ∈ PromAt Ei si ⟨l, k⟩ ↔ t ∈ PromAt E s ⟨l, k⟩)
    (hP' : ∀ k t, t ∈ PromAt Ei si' ⟨l, k⟩ ↔ t ∈ PromAt E' s' ⟨l, k⟩) :
    ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      ∀ g ∈ Gd, g.l = l → g.b ≤ o → g.L (o - g.b) = true := by
  intro o tw ho1 ho2 hov hno g hg hgl hb
  cases hL : g.L (o - g.b) with
  | true => rfl
  | false => exact (nnv_newOver (hLT g hg o hgl hb ho1 ho2 hL) hm hm' hP hP' hov hno).elim

/-- **(hL0) A newly overtaken target unit has its word mask `L0` on** (`TermPiece.GdLT0`
unfolded, same views as `hL_of`). -/
theorem newOver_L0 {E E' Ei : TEnv} {s s' si si' : St} {l : AllocLabel} {ot n : Nat} {L0 : Nat → Bool}
    (hLT0 : ∀ k, k < n → L0 k = false → TermNPmixW.NoNewVis Ei si si' ⟨l, ot + k⟩)
    (hm : si.mem = s.mem) (hm' : si'.mem = s'.mem)
    (hP : ∀ k t, t ∈ PromAt Ei si ⟨l, k⟩ ↔ t ∈ PromAt E s ⟨l, k⟩)
    (hP' : ∀ k t, t ∈ PromAt Ei si' ⟨l, k⟩ ↔ t ∈ PromAt E' s' ⟨l, k⟩) :
    ∀ o tw, ot ≤ o → ot + n > o → TermPlant.OverT E' s' ⟨l, o⟩ tw → ¬ TermPlant.OverT E s ⟨l, o⟩ tw →
      L0 (o - ot) = true := by
  intro o tw ho1 ho2 hov hno
  cases hL : L0 (o - ot) with
  | true => rfl
  | false =>
    have hN := hLT0 (o - ot) (by omega) hL
    rw [show ot + (o - ot) = o by omega] at hN
    exact (nnv_newOver hN hm hm' hP hP' hov hno).elim

end TermOverCrW

#print axioms TermOverCrW.hL_of
#print axioms TermOverCrW.newOver_L0

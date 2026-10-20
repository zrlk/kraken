import WeakCore.TermPoolStaging

namespace TermPoolCovB
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (shared with hWbR route (i) COVER) **Pool cover at overtaken first writes of
predicted units**: at every own frontier cell of `j`, every unit that is predicted (`PredU`), not
a word unit, whose lowest own promise `tw` is its first write and overtaken (no window guard:),
is covered by a pool item (credit bound at `pl j`) in the predicted-unit form (`CrItemQ`: the
pinned word may be the first write's own word). -/
def PoolCovU (Eg : GEnv) (c : Cfg) (pl : Nat → Ts → Res) : Prop :=
  ∀ j thj (S : AllocLabel → Prop), c.ths[j]? = some thj → ∀ l cl, (Cut Eg j S).sto l = some cl →
    cl.owner = some j → Eg.pfr l ≠ none → ¬ Eg.pubd l →
    ∀ o tw, PredU (Cut Eg j S) ⟨l, o⟩ → ¬ VisU (Cut Eg j S) ⟨l, o⟩ →
      TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw → FirstW c.mem ⟨l, o⟩ tw →
      TermPlant.OverT (Cut Eg j S) (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      ∃ x usS i, TermOverCr.CrItemQ (Cut Eg j S) (stOf c.mem c.pairs thj) (pl j) l cl x ∧
        accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧ x.2.2.2.2.2 i = true

/-- With no pool and no outstanding promises the cover is vacuous (`pl := 0` init). -/
theorem poolCovU_nil {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res}
    (h : ∀ (j : Nat) (thj : TTh), c.ths[j]? = some thj → thj.promises = []) : PoolCovU Eg c pl := by
  intro j thj S hj l cl _ _ _ _ o tw _ _ hlo
  obtain ⟨hin, -⟩ := hlo
  have e : (stOf c.mem c.pairs thj).promises = [] := h j thj hj
  rw [e] at hin
  cases hin

#print axioms poolCovU_nil

/-- (list form) **Pool cover, list form**: at every own frontier
cell of `j`, one holder-`Nodup` list `Gs` of pool items (`CrItemQ` at `pl j`) covering every
predicted, non-visible unit whose lowest own promise `tw` is its first write and overtaken (the
`OverCrL` shape); at non-`pubd` cells. -/
def PoolCovUL (Eg : GEnv) (c : Cfg) (pl : Nat → Ts → Res) : Prop :=
  ∀ j thj (S : AllocLabel → Prop), c.ths[j]? = some thj → ∀ l cl, (Cut Eg j S).sto l = some cl →
    cl.owner = some j → Eg.pfr l ≠ none → ¬ Eg.pubd l →
    ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)), (Gs.map (·.1)).Nodup ∧
      (∀ x ∈ Gs, TermOverCr.CrItemQ (Cut Eg j S) (stOf c.mem c.pairs thj) (pl j) l cl x) ∧
      ∀ o tw, PredU (Cut Eg j S) ⟨l, o⟩ → ¬ VisU (Cut Eg j S) ⟨l, o⟩ →
        TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw → FirstW c.mem ⟨l, o⟩ tw →
        TermPlant.OverT (Cut Eg j S) (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
        ∃ x ∈ Gs, ∃ usS i, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS i (o - x.2.1) ∧
          x.2.2.2.2.2 i = true

/-- The list form gives the unit form. -/
theorem poolCovU_of_L {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res} (h : PoolCovUL Eg c pl) :
    PoolCovU Eg c pl := by
  intro j thj S hj l cl hl ho hp hnp o tw h1 h2 h3 h4 h5
  obtain ⟨Gs, -, hit, hcov⟩ := h j thj S hj l cl hl ho hp hnp
  obtain ⟨x, hx, usS, i, a1, a2, a3, a4⟩ := hcov o tw h1 h2 h3 h4 h5
  exact ⟨x, usS, i, hit x hx, a1, a2, a3, a4⟩

/-- With no outstanding promises the list cover is vacuous (`Gs := []`). -/
theorem poolCovUL_nil {Eg : GEnv} {c : Cfg} {pl : Nat → Ts → Res}
    (h : ∀ (j : Nat) (thj : TTh), c.ths[j]? = some thj → thj.promises = []) : PoolCovUL Eg c pl := by
  intro j thj S hj l cl _ _ _ _
  refine ⟨[], List.nodup_nil, fun _ hx => absurd hx (List.not_mem_nil), ?_⟩
  intro o tw _ _ hlo
  obtain ⟨hin, -⟩ := hlo
  have e : (stOf c.mem c.pairs thj).promises = [] := h j thj hj
  rw [e] at hin
  cases hin

#print axioms poolCovU_of_L
#print axioms poolCovUL_nil
end TermPoolCovB

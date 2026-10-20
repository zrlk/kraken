import WeakCore.TermPoolThread

/-! # TermPoolResplit (R4 route (b′))

Before a thread step of `i` (result `r` fixed), the pool credit of `i` at the promises `Q` (the step
discharges them, and no frontier-footprint message lies at or below them: `FrGuard`) moves into
`i`'s credits: `crR cr pl i Q` / `plR pl i Q`.  The sum `crPl` is unchanged, so the pool clause,
balance, key nets and rid freshness carry over; the pool tags shrink; `PromCrK` at the moved
credits is a plant credit (the pool item is piece-lowest, `PieceLow`, below every footprint
message, `FrGuard`, and its value is the item's, `K := ∅`).  The stepper then charges the
consumed pool credit against `cr`, so its inequality is the old one at `crR`. -/

namespace TermPoolResplit
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermPoolStaging
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (b′) No footprint message at the label of `t`'s message lies at or below `t`. -/
def FrGuard (E : TEnv) (mem : Memory) (t : Ts) : Prop :=
  ∀ m, mem[t]? = some m → ∀ f mf, f ∈ FpAt E ⟨m.loc.label, 0⟩ → mem[f]? = some mf →
    mf.loc.label = m.loc.label → t < f

/-- The credits after moving `i`'s pool credit at `Q` into them. -/
noncomputable def crR (cr pl : Nat → Ts → Res) (i : Nat) (Q : Ts → Prop) : Nat → Ts → Res := by
  classical
  exact fun j t => if j = i ∧ Q t then cr j t + pl j t else cr j t

/-- The pool credits after the move. -/
noncomputable def plR (pl : Nat → Ts → Res) (i : Nat) (Q : Ts → Prop) : Nat → Ts → Res := by
  classical
  exact fun j t => if j = i ∧ Q t then .zero else pl j t

section
variable {cr pl : Nat → Ts → Res} {i j : Nat} {Q : Ts → Prop} {t : Ts}

theorem crR_pos (h : j = i ∧ Q t) : crR cr pl i Q j t = cr j t + pl j t := by
  simp only [crR]
  split
  · rfl
  · contradiction

theorem crR_neg (h : ¬ (j = i ∧ Q t)) : crR cr pl i Q j t = cr j t := by
  simp only [crR]
  split
  · contradiction
  · rfl

theorem plR_pos (h : j = i ∧ Q t) : plR pl i Q j t = .zero := by
  simp only [plR]
  split
  · rfl
  · contradiction

theorem plR_neg (h : ¬ (j = i ∧ Q t)) : plR pl i Q j t = pl j t := by
  simp only [plR]
  split
  · contradiction
  · rfl

theorem crR_other (hj : j ≠ i) : crR cr pl i Q j = cr j := funext fun _ => crR_neg fun h => hj h.1

end

/-- The move keeps the credits-plus-pool sum. -/
theorem crPl_R (cr pl : Nat → Ts → Res) (i : Nat) (Q : Ts → Prop) :
    crPl (crR cr pl i Q) (plR pl i Q) = crPl cr pl := by
  funext j t
  simp only [crPl]
  by_cases h : j = i ∧ Q t
  · rw [crR_pos h, plR_pos h, Res.add_zero]
  · rw [crR_neg h, plR_neg h]

/-- The moved credits hold no own key beyond the old ones (pool credits are key-free). -/
theorem crR_own {Eg : GEnv} {c : Cfg} {cr pl : Nat → Ts → Res} {i : Nat} {th : TTh} {Q : Ts → Prop}
    (htag : PoolTag Eg c pl) (hth : c.ths[i]? = some th) (j : Nat) (t : Ts) (l : AllocLabel) :
    crR cr pl i Q j t (.own l) = cr j t (.own l) := by
  by_cases h : j = i ∧ Q t
  · rw [crR_pos h, Res.add_apply]
    obtain ⟨rfl, -⟩ := h
    by_cases hp : pl j t = .zero
    · rw [hp]; rfl
    · rw [(htag.1 j th t hth hp).2.1 l, Nat.add_zero]
  · rw [crR_neg h]

/-- **`PromCrK` at the moved credits.** -/
theorem promCrK_R {p : Prog} {k : Promises.Knobs} {arch : Arch} {Eg : GEnv} {c : Cfg} {i : Nat} {th : TTh}
    {S : AllocLabel → Prop} {cr db pl : Nat → Ts → Res} {Q : Ts → Prop}
    (hth : c.ths[i]? = some th) (htag : PoolTag Eg c pl)
    (hmi : MemInv (gOf p k arch c i) (Cut Eg i S) (stOf c.mem c.pairs th))
    (hQ : ∀ t, Q t → FrGuard (Cut Eg i S) c.mem t)
    (hC : TermPlant.PromCrK (Cut Eg i S) (stOf c.mem c.pairs th) (cr i) (db i)) :
    TermPlant.PromCrK (Cut Eg i S) (stOf c.mem c.pairs th) (crR cr pl i Q i) (db i) := by
  intro tw htw
  obtain ⟨m, hm, hd, hc⟩ := hC tw htw
  refine ⟨m, hm, hd, ?_⟩
  by_cases hnq : ¬ Q tw
  · rw [crR_neg fun h => hnq h.2]; exact hc
  have hq : Q tw := Classical.not_not.1 hnq
  rw [crR_pos ⟨rfl, hq⟩]
  by_cases hp : pl i tw = .zero
  · rw [hp, Res.add_zero]; exact hc
  obtain ⟨-, hK, m', hm', hfr, h3⟩ := htag.1 i th tw hth hp
  have hmm : (stOf c.mem c.pairs th).mem[tw]? = some m' := hm'
  have e : m' = m := Option.some.inj (hmm.symm.trans hm)
  subst e
  have hG := hQ tw hq m' hm'
  have hK0 := hfr.resolve_left fun h => by
    obtain ⟨f, mf, hf, hmf, hfl, hle⟩ := h S
    exact absurd (hG f mf hf hmf hfl) (Nat.not_lt.2 hle)
  obtain ⟨hpf, -⟩ := hK0 S
  obtain ⟨cl, x, hsto, hown, hx, hci, hlow⟩ := h3 S
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, -⟩ := hci
  rw [hx] at a1 a12
  have hmh : mh = m' := Option.some.inj (a1.symm.trans hmm)
  subst hmh
  have hkc : TermPlant.CrKeys (cr i tw) := hc.elim
    (fun ho => by rw [TermPlant.oldCr_nwordZ a4 ho]; exact TermPlant.CrKeys_zero) (fun h => h.2)
  obtain ⟨f0, hf0⟩ := Option.ne_none_iff_exists'.1 hpf
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 _ cl f0 hsto hf0).1
  obtain ⟨sb, S0, b0, hseg, hat, hsum⟩ := TermPiece.seg_of_atOffS hlay a5 a6
  have hlt : tw < c.mem.size := Nat.lt_of_not_le fun h => by
    rw [Array.getElem?_eq_none_iff.2 h] at hm'; cases hm'
  refine Or.inr ⟨⟨cl, sb, S0, b0, x.2.2.1, usS, tw, hsto, by rw [hown]; rfl, hpf, hseg, hat, a6, a4, a7,
    Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.sub_lt_left_of_lt_add a8 a9), hsum ▸ a8, hsum ▸ a9, Nat.le_refl _, hlt, fun tf mf h1 h2 h3 => hG tf mf h1 h2 h3,
    fun t' m2 h1 h2 h3 h4 h5 _ => hlow usS a7 t' m2 h1 h2 h3 (hsum ▸ h4) (hsum ▸ h5),
    Or.inl ⟨fun _ => false, x.2.2.2.1, x.2.2.2.2.1, a10, a11, ?_, fun _ _ _ _ h => absurd h Bool.false_ne_true⟩⟩,
    fun l => by have h1 := hkc l; have h2 := hK l; simp only [Res.add_apply]; omega⟩
  exact Res.le_def.2 fun key => by
    have h1 := Res.le_def.1 a12 key
    simp only [Res.add_apply]
    omega

end TermPoolResplit

#print axioms TermPoolResplit.crPl_R
#print axioms TermPoolResplit.crR_own
#print axioms TermPoolResplit.promCrK_R

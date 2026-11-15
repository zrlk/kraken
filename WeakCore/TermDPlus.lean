import WeakCore.TermTyped
import WeakCore.TermPubSto

/-! # TermDPlus (D+): the seen publishes from `MemInv`, and the bridge `NoHoldPubN → NoHoldPubA`

* `pubWin_ab` (CWN3): at an own cell that is frontier-free or seen, `PubWin` follows from `MemInv`
  alone (`OwnHidP.2`: `rc < ini` needs a frontier and, unless `ZW`, `¬ seen`).
* `noHold_seen` (CWN3): at a seen own cell, `NoHold` follows from `MemInv` ((a) vacuous, (b) by
  `pubWin_ab`, (c) vacuous by `SeenLE`).
* `noHoldPubA_of_N`: the named `NoHoldPubN` (unseen publishes only) gives `NoHoldPubA`; a seen publish's
  cell is an own `sto` cell (`TermPubSto.pubSto_of_typed`).  Only `MemInv` at the current typing and
  the typing itself are used (no run induction, no `OwnXLe`).
-/

namespace TermDPlus
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermTyped
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (D+) `ZW` is decidable: it is a computation on the cell's type (no classical case split). -/
theorem zw_dec (E : TEnv) (l : AllocLabel) : ZW E l ∨ ¬ ZW E l := by
  cases hs : E.sto l with
  | none => exact .inr fun ⟨c, _, _, _, h, _⟩ => by rw [hs] at h; cases h
  | some c =>
    have hd : (∃ N e us, c.ty = .array (.lit N) e ∧ accs e = some us ∧ nWords us = 0) ∨
        ¬ (∃ N e us, c.ty = .array (.lit N) e ∧ accs e = some us ∧ nWords us = 0) := by
      generalize c.ty = t
      cases t <;> try (right; rintro ⟨_, _, _, h, _⟩; cases h; done)
      rename_i i e
      cases i <;> try (right; rintro ⟨_, _, _, h, _⟩; cases h; done)
      rename_i N
      cases ha : accs e with
      | none =>
        right; rintro ⟨_, _, _, h, h2, _⟩; cases h; rw [ha] at h2; cases h2
      | some us =>
        exact if hz : nWords us = 0 then .inl ⟨N, e, us, rfl, ha, hz⟩
        else .inr (by rintro ⟨_, _, _, h, h2, h3⟩; cases h; rw [ha] at h2; cases h2; exact hz h3)
    rcases hd with h | h
    · obtain ⟨N, e, us, h1, h2, h3⟩ := h
      exact .inl ⟨c, N, e, us, hs, h1, h2, h3⟩
    · exact .inr fun ⟨c', N, e, us, h0, h1, h2, h3⟩ => by
        rw [hs] at h0; cases h0; exact h ⟨N, e, us, h1, h2, h3⟩

/-- (D+ (α)/(β)) `PubWin` at an own cell that is frontier-free or seen, from `MemInv`. -/
theorem pubWin_ab {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} (hm : MemInv g E s)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hab : E.pfr l = none ∨ E.seen l) :
    PubWin E s l := by
  refine ⟨fun f hf hns => ?_, ?_⟩
  · rcases hab with h | h
    · rw [h] at hf; cases hf
    · exact absurd h hns
  · by_cases hlt : E.rc l < E.ini l
    · obtain ⟨f, hf, hz, -⟩ := hm.2.2.2.2.2.1.2 l c hsto hown hlt
      rcases hab with h | h
      · rw [h] at hf; cases hf
      · rcases zw_dec E l with hZ | hZ
        · exact .inl hZ
        · exact absurd h (hz hZ)
    · right
      have : E.ini l ≤ E.rc l := Nat.le_of_not_lt hlt
      exact Nat.le_trans this (Nat.min_le_right _ _)

/-- (D+ (β)) `NoHold` at a seen own cell, from `MemInv`. -/
theorem noHold_seen {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} (hm : MemInv g E s)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hs : E.seen l) : NoHold E s l := by
  refine ⟨fun _ _ hns => absurd hs hns, (pubWin_ab hm hsto hown (.inr hs)).2, fun hn u => ?_⟩
  obtain ⟨f, hf, -⟩ := hm.2.2.2.2.1 l hs
  rw [hn] at hf; cases hf

/-- (D+) `NoHold` at an own cell, from `MemInv` and `NoHold` under `¬ seen`, with no case split on
`seen`: (a) needs `¬ seen`; (b) is `ZW`, or the real count is reached, or (`rc < ini`, not `ZW`)
`OwnHidP.2` gives `¬ seen`; (c) a frontier-free cell is not seen (`MemInv`'s `seen` frontier). -/
theorem noHold_own {g : G} {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} (hm : MemInv g E s)
    (hsto : E.sto l = some c) (hown : c.owner = some E.tid) (hN : ¬ E.seen l → NoHold E s l) :
    NoHold E s l := by
  refine ⟨fun f hf hns => (hN hns).1 f hf hns, ?_, fun hn u => ?_⟩
  · rcases zw_dec E l with hZ | hZ
    · exact .inl hZ
    · by_cases hlt : E.rc l < E.ini l
      · obtain ⟨f, hf, hz, -⟩ := hm.2.2.2.2.2.1.2 l c hsto hown hlt
        exact (hN (hz hZ)).2.1
      · right
        have : E.ini l ≤ E.rc l := Nat.le_of_not_lt hlt
        exact Nat.le_trans this (Nat.min_le_right _ _)
  · have hns : ¬ E.seen l := fun hs => by
      obtain ⟨f, hf, -⟩ := hm.2.2.2.2.1 l hs
      rw [hn] at hf; cases hf
    exact (hN hns).2.2 hn u

/-- (D+) **The bridge**: `NoHoldPubN` (unseen publishes) gives `NoHoldPubA` (every publish); a seen
publish is discharged by `noHold_seen` at the typing's `MemInv`. -/
theorem noHoldPubA_of_N {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 E1 : TEnv} {i : Nat} {c : Cfg}
    (h : NoHoldPubN p k arch E0 E1 i c) : NoHoldPubA p k arch E0 E1 i c := by
  intro th hth ρ η cx hE hT htv hi hm hx hia hrm hTy hDy hRP
  have hN := h th hth ρ η cx hE hT htv hi hm hx hia hrm hTy hDy hRP
  refine ⟨fun x a e rt ws ad hterm hea hws => ?_, fun a rn pn tn e rt ws ad hterm hea hws => ?_,
    fun x rn a e rt ws ad hterm hea hws => ?_⟩
  · obtain ⟨cl, hc, ho⟩ := TermPubSto.pubSto_of_typed hT.1 hi hterm hea hws
    exact noHold_own hm hc ho (hN.1 x a e rt ws ad hterm hea hws)
  · -- a seen `region` (as `TermC1.rgn_noHold_seen`)
    have hT' := hT.1
    rw [hterm] at hT'
    obtain ⟨cl, hc, ho⟩ : ∃ c, (CE η).sto ad.label = some c ∧ c.owner = some (CE η).tid := by
      cases hT' with
      | region hu _ _ _ _ => exact TermPubSto.ownSto_of_use hu hi hea hws
      | regionBuf hu _ _ _ _ => exact TermPubSto.ownBufSto_of_use hu hi hea hws
    exact noHold_own hm hc ho (hN.2.1 a rn pn tn e rt ws ad hterm hea hws)
  · -- a seen `intoRgn` (as `TermC1.into_noHold_seen`)
    have hT' := hT.1
    rw [hterm] at hT'
    obtain ⟨cl, hc, ho⟩ : ∃ c, (CE η).sto ad.label = some c ∧ c.owner = some (CE η).tid := by
      cases hT' with
      | let_ hop _ =>
      cases hop with
      | intoRgn _ hu _ _ => exact TermPubSto.ownSto_of_use hu hi hea hws
      | intoRgnBuf _ hu _ _ => exact TermPubSto.ownBufSto_of_use hu hi hea hws
    exact noHold_own hm hc ho (hN.2.2 x rn a e rt ws ad hterm hea hws)

end TermDPlus

#print axioms TermDPlus.pubWin_ab
#print axioms TermDPlus.noHold_seen
#print axioms TermDPlus.zw_dec
#print axioms TermDPlus.noHold_own
#print axioms TermDPlus.noHoldPubA_of_N

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
      · by_cases hZ : ZW E l
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

/-- (D+) **The bridge**: `NoHoldPubN` (unseen publishes) gives `NoHoldPubA` (every publish); a seen
publish is discharged by `noHold_seen` at the typing's `MemInv`. -/
theorem noHoldPubA_of_N {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 E1 : TEnv} {i : Nat} {c : Cfg}
    (h : NoHoldPubN p k arch E0 E1 i c) : NoHoldPubA p k arch E0 E1 i c := by
  intro th hth ρ η cx hE hT htv hi hm hx hia hrm hTy hDy hRP x a e rt ws ad hterm hea hws
  by_cases hs : (CE η).seen ad.label
  · obtain ⟨cl, hc, ho⟩ := TermPubSto.pubSto_of_typed hT hi hterm hea hws
    exact noHold_seen hm hc ho hs
  · exact h th hth ρ η cx hE hT htv hi hm hx hia hrm hTy hDy hRP x a e rt ws ad hterm hea hws hs

end TermDPlus

#print axioms TermDPlus.pubWin_ab
#print axioms TermDPlus.noHold_seen
#print axioms TermDPlus.noHoldPubA_of_N

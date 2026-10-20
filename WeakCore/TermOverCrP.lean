import WeakCore.TermOverCrN

/-! # TermOverCrP: a plant-credit target for a newly overtaken piece (hcovD O2)

The lowest own promise of a piece (below a window bound that clears the foreign promises at
the cell) is a plant credit there with the empty unit mask, for any credit holding a value of
the piece; the target choice then finds a target.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A least element of a nonempty predicate on `Nat`. -/
theorem exists_min_nat {P : Nat → Prop} : ∀ n, P n → ∃ k, P k ∧ ∀ j, P j → k ≤ j
  | n, h => by
      classical
      by_cases hex : ∃ j, j < n ∧ P j
      · obtain ⟨j, hj, hP⟩ := hex
        exact exists_min_nat j hP
      · exact ⟨n, h, fun j hj => Nat.le_of_not_lt fun hlt => hex ⟨j, hlt, hj⟩⟩
  termination_by n => n

#print axioms exists_min_nat

/-- **The empty-mask plant credit**: the lowest own window promise of a non-word solid piece
of an own frontier cell carries any credit covering a value of the piece. -/
theorem plantCr_mk {E : TEnv} {s : St} {m : Msg} {t wb : Ts} {R R0 : Res} {c : Cell} {sb b0 : Nat}
    {S0 S : Ty} {us : List Acc} {ws : List Word}
    (hsto : E.sto m.loc.label = some c) (hown : c.owner = some E.tid) (hpf : E.pfr m.loc.label ≠ none)
    (hseg : SegOf c.ty sb S0) (hat : AtOff S0 b0 S) (hS : Solid S) (hnw : ¬ WordUnit E m.loc)
    (hus : accs S = some us) (hn : 0 < nWords us)
    (h1 : sb + b0 ≤ m.loc.offset) (h2 : m.loc.offset < sb + b0 + nWords us) (htw : t ≤ wb)
    (hwb : wb < s.mem.size)
    (hfp : ∀ tf mf, tf ∈ FpAt E ⟨m.loc.label, 0⟩ → s.mem[tf]? = some mf → mf.loc.label = m.loc.label → wb < tf)
    (hlow : ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = m.loc.label →
      sb + b0 ≤ m'.loc.offset → m'.loc.offset < sb + b0 + nWords us → t' ≤ wb → t ≤ t')
    (hwl : ws.length = nWords us) (hv : ValOfR E S ws R0) (hR : R0 ≤ R) :
    PlantCr E s m t R :=
  ⟨c, sb, S0, b0, S, us, wb, hsto, hown, hpf, hseg, hat, hS, hnw, hus, hn, h1, h2, htw, hwb, hfp, hlow,
    Or.inl ⟨fun _ => false, ws, R0, hwl, hv, hR, fun i _ _ _ hK => by cases hK⟩⟩

#print axioms plantCr_mk

/-- **The lowest own promise of a piece** exists once one does. -/
theorem lowest_in_piece {s : St} {l : AllocLabel} {lo hi : Nat} {tw : Ts} {mw : Msg}
    (ht : tw ∈ s.promises) (hm : s.mem[tw]? = some mw) (hl : mw.loc.label = l)
    (h1 : lo ≤ mw.loc.offset) (h2 : mw.loc.offset < hi) :
    ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc.label = l ∧ lo ≤ m.loc.offset ∧
      m.loc.offset < hi ∧ t ≤ tw ∧
      ∀ t' m', t' ∈ s.promises → s.mem[t']? = some m' → m'.loc.label = l → lo ≤ m'.loc.offset →
        m'.loc.offset < hi → t ≤ t' := by
  obtain ⟨k, ⟨m, hk, hmk, hlk, h1k, h2k⟩, hmin⟩ := exists_min_nat
    (P := fun n => ∃ m, n ∈ s.promises ∧ s.mem[n]? = some m ∧ m.loc.label = l ∧ lo ≤ m.loc.offset ∧
      m.loc.offset < hi) tw ⟨mw, ht, hm, hl, h1, h2⟩
  exact ⟨k, m, hk, hmk, hlk, h1k, h2k, hmin tw ⟨mw, ht, hm, hl, h1, h2⟩,
    fun t' m' ht' hm' hl' h1' h2' => hmin t' ⟨m', ht', hm', hl', h1', h2'⟩⟩

#print axioms lowest_in_piece

/-- **The target choice finds a target** when some candidate qualifies. -/
theorem tgIn_isSome {α : Type} {F : List Ts} {P : α → Ts → Prop} {g : α} {t : Ts}
    (ht : t ∈ F) (hP : P g t) : ∃ t', TermPlant.tgIn F P g = some t' := by
  classical
  unfold TermPlant.tgIn
  cases h : F.find? (fun t => decide (P g t)) with
  | none =>
      have := List.find?_eq_none.1 h t ht
      simp only [decide_eq_true_eq] at this
      exact absurd hP this
  | some t' => exact ⟨t', rfl⟩

#print axioms tgIn_isSome

end TermOverCrW

import WeakCore.TermAffAt
import WeakCore.TermOwnCR5

/-! # TermOwnCLoad: ownC (iii), an own load newly guarding a unit

* `valOfR_copy_zero`: a non-affine type's values carry no resources (any `ValOfR`).
* `atOff_tb`: components of a closed type are closed.
* `load_piece_affine`: a piece meeting a loaded component lies inside it (`AtOff_nest`), so it is
  non-affine (`TermAffAt.affine_loadCell`).
-/

namespace TermOwnCLoad

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **Copyable values are resource-free**: no closedness needed (`KEnv.ask []` is `false`). -/
theorem valOfR_copy_zero {E : TEnv} {U : Ty} {ws : List Word} {R : Res}
    (ha : Ty.affine U = false) (h : ValOfR E U ws R) : R = .zero :=
  VRR_copy_zero U [] _ _ _ ws R ha (fun k hk => by simp [KEnv.ask] at hk)
    (fun k hk => by simp [KEnv.ask] at hk) h.1

#print axioms valOfR_copy_zero

/-- **Components of a closed type are closed.** -/
theorem atOff_tb {T U : Ty} {o : Nat} (h : AtOff T o U) : tb 0 T = true → tb 0 U = true := by
  induction h with
  | here _ => exact id
  | fst _ ih => intro hT; simp only [tb, Bool.and_eq_true] at hT; exact ih hT.1
  | snd _ _ ih => intro hT; simp only [tb, Bool.and_eq_true] at hT; exact ih hT.2
  | elem _ _ _ ih => intro hT; simp only [tb] at hT; exact ih hT
  | mu hW _ _ ih => intro _; exact ih (Clo_cl hW _ _).1
  | fold hW _ _ _ _ => intro _; exact (Clo_cl hW _ _).1

#print axioms atOff_tb

/-- **A piece meeting a loaded component is inside it** (`AtOff_nest`). -/
theorem piece_in_comp {T U V : Ty} {b q : Nat} {us vs : List Acc}
    (hU : AtOff T b U) (hus : accs U = some us) (hV : TermPiece.Piece T q V) (hvs : accs V = some vs)
    (h1 : q < b + nWords us) (h2 : b < q + nWords vs) : b ≤ q ∧ AtOff U (q - b) V := by
  rcases AtOff_nest hV.2.1 hvs hU hus hV.1 with h | h | h
  · omega
  · omega
  · exact h

#print axioms piece_in_comp

/-- **A piece meeting a loaded component is non-affine**: the load's pointee `u` is non-affine,
the component folds its closure (`Fd`), and the piece is a component of the component. -/
theorem load_piece_affine {ρ : Nat → Nat} {W : Nat → Ty} (hW : ∀ k, Clo (W k)) {ke : KEnv}
    {T U V u : Ty} {b q : Nat} {us vs : List Acc}
    (hWk : ∀ k, k < ke.length → ke.ask k true (·.copy) = true → Ty.affine (W k) = false)
    (hu : Ty.affineIn ke u = false) (htb : tb ke.length u = true) (hF : Fd U (cl ρ W 0 0 u))
    (hUo : AtOff T b U) (hus : accs U = some us) (hV : TermPiece.Piece T q V) (hvs : accs V = some vs)
    (h1 : q < b + nWords us) (h2 : b < q + nWords vs) : Ty.affine V = false :=
  TermAffAt.affine_loadCell hW hWk hu htb hF (piece_in_comp hUo hus hV hvs h1 h2).2

#print axioms load_piece_affine

end TermOwnCLoad

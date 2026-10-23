import WeakCore.TermC1Inv

/-! # TermC1Ptr: region pointers as payloads under `ModeOK1` (D-4, G5)

Under c1 a region reference is held to the `pub` clause (`ModeOK1`), so a region pointer inside a
published or region cell moves between environments exactly like a `pub` one (`TermCut.ModeOK_pub_move`).
The facts here are what the switch needs at `VR_transferS`'s reference arms once `noOR` is `noOR1`.
-/

namespace TermC1

open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep TermCut
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A reference mode `noOR1` admits: `pub`, or (pointers only) a region. -/
theorem noOR1_ptr {μ : Mode} {u : Ty} (h : noOR1 (.ptr μ u) = true) : μ ≠ .own := by
  cases μ <;> simp_all [noOR1]
theorem noOR1_ptrOpt {μ : Mode} {u : Ty} (h : noOR1 (.ptrOpt μ u) = true) : μ ≠ .own := by
  cases μ <;> simp_all [noOR1]
theorem noOR1_loc {μ : Mode} {u : Ty} (h : noOR1 (.loc μ u) = true) : μ = .pub := by
  cases μ <;> simp_all [noOR1]

/-- Off `own`, `ModeOK1` is the `pub` clause. -/
theorem ModeOK1_eq_pub {μ : Mode} (hμ : μ ≠ .own) (i : Nat) (P : AllocLabel → Option Ts)
    (S : AllocLabel → Prop) : ModeOK1 i P S μ = ModeOK i P S .pub := by
  cases μ with
  | own => exact absurd rfl hμ
  | pub => rfl
  | rgn _ => rfl

/-- Off `own`, `ModeOK1` gives the cell a frontier (what `VR_transferS`'s `hs` premise reads). -/
theorem ModeOK1_pfr {μ : Mode} (hμ : μ ≠ .own) {i : Nat} {P : AllocLabel → Option Ts} {S : AllocLabel → Prop}
    {l : AllocLabel} {c : Cell} {ws : List Word} (h : ModeOK1 i P S μ l c ws) : ∃ f, P l = some f := by
  rw [ModeOK1_eq_pub hμ] at h; exact ModeOK_pub_pfr h

/-- Off `own`, `ModeOK1` moves to another thread id and larger frontier/seen maps. -/
theorem ModeOK1_move {μ : Mode} (hμ : μ ≠ .own) {i j : Nat} {P P' : AllocLabel → Option Ts}
    {S S' : AllocLabel → Prop}
    (hP : ∀ l f, P l = some f → P' l = some f) (hS : ∀ l, S l → S' l) {l : AllocLabel} {c c' : Cell}
    {ws : List Word} (h : ModeOK1 i P S μ l c ws) : ModeOK1 j P' S' μ l c' ws := by
  rw [ModeOK1_eq_pub hμ] at h ⊢; exact ModeOK_pub_move hP hS h

/-- `ModeOK1_move` at one label (the `VR_transferL` form, `TermCut.ModeOK_pub_moveL`). -/
theorem ModeOK1_moveL {μ : Mode} (hμ : μ ≠ .own) {i j : Nat} {P P' : AllocLabel → Option Ts}
    {S S' : AllocLabel → Prop} {l : AllocLabel} (hP : ∀ f, P l = some f → P' l = some f)
    (hS : ∀ l, S l → S' l) {c c' : Cell} {ws : List Word} (h : ModeOK1 i P S μ l c ws) :
    ModeOK1 j P' S' μ l c' ws := by
  rw [ModeOK1_eq_pub hμ] at h ⊢; exact ModeOK_pub_moveL hP hS h

/-- Off `own`, `ModeOK1` is `ModeOK .pub`: `hmo` at a pointer the `VR` arm gives. -/
theorem ModeOK1_toPub {μ : Mode} (hμ : μ ≠ .own) {i : Nat} {P : AllocLabel → Option Ts}
    {S : AllocLabel → Prop} {l : AllocLabel} {c : Cell} {ws : List Word}
    (h : ModeOK1 i P S μ l c ws) : ModeOK i P S .pub l c ws := by
  rw [ModeOK1_eq_pub hμ] at h; exact h

end TermC1

#print axioms TermC1.noOR1_ptr
#print axioms TermC1.noOR1_ptrOpt
#print axioms TermC1.noOR1_loc
#print axioms TermC1.ModeOK1_eq_pub
#print axioms TermC1.ModeOK1_pfr
#print axioms TermC1.ModeOK1_move
#print axioms TermC1.ModeOK1_moveL
#print axioms TermC1.ModeOK1_toPub

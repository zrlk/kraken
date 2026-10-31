import WeakCore.TvarB
/-! Route (D): hand header of the generated slice (counted as hand lines). -/
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-- The generated layer's `ModeOK`: `ModeOKb` at flag `False` (what VRB's `.ptr`/`.tid` arms give). -/
def ModeOKB (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) :
    Mode → WeakMem.AllocLabel → Cell → List Word → Prop := ModeOKb i P S False

/-- R6: the flag-generic forms of `VR`/`ModeOK` used by the generated slice. -/
abbrev VRF (bk : Prop) (ρ : Nat → Nat) (η : TEnv) : Ty → Shp → List Word → Prop := VRb2 ρ η bk
abbrev ModeOKF (bk : Prop) (i : Nat) (P : WeakMem.AllocLabel → Option WeakMem.Ts) (S : WeakMem.AllocLabel → Prop) :
    Mode → WeakMem.AllocLabel → Cell → List Word → Prop := ModeOKb i P S bk

/-- **The supply.**  Thread `i`'s fresh-label progression at geometry `(lb, n)` is
blank above some `b` (sto/box/ini/rini/pfr/seen), and no box payload mentions it.  Field for field the EtaB
`FreshSup` at `P.base = lb`, `P.n = n`, `P.i = i`. -/
def SupI (lb n i : Nat) (η : TEnv) : Prop :=
  ∃ b, (∀ k, b ≤ k →
      η.sto (freshLabel lb n i k) = none ∧ η.box (freshLabel lb n i k) = none ∧
      η.ini (freshLabel lb n i k) = 0 ∧ η.rini (freshLabel lb n i k) = 0 ∧
      η.pfr (freshLabel lb n i k) = none ∧ ¬ η.seen (freshLabel lb n i k)) ∧
    ∀ x B, η.box x = some B → ∀ w ∈ B.pay, ∀ a g, w.val = .loc a g →
      ∀ k, b ≤ k → a.label ≠ freshLabel lb n i k


/-- `SupI` reads only `CE`-fields. -/
theorem SupI_CE_eq {lb n i : Nat} {η₁ η₂ : TEnv} (h : CE η₁ = CE η₂) (hs : SupI lb n i η₂) :
    SupI lb n i η₁ := by
  have h2 : SupI lb n i (CE η₂) := hs
  rw [← h] at h2; exact h2

end TermSound.Flat
namespace TermMem.Flat
def anchorTM : Unit := ()
end TermMem.Flat
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
/-- ♭ model of W `FreshLP` in the (iii) form (with `rini`), under the ♭ name `FreshLPA`;
body and docstring verbatim.  W's `FreshLP` has the same clause, so `FreshLPA = FreshLP` by `rfl` (below) and the
♭ name can be retired.
Every label the thread has yet to allocate is untouched: not in Σ, (S4)
with no message in memory other than the thread's own promises, (T3c-5b) with
no slot counted initialised or read-initialised, and (M3) with no frontier.  (privSlot) Memory the
owner has not initialised: `PrivCoh`. -/
def FreshLPA (g : G) (E : TEnv) (s : St) : Prop :=
  (∀ j, s.nalloc ≤ j →
    E.sto (freshLabel g.lbase g.n g.i j) = none ∧
    (∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label = freshLabel g.lbase g.n g.i j → t ∈ s.promises) ∧
    E.ini (freshLabel g.lbase g.n g.i j) = 0 ∧ E.rini (freshLabel g.lbase g.n g.i j) = 0 ∧
    E.pfr (freshLabel g.lbase g.n g.i j) = none) ∧
  PrivCoh E s

/-- `FreshLPA` gives W's `FreshLP` (the two are equal). -/
theorem FreshLPA.old {g : G} {E : TEnv} {s : St} (h : FreshLPA g E s) : FreshLP g E s := h

/-- The ♭ model is W's `FreshLP` on the nose. -/
example : FreshLPA = FreshLP := rfl

/-- ♭ `FreshLP_store` for `FreshLPA` (W TermStep:5385 plus the rini frame clause). -/
theorem FreshLPA_store {g : G} {E E' : TEnv} {s s' : St} {lab : AllocLabel} {c : Cell} (h : FreshLPA g E s)
    (hsto : E.sto lab = some c) (hg : GrowsAt s.mem s'.mem lab) (hna : s'.nalloc = s.nalloc)
    (hful : ∀ t, t ∈ s.promises → t ∉ s'.promises → ∃ m, s.mem[t]? = some m ∧ m.loc.label = lab)
    (hE : ∀ l, l ≠ lab → E'.sto l = E.sto l ∧ E'.ini l = E.ini l ∧ E'.rini l = E.rini l ∧ E'.pfr l = E.pfr l)
    (hpc : PrivCoh E' s') : FreshLPA g E' s' :=
  FreshLP_store (g := g) h hsto hg hna hful hE hpc
end
def anchorTS : Unit := ()
end TermStep.Flat

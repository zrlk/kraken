import WeakCore.TermInterf
namespace TermPlantFrz
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermStepper TermInterf TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (B3, planted half) **A thread step keeps the count of every shared
cell whose count is still ahead of its real count** (`¬ ini ≤ rini`): the footprint's
frozen clause (`EFoot`, ini, own disjunct). -/
theorem plantFrozen_planted {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} (hsh : Eg.Shared l) (hlt : ¬ Eg.ini l ≤ Eg.rini l) :
    (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l = Eg.ini l := by
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  show E'.ini l = Eg.ini l
  rcases (hF0.2.2.2.2.1 l).2 with e | hF | ⟨-, -, hz⟩
  · exact e
  · obtain ⟨f, hf⟩ := hsh; rw [(hfr l hF).2.2] at hf; cases hf
  · obtain ⟨f, hf⟩ := hsh
    rcases hz (by show Eg.pfr l ≠ none; rw [hf]; simp) with e | e
    · exact e
    · exact absurd e hlt

/-- (B3, G4) **The residual of `PlantFrozen`: its published half.** A thread step
keeps the count of each of its own shared cells whose count is not ahead of its real
count (`ini ≤ rini`).  The planted half (`¬ ini ≤ rini`) is `plantFrozen_planted`. -/
def PlantFrozenPubF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ l, Eg.OwnAt i l → Eg.Shared l → Eg.ini l ≤ Eg.rini l →
      (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l = Eg.ini l

/-- (B3, G4) **`PlantFrozenF` from its published half**: the planted half is
the footprint's frozen clause (`plantFrozen_planted`). -/
theorem plantFrozenF_of (h : PlantFrozenPubF p k arch Sp Init MintOK c0) : PlantFrozenF p k arch Sp Init MintOK c0 :=
  by
    intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z l ho hsh
    by_cases hle : Eg.ini l ≤ Eg.rini l
    · exact h X Y Z l ho hsh hle
    · exact plantFrozen_planted X Y Z hsh hle

/-- (plantFrozen −1) **The published half of `PlantFrozen` from `IniFixZ`** at the ghost labels
`pfr ≠ none ∧ ini ≤ rini`: an own shared cell with `ini ≤ rini` is not fresh (`gfresh`), is in the
cut, and has a frontier, so the footprint keeps its count. -/
theorem plantFrozenPub_of_iniFix {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hK : IniFixZ { gOf p k arch c i with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l }
      (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2)) :
    ∀ l, Eg.OwnAt i l → Eg.Shared l → Eg.ini l ≤ Eg.rini l →
      (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l = Eg.ini l := by
  intro l ho hsh hle
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  show E'.ini l = Eg.ini l
  obtain ⟨cl, hcl, hown⟩ := ho
  obtain ⟨f, hf⟩ := hsh
  rw [Y.1] at hK
  have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
    rw [(hfr l hF).2.2] at hf; cases hf
  have hc : (Cut Eg i S).sto l = some cl := cutSto_some.2 ⟨hcl, .inl hown⟩
  have hz : (Cut Eg i S).pfr l ≠ none ∧ (Cut Eg i S).ini l ≤ (Cut Eg i S).rini l :=
    ⟨by show Eg.pfr l ≠ none; rw [hf]; simp, hle⟩
  exact (hK l cl f hz hnf hc hf).1

/-- (plantFrozen −1) **`PlantFrozenPubF` holds**: the TOut conjunct `IniFixZ` (H3) at every step. -/
theorem plantFrozenPub_holds : PlantFrozenPubF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hK, -⟩ := Z
  exact plantFrozenPub_of_iniFix X Y hK

end
end TermPlantFrz

#print axioms TermPlantFrz.plantFrozen_planted
#print axioms TermPlantFrz.plantFrozenF_of
#print axioms TermPlantFrz.plantFrozenPub_of_iniFix
#print axioms TermPlantFrz.plantFrozenPub_holds

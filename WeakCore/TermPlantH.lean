import WeakCore.TermPlantP

/-!
# TermPlantH: `selfPlantRest` narrowed to the (H) classes

`TermPlantS.SelfPlantRestF` (the `selfPlant` field at events planting a label with new slots that
is neither a word buffer nor a `UnitT` buffer) follows from `SelfPlantRestHF`, which keeps only the
two classes of planted buffers that (H) is for.  Every other new-slot plant is vacuous or handled
by `TermPlantS.ThSys_plantS`:
* a non-array cell has no slots (`NpZ ≤ slotCnt = 0`);
* a buffer of elements without a layout is not a cell type (`LayT`, `plant_facts`);
* a buffer with a `.two` unit is never raised (`TermPlantP.plantN_two`);
* a buffer of zero-width elements is `UnitT` (raised at once by `ThSysAt_plantS`, whose new slots
  carry nothing: `HeldEntry_raiseZ`);
* a non-affine element is `dwf` (`dwf_of_affine`), so a non-affine element of nonzero width whose
  skeleton is `μ`-free (`SkFree`) or whose `μ` bodies are all guarded (`mg`; zero-width components
  found through guarded unfoldings, `TermBlkZ.zwl_existsM`) is `UnitT`.
-/

namespace TermPlantH

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The two (H) classes of a planted buffer with all-`.one` element layout `us`:
(R1) a resourceful (affine) element of nonzero width, not a single protocol word;
(R2) a resource-free element of nonzero width whose pair skeleton has a `μ` and which has an
unguarded `μ` body (`mg = false`: not a well-formed type). -/
def HClass (T e : Ty) (us : List Acc) : Prop :=
  (us ≠ [] ∧ Ty.affineIn [] e = true ∧ ¬ WordBufT T) ∨
  (us ≠ [] ∧ Ty.affineIn [] e = false ∧ TermBlkZ.SkFree e = false ∧ TermTv.mg e = false)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (residual, **selfPlantRest** narrowed to (H)) `selfPlant` at events planting, with new slots, a
buffer of all-`.one` element layout in one of the (H) classes `HClass`. -/
def SelfPlantRestHF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∃ l f cl N e us, TermPlantF.plantOf c Eg j a v w l = some f ∧ ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l ∧
      Eg.sto l = some cl ∧ cl.ty = .array (.lit N) e ∧ accs e = some us ∧ (∀ u ∈ us, u = Acc.one) ∧
      HClass cl.ty e us) →
    ∃ HP' HS' cr' db', PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db' ∧
      ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
        (EgP Eg (TermPlantF.plantOf c Eg j a v w) (TermPlantF.plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db'

/-- The maximal held prefix is within the cell's slot count. -/
theorem Np_le_slot {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} (hc : E.sto l = some c) :
    Np E s l ≤ slotCnt c := by
  classical
  rw [Np_of hc]
  rcases foldr_max_mem ((List.range (slotCnt c + 1)).filter fun n =>
      @decide (PrefixHeld E s l c n) (Classical.propDecidable _)) with h | h
  · rw [h]; exact Nat.zero_le _
  · have := List.mem_range.1 (List.mem_filter.1 h).1
    omega

theorem NpZ_le_slot {E : TEnv} {s : St} {l : AllocLabel} {c : Cell} (hc : E.sto l = some c) :
    NpZ E s l ≤ slotCnt c := by
  by_cases h : EmptyZ E l
  · rw [NpZ_of_empty h]; exact Nat.zero_le _
  · rw [NpZ_of_not h]; exact Np_le_slot hc

/-- **The classification**: a label planted with new slots that is neither a word buffer nor a
`UnitT` buffer is in an (H) class. -/
theorem hclass_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} {f : Ts} {cl : Cell} (hf : TermPlantF.plantOf c Eg j a v w l = some f)
    (hno : ¬ TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l) (hcl : Eg.sto l = some cl)
    (hW : ¬ WordBufT cl.ty) (hU : ¬ UnitT cl.ty) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ N e us, cl.ty = .array (.lit N) e ∧ accs e = some us ∧ (∀ u ∈ us, u = Acc.one) ∧
      HClass cl.ty e us := by
  obtain ⟨hPL, -⟩ := TermPlantF.plantOf_some X.hth hf
  obtain ⟨l', -, hR⟩ := id hPL
  obtain ⟨cl2, hc2, ho2, -, hLay, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hc2; cases hc2
  have hcP : (TermPlantF.cutP Eg j).sto l = some cl := by
    obtain ⟨-, -, t1, -, m1, -, -, -, a1, g1, -, hal, cl1, hc1, -, -⟩ := hPL
    have e := cutSto_sub hc1
    rw [hcl] at e; cases e; exact hc1
  have hN : TermPlantF.plantN c Eg j a v w l = NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l := by
    simp only [TermPlantF.plantN, X.hth]
  -- an array
  obtain ⟨N, e, hT⟩ : ∃ N e, cl.ty = .array (.lit N) e := by
    apply Classical.byContradiction; intro hne
    have h0 : slotCnt cl = 0 := by
      unfold slotCnt; split
      · rename_i Na e' he; exact absurd ⟨Na, e', he⟩ hne
      · rfl
    have := NpZ_le_slot (s := stOf c.mem c.pairs th) hcP
    rw [h0, ← hN] at this; omega
  -- with a layout
  obtain ⟨us, hus⟩ : ∃ us, accs e = some us := by
    rcases hLay with h | ⟨n, e', hT', h⟩
    · rw [hT] at h; simp [accs] at h
    · rw [hT] at hT'; simp only [Ty.array.injEq, Idx.lit.injEq] at hT'; obtain ⟨-, rfl⟩ := hT'
      exact Option.ne_none_iff_exists'.1 h
  -- of `.one` units
  have hone : ∀ u ∈ us, u = Acc.one := by
    intro u hu
    cases u with
    | one => rfl
    | two =>
      obtain ⟨i, hi, e2⟩ := List.getElem_of_mem hu
      exact absurd (TermPlantP.plantN_two (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hf hcl hT hus (i := i) (by rw [List.getElem?_eq_getElem hi, e2]))
        hno
  refine ⟨N, e, us, hT, hus, hone, ?_⟩
  by_cases hnil : us = []
  · -- zero width: `UnitT`
    exact absurd ⟨N, e, us, hT, hus, hone, .inl hnil⟩ hU
  · cases hA : Ty.affineIn [] e with
    | true => exact .inl ⟨hnil, hA, hW⟩
    | false =>
      cases hS : TermBlkZ.SkFree e with
      | true => exact absurd ⟨N, e, us, hT, hus, hone, .inr ⟨hnil, hA, dwf_of_affine e [] hA, .inl hS⟩⟩ hU
      | false =>
      cases hM : TermTv.mg e with
      | true => exact absurd ⟨N, e, us, hT, hus, hone, .inr ⟨hnil, hA, dwf_of_affine e [] hA, .inr hM⟩⟩ hU
      | false => exact .inr ⟨hnil, hA, hS, hM⟩

/-- **`SelfPlantRestF` from the (H)-narrowed residual.** -/
theorem selfPlantRest_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hH : SelfPlantRestHF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : TermPlantS.SelfPlantRestF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X ⟨l, f, cl, hf, hno, hcl, hW, hU⟩
  obtain ⟨N, e, us, hT, hus, hone, hC⟩ := hclass_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hf hno hcl hW hU
  exact hH X ⟨l, f, cl, N, e, us, hf, hno, hcl, hT, hus, hone, hC⟩

end

end TermPlantH

#print axioms TermPlantH.Np_le_slot
#print axioms TermPlantH.hclass_of
#print axioms TermPlantH.selfPlantRest_of

import WeakCore.TermPromClos
import WeakCore.TermPtrStab

/-! # TermCellOwn: the `SysInvN` clause `cellOwn` (`CellOwnerLiveM`)

The clause (`TermMain.CellOwnerLiveM`): a cell of `E_g` holding a message, or shared, is owned
by a live thread, or, ownerless, is shared.
* init: memory is empty and no label has a frontier (`cellOwn_init`);
* thread step (`cellOwn_thread`): a cell of `E_g` is kept (`GFoot`), with frontiers only growing (a
  new frontier at a cell of the stepper), or is a fresh cell of the stepper; a new message lies at a
  fresh label of the stepper or in its cut (`tstep_writeAt`): a cell it owns or a shared one;
* promise step (`cellOwn_prom`): `E_g`'s cells are untouched, a plant is at a cell of the promiser
  (`PlantSpec`), and the new message lies in the promiser's cut or at a label holding no cell
  (`PromLocF`'s disjunction).
-/

namespace TermCellOwn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain TermInterf TermPromClos TermPtrRts TermPtrStab
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- The consumer form (`TermPtrStab.CellOwnerLive` at labels holding a message). -/
theorem cellOwn_use {Eg : GEnv} {c : Cfg} (h : CellOwnerLiveM Eg c) {l : AllocLabel} {cl : Cell}
    (hl : Eg.sto l = some cl) {t : Nat} {m : Msg} (hm : c.mem[t]? = some m) (e : m.loc.label = l) :
    (∀ i, cl.owner = some i → i < c.ths.size) ∧ (cl.owner = none → Eg.Shared l) :=
  h l cl hl (.inl ⟨t, m, hm, e⟩)

/-- Initially (empty memory, no frontier) the clause holds. -/
theorem cellOwn_init {Eg : GEnv} {c : Cfg} (h : c.mem = #[]) (hp : ∀ l, Eg.pfr l = none) :
    CellOwnerLiveM Eg c := by
  intro l cl _ hg
  rcases hg with ⟨t, m, hm, _⟩ | ⟨f, hf⟩
  · rw [h] at hm
    cases hm
  · rw [hp l] at hf
    cases hf

/-- A cell owned by a live thread has the clause's conclusion. -/
theorem fin_own {Eg : GEnv} {n : Nat} {l : AllocLabel} {cl : Cell} {i : Nat} (ho : cl.owner = some i)
    (hi : i < n) : (∀ i', cl.owner = some i' → i' < n) ∧ (cl.owner = none → Eg.Shared l) :=
  ⟨fun i' h => by rw [ho] at h; cases h; exact hi, fun h => by rw [ho] at h; cases h⟩

/-- The clause's conclusion moves along a frontier-growing map with at least as many threads. -/
theorem fin_mono {Eg Eg' : GEnv} {n n' : Nat} {l : AllocLabel} {cl : Cell}
    (hp : ∀ f, Eg.pfr l = some f → ∃ f', Eg'.pfr l = some f') (hn : n ≤ n')
    (h : (∀ i, cl.owner = some i → i < n) ∧ (cl.owner = none → Eg.Shared l)) :
    (∀ i, cl.owner = some i → i < n') ∧ (cl.owner = none → Eg'.Shared l) :=
  ⟨fun i hi => Nat.lt_of_lt_of_le (h.1 i hi) hn, fun ho => let ⟨f, hf⟩ := h.2 ho; hp f hf⟩

/-- At a cell of a live thread's cut (owned by it, or shared) the clause's conclusion holds. -/
theorem fin_cut {Eg : GEnv} {c : Cfg} (hF : CellOwnerLiveM Eg c) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) {l : AllocLabel} {cl : Cell} (h : cutSto Eg i l = some cl) :
    (∀ i', cl.owner = some i' → i' < c.ths.size) ∧ (cl.owner = none → Eg.Shared l) := by
  rcases (cutSto_some.1 h).2 with ho | hs
  · exact fin_own ho (TermCert.arr_lt hth)
  · exact hF l cl (cutSto_some.1 h).1 (.inr hs)

/-- `TermPtrStab.NonPromLbl` from `SysInvN` and `cellOwn` (the guarded form of
`TermPtrStab.nonPromLbl_of`: the plant-edge message sits at the cell). -/
theorem nonPromLbl_ofM {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (X : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hCO : CellOwnerLiveM Eg c)
    {j : Nat} {th : TTh} (hth : c.ths[j]? = some th) : NonPromLbl Eg c := by
  intro u m L hmu hE hall
  obtain ⟨⟨ca, hca, -, -⟩, -⟩ := id hE
  obtain ⟨hlive, hsh⟩ := hCO _ ca hca (.inl ⟨u, m, hmu, rfl⟩)
  cases ho : ca.owner with
  | some i =>
    have hi := hlive i ho
    have hthi : c.ths[i]? = some c.ths[i] := Array.getElem?_eq_getElem hi
    exact plantEdge_lbl_of_thSys (X.thr i _ hthi) (hall i _ hthi) hmu hE
      (fun ca' h => by rw [hca] at h; cases h; exact Or.inl ho)
  | none =>
    exact plantEdge_lbl_of_thSys (X.thr j th hth) (hall j th hth) hmu hE
      (fun _ _ => Or.inr (hsh ho))

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **A thread step keeps `cellOwn`.** -/
theorem cellOwn_thread
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (hF : CellOwnerLiveM Eg c) :
    CellOwnerLiveM (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  have hgf := gfoot_of X Y Z
  have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
  have hi : i < c.ths.size := TermCert.arr_lt X.hth
  have hpg : ∀ l f, Eg.pfr l = some f →
      ∃ f', (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f' :=
    fun l f h => ⟨f, gfoot_pfr hgf h⟩
  obtain ⟨S0, -, hE0, hm0, -⟩ := X.inv.thr i th X.hth
  have hwr := tstep_writeAt hE0 hm0.2.2.1 X.hr
  intro l cl hl hg
  rw [hsz]
  have hl' : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l = some cl := hl
  rcases hgf.2.1 l with e | ⟨-, -, -, T, hT⟩
  · rw [e] at hl'
    rcases hg with ⟨t, m, hm, e2⟩ | ⟨f, hf⟩
    · rcases Nat.lt_or_ge t c.mem.size with ht | ht
      · exact fin_mono (hpg l) (Nat.le_refl _)
          (hF l cl hl' (.inl ⟨t, m, by rw [← tctx_pre X t ht]; exact hm, e2⟩))
      · rcases hwr t m ht (by rw [← X.e1]; exact hm) with ⟨n, hn, -, hfl⟩ | ⟨cl2, hcl2⟩
        · have h0 := (X.inv.fresh i th X.hth n hn).1
          rw [← e2] at hl'
          rw [hfl] at hl'
          exact absurd (h0.symm.trans hl') (fun e => by cases e)
        · have hcl2' : cutSto Eg i l = some cl := by
            rw [← e2]
            have h2 := cutSto_sub (Eg := Eg) (i := i) hcl2
            rw [e2, hl'] at h2
            cases h2
            exact hcl2
          exact fin_mono (hpg l) (Nat.le_refl _) (fin_cut hF X.hth hcl2')
    · have hf' : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').pfr l = some f := hf
      rcases hgf.2.2.2.2.1 l with e3 | ⟨-, -, -, -, cq, hcq, hoq⟩ | ⟨-, -, e3⟩
      · rw [e3] at hf'
        exact fin_mono (hpg l) (Nat.le_refl _) (hF l cl hl' (.inr ⟨f, hf'⟩))
      · rw [hl'] at hcq
        cases hcq
        exact fin_own hoq hi
      · have h4 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l = some cl := hl
        rw [e3] at h4
        cases h4
  · rw [hT] at hl'
    cases hl'
    exact fin_own rfl hi

/-- **A promise step keeps `cellOwn`** (plants at cells of the promiser, `PlantSpec`; the promised
location in the promiser's cut or holding no cell, `PromLocF`). -/
theorem cellOwn_prom
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hPS : PlantSpec Eg P j c.mem.size)
    (hpl : (∃ cl, cutSto Eg j a.label = some cl) ∨
      ∃ n, th.nalloc ≤ n ∧ a.label = freshLabel c.lbase c.n j n)
    (hF : CellOwnerLiveM Eg c) :
    CellOwnerLiveM (EgP Eg P N j c.mem.size) (promise c j a v w) := by
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hsz : (promise c j a v w).ths.size = c.ths.size := TermStep.promise_size c j a v w
  have hj : j < c.ths.size := TermCert.arr_lt X.hth
  have hpg : ∀ l f, Eg.pfr l = some f → ∃ f', (EgP Eg P N j c.mem.size).pfr l = some f' := by
    intro l f h
    simp only [EgP, GEnv.withFp, plantG]
    cases e : P l with
    | none => exact ⟨f, h⟩
    | some f' => exact ⟨f', rfl⟩
  intro l cl hl hg
  have hl0 : Eg.sto l = some cl := hl
  rw [hsz]
  rcases hg with ⟨t, m, hm, e2⟩ | ⟨f, hf⟩
  · rw [hpi.1] at hm
    rcases Nat.lt_or_ge t c.mem.size with ht | ht
    · rw [Array.getElem?_push_lt ht] at hm
      have hm' : c.mem[t]? = some m := by rw [Array.getElem?_eq_getElem ht]; exact hm
      exact fin_mono (hpg l) (Nat.le_refl _) (hF l cl hl0 (.inl ⟨t, m, hm', e2⟩))
    · rcases Nat.eq_or_lt_of_le ht with e3 | e3
      · subst e3
        rw [Array.getElem?_push_size] at hm
        cases hm
        rcases hpl with ⟨cl2, hcl2⟩ | ⟨n, hn, hfl⟩
        · have hcl2' : cutSto Eg j l = some cl := by
            rw [← e2]
            have h2 := cutSto_sub (Eg := Eg) (i := j) hcl2
            rw [e2, hl0] at h2
            cases h2
            exact hcl2
          exact fin_mono (hpg l) (Nat.le_refl _) (fin_cut hF X.hth hcl2')
        · have h0 := (X.inv.fresh j th X.hth n hn).1
          rw [← e2, hfl, h0] at hl0
          cases hl0
      · rw [Array.getElem?_eq_none (by rw [Array.size_push]; exact e3)] at hm
        cases hm
  · cases e : P l with
    | none =>
      have hf' : Eg.pfr l = some f := by
        revert hf
        simp only [EgP, GEnv.withFp, plantG, e]
        exact id
      exact fin_mono (hpg l) (Nat.le_refl _) (hF l cl hl0 (.inr ⟨f, hf'⟩))
    | some f' =>
      obtain ⟨-, ⟨cq, hcq, hoq⟩, -⟩ := hPS l f' e
      rw [hl0] at hcq
      cases hcq
      exact fin_own hoq hj

end

end TermCellOwn

#print axioms TermCellOwn.cellOwn_use
#print axioms TermCellOwn.cellOwn_init
#print axioms TermCellOwn.cellOwn_thread
#print axioms TermCellOwn.cellOwn_prom
#print axioms TermCellOwn.nonPromLbl_ofM

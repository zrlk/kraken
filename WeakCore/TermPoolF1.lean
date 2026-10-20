import WeakCore.TermPoolStaging
import WeakCore.TermOverCrT
import WeakCore.TermOwnCF

/-! # TermPoolF1: the `f1T` member

Construction at a thread step of `i`: for `j ≠ i` the post credit plus pool `crN` re-splits per
promise `t`; with `V := pl j t + dh t`, the item **converts** (`Conv`) when `V ≠ 0` and its tag
fails after the step: then `cr2 j t := cr j t + dc t + V`, `pl2 j t := 0`; otherwise
`cr2 j t := cr j t + dc t`, `pl2 j t := V`.  A converted item at an own promise of `j` is an old
pool item (`dh t = 0`: the `dh` items are tagged after the step, by `PromsDisj`) whose tag
survives the step except its footprint clause, so the footprint lies above `t` and the item is a
plant credit at window bound `t` (`ptag_conv`).
-/

namespace TermPoolF1
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh TermPoolStaging TermInterf TermOverCrW
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `FpAt` at a cut does not read the seen set. -/
theorem FpAt_cut_seen (Eg : GEnv) (j : Nat) (S S' : AllocLabel → Prop) (a : Address) :
    FpAt (Cut Eg j S) a = FpAt (Cut Eg j S') a := rfl

/-- The lowest window promise at a unit is the lowest own promise there. -/
theorem lowOwn_of_lowestIn {s : St} {wb t' : Ts} {a : Address} (h : LowestIn s.mem (winL wb s.promises) a t') :
    TermPiece.LowOwn s a t' := by
  obtain ⟨h1, h2, h3⟩ := h
  have h1' := List.mem_filter.1 h1
  have hw : t' ≤ wb := of_decide_eq_true h1'.2
  refine ⟨h1'.1, h2, fun t'' m' ht hm hl => ?_⟩
  by_cases hle : t'' ≤ wb
  · exact h3 t'' (List.mem_filter.2 ⟨ht, decide_eq_true hle⟩) ⟨m', hm, hl⟩
  · exact Nat.le_of_lt (Nat.lt_of_le_of_lt hw (Nat.lt_of_not_le hle))

/-- **A credit item of an idle thread is kept** along a step keeping the memory prefix and the
thread's promises, and growing its cut (`Incl`) without changing the cell. -/
theorem crItem_post {c c' : Cfg} {E1 E2 : TEnv} {thj : TTh} {f : Ts → Res} {l : AllocLabel} {cl : Cell}
    {x : TermPiece.CrIt}
    (hI : Incl E1 E2) (htid : E1.tid = E2.tid) (hsto : E2.sto l = E1.sto l)
    (hpre : ∀ t, t < c.mem.size → c'.mem[t]? = c.mem[t]?) (hP : ∀ t, t ∈ thj.promises → t < c.mem.size)
    (h : TermPiece.CrItem E1 (stOf c.mem c.pairs thj) f l cl x) :
    TermPiece.CrItem E2 (stOf c'.mem c'.pairs thj) f l cl x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  have hx : x.1 < c.mem.size := hP _ a3.1
  refine ⟨mh, usS, by show c'.mem[x.1]? = _; rw [hpre _ hx]; exact a1, a2, ?_, ?_, a5, a6, a7, a8, a9, a10,
    ValOfR_mono hI.prog htid hI.sto hI.ini a11 hI.pfr hI.box hI.rini, a12, ?_⟩
  · obtain ⟨b1, ⟨m, hm, hl⟩, b3⟩ := a3
    refine ⟨b1, ⟨m, by show c'.mem[x.1]? = _; rw [hpre _ hx]; exact hm, hl⟩,
      fun t' m' ht' hm' hl' => b3 t' m' ht' ?_ hl'⟩
    show c.mem[t']? = _; rw [← hpre _ (hP _ ht')]; exact hm'
  · intro hw; apply a4
    have e : E2.sto mh.loc.label = E1.sto mh.loc.label := by rw [a2]; exact hsto
    exact (WordUnit_congr e).1 hw
  · intro i o w tw' hK hIn hw hlo
    obtain ⟨b1, ⟨m, hm, hl⟩, b3⟩ := hlo
    have htw : tw' < c.mem.size := hP _ b1
    refine TermPlant.PredAt_mono htw hpre
      (a13 i o w tw' hK hIn hw ⟨b1, ⟨m, ?_, hl⟩, fun t' m' ht' hm' hl' => b3 t' m' ht' ?_ hl'⟩)
    · show c.mem[tw']? = _; rw [← hpre _ htw]; exact hm
    · show c'.mem[t']? = _; rw [hpre _ (hP _ ht')]; exact hm'

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- `gfoot_of` at any input credits of the step (it reads only the footprint `Z.1`). -/
theorem gfootZ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ cri dbi : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      cri dbi δ) :
    GFoot (gOf p k arch c i) Eg (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') th.nalloc r.2.2.nalloc
      c.mem.size := by
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  exact EFoot_post hF0 (X.inv.gfresh X.hth _) (X.inv.vwr i th X.hth)

/-- **Conversion**: a pre-step pool tag of an idle thread `j` whose tag fails after the step is a
key-free plant credit at every post cut of `j` (window bound `t` itself), at a non-word unit. -/
theorem ptag_conv {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ cri dbi : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      cri dbi δ)
    {j : Nat} {thj : TTh} (hji : j ≠ i) (hj : c.ths[j]? = some thj) {f : Ts → Res} {t : Ts}
    (hpt : PTag Eg c j thj f t)
    (hn : ¬ PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj f t)
    (Sj : AllocLabel → Prop) :
    ∃ m, c'.mem[t]? = some m ∧
      PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj)
        m t (f t) ∧
      ¬ WordUnit (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) m.loc ∧
      TermPlant.CrKeys (f t) := by
  have hgf := gfootZ X Y Z
  have hI : ∀ S' : AllocLabel → Prop,
      Incl (Cut Eg j S') (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') :=
    fun S' => (Cut_other hgf (j := j) hji S').1.trans (Incl_cut_withFp _ (fpSync Eg c') j S')
  have hpre := tctx_pre X
  have hP : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => X.inv.plt j thj t hj ht
  obtain ⟨h1, h2, m, hm, h4, h5⟩ := hpt
  have ht : t < c.mem.size := hP t h1
  have hm' : c'.mem[t]? = some m := by rw [hpre t ht]; exact hm
  -- the item part of the tag survives at every cut
  have h5' : ∀ S' : AllocLabel → Prop, ∃ cl x,
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S').sto m.loc.label = some cl ∧
      cl.owner = some j ∧ x.1 = t ∧
      TermPiece.CrItem (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S')
        (stOf c'.mem c'.pairs thj) f m.loc.label cl x ∧
      PieceLow c'.mem thj.promises m.loc.label x.2.1 x.2.2.1 t := by
    intro S'
    obtain ⟨cl, x, hcl, ho, hx, hci, hpl⟩ := h5 S'
    have hcl' := (hI S').sto _ _ hcl
    exact ⟨cl, x, hcl', ho, hx, crItem_post (hI S') rfl (hcl'.trans hcl.symm) hpre hP hci,
      pieceLow_foreign hpre hP ht hpl⟩
  -- the key-free item disjunct survives the step, so the pre tag used the footprint disjunct
  have h4 : ∀ S : AllocLabel → Prop, ∃ fq mf, fq ∈ FpAt (Cut Eg j S) ⟨m.loc.label, 0⟩ ∧ c.mem[fq]? = some mf ∧
      mf.loc.label = m.loc.label ∧ fq ≤ t := by
    rcases h4 with h4 | h4
    · exact h4
    · refine absurd ⟨h1, h2, m, hm', Or.inr fun S' => ?_, h5'⟩ hn
      obtain ⟨hpf, cl, x, hcl, ho, hx, hK, hci⟩ := h4 S'
      have hcl' := (hI S').sto _ _ hcl
      obtain ⟨f0, hf0⟩ := Option.ne_none_iff_exists'.1 hpf
      refine ⟨?_, cl, x, hcl', ho, hx, hK, crItem_post (hI S') rfl (hcl'.trans hcl.symm) hpre hP hci⟩
      rw [(hI S').pfr _ _ hf0]
      exact fun h => by cases h
  -- so the footprint part fails at some cut, hence at all (it does not read the seen set)
  have h4n : ¬ ∀ S' : AllocLabel → Prop, ∃ fq mf,
      fq ∈ FpAt (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') ⟨m.loc.label, 0⟩ ∧
      c'.mem[fq]? = some mf ∧ mf.loc.label = m.loc.label ∧ fq ≤ t :=
    fun h => hn ⟨h1, h2, m, hm', Or.inl h, h5'⟩
  obtain ⟨Sf, hSf⟩ := Classical.not_forall.1 h4n
  -- the item at `Sj`
  obtain ⟨cl, x, hcl0, ho, hx, hci0, hpl0⟩ := h5 Sj
  have hcl := (hI Sj).sto _ _ hcl0
  have hci := crItem_post (hI Sj) rfl (hcl.trans hcl0.symm) hpre hP hci0
  have hpl := pieceLow_foreign hpre hP ht hpl0
  -- the frontier: the pre tag's footprint message makes the cell visible
  obtain ⟨fq, mf, hfq, -, -, -⟩ := h4 Sj
  obtain ⟨f0, hf0⟩ : ∃ f0, Eg.pfr m.loc.label = some f0 := by
    cases e : Eg.pfr m.loc.label with
    | some f0 => exact ⟨f0, rfl⟩
    | none =>
      have hpv : Priv (Cut Eg j Sj) m.loc.label := ⟨⟨cl, hcl0, ho⟩, e⟩
      rw [FpAt_priv (a := ⟨m.loc.label, 0⟩) (fun hv => hv hpv)] at hfq
      cases hfq
  have hpf2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr m.loc.label ≠ none := by
    rw [(hI Sj).pfr _ _ hf0]; exact fun h => by cases h
  -- the cell's layout
  obtain ⟨S1, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 m.loc.label cl f0 hcl0 hf0).1
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hci
  have emh : mh = m := by
    have a1' : c'.mem[t]? = some mh := by rw [← hx]; exact a1
    exact Option.some.inj (a1'.symm.trans hm')
  rw [emh] at a4 a8 a9
  obtain ⟨sb, S0, b0, hseg, hat, hsb⟩ := TermPiece.seg_of_atOffS hlay a5 a6
  have htc : t < c'.mem.size := Nat.lt_of_not_le fun hc => by
    rw [Array.getElem?_eq_none hc] at hm'; cases hm'
  refine ⟨m, hm', ⟨cl, sb, S0, b0, x.2.2.1, usS, t, hcl, ho, hpf2, hseg, hat, a6, a4, a7,
    Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.add_zero] at a9; exact absurd a8 (Nat.not_le_of_lt a9),
    by rw [hsb]; exact a8, by rw [hsb]; exact a9, Nat.le_refl _, htc, ?_, ?_,
    Or.inl ⟨x.2.2.2.2.2, x.2.2.2.1, x.2.2.2.2.1, a10, a11, by rw [← hx]; exact a12, ?_⟩⟩, a4, h2⟩
  · intro tf mf htf hmf hl
    exact Nat.lt_of_not_le fun hle => hSf ⟨tf, mf, htf, hmf, hl, hle⟩
  · intro t' m' h1' h2' h3' h4' h5' _
    exact hpl usS a7 t' m' h1' h2' h3' (by rw [← hsb]; exact h4') (by rw [← hsb]; exact h5')
  · intro i' o w t' hK hIn hw hlo
    rw [hsb] at hlo ⊢
    exact a13 i' o w t' hK hIn hw (lowOwn_of_lowestIn hlo)

end

/-- The conversion predicate at `(j, t)`. -/
def Conv (Eg' : GEnv) (c' : Cfg) (pl : Nat → Ts → Res) (dh : Ts → Res) (j : Nat) (t : Ts) : Prop :=
  pl j t + dh t ≠ .zero ∧ ∃ thj', c'.ths[j]? = some thj' ∧ ¬ PTag Eg' c' j thj' (fun u => pl j u + dh u) t

/-- The post credits. -/
noncomputable def cr2F (Eg' : GEnv) (c' : Cfg) (cr pl : Nat → Ts → Res) (i : Nat) (cr' dc dh : Ts → Res) :
    Nat → Ts → Res := by
  classical
  exact fun j => if j = i then cr' else fun t =>
    if Conv Eg' c' pl dh j t then cr j t + dc t + (pl j t + dh t) else cr j t + dc t

/-- The post pool. -/
noncomputable def pl2F (Eg' : GEnv) (c' : Cfg) (pl : Nat → Ts → Res) (i : Nat) (pli dh : Ts → Res) :
    Nat → Ts → Res := by
  classical
  exact fun j => if j = i then pli else fun t => if Conv Eg' c' pl dh j t then .zero else pl j t + dh t

/-! ## The tag of an idle thread survives a foreign step, so no conversion -/

/-- The masked item: same piece, words and credit, no pins. -/
def maskK (x : TermPiece.CrIt) : TermPiece.CrIt := (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, fun _ => false)

/-- Masking keeps a credit item. -/
theorem crItem_mask {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {cl : Cell} {x : TermPiece.CrIt}
    (h : TermPiece.CrItem E s f l cl x) : TermPiece.CrItem E s f l cl (maskK x) := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, -⟩ := h
  exact ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun _ _ _ _ hK => by cases hK⟩

/-- **A masked `CrItemQ` item is a credit item** (`crItem_of_crItemQ_mask`): with no pins the
first-write alternative is never asked for. -/
theorem crItem_of_crItemQ_mask {E : TEnv} {s : St} {f : Ts → Res} {l : AllocLabel} {cl : Cell}
    {x : TermPiece.CrIt} (h : TermOverCr.CrItemQ E s f l cl x) : TermPiece.CrItem E s f l cl (maskK x) := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, -⟩ := h
  exact ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, fun _ _ _ _ hK => by cases hK⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **An idle thread's pool tag survives a foreign step.** -/
theorem ptag_keep {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ cri dbi : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      cri dbi δ)
    {j : Nat} {thj : TTh} (hji : j ≠ i) (hj : c.ths[j]? = some thj) {f : Ts → Res} {t : Ts}
    (hpt : PTag Eg c j thj f t) :
    PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj f t := by
  have hgf := gfootZ X Y Z
  have hI : ∀ S' : AllocLabel → Prop,
      Incl (Cut Eg j S') (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') :=
    fun S' => (Cut_other hgf (j := j) hji S').1.trans (Incl_cut_withFp _ (fpSync Eg c') j S')
  have hpre := tctx_pre X
  have hP : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => X.inv.plt j thj t hj ht
  obtain ⟨h1, h2, m, hm, h4, h5⟩ := hpt
  have ht : t < c.mem.size := hP t h1
  have hm' : c'.mem[t]? = some m := by rw [hpre t ht]; exact hm
  -- the item part of the tag survives at every cut
  have h5' : ∀ S' : AllocLabel → Prop, ∃ cl x,
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S').sto m.loc.label = some cl ∧
      cl.owner = some j ∧ x.1 = t ∧
      TermPiece.CrItem (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S')
        (stOf c'.mem c'.pairs thj) f m.loc.label cl x ∧
      PieceLow c'.mem thj.promises m.loc.label x.2.1 x.2.2.1 t := by
    intro S'
    obtain ⟨cl, x, hcl, ho, hx, hci, hpl⟩ := h5 S'
    have hcl' := (hI S').sto _ _ hcl
    exact ⟨cl, x, hcl', ho, hx, crItem_post (hI S') rfl (hcl'.trans hcl.symm) hpre hP hci,
      pieceLow_foreign hpre hP ht hpl⟩
  -- the frontier at the cell, before the step
  have hpf : ∀ S' : AllocLabel → Prop, (Cut Eg j S').pfr m.loc.label ≠ none := by
    intro S'
    rcases h4 with h4 | h4
    · obtain ⟨cl, x, hcl0, ho, -⟩ := h5 S'
      obtain ⟨fq, mf, hfq, -, -, -⟩ := h4 S'
      intro e
      have hpv : Priv (Cut Eg j S') m.loc.label := ⟨⟨cl, hcl0, ho⟩, e⟩
      rw [FpAt_priv (a := ⟨m.loc.label, 0⟩) (fun hv => hv hpv)] at hfq
      cases hfq
    · exact (h4 S').1
  refine ⟨h1, h2, m, hm', Or.inr fun S' => ?_, h5'⟩
  obtain ⟨cl, x, hcl, ho, hx, hci, -⟩ := h5' S'
  obtain ⟨f0, hf0⟩ := Option.ne_none_iff_exists'.1 (hpf S')
  refine ⟨?_, cl, maskK x, hcl, ho, hx, fun _ => rfl, crItem_mask hci⟩
  rw [(hI S').pfr _ _ hf0]
  exact fun h => by cases h

/-- **The conversion never fires** at a post-tagged item of an idle thread. -/
theorem not_conv {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ dh cri dbi : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      cri dbi δ)
    (hPT : PoolTag Eg c pl)
    (hdh : ∀ t, dh t ≠ .zero → ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ t ∈ thj.promises ∧
      ∀ thj', c'.ths[j]? = some thj' →
        PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj' (fun u => pl j u + dh u) t)
    {j : Nat} {t : Ts} (hji : j ≠ i) (hpr : ∀ thj', c'.ths[j]? = some thj' → t ∈ thj'.promises) :
    ¬ Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j t := by
  rintro ⟨hV, thj', hj', hnP⟩
  have hjc : c.ths[j]? = some thj' := by rw [← X.ho j hji]; exact hj'
  by_cases hd : dh t = .zero
  · have hpz : pl j t ≠ .zero := fun h => hV (by rw [h, hd, Res.add_zero])
    have hk := ptag_keep X Y Z hji hjc (hPT.1 j thj' t hjc hpz)
    exact hnP (PTag_congr (show pl j t = pl j t + dh t by rw [hd, Res.add_zero]) hk)
  · obtain ⟨j0, thj0, hj0i, hj0, ht0, hP⟩ := hdh t hd
    by_cases hjj : j0 = j
    · subst hjj; exact hnP (hP thj' hj')
    · exact X.inv.disj j0 j thj0 thj' t hjj hj0 hjc ht0 (hpr thj' hj')
end


section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **`f1T`**. -/
theorem f1T_of : f1T p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F crS cr' db' δ dc dh plh
    X Y Z _hQ _hOC hPT _hle _hsh hdh hNew
  classical
  -- the `dh` items are key-free
  have hdhK : ∀ t l, dh t (.own l) = 0 := by
    intro t l
    by_cases h0 : dh t = .zero
    · rw [h0]; rfl
    · obtain ⟨j0, thj0, hj0i, hj0, -, hP⟩ := hdh t h0
      have := (hP thj0 (by rw [X.ho j0 hj0i]; exact hj0)).2.1 l
      simp only [Res.add_apply] at this; omega
  -- converted items are key-free
  have hplK : ∀ j t l, j ≠ i →
      Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j t → pl j t (.own l) = 0 := by
    intro j t l hji hc
    obtain ⟨-, thj', hj', -⟩ := hc
    by_cases h0 : pl j t = .zero
    · rw [h0]; rfl
    · exact (hPT.1 j thj' t (by rw [← X.ho j hji]; exact hj') h0).2.1 l
  -- a converted item at an own promise is an old pool item whose tag fails
  have hconv : ∀ j thj' t, j ≠ i → c'.ths[j]? = some thj' → t ∈ thj'.promises →
      Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j t →
      dh t = .zero ∧ pl j t ≠ .zero ∧
        ¬ PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj' (pl j) t := by
    intro j thj' t hji hj' ht hc
    obtain ⟨hV, thj'', hj'', hnP⟩ := hc
    have e : thj'' = thj' := Option.some.inj (hj''.symm.trans hj')
    subst e
    have hjc : c.ths[j]? = some thj'' := by rw [← X.ho j hji]; exact hj'
    have hdt : dh t = .zero := by
      by_cases h0 : dh t = .zero
      · exact h0
      · exfalso
        obtain ⟨j0, thj0, hj0i, hj0, ht0, hP⟩ := hdh t h0
        by_cases hjj : j0 = j
        · subst hjj; exact hnP (hP thj'' hj')
        · exact X.inv.disj j0 j thj0 thj'' t hjj hj0 hjc ht0 ht
    refine ⟨hdt, fun h => hV (by rw [h, hdt, Res.add_zero]), fun h => hnP (PTag_congr ?_ h)⟩
    show pl j t = pl j t + dh t
    rw [hdt, Res.add_zero]
  refine ⟨cr2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' cr pl i cr' dc dh,
    pl2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl i
      (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) dh, by simp [cr2F], by simp [pl2F], ?_, ?_, ?_, ?_, ?_⟩
  · funext j t
    by_cases hji : j = i
    · subst hji; simp [crPl, crN, cr2F, pl2F, updD]
    · by_cases hc : Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j t
      · simp [crPl, crN, cr2F, pl2F, updD, hji, hc]
      · simp [crPl, crN, cr2F, pl2F, updD, hji, hc]
  · intro j thj' t hji hj' hne
    by_cases hc : Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j t
    · simp [pl2F, hji, hc] at hne
    · have e : pl2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl i
          (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) dh j t = pl j t + dh t := by simp [pl2F, hji, hc]
      have hV : pl j t + dh t ≠ .zero := e ▸ hne
      by_cases hT : PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj'
          (fun u => pl j u + dh u) t
      · exact PTag_congr e.symm hT
      · exact absurd ⟨hV, thj', hj', hT⟩ hc
  · intro j t l
    by_cases hji : j = i
    · subst hji; simp [cr2F, updD]
    · by_cases hc : Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j t
      · simp [cr2F, updD, hji, hc, Res.add_apply, hdhK, hplK j t l hji hc]
      · simp [cr2F, updD, hji, hc]
  · intro j thj' Sj hji hj' hC tw htw
    obtain ⟨m, hm, hd, hor⟩ := hC tw htw
    by_cases hc : Conv (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl dh j tw
    · obtain ⟨hdt, hpn, hnP⟩ := hconv j thj' tw hji hj' htw hc
      have hj : c.ths[j]? = some thj' := by rw [← X.ho j hji]; exact hj'
      obtain ⟨m', hm', hPC, hw, hK⟩ := ptag_conv X Y Z hji hj (hPT.1 j thj' tw hj hpn) hnP Sj
      have e1 : m' = m := Option.some.inj (hm'.symm.trans hm)
      rw [e1] at hPC hw
      have hA := plantCrK_add hC htw hm hw hPC hK
      have e : cr2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' cr pl i cr' dc dh j tw =
          cr j tw + dc tw + pl j tw := by simp [cr2F, hji, hc, hdt]
      refine ⟨m, hm, hd, Or.inr ?_⟩
      rw [e]; exact hA
    · have e : cr2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' cr pl i cr' dc dh j tw =
          cr j tw + dc tw := by simp [cr2F, hji, hc]
      refine ⟨m, hm, hd, ?_⟩
      rw [e]; exact hor
  -- the pool cover of an idle thread: old items move, `hNew` adds the newly needed ones
  · intro j thj' Sj hji hj' l cl hcl ho hpf hnp
    have hjc : c.ths[j]? = some thj' := by rw [← X.ho j hji]; exact hj'
    have hpl2 : ∀ u, u ∈ thj'.promises → pl2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl i (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) dh j u =
        pl j u + dh u := by
      intro u hu
      have hnc := not_conv X Y Z hPT hdh (t := u) hji (fun thj'' h => by rw [hj'] at h; cases h; exact hu)
      simp [pl2F, hji, hnc]
    -- a post item at `pl j + dh` is one at `pl2 j`
    have hup : ∀ x, TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj') (fun u => pl j u + dh u) l cl x →
        TermOverCr.CrItemQ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj')
          (pl2F (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' pl i (plStep pl i (stOf r.1 r.2.1 r.2.2) plh) dh j) l cl x := by
      intro x hx
      obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hx
      refine ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, ?_, a13⟩
      rw [hpl2 x.1 a3.1]; exact a12
    -- the pre list (empty off a pre frontier cell)
    obtain ⟨Gs, hsum, hit, hcov, hGs⟩ : ∃ Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
        (∀ t, Res.sum ((Gs.filter fun x => decide (x.1 = t)).map (·.2.2.2.2.1)) ≤ pl j t) ∧
        (∀ x ∈ Gs, TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj') (pl j) l cl x) ∧
        (∀ o tw, ((Cut Eg j Sj).sto l = some cl ∧ Eg.pfr l ≠ none ∧ ¬ Eg.pubd l ∧
            PredU (Cut Eg j Sj) ⟨l, o⟩ ∧ ¬ VisU (Cut Eg j Sj) ⟨l, o⟩ ∧
            TermPlant.LowOwn (stOf c.mem c.pairs thj') ⟨l, o⟩ tw ∧ FirstW c.mem ⟨l, o⟩ tw ∧
            TermPlant.OverT (Cut Eg j Sj) (stOf c.mem c.pairs thj') ⟨l, o⟩ tw) →
          ∃ x ∈ Gs, ∃ usS ii, accs x.2.2.1 = some usS ∧ x.2.1 ≤ o ∧ InAcc usS ii (o - x.2.1) ∧
            x.2.2.2.2.2 ii = true) ∧
        ((Cut Eg j Sj).sto l = some cl ∧ Eg.pfr l ≠ none ∧ ¬ Eg.pubd l ∨ Gs = []) := by
      by_cases hc : (Cut Eg j Sj).sto l = some cl ∧ Eg.pfr l ≠ none ∧ ¬ Eg.pubd l
      · obtain ⟨hc0, hpf0, hnp0⟩ := hc
        obtain ⟨Gs, a, b, d⟩ := hPT.2 j thj' Sj hjc l cl hc0 ho hpf0 hnp0
        exact ⟨Gs, a, b, fun o tw h => d o tw h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
          h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2, .inl ⟨hc0, hpf0, hnp0⟩⟩
      · exact ⟨[], fun _ => Res.zero_le _, fun _ h => absurd h List.not_mem_nil,
          fun o tw h => absurd ⟨h.1, h.2.1, h.2.2.1⟩ hc, .inr rfl⟩
    obtain ⟨K, Gn, hsn, hitn, hcovn⟩ := hNew j thj' thj' Sj l cl hji hjc hj' hcl ho hpf hnp Gs hGs hit hcov
    refine ⟨Gs.map (TermPoolStaging.bitExt K) ++ Gn, fun t => ?_, fun x hx => hup x (hitn x hx),
      fun o tw h1 h2 h3 h4 h5 => hcovn o tw h1 h2 h3 h4 h5⟩
    rw [List.filter_append, List.map_append, Res.sum_append, TermPoolStaging.sum_bitExt]
    by_cases ht : t ∈ thj'.promises
    · rw [hpl2 t ht]; exact Res.add_le_add (hsum t) (hsn t)
    · have hnil : ∀ G : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool)),
          (∀ x ∈ G, x.1 ∈ thj'.promises) → G.filter (fun x => decide (x.1 = t)) = [] := by
        intro G hG
        refine List.filter_eq_nil_iff.2 fun x hx => ?_
        simp only [decide_eq_true_eq]
        intro e; exact ht (e ▸ hG x hx)
      rw [hnil Gs (fun x hx => by obtain ⟨_, _, _, _, a3, _⟩ := hit x hx; exact a3.1),
        hnil Gn (fun x hx => by
          obtain ⟨_, _, _, _, a3, _⟩ := hitn x (List.mem_append_right _ hx); exact a3.1)]
      intro k; simp [Res.sum_nil]

end

#print axioms ptag_conv
#print axioms ptag_keep
#print axioms not_conv
#print axioms crItem_of_crItemQ_mask
#print axioms f1T_of

end TermPoolF1

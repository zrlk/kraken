import WeakCore.TermPoolFgnCov
import WeakCore.TermOwnKey

/-! The gap-2 support `SuppAll` of `TermPoolFgnCov.fgnCov_of`, from its antecedent `Ante`
(`StepTgt` with `HPd`).

An item of the post cover at `crPl cr pl j + δ` whose amount exceeds `crPl cr pl j` at its holder
`t` has `δ t ≠ 0`, so `t` is the target of a drop entry `g` (`plantD1_cases`) with `δ t = g.R`.
`HPd` places `t` in `g`'s piece as the owner's piece-lowest promise.  Then:
* no footprint message at the label is at or below `t` (at some cut): `QC` at `cr j t + δ t`, a
  plant credit with window bound `t` and the empty mask (`plantCr_mk`);
* otherwise: the post pool tag at `pl j + δ`, with the entry as an empty-mask credit item.
Key-freeness of `g.R` (gap s2): an own key in `g.R` would make its label owned by both the stepper
`i` and the owner `j` (`ValOfR_ownL` at both cuts; `noOR` piece of a shared cell).  The entry's
value moves to the owner's post cut by `ValOfR_transferS` (gap s3). -/

namespace TermPoolSupp
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper TermPool TermOverCrW TermPoolStaging TermPoolFgnCov
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (s2) **A drop entry's resources carry no own keys** when the entry's piece is `noOR` and the
entry is typed at the cut of a thread `i` other than an owner-side thread `j`: an own key would be
owned by both. -/
theorem crKeys_entry {Eg : GEnv} {i j : Nat} {S Sj : AllocLabel → Prop} {T : Ty} {ws : List Word} {R : Res}
    (hji : j ≠ i) (hnr : noOR T = true) (hv : ValOfR (Cut Eg i S) T ws R) : TermPlant.CrKeys R := by
  intro l'
  cases hR0 : R (.own l') with
  | zero => rfl
  | succ n =>
  exfalso
  have h0 : R (.own l') ≠ 0 := by rw [hR0]; exact Nat.succ_ne_zero n
  obtain ⟨ci, hci, hoi⟩ := TermOwnKey.ValOfR_ownL hv h0
  obtain ⟨cj, hcj, hoj⟩ := TermOwnKey.ValOfR_ownL (ValOfR_transferS (InclS_cut Eg i j S Sj) hnr hv) h0
  have e1 := (cutSto_some.1 hci).1
  have e2 := (cutSto_some.1 hcj).1
  rw [e1] at e2
  cases e2
  rw [hoi] at hoj
  exact hji (Option.some.inj hoj).symm

/-- **The support at one drop target** `t = tg g` (holder facts after the step): `t` is an outstanding
promise of the owner `j`, and `QCr` (plant credit off `SlotFW`) or the post pool tag at `pl j + δ` (the
K∅ branch at `SlotFW` targets). -/
theorem tgtSupp_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl)
    {g : TermPiece.GdE} (hg : g ∈ Gd) {t : Ts} (htg : tg g = some t) (hδg : δ t = g.R) {mh : Msg}
    (hmh : (stOf c'.mem c'.pairs thj).mem[t]? = some mh) (hlab : mh.loc.label = l)
    (hlow : TermPlant.LowOwn (stOf c'.mem c'.pairs thj) mh.loc t)
    (hnw : ¬ WordUnit (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) mh.loc) :
    t ∈ thj.promises ∧ (QCr (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j t (cr j t + δ t) ∨
      ∀ thj', c'.ths[j]? = some thj' →
        PTag (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j thj' (fun u => pl j u + δ u) t) := by
  classical
  obtain ⟨X, Y, Z, -, hPT, hDrop, hδ, ⟨-, hPd, -, -⟩, hji, hj, hc2, hown, hpf2⟩ := hA
  -- the owner's cell before the step
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, -, -, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hj' : c'.ths[j]? = some thj := by rw [X.ho j hji]; exact hj
  have hpreM := tctx_pre X
  obtain ⟨S0, -, -, hmi, -, -, hCK⟩ := X.inv.thr j thj hj
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  have hstoi : (Cut Eg i S).sto l = some cl := cutSto_some.2 ⟨hs, Or.inr ⟨f, hf⟩⟩
  have hnoOR : noOR cl.ty = true := X.inv.shty l cl ⟨f, hf⟩ hs
  have hDr : TermPiece.Drop (Cut Eg i S) (stOf c.mem c.pairs th) Gd := by rw [← Y.1]; exact hDrop
  have hI : ∀ S' : AllocLabel → Prop,
      Incl (Cut Eg j S') (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') :=
    fun S' => (Cut_other hgf (j := j) hji S').1.trans (Incl_cut_withFp _ (fpSync Eg c') j S')
  obtain ⟨j0, thj0, m, hj0, ht0, hm, hml, us, hus, h1, h2, hlowP, ⟨cl0, hcl0, ho0⟩, hnw0⟩ := hPd g hg t htg
  have emh : m = mh := Option.some.inj (hm.symm.trans hmh)
  subst emh
  have hgl : g.l = l := by rw [← hml, hlab]
  have hj0e : j = j0 := by
    rw [hml, hgl, hs] at hcl0
    cases hcl0
    rw [hown] at ho0
    exact Option.some.inj ho0
  subst hj0e
  have e1 : thj = thj0 := Option.some.inj (hj.symm.trans hj0)
  subst e1
  -- the entry
  obtain ⟨c1, hc1, -, -, hpc, hwc, -, hv⟩ := hDr.1 g hg
  rw [hgl, hstoi] at hc1
  cases hc1
  have hnr : noOR g.S = true := noOR_atOffR hpc.1 hnoOR
  have hlen : g.ws.length = nWords us := Option.some.inj (hwc.symm.trans (wc_of_accs hus))
  have hV : ∀ S' : AllocLabel → Prop,
      ValOfR (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') g.S g.ws g.R :=
    fun S' => ValOfR_transferS ((InclS_cut Eg i j S S').trans (InclS.of_incl (hI S'))) hnr hv
  have hKg : TermPlant.CrKeys g.R := crKeys_entry (Sj := Sj) hji hnr hv
  -- the holder's pre credit is key-free (`PromCrK`, zero at a non-word unit unless a plant credit)
  have hKc : TermPlant.CrKeys (cr j t) := by
    obtain ⟨m', hm', -, hc⟩ := hCK t ht0
    change c.mem[t]? = some m' at hm'
    rw [← hpreM t (X.inv.plt j thj t hj ht0), hm] at hm'
    cases hm'
    rcases hc with hc | ⟨-, hk⟩
    · rw [TermPlant.oldCr_nwordZ (hnw0 S0) hc]
      exact TermPlant.CrKeys_zero
    · exact hk
  refine ⟨ht0, ?_⟩
  by_cases hF : ∀ S' : AllocLabel → Prop, ∃ fq mf,
      fq ∈ FpAt (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') ⟨m.loc.label, 0⟩ ∧
        c'.mem[fq]? = some mf ∧ mf.loc.label = m.loc.label ∧ fq ≤ t
  · -- a footprint message at or below the holder: the post pool tag
    right
    intro thj' hthj'
    rw [hj'] at hthj'
    cases hthj'
    refine ⟨ht0, ?_, m, hm, Or.inl hF, fun S' => ⟨cl, (t, g.b, g.S, g.ws, g.R, fun _ => false), ?_, hown, rfl, ?_, ?_⟩⟩
    · refine crKeys_add ?_ (by rw [hδg]; exact hKg)
      by_cases hz : pl j t = .zero
      · rw [hz]; exact TermPlant.CrKeys_zero
      · exact (hPT.1 j thj t hj hz).2.1
    · rw [hlab]; exact hc2
    · refine ⟨m, us, hm, rfl, hlow, hnw, hpc.1, hpc.2.1, hus, h1, h2, hlen, hV S', ?_, ?_⟩
      · intro k'
        show g.R k' ≤ (pl j t + δ t) k'
        rw [Res.add_apply, hδg]
        exact Nat.le_add_left _ _
      · intro i' o w tw' hK
        cases hK
    · intro usS' hus' t' m' ht' hm' hl' hb1 hb2
      rw [hus] at hus'
      cases hus'
      exact hlowP t' m' ht' hm' hl' hb1 hb2
  · -- no footprint message at or below the holder (at some cut)
    -- the entry as an empty-mask credit item at the post pool `pl j + δ` (holder `t`)
    have hIt : ∀ S' : AllocLabel → Prop, TermPiece.CrItem (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S')
        (stOf c'.mem c'.pairs thj) (fun u => pl j u + δ u) m.loc.label cl
        (t, g.b, g.S, g.ws, g.R, fun _ => false) := fun S' => by
      refine ⟨m, us, hm, rfl, hlow, hnw, hpc.1, hpc.2.1, hus, h1, h2, hlen, hV S', ?_, ?_⟩
      · intro k'
        show g.R k' ≤ (pl j t + δ t) k'
        rw [Res.add_apply, hδg]
        exact Nat.le_add_left _ _
      · intro i' o w tw' hK
        cases hK
    by_cases hSF : SlotFW (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j t
    · -- a `SlotFW` target: the post pool tag through the K∅ branch
      right
      intro thj' hthj'
      rw [hj'] at hthj'
      cases hthj'
      refine ⟨ht0, ?_, m, hm, Or.inr fun S' => ⟨by rw [hlab]; exact hpf2, cl, (t, g.b, g.S, g.ws, g.R, fun _ => false), by rw [hlab]; exact hc2, hown, rfl,
        fun _ => rfl, hIt S'⟩, fun S' => ⟨cl, (t, g.b, g.S, g.ws, g.R, fun _ => false), by rw [hlab]; exact hc2, hown, rfl, hIt S', ?_⟩⟩
      · refine crKeys_add ?_ (by rw [hδg]; exact hKg)
        by_cases hz : pl j t = .zero
        · rw [hz]; exact TermPlant.CrKeys_zero
        · exact (hPT.1 j thj t hj hz).2.1
      · intro usS' hus' t' m' ht' hm' hl' hb1 hb2
        rw [hus] at hus'
        cases hus'
        exact hlowP t' m' ht' hm' hl' hb1 hb2
    -- off `SlotFW`: a plant credit (`QCr`)
    left
    refine ⟨?_, hSF⟩
    obtain ⟨S1, hS1⟩ := Classical.not_forall.1 hF
    obtain ⟨sb, S0', b0, hseg, hat, hsb⟩ := seg_of_atOff hlay hpc.1 hpc.2.1
    refine ⟨m, hm, fun Sj' thj' hthj' => ?_⟩
    rw [hj'] at hthj'
    cases hthj'
    have hn0 : 0 < nWords us := Nat.pos_of_ne_zero fun h0 => hpc.2.2 (by rw [wc_of_accs hus, h0])
    refine ⟨plantCr_mk (c := cl) (sb := sb) (b0 := b0) (by rw [hlab]; exact hc2) hown
      (by rw [hlab]; exact hpf2) hseg hat hpc.2.1 hnw hus hn0 (by rw [hsb]; exact h1) (by rw [hsb]; exact h2)
      (Nat.le_refl _) (Array.getElem?_eq_some_iff.1 hm).1 ?_ ?_ hlen (hV Sj') ?_,
      crKeys_add hKc (by rw [hδg]; exact hKg)⟩
    · intro tf mf htf hmf hlf
      exact Nat.lt_of_not_le fun hle => hS1 ⟨tf, mf, htf, hmf, hlf, hle⟩
    · intro t' m' ht' hm' hl' hb1 hb2 _
      exact hlowP t' m' ht' hm' hl' (by rw [← hsb]; exact hb1) (by rw [← hsb]; exact hb2)
    · intro k'
      rw [Res.add_apply, hδg]
      exact Nat.le_add_left _ _

/-- **The gap-2 support** from the antecedent of the amended `fgnCov`. -/
theorem suppAll_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl) :
    SuppAll cr pl δ c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j thj Sj l cl := by
  classical
  have hδ := hA.2.2.2.2.2.2.1
  intro Gs hL x hx hn
  obtain ⟨mh, usS, hmh, hlab, hlow, hnw, -, -, -, -, -, -, -, hR, -⟩ := hL.2.1 x hx
  -- the transfer at the holder is nonzero
  have hδn : δ x.1 ≠ .zero := by
    intro h0
    apply hn
    intro k'
    have h1 : x.2.2.2.2.1 k' ≤ crPl cr pl j x.1 k' + δ x.1 k' := hR k'
    rw [h0, Res.zero_apply] at h1
    exact h1
  rcases TermPlant.plantD1_cases Gd TermPiece.GdE.R tg x.1 with h0 | ⟨g, hg, htg, hgR⟩
  · exact absurd ((hδ x.1).trans h0) hδn
  exact tgtSupp_of hA hg htg ((hδ x.1).trans hgR) hmh hlab hlow hnw

/-- **The amended `fgnCov` from OPEN `hWbR` alone** (the gap-2 support discharged). -/
theorem fgnCov_of_wb {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0)
    (hWb : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
      {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
      {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell},
      Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ
        Gd tg j thj Sj l cl → TermPiece.PubShape cx th →
      TermFreeQW.HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (crPl cr pl) j thj Sj l cl) :
    fgnCov p k arch Sp Init MintOK c0 :=
  fgnCov_of hsc hWb (fun hA => suppAll_of hA)

end TermPoolSupp

#print axioms TermPoolSupp.crKeys_entry
#print axioms TermPoolSupp.tgtSupp_of
#print axioms TermPoolSupp.suppAll_of
#print axioms TermPoolSupp.fgnCov_of_wb

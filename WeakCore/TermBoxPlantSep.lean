import WeakCore.TermPtrRtsGLT
import WeakCore.OwnFreshW5b

/-!
# TermBoxPlantSep: the SysInvN clause `BoxPlantSep` and its preservation

`BoxPlantSep` (SysInvN clause): a payload word of a box
naming a gated cell `a` of `j` (with frontier `f` and `tmin` `t`) either has view below `f`, or
every message carrying it at its box slot has index `≥ t`.  The message side is upward-closed in
memory (every new message is above `t < c.mem.size`), so no "no append at a box label" fact is needed.

* thread step of `i` (`boxPlantSep_thread`): a gated cell after the step was gated before with the
  same frontier and `tmin` (`gateBack`; for `i` via K-2a's keep conjunct, as in `ptrRtsGL_thread`).
  For an old box the pre-state clause applies.  A new box is at a fresh label, and no old message
  lies there (`oldMsg_not_fresh`, the W5b site), so the index disjunct holds.
* promise step (`boxPlantSep_prom`): boxes are unchanged.  For an old frontier the `tmin` is unchanged
  (`tminG_prom_own_some`/`tminG_prom_fgn`).  A newly planted cell is the promiser's (`plantOf_target`),
  so `PayOwn` makes it the box's owner, and `BoxPV` and `BoxFrOwn` give `w.view < B.fr ≤ vWr ≤ plantF`.
* initial states: `boxPlantSep_none` (no boxes) and `boxPlantSep_noProm` (no promises).

Certificate facts: none beyond those of `ptrRtsGL_thread` (`hA` now also through W5b).
-/

namespace TermPtrRtsK

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF TermPromClos TermCert TermGlob TermTyped TermPtrRts TermGranW TermBal
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem boxPlantSep_none {Eg : GEnv} {Tot HP : Nat → Res} {c : Cfg} (h : ∀ l, Eg.box l = none) :
    BoxPlantSep Eg Tot HP c :=
  fun l B hB => by rw [h l] at hB; cases hB

theorem boxPlantSep_noProm {Eg : GEnv} {Tot HP : Nat → Res} {c : Cfg} (h : AllNoProm c) :
    BoxPlantSep Eg Tot HP c := by
  intro l B _ o w _ j th a cl f t hj _ _ _ _ ht _
  rw [tminG_eq hj] at ht
  have h1 := (tminOf_spec ht).1
  simp only [stOf, h j th hj] at h1
  cases h1

/-! ## Promise step -/

theorem boxPlantSep_prom {P : AllocLabel → Option Ts} {c : Cfg} {Eg : GEnv} {Tot HP HP2 : Nat → Res} {N : AllocLabel → Nat}
    {j0 n : Nat} {th0 : TTh} {a0 : Address} {v : WeakMem.Val} {w0 : Ts}
    (hth : c.ths[j0]? = some th0)
    (hPL : ∀ l0 f0, P l0 = some f0 → TermPlantF.PlantL c Eg j0 th0 a0 v w0 l0 ∧
      f0 = TermStep.plantF (TermPlantF.cutP Eg j0) (stOf c.mem c.pairs th0) l0) (hplt : AllPromLt c) (hT : GateTmin Eg Tot HP c)
    (hkey : ∀ q l, (Tot q + HP2 q) (.own l) ≤ (Tot q + HP q) (.own l))
    (hPO : TermBoxZ.PayOwn Eg) (hPV : TermBoxZ.BoxPV Eg) (hFO : TermBoxZ.BoxFrOwn Eg c)
    (hBP : BoxPlantSep Eg Tot HP c) :
    BoxPlantSep (EgP Eg P N j0 n) Tot HP2 (promise c j0 a0 v w0) := by
  intro l B hB o w hw j thj a cl f t hj hs ho hp hk ht hN
  have hB0 : Eg.box l = some B := hB
  have hs0 : Eg.sto a = some cl := hs
  have hk0 := Nat.lt_of_lt_of_le hk (hkey j a)
  cases hP : P a with
  | none =>
    have hp0 : Eg.pfr a = some f := by rw [TermPtrStab.egP_pfr_none hP] at hp; exact hp
    obtain ⟨t0, ht0⟩ := Option.ne_none_iff_exists'.1 (hT j a cl f hs0 ho hp0 hk0)
    obtain ⟨th1, hth1⟩ : ∃ th1, c.ths[j]? = some th1 := by
      by_cases hjj : j = j0
      · rw [hjj]; exact ⟨th0, hth⟩
      · exact ⟨thj, (promise_other hjj).symm.trans hj⟩
    have htt : tminG Eg c j a = some t := by
      by_cases hjj : j = j0
      · rw [hjj] at ht ht0 ⊢
        rw [TermPtrStab.tminG_prom_own_some (a := a0) (v := v) (w := w0) hth hplt ht0] at ht
        rw [ht0, ht]
      · rw [TermPtrStab.tminG_prom_fgn hth hplt hjj] at ht
        exact ht
    have htl : t < c.mem.size := by
      rw [tminG_eq hth1] at htt
      exact hplt j th1 t hth1 (tminOf_spec htt).1
    rcases hBP l B hB0 o w hw j th1 a cl f t hth1 hs0 ho hp0 hk0 htt hN with h | h
    · exact .inl h
    · right
      intro u m hu hl hv
      rw [TermPtrStab.promise_mem hth] at hu
      by_cases hu' : u = c.mem.size
      · rw [hu']; exact Nat.le_of_lt htl
      · exact h u m (TermPtrStab.push_get_ne hu hu') hl hv
  | some f' =>
    obtain ⟨cl', hcl', ho', hpn⟩ := TermPtrStab.plantOf_target hPL hP
    rw [hs0] at hcl'
    cases hcl'
    have hff : f = f' := by
      have h2 : (EgP Eg P N j0 n).pfr a = some f' := by
        simp [EgP, GEnv.withFp, plantG, hP]
      rw [h2] at hp
      exact (Option.some.inj hp).symm
    obtain ⟨-, hfe⟩ := hPL _ _ hP
    obtain ⟨a', g, hv, hl'⟩ := hN
    have hmem : w ∈ B.pay := List.mem_of_getElem? hw
    have hown := hPO l B hB0 w hmem a' g hv cl (by rw [hl']; exact hs0) (by rw [hl']; exact hpn)
    have hBo : B.own = j0 := Option.some.inj (hown.symm.trans ho')
    have hpv := hPV l B hB0 w hmem a' g hv
    have hfo := hFO l B hB0 th0 (by rw [hBo]; exact hth)
    left
    rw [hff, hfe]
    exact Nat.lt_of_lt_of_le hpv (Nat.le_trans hfo (Nat.le_max_left _ _))

/-! ## Thread step -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
  {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
  {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- A gated cell after a thread step was gated before, with the same frontier and `tmin`. -/
theorem gateBack
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    {j : Nat} {thj : TTh} {a : AllocLabel} {cl : Cell} {f t : Ts} (hj : c'.ths[j]? = some thj)
    (hs : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto a = some cl) (ho : cl.owner = some j)
    (hp : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr a = some f)
    (hk' : 0 < (upd Tot i Tot' j + upd HP i HP' j) (.own a))
    (ht : tminG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' j a = some t) :
    ∃ th0, c.ths[j]? = some th0 ∧ Eg.sto a = some cl ∧ Eg.pfr a = some f ∧ 0 < (Tot j + HP j) (.own a) ∧
      tminG Eg c j a = some t := by
  have hs0 := stoOld H hs hp
  by_cases hji : j = i
  · rw [hji] at hj ho hk' ht ⊢
    obtain ⟨⟨⟨-, htm⟩, -⟩, t0, ht0⟩ := ownGate H hs ho hp hk'
    rw [tminG_eq H.X.e3, H.X.e1, H.X.e2, htm t0 ht0] at ht
    cases ht
    have hnf := notFresh H hs hp
    rw [upd_self, upd_self] at hk'
    have hk0 := Nat.lt_of_lt_of_le hk' (TermPtrKey.ownKey_noIncrease_thread_noHS H.hb1 H.X H.Y H.Z H.hKS hnf)
    obtain ⟨f0, hf0⟩ := pfrOldOwn H hnf hs0 hp hk'
    have hff : f0 = f := Option.some.inj ((pfrKeepT H a f0 hf0).symm.trans hp)
    rw [hff] at hf0
    refine ⟨th, H.X.hth, hs0, hf0, hk0, ?_⟩
    rw [tminG_eq H.X.hth]
    exact ht0
  · have hq : c.ths[j]? = some thj := (H.X.ho j hji).symm.trans hj
    rw [upd_other _ _ hji, upd_other _ _ hji] at hk'
    rw [TermPtrStab.tminG_thread_fgn H.X E' hji] at ht
    exact ⟨thj, hq, hs0, pfrOldFgn H (notFresh H hs hp) hs0 ho hji hp, hk', ht⟩

theorem boxPlantSep_T
    (H : GLT p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS)
    (hBP : BoxPlantSep Eg Tot HP c) :
    BoxPlantSep (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' := by
  intro l B hB o w hw j thj a cl f t hj hs ho hp hk' ht hN
  obtain ⟨th0, hj0, hs0, hp0, hk0, ht0⟩ := gateBack H hj hs ho hp hk' ht
  have htl : t < c.mem.size := by
    rw [tminG_eq hj0] at ht0
    exact H.X.inv.plt j th0 t hj0 (tminOf_spec ht0).1
  have hpost : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box l = some B := hB
  by_cases hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · right
    intro u m hu hl hv
    rcases Nat.lt_or_ge u c.mem.size with hlt | hge
    · have hml : m.loc.label = l := by rw [hl]
      exact absurd (by rw [hml]; exact hf) (oldMsg_not_fresh H.hA H.X H.Y (H.Z.toC _ _ _ _ _) H.hS H.hPfrP hlt hu)
    · exact Nat.le_of_lt (Nat.lt_of_lt_of_le htl hge)
  · rw [post_box_old hf] at hpost
    rcases hBP l B hpost o w hw j th0 a cl f t hj0 hs0 ho hp0 hk0 ht0 hN with h | h
    · exact .inl h
    · right
      intro u m hu hl hv
      rcases Nat.lt_or_ge u c.mem.size with hlt | hge
      · exact h u m ((tctx_pre H.X u hlt).symm.trans hu) hl hv
      · exact Nat.le_of_lt (Nat.lt_of_lt_of_le htl hge)

/-- **`boxPlantSep_thread`**: `BoxPlantSep` across a thread step of `i`, at `EgT` with
`upd Tot i Tot'`, `upd HP i HP'`; hypotheses of `ptrRtsGL_thread` plus the pre-state clause. -/
theorem boxPlantSep_thread (hK : PtrRtsThreadGL p) (hk : k.storeDepRts = true)
    (hb1 : AllocGT p k arch Sp Init MintOK c0) (hA : PromAllocF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hKS : ∀ t l, crS t (.own l) = cr i t (.own l))
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hPC : TermPtrKey.PubConsumeC th C)
    (hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hNCE : FootNCE (CE η) E' r) (hG : PtrRtsGL Eg Tot HP c) (hGW : GranuleW Eg.sto c.mem c.pairs)
    (hLay : ∀ l cl, Eg.sto l = some cl → LayT cl.ty) (hsc : TermTyped.ScopeOK p th)
    (hdrf : TermScope.ThScope th) (hps : TermScope.ProgScopeOK p = true) (hPT : ProgT p)
    (hFBP : TermFootBP0.FootBP { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } E' th r)
    (hRP : RetPw th.σs th.stack cx.ret) (hBP : BoxPlantSep Eg Tot HP c) :
    BoxPlantSep (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') c' :=
  boxPlantSep_T (S := S) (ρ := ρ) (cx := cx) (F := F)
    ⟨hK, hk, hb1, hA, X, Y, Z, hS, hKS, hm, hPC, hPfrP, hNCE, hG, hGW, hLay, hsc, hdrf, hps, hPT, hFBP, hRP, hBP⟩ hBP

end

end TermPtrRtsK

#print axioms TermPtrRtsK.boxPlantSep_thread
#print axioms TermPtrRtsK.boxPlantSep_prom
#print axioms TermPtrRtsK.boxPlantSep_none
#print axioms TermPtrRtsK.boxPlantSep_noProm

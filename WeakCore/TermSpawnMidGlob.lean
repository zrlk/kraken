import WeakCore.TermSpawnMid
/-!
# TermSpawnMidGlob — the share of the `SysInvN` clauses after a mid-run spawn (M4)

Clauses: bf proms fpok disj fpfree plt vwr vwrLt frle frlt rle promIni promTy promNU promNoTwo promInCut
promClos promAbove fgnClos ownCoh riniCoh (thr/fresh: stride-dependent, stated with explicit premises).
-/
namespace TermSpawnMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {c : Cfg} {i : Nat} {th par kid : TTh} {Eg : GEnv}

/-- The barrier keeps `vWr` and `coh`. -/
theorem fenceSy_vWr (s : St) : (fenceS s .sy).vs.vWr = s.vs.vWr := rfl
theorem fenceSy_coh (s : St) : (fenceS s .sy).vs.coh = s.vs.coh := rfl

/-- A clause over every outstanding promise transfers: the parent and the kid hold none. -/
theorem spawnT_promAll (hth : c.ths[i]? = some th) (hpp : par.promises = []) (hkp : kid.promises = [])
    {P : Nat → TTh → Ts → Prop} (h : ∀ j tj t, c.ths[j]? = some tj → t ∈ tj.promises → P j tj t) :
    ∀ j tj t, (spawnT c i par kid).ths[j]? = some tj → t ∈ tj.promises → P j tj t := by
  intro j tj t hj ht
  rcases spawnT_get_cases (TermSpawn.lt_of_get hth) hj with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, hj'⟩
  · rw [hpp] at ht; cases ht
  · rw [hkp] at ht; cases ht
  · exact h j tj t hj' ht

/-- A clause over every thread with `P` true of the parent and the kid transfers. -/
theorem spawnT_thAll (hth : c.ths[i]? = some th) {P : Nat → TTh → Prop}
    (h : ∀ j tj, c.ths[j]? = some tj → j ≠ i → P j tj) (hP : P i par) (hK : P c.ths.size kid) :
    ∀ j tj, (spawnT c i par kid).ths[j]? = some tj → P j tj := by
  intro j tj hj
  rcases spawnT_get_cases (TermSpawn.lt_of_get hth) hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hji, -, hj'⟩
  · exact hP
  · exact hK
  · exact h j tj hj' hji

variable (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = [])
include hth hpp hkp

theorem plt_spawnT (h : AllPromLt c) : AllPromLt (spawnT c i par kid) :=
  spawnT_promAll hth hpp hkp (P := fun _ _ t => t < c.mem.size) (fun j tj t hj ht => h j tj t hj ht)

theorem disj_spawnT (h : PromsDisj c) : PromsDisj (spawnT c i par kid) := by
  intro a b ta tb t hab ha hb hta htb
  have hi := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi ha with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, ha'⟩
  · rw [hpp] at hta; cases hta
  · rw [hkp] at hta; cases hta
  rcases spawnT_get_cases hi hb with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, hb'⟩
  · rw [hpp] at htb; cases htb
  · rw [hkp] at htb; cases htb
  exact h a b ta tb t hab ha' hb' hta htb

theorem promIni_spawnT (h : PromIniOK Eg c) : PromIniOK (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m hj ht hm => spawnT_promAll hth hpp hkp
    (P := fun _ _ t => ∀ m, c.mem[t]? = some m → ∀ cl, Eg.sto m.loc.label = some cl → Eg.Shared m.loc.label →
      InitR (PubE Eg) cl m.loc.label m.loc.offset) (fun j tj t hj ht m hm => h j tj t m hj ht hm) j tj t hj ht m hm

theorem promTy_spawnT (h : PromTyAOK Eg c) : PromTyAOK (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m hj ht hm => spawnT_promAll hth hpp hkp
    (P := fun _ _ t => ∀ m, c.mem[t]? = some m → ∀ cl, Eg.sto m.loc.label = some cl → Eg.Shared m.loc.label →
      WordOK (PubE Eg) cl.ty m.loc.offset (mw m)) (fun j tj t hj ht m hm => h j tj t m hj ht hm) j tj t hj ht m hm

theorem promNU_spawnT (h : PromNotUndef c) : PromNotUndef (spawnT c i par kid) :=
  fun j tj t m hj ht hm => spawnT_promAll hth hpp hkp
    (P := fun _ _ t => ∀ m, c.mem[t]? = some m → m.val ≠ .undef) (fun j tj t hj ht m hm => h j tj t m hj ht hm)
    j tj t hj ht m hm

theorem promNoTwo_spawnT (h : PromNoTwoOK Eg c) : PromNoTwoOK (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m cl hj ht hm => spawnT_promAll hth hpp hkp
    (P := fun _ _ t => ∀ m cl, c.mem[t]? = some m → Eg.sto m.loc.label = some cl → ∀ o, TwoAtT cl.ty o →
      m.loc.offset ≠ o ∧ m.loc.offset ≠ o + 1) (fun j tj t hj ht m cl hm => h j tj t m cl hj ht hm) j tj t hj ht m cl hm

theorem promInCut_spawnT (h : TermPtrStab.PromInCut Eg c) : TermPtrStab.PromInCut (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m hj ht hm => spawnT_promAll hth hpp hkp
    (P := fun j _ t => ∀ m, c.mem[t]? = some m → ∀ cm, Eg.sto m.loc.label = some cm → cm.owner = some j ∨ Eg.Shared m.loc.label)
    (fun j tj t hj ht m hm => h j tj t m hj ht hm) j tj t hj ht m hm

theorem promClos_spawnT (h : PromClosG Eg c) : PromClosG (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m hj ht hm => spawnT_promAll hth hpp hkp
    (P := fun j _ t => ∀ m, c.mem[t]? = some m →
      ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cl, Eg.sto a'.label = some cl → cl.owner = some j →
      ∀ cm, Eg.sto m.loc.label = some cm → (cm.owner = some j ∨ Eg.Shared m.loc.label) →
        Ty.noOwnIn [] cm.ty = true → rgnFree cm.ty = true → ∃ f, Eg.pfr a'.label = some f)
    (fun j tj t hj ht m hm => h j tj t m hj ht hm) j tj t hj ht m hm

/-- `fgnClos`, given the target transfer (`TgtOK` reads the stride `c.ths.size`; on M0 it is `c.n`, kept). -/
theorem fgnClos_spawnT (h : FgnPromClosG Eg c)
    (hT : ∀ j l, TgtOK Eg c j l → TgtOK (EgK Eg c) (spawnT c i par kid) j l) :
    FgnPromClosG (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m hj ht hm a' g hv cm hcm hno hrg => hT j _ (spawnT_promAll hth hpp hkp
    (P := fun j _ t => ∀ m, c.mem[t]? = some m →
      ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cm, Eg.sto m.loc.label = some cm →
        Ty.noOwnIn [] cm.ty = true → rgnFree cm.ty = true → TgtOK Eg c j a'.label)
    (fun j tj t hj ht m hm => h j tj t m hj ht hm) j tj t hj ht m hm a' g hv cm hcm hno hrg)

theorem promAbove_spawnT (h : TermOverCr.PromAboveG c) : TermOverCr.PromAboveG (spawnT c i par kid) :=
  spawnT_thAll hth (P := fun _ tj => PromAbove (stOf c.mem c.pairs tj)) (fun j tj hj _ => h j tj hj)
    (fun t ht => by simp [stOf, hpp] at ht) (fun t ht => by simp [stOf, hkp] at ht)

theorem fpfree_spawnT (h : FpOwnFree Eg c) : FpOwnFree (EgK Eg c) (spawnT c i par kid) :=
  fun j0 tj0 t0 hj0 => spawnT_thAll hth (P := fun j tj => ∀ t, t ∈ (EgK Eg c).fpOf j → t ∉ tj.promises)
    (fun j tj hj _ t ht => by
      have hjn : j ≠ c.ths.size := fun e => by subst e; simp at hj
      rw [EgK_fp_ne Eg c hjn] at ht; exact h j tj t hj ht)
    (fun t _ => by rw [hpp]; exact List.not_mem_nil) (fun t _ => by rw [hkp]; exact List.not_mem_nil) j0 tj0 hj0 t0

include hnp in
theorem proms_spawnT (h : PromsOK Eg c) : PromsOK (EgK Eg c) (spawnT c i par kid) := by
  have hi := TermSpawn.lt_of_get hth
  refine spawnT_thAll hth (P := fun j tj => ∀ t, t ∈ tj.promises ++ (EgK Eg c).fpOf j ↔ t ∈ allProms (spawnT c i par kid))
    (fun j tj hj _ t => ?_) (fun t => ?_) (promsOK_kid hth hnp hpp hkp)
  · have hjn : j ≠ c.ths.size := fun e => by subst e; simp at hj
    rw [EgK_fp_ne Eg c hjn, mem_allProms_spawnT hth hnp hpp hkp]; exact h j tj hj t
  · rw [EgK_fp_ne Eg c (Nat.ne_of_lt hi), mem_allProms_spawnT hth hnp hpp hkp, hpp, ← h i th hth t, hnp]

end

section
variable {c : Cfg} {i : Nat} {th par kid : TTh} {Eg : GEnv}

theorem bf_spawnT (h : c.boxFence = true) : (spawnT c i par kid).boxFence = true := h
theorem frle_spawnT (h : FrontierLe Eg c.mem.size) : FrontierLe (EgK Eg c) (spawnT c i par kid).mem.size := h
theorem frlt_spawnT (h : FrontierLe Eg (c.mem.size - 1)) : FrontierLe (EgK Eg c) ((spawnT c i par kid).mem.size - 1) := h
theorem rle_spawnT (h : ∀ l, Eg.rini l ≤ Eg.ini l) : ∀ l, (EgK Eg c).rini l ≤ (EgK Eg c).ini l := h

/-- The parent's and the kid's `vWr` are the parent's old one. -/
theorem vWr_par {par : TTh} (hv : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs) : par.vs.vWr = th.vs.vWr := by
  rw [hv]; rfl

theorem vwr_spawnT {f : String} {ts : List Ty} {t : Ty} {ws : List Word} (hth : c.ths[i]? = some th)
    (hv : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs) (hK : KidShape par kid f ts t ws) {N : Nat}
    (h : ∀ (j : Nat) (tj : TTh), c.ths[j]? = some tj → tj.vs.vWr ≤ N) :
    ∀ (j : Nat) (tj : TTh), (spawnT c i par kid).ths[j]? = some tj → tj.vs.vWr ≤ N :=
  spawnT_thAll hth (P := fun _ (tj : TTh) => tj.vs.vWr ≤ N) (fun j tj hj _ => h j tj hj)
    (by rw [vWr_par hv]; exact h i th hth) (by rw [hK.vs]; show par.vs.vWr ≤ N; rw [vWr_par hv]; exact h i th hth)

theorem fpok_spawnT (hth : c.ths[i]? = some th) (hpp : par.promises = []) (hkp : kid.promises = [])
    (hOL : OwnLive Eg c) (hplt : AllPromLt c)
    (h : ∀ j tj (S : AllocLabel → Prop), c.ths[j]? = some tj → FpOK (Cut Eg j S) (stOf c.mem c.pairs tj)) :
    ∀ j tj (S : AllocLabel → Prop), (spawnT c i par kid).ths[j]? = some tj →
      FpOK (Cut (EgK Eg c) j S) (stOf (spawnT c i par kid).mem (spawnT c i par kid).pairs tj) := by
  intro j tj S hj
  have hi := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
  · rw [cut_EgK_ne Eg c (Nat.ne_of_lt hi)]; exact h j th S hth
  · refine ⟨fun t ht => ?_, fun t m ht hm hP => ?_⟩
    · rw [Cut_fp, EgK_fp_kid] at ht
      obtain ⟨q, tq, hq, htq⟩ := TermStepper.mem_allProms.1 ht
      exact hplt q tq t hq htq
    · obtain ⟨⟨c1, hc1, ho⟩, -⟩ := hP
      exact cutSto_kid_own hOL hc1 ho
  · rw [cut_EgK_ne Eg c hjn]; exact h j tj S hj'

theorem ownCoh_spawnT (hth : c.ths[i]? = some th)
    (hv : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs) (hOL : OwnLive Eg c)
    (h : ∀ j tj (S : AllocLabel → Prop), c.ths[j]? = some tj → TermOwnCohZ.OwnCohZ (Cut Eg j S) (stOf c.mem c.pairs tj)) :
    ∀ j tj (S : AllocLabel → Prop), (spawnT c i par kid).ths[j]? = some tj →
      TermOwnCohZ.OwnCohZ (Cut (EgK Eg c) j S) (stOf (spawnT c i par kid).mem (spawnT c i par kid).pairs tj) := by
  intro j tj S hj
  have hi := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
  · rw [cut_EgK_ne Eg c (Nat.ne_of_lt hi)]
    intro l cl hc ho hp o ho'
    have := h j th S hth l cl hc ho hp o ho'
    simp only [stOf] at this ⊢; rw [hv]; exact this
  · intro l cl hc ho
    exact absurd ho (cutSto_kid_own hOL hc)
  · rw [cut_EgK_ne Eg c hjn]; exact h j tj S hj'

theorem riniCoh_spawnT (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = [])
    (hOL : OwnLive Eg c)
    (h : ∀ j tj (S : AllocLabel → Prop), c.ths[j]? = some tj → TermTyped.RiniCoh (Cut Eg j S) (stOf c.mem c.pairs tj)) :
    ∀ j tj (S : AllocLabel → Prop), (spawnT c i par kid).ths[j]? = some tj →
      TermTyped.RiniCoh (Cut (EgK Eg c) j S) (stOf (spawnT c i par kid).mem (spawnT c i par kid).pairs tj) := by
  intro j tj S hj
  have hi := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
  · rw [cut_EgK_ne Eg c (Nat.ne_of_lt hi)]
    intro t m cl N e us f _ hm hc ho hf htf hty hu h1 h2
    exact h j th S hth t m cl N e us f (by simp [stOf, hnp]) hm hc ho hf htf hty hu h1 h2
  · intro t m cl N e us f _ hm hc ho
    exact absurd ho (cutSto_kid_own hOL hc)
  · rw [cut_EgK_ne Eg c hjn]; exact h j tj S hj'

/-- `fresh` after the spawn, given the old threads' freshness at the post-spawn stride (`hFrS`; on M0
the stride is `c.n`, unchanged, and `hFrS` is `SysInvN.fresh`) and the kid's stripe (`hU`, freshU). -/
theorem fresh_spawnT (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = [])
    (hkp : kid.promises = []) (hna : par.nalloc = th.nalloc)
    (hFrS : ∀ j tj, c.ths[j]? = some tj → ∀ q, tj.nalloc ≤ q →
      GFreshL Eg c tj (freshLabel c.lbase (spawnT c i par kid).n j q))
    (hU : ∀ q, Eg.sto (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.box (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.ini (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = 0 ∧
      Eg.pfr (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m →
        m.loc.label ≠ freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) :
    ∀ j tj, (spawnT c i par kid).ths[j]? = some tj → ∀ q, tj.nalloc ≤ q →
      GFreshL (EgK Eg c) (spawnT c i par kid) tj
        (freshLabel (spawnT c i par kid).lbase (spawnT c i par kid).n j q) := by
  intro j tj hj q hq
  have hi := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, hj'⟩
  · obtain ⟨f1, f2, f3, f4, f5⟩ := hFrS j th hth q (by rw [← hna]; exact hq)
    refine ⟨f1, f2, f3, f4, fun t m hm hl => ?_⟩
    have := f5 t m hm hl; rw [hnp] at this; cases this
  · obtain ⟨f1, f2, f3, f4, f5⟩ := hU q
    exact ⟨f1, f2, f3, f4, fun t m hm hl => absurd hl (f5 t m hm)⟩
  · exact hFrS j tj hj' q hq

end

section
variable {c : Cfg} {i : Nat} {th par kid : TTh} {Eg : GEnv}

theorem stoW_spawnT (h : ∀ l cl, Eg.sto l = some cl → TermA4.wrapTop cl.ty = true) :
    ∀ l cl, (EgK Eg c).sto l = some cl → TermA4.wrapTop cl.ty = true := h

theorem cfgCoh_spawnT {f : String} {ts : List Ty} {t : Ty} {ws : List Word} (hth : c.ths[i]? = some th)
    (hv : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs) (hK : KidShape par kid f ts t ws)
    (h : TermLiveProps.CfgCoh c) : TermLiveProps.CfgCoh (spawnT c i par kid) := by
  have hp : TermLiveProps.CohAt c.mem par.vs := by
    rw [hv]; exact h i th hth
  exact spawnT_thAll hth (P := fun _ (tj : TTh) => TermLiveProps.CohAt c.mem tj.vs) (fun j tj hj _ => h j tj hj) hp
    (by rw [hK.vs]; exact hp)

theorem fgnCnt_spawnT (hth : c.ths[i]? = some th) (hpp : par.promises = []) (hkp : kid.promises = [])
    (h : FgnPromCntG Eg c) (hT : ∀ j l, TgtOK Eg c j l → TgtOK (EgK Eg c) (spawnT c i par kid) j l) :
    FgnPromCntG (EgK Eg c) (spawnT c i par kid) :=
  fun j tj t m hj ht hm a' g hv cm hcm hns hco => hT j _ (spawnT_promAll hth hpp hkp
    (P := fun j _ t => ∀ m, c.mem[t]? = some m →
      ∀ (a' : Address) (g : Nat), m.val = .loc a' g → ∀ cm, Eg.sto m.loc.label = some cm →
        TermPtrRts.NotSnd cm.ty m.loc.offset → TermPtrRts.CntOK cm.ty m.loc.offset (mw m) → TgtOK Eg c j a'.label)
    (fun j tj t hj ht m hm => h j tj t m hj ht hm) j tj t hj ht m hm a' g hv cm hcm hns hco)

end

end TermSpawnMid
#print axioms TermSpawnMid.plt_spawnT
#print axioms TermSpawnMid.disj_spawnT
#print axioms TermSpawnMid.promIni_spawnT
#print axioms TermSpawnMid.promTy_spawnT
#print axioms TermSpawnMid.promNU_spawnT
#print axioms TermSpawnMid.promNoTwo_spawnT
#print axioms TermSpawnMid.promInCut_spawnT
#print axioms TermSpawnMid.promClos_spawnT
#print axioms TermSpawnMid.fgnClos_spawnT
#print axioms TermSpawnMid.promAbove_spawnT
#print axioms TermSpawnMid.fpfree_spawnT
#print axioms TermSpawnMid.proms_spawnT
#print axioms TermSpawnMid.vwr_spawnT
#print axioms TermSpawnMid.fpok_spawnT
#print axioms TermSpawnMid.ownCoh_spawnT
#print axioms TermSpawnMid.riniCoh_spawnT
#print axioms TermSpawnMid.fresh_spawnT
#print axioms TermSpawnMid.cfgCoh_spawnT
#print axioms TermSpawnMid.fgnCnt_spawnT
#print axioms TermSpawnMid.fenceSy_vWr
#print axioms TermSpawnMid.fenceSy_coh
#print axioms TermSpawnMid.spawnT_promAll
#print axioms TermSpawnMid.spawnT_thAll
#print axioms TermSpawnMid.bf_spawnT
#print axioms TermSpawnMid.frle_spawnT
#print axioms TermSpawnMid.frlt_spawnT
#print axioms TermSpawnMid.rle_spawnT
#print axioms TermSpawnMid.vWr_par
#print axioms TermSpawnMid.stoW_spawnT

import WeakCore.TermSpawnSim
import WeakCore.TermMain
/-! # TermSpawnPh — the invariant at the phantom start -/
namespace TermSpawnSim
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem phantC_cases {f0 : Frame} {c : Cfg} {i : Nat} {th : TTh} (h : (phantC f0 c).ths[i]? = some th) :
    ∃ th0, c.ths[i]? = some th0 ∧ (th = app f0 th0 ∨ th = th0) := by
  rw [phantC_get] at h
  split at h
  · obtain ⟨th0, h0, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨th0, h0, .inl rfl⟩
  · exact ⟨th, h, .inr rfl⟩

@[simp] theorem phantC_mem (f0 : Frame) (c : Cfg) : (phantC f0 c).mem = c.mem := rfl
@[simp] theorem phantC_pairs (f0 : Frame) (c : Cfg) : (phantC f0 c).pairs = c.pairs := rfl
@[simp] theorem phantC_lbase (f0 : Frame) (c : Cfg) : (phantC f0 c).lbase = c.lbase := rfl
@[simp] theorem phantC_bf (f0 : Frame) (c : Cfg) : (phantC f0 c).boxFence = c.boxFence := rfl
@[simp] theorem phantC_size' (f0 : Frame) (c : Cfg) : (phantC f0 c).ths.size = c.ths.size := phantC_size f0 c
@[simp] theorem phantC_n (f0 : Frame) (c : Cfg) : (phantC f0 c).n = c.n := by simp [Cfg.n, phantC]

theorem phantC_promises (f0 : Frame) (c : Cfg) (i : Nat) :
    ((phantC f0 c).ths[i]?).map (·.promises) = (c.ths[i]?).map (·.promises) := by
  rw [phantC_get]; split <;> (try cases c.ths[i]?) <;> rfl


/-- `appIf`: what thread `i` of the phantom configuration is. -/
def appIf (f0 : Frame) (i : Nat) (th : TTh) : TTh := if i = 0 then app f0 th else th

@[simp] theorem appIf_promises (f0 : Frame) (i : Nat) (th : TTh) : (appIf f0 i th).promises = th.promises := by
  unfold appIf; split <;> rfl
@[simp] theorem appIf_vs (f0 : Frame) (i : Nat) (th : TTh) : (appIf f0 i th).vs = th.vs := by
  unfold appIf; split <;> rfl
@[simp] theorem appIf_nalloc (f0 : Frame) (i : Nat) (th : TTh) : (appIf f0 i th).nalloc = th.nalloc := by
  unfold appIf; split <;> rfl
@[simp] theorem appIf_undefs (f0 : Frame) (i : Nat) (th : TTh) : (appIf f0 i th).undefs = th.undefs := by
  unfold appIf; split <;> rfl
@[simp] theorem stOf_appIf (f0 : Frame) (i : Nat) (mem : Memory) (pairs : List Ts) (th : TTh) :
    stOf mem pairs (appIf f0 i th) = stOf mem pairs th := by
  unfold appIf; split <;> rfl

theorem phantC_some_iff {f0 : Frame} {c : Cfg} {i : Nat} {th : TTh} :
    (phantC f0 c).ths[i]? = some th ↔ ∃ th0, c.ths[i]? = some th0 ∧ appIf f0 i th0 = th := by
  rw [phantC_get]; unfold appIf
  split
  · subst_vars; simp [Option.map_eq_some_iff]
  · simp

theorem allProms_phantC (f0 : Frame) (c : Cfg) : allProms (phantC f0 c) = allProms c := by
  unfold allProms
  show ((phantC f0 c).ths.toList.map (·.promises)).flatten = (c.ths.toList.map (·.promises)).flatten
  congr 1
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, Array.getElem?_toList]
  exact phantC_promises f0 c j

theorem pSumAt_phantC (f0 : Frame) (c : Cfg) (i : Nat) (f : Ts → Res) : pSumAt (phantC f0 c) i f = pSumAt c i f := by
  unfold pSumAt
  rw [phantC_get]
  by_cases hi : i = 0 <;> cases hc : c.ths[i]? <;> simp [hi] <;> rfl

theorem promAtG_phantC (f0 : Frame) (Eg : GEnv) (c : Cfg) (a : Address) : PromAtG Eg (phantC f0 c) a = PromAtG Eg c a := by
  unfold PromAtG; rw [allProms_phantC]; rfl

attribute [local simp] allProms_phantC pSumAt_phantC promAtG_phantC


theorem ph_get {f0 : Frame} {c : Cfg} {i : Nat} {th : TTh} (h : (phantC f0 c).ths[i]? = some th) :
    ∃ th0, c.ths[i]? = some th0 ∧ th.promises = th0.promises ∧ th.vs = th0.vs ∧ th.nalloc = th0.nalloc ∧
      ∀ m ps, stOf m ps th = stOf m ps th0 := by
  obtain ⟨th0, h0, rfl⟩ := phantC_some_iff.1 h
  exact ⟨th0, h0, by simp, by simp, by simp, fun _ _ => by simp⟩

theorem ph_get0 {f0 : Frame} {c : Cfg} {i : Nat} {th : TTh} (h : c.ths[i]? = some th) :
    (phantC f0 c).ths[i]? = some (appIf f0 i th) := phantC_some_iff.2 ⟨th, h, rfl⟩

theorem tminG_phantC (f0 : Frame) (Eg : GEnv) (c : Cfg) (j : Nat) (a : AllocLabel) :
    TermPtrRts.tminG Eg (phantC f0 c) j a = TermPtrRts.tminG Eg c j a := by
  unfold TermPtrRts.tminG
  cases h : (phantC f0 c).ths[j]? with
  | none =>
    cases h0 : c.ths[j]? with
    | none => rfl
    | some th0 => rw [ph_get0 h0] at h; cases h
  | some th =>
    obtain ⟨th0, h0, rfl⟩ := phantC_some_iff.1 h
    simp only [h0, stOf_appIf, phantC_mem, phantC_pairs]

theorem thRts_appIf {f0 : Frame} {i : Nat} {th : TTh} {t : Ts} {a : AllocLabel} (h : TermPtrRts.ThRts t a th)
    (hfe : f0.env = []) : TermPtrRts.ThRts t a (appIf f0 i th) := by
  unfold appIf; split
  · refine ⟨h.1, fun f hf => ?_⟩
    simp only [app, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact h.2 f hf
    · intro x rt ws hm; rw [hfe] at hm; cases hm
  · exact h

theorem lblSto_phantC {Eg : GEnv} {c : Cfg} {f0 : Frame} (h : TermPtrRts.LblSto Eg c) (hfe : f0.env = []) :
    TermPtrRts.LblSto Eg (phantC f0 c) := by
  intro i th hi
  obtain ⟨th0, h0, rfl⟩ := phantC_some_iff.1 hi
  have ht := h i th0 h0
  unfold appIf; split
  · refine ⟨ht.1, fun f hf => ?_⟩
    simp only [app, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact ht.2 f hf
    · intro x rt ws hm; rw [hfe] at hm; cases hm
  · exact ht

set_option maxHeartbeats 400000 in
theorem sysInvN_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {f0 : Frame}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (h0 : ∀ th, c.ths[0]? = some th →
      ThSys p (gOf p k arch c 0) c.mem c.pairs (app f0 th) Eg (Tot 0) (HP 0) HS (cr 0) (db 0)) (hfe : f0.env = []) :
    SysInvN p k arch Init MintOK (phantC f0 c) Eg Tot HP HS cr db := by
  have hg : ∀ i, gOf p k arch (phantC f0 c) i = gOf p k arch c i := gOf_phantC p k arch f0 c
  constructor
  case thr =>
    intro i th hi
    obtain ⟨th0, hc, rfl⟩ := phantC_some_iff.1 hi
    rw [hg]; unfold appIf; split
    · subst_vars; exact h0 th0 hc
    · exact h.thr i th0 hc
  case held => simpa only [MemHeldG, promAtG_phantC, phantC_mem] using h.held
  case clo => exact h.clo
  case cmg => exact h.cmg
  case shty => exact h.shty
  case proms =>
    intro i th hi t; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp, allProms_phantC]; exact h.proms i th0 h0 t
  case fpok =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hi; rw [hs]; exact h.fpok i th0 S h0
  case fresh =>
    intro i th hi j hj; obtain ⟨th0, h0, hp, -, hn, -⟩ := ph_get hi
    have := h.fresh i th0 h0 j (hn ▸ hj)
    unfold GFreshL at *; rw [hp]; simpa only [phantC_mem, phantC_lbase, phantC_size', phantC_n] using this
  case bal => simpa only [phantC_size', phantC_n, pSumAt_phantC] using h.bal
  case knet => intro key hk; simpa only [KeyNet, phantC_size', phantC_n, pSumAt_phantC] using h.knet key hk
  case bf => exact h.bf
  case boxtop => simpa only [BoxTopG, allProms_phantC, phantC_mem] using h.boxtop
  case disj =>
    intro i j thi thj t hij hi hj ht
    obtain ⟨ti, hi0, hpi, -⟩ := ph_get hi; obtain ⟨tj, hj0, hpj, -⟩ := ph_get hj
    rw [hpi] at ht; rw [hpj]; exact h.disj i j ti tj t hij hi0 hj0 ht
  case fpfree =>
    intro i th t hi ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp]; exact h.fpfree i th0 t h0 ht
  case plt =>
    intro i th t hi ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp] at ht; exact h.plt i th0 t h0 ht
  case vwr => intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := ph_get hi; rw [hv]; exact h.vwr i th0 h0
  case frle => exact h.frle
  case rle => exact h.rle
  case zwIni => exact h.zwIni
  case predHold =>
    intro j th S a hj; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp]; exact h.predHold j th0 S a h0
  case bnamed => exact h.bnamed
  case rid => simpa only [RidOK, phantC_size', phantC_n, pSumAt_phantC] using h.rid
  case promIni =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp] at ht; exact h.promIni j th0 t m h0 ht
  case promTy =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp] at ht; exact h.promTy j th0 t m h0 ht
  case promNU =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp] at ht; exact h.promNU j th0 t m h0 ht
  case ownF =>
    intro q thq j hq hj; obtain ⟨th0, h0, -, -, hn, -⟩ := ph_get hq
    have := h.ownF q th0 j h0 (hn ▸ hj)
    simpa only [phantC_size', phantC_n, pSumAt_phantC, phantC_lbase] using this
  case promNoTwo =>
    intro j th t m cl hj ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp] at ht; exact h.promNoTwo j th0 t m cl h0 ht
  case undefAt => exact h.undefAt
  case ownKeyOwn => intro j th l hj; obtain ⟨th0, h0, -⟩ := ph_get hj; exact h.ownKeyOwn j th0 l h0
  case ownPub =>
    intro l hl; obtain ⟨a, b⟩ := h.ownPub l hl
    refine ⟨a, fun hs => ⟨fun j th hj => ?_, (b hs).2⟩⟩
    obtain ⟨th0, h0, -⟩ := ph_get hj; exact (b hs).1 j th0 h0
  case boxPV => exact h.boxPV
  case boxFrOwn =>
    intro l B hB th hth; obtain ⟨th0, h0, -, hv, -⟩ := ph_get hth; rw [hv]; exact h.boxFrOwn l B hB th0 h0
  case boxFrLe => exact h.boxFrLe
  case vwrLt => intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := ph_get hi; rw [hv]; exact h.vwrLt i th0 h0
  case boxFrLt => exact h.boxFrLt
  case frlt => exact h.frlt
  case payOwn => exact h.payOwn
  case boxSto => exact h.boxSto
  case ownCoh =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hi; rw [hs]; exact h.ownCoh i th0 S h0
  case riniCoh =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hi; rw [hs]; exact h.riniCoh i th0 S h0
  case promInCut =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp] at ht; exact h.promInCut j th0 t m h0 ht
  case promClos =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hj; rw [hp] at ht; exact h.promClos j th0 t m h0 ht
  case stoNI => exact h.stoNI
  case stoW => exact h.stoW
  case freshU =>
    simpa only [FreshU, FreshX, OwnZ, phantC_mem, phantC_lbase, phantC_size', phantC_n, pSumAt_phantC] using h.freshU
  case undefLow => exact h.undefLow
  case promAbove =>
    intro j th hj; obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hj; rw [hs]; exact h.promAbove j th0 h0
  case msgWords => exact h.msgWords
  case fgnClos =>
    intro i th t m hi ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp] at ht
    have := h.fgnClos i th0 t m h0 ht; simp only [TgtOK, phantC_lbase, phantC_size', phantC_n] at this ⊢; exact this
  case cellOwn => simpa only [CellOwnerLiveM, phantC_mem, phantC_size', phantC_n] using h.cellOwn
  case ptrGL =>
    intro hk
    obtain ⟨hG, hL, hT, hC⟩ := h.ptrGL hk
    refine ⟨?_, lblSto_phantC hL hfe, ?_, ?_⟩
    · intro j th a cl f hj ha ho hf hp t ht
      obtain ⟨th0, h0, rfl⟩ := phantC_some_iff.1 hj
      rw [tminG_phantC] at ht
      obtain ⟨hM, hR⟩ := hG j th0 a cl f h0 ha ho hf hp t ht
      refine ⟨?_, thRts_appIf hR hfe⟩
      rw [appIf_promises, phantC_mem]; exact hM
    · intro j a cl f ha ho hf hp; rw [tminG_phantC]; exact hT j a cl f ha ho hf hp
    · intro j th a cl f hj ha ho hf hp t ht
      obtain ⟨th0, h0, hpr, -⟩ := ph_get hj
      rw [tminG_phantC] at ht; rw [hpr]; exact hC j th0 a cl f h0 ha ho hf hp t ht
  case granW => intro hk; simpa only [phantC_size', phantC_n, phantC_mem, phantC_pairs] using h.granW hk
  case stoLay => exact h.stoLay
  case boxPlantSep =>
    intro hk l B hB o w hw j th a cl f t hj ha ho hf hp ht hn
    obtain ⟨th0, h0, -⟩ := ph_get hj
    rw [tminG_phantC] at ht
    exact h.boxPlantSep hk l B hB o w hw j th0 a cl f t h0 ha ho hf hp ht hn
  case fgnCnt =>
    intro hk i th t m hi ht hm a0 g hv cm hc hns hco
    obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp] at ht
    have := h.fgnCnt hk i th0 t m h0 ht hm a0 g hv cm hc hns hco
    simpa only [TgtOK, phantC_lbase, phantC_size', phantC_n] using this
  case plantIdx =>
    intro hk j th l cl hj hs ho hpf hK
    obtain ⟨th0, h0, hp, hv, -⟩ := ph_get hj
    obtain ⟨t, mP, ht, rest⟩ := h.plantIdx hk j th0 l cl h0 hs ho hpf hK
    rw [hp, hv]
    exact ⟨t, mP, by rw [tminG_phantC]; exact ht, rest⟩
  case cfgCoh =>
    intro i th hi
    obtain ⟨th0, h0, -, hv, -⟩ := ph_get hi
    rw [hv]
    exact h.cfgCoh i th0 h0
  case pool =>
    obtain ⟨pl, ⟨hT, hU⟩, hO, ⟨M, hM, hb⟩, hK, ⟨rc, hR⟩⟩ := h.pool
    refine ⟨pl, ⟨?_, ?_⟩, ?_, ⟨M, hM, by simpa only [phantC_size', phantC_n, pSumAt_phantC] using hb⟩,
      fun key hk => by simpa only [KeyNet, phantC_size', phantC_n, pSumAt_phantC] using hK key hk,
      ⟨rc, by simpa only [RidOK, phantC_size', phantC_n, pSumAt_phantC] using hR⟩⟩
    · intro j thj t hj hne
      obtain ⟨th0, h0, hp, -, -, hs⟩ := ph_get hj
      simp only [phantC_mem, phantC_pairs, hp, hs]
      exact hT j th0 t h0 hne
    · intro j thj S hj l cl hcl ho hpf hnp
      obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hj
      simp only [phantC_mem, phantC_pairs, hs]
      exact hU j th0 S h0 l cl hcl ho hpf hnp
    · intro i th S hi l cl hcl ho hpf
      obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hi
      simp only [phantC_mem, phantC_pairs, hs]
      exact hO i th0 S h0 l cl hcl ho hpf

set_option maxHeartbeats 400000 in
theorem sysInvW_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {f0 : Frame}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db)
    (h0 : ∀ th, c.ths[0]? = some th →
      ThSys p (gOf p k arch c 0) c.mem c.pairs (app f0 th) Eg (Tot 0) (HP 0) HS (cr 0) (db 0)) :
    SysInvW p k arch Init MintOK (phantC f0 c) Eg Tot HP HS cr db := by
  have hg : ∀ i, gOf p k arch (phantC f0 c) i = gOf p k arch c i := gOf_phantC p k arch f0 c
  constructor
  case thr =>
    intro i th hi
    obtain ⟨th0, hc, rfl⟩ := phantC_some_iff.1 hi
    rw [hg]; unfold appIf; split
    · subst_vars; exact h0 th0 hc
    · exact h.thr i th0 hc
  case held => simpa only [MemHeldG, promAtG_phantC, phantC_mem] using h.held
  case clo => exact h.clo
  case cmg => exact h.cmg
  case shty => exact h.shty
  case proms =>
    intro i th hi t; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp, allProms_phantC]; exact h.proms i th0 h0 t
  case fpok =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hi; rw [hs]; exact h.fpok i th0 S h0
  case fresh =>
    intro i th hi j hj; obtain ⟨th0, h0, hp, -, hn, -⟩ := ph_get hi
    have := h.fresh i th0 h0 j (hn ▸ hj)
    unfold GFreshL at *; rw [hp]; simpa only [phantC_mem, phantC_lbase, phantC_size', phantC_n] using this
  case bal => simpa only [phantC_size', phantC_n, pSumAt_phantC] using h.bal
  case tok => intro n; rw [phantC_size']; exact h.tok n
  case wd => intro n; rw [phantC_size']; exact h.wd n
  case own => intro n; rw [phantC_size']; exact h.own n
  case bf => exact h.bf
  case boxtop => simpa only [BoxTopG, allProms_phantC, phantC_mem] using h.boxtop
  case disj =>
    intro i j thi thj t hij hi hj ht
    obtain ⟨ti, hi0, hpi, -⟩ := ph_get hi; obtain ⟨tj, hj0, hpj, -⟩ := ph_get hj
    rw [hpi] at ht; rw [hpj]; exact h.disj i j ti tj t hij hi0 hj0 ht
  case fpfree =>
    intro i th t hi ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp]; exact h.fpfree i th0 t h0 ht
  case plt =>
    intro i th t hi ht; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp] at ht; exact h.plt i th0 t h0 ht
  case vwr => intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := ph_get hi; rw [hv]; exact h.vwr i th0 h0
  case frle => exact h.frle
  case rle => exact h.rle
  case bnamed => exact h.bnamed
  case freshU =>
    simpa only [FreshU, FreshX, OwnZ, phantC_mem, phantC_lbase, phantC_size', phantC_n, pSumAt_phantC] using h.freshU

/-- `InitOK` at the phantom configuration, given that pushing `f0` keeps thread `0`'s `ThSys`. -/
theorem initOK_phantC {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {f0 : Frame} (h : InitOK p k arch Init MintOK c) (hfe : f0.env = [])
    (hA : ∀ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) th, c.ths[0]? = some th →
      ThSys p (gOf p k arch c 0) c.mem c.pairs th Eg (Tot 0) (HP 0) HS (cr 0) (db 0) →
      ThSys p (gOf p k arch c 0) c.mem c.pairs (app f0 th) Eg (Tot 0) (HP 0) HS (cr 0) (db 0)) :
    InitOK p k arch Init MintOK (phantC f0 c) := by
  obtain ⟨⟨Eg, Tot, HP, HS, cr, db, hw, ⟨rc, hrc⟩, hof, hu, hoc, hbx, hpf, hko, hop, hni, hsw, hlb, hly, hmem, ⟨hmv, hvt⟩, hvl⟩, hnp, hcc⟩ := h
  refine ⟨⟨Eg, Tot, HP, HS, cr, db, sysInvW_phantC hw (fun th h0 => hA _ _ _ _ _ _ th h0 (hw.thr 0 th h0)),
    ⟨rc, by simpa only [RidOK, phantC_size', phantC_n, pSumAt_phantC] using hrc⟩, ?_, hu, ?_, hbx, hpf, ?_, ?_, hni, hsw, lblSto_phantC hlb hfe, hly, hmem,
    ⟨hmv, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro q thq j hq hj; obtain ⟨th0, h0, -, -, hn, -⟩ := ph_get hq
    have := hof q th0 j h0 (hn ▸ hj)
    simpa only [phantC_size', phantC_n, pSumAt_phantC, phantC_lbase] using this
  · intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := ph_get hi; rw [hs]; exact hoc i th0 S h0
  · intro j th l hj; obtain ⟨th0, h0, -⟩ := ph_get hj; exact hko j th0 l h0
  · intro l hl; obtain ⟨a, b⟩ := hop l hl
    refine ⟨a, fun hs => ⟨fun j th hj => ?_, (b hs).2⟩⟩
    obtain ⟨th0, h0, -⟩ := ph_get hj; exact (b hs).1 j th0 h0
  · intro i th hi
    obtain ⟨th0, h0, rfl⟩ := phantC_some_iff.1 hi
    have ht := hvt i th0 h0
    unfold appIf; split
    · refine ⟨ht.1, fun fr hf => ?_, ht.2.2⟩
      simp only [app, List.mem_append, List.mem_singleton] at hf
      rcases hf with hf | rfl
      · exact ht.2.1 fr hf
      · rw [hfe]; intro e he; cases he
    · exact ht
  · intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := ph_get hi; rw [hv]; exact hvl i th0 h0
  · intro i th hi; obtain ⟨th0, h0, hp, -⟩ := ph_get hi; rw [hp]; exact hnp i th0 h0
  · intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := ph_get hi; rw [hv]; exact hcc i th0 h0
end TermSpawnSim

#print axioms TermSpawnSim.phantC_n

import WeakCore.TermMain
/-! # TermSetTh — (E2) `SysInvN` when one thread's code/env changes in place (same views, promises,
allocations, undefs): the ext arms (`current`, `emit`, `exitEv`) and the bind half of `current`'s first use. -/
namespace TermSetTh
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Thread `i` replaced by `th'`, the trace set to `tr`. -/
def setC (c : Cfg) (i : Nat) (th' : TTh) (tr : List Event) : Cfg := { c with ths := c.ths.set! i th', trace := tr }

section
variable {c : Cfg} {i : Nat} {th th' : TTh} {tr : List Event}

@[simp] theorem setC_mem : (setC c i th' tr).mem = c.mem := rfl
@[simp] theorem setC_pairs : (setC c i th' tr).pairs = c.pairs := rfl
@[simp] theorem setC_lbase : (setC c i th' tr).lbase = c.lbase := rfl
@[simp] theorem setC_bf : (setC c i th' tr).boxFence = c.boxFence := rfl
@[simp] theorem setC_size : (setC c i th' tr).ths.size = c.ths.size := by simp [setC]
@[simp] theorem setC_n : (setC c i th' tr).n = c.n := by simp [Cfg.n, setC]

theorem gOf_setC (p : Prog) (k : Promises.Knobs) (arch : Arch) (j : Nat) :
    gOf p k arch (setC c i th' tr) j = gOf p k arch c j := by
  unfold gOf; rw [setC_n]; rfl

theorem setC_get (hth : c.ths[i]? = some th) {j : Nat} {t : TTh} (h : (setC c i th' tr).ths[j]? = some t) :
    (j = i ∧ t = th') ∨ (j ≠ i ∧ c.ths[j]? = some t) := by
  by_cases hji : j = i
  · subst hji
    rw [show (setC c j th' tr).ths = c.ths.set! j th' from rfl, arr_get_set_eq th' hth] at h
    exact .inl ⟨rfl, (Option.some.inj h).symm⟩
  · rw [show (setC c i th' tr).ths = c.ths.set! i th' from rfl, arr_get_set_ne _ _ (Ne.symm hji)] at h
    exact .inr ⟨hji, h⟩

theorem setC_self (hth : c.ths[i]? = some th) : (setC c i th' tr).ths[i]? = some th' :=
  arr_get_set_eq th' hth

theorem setC_other {j : Nat} (h : j ≠ i) : (setC c i th' tr).ths[j]? = c.ths[j]? := arr_get_set_ne _ _ (Ne.symm h)

end

/-- What the replacement keeps. -/
structure Same (th th' : TTh) : Prop where
  p : th'.promises = th.promises
  v : th'.vs = th.vs
  n : th'.nalloc = th.nalloc
  u : th'.undefs = th.undefs

theorem Same.st {th th' : TTh} (h : Same th th') (m : Memory) (ps : List Ts) : stOf m ps th' = stOf m ps th := by
  simp [stOf, h.p, h.v, h.n, h.u]

section
variable {c : Cfg} {i : Nat} {th th' : TTh} {tr : List Event}

theorem sc_get (hth : c.ths[i]? = some th) (hs : Same th th') {j : Nat} {t : TTh}
    (h : (setC c i th' tr).ths[j]? = some t) :
    ∃ t0, c.ths[j]? = some t0 ∧ t.promises = t0.promises ∧ t.vs = t0.vs ∧ t.nalloc = t0.nalloc ∧
      ∀ m ps, stOf m ps t = stOf m ps t0 := by
  rcases setC_get hth h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact ⟨th, hth, hs.p, hs.v, hs.n, hs.st⟩
  · exact ⟨t, h, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem setC_promises (hth : c.ths[i]? = some th) (hp : th'.promises = th.promises) (j : Nat) :
    ((setC c i th' tr).ths[j]?).map (·.promises) = (c.ths[j]?).map (·.promises) := by
  by_cases hji : j = i
  · subst hji; rw [setC_self hth, hth]; simp [hp]
  · rw [setC_other hji]

theorem allProms_setC (hth : c.ths[i]? = some th) (hp : th'.promises = th.promises) :
    allProms (setC c i th' tr) = allProms c := by
  unfold allProms
  show ((setC c i th' tr).ths.toList.map (·.promises)).flatten = (c.ths.toList.map (·.promises)).flatten
  congr 1
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, Array.getElem?_toList]
  exact setC_promises hth hp j

theorem pSumAt_setC (hth : c.ths[i]? = some th) (hs : Same th th') (j : Nat) (f : Ts → Res) :
    pSumAt (setC c i th' tr) j f = pSumAt c j f := by
  unfold pSumAt
  by_cases hji : j = i
  · subst hji; rw [setC_self hth, hth]; dsimp only; rw [setC_mem, setC_pairs, hs.st]
  · rw [setC_other hji]; rfl

theorem promAtG_setC (hth : c.ths[i]? = some th) (hp : th'.promises = th.promises) (Eg : GEnv) (a : Address) :
    PromAtG Eg (setC c i th' tr) a = PromAtG Eg c a := by
  unfold PromAtG; rw [allProms_setC hth hp]; rfl

theorem tminG_setC (hth : c.ths[i]? = some th) (hs : Same th th') (Eg : GEnv) (j : Nat) (a : AllocLabel) :
    TermPtrRts.tminG Eg (setC c i th' tr) j a = TermPtrRts.tminG Eg c j a := by
  unfold TermPtrRts.tminG
  by_cases hji : j = i
  · subst hji; rw [setC_self hth, hth]; dsimp only; rw [setC_mem, setC_pairs, hs.st]
  · rw [setC_other hji]; rfl

end


set_option maxHeartbeats 800000 in
/-- **`SysInvN` across an in-place replacement** of thread `i` by `th'` (same views, promises, allocations,
undefs; any trace), given `th'`'s `ThSys`, labels, rts and box. -/
theorem sysInvN_setC {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th th' : TTh}
    {tr : List Event}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hth : c.ths[i]? = some th) (hS0 : Same th th')
    (hT : ThSys p (gOf p k arch c i) c.mem c.pairs th' Eg (Tot i) (HP i) HS (cr i) (db i))
    (hL : k.storeDepRts = true → TermPtrRts.ThLbl Eg th')
    (hR : k.storeDepRts = true → ∀ t a cl, Eg.sto a = some cl → cl.owner = some i →
      TermPtrRts.ThRts t a th → TermPtrRts.ThRts t a th')
    (hB : TidBox Eg th') :
    SysInvN p k arch Init MintOK (setC c i th' tr) Eg Tot HP HS cr db := by
  have hg : ∀ j, gOf p k arch (setC c i th' tr) j = gOf p k arch c j := gOf_setC p k arch
  constructor
  case tidBox =>
    intro j t hj
    rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
    · exact hB
    · exact h.tidBox j t hj'
  case thr =>
    intro j t hj
    rw [hg]
    rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
    · exact hT
    · exact h.thr j t hj'
  case held => simpa only [MemHeldG, promAtG_setC hth hS0.p, setC_mem] using h.held
  case clo => exact h.clo
  case cmg => exact h.cmg
  case shty => exact h.shty
  case proms =>
    intro i th hi t; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hi; rw [hp, allProms_setC hth hS0.p]; exact h.proms i th0 h0 t
  case fpok =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := sc_get hth hS0 hi; rw [hs]; exact h.fpok i th0 S h0
  case fresh =>
    intro i th hi j hj; obtain ⟨th0, h0, hp, -, hn, -⟩ := sc_get hth hS0 hi
    have := h.fresh i th0 h0 j (hn ▸ hj)
    unfold GFreshL at *; rw [hp]; simpa only [setC_mem, setC_lbase, setC_size, setC_n] using this
  case bal => simpa only [setC_size, setC_n, pSumAt_setC hth hS0] using h.bal
  case knet => intro key hk; simpa only [KeyNet, setC_size, setC_n, pSumAt_setC hth hS0] using h.knet key hk
  case bf => exact h.bf
  case boxtop => simpa only [BoxTopG, allProms_setC hth hS0.p, setC_mem] using h.boxtop
  case disj =>
    intro i j thi thj t hij hi hj ht
    obtain ⟨ti, hi0, hpi, -⟩ := sc_get hth hS0 hi; obtain ⟨tj, hj0, hpj, -⟩ := sc_get hth hS0 hj
    rw [hpi] at ht; rw [hpj]; exact h.disj i j ti tj t hij hi0 hj0 ht
  case fpfree =>
    intro i th t hi ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hi; rw [hp]; exact h.fpfree i th0 t h0 ht
  case plt =>
    intro i th t hi ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hi; rw [hp] at ht; exact h.plt i th0 t h0 ht
  case vwr => intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := sc_get hth hS0 hi; rw [hv]; exact h.vwr i th0 h0
  case frle => exact h.frle
  case rle => exact h.rle
  case zwIni => exact h.zwIni
  case predHold =>
    intro j th S a hj; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp]; exact h.predHold j th0 S a h0
  case bnamed => exact h.bnamed
  case rid => simpa only [RidOK, setC_size, setC_n, pSumAt_setC hth hS0] using h.rid
  case promIni =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp] at ht; exact h.promIni j th0 t m h0 ht
  case promTy =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp] at ht; exact h.promTy j th0 t m h0 ht
  case promNU =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp] at ht; exact h.promNU j th0 t m h0 ht
  case ownF =>
    intro q thq j hq hj; obtain ⟨th0, h0, -, -, hn, -⟩ := sc_get hth hS0 hq
    have := h.ownF q th0 j h0 (hn ▸ hj)
    simpa only [setC_size, setC_n, pSumAt_setC hth hS0, setC_lbase] using this
  case promNoTwo =>
    intro j th t m cl hj ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp] at ht; exact h.promNoTwo j th0 t m cl h0 ht
  case undefAt => exact h.undefAt
  case ownKeyOwn => intro j th l hj; obtain ⟨th0, h0, -⟩ := sc_get hth hS0 hj; exact h.ownKeyOwn j th0 l h0
  case ownPub =>
    intro l hl; obtain ⟨a, b⟩ := h.ownPub l hl
    refine ⟨a, fun hs => ⟨fun j th hj => ?_, (b hs).2⟩⟩
    obtain ⟨th0, h0, -⟩ := sc_get hth hS0 hj; exact (b hs).1 j th0 h0
  case boxPV => exact h.boxPV
  case boxFrOwn =>
    intro l B hB t ht; obtain ⟨th0, h0, -, hv, -⟩ := sc_get hth hS0 ht; rw [hv]; exact h.boxFrOwn l B hB th0 h0
  case boxFrLe => exact h.boxFrLe
  case vwrLt => intro i th hi; obtain ⟨th0, h0, -, hv, -⟩ := sc_get hth hS0 hi; rw [hv]; exact h.vwrLt i th0 h0
  case boxFrLt => exact h.boxFrLt
  case frlt => exact h.frlt
  case payOwn => exact h.payOwn
  case boxSto => exact h.boxSto
  case ownCoh =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := sc_get hth hS0 hi; rw [hs]; exact h.ownCoh i th0 S h0
  case riniCoh =>
    intro i th S hi; obtain ⟨th0, h0, -, -, -, hs⟩ := sc_get hth hS0 hi; rw [hs]; exact h.riniCoh i th0 S h0
  case promInCut =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp] at ht; exact h.promInCut j th0 t m h0 ht
  case promClos =>
    intro j th t m hj ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hj; rw [hp] at ht; exact h.promClos j th0 t m h0 ht
  case stoNI => exact h.stoNI
  case stoW => exact h.stoW
  case freshU =>
    simpa only [FreshU, FreshX, OwnZ, setC_mem, setC_lbase, setC_size, setC_n, pSumAt_setC hth hS0] using h.freshU
  case undefLow => exact h.undefLow
  case promAbove =>
    intro j th hj; obtain ⟨th0, h0, -, -, -, hs⟩ := sc_get hth hS0 hj; rw [hs]; exact h.promAbove j th0 h0
  case msgWords => exact h.msgWords
  case fgnClos =>
    intro i th t m hi ht; obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hi; rw [hp] at ht
    have := h.fgnClos i th0 t m h0 ht; simp only [TgtOK, setC_lbase, setC_size, setC_n] at this ⊢; exact this
  case cellOwn => simpa only [CellOwnerLiveM, setC_mem, setC_size, setC_n] using h.cellOwn
  case ptrGL =>
    intro hk
    obtain ⟨hG, hL0, hT0, hC⟩ := h.ptrGL hk
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j t a cl f hj ha ho hf hp u hu
      rw [tminG_setC hth hS0] at hu
      rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · obtain ⟨hM, hR0⟩ := hG j th a cl f hth ha ho hf hp u hu
        refine ⟨?_, hR hk u a cl ha ho hR0⟩
        rw [hS0.p, setC_mem]; exact hM
      · simpa only [setC_mem] using hG j t a cl f hj' ha ho hf hp u hu
    · intro j t hj
      rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · exact hL hk
      · exact hL0 j t hj'
    · intro j a cl f ha ho hf hp; rw [tminG_setC hth hS0]; exact hT0 j a cl f ha ho hf hp
    · intro j t a cl f hj ha ho hf hp u hu
      obtain ⟨th0, h0, hpr, -⟩ := sc_get hth hS0 hj
      rw [tminG_setC hth hS0] at hu; rw [hpr]; exact hC j th0 a cl f h0 ha ho hf hp u hu
  case granW => intro hk; simpa only [setC_size, setC_n, setC_mem, setC_pairs] using h.granW hk
  case stoLay => exact h.stoLay
  case boxPlantSep =>
    intro hk l B hB o w hw j th a cl f t hj ha ho hf hp ht hn
    obtain ⟨th0, h0, -⟩ := sc_get hth hS0 hj
    rw [tminG_setC hth hS0] at ht
    exact h.boxPlantSep hk l B hB o w hw j th0 a cl f t h0 ha ho hf hp ht hn
  case fgnCnt =>
    intro hk i th t m hi ht hm a0 g hv cm hc hns hco
    obtain ⟨th0, h0, hp, -⟩ := sc_get hth hS0 hi; rw [hp] at ht
    have := h.fgnCnt hk i th0 t m h0 ht hm a0 g hv cm hc hns hco
    simpa only [TgtOK, setC_lbase, setC_size, setC_n] using this
  case plantIdx =>
    intro hk j th l cl hj hs ho hpf hK
    obtain ⟨th0, h0, hp, hv, -⟩ := sc_get hth hS0 hj
    obtain ⟨t, mP, ht, rest⟩ := h.plantIdx hk j th0 l cl h0 hs ho hpf hK
    rw [hp, hv]
    exact ⟨t, mP, by rw [tminG_setC hth hS0]; exact ht, rest⟩
  case cfgCoh =>
    intro i th hi
    obtain ⟨th0, h0, -, hv, -⟩ := sc_get hth hS0 hi
    rw [hv]
    exact h.cfgCoh i th0 h0
  case pool =>
    obtain ⟨pl, ⟨hT, hU⟩, hO, ⟨M, hM, hb⟩, hK, ⟨rc, hR⟩⟩ := h.pool
    refine ⟨pl, ⟨?_, ?_⟩, ?_, ⟨M, hM, by simpa only [setC_size, setC_n, pSumAt_setC hth hS0] using hb⟩,
      fun key hk => by simpa only [KeyNet, setC_size, setC_n, pSumAt_setC hth hS0] using hK key hk,
      ⟨rc, by simpa only [RidOK, setC_size, setC_n, pSumAt_setC hth hS0] using hR⟩⟩
    · intro j thj t hj hne
      obtain ⟨th0, h0, hp, -, -, hs⟩ := sc_get hth hS0 hj
      simp only [setC_mem, setC_pairs, hp, hs]
      exact hT j th0 t h0 hne
    · intro j thj S hj l cl hcl ho hpf hnp
      obtain ⟨th0, h0, -, -, -, hs⟩ := sc_get hth hS0 hj
      simp only [setC_mem, setC_pairs, hs]
      exact hU j th0 S h0 l cl hcl ho hpf hnp
    · intro i th S hi l cl hcl ho hpf
      obtain ⟨th0, h0, -, -, -, hs⟩ := sc_get hth hS0 hi
      simp only [setC_mem, setC_pairs, hs]
      exact hO i th0 S h0 l cl hcl ho hpf

end TermSetTh

#print axioms TermSetTh.sysInvN_setC

/-! (hygiene) axiom reports. -/
#print axioms TermSetTh.gOf_setC
#print axioms TermSetTh.setC_get
#print axioms TermSetTh.setC_self
#print axioms TermSetTh.setC_other
#print axioms TermSetTh.Same.st
#print axioms TermSetTh.sc_get
#print axioms TermSetTh.setC_promises
#print axioms TermSetTh.allProms_setC
#print axioms TermSetTh.pSumAt_setC
#print axioms TermSetTh.promAtG_setC
#print axioms TermSetTh.tminG_setC

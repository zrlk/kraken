import WeakCore.TermBoxT
import WeakCore.TermSetTh
import WeakCore.TermSpawn
import WeakCore.TermSpawnRun
/-! # TermBoxG — (E2) `SysInvN` across the ghost box: thread `i` takes its next label `l` as its
`ThreadId` box (`nalloc + 1`), `E_g` gains the published unit cell `EgB Eg l`. -/
namespace TermBox
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermInterf
open TermSetTh TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The thread after taking its box label. -/
def thB (th : TTh) (tl : Option AllocLabel) : TTh := { th with nalloc := th.nalloc + 1, tidLbl := tl }


section
variable {Eg : GEnv} {l : AllocLabel}
theorem EgB_sto_cases {x : AllocLabel} {cl : Cell} (h : (EgB Eg l).sto x = some cl) :
    (x = l ∧ cl = ⟨.unit, none⟩) ∨ (x ≠ l ∧ Eg.sto x = some cl) := by
  by_cases e : x = l
  · subst e; simp [EgB] at h; exact .inl ⟨rfl, h.symm⟩
  · rw [EgB_sto_ne e] at h; exact .inr ⟨e, h⟩
theorem EgB_pfr_cases {x : AllocLabel} {f : Ts} (h : (EgB Eg l).pfr x = some f) :
    (x = l ∧ f = 0) ∨ (x ≠ l ∧ Eg.pfr x = some f) := by
  by_cases e : x = l
  · subst e; simp [EgB] at h; exact .inl ⟨rfl, h.symm⟩
  · rw [EgB_pfr_ne e] at h; exact .inr ⟨e, h⟩
@[simp] theorem EgB_box : (EgB Eg l).box = Eg.box := rfl
@[simp] theorem EgB_ini : (EgB Eg l).ini = Eg.ini := rfl
@[simp] theorem EgB_rini : (EgB Eg l).rini = Eg.rini := rfl
@[simp] theorem EgB_fpOf : (EgB Eg l).fpOf = Eg.fpOf := rfl
@[simp] theorem EgB_prog : (EgB Eg l).prog = Eg.prog := rfl
end

theorem thB_get {c : Cfg} {i : Nat} {th : TTh} {tl : Option AllocLabel} {tr : List Event} (hth : c.ths[i]? = some th)
    {j : Nat} {t : TTh} (h : (setC c i (thB th tl) tr).ths[j]? = some t) :
    ∃ t0, c.ths[j]? = some t0 ∧ t.promises = t0.promises ∧ t.vs = t0.vs ∧ t.undefs = t0.undefs ∧ t0.nalloc ≤ t.nalloc := by
  rcases setC_get hth h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
  · exact ⟨th, hth, rfl, rfl, rfl, Nat.le_succ _⟩
  · exact ⟨t, h', rfl, rfl, rfl, Nat.le_refl _⟩

theorem allProms_thB {c : Cfg} {i : Nat} {th : TTh} {tl : Option AllocLabel} {tr : List Event} (hth : c.ths[i]? = some th) :
    allProms (setC c i (thB th tl) tr) = allProms c := allProms_setC hth rfl

theorem pSumAt_thB {c : Cfg} {i : Nat} {th : TTh} {tl : Option AllocLabel} {tr : List Event} (hth : c.ths[i]? = some th)
    (j : Nat) (f : Ts → Res) : pSumAt (setC c i (thB th tl) tr) j f = pSumAt c j f := by
  unfold pSumAt
  by_cases hji : j = i
  · subst hji; rw [setC_self hth, hth]; rfl
  · rw [setC_other hji]; rfl


section
variable {Eg : GEnv} {l : AllocLabel}
theorem gfresh_box {c c' : Cfg} {t t0 : TTh} {x : AllocLabel} (hm : c'.mem = c.mem) (hp : t.promises = t0.promises)
    (e : x ≠ l) (h : GFreshL Eg c t0 x) : GFreshL (EgB Eg l) c' t x := by
  obtain ⟨a, b, c1, d, f⟩ := h
  exact ⟨by rw [EgB_sto_ne e]; exact a, b, c1, by rw [EgB_pfr_ne e]; exact d,
    fun u m hu he => by rw [hp]; exact f u m (hm ▸ hu) he⟩
theorem tgtOK_box {c c' : Cfg} {j : Nat} {x : AllocLabel} (hlb : c'.lbase = c.lbase) (hn : c'.n = c.n)
    (h : TgtOK Eg c j x) : TgtOK (EgB Eg l) c' j x := by
  by_cases e : x = l
  · exact .inl ⟨0, by rw [e]; exact EgB_pfr_self⟩
  · unfold TgtOK at h ⊢; rw [EgB_pfr_ne e, EgB_sto_ne e, EgB_box, hlb, hn]; exact h
open Classical in
theorem pubE_box_sto (hs0 : Eg.sto l = none) : ∀ x c, (PubE Eg).sto x = some c → (PubE (EgB Eg l)).sto x = some c := by
  intro x c h
  by_cases e : x = l
  · subst e; simp [PubE, hs0] at h
  · have h' : (if Eg.Shared x then Eg.sto x else none) = some c := h
    show (if (EgB Eg l).Shared x then (EgB Eg l).sto x else none) = some c
    have hsh : (EgB Eg l).Shared x ↔ Eg.Shared x := by simp only [GEnv.Shared, EgB_pfr_ne e]
    by_cases hs : Eg.Shared x
    · rw [if_pos hs] at h'; rw [if_pos (hsh.2 hs), EgB_sto_ne e]; exact h'
    · rw [if_neg hs] at h'; cases h'
theorem pubE_box_pfr (hp0 : Eg.pfr l = none) : ∀ x f, (PubE Eg).pfr x = some f → (PubE (EgB Eg l)).pfr x = some f := by
  intro x f h
  by_cases e : x = l
  · subst e; simp [PubE, hp0] at h
  · simp only [PubE] at h ⊢; rw [EgB_pfr_ne e]; exact h
end

section boxH
variable {E : TEnv} {l : AllocLabel}
theorem vis_boxE {x : AllocLabel} (h : x ≠ l → Vis E x) : Vis (boxE E l) x := by
  by_cases e : x = l
  · subst e; exact Vis_pfr boxE_pfr_self
  · exact (Vis_congr (boxE_sto_ne e) rfl (boxE_pfr_ne e)).2 (h e)
theorem predU_boxE_iff {a : Address} (e : a.label ≠ l) : PredU (boxE E l) a ↔ PredU E a :=
  PredU_congr (boxE_sto_ne e) rfl (boxE_pfr_ne e) rfl rfl
theorem visU_boxE_iff {a : Address} (e : a.label ≠ l) : VisU (boxE E l) a ↔ VisU E a :=
  VisU_congr (boxE_sto_ne e) rfl (boxE_pfr_ne e)
theorem promAt_boxE {a : Address} (e : a.label ≠ l) {s : St} : PromAt (boxE E l) s a = PromAt E s a :=
  PromAt_congr (boxE_sto_ne e) rfl (boxE_pfr_ne e)
theorem fpAt_boxE {a : Address} (e : a.label ≠ l) : FpAt (boxE E l) a = FpAt E a :=
  FpAt_congr (boxE_sto_ne e) rfl (boxE_pfr_ne e)
theorem wordUnit_boxE_iff {a : Address} (e : a.label ≠ l) : WordUnit (boxE E l) a ↔ WordUnit E a :=
  WordUnit_congr (boxE_sto_ne e)
theorem valOfR_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {S : Ty} {ws : List Word} {R : Res}
    (h : ValOfR E S ws R) : ValOfR (boxE E l) S ws R :=
  ValOfR_mono (η₁ := E) (η₂ := boxE E l) rfl rfl (incl_boxE hs hp).sto (fun _ => Nat.le_refl _) h (incl_boxE hs hp).pfr
theorem overT_boxE_iff {x : AllocLabel} (e : x ≠ l) {s : St} {o : Nat} {tw : Ts} :
    TermPlant.OverT (boxE E l) s ⟨x, o⟩ tw ↔ TermPlant.OverT E s ⟨x, o⟩ tw := by
  unfold TermPlant.OverT; rw [promAt_boxE (a := ⟨x, o⟩) e]
theorem winG_boxE_iff {x : AllocLabel} (e : x ≠ l) {s : St} {o : Nat} {tw : Ts} :
    TermOverCr.WinG (boxE E l) s x o tw ↔ TermOverCr.WinG E s x o tw := by
  unfold TermOverCr.WinG; rw [fpAt_boxE (a := ⟨x, 0⟩) e]
theorem crItem_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s : St} {cr : Ts → Res} {x : AllocLabel}
    {c : Cell} {it : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (e : x ≠ l)
    (h : TermPiece.CrItem E s cr x c it) : TermPiece.CrItem (boxE E l) s cr x c it := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  exact ⟨mh, usS, a1, a2, a3, fun hw => a4 ((wordUnit_boxE_iff (by rw [a2]; exact e)).1 hw), a5, a6, a7, a8, a9,
    a10, valOfR_boxE hs hp a11, a12, a13⟩
theorem crItemQ_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s : St} {cr : Ts → Res} {x : AllocLabel}
    {c : Cell} {it : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (e : x ≠ l)
    (h : TermOverCr.CrItemQ E s cr x c it) : TermOverCr.CrItemQ (boxE E l) s cr x c it := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h
  exact ⟨mh, usS, a1, a2, a3, fun hw => a4 ((wordUnit_boxE_iff (by rw [a2]; exact e)).1 hw), a5, a6, a7, a8, a9,
    a10, valOfR_boxE hs hp a11, a12, fun i o w tw' hk hi hw hlo =>
      (a13 i o w tw' hk hi hw hlo).imp id fun ⟨q1, q2⟩ => ⟨(predU_boxE_iff (a := ⟨x, _⟩) e).2 q1, q2⟩⟩
theorem overCrE_boxE (hs : E.sto l = none) (hp : E.pfr l = none) {s : St} {cr : Ts → Res} {x : AllocLabel}
    {c : Cell} (e : x ≠ l) (h : TermOverCr.OverCrE E s cr x c) : TermOverCr.OverCrE (boxE E l) s cr x c := by
  obtain ⟨Gs, ⟨h1, h2, h3, h4, h5⟩, hHL⟩ := h
  refine ⟨Gs, ⟨h1, fun it hit => crItemQ_boxE hs hp e (h2 it hit), fun o tw hc hv hlo hg hov => ?_, h4,
    fun t m ht hm hl hw hnz => h5 t m ht hm hl (fun hw' => hw ((wordUnit_boxE_iff (by rw [hl]; exact e)).2 hw')) hnz⟩,
    hHL⟩
  exact h3 o tw (hc.imp id (predU_boxE_iff (a := ⟨x, o⟩) e).1)
    (fun hv' => hv ((visU_boxE_iff (a := ⟨x, o⟩) e).2 hv')) hlo ((winG_boxE_iff e).1 hg) ((overT_boxE_iff e).1 hov)
end boxH

section boxG
variable {Eg : GEnv} {l : AllocLabel}
open TermPtrRts in
theorem plantEdge_box {m : Msg} {a : AllocLabel} (hm : m.loc.label ≠ l) :
    PlantEdge (EgB Eg l).sto m a ↔ PlantEdge Eg.sto m a := by
  unfold PlantEdge; rw [EgB_sto_ne hm]
open TermPtrRts in
theorem tminOf_box {s : St} {a : AllocLabel} (hm : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label ≠ l) :
    tminOf (EgB Eg l).sto s a = tminOf Eg.sto s a := by
  unfold tminOf
  congr 1
  apply List.filter_congr
  intro t _
  apply Bool.eq_iff_iff.2
  rw [edgeB_iff, edgeB_iff]
  exact ⟨fun ⟨m, h1, h2⟩ => ⟨m, h1, (plantEdge_box (hm t m h1)).1 h2⟩,
    fun ⟨m, h1, h2⟩ => ⟨m, h1, (plantEdge_box (hm t m h1)).2 h2⟩⟩
theorem tminG_box {c : Cfg} {i : Nat} {th : TTh} {tl : Option AllocLabel} {tr : List Event} (hth : c.ths[i]? = some th)
    (hm : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ l) (j : Nat) (a : AllocLabel) :
    TermPtrRts.tminG (EgB Eg l) (setC c i (thB th tl) tr) j a = TermPtrRts.tminG Eg c j a := by
  unfold TermPtrRts.tminG
  by_cases hji : j = i
  · subst hji; rw [setC_self hth, hth]; dsimp only
    rw [tminOf_box hm]; rfl
  · rw [setC_other hji]
    cases c.ths[j]? with
    | none => rfl
    | some t => dsimp only; exact tminOf_box hm
end boxG
theorem pfr_ne_none_box {Eg : GEnv} {l x : AllocLabel} (h : Eg.pfr x ≠ none) : (EgB Eg l).pfr x ≠ none := by
  by_cases e : x = l
  · subst e; rw [EgB_pfr_self]; exact fun h' => by cases h'
  · rw [EgB_pfr_ne e]; exact h

set_option maxHeartbeats 1600000 in
theorem sysInvN_box {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {l : AllocLabel} {tl : Option AllocLabel}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c)
    (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hl : l = freshLabel c.lbase c.n i th.nalloc)
    (htl : tl = th.tidLbl ∨ tl = some l) :
    SysInvN p k arch Init MintOK (setC c i (thB th tl) c.trace) (EgB Eg l) Tot HP HS cr db := by
  have hi : i < c.ths.size := by
    rcases Nat.lt_or_ge i c.ths.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hth; cases hth
  have hsn : c.ths.size ≤ c.n := Nat.le_max_right _ _
  have hin : i < c.n := Nat.lt_of_lt_of_le hi hsn
  have hG := h.fresh i th hth th.nalloc (Nat.le_refl _)
  rw [← hl] at hG
  obtain ⟨hs0, hb0, hi0, hp0, hm0⟩ := hG
  have hri0 : Eg.rini l = 0 := Nat.le_zero.1 (hi0 ▸ h.rle l)
  have hmsg : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ l := fun t m ht he => by
    have := hm0 t m ht he; rw [hnp] at this; cases this
  have hf : BoxFresh Eg c.mem l := ⟨hs0, hb0, hp0, hi0, hri0, hmsg⟩
  have hlab : ∀ j q, j < c.n → freshLabel c.lbase c.n j q = l → j = i ∧ q = th.nalloc := fun j q hj e => by
    rw [hl] at e; exact TermRun.freshLabel_inj hj hin e
  have hz := h.ownF i th th.nalloc hth (Nat.le_refl _)
  rw [← hl] at hz
  have hne : ∀ x cl, Eg.sto x = some cl → x ≠ l := fun x cl hx e => by subst e; rw [hs0] at hx; cases hx
  have hg : ∀ j, gOf p k arch (setC c i (thB th tl) c.trace) j = gOf p k arch c j := gOf_setC p k arch
  have hlts : ∀ j t, c.ths[j]? = some t → j < c.ths.size := fun j t h' => by
    rcases Nat.lt_or_ge j c.ths.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at h'; cases h'
  have hlt : ∀ j t, c.ths[j]? = some t → j < c.n := fun j t h' => Nat.lt_of_lt_of_le (hlts j t h') hsn
  constructor
  case thr =>
    intro j t hj
    rw [hg]
    rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨hji, hj'⟩
    · exact thSys_box hf (h.thr j th hth) (Nat.le_succ _)
        (fun q h1 h2 => by
          have e : q = th.nalloc := by omega
          subst e; exact hl.symm)
        (fun q hq e => by have := (hlab j q hin e).2; omega)
    · exact thSys_box (n' := t.nalloc) (tl := t.tidLbl) hf (h.thr j t hj') (Nat.le_refl _)
        (fun q h1 h2 => absurd h2 (by omega)) (fun q hq e => hji (hlab j q (hlt j t hj') e).1)
  case held =>
    obtain ⟨L, Rl, hnd, hc, hq, hH, he⟩ := h.held
    have hlL : l ∉ L := fun hl' => by obtain ⟨f, hf⟩ := hq l hl'; rw [hp0] at hf; cases hf
    have hneL : ∀ x, x ∈ L → x ≠ l := fun x hx e => hlL (e ▸ hx)
    have hPA : ∀ a : Address, a.label ≠ l →
        PromAtG (EgB Eg l) (setC c i (thB th tl) c.trace) a = PromAtG Eg c a := fun a ne => by
      unfold PromAtG
      rw [allProms_thB hth]
      have h1 : WordUnitG (EgB Eg l) a ↔ WordUnitG Eg a := by unfold WordUnitG; rw [EgB_sto_ne ne]
      have h2 : PredUG (EgB Eg l) a ↔ PredUG Eg a := by unfold PredUG IniWG IniWrG; rw [EgB_sto_ne ne]; rfl
      by_cases hw : WordUnitG Eg a
      · rw [if_pos (h1.2 hw), if_pos hw]
      · rw [if_neg (fun h' => hw (h1.1 h')), if_neg hw]
        by_cases hq' : PredUG Eg a
        · rw [if_pos (h2.2 hq'), if_pos hq']; rfl
        · rw [if_neg (fun h' => hq' (h2.1 h')), if_neg hq']
    have inclP : Incl (PubE Eg) (PubE (EgB Eg l)) :=
      ⟨rfl, pubE_box_sto hs0, fun _ => Nat.le_refl _, pubE_box_pfr hp0, fun _ _ h' => h', fun _ => Nat.le_refl _⟩
    refine ⟨l :: L, fun x => if x = l then .zero else Rl x, List.nodup_cons.2 ⟨hlL, hnd⟩, fun x cl hx hsx => ?_,
      fun x hx => ?_, ?_, fun x hx => ?_⟩
    · by_cases ne : x = l
      · exact ne ▸ List.mem_cons_self
      · have hx' : Eg.Shared x := by obtain ⟨f, hf⟩ := hx; exact ⟨f, by rw [EgB_pfr_ne ne] at hf; exact hf⟩
        rw [EgB_sto_ne ne] at hsx
        exact List.mem_cons_of_mem _ (hc x cl hx' hsx)
    · rcases List.mem_cons.1 hx with e | hx
      · rw [e]; exact ⟨0, EgB_pfr_self⟩
      · obtain ⟨f, hf⟩ := hq x hx; exact ⟨f, by rw [EgB_pfr_ne (hneL x hx)]; exact hf⟩
    · rw [hH]; simp only [List.map_cons, Res.sum_cons, ite_true, Res.zero_add]
      exact congrArg Res.sum (List.map_congr_left fun x hx => by simp only [hneL x hx, ite_false]).symm
    · rcases List.mem_cons.1 hx with e | hx
      · rw [e]; dsimp only; rw [if_pos rfl]
        refine ⟨fun _ => rfl, fun cl hc => ?_⟩
        rw [EgB_sto_self] at hc; cases hc
        exact ⟨[], fun o w hw => by simp at hw, Or.inl ⟨rfl, by unfold ValOfR; simp [VRR, Valid]⟩⟩
      · have ne := hneL x hx
        dsimp only; rw [if_neg ne]
        refine ⟨fun h0 => (he x hx).1 (by rw [EgB_sto_ne ne] at h0; exact h0), fun cl hc => ?_⟩
        rw [EgB_sto_ne ne] at hc
        obtain ⟨vals, hv, hk⟩ := (he x hx).2 cl hc
        exact ⟨vals, fun o w hw => by rw [hPA ⟨x, o⟩ ne]; exact hv o w hw,
          CellOKR_mono (η₁ := PubE Eg) (η₂ := PubE (EgB Eg l)) rfl rfl inclP hk⟩
  case clo =>
    intro x cl hx
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact ⟨rfl, fun _ _ _ _ => rfl⟩
    · exact h.clo x cl hx
  case cmg =>
    intro x cl hx
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · rfl
    · exact h.cmg x cl hx
  case shty =>
    intro x cl hsh hx
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨e, hx⟩
    · rfl
    · refine h.shty x cl ?_ hx
      obtain ⟨f, hf⟩ := hsh; exact ⟨f, by rw [EgB_pfr_ne e] at hf; exact hf⟩
  case proms =>
    intro j t hj u
    rw [allProms_thB hth]
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    rw [hp]; exact h.proms j t0 h0 u
  case fpok =>
    intro j t S hj
    obtain ⟨t0, h0, -⟩ := thB_get hth hj
    have H := h.fpok j t0 S h0
    rw [cut_EgB]
    exact ⟨H.1, fun u m hu hm => vis_boxE fun _ => H.2 u m hu hm⟩
  case fresh =>
    intro j t hj q hq
    rw [setC_n]
    rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨hji, hj'⟩
    · have hq' : th.nalloc + 1 ≤ q := hq
      have e : freshLabel c.lbase c.n j q ≠ l := fun e => by have := (hlab j q hin e).2; omega
      exact gfresh_box rfl rfl e (h.fresh j th hth q (by omega))
    · have e : freshLabel c.lbase c.n j q ≠ l := fun e => hji (hlab j q (hlt j t hj') e).1
      exact gfresh_box rfl rfl e (h.fresh j t hj' q hq)
  case bal =>
    simpa only [setC_size, setC_n, pSumAt_thB hth] using h.bal
  case knet =>
    intro key hk; simpa only [KeyNet, setC_size, setC_n, pSumAt_thB hth] using h.knet key hk
  case bf =>
    exact h.bf
  case boxtop =>
    simpa only [BoxTopG, allProms_thB hth, setC_mem, EgB_box] using h.boxtop
  case disj =>
    intro j1 j2 t1 t2 u hij h1 h2 hu
    obtain ⟨s1, h1', hp1, -⟩ := thB_get hth h1; obtain ⟨s2, h2', hp2, -⟩ := thB_get hth h2
    rw [hp1] at hu; rw [hp2]; exact h.disj j1 j2 s1 s2 u hij h1' h2' hu
  case fpfree =>
    intro j t u hj hu
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    rw [hp]; exact h.fpfree j t0 u h0 hu
  case plt =>
    intro j t u hj hu
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    rw [hp] at hu; exact h.plt j t0 u h0 hu
  case vwr =>
    intro j t hj
    obtain ⟨t0, h0, -, hv, -⟩ := thB_get hth hj
    rw [hv]; exact h.vwr j t0 h0
  case frle =>
    intro x cl f hx hf
    rcases EgB_pfr_cases hf with ⟨rfl, rfl⟩ | ⟨e, hf⟩
    · exact Nat.zero_le _
    · rw [EgB_sto_ne e] at hx; exact h.frle x cl f hx hf
  case rle =>
    exact h.rle
  case zwIni =>
    intro x cl N e us hp hpub hx
    by_cases e1 : x = l
    · exact absurd (.inl e1) hpub
    · rw [EgB_pfr_ne e1] at hp; rw [EgB_sto_ne e1] at hx; exact h.zwIni x cl N e us hp (fun h' => hpub (.inr h')) hx
  case predHold =>
    intro j t S a hj hcl hpub hq
    obtain ⟨cl, hc, ho⟩ := hcl
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    have e : a.label ≠ l := fun e => by rw [e, EgB_sto_self] at hc; cases hc; cases ho
    rw [EgB_sto_ne e] at hc
    rw [cut_EgB, predU_boxE_iff e] at hq
    obtain ⟨hh, h1, h2, h3⟩ := h.predHold j t0 S a h0 ⟨cl, hc, ho⟩ (fun h' => hpub (Or.inr h')) hq
    exact ⟨hh, h1, by rw [hp]; exact h2, fun F hF => h3 F (by rw [EgB_pfr_ne e] at hF; exact hF)⟩
  case bnamed =>
    intro x B hB w hw a g hv
    rcases h.bnamed x B hB w hw a g hv with ⟨cl, hc⟩ | hb
    · exact .inl ⟨cl, by rw [EgB_sto_ne (hne _ cl hc)]; exact hc⟩
    · exact .inr hb
  case rid =>
    simpa only [RidOK, setC_size, setC_n, pSumAt_thB hth] using h.rid
  case promIni =>
    intro j t u m hj hu hm cl hc hsh
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj; rw [hp] at hu
    have em := hmsg u m hm
    rw [EgB_sto_ne em] at hc
    exact h.promIni j t0 u m h0 hu hm cl hc (by obtain ⟨f, hf⟩ := hsh; exact ⟨f, by rwa [EgB_pfr_ne em] at hf⟩)
  case promTy =>
    intro j t u m hj hu hm cl hc hsh
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj; rw [hp] at hu
    have em := hmsg u m hm
    rw [EgB_sto_ne em] at hc
    exact WordOK_mono (η₁ := PubE Eg) (η₂ := PubE (EgB Eg l)) rfl rfl (pubE_box_sto hs0) (fun _ => Nat.le_refl _) (pubE_box_pfr hp0) (fun _ h' => h')
      (h.promTy j t0 u m h0 hu hm cl hc (by obtain ⟨f, hf⟩ := hsh; exact ⟨f, by rwa [EgB_pfr_ne em] at hf⟩))
  case promNU =>
    intro j t u m hj hu
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    rw [hp] at hu; exact h.promNU j t0 u m h0 hu
  case ownF =>
    intro q t j hq hj
    obtain ⟨t0, h0, -, -, -, hle⟩ := thB_get hth hq
    simpa only [setC_size, setC_n, setC_lbase, pSumAt_thB hth] using h.ownF q t0 j h0 (Nat.le_trans hle hj)
  case promNoTwo =>
    intro j t u m cl hj hu hm hc
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    rw [EgB_sto_ne (hmsg u m hm)] at hc; rw [hp] at hu
    exact h.promNoTwo j t0 u m cl h0 hu hm hc
  case undefAt =>
    intro x cl hx o n P hA hgh
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · cases hA
    · exact h.undefAt x cl hx o n P hA hgh
  case ownKeyOwn =>
    intro j t x hj hT
    obtain ⟨t0, h0, -⟩ := thB_get hth hj
    rcases h.ownKeyOwn j t0 x h0 hT with a | ⟨cl, a, b⟩
    · by_cases e : x = l
      · subst e
        have := hz.1 j (hlts j t0 h0); simp only [Res.add_apply] at this; exact absurd (by omega) hT
      · exact .inl (by rw [EgB_sto_ne e]; exact a)
    · exact .inr ⟨cl, by rw [EgB_sto_ne (hne x cl a)]; exact a, b⟩
  case ownPub =>
    intro x hx
    rcases hx with rfl | hx
    · refine ⟨by simp, fun _ => ⟨fun j t hj => ?_, hz.2⟩⟩
      obtain ⟨t0, h0, -⟩ := thB_get hth hj
      have := hz.1 j (hlts j t0 h0); simp only [Res.add_apply] at this ⊢; omega
    · obtain ⟨a, b⟩ := h.ownPub x hx
      by_cases e : x = l
      · subst e; exact absurd hp0 a
      · refine ⟨by rw [EgB_pfr_ne e]; exact a, fun hs => ?_⟩
        obtain ⟨b1, b2⟩ := b (by rwa [EgB_sto_ne e] at hs)
        exact ⟨fun j t hj => by obtain ⟨t0, h0, -⟩ := thB_get hth hj; exact b1 j t0 h0, b2⟩
  case boxPV =>
    exact h.boxPV
  case boxFrOwn =>
    intro x B hB t ht
    obtain ⟨t0, h0, -, hv, -⟩ := thB_get hth ht
    rw [hv]; exact h.boxFrOwn x B hB t0 h0
  case boxFrLe =>
    exact h.boxFrLe
  case vwrLt =>
    intro j t hj
    obtain ⟨t0, h0, -, hv, -⟩ := thB_get hth hj
    rw [hv]; exact h.vwrLt j t0 h0
  case boxFrLt =>
    exact h.boxFrLt
  case frlt =>
    intro x cl f hx hf
    rcases EgB_pfr_cases hf with ⟨rfl, rfl⟩ | ⟨e, hf⟩
    · exact Nat.zero_le _
    · rw [EgB_sto_ne e] at hx; exact h.frlt x cl f hx hf
  case payOwn =>
    intro x B hB w hw a g hv cl hc hpf
    by_cases e : a.label = l
    · rw [e, EgB_pfr_self] at hpf; cases hpf
    · rw [EgB_sto_ne e] at hc; rw [EgB_pfr_ne e] at hpf; exact h.payOwn x B hB w hw a g hv cl hc hpf
  case boxSto =>
    intro x B hB
    have e : x ≠ l := fun e => by rw [e, EgB_box, hb0] at hB; cases hB
    rw [EgB_sto_ne e]; exact h.boxSto x B hB
  case ownCoh =>
    intro j t S hj
    obtain ⟨t0, h0, -, hv, -⟩ := thB_get hth hj
    have H := h.ownCoh j t0 S h0
    intro x cl hx ho hpf o ho'
    rw [Cut_sto] at hx
    by_cases e : x = l
    · subst e; rw [cutSto_EgB_self] at hx; cases hx; exact absurd ho (by simp)
    · rw [cutSto_EgB_ne e] at hx
      have := H x cl hx ho (by simpa [Cut_pfr, EgB_pfr_ne e] using hpf) o ho'
      simpa [stOf, hv] using this
  case riniCoh =>
    intro j t S hj
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    have H := h.riniCoh j t0 S h0
    intro u m cl N e us f hu hm hc ho hpf hle hty hacc hlo hhi
    have em := hmsg u m hm
    rw [Cut_sto, cutSto_EgB_ne em] at hc
    exact H u m cl N e us f (fun h' => hu (by show u ∈ t.promises; rw [hp]; exact h')) hm hc ho
      (by simpa [Cut_pfr, EgB_pfr_ne em] using hpf) hle hty hacc hlo hhi
  case promInCut =>
    intro j t u m hj hu hm cm hc
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
    have e := hmsg u m hm
    rw [EgB_sto_ne e] at hc; rw [hp] at hu
    rcases h.promInCut j t0 u m h0 hu hm cm hc with a | ⟨f, hf⟩
    · exact .inl a
    · exact .inr ⟨f, by rw [EgB_pfr_ne e]; exact hf⟩
  case promClos =>
    intro j t u m hj hu hm a' g hv cl hc ho cm hcm hsh hno hrg
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj; rw [hp] at hu
    by_cases ea : a'.label = l
    · exact ⟨0, by rw [ea]; exact EgB_pfr_self⟩
    · have em := hmsg u m hm
      rw [EgB_sto_ne ea] at hc; rw [EgB_sto_ne em] at hcm
      obtain ⟨f, hf⟩ := h.promClos j t0 u m h0 hu hm a' g hv cl hc ho cm hcm
        (hsh.imp_right fun hs => by obtain ⟨f, hf⟩ := hs; exact ⟨f, by rwa [EgB_pfr_ne em] at hf⟩) hno hrg
      exact ⟨f, by rw [EgB_pfr_ne ea]; exact hf⟩
  case stoNI =>
    intro x cl hx
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · rfl
    · exact h.stoNI x cl hx
  case undefLow =>
    intro x cl hx o hO t1 t2 m1 m2 hlt12 h1 h2 e1 e2
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact absurd (congrArg Address.label e1) (hmsg t1 m1 h1)
    · exact h.undefLow x cl hx o hO t1 t2 m1 m2 hlt12 h1 h2 e1 e2
  case promAbove =>
    intro j t hj
    rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
    · exact h.promAbove j th hth
    · exact h.promAbove j t hj' 
  case msgWords =>
    intro t m cl ht hc
    rw [EgB_sto_ne (hmsg t m ht)] at hc; exact h.msgWords t m cl ht hc
  case fgnClos =>
    intro j t u m hj hu hm a' g hv cm hcm hno hrg
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj; rw [hp] at hu
    rw [EgB_sto_ne (hmsg u m hm)] at hcm
    exact tgtOK_box (c := c) rfl setC_n (h.fgnClos j t0 u m h0 hu hm a' g hv cm hcm hno hrg)
  case cellOwn =>
    unfold CellOwnerLiveM
    simp only [setC_size, setC_mem]
    intro x cl hx hc
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨e, hx⟩
    · exact ⟨fun _ h' => (by cases h'), fun _ => ⟨0, EgB_pfr_self⟩⟩
    · have hc' : (∃ (t : Nat) (m : Msg), c.mem[t]? = some m ∧ m.loc.label = x) ∨ Eg.Shared x :=
        hc.imp_right fun hs => by obtain ⟨f, hf⟩ := hs; exact ⟨f, by rwa [EgB_pfr_ne e] at hf⟩
      obtain ⟨a, b⟩ := h.cellOwn x cl hx hc'
      exact ⟨a, fun ho => by obtain ⟨f, hf⟩ := b ho; exact ⟨f, by rw [EgB_pfr_ne e]; exact hf⟩⟩
  case ptrGL =>
    intro hk
    obtain ⟨P1, P2, P3, P4⟩ := h.ptrGL hk
    have own_ne : ∀ a cl j, (EgB Eg l).sto a = some cl → cl.owner = some j → a ≠ l := fun a cl j hc ho e => by
      rw [e, EgB_sto_self] at hc; cases hc; cases ho
    have hE : ∀ env, TermPtrRts.EnvLbl Eg env → TermPtrRts.EnvLbl (EgB Eg l) env := fun env H x rt ws hx w hw a ha =>
      (H x rt ws hx w hw a ha).imp pfr_ne_none_box id
    refine ⟨fun j t a cl f hj hc ho hpf hkey u hu => ?_, fun j t hj => ?_, fun j a cl f hc ho hpf hkey => ?_,
      fun j t a cl f hj hc ho hpf hkey u hu => ?_⟩
    · have e := own_ne a cl j hc ho
      rw [EgB_sto_ne e] at hc; rw [EgB_pfr_ne e] at hpf
      rw [tminG_box hth hmsg] at hu
      rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · exfalso
        have hu' : TermPtrRts.tminOf Eg.sto (stOf c.mem c.pairs th) a = some u := by
          unfold TermPtrRts.tminG at hu; rw [hth] at hu; exact hu
        have := (TermPtrRts.tminOf_spec hu').1
        exact absurd this (by show u ∉ th.promises; rw [hnp]; exact List.not_mem_nil)
      · obtain ⟨M, R⟩ := P1 j t a cl f hj' hc ho hpf hkey u hu
        exact ⟨fun v m hv hpe hvP => M v m hv ((plantEdge_box (hmsg v m hv)).1 hpe) hvP, R⟩
    · rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · obtain ⟨A, B⟩ := P2 j th hth; exact ⟨hE _ A, fun f hf => hE _ (B f hf)⟩
      · obtain ⟨A, B⟩ := P2 j t hj'; exact ⟨hE _ A, fun f hf => hE _ (B f hf)⟩
    · have e := own_ne a cl j hc ho
      rw [EgB_sto_ne e] at hc; rw [EgB_pfr_ne e] at hpf
      rw [tminG_box hth hmsg]; exact P3 j a cl f hc ho hpf hkey
    · have e := own_ne a cl j hc ho
      rw [EgB_sto_ne e] at hc; rw [EgB_pfr_ne e] at hpf
      rw [tminG_box hth hmsg] at hu
      obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj
      have M := P4 j t0 a cl f h0 hc ho hpf hkey u hu
      intro v m cl' hv hvP hc' hN hq
      rw [EgB_sto_ne (hmsg v m hv)] at hc'
      rw [hp] at hvP
      exact M v m cl' hv hvP hc' hN hq
  case granW =>
    intro hk
    rcases h.granW hk with h0 | ⟨g1, g2, g3, g4⟩
    · exact .inl (by rw [setC_size]; exact h0)
    · refine .inr ⟨g1, g2, fun q hq m0 cl hm hc => ?_, fun v mv cl o hv hc ho hT => ?_⟩
      · rw [EgB_sto_ne (hmsg q m0 hm)] at hc; exact g3 q hq m0 cl hm hc
      · rw [EgB_sto_ne (hmsg v mv hv)] at hc; exact g4 v mv cl o hv hc ho hT
  case stoLay =>
    intro hk x cl hx
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · exact .inl (by simp [accs])
    · exact h.stoLay hk x cl hx
  case boxPlantSep =>
    intro hk x B hB o w hw j t a cl f u hj hc ho hpf hkey hu hN
    have e : a ≠ l := fun e => by rw [e, EgB_sto_self] at hc; cases hc; cases ho
    rw [EgB_sto_ne e] at hc; rw [EgB_pfr_ne e] at hpf
    rw [tminG_box hth hmsg] at hu
    obtain ⟨t0, h0, -⟩ := thB_get hth hj
    exact h.boxPlantSep hk x B hB o w hw j t0 a cl f u h0 hc ho hpf hkey hu hN
  case fgnCnt =>
    intro hk j t u m hj hu hm a' g hv cm hcm hns hco
    obtain ⟨t0, h0, hp, -⟩ := thB_get hth hj; rw [hp] at hu
    rw [EgB_sto_ne (hmsg u m hm)] at hcm
    exact tgtOK_box (c := c) rfl setC_n (h.fgnCnt hk j t0 u m h0 hu hm a' g hv cm hcm hns hco)
  case pool =>
    obtain ⟨pl, ⟨T1, T2⟩, O, ⟨M, hM, hB⟩, K, ⟨rc, R⟩⟩ := h.pool
    have hcs : ∀ j S, (Cut Eg j S).sto l = none := fun j S => cutSto_fresh hf
    refine ⟨pl, ⟨fun j thj t hj hne => ?_, fun j thj S hj x cl hx ho hpf hnpub => ?_⟩, fun j thj S hj x cl hx ho hpf => ?_,
      ⟨M, hM, by simpa only [setC_size, setC_n, pSumAt_thB hth] using hB⟩,
      fun key hk => by simpa only [KeyNet, setC_size, setC_n, pSumAt_thB hth] using K key hk,
      ⟨rc, by simpa only [RidOK, setC_size, setC_n, pSumAt_thB hth] using R⟩⟩
    · rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · have := (T1 j th t hth hne).1; rw [hnp] at this; cases this
      · obtain ⟨a1, a2, m, hm, a3, a4⟩ := T1 j thj t hj' hne
        have e := hmsg t m hm
        refine ⟨a1, a2, m, hm, ?_, fun S => ?_⟩
        · rcases a3 with a3 | a3
          · refine .inl fun S => ?_
            obtain ⟨f, mf, b1, b2, b3, b4⟩ := a3 S
            exact ⟨f, mf, by rw [cut_EgB, fpAt_boxE (a := ⟨m.loc.label, 0⟩) e]; exact b1, b2, b3, b4⟩
          · refine .inr fun S => ?_
            obtain ⟨b0, cl, x, b1, b2, b3, b4, b5⟩ := a3 S
            rw [cut_EgB]
            exact ⟨by rw [boxE_pfr_ne e]; exact b0, cl, x, by rw [boxE_sto_ne e]; exact b1, b2, b3, b4,
              crItem_boxE (hcs j S) hp0 e b5⟩
        · obtain ⟨cl, x, b1, b2, b3, b4, b5⟩ := a4 S
          rw [cut_EgB]
          exact ⟨cl, x, by rw [boxE_sto_ne e]; exact b1, b2, b3, crItem_boxE (hcs j S) hp0 e b4, b5⟩
    · have e : x ≠ l := fun e => by rw [e, cut_EgB, boxE_sto_self] at hx; cases hx; cases ho
      rw [cut_EgB, boxE_sto_ne e] at hx
      rw [EgB_pfr_ne e] at hpf
      rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · refine ⟨[], fun t => Res.zero_le _, fun _ hx => absurd hx List.not_mem_nil, ?_⟩
        intro o tw _ _ hlo
        obtain ⟨hin, -⟩ := hlo
        exact absurd hin (by show tw ∉ th.promises; rw [hnp]; exact List.not_mem_nil)
      · obtain ⟨Gs, g1, g2, g3⟩ := T2 j thj S hj' x cl hx ho hpf (fun h' => hnpub (Or.inr h'))
        rw [cut_EgB]
        refine ⟨Gs, g1, fun it hit => crItemQ_boxE (hcs j S) hp0 e (g2 it hit), fun o tw q1 q2 q3 q4 q5 => ?_⟩
        exact g3 o tw ((predU_boxE_iff (a := ⟨x, o⟩) e).1 q1) (fun h' => q2 ((visU_boxE_iff (a := ⟨x, o⟩) e).2 h'))
          q3 q4 ((overT_boxE_iff e).1 q5)
    · have e : x ≠ l := fun e => by rw [e, cut_EgB, boxE_sto_self] at hx; cases hx; cases ho
      rw [cut_EgB, boxE_sto_ne e] at hx
      rw [EgB_pfr_ne e] at hpf
      rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
      · exact TermPool.overCr_noPromP (by show th.promises = []; exact hnp)
      · rw [cut_EgB]; exact overCrE_boxE (hcs j S) hp0 e (O j thj S hj' x cl hx ho hpf)
  case plantIdx =>
    intro hk j t x cl hj hc ho hpf hkey
    have e : x ≠ l := fun e => by rw [e, EgB_sto_self] at hc; cases hc; cases ho
    rw [EgB_sto_ne e] at hc; rw [EgB_pfr_ne e] at hpf
    obtain ⟨t0, h0, hp, hv, -⟩ := thB_get hth hj
    obtain ⟨u, mP, a1, a2, a3, a4, a5, a6⟩ := h.plantIdx hk j t0 x cl h0 hc ho hpf hkey
    refine ⟨u, mP, by rw [tminG_box hth hmsg]; exact a1, a2, by rw [hp]; exact a3, by rw [hv]; exact a4,
      fun v m h1 h2 h3 => ?_, a6⟩
    rw [hp, hv]; exact a5 v m h1 h2 h3
  case cfgCoh =>
    intro j t hj
    obtain ⟨t0, h0, -, hv, -⟩ := thB_get hth hj
    rw [hv]; exact h.cfgCoh j t0 h0
  case stoW =>
    intro x cl hx
    rcases EgB_sto_cases hx with ⟨rfl, rfl⟩ | ⟨-, hx⟩
    · rfl
    · exact h.stoW x cl hx
  case freshU =>
    intro q j hq hqn
    simp only [setC_size, setC_n, setC_lbase] at hq hqn ⊢
    obtain ⟨⟨a, b, c1, d, f⟩, o⟩ := h.freshU q j hq hqn
    have e : freshLabel c.lbase c.n q j ≠ l := fun e => by have := (hlab q j hqn e).1; omega
    refine ⟨⟨by rw [EgB_sto_ne e]; exact a, b, c1, by rw [EgB_pfr_ne e]; exact d, f⟩, ?_⟩
    simpa only [OwnZ, setC_size, setC_lbase, setC_n, pSumAt_thB hth] using o
  case tidBox =>
    intro j t hj x hx
    have old : ∀ t0, c.ths[j]? = some t0 → t0.tidLbl = some x → (EgB Eg l).sto x = some ⟨.unit, none⟩ ∧ (EgB Eg l).pfr x = some 0 := by
      intro t0 h0 hx0
      obtain ⟨a, b⟩ := h.tidBox j t0 h0 x hx0
      have e := hne x _ a
      exact ⟨by rw [EgB_sto_ne e]; exact a, by rw [EgB_pfr_ne e]; exact b⟩
    rcases setC_get hth hj with ⟨rfl, rfl⟩ | ⟨-, hj'⟩
    · rcases htl with rfl | rfl
      · exact old th hth hx
      · cases hx; exact ⟨EgB_sto_self, EgB_pfr_self⟩
    · exact old t hj' hx

end TermBox

#print axioms TermBox.sysInvN_box

/-! (hygiene) axiom reports. -/
#print axioms TermBox.EgB_sto_cases
#print axioms TermBox.EgB_pfr_cases
#print axioms TermBox.thB_get
#print axioms TermBox.allProms_thB
#print axioms TermBox.pSumAt_thB
#print axioms TermBox.gfresh_box
#print axioms TermBox.tgtOK_box
#print axioms TermBox.pubE_box_sto
#print axioms TermBox.pubE_box_pfr
#print axioms TermBox.vis_boxE
#print axioms TermBox.predU_boxE_iff
#print axioms TermBox.visU_boxE_iff
#print axioms TermBox.promAt_boxE
#print axioms TermBox.fpAt_boxE
#print axioms TermBox.wordUnit_boxE_iff
#print axioms TermBox.valOfR_boxE
#print axioms TermBox.overT_boxE_iff
#print axioms TermBox.winG_boxE_iff
#print axioms TermBox.crItem_boxE
#print axioms TermBox.crItemQ_boxE
#print axioms TermBox.overCrE_boxE
#print axioms TermBox.plantEdge_box
#print axioms TermBox.tminOf_box
#print axioms TermBox.tminG_box
#print axioms TermBox.pfr_ne_none_box

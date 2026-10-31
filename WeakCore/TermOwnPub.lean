import WeakCore.TermOwnNet
import WeakCore.TermOwnKey

/-! # TermOwnPub: the `SysInvN` clauses `ownKeyOwn` and `ownPub` (B2)

* `ownKeyOwn` (`OwnKeyOwnG`): a frame carries `own l` only for a label outside Σ or a cell its thread
  owns.  Thread step: the step inequality at `own l` (credits and debits own-free); the old frame by the
  clause, the old holdings by typing (`TermOwnKey.MemHeldOn_ownL`: a holding's own key names an own cell
  of the thread), a mint only at the stepper's fresh label (`AllocGT`), whose new cell the stepper owns
  (`EFoot`), and which no other thread holds (`OwnFreshZ`).  Promise step: frames unchanged.
* `ownPub` (`OwnPubG`): a published label has a frontier and, in Σ, no own key anywhere.  At the step
  that publishes `l` (`GEnv.post`'s `pubd`): `EFoot` makes `l` an own cell of the stepper not yet seen
  (`SeenLE`), so the step's `SeenOK` zeroes its frame and holdings; the other threads' frames by
  `ownKeyOwn`, their private holdings by typing.  Afterwards: the step inequality (nothing to take from,
  no mint at a Σ label). -/

namespace TermOwnPub
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermBal TermOwnKey
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem EgT_sto_fresh {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {c' : Cfg} {l : AllocLabel}
    (h : FreshIn g n n' l) : (EgT Eg g n n' E' c').sto l = E'.sto l := post_sto_fresh h

theorem EgT_sto_old {Eg : GEnv} {g : G} {n n' : Nat} {E' : TEnv} {c' : Cfg} {l : AllocLabel}
    (h : ¬ FreshIn g n n' l) : (EgT Eg g n n' E' c').sto l = Eg.sto l := post_sto_old h

theorem EgT_pfr (Eg : GEnv) (g : G) (n n' : Nat) (E' : TEnv) (c' : Cfg) (l : AllocLabel) :
    (EgT Eg g n n' E' c').pfr l = E'.pfr l := rfl

theorem EgT_pubd (Eg : GEnv) (g : G) (n n' : Nat) (E' : TEnv) (c' : Cfg) (l : AllocLabel) :
    (EgT Eg g n n' E' c').pubd l = (Eg.pubd l ∨ (Eg.pfr l = none ∧ E'.pfr l ≠ none ∧ E'.seen l)) := rfl

theorem EgP_sto (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (j n : Nat) (l : AllocLabel) :
    (EgP Eg P N j n).sto l = Eg.sto l := rfl

theorem EgP_pubd (Eg : GEnv) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (j n : Nat) (l : AllocLabel) :
    (EgP Eg P N j n).pubd l = Eg.pubd l := rfl

theorem EgP_pfr {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} {l : AllocLabel}
    (h : Eg.pfr l ≠ none) : (EgP Eg P N j n).pfr l ≠ none := by
  show (match P l with | some f => some f | none => Eg.pfr l) ≠ none
  cases P l with
  | some f => exact fun h' => by cases h'
  | none => exact h

theorem ne_zero_of_add {a b : Nat} (h : a + b ≠ 0) : a ≠ 0 ∨ b ≠ 0 := by omega

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- A fresh label of the stepper is outside Σ, has no frontier, and no thread holds its own key. -/
theorem fresh_facts {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) {l : AllocLabel}
    (hf : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) :
    Eg.sto l = none ∧ Eg.pfr l = none ∧ ∀ n, n < c.ths.size → Tot n (.own l) = 0 := by
  obtain ⟨j', hj1, -, rfl⟩ := hf
  have hg := X.inv.fresh i th X.hth j' hj1
  obtain ⟨hz, -⟩ := X.inv.ownF i th j' X.hth hj1
  refine ⟨hg.1, hg.2.2.2.1, fun n hn => ?_⟩
  have := hz n hn
  simp only [Res.add_apply] at this
  show Tot n (.own (freshLabel c.lbase c.n i j')) = 0
  omega

/-- The stepper's step inequality at `own l`. -/
theorem step_own_le {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l)) (l : AllocLabel) :
    Tot' (.own l) + HP' (.own l) + HS' (.own l) ≤ Tot i (.own l) + HP i (.own l) + HS (.own l) + F (.own l) := by
  obtain ⟨S0, -, -, -, -, -, hPK⟩ := X.inv.thr i th X.hth
  have hc0 := (TermOwnFresh.promCrK_own hPK l).1
  have hd0 := (TermOwnFresh.promCrK_own Z.2.2.2.2.2.1 l).2
  have hI := Z.2.2.2.2.2.2.2.1 (.own l)
  have hT := congrFun Y.2.2.2.2.2.2 (.own l)
  simp only [Res.add_apply] at hI hT hc0 hd0
  rw [TermBal.pSum_congr_key (fun t => hK t l)] at hI
  omega

/-- **`ownKeyOwn` across a thread step.** -/
theorem ownKeyOwn_thread (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l))
    (h : OwnKeyOwnG c Eg Tot) :
    OwnKeyOwnG c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') := by
  intro j thj l hj h0
  have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
  have hjs : j < c.ths.size := hsz ▸ lt_of_getq hj
  by_cases hfr : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · rw [EgT_sto_fresh hfr]
    obtain ⟨hs0, -, hz⟩ := fresh_facts X hfr
    by_cases hji : j = i
    · subst hji
      rcases Z.1.2.2.1 l with e | ⟨-, T, e, -⟩
      · left; rw [e, Y.1]; show cutSto Eg j l = none
        cases e' : cutSto Eg j l with
        | none => rfl
        | some c1 => rw [(cutSto_some.1 e').1] at hs0; cases hs0
      · right; refine ⟨_, e, ?_⟩
        show some (CE η).tid = some j
        rw [Y.1]; rfl
    · rw [upd_other _ _ hji] at h0
      exact absurd (hz j hjs) h0
  · rw [EgT_sto_old hfr]
    cases hs : Eg.sto l with
    | none => exact .inl rfl
    | some cl =>
      right
      refine ⟨cl, rfl, ?_⟩
      by_cases hji : j = i
      · subst hji
        rw [upd_self] at h0
        have hle := step_own_le X Y Z hK l
        have hF0 : F (.own l) = 0 := by
          cases e : F (.own l) with
          | zero => rfl
          | succ n => exact absurd (hb1 X Y (Z.toC _ _ _ _ _) l (by rw [e]; exact Nat.succ_ne_zero n)) hfr
        obtain ⟨S0, -, -, -, hHP, hHS, -⟩ := X.inv.thr j th X.hth
        have hpre : Tot j (.own l) + HP j (.own l) + HS (.own l) ≠ 0 := by omega
        rcases ne_zero_of_add hpre with hpre | hHS0
        · rcases ne_zero_of_add hpre with hT0 | hHP0
          · rcases h j th l X.hth hT0 with e | ⟨cl', e, ho⟩
            · rw [hs] at e; cases e
            · rw [hs] at e; cases e; exact ho
          · obtain ⟨cl', e, ho⟩ := OwnL_cut (MemHeldOn_ownL hHP hHP0)
            rw [hs] at e; cases e; exact ho
        · obtain ⟨cl', e, ho⟩ := OwnL_cut (MemHeldOn_ownL hHS hHS0)
          rw [hs] at e; cases e; exact ho
      · rw [upd_other _ _ hji] at h0
        have hj0 : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hj
        rcases h j thj l hj0 h0 with e | ⟨cl', e, ho⟩
        · rw [hs] at e; cases e
        · rw [hs] at e; cases e; exact ho

/-- **`ownPub` across a thread step**, given the step's `SeenOK` (at the split holdings) and the
stepper's `MemInv`. -/
theorem ownPub_thread (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l))
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hSK : SeenOK (CE η) E' Tot' (HP' + HS'))
    (hko : OwnKeyOwnG c Eg Tot) (h : OwnPubG c Eg Tot HP HS) :
    OwnPubG c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot') (upd HP i HP') HS' := by
  intro l hl
  rw [EgT_pubd] at hl
  rw [EgT_pfr]
  have hpfrE : (CE η).pfr = Eg.pfr := by rw [Y.1]; rfl
  have hstoE : (CE η).sto = cutSto Eg i := by rw [Y.1]; rfl
  have hle := step_own_le X Y Z hK l
  have hFfr : F (.own l) ≠ 0 → FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := hb1 X Y (Z.toC _ _ _ _ _) l
  by_cases hold : Eg.pubd l
  · obtain ⟨hp1, hp2⟩ := h l hold
    have hE'p : E'.pfr l = Eg.pfr l := by
      rcases Z.1.2.2.2.2.2.1 l with e | ⟨e, -⟩ | ⟨-, e, -⟩
      · rw [e, hpfrE]
      · rw [hpfrE] at e; exact absurd e hp1
      · rw [hpfrE] at e; exact absurd e hp1
    have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hf =>
      hp1 (fresh_facts X hf).2.1
    refine ⟨by rw [hE'p]; exact hp1, fun hs => ?_⟩
    rw [EgT_sto_old hnf] at hs
    obtain ⟨hz, hzS⟩ := hp2 hs
    have hF0 : F (.own l) = 0 := by
      cases e : F (.own l) with
      | zero => rfl
      | succ n => exact absurd (hFfr (by rw [e]; exact Nat.succ_ne_zero n)) hnf
    have hzi := hz i th X.hth
    simp only [Res.add_apply] at hzi
    refine ⟨fun j thj hj => ?_, by omega⟩
    by_cases hji : j = i
    · subst hji
      rw [upd_self, upd_self, Res.add_apply]
      omega
    · rw [upd_other _ _ hji, upd_other _ _ hji]
      have hj0 : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hj
      exact hz j thj hj0
  · rcases hl with hl | ⟨hpn, hpe, hse⟩
    · exact absurd hl hold
    refine ⟨hpe, fun hs => ?_⟩
    -- `EFoot`: the new frontier is at an own cell of the stepper
    rcases Z.1.2.2.2.2.2.1 l with e | ⟨-, F', -, -, -, hown, -⟩ | ⟨hf, -, e⟩
    · rw [e, hpfrE] at hpe; exact absurd hpn hpe
    · obtain ⟨cc, hcc, hcco⟩ := hown
      rw [hstoE] at hcc
      have hgs : Eg.sto l = some cc := (cutSto_some.1 hcc).1
      have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hf => by
        rw [(fresh_facts X hf).1] at hgs; cases hgs
      have hti : (CE η).tid = i := by rw [Y.1]; rfl
      rw [hti] at hcco
      have hns : ¬ (CE η).seen l := fun hsn => by
        obtain ⟨f, hf, -⟩ := hm.2.2.2.2.1 l hsn
        rw [hpfrE] at hf; rw [hpn] at hf; cases hf
      obtain ⟨hT', hH'⟩ := hSK l hse hns ⟨cc, by rw [hstoE]; exact hcc, by rw [hti]; exact hcco⟩
      simp only [Res.add_apply] at hH'
      refine ⟨fun j thj hj => ?_, by omega⟩
      by_cases hji : j = i
      · subst hji
        rw [upd_self, upd_self, Res.add_apply]
        omega
      · rw [upd_other _ _ hji, upd_other _ _ hji, Res.add_apply]
        have hj0 : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hj
        have hT0 : Tot j (.own l) = 0 := by
          cases e : Tot j (.own l) with
          | zero => rfl
          | succ n =>
            rcases hko j thj l hj0 (by rw [e]; exact Nat.succ_ne_zero n) with e' | ⟨cl', e', ho⟩
            · rw [hgs] at e'; cases e'
            · rw [hgs] at e'; cases e'; rw [hcco] at ho; cases ho; exact absurd rfl hji
        have hP0 : HP j (.own l) = 0 := by
          cases e : HP j (.own l) with
          | zero => rfl
          | succ n =>
            obtain ⟨S0, -, -, -, hHP, -, -⟩ := X.inv.thr j thj hj0
            obtain ⟨cl', e', ho⟩ := OwnL_cut (MemHeldOn_ownL hHP (by rw [e]; exact Nat.succ_ne_zero n))
            rw [hgs] at e'; cases e'; rw [hcco] at ho; cases ho; exact absurd rfl hji
        omega
    · rw [EgT_sto_fresh (g := gOf p k arch c i) (n := th.nalloc) (n' := r.2.2.nalloc) hf] at hs; exact absurd e hs

/-- **`ownKeyOwn` across a promise step**: frames and Σ unchanged. -/
theorem ownKeyOwn_prom {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (h : OwnKeyOwnG c Eg Tot)
    (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (n : Nat) :
    OwnKeyOwnG (promise c j a v w) (EgP Eg P N j n) Tot := by
  intro q thq l hq h0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  obtain ⟨thq0, hq0⟩ : ∃ thq0, c.ths[q]? = some thq0 := by
    by_cases hqj : q = j
    · subst hqj; exact ⟨th, X.hth⟩
    · rw [TermStep.promise_other hqj] at hq; exact ⟨thq, hq⟩
  rw [EgP_sto]
  exact h q thq0 l hq0 h0

/-- **`ownPub` across a promise step**: `pubd`, Σ and frames unchanged; the promiser's holdings at
`own l` do not grow (`PAcct`, credits and debits own-free). -/
theorem ownPub_prom {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (h : OwnPubG c Eg Tot HP HS) (P : AllocLabel → Option Ts) (N : AllocLabel → Nat) (n : Nat) :
    OwnPubG (promise c j a v w) (EgP Eg P N j n) Tot (upd HP j HP') HS' := by
  intro l hl
  rw [EgP_pubd] at hl
  obtain ⟨hp1, hp2⟩ := h l hl
  refine ⟨EgP_pfr hp1, fun hs => ?_⟩
  rw [EgP_sto] at hs
  obtain ⟨hz, hzS⟩ := hp2 hs
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  obtain ⟨S0, -, -, -, -, -, hK⟩ := X.inv.thr j th X.hth
  have hc0 := (TermOwnFresh.promCrK_own hK l).1
  have hA' := congrFun hA (.own l)
  have hd := hdb l
  have hzj := hz j th X.hth
  unfold PAcct at hA
  simp only [Res.add_apply] at hA' hzj hc0
  refine ⟨fun q thq hq => ?_, by omega⟩
  by_cases hqj : q = j
  · subst hqj
    rw [upd_self, Res.add_apply]
    omega
  · rw [upd_other _ _ hqj]
    rw [TermStep.promise_other hqj] at hq
    exact hz q thq hq

end

end TermOwnPub

#print axioms TermOwnPub.ownKeyOwn_thread
#print axioms TermOwnPub.ownPub_thread
#print axioms TermOwnPub.ownKeyOwn_prom
#print axioms TermOwnPub.ownPub_prom

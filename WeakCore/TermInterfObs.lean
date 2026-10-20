import WeakCore.TermMain
/-!
# TermInterfObs — observer variants of the idle-reader clauses (R1)

`cl7_pubDefP`, `cl9d_pubPair`, `cl9e_pubLive` (and the promise-step `pcl…`) with the idle thread `j`
replaced by an **observer**: a non-thread index `j` with no promises, whose clause is carried as a
hypothesis at `Cut Eg j Sj` (no `c.ths[j]?`, no `ThSysAt`).  Proof text copied from `TermInterf`.
-/
namespace TermInterfObs
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain TermInterf
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- An observer clause across a thread step: `Qa` of observer `j` before gives `Qb` after. -/
def ObsClT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Qa Qb : TEnv → Memory → List Ts → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j (Sj : AllocLabel → Prop), j ≠ i → Qa (Cut Eg j Sj) c.mem c.pairs →
      Qb (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) c'.mem c'.pairs

/-- `ObsClT` with the stepper's `ThSysAt` at its cut and its frontier change only at its publish
(certWin-D). -/
def ObsClTH (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Qa Qb : TEnv → Memory → List Ts → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ j (Sj : AllocLabel → Prop), j ≠ i → Qa (Cut Eg j Sj) c.mem c.pairs →
      Qb (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) c'.mem c'.pairs

/-- `ObsClT` with the stepper's frontier change only at its publish (`PfrG` at `pf := PubAt th`). -/
def ObsClTP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Qa Qb : TEnv → Memory → List Ts → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ j (Sj : AllocLabel → Prop), j ≠ i → Qa (Cut Eg j Sj) c.mem c.pairs →
      Qb (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) c'.mem c'.pairs

theorem cl7_pubDefP_obs (hpf : PlantFrozenF p k arch Sp Init MintOK c0) (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (hfr' : PubFrontierF p k arch Sp Init MintOK c0) (hpa : PromTyAPostF p k arch Sp Init MintOK c0) :
    ObsClTP p k arch Sp Init MintOK c0 (fun E mem _ => PubDefP E mem []) (fun E mem _ => PubDefP E mem []) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS j Sj hji hold l cl f hc ho hf o hio
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hgf := gfoot_of X Y ZC
  have hfrE := X.inv.gfresh X.hth r.2.2.nalloc
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hs2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hc
  have hf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
  obtain ⟨hs', hf', hT⟩ := tctx_shared X Y ZC hs2 hf2
  have hIS := tctx_inclS X Y ZC j Sj
  have htid : E'.tid = i := by rw [← tctx_cut X Y ZC]; rfl
  cases ep : Eg.pfr l with
  | some f0 =>
    have hff : f0 = f := Option.some.inj ((hgf.le.pfr l f0 ep).symm.trans hf2)
    subst hff
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
      rw [(hfrE l hF).2.2] at ep; cases ep
    have hc1 : Eg.sto l = some cl := by rw [← hgf.sto_old hnF]; exact hs2
    have hc0 : cutSto Eg j l = some cl := cutSto_shared hc1 ⟨f0, ep⟩
    have hini : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l :=
      gfoot_ini_shared hgf hfrE (hpf X Y ZC) ⟨f0, ep⟩
    have hio0 : InitR (Cut Eg j Sj) cl l o := fun N e us hT' hu => by
      have := hio N e us hT' hu; rw [Cut_ini, hini] at this; exact this
    have hH := hold l cl f0 hc0 ho ep o hio0
    refine HiddenP_move (tctx_pre X) (fun t m h1 h2 h3 => ?_)
      (fun w h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini) hH
    by_cases hoi : cl.owner = some i
    · have hio' : InitR E' cl l o := fun N e us hT' hu => by
        have := hio N e us hT' hu; rw [Cut_ini] at this; exact this
      exact WordOK_transferS hIS hT (tctx_newOwn hsc X Y ZC hc1 hoi hio' h1 h2 h3)
    · exact tctx_newOK_other X Y ZC j Sj hc1 hoi ep hio h1 h2 h3
  | none =>
    -- a cell newly shared by the step: the stepper's own, hidden by its `OwnHidP`
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
      intro hF
      have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
        rw [← Y.1]; exact ZC.1
      rcases hF0.2.2.2.2.2.1 l with e | ⟨-, -, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hs0⟩
      · rw [e] at hf'; exact absurd (hf'.symm.trans ep) (by simp)
      · have h2 : Eg.sto l = some c1 := cutSto_sub hc1
        rw [(hfrE l hF).1] at h2; cases h2
      · rw [hs0] at hs'; cases hs'
    have hc1 : Eg.sto l = some cl := by rw [← hgf.sto_old hnF]; exact hs2
    have hoi : cl.owner = some i := by
      rcases hgf.2.2.2.2.1 l with e | ⟨-, -, -, -, c1, hc1', ho1⟩ | ⟨hF, -⟩
      · have h3 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').pfr l = some f := hf2
        rw [e, ep] at h3; cases h3
      · rw [hc1] at hc1'; cases hc1'; exact ho1
      · exact absurd hF hnF
    have hown : cl.owner = some E'.tid := by rw [htid]; exact hoi
    have hPi : ∀ (t : Ts) (m : Msg), t ∈ r.2.2.promises → r.1[t]? = some m → m.loc = ⟨l, o⟩ →
        WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m) := by
      intro t m ht hm hl
      have hl' : m.loc.label = l := by rw [hl]
      have := hpa X Y Z hPub hPfrP hS i r.2.2 t m X.e3 ht (by rw [X.e1]; exact hm) cl (by rw [hl']; exact hs2)
        ⟨f, by rw [hl']; exact hf2⟩
      rw [hl] at this
      exact WordOK_transferS (InclS_pub_cut _ j Sj) hT this
    have hmono : ∀ w, WordOK E' cl.ty o w →
        WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o w :=
      fun w h => WordOK_transferS hIS hT h
    have hio' : InitR E' cl l o := fun N e us hT' hu => by
      have := hio N e us hT' hu; rw [Cut_ini] at this; exact this
    rw [X.e1]
    by_cases hrc : E'.rc l < E'.ini l
    · obtain ⟨f1, hf1, -, hH⟩ := ZC.2.2.1.2.2.2.2.2.1.2 l cl hs' hown hrc
      rw [hf'] at hf1; cases hf1
      exact HiddenP_conv hPi hmono (hH o hio')
    · have hrr : InitRr E' cl l o := fun N e us hT' hu => by
        have := hio' N e us hT' hu
        unfold TEnv.rc
        have : E'.ini l ≤ E'.rini l := by unfold TEnv.rc at hrc; omega
        rw [Nat.min_eq_left this]; assumption
      have hH := ZC.2.2.1.2.2.2.2.2.1.1 l cl hs' hown o hrr
      have hle : r.2.2.vs.vWr ≤ f := hfr' X Y ZC l f cl (by rw [Y.1]; exact ep) hf' hs'
      exact HiddenP_conv hPi hmono (HiddenP_bound hle hH)

theorem cl9e_pubLive_obs : ObsClT p k arch Sp Init MintOK c0 (fun _ _ _ => True) (fun E mem _ => PubLive E mem) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j Sj hji _ l cl f b S1 us o hc ho hf hs hu hlt
  obtain ⟨hs', hf', -⟩ := tctx_shared X Y Z (cutSto_sub hc) hf
  have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
  by_cases hoi : cl.owner = some i
  · obtain ⟨vals, hcv, hl, -⟩ := Z.2.2.1.2.1 l cl hs' (by rw [htid]; exact hoi)
    have hcov := seg_cover hcv hs hu hlt
    obtain ⟨⟨m, hm, hma, -⟩, -, -⟩ := hl (b + o) _ (List.getElem?_eq_getElem hcov)
    exact ⟨_, m, by rw [X.e1]; exact hm, hma⟩
  · obtain ⟨t, m, hm, hma⟩ := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.2 l cl f b S1 us o hs' (by rw [htid]; exact hoi) hf' hs hu hlt
    exact ⟨t, m, by rw [X.e1]; exact hm, hma⟩

theorem pairStepper_obs (hnp : NewPairF p k arch Sp Init MintOK c0) (hco : OwnCohLeF p k arch Sp Init MintOK c0)
    (hpf : PlantFrozenF p k arch Sp Init MintOK c0) (hnt : PromNoTwoPostF p k arch Sp Init MintOK c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ j (Sj : AllocLabel → Prop), j ≠ i → PubPair (Cut Eg j Sj) c.mem c.pairs [] →
      ∀ l cl f o, cl.owner = some i →
        (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl →
        (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f →
        TwoAtT cl.ty o →
        (∃ b S us o', SegOf cl.ty b S ∧ accs S = some us ∧ TwoAt us o' ∧ o = b + o' ∧
          IniSegN ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l) cl b) →
        ∀ (t0 t1 : Nat) (m0 m1 : Msg), t0 ∉ ([] : List Ts) → t1 ∉ ([] : List Ts) →
        c'.mem[t0]? = some m0 → c'.mem[t1]? = some m1 → m0.loc = ⟨l, o⟩ → m1.loc = ⟨l, o + 1⟩ →
        WeakMem.hiddenFrom c'.mem ⟨l, o⟩ t0 f = false → WeakMem.hiddenFrom c'.mem ⟨l, o + 1⟩ t1 f = false →
        WeakMem.pairStraddles c'.mem c'.pairs ⟨l, o⟩ t0 t1 = false →
        PairOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m0) (mw m1) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr j Sj hji hold
    l cl f o hoi hc hf hTw hgd t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hh0 hh1 hps
  have hgf := gfoot_of X Y Z
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hs2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hc
  have hf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
  obtain ⟨hs', hf', hT⟩ := tctx_shared X Y Z hs2 hf2
  have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
  have hfrE := X.inv.gfresh X.hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
    intro hF
    have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
      rw [← Y.1]; exact Z.1
    rcases hF0.2.2.2.2.2.1 l with e | ⟨-, -, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hs0⟩
    · have h4 : Eg.pfr l = none := (hfrE l hF).2.2
      rw [e] at hf'; exact absurd (hf'.symm.trans h4) (by simp)
    · have h2 : Eg.sto l = some c1 := cutSto_sub hc1
      rw [(hfrE l hF).1] at h2; cases h2
    · rw [hs0] at hs'; cases hs'
  have hc1 : Eg.sto l = some cl := by rw [← hgf.sto_old hnF]; exact hs2
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have honce : ∀ (u1 u2 : Nat) (n1 n2 : Msg), c.mem.size ≤ u1 → c.mem.size ≤ u2 → c'.mem[u1]? = some n1 →
      c'.mem[u2]? = some n2 → n1.loc = n2.loc → n1.loc.label = l → u1 = u2 := fun u1 u2 n1 n2 a1 a2 a3 a4 a5 a6 =>
    tstep_once hm0.2.2.1 X.hr u1 u2 n1 n2 a1 a2 (by rw [← X.e1]; exact a3) (by rw [← X.e1]; exact a4) a5
      (by rw [a6]; exact hnF)
  have hnP : ∀ t m, c'.mem[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) → t ∉ r.2.2.promises :=
    fun t m hm hl ht => by
      have hl' : m.loc.label = l := by rcases hl with e | e <;> rw [e]
      have := hnt X Y Z hS hPfr i r.2.2 t m X.e3 ht hm cl (by rw [hl']; exact hs2) ⟨f, by rw [hl']; exact hf2⟩ o hTw
      rcases hl with e | e
      · exact this.1 (by rw [e])
      · exact this.2 (by rw [e])
  have hIS := tctx_inclS X Y Z j Sj
  -- the pair written by the step at `(t0, t0+1)`, typed by the stepper's MemOKP
  have hnewpair : ∀ m1' : Msg, t0 ∈ c'.pairs → c'.mem[t0 + 1]? = some m1' →
      PairOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m0) (mw m1') := by
    intro m1' hq hm1'
    have hq' : t0 ∈ r.2.1 := by rw [← X.e2]; exact hq
    have hpo := Z.2.2.1.1.2.1 t0 m0 m1' cl hq' (by rw [← X.e1]; exact h0) (by rw [← X.e1]; exact hm1')
      (by rw [hl0]; exact hs')
    rw [hl0] at hpo
    exact PairOK_transferS hIS hT hpo
  cases ep : Eg.pfr l with
  | some f0 =>
    have hff : f0 = f := Option.some.inj ((hgf.le.pfr l f0 ep).symm.trans hf2)
    subst hff
    have hc0 : cutSto Eg j l = some cl := cutSto_shared hc1 ⟨f0, ep⟩
    have hpre : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → c'.mem[t]? = some m :=
      fun t m h => by rw [tctx_pre X t (lt_of_get h)]; exact h
    have hpairs : ∀ q, q ∈ c.pairs → q + 1 < c.mem.size := hm0.1.2.2
    have hpup : PairsUp c.pairs c'.pairs := by rw [X.e2]; exact tstep_pairsUp X.hr
    rcases Nat.lt_or_ge t0 c.mem.size with a0 | a0 <;> rcases Nat.lt_or_ge t1 c.mem.size with a1 | a1
    · have h0o : c.mem[t0]? = some m0 := by rw [← tctx_pre X t0 a0]; exact h0
      have h1o : c.mem[t1]? = some m1 := by rw [← tctx_pre X t1 a1]; exact h1
      exact PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h)
        (hold l cl f0 o hc0
          (.inl ⟨by rw [hoi]; intro e; exact hji (Option.some.inj e).symm, hgd.imp fun b ⟨S1, us, o', h2, h3, h4, h5, h7⟩ =>
            ⟨S1, us, o', h2, h3, h4, h5, by
              have hini : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l :=
                gfoot_ini_shared hgf hfrE (hpf X Y Z) ⟨f0, ep⟩
              have h7' : IniSegN ((EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l) cl b := h7
              rw [hini] at h7'; exact h7'⟩⟩)
          ep hTw t0 t1 m0 m1 hs0 hs1 h0o h1o hl0 hl1 (hiddenFrom_grow hpre hh0) (hiddenFrom_grow hpre hh1)
          (pairStraddles_back (tctx_pre X) hpup hpairs hps)) hI.box hI.rini
    · obtain ⟨q, rfl, hq, hqp, m0', hm0', hl0'⟩ := (hnp X Y Z t1 m1 l o cl a1 h1 hc1 hTw).2 hl1
      exact absurd (straddle_true hqp hm0' hl0' h1 (by rw [hl1]; rfl)
        (fun e => absurd (e.mpr (Nat.le_refl _)) (Nat.not_le.2 (Nat.lt_of_lt_of_le a0 hq)))) (by rw [hps]; simp)
    · obtain ⟨hqp, m1', hm1', hl1'⟩ := (hnp X Y Z t0 m0 l o cl a0 h0 hc1 hTw).1 hl0
      exact absurd (straddle_true hqp h0 hl0 hm1' (by rw [hl1']; rfl)
        (fun e => absurd (e.mp (Nat.le_refl _))
          (Nat.not_le.2 (Nat.lt_of_lt_of_le a1 (Nat.le_trans a0 (Nat.le_succ _)))))) (by rw [hps]; simp)
    · obtain ⟨hqp, m1', hm1', hl1'⟩ := (hnp X Y Z t0 m0 l o cl a0 h0 hc1 hTw).1 hl0
      have e1 : t1 = t0 + 1 := honce t1 (t0 + 1) m1 m1' a1 (Nat.le_succ_of_le a0) h1 hm1' (by rw [hl1, hl1'])
        (by rw [hl1])
      subst e1
      have hme : m1' = m1 := by rw [hm1'] at h1; cases h1; rfl
      subst hme
      exact hnewpair m1' hqp hm1'
  | none =>
    -- newly shared by the step: the stepper's own frontier-cell invariant at `E'`
    have hown : cl.owner = some E'.tid := by rw [htid]; exact hoi
    have hp0 : (CE η).pfr l = none := by rw [Y.1]; exact ep
    have hfne : E'.pfr l ≠ none := by rw [hf']; simp
    have hvf : r.2.2.vs.vWr ≤ f := pubFrontier_holds X Y Z l f cl hp0 hf' hs'
    obtain ⟨vals, hcv, hlat, hopf⟩ := Z.2.2.1.2.1 l cl hs' hown
    have hmem : ∀ t : Nat, c'.mem[t]? = r.1[t]? := fun t => by rw [X.e1]
    -- coherence is below both messages, else they are hidden below the frontier
    have hcohle : ∀ (t : Nat) (m : Msg) (o2 : Nat), c'.mem[t]? = some m → m.loc = ⟨l, o2⟩ →
        WeakMem.hiddenFrom c'.mem ⟨l, o2⟩ t f = false → o2 < vals.length → r.2.2.vs.coh ⟨l, o2⟩ ≤ t := by
      intro t m o2 hm hl hh hlt
      obtain ⟨⟨mc, hmc, hmcl, -⟩, -, -⟩ := hlat o2 _ (List.getElem?_eq_getElem hlt)
      refine Nat.le_of_not_lt fun hlt2 => ?_
      have := hiddenFrom_true (mem := c'.mem) hlt2 (Nat.le_trans (hco X Y Z l hp0 hfne cl vals hs' hcv o2 hlt) hvf)
        (by rw [hmem]; exact hmc) hmcl
      rw [hh] at this; cases this
    obtain ⟨b, S1, us, o', hseg, hus, hTw', rfl, hgini⟩ := hgd
    have hcov1 := seg_cover hcv hseg hus (o := o' + 1) (by have := TwoAt_lt hTw'; omega)
    have hcov0 := seg_cover hcv hseg hus (o := o') (by have := TwoAt_lt hTw'; omega)
    by_cases hrs : IniSegN (E'.rc l) cl b
    · have hrr : InitRr E' cl l (b + o') := by
        intro N e us2 hT2 hu2
        obtain ⟨us3, j3, hu3, hj3, hb3⟩ := hrs N e hT2
        have e3 : us3 = us2 := Option.some.inj (hu3.symm.trans hu2)
        have hS : us = us2 := by
          rcases hseg with ⟨-, rfl, hA⟩ | ⟨N', us', j', hT', hus', -, -⟩
          · rw [hT2] at hA; simp [accs] at hA
          · rw [hT2] at hT'; simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
            obtain ⟨-, rfl⟩ := hT'
            exact Option.some.inj (hus.symm.trans hu2)
        rw [e3, ← hS] at hb3
        rw [← hS]
        have := TwoAt_lt hTw'
        have hm := Nat.mul_le_mul_right (nWords us) (show j3 + 1 ≤ E'.rc l by omega)
        rw [Nat.succ_mul] at hm; omega
      have hpf' : E'.pfr l ≠ none := hfne
      rcases hopf hpf' (b + o') ⟨b, S1, us, o', hseg, hus, hTw', rfl⟩ hrr t0 t1 m0 m1
          (hnP t0 m0 h0 (.inl hl0)) (hnP t1 m1 h1 (.inr hl1)) (by show r.1[t0]? = some m0; rw [← hmem]; exact h0)
          (by show r.1[t1]? = some m1; rw [← hmem]; exact h1)
          hl0 hl1 (hcohle t0 m0 (b + o') h0 hl0 hh0 (by omega))
          (hcohle t1 m1 (b + o' + 1) h1 hl1 hh1 (by omega)) (by rw [← X.e1, ← X.e2]; exact hps) with
        ⟨-, -, hv0, hv1⟩ | hpo
      · exact PairOK_transferS hIS hT (cellOK_pairOK hcv hseg hus hTw' hrs hv0 hv1)
      · exact PairOK_transferS hIS hT hpo
    · have hini : IniSegN (E'.ini l) cl b := hgini
      have hrc : E'.rc l < E'.ini l := Nat.lt_of_not_le fun hle => hrs (hini.mono hle)
      have hpo := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl f (b + o') hs'
        (.inr ⟨hrc, b, S1, us, o', hseg, hus, hTw', rfl, hrs, hini⟩) hf' ⟨b, S1, us, o', hseg, hus, hTw', rfl⟩
        t0 t1 m0 m1 (hnP t0 m0 h0 (.inl hl0)) (hnP t1 m1 h1 (.inr hl1)) (by show r.1[t0]? = some m0; rw [← hmem]; exact h0)
        (by show r.1[t1]? = some m1; rw [← hmem]; exact h1) hl0 hl1 (by rw [← X.e1]; exact hh0) (by rw [← X.e1]; exact hh1)
        (by rw [← X.e1, ← X.e2]; exact hps)
      exact PairOK_transferS hIS hT hpo


theorem cl9d_pubPair_obs (hnp : NewPairF p k arch Sp Init MintOK c0) (hco : OwnCohLeF p k arch Sp Init MintOK c0)
    (hpf : PlantFrozenF p k arch Sp Init MintOK c0) (hnt : PromNoTwoPostF p k arch Sp Init MintOK c0) :
    ObsClTH p k arch Sp Init MintOK c0 (fun E mem pairs => PubPair E mem pairs []) (fun E mem pairs => PubPair E mem pairs []) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr j Sj hji hold
    l cl f o hc hg hf hTw t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hh0 hh1 hps
  have hgd : ∃ b S us o', SegOf cl.ty b S ∧ accs S = some us ∧ TwoAt us o' ∧ o = b + o' ∧
      IniSegN ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l) cl b := by
    rcases hg with ⟨-, b, S1, us, o', h2, h3, h4, h5, h7⟩ | ⟨-, b, S1, us, o', h2, h3, h4, h5, -, h7⟩
    · exact ⟨b, S1, us, o', h2, h3, h4, h5, h7⟩
    · exact ⟨b, S1, us, o', h2, h3, h4, h5, h7⟩
  by_cases hoi : cl.owner = some i
  · exact pairStepper_obs hnp hco hpf hnt X Y Z hS hPfr j Sj hji hold l cl f o hoi hc hf hTw hgd t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hh0 hh1 hps
  · have hs2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hc
    have hf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
    obtain ⟨hs', hf', hT⟩ := tctx_shared X Y Z hs2 hf2
    have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
    have hj' : c'.ths[i]? = some r.2.2 := X.e3
    have hnp : ∀ t m, c'.mem[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) → t ∉ r.2.2.promises :=
      fun t m hm hl ht => by
        have hl' : m.loc.label = l := by rcases hl with e | e <;> rw [e]
        have := hnt X Y Z hS hPfr i r.2.2 t m hj' ht hm cl (by rw [hl']; exact hs2) ⟨f, by rw [hl']; exact hf2⟩ o hTw
        rcases hl with e | e
        · exact this.1 (by rw [e])
        · exact this.2 (by rw [e])
    obtain ⟨b, S1, us, o', h2, h3, h4, h5, h7⟩ := hgd
    have hpp := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl f o hs'
      (.inl ⟨by rw [htid]; exact hoi, b, S1, us, o', h2, h3, h4, h5, h7⟩) hf' hTw t0 t1 m0 m1
      (hnp t0 m0 h0 (.inl hl0)) (hnp t1 m1 h1 (.inr hl1)) (by rw [← X.e1]; exact h0) (by rw [← X.e1]; exact h1)
      hl0 hl1 (by rw [← X.e1]; exact hh0) (by rw [← X.e1]; exact hh1) (by rw [← X.e1, ← X.e2]; exact hps)
    exact PairOK_transferS (tctx_inclS X Y Z j Sj) hT hpp

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- An observer clause across a promise step. -/
def ObsClP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat)
    (Qa Qb : TEnv → Memory → List Ts → Prop) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' (Sj : AllocLabel → Prop), j' ≠ j → Qa (Cut Eg j' Sj) c.mem c.pairs →
      Qb (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (c.mem.push ⟨a, v, w⟩) c.pairs

theorem pcl7_pubDefP_obs (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN) (hph : PlantHidF p k arch Sp Init MintOK c0 plantOf plantN) :
    ObsClP p k arch Sp Init MintOK c0 plantOf plantN (fun E mem _ => PubDefP E mem []) (fun E mem _ => PubDefP E mem []) := by
  intro c Eg Tot HP HS cr db j th a v w X j' Sj hjj hold l cl f hc ho hf o hio
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    have hH := hold l cl' f e ho hf0 o (InitR_ini (cutP_ini hn) hio)
    refine HiddenP_move push_pre (fun t m h1 h2 h3' => ?_)
      (fun w h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini) hH
    rcases push_get h2 with ⟨h4, -⟩ | ⟨-, rfl⟩
    · exact absurd h4 (Nat.not_lt.2 h1)
    · have e' : a = ⟨l, o⟩ := h3'
      subst e'
      exact pctx_newOK hspec hpl hpa X hjj Sj hc
  | none =>
    obtain ⟨hs, -, f', hf'⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    have hff : f' = f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hf'] at h; exact Option.some.inj h
    subst hff
    have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l :=
      ⟨f', by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf']⟩
    have hT := pctx_noOR hspec X hs hsh
    have hH := hph X l f' cl hf' hs o (fun N e us hT' hu => hio N e us hT' hu)
    exact HiddenP_weaken (fun t _ => by simp) (fun w h => WordOK_transferS (InclS_pub_cut _ j' Sj) hT h) hH


theorem pcl9e_pubLive_obs (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    ObsClP p k arch Sp Init MintOK c0 plantOf plantN (fun E mem _ => PubLive E mem) (fun E mem _ => PubLive E mem) := by
  intro c Eg Tot HP HS cr db j th a v w X j' Sj hjj hold l cl f b S1 us o hc ho hf hs hu hlt
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    obtain ⟨t, m, hm, hma⟩ := hold l cl' f b S1 us o e ho hf0 hs hu hlt
    have hm' : c.mem[t]? = some m := hm
    exact ⟨t, m, by show (c.mem.push ⟨a, v, w⟩)[t]? = some m; rw [push_pre t (lt_of_get hm')]; exact hm', hma⟩
  | none =>
    obtain ⟨hs0, hoj, -, -⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
    obtain ⟨vals, hcv, hl, -⟩ := hm0.2.1 l cl (cutSto_own hs0 hoj) hoj
    have hcov := seg_cover hcv hs hu hlt
    obtain ⟨⟨m, hm, hma, -⟩, -, -⟩ := hl (b + o) _ (List.getElem?_eq_getElem hcov)
    have hm' : c.mem[th.vs.coh ⟨l, b + o⟩]? = some m := hm
    exact ⟨_, m, by show (c.mem.push ⟨a, v, w⟩)[_]? = some m; rw [push_pre _ (lt_of_get hm')]; exact hm', hma⟩


theorem pcl9d_pubPair_obs (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hnt : PromNoTwoPF p k arch Sp Init MintOK c0)
    (hpp : PlantPairF p k arch Sp Init MintOK c0 plantOf plantN) :
    ObsClP p k arch Sp Init MintOK c0 plantOf plantN (fun E mem pairs => PubPair E mem pairs []) (fun E mem pairs => PubPair E mem pairs []) := by
  intro c Eg Tot HP HS cr db j th a v w X j' Sj hjj hold l cl f o hc hg hf hTw t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1
    hh0 hh1 hps
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  have hc1 : Eg.sto l = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
  -- the new message is not at either word of the unit
  have hold' : ∀ (t : Nat) (m : Msg), (c.mem.push ⟨a, v, w⟩)[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) →
      c.mem[t]? = some m := by
    intro t m ht hl
    rcases push_get ht with ⟨-, h2⟩ | ⟨-, rfl⟩
    · exact h2
    · rcases hl with e | e
      · have e' : a = ⟨l, o⟩ := e
        have hal : a.label = l := by rw [e']
        exact absurd (by rw [e']) ((hnt X cl (by rw [hal]; exact hc1) o hTw).1)
      · have e' : a = ⟨l, o + 1⟩ := e
        have hal : a.label = l := by rw [e']
        exact absurd (by rw [e']) ((hnt X cl (by rw [hal]; exact hc1) o hTw).2)
  have h0' := hold' t0 m0 h0 (.inl hl0)
  have h1' := hold' t1 m1 h1 (.inr hl1)
  have hpre : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → (c.mem.push ⟨a, v, w⟩)[t]? = some m :=
    fun t m h => by rw [push_pre t (lt_of_get h)]; exact h
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    have hpairs : ∀ q, q ∈ c.pairs → q + 1 < c.mem.size := by
      obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
      exact hm0.1.2.2
    exact PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h)
      (hold l cl' f o e (by have h := hg; rw [cutP_ini hn, cutP_rc hn] at h; exact h) hf0 hTw t0 t1 m0 m1 hs0 hs1 h0' h1' hl0 hl1
        (hiddenFrom_grow hpre hh0) (hiddenFrom_grow hpre hh1)
        (pairStraddles_back push_pre (fun q h => h) hpairs hps)) hI.box hI.rini
  | none =>
    obtain ⟨hs0', -, f', hf'⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    have hff : f' = f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hf'] at h; exact Option.some.inj h
    subst hff
    have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l :=
      ⟨f', by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf']⟩
    exact PairOK_transferS (InclS_pub_cut _ j' Sj) (pctx_noOR hspec X hs0' hsh)
      (hpp X l f' cl hf' hs0' o hTw (hg.elim (fun h => h.2) (fun h => by
        obtain ⟨b, S, us, o', h1, h2, h3, h4, -, h6⟩ := h.2
        exact ⟨b, S, us, o', h1, h2, h3, h4, h6⟩)) t0 t1 m0 m1 h0 h1 hl0 hl1 hh0 hh1 hps)

end
#print axioms TermInterfObs.pcl7_pubDefP_obs
#print axioms TermInterfObs.pcl9e_pubLive_obs
#print axioms TermInterfObs.pcl9d_pubPair_obs
#print axioms TermInterfObs.cl9e_pubLive_obs
#print axioms TermInterfObs.cl9d_pubPair_obs
#print axioms TermInterfObs.cl7_pubDefP_obs
end TermInterfObs

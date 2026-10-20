import WeakCore.TermOwnX2
import WeakCore.TermPubW
import WeakCore.TermInterf
import WeakCore.TermOwnHeldQ

/-!
# TermOwnK4 (own-key layer, package): word/pub/cas/ldp/stp/sum ops, and `OwnXPub1`

The share of `OwnXStepT` (`TermOwnX2.OwnXStepPkg … 4`) and the publish of `x` (`OwnXPub1`).

* Skeleton: `ownXLe_of_step` (any thread step into a certified configuration, from a per-result
  obligation `Tgt` at the source frame `Src`).
* Vacuous: `intoRgn`, `mkTicket`, `claim` are outside `ScopeD`.
* Frame-only (`tstepR_step` + `Same`): non-boxed `inl`, `inr`, `case`.
-/

namespace TermOwnK4
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Generic helpers -/

/-- A frame-only step moves no own key. -/
theorem totStep_own_le {t : Expr} {η : TEnv} {Tot Tot' : Res} (h : TotStep t η Tot Tot') (l : AllocLabel) :
    Tot' (.own l) ≤ Tot (.own l) := by
  cases h with
  | same => exact Nat.le_refl _
  | fresh => simp
  | claim n j _ hle =>
    have h1 := Res.le_def.1 hle (.own l)
    simp at h1
    exact h1

/-! ## The step skeleton -/

/-- The source of a K4 step: thread `i`'s resourceful frame `ρ η cx Rf Rs`, memory, the private
holding `HP`, the bound, and what the footprint lemma needs. -/
structure Src (p : Prog) (g : G) (x : AllocLabel) (n : Nat) (mem : Memory) (pairs : List Ts) (th : TTh)
    (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs HP : Res) : Prop where
  gp : g.p = p
  gn : 0 < g.n
  hE : EnvOK p η
  hT : Typed p cx th.term
  ck : TermA4.CkW p η.wit cx th.term
  tv : TvOK cx
  hF : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf
  hm : MemInv g (CE η) (stOf mem pairs th)
  hH : MemHeldP (CE η) (stOf mem pairs th) HP
  bf : g.boxFence = true
  nie : TermOwnX2.StoNIE (CE η)
  sto : (CE η).sto x ≠ none
  le : (Rf + Rs) (.own x) + HP (.own x) ≤ n
  sc : ScopeD th.σs cx th.term
  px : PAx g mem pairs th
  win : TermStep.PubWinT3 (CE η) (stOf mem pairs th) th
  rp : RetPw th.σs th.stack cx.ret

/-- The target at every taken result: `OwnXLe`'s body at bound `n'`. -/
def Tgt (p : Prog) (g : G) (x : AllocLabel) (n' : Nat) (Es : TEnv) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ E Tot HP, ThInvRE p E r.2.2 Tot ∧
    MemInv g E (stOf r.1 r.2.1 r.2.2) ∧ MemHeldP E (stOf r.1 r.2.1 r.2.2) HP ∧ TermOwnX2.StoNIE E ∧
    E.sto x ≠ none ∧
    Tot (.own x) + HP (.own x) ≤ n' ∧ TermOwnX2.AnchStep g th Es E (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)

/-- **The skeleton**: `OwnXLe … n'` after a thread step into a certified configuration, from `Tgt`
at every source frame. -/
theorem ownXLe_of_src [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n n' : Nat}
    {c0 c0' : Cfg} {th : TTh} (hth : c0.ths[i]? = some th) (hsc : ScopeAt p i c0)
    (hw : NoHoldPubA p k arch E0 E0 i c0) (hvI : TermViewInv.ViewInv c0) (hI : TermOwnX2.OwnXLe p k arch E0 i x n c0)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hc : Certified p k arch c0' i)
    (h : ∀ ρ η cx Rf Rs HP, Src p (gOf p k arch c0 i) x n c0.mem c0.pairs th ρ η cx Rf Rs HP →
      Tgt p (gOf p k arch c0 i) x n' (CE η) c0.mem c0.pairs th) :
    TermOwnX2.OwnXLe p k arch E0 i x n' c0' := by
  obtain ⟨th1, E, Tot, HP, hth1, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hT, htv, hFI, rfl, hRP⟩, hm, hH, hbf, hnie, hsto, hle, hx0, hA⟩ := hI
  rw [hth] at hth1
  cases hth1
  have hFp := TermOwnX2.finv_of htv hFI
  have hS : Src p (gOf p k arch c0 i) x n c0.mem c0.pairs th ρ η cx Rf Rs HP :=
    ⟨rfl, Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (arr_lt hth)), hE, hT.1, hT.2, htv, hFI, hm, hH, hbf, hnie, hsto, hle,
      hsc th hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hT.1 htv hFp, PAx_of_step hs hc hth, TermStep.PubWinT3_of hm (hw th hth ρ η cx hE hT.1 htv hFp hm hx0 hA.1 hA.2.2.1)
        (fun _ _ _ _ _ _ ht hea hws => TermOwnX2.publish_own_cell (η := η) hT.1 hFp ht hea hws), hRP⟩
  obtain ⟨th', r, hth', hr, e1, e2, e3, hpa⟩ := taken_promAbove hs hc
  rw [hth] at hth'
  cases hth'
  obtain ⟨E', Tot', HP', hT', hm', hH', hnie', hsto', hle', hAS⟩ := h ρ η cx Rf Rs HP hS r hr hpa
  obtain ⟨hx', hA'⟩ := hAS E0 hx0 hA hm.2.2.2.1 hm' (TermOwnX2.wrHyp hE hT.1 htv hFp hm hS.sc (TermViewInv.envVR_solo (p := p) (k := k) (arch := arch) hvI (.refl _) hth) hr)
  refine ⟨r.2.2, E', Tot', HP', e3, hT', ?_, ?_, by rw [gOf_thread hs]; exact hbf, hnie', hsto', hle', hx', ?_⟩
  · rw [gOf_thread hs, e1, e2]; exact hm'
  · rw [e1, e2]; exact hH'
  · rw [e1, e2]; exact hA'

/-! ## Frame-only steps that change no state -/

/-- `Tgt` for a frame-only step (`tstepR_step`'s conclusion) changing nothing `MemInv` reads. -/
theorem tgt_same {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (hR : ∀ r ∈ tstep g mem pairs th, ∃ Tot', ThInvRE p (CE η) r.2.2 Tot' ∧ TotStep th.term η (Rf + Rs) Tot')
    (hsm : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    Tgt p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨Tot', hT', hts⟩ := hR r hr
  have e := hsm r hr
  refine ⟨CE η, Tot', HP, hT', MemInv_same hS.hm e, TermOwnHeldQ.memHeldOn_eqs hS.hH e.1 e.2.2.2.1, hS.nie, hS.sto, ?_, TermOwnX2.anchStep_eqs e.1 e.2.2.2.1⟩
  have h1 := totStep_own_le hts x
  have h2 := hS.le
  omega

/-- `Tgt` for a frame-only term (`StepScopeR`) whose steps change nothing `MemInv` reads. -/
theorem tgt_frame {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP) (hscR : StepScopeR th.σs cx th.term)
    (hsm : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    Tgt p g x n (CE η) mem pairs th := fun r hr hpa =>
  tgt_same hS (tstepR_step hP hS.gp (tstep_notDone hr) hscR hS.hT hS.ck hS.hF hS.hE hS.tv hS.rp hPS hSub hSig).2 hsm r hr hpa

/-- A `let` outside `OpScope` and not a capability op is outside `ScopeD`. -/
theorem scopeD_vac {σs : List Ty} {cx : Cx} {y : String} {op : Op} {e : Expr} (h : ScopeD σs cx (.let_ y op e))
    (hop : ¬ OpScope cx op) (hb : ∀ a b, op ≠ .borrow a b) (hf : ∀ a, op ≠ .freeze a)
    (he : ∀ a, op ≠ .endBorrow a) : False := by
  rcases h with h | ⟨-, x', e', ⟨a, b, h⟩ | ⟨a, h⟩ | ⟨a, h⟩⟩
  · exact hop h
  · cases h; exact hb a b rfl
  · cases h; exact hf a rfl
  · cases h; exact he a rfl

/-! ## Steps that keep memory and only shrink the private labels (publish) -/

/-- The environment change of a step that keeps Σ, the counts and memory, and only adds frontiers
(and `seen`): every private label of `E1` was private in `E`. -/
def EnvShrink (E E1 : TEnv) : Prop :=
  E.prog = E1.prog ∧ E.tid = E1.tid ∧ Incl E E1 ∧ E1.sto = E.sto ∧ E1.ini = E.ini ∧ E1.rini = E.rini ∧
    ∀ l, E1.pfr l = none → E.pfr l = none

theorem envShrink_refl (E : TEnv) : EnvShrink E E :=
  ⟨rfl, rfl, Incl.refl E, rfl, rfl, rfl, fun _ h => h⟩

theorem envShrink_pub (η : TEnv) (lab : AllocLabel) (V : Ts) :
    EnvShrink (CE η) (CE (η.withSto η.sto η.ini (pubP η lab V) (pubS η lab))) := by
  refine ⟨rfl, rfl, ⟨rfl, fun _ _ h => h, fun _ => Nat.le_refl _, fun l f h => pubP_mono η lab V l f h,
    fun _ _ h => h, fun _ => Nat.le_refl _⟩, rfl, rfl, rfl, fun l h => ?_⟩
  show η.pfr l = none
  have h' : pubP η lab V l = none := h
  simp only [pubP] at h'
  split at h'
  · cases h'
  · exact h'

theorem sum_filter_le {α : Type} (q : α → Bool) (f : α → Res) (k : Key) :
    ∀ L : List α, Res.sum ((L.filter q).map f) k ≤ Res.sum (L.map f) k
  | [] => Nat.le_refl _
  | a :: L => by
    have ih := sum_filter_le q f k L
    by_cases hq : q a = true
    · simp only [List.filter_cons, hq, ite_true, List.map_cons, Res.sum_cons, Res.add_apply]; omega
    · simp only [List.filter_cons, hq, List.map_cons, Res.sum_cons, Res.add_apply]
      simp only [Bool.false_eq_true, ite_false]; omega

/-- **The private holding under `EnvShrink`** with memory and promises kept: the entries of the
labels still private move (`HeldEntry_priv_move`); the holding only shrinks. -/
theorem memHeldP_shrink {E E1 : TEnv} {s s' : St} {HP : Res} (hx : EnvShrink E E1)
    (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) (h : MemHeldP E s HP) :
    ∃ HP', MemHeldP E1 s' HP' ∧ ∀ k, HP' k ≤ HP k := by
  classical
  obtain ⟨hp, ht, hI, hsto, hini, hri, hpf⟩ := hx
  have hpv : ∀ l, Priv E1 l → Priv E l := fun l ⟨⟨c, hc, ho⟩, hn⟩ =>
    ⟨⟨c, by rw [← hsto]; exact hc, by rw [ht]; exact ho⟩, hpf l hn⟩
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := h
  refine ⟨Res.sum ((L.filter (fun l => decide (Priv E1 l))).map Rl),
    ⟨_, Rl, hn.filter _, fun l c hq1 hs => List.mem_filter.2 ⟨hc l c (hpv l hq1) (by rw [← hsto]; exact hs),
      by simpa using hq1⟩, fun l hl => by simpa using (List.mem_filter.1 hl).2, rfl, fun l hl => ?_⟩,
    fun k => sum_filter_le _ Rl k L⟩
  have hl1 := (List.mem_filter.1 hl).1
  exact TermInterf.HeldEntry_priv_move hp ht hI (hq l hl1) (by simpa using (List.mem_filter.1 hl).2) (by rw [hsto])
    (by rw [hini]) (by rw [hri]) e2 (fun t _ => by rw [e1])
    (fun t m h1 h2 => by rw [e1] at h2; exact absurd (lt_of_get h2) (by omega)) (he l hl1)

/-- `PubScope` from `ScopeD` at a `publish`. -/
theorem pubScope_of {σs : List Ty} {cx : Cx} {y : String} {a : At} {e : Expr}
    (h : ScopeD σs cx (.let_ y (.publish a) e)) : PubScope cx a := by
  rcases h with h | ⟨-, x', e', ⟨a, b, h⟩ | ⟨a, h⟩ | ⟨a, h⟩⟩
  · exact h
  all_goals cases h

/-- The coupling/own/region side conditions of `MemInv_publishW` at a published pointer's cell. -/
theorem pubCell_side {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx c₁ : Cx} {env : Env}
    {a : At} {u : Ty} {c : Cell} (hE : EnvOK p η) (htv : TvOK cx)
    (hi1 : FInv ρ η σs (fun _ _ => True) c₁ env) (hu : cx.use a = .ok (.ptr .own u, c₁))
    (hsh : Ty.sharedOKIn c₁.ke (.ptr .pub u) = true) (hsc : PubScope cx a)
    (hcty : Fd c.ty (cl ρ η.wit 0 0 u)) (hacc : accs c.ty ≠ none) :
    (∀ b S, SegOf c.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] c.ty = true ∧
      Ty.noOwnIn [] c.ty = true ∧ rgnFree c.ty = true := by
  have hcu : Ty.coupledOKIn c₁.ke u = true := by
    simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
  have htbu : tb c₁.ke.length u = true := by
    have h := (use_TvOK hu htv).2.1
    rw [← (use_TvOK hu htv).2.2] at h
    simpa [tb] using h
  have hcp := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu
  refine ⟨fun b S hseg _ => ?_, coupledOK_Fd hcty hcp, noOwn_Fd hcty ?_, rgnFree_Fd hcty
    (rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk) hcu
      (hsc _ (use_cases hu).1 _ _ (Or.inl rfl)))⟩
  · obtain ⟨-, rfl⟩ := SegOf_lay hacc hseg
    exact TearOK_Fd hcty (TearOK_of_cpl hcp)
  · have hnu : Ty.noOwnIn c₁.ke u = true := by
      simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
    exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
      (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) u hnu htbu

-- copied from TermStep.tstepMR_publishW, publishBuf rule; holding/credit/footprint
-- lines deleted
/-- `publish` of a buffer: frame part and `MemInv`. -/
theorem pubBuf_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {a : At} {e : Expr} {Rf Rs : Res} {n k : Idx} {u : Ty}
    (hterm : th.term = .let_ y (.publish a) e) (hP : ProgT p)
    (hu : cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁))
    (hsh : Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true)
    (hb : c₁.bind y (.refine (.loc .pub (.array n u)) (.ini k)) = .ok c') (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      ∀ f, (CE η).pfr ad.label = some f → ¬ (CE η).seen ad.label → PubWin (CE η) (stOf mem pairs th) ad.label) (hRP : RetPw th.σs th.stack cx.ret) :
    ∀ r ∈ tstep g mem pairs th, ∃ rt ws E1 Tot', evalAt th.env a = some (rt, ws) ∧ ThInvRE p E1 r.2.2 Tot' ∧
      MemInv g E1 (stOf r.1 r.2.1 r.2.2) ∧ (stOf r.1 r.2.1 r.2.2).mem = mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = th.promises ∧ Tot' + ownW .own ws ≤ Rf + Rs ∧ EnvShrink (CE η) E1 ∧ ∀ l, (CE η).seen l → E1.seen l := by
  obtain ⟨rb, wsb, R0, Rr, hea, hvb, hlb, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
  have hR0 := VRR_buf_R rfl hvR
  have hi1 := hi1R.1
  simp only [VR] at hvb
  obtain ⟨hv, hir⟩ := hvb
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, hμ, hsu⟩ := buf_runtime' hs'
  have hlay : Lay th.σs (.refine (.loc .pub (.array n u)) (.ini k)) (.refine (.loc .pub (.array nr ur)) ψ) wsb := by
    obtain ⟨h1, -, h3, h4⟩ := hlb
    refine ⟨h1, ?_, h3, h4.1, ?_⟩
    · rw [close_refine]
      show etok (rf (skel (.loc .pub (.array nr ur)))) = etok (rf (skel (close th.σs (.loc .pub (.array n u)))))
      rw [skel_close_locArr]
      show rf (.loc (skelM .pub) (.array (.lit 0) (etok (skel ur)))) = _
      rw [hsu]; rfl
    · simp only [close, substTs, lyt, etok, anyB_zero, Bool.false_eq_true, ite_false, idxC, ofMs, modeC]
      rw [(buf_lyt h4.2 rfl).2]; rfl
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
        withS { th with term := e, env := (y, .refine (.loc .pub (.array nr ur)) ψ, wsb) :: th.env }
          (fenceS (stOf mem pairs th) .st))] := by
    simp only [tstep, hterm, evalOp, hea]; rfl
  intro r hr
  rw [key, List.mem_singleton] at hr
  subst hr
  have hleT : Rr + Rs + ownW .own wsb ≤ Rf + Rs := Res.le_def.2 fun k => by
    have h1 := Res.le_def.1 hle k
    have h3 := congrArg (fun R : Res => R k) hR0
    simp only [Res.add_apply] at h1 h3 ⊢; omega
  rcases hv with ⟨hnull, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat, hFU, hmode, hini⟩
  · -- a null handle (an empty buffer): only the fence
    have hvz : VRR ρ η (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
      simp only [VRR]; exact ⟨⟨Or.inl ⟨hnull, e0, he0⟩, rfl⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
    have hfr := bindR hb hi1R (RLink_of hE.2.1 hE.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    exact ⟨_, wsb, CE η, Rr + Rs, hea, ⟨ρ, η, c', Rr, Rs, rfl, hE, he, htv', hfr, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, MemInv_fence hm, rfl, rfl,
      hleT, envShrink_refl _, fun _ h => h⟩
  · obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
    have hown : c.owner = some η.tid := hmode
    have hx : Ext η (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
      Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η ad.label _) (fun l h => Or.inr h)
    have hvr : VR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
        (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb := by
      simp only [VR]
      exact ⟨Or.inr ⟨ad, c, _, hws, hsto, hat, .refl,
        ⟨(η.pfr ad.label).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩,
        (IniAt_mono (modeIni_le_ini _ _ _) hini)⟩, IniR_mono (TEnv.selIni_le_ini η _) hir⟩
    have hE' : EnvOK p (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hvz : VRR ρ (η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label))
        (.refine (.loc .pub (.array n u)) (.ini k)) (shp (.refine (.loc .pub (.array nr ur)) ψ)) wsb .zero := by
      simp only [VR] at hvr; simp only [VRR]; exact ⟨⟨hvr.1, rfl⟩, hvr.2⟩
    have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    have hcu : Ty.coupledOKIn c₁.ke (.array n u) = true := by
      simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.1
    have htbu : tb c₁.ke.length (.array n u) = true := by
      have h := (use_TvOK hu htv).2.1
      rw [← (use_TvOK hu htv).2.2] at h
      simpa [tb] using h
    have hcp := coupledOK_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1) (fun k _ hk => hi1.2.2.2.2.2.2.2.1 k hk) hcu htbu
    obtain ⟨vals, hcell, -⟩ := hm.2.1 ad.label c hsto hown
    exact ⟨_, wsb, _, Rr + Rs, hea,
      ⟨ρ, η.withSto η.sto η.ini (pubP η ad.label (stOf mem pairs th).vs.vWr) (pubS η ad.label), c', Rr, Rs, rfl, hE',
        he, htv', hfr, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩,
      MemInv_publishW (E := CE η) (hF3 := hwin _ _ ad hea hws) hm hsto hown rfl rfl rfl rfl rfl rfl rfl
        (fun b S hseg ha => by
          rcases hseg with ⟨-, rfl, -⟩ | ⟨N, usS, j, hT, -, -, -⟩
          · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
          · have e1 := AtOff_arr_here hat hT ha (by simp [cl, accs])
            rw [hT] at e1
            simp only [cl, Ty.array.injEq] at e1
            obtain ⟨-, rfl⟩ := e1
            have := hcp
            simp only [cl, Ty.coupledOK, Ty.coupledOKIn] at this; exact TearOK_of_cpl this)
        (by
          rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
          · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
          · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]; exact hcp)
        (by
          rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
          · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
          · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
            have hnu : Ty.noOwnIn c₁.ke (.array n u) = true := by
              simp only [Ty.sharedOKIn, Bool.and_eq_true] at hsh; exact hsh.1.2
            exact NoOwnCl.noOwn_cl0 ρ η.wit c₁.ke (fun k => (hE.2.1 k).1)
              (fun k _ hk => hi1.2.2.2.2.2.2.2.2.2.1 k hk) _ hnu htbu)
        (by
          rcases LayT_of_CellOK hcell with ha | ⟨N, S, hT, ha⟩
          · exact absurd (accs_AtOff hat ha) (by simp [cl, accs])
          · rw [← AtOff_arr_here hat hT ha (by simp [cl, accs])]
            exact rgnFree_cl0 ρ η.wit c₁.ke (fun k hk => hi1.2.2.2.2.2.2.2.2.2.2 k hk) hcu
              (hsc _ (use_cases hu).1 _ _ (Or.inr ⟨_, rfl⟩))),
      rfl, rfl, hleT, envShrink_pub η ad.label _, fun _ h => Or.inr h⟩

-- copied from TermStep.tstepMR_publishW, publish rule; holding/credit/footprint
-- lines deleted, side conditions factored into `pubCell_side`
/-- **`publish`, frame part and `MemInv`**: the frame drops the own handle; memory is kept. -/
theorem pub_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {a : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ y (.publish a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : PubScope cx a)
    (hwin : ∀ rt ws ad, evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad 0] →
      ∀ f, (CE η).pfr ad.label = some f → ¬ (CE η).seen ad.label → PubWin (CE η) (stOf mem pairs th) ad.label) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    ∀ r ∈ tstep g mem pairs th, ∃ rt ws E1 Tot', evalAt th.env a = some (rt, ws) ∧ ThInvRE p E1 r.2.2 Tot' ∧
      MemInv g E1 (stOf r.1 r.2.1 r.2.2) ∧ (stOf r.1 r.2.1 r.2.2).mem = mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = th.promises ∧ Tot' + ownW .own ws ≤ Rf + Rs ∧ EnvShrink (CE η) E1 ∧ ∀ l, (CE η).seen l → E1.seen l := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, hsh, hb⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind y (.ptr .pub u) = .ok c' := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨rt, ws, R0, Rr, hea, hv, hl, hvR, hi1R, hle⟩ := useR hu hi hE.2.2
    have hR0 := VRR_cell_R rfl hvR
    have hi1 := hi1R.1
    simp only [VR] at hv
    obtain ⟨⟨lab, off⟩, c, hws, hoff, hsto, hcty, hmode, hacc⟩ := hv
    simp only at hoff; subst hoff
    obtain ⟨pw, rfl, hpw⟩ : ∃ pw, ws = [pw] ∧ pw.val = .loc ⟨lab, 0⟩ 0 := by
      match ws, hws with
      | [pw], h => exact ⟨pw, rfl, by simpa using h⟩
      | [], h => simp at h
      | _ :: _ :: _, h => simp at h
    have hsk := hl.2.1
    rw [close_ptr] at hsk
    obtain ⟨ru, rfl, hsku⟩ : ∃ ru, rt = .ptr .own ru ∧ etok (skel ru) = etok (skel (close th.σs u)) := by
      cases rt <;> simp [skel, etok] at hsk
      case ptr μ ru =>
        cases μ <;> simp [skelM, etok] at hsk
        exact ⟨ru, rfl, hsk⟩
      case refine t ψ => unfold rf at hsk; split at hsk <;> simp [etok] at hsk
    have hown : c.owner = some η.tid := hmode
    have hx : Ext η (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      Ext_withSto hE.2.1 (fun l c h => h) (fun _ => Nat.le_refl _) (pubP_mono η lab _) (fun l h => Or.inr h)
    have key : tstep g mem pairs th =
        [((fenceS (stOf mem pairs th) .st).mem, (fenceS (stOf mem pairs th) .st).pairs,
          withS { th with term := e, env := (y, .ptr .pub ru, [pw]) :: th.env } (fenceS (stOf mem pairs th) .st))] := by
      simp only [tstep, hterm, evalOp, hea]; rfl
    intro r hr
    rw [key, List.mem_singleton] at hr
    subst hr
    have hvr : VR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] := by
      simp only [VR]
      exact ⟨⟨lab, 0⟩, c, hws, rfl, hsto, hcty,
        ⟨(η.pfr lab).getD (stOf mem pairs th).vs.vWr, by simp [TEnv.withSto, pubP], Or.inl (Or.inl rfl)⟩, hacc⟩
    have hlay : Lay th.σs (.ptr .pub u) (.ptr .pub ru) [pw] :=
      ⟨fun us h => by simp [accs] at h; subst h; rfl, by rw [close_ptr]; simp only [skel, etok, hsku],
        by simp [wc, accs], ⟨⟨lab, 0⟩, hws⟩, by
          simp only [close, substTs, lyt, etok]; rw [(cell_lyt hl.2.2.2.2 rfl rfl).2]; rfl⟩
    have hE' : EnvOK p (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab)) :=
      ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩
    have hvz : VRR ρ (η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab))
        (.ptr .pub u) (shp (.ptr .pub ru)) [pw] .zero := by
      simp only [VR] at hvr; simp only [VRR]; exact ⟨hvr, rfl⟩
    have hfr := bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1R) (RLink_of hE'.2.1 hE'.2.2) hvz hlay
    rw [Res.add_zero] at hfr
    have hleT : Rr + Rs + ownW .own [pw] ≤ Rf + Rs := Res.le_def.2 fun k => by
      have h1 := Res.le_def.1 hle k
      have h3 := congrArg (fun R : Res => R k) hR0
      simp only [Res.add_apply] at h1 h3 ⊢; omega
    obtain ⟨s1, s2, s3, s4⟩ := pubCell_side hE htv hi1 hu hsh hsc hcty hacc
    exact ⟨_, [pw], _, Rr + Rs, hea,
      ⟨ρ, η.withSto η.sto η.ini (pubP η lab (stOf mem pairs th).vs.vWr) (pubS η lab), c', Rr, Rs, rfl, hE', ⟨he, hck⟩,
        htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩,
      MemInv_publishW (E := CE η) (hF3 := hwin _ _ ⟨lab, 0⟩ hea (by simp [hpw])) hm hsto hown rfl rfl rfl rfl rfl
        rfl rfl s1 s2 s3 s4, rfl, rfl, hleT, envShrink_pub η lab _, fun _ h => Or.inr h⟩
  | publishBuf hu hsh hb => exact pubBuf_step hterm hP hu hsh hb ⟨he, hck⟩ htv' hi hE htv hm hsc hwin hRP

/-- A shrink step's environment extends the source's (it adds `seen`). -/
theorem ext_shrink {p : Prog} {η E1 : TEnv} {th : TTh} {Tot : Res} (hRE : ThInvRE p E1 th Tot)
    (hx : EnvShrink (CE η) E1) (hsn : ∀ l, (CE η).seen l → E1.seen l) : Ext (CE η) E1 := by
  obtain ⟨_, η', _, _, _, rfl, _⟩ := hRE
  exact ⟨Coh_CE η', rfl, hx.1.symm, hx.2.1.symm, hx.2.2.1.sto, hx.2.2.1.ini, hx.2.2.1.pfr, hsn, hx.2.2.1.box,
    Nat.le_refl _, CohR_CE η', hx.2.2.1.rini⟩

/-- **`Tgt` at a `publish`** (generic bound): the handle leaves the frame, the private holding shrinks. -/
theorem tgt_publish {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {a : At} {e : Expr} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (hterm : th.term = .let_ y (.publish a) e) (hPS : PwSkel) : Tgt p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨rt, ws, E1, Tot', -, hT', hm', e1, e2, hle, hx, hsn⟩ := pub_step hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    (pubScope_of (by rw [← hterm]; exact hS.sc)) (fun rt ws ad hea hws => hS.win _ _ _ rt ws ad hterm hea hws) hS.rp hPS r hr
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrink hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.anchStep_shrink (ext_shrink hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  simp only [Res.add_apply] at h1 h3
  omega

/-- **`Tgt` at the publish of `x`** (sharp bound 1 → 0). -/
theorem tgt_publish1 {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat}
    (hS : Src p g x 1 mem pairs th ρ η cx Rf Rs HP) (hterm : th.term = .let_ y (.publish a) e)
    (hea0 : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hxl : ad.label = x) (hPS : PwSkel) :
    Tgt p g x 0 (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨rt', ws', E1, Tot', hea, hT', hm', e1, e2, hle, hx, hsn⟩ := pub_step hterm hP hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm
    (pubScope_of (by rw [← hterm]; exact hS.sc)) (fun rt ws ad hea hws => hS.win _ _ _ rt ws ad hterm hea hws) hS.rp hPS r hr
  rw [hea0, Option.some.injEq, Prod.mk.injEq] at hea
  obtain ⟨-, rfl⟩ := hea
  obtain ⟨HP', hH', hle'⟩ := memHeldP_shrink hx e1 e2 hS.hH
  refine ⟨E1, Tot', HP', hT', hm', hH', fun l cl h => hS.nie l cl (by rw [← hx.2.2.2.1]; exact h),
    by rw [hx.2.2.2.1]; exact hS.sto, ?_,
    TermOwnX2.anchStep_shrink (ext_shrink hT' hx hsn) hx.2.2.2.1 hx.2.2.2.2.1 e1 e2⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h2 := hle' (.own x)
  have h3 := hS.le
  rw [ownW_own_loc hws, hxl] at h1
  simp only [Res.add_apply, Res.one_apply, ite_true] at h1 h3
  omega

/-- **The publish of `x`** (n = 1 → 0), private form. -/
theorem ownXPub1 [WrIniC] {p : Prog} [ProgRetIall p] (hP : ProgT p) {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {x : AllocLabel} (hPS : PwSkel) : TermOwnX2.OwnXPub1 p k arch i x :=
  fun _ _ _ th _ _ _ _ _ _ _ hsc hw hvI hI hs hc hth hterm hea hws hxl =>
    ownXLe_of_src hth hsc hw hvI hI hs hc fun _ _ _ _ _ _ hS => tgt_publish1 hP hS hterm hea hws hxl hPS

/-! ## Word constructors: memory kept, the frame's total kept -/

/-- The shape of a state-keeping step at the frame's total. -/
def KeepOut (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (T : Res) : Prop :=
  ∀ r ∈ tstep g mem pairs th, stOf r.1 r.2.1 r.2.2 = stOf mem pairs th ∧ ThInvRE p (CE η) r.2.2 T

theorem tgt_keep {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (h : KeepOut p g mem pairs th η (Rf + Rs)) : Tgt p g x n (CE η) mem pairs th := by
  intro r hr _
  obtain ⟨e, hT'⟩ := h r hr
  rw [e]
  exact ⟨CE η, Rf + Rs, HP, hT', hS.hm, hS.hH, hS.nie, hS.sto, hS.le, TermOwnX2.anchStep_eqs rfl rfl⟩

-- copied from TermStep.tstepMC_mkWord and TermStep.tstepMC_mkWordGhost;
-- holding/credit lines deleted
theorem mkWord_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : Proto} {v tk : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.mkWord rn P v tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) : KeepOut p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord hidx hpwf hu heq hv hst hcl hng hho hb =>
    rename_i c₁ r r' j k c cl
    obtain ⟨rt0, ws0, R0, Rr, -, -, -, hR0, hi1, hle⟩ := useR hu hi hE.2.2
    have hR : R0 = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r)) := by
      simp only [VRR, tokWd_none] at hR0; rw [hR0, heq ρ hi1.1.1]
    obtain ⟨tv, htvk, hio⟩ := hv
    obtain ⟨rt, w, hea, hwv, -⟩ := atom_num hi1.1.2.1 htvk hio
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .word (.lit 0) P, [w]) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hng, hea]; rfl
    intro r0 hr
    rw [key, List.mem_singleton] at hr
    subst hr
    obtain ⟨cl', hcl', hent⟩ := hst
    rw [hcl] at hcl'; cases hcl'
    have hn := hent ρ hi1.1.1
    have hvr : VRR ρ η (.word r P) (shp (.word (.lit 0) P)) [w] (.one (.rg (ev ρ r)) + wdW P (ev ρ r)) := by
      simp only [VRR]
      refine ⟨⟨hpwf, fun _ => ⟨_, by simp [hwv], _, cl, _, hcl, hn⟩⟩, Or.inl ⟨?_, by first | rfl | trivial⟩⟩
      exact ⟨hng, ev ρ j, c, cl, ev ρ k, by simp [hwv], hcl, hho, hn⟩
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr (Lay_word th.σs r P hng w)
    have hfr' : FInvR ρ η th.σs (ResumeR p th.stack Rs) c' ((x, .word (.lit 0) P, [w]) :: th.env) Rf :=
      FInvR_mono hfr (frame_trade hle (by rw [hR]; exact tokNone_pays P _ _ (Res.le_refl _)))
    exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩
  | mkWordGhost hidx hpwf hu heq hv hst hcl hg hho hb =>
    rename_i c₁ r r' j k c cl
    obtain ⟨rt0, ws0, R0, Rr, -, -, -, hR0, hi1, hle⟩ := useR hu hi hE.2.2
    have hR : R0 = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r)) := by
      simp only [VRR, tokWd_none] at hR0; rw [hR0, heq ρ hi1.1.1]
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .prod (.word (.lit 0) P) (.tok (.lit 0) none), []) :: th.env }
            (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hg]; rfl
    intro r0 hr
    rw [key, List.mem_singleton] at hr
    subst hr
    have hvr : VRR ρ η (.prod (.word r P) (.tok r (some (P, j))))
        (shp (.prod (.word (.lit 0) P) (.tok (.lit 0) none))) [] (wdW P (ev ρ r) + .one (.rg (ev ρ r))) := by
      simp only [VRR]
      refine ⟨_, _, rfl, wdW P (ev ρ r), .one (.rg (ev ρ r)), rfl, fun hn => ?_, fun n hn => ?_⟩
      · simp [shp_wc, wc, accs, hg, nWords] at hn
      · simp [shp_wc, wc, accs, hg, nWords] at hn
        subst hn
        refine ⟨by simp, ⟨⟨hpwf, fun h => by rw [hg] at h; cases h⟩, Or.inr ⟨fun h => ?_, by first | rfl | trivial⟩⟩,
          by first | rfl | trivial⟩
        have h1 := h.1; rw [hg] at h1; cases h1
    have hl2 := Lay_pair (Lay_wordGhost th.σs r P hg) (Lay_tokGhost th.σs r P j)
    have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr hl2
    have hfr' : FInvR ρ η th.σs (ResumeR p th.stack Rs) c'
        ((x, .prod (.word (.lit 0) P) (.tok (.lit 0) none), []) :: th.env) Rf :=
      FInvR_mono hfr (frame_trade hle (by
        rw [hR]; exact fun k => by have := wdW_le P (ev ρ r) k; simp only [Res.add_apply] at *; omega))
    exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩

-- copied from TermStep.tstepMC_mkWord2; holding/credit lines deleted
theorem mkWord2_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : Proto2} {v0 v1 tk : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.mkWord2 rn P v0 v1 tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) : KeepOut p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord2 hidx hpwf hu heq hv0 hv1 hst hcl hho hb =>
  rename_i c₁ r r' j0 j1 k0 k1 c cl
  obtain ⟨rt0, ws0, R0, Rr, -, -, -, hR0, hi1, hle⟩ := useR hu hi hE.2.2
  have hR : R0 = .one (.rg (ev ρ r)) + .one (.wd (ev ρ r)) := by
    simp only [VRR, tokWd_none] at hR0; rw [hR0, heq ρ hi1.1.1]
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_num hi1.1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_num hi1.1.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .word2 (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  intro r0 hr
  rw [key, List.mem_singleton] at hr
  subst hr
  obtain ⟨cl', hcl', hent⟩ := hst
  rw [hcl] at hcl'; cases hcl'
  obtain ⟨h0, h1, h2⟩ := hent ρ hi1.1.1
  have hvr : VRR ρ η (.word2 r P) (shp (.word2 (.lit 0) P)) [w0, w1] (.one (.rg (ev ρ r)) + .one (.wd (ev ρ r))) := by
    simp only [VRR]
    refine ⟨⟨hpwf, _, _, by simp [hwv0, hwv1], _, cl, _, _, hcl, h0, h1, h2⟩,
      Or.inl ⟨?_, by first | rfl | trivial⟩⟩
    exact ⟨_, _, c, cl, _, _, by simp [hwv0, hwv1], hcl, hho, h0, h1, h2⟩
  have hfr := bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr (Lay_word2 th.σs r P w0 w1)
  have hfr' : FInvR ρ η th.σs (ResumeR p th.stack Rs) c' ((x, .word2 (.lit 0) P, [w0, w1]) :: th.env) Rf :=
    FInvR_mono hfr (by rw [← hR, Res.add_comm]; exact hle)
  exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩

-- copied from TermStep.tstepMC_mkEPair; holding/credit lines deleted
theorem mkEPair_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : ECounter} {v0 v1 : At} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.mkEPair rn P v0 v1) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) : KeepOut p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkEPair hidx hpwf hv0 hv1 hb =>
  rename_i r j0 j1
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_num hi.1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_num hi.1.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .epair (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  intro r0 hr
  rw [key, List.mem_singleton] at hr
  subst hr
  have hvr : VRR ρ η (.epair r P) (shp (.epair (.lit 0) P)) [w0, w1] .zero := by
    simp only [VRR]
    exact ⟨⟨hpwf, _, _, by simp [hwv0, hwv1]; exact ⟨rfl, rfl⟩⟩, by first | rfl | trivial⟩
  have hfr := bindR hb hi (RLink_of hE.2.1 hE.2.2) hvr (Lay_epair th.σs r P w0 w1)
  have hfr' : FInvR ρ η th.σs (ResumeR p th.stack Rs) c' ((x, .epair (.lit 0) P, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr; exact hfr
  exact ⟨by rw [stOf_withS], ⟨ρ, η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', by simpa [withS] using hfr', rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩

/-! ## Pair loads: memory and promises kept, `MemInv` re-proved at the same environment -/

/-- The shape of a step keeping memory and promises at the source environment and frame total. -/
def KeepOutM (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (T : Res) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
    (stOf r.1 r.2.1 r.2.2).mem = (stOf mem pairs th).mem ∧
    (stOf r.1 r.2.1 r.2.2).promises = (stOf mem pairs th).promises ∧
    MemInv g (CE η) (stOf r.1 r.2.1 r.2.2) ∧ ThInvRE p (CE η) r.2.2 T

theorem tgt_keepM {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (h : KeepOutM p g mem pairs th η (Rf + Rs)) : Tgt p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨e1, e2, hm', hT'⟩ := h r hr hpa
  exact ⟨CE η, Rf + Rs, HP, hT', hm', TermOwnHeldQ.memHeldOn_eqs hS.hH e1 e2, hS.nie, hS.sto, hS.le, TermOwnX2.anchStep_eqs e1 e2⟩

-- copied from TermStep.tstepMC_ldpOwn; holding/credit lines deleted
theorem ldpOwn_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    KeepOutM p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi0 hpk htv hoq
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku
    (peek_cell_lyt hi0.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi0.2.2.2.1 hi0.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi0.2.1 htv hpk rfl hoq hea rfl)
  obtain ⟨hru, hpr⟩ := pair_ru .own hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  intro r0 hr hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bind hu hvr
  have hfr0 := bindR hb (pushR n1 m1 (pushR n0 m0 hi)) (RLink_of hE.2.1 hE.2.2)
    (VR_VRR_copy_closed (by rfl) (by rfl) hvr') (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl))
  have hfr : FInvR (vcons m1 (vcons m0 ρ)) η th.σs (ResumeR p th.stack Rs) c'
      ((x, .prod .int .int, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr0; exact hfr0
  exact ⟨f1, f4, MemInv_load hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl),
    ⟨vcons m1 (vcons m0 ρ), η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩

-- copied from TermStep.tstepMC_ldpPub; holding/credit lines deleted
theorem ldpPub_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr} {Rf Rs : Res}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .pub u))
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    KeepOutM p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_core (p := p) (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hoq hi0 hE htv hm
  obtain ⟨hru, hpr⟩ := pair_ru .pub hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  intro r0 hr hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.two] 0 _ (s', wsr) hl
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bind hu hvr
  have hfr0 := bindR hb (pushR n1 m1 (pushR n0 m0 hi)) (RLink_of hE.2.1 hE.2.2)
    (VR_VRR_copy_closed (by rfl) (by rfl) hvr') (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl))
  have hfr : FInvR (vcons m1 (vcons m0 ρ)) η th.σs (ResumeR p th.stack Rs) c'
      ((x, .prod .int .int, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr0; exact hfr0
  exact ⟨f1, f3, hm', ⟨vcons m1 (vcons m0 ρ), η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩

-- copied from TermStep.tstepMC_ldpLoc; holding/credit lines deleted
theorem ldpLoc_step {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    {Rf Rs : Res}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) :
    KeepOutM p g mem pairs th η (Rf + Rs) := by
  rw [hterm] at hT hCk
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCk
  have htv' := OpT_TvOK hP hop htv
  have hi0 := hi.1
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, -, hstw⟩ :=
    locCell (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ hoq
      (pair_accs_cl hu) hi0 hE htv hm
  obtain ⟨-, hpr⟩ := pair_ru_loc μr hu hsku
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, haddr, ↓reduceIte, List.map_map]; rfl
  intro r0 hr hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨f1, -, f3, -⟩ := loadUnits_frame [.two] 0 _ (s', wsr) hl
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bind hu hvr
  have hfr0 := bindR hb (pushR n1 m1 (pushR n0 m0 hi)) (RLink_of hE.2.1 hE.2.2)
    (VR_VRR_copy_closed (by rfl) (by rfl) hvr') (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl))
  have hfr : FInvR (vcons m1 (vcons m0 ρ)) η th.σs (ResumeR p th.stack Rs) c'
      ((x, .prod .int .int, [w0, w1]) :: th.env) Rf := by
    rw [Res.add_zero] at hfr0; exact hfr0
  exact ⟨f1, f3, hm', ⟨vcons m1 (vcons m0 ρ), η, c', Rf, Rs, rfl, hE, ⟨he, hck⟩, htv', hfr, rfl, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩⟩

/-- `OpScope` from `ScopeD` at a non-capability `let`. -/
theorem opScope_of {σs : List Ty} {cx : Cx} {y : String} {op : Op} {e : Expr} (h : ScopeD σs cx (.let_ y op e))
    (hb : ∀ a b, op ≠ .borrow a b) (hf : ∀ a, op ≠ .freeze a) (he : ∀ a, op ≠ .endBorrow a) : OpScope cx op := by
  rcases h with h | ⟨-, x', e', ⟨a, b, h⟩ | ⟨a, h⟩ | ⟨a, h⟩⟩
  · exact h
  · cases h; exact absurd rfl (hb a b)
  · cases h; exact absurd rfl (hf a)
  · cases h; exact absurd rfl (he a)

theorem tgt_ldp {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {acq : Bool} {a : At} {n0 n1 : String} {e : Expr} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .let_ y (.ldp acq a n0 n1) e) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) : Tgt p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.ldp acq a n0 n1) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hT := hS.hT
  rw [ht] at hT
  cases hT with
  | let_ hop _ =>
    cases hop with
    | ldp hpk _ _ =>
      obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc' _ hpk
      · rw [hteq] at hpk
        rcases hμ with rfl | rfl
        · exact tgt_keepM hS (ldpOwn_step ht hP hu hpk hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
        · exact tgt_keepM hS (ldpPub_step ht hP hu hpk hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)
      · rw [hteq] at hpk
        exact tgt_keepM hS (ldpLoc_step ht hP hu hpk hμ hS.hT hS.ck hS.hF hS.hE hS.tv hS.hm hRP hPS)

/-! ## Pair stores: the private holding by `heldStoreAtP` (private target) or kept (otherwise) -/

-- copied from TermStep.stpC_fin; holding via heldStoreAtP / memHeldOn_store
theorem tgt_pstore {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (hnb : ∀ E1, BumpIf th E1)
    {c' : Cx} {y : String} {rel : Bool} {e : Expr} {pw w0 w1 : Word} {A : Address} {c : Cell} {m : Nat}
    {P : Proto2} {Tf Rv : Res}
    (hkey : tstep g mem pairs th = (storeUnits g.k g.arch pw A rel [.two] [w0, w1] 0 (stOf mem pairs th)).map
        fun s' => (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s'))
    (hmi : ∀ s', s' ∈ storeUnits g.k g.arch pw A rel [.two] [w0, w1] 0 (stOf mem pairs th) → MemInv g (CE η) s')
    (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset (.word2 (.lit m) P))
    (hini : Priv (CE η) A.label → IniAt (CE η).rc c A (.word2 (.lit m) P))
    (hv : EnvValR (CE η) (.word2 (.lit m) P) [w0, w1] (Rv + Res.one (.wd m)))
    (hfr : FInvR ρ η th.σs (ResumeR p th.stack Rs) c' ((y, .unit, []) :: th.env) Tf) (hle : Tf + Rv ≤ Rf)
    (he : TypedK p η c' e) (htv' : TvOK c') (hRPc : RetPw th.σs th.stack c'.ret) : Tgt p g x n (CE η) mem pairs th := by
  intro r hr _
  rw [hkey, List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hT' : ThInvRE p (CE η) (withS { th with term := e, env := (y, .unit, []) :: th.env } s') (Tf + Rs) :=
    ⟨ρ, η, c', Tf, Rs, rfl, hS.hE, he, htv', hfr, rfl, hRPc⟩
  have h1 := Res.le_def.1 hle (.own x)
  have h0 := hS.le
  simp only [Res.add_apply] at h1 h0
  by_cases hq : Priv (CE η) A.label
  · have hq' := hq
    obtain ⟨⟨c0, hc0, hown0⟩, hpfN⟩ := hq'
    have ec : some c0 = some c := hc0.symm.trans hsto
    cases ec
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := TermOwnHeldQ.heldStoreAtP (us := [.two]) hS.hm hS.hH hq hsto
      hown0 (NVP_priv hq) (OwnOKPF_cellP hS.hm.2.1 hsto hown0 hpfN) hat (hini hq) (fun N e h => by cases h) hv
      (by simp [wc, accs, nWords, Acc.size]) rfl
    refine ⟨CE η, Tf + Rs, R2 + H0, hT', hmi s' hs', hput g.k g.arch pw rel _ rfl rfl
      (LoadCoh_of_eq hS.hm.2.1 rfl) (fun _ => Nat.le_refl _) hS.hm.2.2.2.2.1 s' hs', hS.nie, hS.sto, ?_, TermOwnX2.anchStep_same hnb⟩
    have h2 := congrArg (fun R : Res => R (.own x)) hRe
    simp only [Res.add_apply] at h2 ⊢
    have h3 : (Res.one (.wd m)) (.own x) = 0 := by simp [Res.one]
    omega
  · refine ⟨CE η, Tf + Rs, HP, hT', hmi s' hs', TermOwnHeldQ.memHeldOn_store hS.hH (fun l hl e => hq (e ▸ hl))
      hS.hm.2.2.1 hs', hS.nie, hS.sto, ?_, TermOwnX2.anchStep_same hnb⟩
    simp only [Res.add_apply]
    omega

-- copied from TermStep.stpC_core; pwf from ownLoad / loadPub_core, holding lines deleted
theorem stpPtr_tgt {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    {c₁ c' : Cx} {y : String} {rel : Bool} {a v0 v1 tk : At}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause2}
    (hterm : th.term = .let_ y (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hr : EqI c₁ r r') (hj0 : IntIdx c₁ v0 j0)
    (hj1 : IntIdx c₁ v1 j1) (hst : InState2 c₁ P j0 j1 c₂ k0' k1') (hcl : P.clauses[c₂]? = some cl')
    (hxt : (xt = .unit ∧ cl'.holds = true) ∨ (xt = .tok2 r' P j0 j1 ∧ cl'.holds = false))
    (hb : c₁.bind y xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c') (hRP : RetPw th.σs th.stack cx.ret) : Tgt p g x n (CE η) mem pairs th := by
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  obtain ⟨hi1, -⟩ := use_FInv hu hi.1
  have ho : cx.opaqueOK (.word2 r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hcellW : ∀ {c : Cell}, Fd c.ty (cl ρ η.wit 0 0 (.word2 r P)) →
      c.ty = .word2 (.lit (ev ρ r)) P := fun hcty => by
    have h' := hcty; simp only [cl, clI_zero] at h'; exact Fd_word2_eq h'
  rcases hμ with rfl | rfl
  · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi.1 hpk htv ho
    have hct := hcellW hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word2 (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs]))
    have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
    have hpwf : pwf2 P = true := by
      obtain ⟨-, -, -, -, hstw⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
        hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
        (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku
        (peek_cell_lyt hi.1.2.1 hpk hea rfl rfl).2 hsig
        (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi.1.2.2.2.1 hi.1.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.1.2.1 htv hpk rfl ho hea rfl)
      obtain ⟨_, hvr0, -⟩ := hstw
      simp only [VR] at hvr0; exact hvr0.1
    obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
      stp_frame hi hE.2.2 (RLink_of hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
    have hval := (Fd_EnvVal (CE η) hcty).2 (storeWord2_val (r := r) hpwf hi1.1 hst hwv0 hwv1)
    have husA : accs c.ty = some [Acc.two] := by rw [hct]; simp [accs]
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
    exact tgt_pstore hS (TermOwnX2.bumpIf_nb hterm) (A := ⟨lab, 0⟩) key (fun s' hs' => MemInv_store hm hsto hown husA hval rfl s' hs')
      hsto hat (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h) ⟨hvR _ _, by simp [Valid]⟩ hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
  · obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, -, hsku, -⟩ := pubPtr_view hi.1 hpk htv ho
    have hct := hcellW hcty
    have hat : AtOff c.ty (⟨lab, 0⟩ : Address).offset (.word2 (.lit (ev ρ r)) P) := by
      rw [hct]; exact .here (Or.inl (by simp [accs]))
    have hpwf : pwf2 P = true := by
      obtain ⟨_, _, _, _, -, -, -, -, -, -, _, hvr0⟩ :=
        loadPub_core (p := p) (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi.1 hE htv hm
      simp only [VR] at hvr0; exact hvr0.1
    obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
      stp_frame hi hE.2.2 (RLink_of hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
    obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
    have husc : accs c.ty = some [.two] := by rw [hct]; simp [accs]
    have hval := (Fd_EnvVal (CE η) hcty).2 (storeWord2_val (r := r) hpwf hi1.1 hst hwv0 hwv1)
    have key : tstep g mem pairs th =
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
          (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
      simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
    refine tgt_pstore hS (TermOwnX2.bumpIf_nb hterm) (A := ⟨lab, 0⟩) key (fun s' hs' => ?_) hsto hat
      (fun _ => IniAt_of_ne fun N e h => by rw [hct] at h; cases h) ⟨hvR _ _, by simp [Valid]⟩ hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
    by_cases hown : c.owner = some η.tid
    · exact MemInv_storeF hm hsto hown husc hval rfl s' hs'
    · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
      exact MemInv_storePubAt (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
        (IniAt_of_ne fun N e he => hna N e he) hna hval husc rfl s' hs'

-- copied from TermStep.stpLocC_core; pwf from locCell, holding lines deleted
theorem stpLoc_tgt {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    {c₁ c' : Cx} {y : String} {rel : Bool} {a v0 v1 tk : At}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty} {cl' : Clause2}
    (hterm : th.term = .let_ y (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hr : EqI c₁ r r') (hj0 : IntIdx c₁ v0 j0)
    (hj1 : IntIdx c₁ v1 j1) (hst : InState2 c₁ P j0 j1 c₂ k0' k1') (hcl : P.clauses[c₂]? = some cl')
    (hxt : (xt = .unit ∧ cl'.holds = true) ∨ (xt = .tok2 r' P j0 j1 ∧ cl'.holds = false))
    (hb : c₁.bind y xt = .ok c') (he : TypedK p η c' e) (htv' : TvOK c') (hRP : RetPw th.σs th.stack cx.ret) : Tgt p g x n (CE η) mem pairs th := by
  have hi := hS.hF
  have hE := hS.hE
  have hm := hS.hm
  have hi0 := hi.1
  obtain ⟨hi1, -⟩ := use_FInv hu hi0
  have hus2 : accs (cl ρ η.wit 0 0 (.word2 r P)) = some [.two] := pair_accs_cl (wit := η.wit) (Or.inl ⟨r, P, rfl⟩)
  have hcell : cellOf (Ty.loc μ (.word2 r P)) = some (μ, .word2 r P) := by simp [cellOf]
  have hpwf : pwf2 P = true := by
    obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, _, hvr0⟩ :=
      locCell (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus2 hi0 hE hS.tv hm
    simp only [VR] at hvr0; exact hvr0.1
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VR hi0.2.1 hpk
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ := cell_target hcell (Fd_noarr (by rw [hus2]; simp)) hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM μ ∧
      etok (skel ru) = etok (skel (close th.σs (.word2 r P))) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hat' : AtOff c.ty ad.offset (.word2 (.lit (ev ρ r)) P) := by simpa only [cl, clI_zero] using hat
  have hini' : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word2 (.lit (ev ρ r)) P) := fun hq => by
    rcases hμ with rfl | rfl
    · have h2 : IniAt (modeIni .own η.ini η.rini) c ad (.word2 (.lit (ev ρ r)) P) := by
        simpa only [cl, clI_zero] using hini
      exact h2
    · simp only [ModeOK] at hmode
      obtain ⟨f, hf, -⟩ := hmode
      have := hq.2; simp only [CE] at this; rw [this] at hf; cases hf
  obtain ⟨rt0, rt1, w0, w1, Tf, Rv, hev0, hwv0, hev1, hwv1, hfr, hle, hvR⟩ :=
    stp_frame hi hE.2.2 (RLink_of hE.2.1 hE.2.2) hpwf hu hr hj0 hj1 hst hcl hb hxt
  have hval := storeWord2_val (η := η) (r := r) hpwf hi1.1 hst hwv0 hwv1
  have hna : ∀ N e, cl ρ η.wit 0 0 (.word2 r P) ≠ .array (.lit N) e := fun N e h => by simp [cl] at h
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (y, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  refine tgt_pstore hS (TermOwnX2.bumpIf_nb hterm) (A := ad) key (fun s' hs' => ?_) hsto hat' hini' ⟨hvR _ _, by simp [Valid]⟩
    hfr hle he htv' (retPw_eq hRP ((bind_ret hb).trans (use_ret hu)))
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeAtI hm hsto hown hat (IniAt_mono (modeIni_le_ini _ _ _) hini) hna hval hus2 rfl s' hs'
  · have hpub : μ = .pub := by
      rcases hμ with rfl | rfl
      · exact absurd hmode hown
      · rfl
    subst hpub
    simp only [ModeOK] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    exact MemInv_storePubAt hm hsto hown hf hat hini hna hval hus2 rfl s' hs'

theorem tgt_stp {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {rel : Bool} {a v0 v1 tk : At} {e : Expr} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (hP : ProgT p) (ht : th.term = .let_ y (.stp rel a v0 v1 tk) e) (hRP : RetPw th.σs th.stack cx.ret) : Tgt p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.stp rel a v0 v1 tk) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hT := hS.hT
  have hCkL := hS.ck
  rw [ht] at hT hCkL
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
  have htv' := OpT_TvOK hP hop hS.tv
  cases hop with
  | stpGive hp hw hu hr hj0 hj1 _ _ hst hcl _ _ hh _ hb =>
    obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpPtr_tgt hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpLoc_tgt hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inl ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
  | stpKeep hp hw hu hr hj0 hj1 _ _ hst hcl _ _ hh hb =>
    obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpPtr_tgt hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inr ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP
    · subst hteq
      simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact stpLoc_tgt hS ht hp hμ hu hr hj0 hj1 hst hcl (Or.inr ⟨rfl, hh⟩) hb ⟨he, hck⟩ htv' hRP

/-! ## Read-modify-writes: a load, then (maybe) a store; the private holding as for stores -/

/-- The cell side of an RMW store: the target cell, the component type, the value stored and its
resources (no own key). -/
def RmwCell (η : TEnv) (x : AllocLabel) (s s1 : St) (ad : Address) (us : List Acc) (ws : List Word) : Prop :=
  ¬ Priv (CE η) ad.label ∨ LoadCoh (CE η) s s1 ∧ SeenLE (CE η) s1.vs.vRelSt ∧
    ∃ c U Rv, η.sto ad.label = some c ∧ AtOff c.ty ad.offset U ∧
    (Priv (CE η) ad.label → IniAt (CE η).rc c ad U) ∧ (∀ N e, U ≠ .array (.lit N) e) ∧
    EnvValR (CE η) U ws Rv ∧ wc U = some (nWords us) ∧ ws.length = nWords us ∧ Rv (.own x) = 0

/-- The shape of an RMW step's results: the state after a load `s1` (memory and promises kept),
then either nothing more or a store from `s1`; `MemInv` and the frame at the source environment. -/
def RmwOut (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (x : AllocLabel)
    (m : Nat) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot, ThInvRE p (CE η) r.2.2 Tot ∧
    MemInv g (CE η) (stOf r.1 r.2.1 r.2.2) ∧ Tot (.own x) ≤ m ∧
    (((stOf r.1 r.2.1 r.2.2).mem = (stOf mem pairs th).mem ∧
      (stOf r.1 r.2.1 r.2.2).promises = (stOf mem pairs th).promises) ∨
    ∃ s1 s2 pw ad rel us ws, s1.mem = (stOf mem pairs th).mem ∧ s1.promises = (stOf mem pairs th).promises ∧
      s2 ∈ storeUnits g.k g.arch pw ad rel us ws 0 s1 ∧
      (stOf r.1 r.2.1 r.2.2).mem = s2.mem ∧ (stOf r.1 r.2.1 r.2.2).promises = s2.promises ∧
      RmwCell η x (stOf mem pairs th) s1 ad us ws)

theorem tgt_rmw {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP) (hnb : ∀ E1, BumpIf th E1)
    (h : RmwOut p g mem pairs th η x ((Rf + Rs) (.own x))) : Tgt p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨Tot, hT', hm', hle, hk | ⟨s1, s2, pw, ad, rel, us, ws, e1, e2, hs2, e3, e4, hcell⟩⟩ :=
    h r hr hpa
  · exact ⟨CE η, Tot, HP, hT', hm', TermOwnHeldQ.memHeldOn_eqs hS.hH hk.1 hk.2, hS.nie, hS.sto,
      by have := hS.le; omega, TermOwnX2.anchStep_eqs hk.1 hk.2⟩
  by_cases hq : Priv (CE η) ad.label
  · obtain ⟨hlc, hsl, c, U, Rv, hsto, hat, hini, hna, hv, hwU, hlen, hRv⟩ := hcell.resolve_left (fun h => h hq)
    have hq' := hq
    obtain ⟨⟨c0, hc0, hown0⟩, hpfN⟩ := hq'
    have ec : some c0 = some c := hc0.symm.trans hsto
    cases ec
    obtain ⟨-, Rq, R2, H0, hRe, -, -, -, hput⟩ := TermOwnHeldQ.heldStoreAtP hS.hm hS.hH hq hsto
      hown0 (NVP_priv hq) (OwnOKPF_cellP hS.hm.2.1 hsto hown0 hpfN) hat (hini hq) hna hv hwU hlen
    refine ⟨CE η, Tot, R2 + H0, hT', hm', TermOwnHeldQ.memHeldOn_eqs
      (hput g.k g.arch pw rel s1 e1 e2 hlc hlc.2.2 hsl s2 hs2) e3 e4, hS.nie, hS.sto, ?_, TermOwnX2.anchStep_same hnb⟩
    have h2 := congrArg (fun R : Res => R (.own x)) hRe
    have h0 := hS.le
    simp only [Res.add_apply] at h2 h0 hle ⊢
    omega
  · have hpl : PromLt s1 := fun t ht => by rw [e1]; rw [e2] at ht; exact hS.hm.2.2.1 t ht
    have hH1 : MemHeldP (CE η) s1 HP := TermOwnHeldQ.memHeldOn_eqs hS.hH e1 e2
    exact ⟨CE η, Tot, HP, hT', hm', TermOwnHeldQ.memHeldOn_eqs
      (TermOwnHeldQ.memHeldOn_store hH1 (fun l hl e => hq (e ▸ hl)) hpl hs2) e3 e4, hS.nie, hS.sto,
      by have := hS.le; simp only [Res.add_apply] at this hle ⊢; omega, TermOwnX2.anchStep_same hnb⟩

/-- A `pub` reference's target is not private (`ModeOK .pub`: a frontier). -/
theorem pub_npriv {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {t u rt : Ty} {pw : Word} {ad : Address} (hi : FInv ρ η σs K cx env)
    (hpk : cx.peek w = .ok t) (hc : cellOf t = some (.pub, u)) (hna : accs (cl ρ η.wit 0 0 u) ≠ none)
    (hea : evalAt env w = some (rt, [pw])) (haddr : addrOf pw = some ad) : ¬ Priv (CE η) ad.label := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hi.2.1 hpk
  obtain ⟨ad', c, hws, -, -, hmode, -⟩ := cell_target hc (Fd_noarr hna) hv
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨-, rfl⟩ := hea'
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have e : ad = ad' := by simp only [addrOf, hws, Option.some.injEq] at haddr; exact haddr.symm
  subst e
  simp only [ModeOK] at hmode
  obtain ⟨f, hf, -⟩ := hmode
  intro hq
  have h2 := hq.2
  simp only [CE] at h2
  rw [h2] at hf
  cases hf

theorem loadCoh_bump {E : TEnv} {s s1 : St} (X : Ts) (h : LoadCoh E s s1) : LoadCoh E s (bumpRel s1 X) :=
  ⟨OwnOKSF_congr h.1 (fun _ _ _ _ _ => rfl), h.2.1, h.2.2⟩

-- copied from TermStep.fetchCellC_core; holding/credit lines deleted
theorem fetchCell_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {tw tv : Ty} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .let_ y (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok tw) (hcw : cellOf tw = some (.pub, .int))
    (hu : cx.use v = .ok (tv, c₁)) (hsub : SubS c₁ tv .int) (hb : c₁.bind y .int = .ok c')
    (he : TypedK p η c' e) (htv' : TvOK c')
    (hFC : FetchIntCell g mem pairs th η acq rel a)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (hRP : RetPw th.σs th.stack cx.ret) : RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hRL := RLink_of hE.2.1 hE.2.2
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have hvi := VR_sub hi1.1.1 hsub _ _ hvv
  simp only [VR] at hvi
  obtain ⟨dd, hdd⟩ := hvi
  obtain ⟨nw, rfl, hnw⟩ := map_singleton hdd
  obtain ⟨ad, pw, rt, hea, haddr, hrt, hne, hcell⟩ := hFC
  have hnp := pub_npriv hi.1 hpk hcw (by simp [cl, accs]) hea haddr
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (y, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨hm1, ⟨n, hn⟩, hst⟩ := hcell s1 [rd] hl1 hp1
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
  obtain ⟨k, hk⟩ := FetchOp.apply_num o n dd
  rw [hnw] at hs2
  have hkv : (cst (o.kind.apply rd.val (.num dd))).val = .num k := by
    simp [cst, Promises.TVal.mk0, hn, hk]
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  have hm1b := MemInv_bumpRel (MemInv_lockR g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
  have hfr := bindR hb hi1 hRL (show VRR ρ η .int (shp .int) [rd] .zero by simp [VRR, hn]) (Lay_int rd rfl)
  have hmi := MemInv_same (MemInv_lockS g.arch
    (MemInv_setRel (hst _ hm1b _ ⟨k, hkv⟩ s2 hs2) (MemInv_lockR g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame
  subst hrd
  refine ⟨Rr + .zero + Rs, ⟨ρ, η, c', Rr + .zero, Rs, rfl, hE, he, htv', (by rw [hrt]; exact hfr), rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, hmi, ?_,
    Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
      hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inl hnp⟩⟩
  have h1 := Res.le_def.1 hle (.own xk)
  simp only [Res.add_apply, Res.zero_apply] at h1 ⊢
  omega

/-- An own or `pub` reference's target: the cell, and `rc`-initialisation when private. -/
theorem cellTargetP {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} {w : At} {t u rt : Ty} {μ : Mode} {pw : Word} {ad : Address} (hi : FInv ρ η σs K cx env)
    (hpk : cx.peek w = .ok t) (hc : cellOf t = some (μ, u)) (hμ : μ = .own ∨ μ = .pub)
    (hna : accs (cl ρ η.wit 0 0 u) ≠ none)
    (hea : evalAt env w = some (rt, [pw])) (haddr : addrOf pw = some ad) :
    ∃ c, η.sto ad.label = some c ∧ AtOff c.ty ad.offset (cl ρ η.wit 0 0 u) ∧
      (Priv (CE η) ad.label → IniAt (CE η).rc c ad (cl ρ η.wit 0 0 u)) := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hi.2.1 hpk
  obtain ⟨ad', c, hws, hsto, hat, hmode, hini⟩ := cell_target hc (Fd_noarr hna) hv
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨-, rfl⟩ := hea'
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hws
  have e : ad = ad' := by simp only [addrOf, hws, Option.some.injEq] at haddr; exact haddr.symm
  subst e
  refine ⟨c, hsto, hat, fun hq => ?_⟩
  rcases hμ with rfl | rfl
  · exact hini
  · simp only [ModeOK] at hmode
    obtain ⟨f, hf, -⟩ := hmode
    have h2 := hq.2
    simp only [CE] at h2
    rw [h2] at hf
    cases hf

theorem wrW_own (P : Proto) (n : Nat) (v : WeakMem.Val) (l : AllocLabel) : (wr P n v + wdW P n) (.own l) = 0 := by
  unfold wr wdW
  split <;> split <;> simp [Res.add_apply, Res.one]

-- copied from TermStep.fetchC_core; holding/credit/mint lines deleted
theorem fetchW_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {c : Cell} {n : Nat} {P : Proto} {pw nw : Word} {rt rv : Ty} {dd : Nat}
    {Rf Rs : Res} {xk : AllocLabel} {Q : List Word → Prop} {SOK : Word → Prop}
    (hterm : th.term = .let_ y (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
      MemInv g (CE η) s1 ∧ Q ws ∧ ∀ s1', MemInv g (CE η) s1' → ∀ w, SOK w →
        ∀ s2, s2 ∈ storeUnits g.k g.arch pw ad rel [.one] [w] 0 s1' → MemInv g (CE η) s2)
    (hsto : η.sto ad.label = some c) (hat : AtOff c.ty ad.offset (.word (.lit n) P))
    (hini : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word (.lit n) P)) (hpwf : pwf P = true)
    (hg : P.ghost = false)
    (hpost : ∀ rd, Q [rd] → SOK (cst (o.kind.apply rd.val (.num dd))) ∧
      (∃ k, o.kind.apply rd.val (.num dd) = .num k ∧ InP P k) ∧
      ∃ ρ' cx' Rok, TypedK p η cx' e ∧ TvOK cx' ∧ RetPw th.σs th.stack cx'.ret ∧
        FInvR ρ' η th.σs (ResumeR p th.stack Rs) cx' ((y, fetchRtTy rt, [rd]) :: th.env) Rok ∧
        Rok (.own xk) ≤ Rf (.own xk))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (y, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨hm1, hq, hst⟩ := hcell s1 [rd] hl1 hp1
  obtain ⟨hsok, ⟨k, happ, hink⟩, ρ', cx', Rok, he', htv', hRPx, hi', hres⟩ := hpost rd hq
  rw [hnw] at hs2
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  have hm1b := MemInv_bumpRel (MemInv_lockR g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
  have hlc := loadCoh_bump (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
    (LoadCoh_load hl1 hp1 hm.2.1 ⟨c, hsto⟩)
  subst hrd
  refine ⟨Rok + Rs, ⟨ρ', η, cx', Rok, Rs, rfl, hE, he', htv', hi', rfl, hRPx⟩,
    MemInv_same (MemInv_lockS g.arch (MemInv_setRel (hst _ hm1b _ hsok s2 hs2) (MemInv_lockR g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame, ?_,
    Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
      hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inr ⟨hlc, hm1b.2.2.2.2.1, c, _, _, hsto, hat, hini,
        (fun N e h => by cases h),
        ⟨VRR_word_of hpwf ⟨k, by simp [cst, Promises.TVal.mk0, happ], hink⟩, by simp [Valid]⟩,
        by simp [wc, accs, nWords, Acc.size, hg], rfl, wrW_own _ _ _ _⟩⟩⟩
  simp only [Res.add_apply]
  omega

-- copied from TermStep.fetchWordC; holding/credit/mint lines deleted
theorem fetchWord_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {tw : Ty} {μ : Mode} {r j : Idx} {P : Proto} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .let_ y (.fetch o acq rel a v) e)
    (hpk : cx.peek a = .ok tw) (hcw : cellOf tw = some (μ, .word r P)) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hpwf : pwf P = true) (hFC : FetchCell g mem pairs th ρ η acq rel a r P)
    (ho : o = .add) (hj : IntIdx cx v j)
    (hcase : (P.epoch = true ∧ EqI cx j (.lit 1) ∧ cx.bind y (fetchEpochTy r P) = .ok c') ∨
      (∃ d, P.epoch = false ∧ EqI cx j (.lit d) ∧ fetchOK P d = true ∧ cx.bind y .int = .ok c'))
    (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  subst ho
  have hRL := RLink_of hE.2.1 hE.2.2
  obtain ⟨ad, pw, rt, r', hea, haddr, hwo, hne, hcell⟩ := hFC
  obtain ⟨c, hsto, hat, hini⟩ := cellTargetP hi.1 hpk hcw hμ (by simp [cl, accs, hg]) hea haddr
  have hcl : cl ρ η.wit 0 0 (.word r P) = .word (.lit (ev ρ r)) P := by simp [cl, clI_zero]
  rw [hcl] at hat hini
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.1.2.1 htvk hjo
  rcases hcase with ⟨hep, heq, hb⟩ | ⟨d, hep, heq, hok, hb⟩
  · have hj1 := heq ρ hi.1.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    have hrt : fetchRtTy rt = fetchEpochTy r' P := by simp [fetchRtTy, hwo, hep]
    refine fetchW_out hterm hea haddr hev hnwv hcell hsto hat hini hpwf hg (fun rd hq => ?_) hE hm
    simp only [VR] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    have happ : (FetchOp.add).kind.apply rd.val (.num 1) = .num (n + 1) := by
      simp [hn, FetchOp.kind, WeakMem.RmwKind.apply]
    refine ⟨wordVal hpwf (m := n + 1) (by simp [cst, Promises.TVal.mk0, happ]) (InP_epoch hpwf hep (n + 1)),
      ⟨n + 1, happ, InP_epoch hpwf hep (n + 1)⟩, ρ, c', Rf + .one (.ep (ev ρ r) (n + 1)), he, htv', (by rw [bind_ret hb]; exact hRP), ?_,
      by simp [Res.add_apply, Res.one]⟩
    rw [hrt]
    exact bindR hb hi hRL (VRR_fetchEpoch hn) (Lay_fetchEpoch _ r r' P rd)
  · have hjd := heq ρ hi.1.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    have hrt : fetchRtTy rt = .int := by simp [fetchRtTy, hwo, hep]
    refine fetchW_out hterm hea haddr hev hnwv hcell hsto hat hini hpwf hg (fun rd hq => ?_) hE hm
    simp only [VR] at hq
    obtain ⟨n, hn, hin⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    have happ : (FetchOp.add).kind.apply rd.val (.num d) = .num (n + d) := by
      simp [hn, FetchOp.kind, WeakMem.RmwKind.apply]
    refine ⟨wordVal hpwf (m := n + d) (by simp [cst, Promises.TVal.mk0, happ]) (InP_fetch hok hin),
      ⟨n + d, happ, InP_fetch hok hin⟩, ρ, c', Rf + .zero, he, htv', (by rw [bind_ret hb]; exact hRP), ?_, by simp [Res.add_apply]⟩
    rw [hrt]
    exact bindR hb hi hRL (show VRR ρ η .int (shp .int) [rd] .zero by simp [VRR, hn]) (Lay_int rd rfl)

-- copied from TermStep.tstepMC_fetch/tstepMC_fetchLoc, the word rules
theorem fetchRef_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c' : Cx} {ρ : Nat → Nat} {η : TEnv} {y : String} {acq rel : Bool} {a v : At} {e : Expr}
    {t : Ty} {μ : Mode} {r j : Idx} {P : Proto} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .let_ y (.fetch .add acq rel a v) e)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P)) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false) (hpwf : pwf P = true) (hj : IntIdx cx v j)
    (hcase : (P.epoch = true ∧ EqI cx j (.lit 1) ∧ cx.bind y (fetchEpochTy r P) = .ok c') ∨
      (∃ d, P.epoch = false ∧ EqI cx j (.lit d) ∧ fetchOK P d = true ∧ cx.bind y .int = .ok c'))
    (he : TypedK p η c' e) (htv' : TvOK c')
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  rcases ht with rfl | rfl
  · obtain ⟨lab, pw, μ', r', hea, hpw, hne, hcell⟩ :=
      wordCellF (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hμ hg hi.1 hE htv hm
    exact fetchWord_out hterm hp rfl hμ hg hpwf ⟨⟨lab, 0⟩, pw, _, r', hea, by simp [addrOf, hpw], rfl, hne, hcell⟩
      rfl hj hcase he htv' hi hE hm hRP
  · have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, -⟩ :=
      locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi.1 hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    exact fetchWord_out hterm hp rfl hμ hg hpwf ⟨ad, pw, _, r', hea, haddr, rfl, hne,
        fun s1 ws hl hp => ⟨(hld s1 ws hl hp).2.2, (hld s1 ws hl hp).1,
          fun s1' hm1' w hw s2 hs2 => hsto s1' [w] hm1' hw rfl s2 hs2⟩⟩
      rfl hj hcase he htv' hi hE hm hRP

-- copied from TermStep.tstepMC_fetch/tstepMC_fetchLoc; holding/credit lines deleted
theorem tgt_fetch {p : Prog} (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {y : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .let_ y (.fetch o acq rel a v) e) (hRP : RetPw th.σs th.stack cx.ret) : Tgt p g x n (CE η) mem pairs th := by
  have hsc' : OpScope cx (.fetch o acq rel a v) := opScope_of (by rw [← ht]; exact hS.sc)
    (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hT := hS.hT
  have hCkL := hS.ck
  rw [ht] at hT hCkL
  cases hT with
  | let_ hop he =>
  rename_i c'
  obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
  have htv' := OpT_TvOK hP hop htv
  refine tgt_rmw hS (TermOwnX2.bumpIf_nb ht) ?_
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp
    · subst hteq
      rcases hc with hc | ⟨r, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨lab, pw, ru, hea, hpw, hnwr, hne, hcell⟩ :=
          pubIntCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp hi.1 hE htv hm
        have hrt : fetchRtTy (.ptr .pub ru) = .int := by
          cases ru <;> simp [fetchRtTy, wordOf]
          exact (hnwr _ _ rfl).elim
        exact fetchCell_out ht hp rfl hu hsub hb ⟨he, hck⟩ htv'
          ⟨⟨lab, 0⟩, pw, _, hea, by simp [addrOf, hpw], hrt, hne, hcell⟩ hi hE hRP
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        rcases hμ with h | h <;> cases h
    · subst hteq
      rcases hc with hc | ⟨r, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
        obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, -⟩ :=
          locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hp (Or.inr rfl)
            (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi.1 hE htv hm
        have hrt : fetchRtTy (.loc μr ru) = .int := by
          cases ru <;> simp [fetchRtTy, wordOf]
          simp [skel, etok, close, substTs] at hsku
        refine fetchCell_out ht hp rfl hu hsub hb ⟨he, hck⟩ htv'
          ⟨ad, pw, _, hea, haddr, hrt, hne, fun s1 ws hl hp => ?_⟩ hi hE hRP
        obtain ⟨hvr, -, hm1⟩ := hld s1 ws hl hp
        exact ⟨hm1, by simpa [VR] using hvr, fun s1' hm1' w ⟨m, hw⟩ s2 hs2 =>
          hsto s1' [w] hm1' (intVal (ρ := ρ) hw) rfl s2 hs2⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, -⟩ := hc
        rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp <;> subst hteq <;>
    · cases u <;> simp [wordOf] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rename_i r P
      have hpwf := wordRef_pwf hp (by first | exact .inl rfl | exact .inr rfl) hμ hi.1 hE htv hm
      have hg : P.ghost = false := by
        have := pwf_epochOK hpwf hep
        unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
        exact this.1.2
      exact fetchRef_out ht hp (by first | exact .inl rfl | exact .inr rfl) hμ hg hpwf hj (.inl ⟨hep, heq, hb⟩)
        ⟨he, hck⟩ htv' hi hE htv hm hS.rp
  | fetchShare hp hw hep hj heq hok hb =>
    obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc' _ hp <;> subst hteq <;>
    · cases u <;> simp [wordOf] at hw
      obtain ⟨rfl, rfl⟩ := hw
      rename_i r P
      have hpwf := wordRef_pwf hp (by first | exact .inl rfl | exact .inr rfl) hμ hi.1 hE htv hm
      have hg : P.ghost = false := by
        have hok' := hok
        unfold fetchOK at hok'; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok'
        exact hok'.1.1.1.1
      exact fetchRef_out ht hp (by first | exact .inl rfl | exact .inr rfl) hμ hg hpwf hj
        (.inr ⟨_, hep, heq, hok, hb⟩) ⟨he, hck⟩ htv' hi hE htv hm hS.rp

/-! ## `cas` -/

/-- `StepScope` from `ScopeD` at a non-`let` term. -/
theorem stepScope_of {σs : List Ty} {cx : Cx} {t : Expr} (h : ScopeD σs cx t)
    (hn : ∀ x op e, t ≠ .let_ x op e) : StepScope cx t := by
  rcases h with h | ⟨-, hc⟩
  · exact h
  · obtain ⟨x, op, e, rfl, -⟩ := capT_inv hc
    exact absurd rfl (hn x op e)

-- copied from TermStep.casWordC_core; holding/credit/mint lines deleted
theorem casW_core {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {P : Proto} {n : Nat} {ad : Address} {c : Cell} {pw ew nw : Word} {rw rte rtv : Ty}
    {Rf Rs Rok : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hea : evalAt th.env w = some (rw, [pw])) (haddr : addrOf pw = some ad)
    (hee : evalAt th.env e = some (rte, [ew])) (hev : evalAt th.env v = some (rtv, [nw]))
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
        MemInv g (CE η) s1 ∧ ∀ s1', MemInv g (CE η) s1' →
          ∀ s2, s2 ∈ storeUnits g.k g.arch pw ad rel [.one] [nw] 0 s1' → MemInv g (CE η) s2)
    (hsto : η.sto ad.label = some c) (hat : AtOff c.ty ad.offset (.word (.lit n) P))
    (hini : Priv (CE η) ad.label → IniAt (CE η).rc c ad (.word (.lit n) P)) (hg : P.ghost = false)
    (hpwf : pwf P = true) (hnin : ∃ k, nw.val = .num k ∧ InP P k)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvR ρ η th.σs (ResumeR p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, haddr]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  have hp1 := hpS (fun t ht m hm => hpr t ht m hm)
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 hp1
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb]
    exact ⟨Rf + Rs, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hfail, htv, hi, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, MemInv_same (MemInv_lockS g.arch hm1) hsame,
      Nat.le_refl _, Or.inl ⟨hsame.1.trans ((lockS_memP _ _).1.trans f1),
        hsame.2.2.2.1.trans ((lockS_memP _ _).2.trans f2)⟩⟩
  · have hb : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb, ite_true]
    have hm1b := MemInv_bumpRel (MemInv_lockR g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
    have hlc := loadCoh_bump (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
      (LoadCoh_load hl1 hp1 hm.2.1 ⟨c, hsto⟩)
    obtain ⟨k, hk, hink⟩ := hnin
    refine ⟨Rok + Rs, ⟨ρ, η, cok, Rok, Rs, rfl, hE, hok, htvok, hiok, rfl, hRPo⟩,
      MemInv_same (MemInv_lockS g.arch (MemInv_setRel (hst2 _ hm1b s2 hs2) (MemInv_lockR g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame, ?_,
      Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
        hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inr ⟨hlc, hm1b.2.2.2.2.1, c, _, _, hsto, hat, hini,
          (fun N e h => by cases h), ⟨VRR_word_of hpwf ⟨k, hk, hink⟩, by simp [Valid]⟩,
          by simp [wc, accs, nWords, Acc.size, hg], rfl, wrW_own _ _ _ _⟩⟩⟩
    simp only [Res.add_apply]
    omega

-- copied from TermStep.casWordC_mid; cellTargetP for wordTarget
theorem casW_mid {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {tw : Ty} {μ : Mode} {r i j k' : Idx} {P : Proto} {c₂ : Nat} {Rf Rs Rok : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (μ, .word r P)) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false) (hpwf : pwf P = true)
    (hie : IntIdx cx e i) (hj : IntIdx cx v j) (hst : InState cx P j c₂ k')
    (hcellL : ∀ nw : Word, nw.val = .num (ev ρ j) → CasCell g mem pairs th η acq rel w nw)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvR ρ η th.σs (ResumeR p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  obtain ⟨te, hte, hio⟩ := hie
  obtain ⟨rte, ew, hee, hewv, -⟩ := atom_num hi.1.2.1 hte hio
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_num hi.1.2.1 htvk hjo
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := hcellL nw hnwv
  obtain ⟨c, hsto, hat, hini⟩ := cellTargetP hi.1 hpk hcw hμ (by simp [cl, accs, hg]) hea haddr
  have hcl : cl ρ η.wit 0 0 (.word r P) = .word (.lit (ev ρ r)) P := by simp [cl, clI_zero]
  rw [hcl] at hat hini
  exact casW_core hterm hea haddr hee hev hcell hsto hat hini hg hpwf ⟨_, hnwv, InP_of_st hi.1.1 hst⟩
    hok htvok hiok hres hfail hi hE htv hm hRP hRPo

-- copied from TermStep.casWordC_typed; holding/credit/mint lines deleted
theorem casW_typed {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {tw : Ty} {μ : Mode} {r : Idx} {P : Proto} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (μ, .word r P)) (hwo : wordOf tw = some (r, P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false) (hpwf : pwf P = true)
    (hL : ∀ {j k' : Idx} {c₂ : Nat}, InState cx P j c₂ k' → ∀ nw : Word, nw.val = .num (ev ρ j) →
      CasCell g mem pairs th η acq rel w nw)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hRL := RLink_of hE.2.1 hE.2.2
  have hT0 := hT
  rw [hterm] at hT0 hCk
  cases TermA4.CkW_inv_cas hCk with
  | casCell hp hnw => exfalso; rw [hpk] at hp; cases hp; rw [hwo] at hnw; cases hnw
  | casShare hp hw _ hie hj hsti hcl hst hcl' hh _ hh' hlend hok hfail =>
    rw [hpk] at hp; cases hp
    rw [hwo] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have htv2 := LendCx_TvOK hlend htv
    cases hlend with
    | none hsm hb =>
      have hiok := bindR hb hi hRL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
      exact casW_mid hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv2 hiok
        (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    | up hsm _ hb =>
      have hiok := bindR (rt := .unit) (ws := []) (R := .one (.sh (ev ρ r))) hb hi hRL rfl (Lay_etok_unit rfl)
      exact casW_mid hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv2 hiok
        (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    | down _ _ _ _ hu hb =>
      obtain ⟨-, -, R, Rr, -, -, -, -, hi1, hle⟩ := useR hu hi hE.2.2
      have hiok := bindR hb hi1 hRL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
      exact casW_mid hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv2 hiok
        (by have := Res.le_def.1 hle (.own xk); simp only [Res.add_apply, Res.zero_apply] at this ⊢; omega)
        hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | casTake hp hw hgh hie hj hsti hcl hst hcl' hh hstp hh' hl1 hl2 hacq hb hok hfail =>
    rw [hpk] at hp; cases hp
    rw [hwo] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hiok := bindR (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    have htv' := (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1
    split at hok
    · exact casW_mid hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv' hiok
        (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    · exact casW_mid hterm hpk hcw hμ hg hpwf hie hj hst (hL hst) hok.tk htv' hiok
        (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | casEpoch hp hw hep hacq hie hj hsti hst hstep hb hok hfail =>
    rw [hpk] at hp; cases hp
    rw [hwo] at hw; simp only [Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hiok := bindR (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    exact casW_mid hterm hpk hcw hμ hg hpwf hie hj hst (hL hst)
      hok.tk (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok
      (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))

-- copied from TermStep.casCellC_core; holding/credit lines deleted, pub_npriv
theorem casC_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c₂ : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {tw : Ty} {u te tv : Ty} {Rf Rs : Res} {xk : AllocLabel}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok tw) (hcw : cellOf tw = some (.pub, u)) (hone : u.rawWords = some 1)
    (hpe : cx.peek e = .ok te) (hu : cx.use v = .ok (tv, c₁))
    (hsube : SubS c₁ te u) (hsubv : SubS c₁ tv u) (hb : c₁.bind t .unit = .ok c₂)
    (hok : TypedK p η c₂ ok) (hfail : TypedK p η c₁ fail)
    (hcellL : ∀ nw, EnvVal (CE η) (cl ρ η.wit 0 0 u) [nw] → CasCell g mem pairs th η acq rel w nw)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) : RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hRL := RLink_of hE.2.1 hE.2.2
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) hcw
  have hus : accs (cl ρ η.wit 0 0 u) = some [.one] := accs_cl_one hone
  obtain ⟨rv, wsv, Rv, Rr, hev, hvv, hlv, hvrv, hi1, hle⟩ := useR hu hi hE.2.2
  have htv1 := (use_TvOK hu htv).1
  obtain ⟨hval, hlen⟩ := ownStoreVal (ru := cl ρ η.wit 0 0 u) hE.2.1 hi.1.2.2.2.1 hi.1.2.2.2.2.1 hi1.1.1
    hsubv ho htb hvv hlv rfl hus
  obtain ⟨nw, rfl⟩ := len_one hlen
  obtain ⟨rte, wse, hee, hve, hle'⟩ := peek_VR hi.1.2.1 hpe
  obtain ⟨hve1, hlene⟩ := ownStoreVal (ru := cl ρ η.wit 0 0 u) hE.2.1 hi.1.2.2.2.1 hi.1.2.2.2.2.1 hi1.1.1
    hsube ho htb hve hle' rfl hus
  obtain ⟨ew, rfl⟩ := len_one hlene
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := hcellL nw hval
  have hnp := pub_npriv hi.1 hpk hcw (by rw [hus]; simp) hea haddr
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, haddr]; rfl
  have h1 := Res.le_def.1 hle (.own xk)
  simp only [Res.add_apply] at h1
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.one] 0 _ (s1, [rd]) hl1
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb']
    exact ⟨Rr + Rs, ⟨ρ, η, c₁, Rr, Rs, rfl, hE, hfail, htv1, hi1, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, MemInv_same (MemInv_lockS g.arch hm1) hsame,
      by simp only [Res.add_apply]; omega, Or.inl ⟨hsame.1.trans ((lockS_memP _ _).1.trans f1),
        hsame.2.2.2.1.trans ((lockS_memP _ _).2.trans f2)⟩⟩
  · have hb' : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb', ite_true]
    have hm1b := MemInv_bumpRel (MemInv_lockR g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
    have hfr := bindR hb hi1 hRL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    exact ⟨Rr + .zero + Rs, ⟨ρ, η, c₂, Rr + .zero, Rs, rfl, hE, hok,
      (bind_TvOK hb htv1 (by simp [tb]) (by simp [mg])).1, (by exact hfr), rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩,
      MemInv_same (MemInv_lockS g.arch (MemInv_setRel (hst2 _ hm1b s2 hs2) (MemInv_lockR g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame,
      by simp only [Res.add_apply, Res.zero_apply]; omega,
      Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, ad, rel, [.one], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
        hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inl hnp⟩⟩

-- copied from TermStep.tstepMCF_stepK/tstepMC_casCell(Loc)/tstepMC_casWord(Loc)
theorem tgt_cas {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .cas acq rel w e v t ok fail) (hRP : RetPw th.σs th.stack cx.ret) : Tgt p g x n (CE η) mem pairs th := by
  have hsc' : StepScope cx (.cas acq rel w e v t ok fail) :=
    stepScope_of (by rw [← ht]; exact hS.sc) (fun _ _ _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hT := hS.hT
  have hCk0 := hS.ck
  refine tgt_rmw hS (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [ht] at h; cases h) ?_
  have hT0 := hT
  rw [ht] at hT0 hCk0
  have hcasW : ∀ {μ r P}, (cx.peek w = .ok (.ptr μ (.word r P)) ∨ cx.peek w = .ok (.loc μ (.word r P))) →
      (μ = .own ∨ μ = .pub) → P.ghost = false → RmwOut p g mem pairs th η x ((Rf + Rs) (.own x)) := by
    intro μ r P hpk hμ hg
    rcases hpk with hpk | hpk
    · exact casW_typed ht hpk rfl rfl hμ hg (wordRef_pwf hpk (.inl rfl) hμ hi.1 hE htv hm)
        (fun hst nw hnwv => by
          obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := casWordCell (acq := acq) (rel := rel) (g := g)
            (mem := mem) (pairs := pairs) hpk hμ hg hst hnwv hi.1 hE htv hm
          exact ⟨⟨lab, 0⟩, pw, rw, hea, by simp [addrOf, hpw], hne, hcell⟩) hT hS.ck hi hE htv hm hRP
    · exact casW_typed ht hpk rfl rfl hμ hg (wordRef_pwf hpk (.inr rfl) hμ hi.1 hE htv hm)
        (fun hst _ hnwv => wordLocCell (acq := acq) (rel := rel) (g := g)
          (mem := mem) (pairs := pairs) hpk hμ hg hst hnwv hi.1 hE htv hm) hT hS.ck hi hE htv hm hRP
  cases TermA4.CkW_inv_cas hCk0 with
  | casCell hpk hnw0 hc hone haff hpe hu hsube hsubv _ hb hok hfail =>
    rcases hsc' _ hpk with ⟨μ, r, P, hteq | hteq, hμ⟩ | ⟨u, rfl | rfl, hnw⟩
    · subst hteq; simp [wordOf] at hnw0
    · subst hteq; simp [wordOf] at hnw0
    · rcases hc with hc | ⟨_, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
        subst hc
        have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv
          (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
        exact casC_out ht hpk rfl hone hpe hu hsube hsubv hb hok.tk hfail.tk
          (plainCellPtr hpk hone ho hi.1 hE htv hm) hi hE htv hRP
      · simp [cellOf] at hc
    · rcases hc with hc | ⟨_, hc, -⟩
      · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
        subst hc
        have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv
          (peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
        refine casC_out ht hpk rfl hone hpe hu hsube hsubv hb hok.tk hfail.tk (fun nw hval => ?_) hi hE htv hRP
        obtain ⟨ad, pw, μr, ru, hea, haddr, -, -, -, hne, hld, hsto, -⟩ :=
          locCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk (.inr rfl) ho
            (accs_cl_one hone) hi.1 hE htv hm
        exact ⟨ad, pw, _, hea, haddr, hne, fun s1 ws hl hp => ⟨(hld s1 ws hl hp).2.2,
          fun s1' hm1 s2 hs2 => hsto s1' [nw] hm1 hval rfl s2 hs2⟩⟩
      · simp [cellOf] at hc
  | casShare hpk hw | casTake hpk hw | casEpoch hpk hw =>
    rcases hsc' _ hpk with ⟨μ, r, P, hteq, hμ⟩ | ⟨u, hteq, hnw⟩
    · cases hg : P.ghost
      · rcases hteq with rfl | rfl
        · exact hcasW (.inl hpk) hμ hg
        · exact hcasW (.inr hpk) hμ hg
      · exact (cas_ghost_absurd (by rw [← ht]; exact hT) hpk hteq
          (wordRef_pwf hpk hteq hμ hi.1 hE htv hm) hg).elim
    · rw [hnw] at hw; cases hw

/-! ## `casp` -/

/-- A pair reference's value (from the load lemmas), for the pair's protocol well-formedness. -/
theorem pairRef_vr {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {K : TEnv → List Word → Prop} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {w : At} {t u : Ty} {μ : Mode}
    (hpk : cx.peek w = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hi : FInv ρ η th.σs K cx th.env) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) : ∃ R ws, VR ρ η u R ws := by
  have ho : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  rcases ht with rfl | rfl
  · rcases hμ with rfl | rfl
    · obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_view hi hpk htv ho
      have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
      obtain ⟨-, -, -, -, _, hvr, -⟩ := ownLoad (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
        hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
        (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VR η hcty).1) hna hsku
        (peek_cell_lyt hi.2.1 hpk hea rfl rfl).2 hsig
        (by rw [(Fd_lay hcty).2.2.1]; exact pub_accs hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl)
      exact ⟨_, _, hvr⟩
    · obtain ⟨_, _, _, _, -, -, -, -, -, -, _, hvr⟩ :=
        loadPub_core (p := p) (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
      exact ⟨_, _, hvr⟩
  · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, _, hvr⟩ :=
      locCell (acq := false) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ ho
        (pair_accs_cl hu) hi hE htv hm
    exact ⟨_, _, hvr⟩

-- copied from TermStep.caspC_coreA; holding/credit/mint lines deleted
theorem caspA_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {A : Address} {c : Cell} {U : Ty}
    {pw x0 x1 n0 n1 : Word} {rw rt0 rt1 rtv0 rtv1 : Ty} {Rf Rs Rok Rv : Res} {xk : AllocLabel}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hea : evalAt th.env w = some (rw, [pw])) (haddr : addrOf pw = some A)
    (hee0 : evalAt th.env e0 = some (rt0, [x0])) (hee1 : evalAt th.env e1 = some (rt1, [x1]))
    (hev0 : evalAt th.env v0 = some (rtv0, [n0])) (hev1 : evalAt th.env v1 = some (rtv1, [n1]))
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw A acq [.two] 0 (stOf mem pairs th) → PromAbove s1 →
        MemInv g (CE η) s1 ∧ ∀ s1', MemInv g (CE η) s1' →
          ∀ s2, s2 ∈ storeUnits g.k g.arch pw A rel [.two] [n0, n1] 0 s1' → MemInv g (CE η) s2)
    (hsto : η.sto A.label = some c) (hat : AtOff c.ty A.offset U)
    (hini : Priv (CE η) A.label → IniAt (CE η).rc c A U)
    (hwU : wc U = some (nWords [.two])) (hna : ∀ N e, U ≠ .array (.lit N) e)
    (hv : EnvValR (CE η) U [n0, n1] Rv) (hRv : Rv (.own xk) = 0)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvR ρ η th.σs (ResumeR p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  have hpd : ∀ t, t ∈ th.promises → t ∉ pairs := MemInv_nopair hm
  have key : tstep g mem pairs th =
      (Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw n0 n1) 1 2 A x0.val x1.val
          (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
        (mem', pairs', withS (if (th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1, th'.regs 2]⟩) := by
    simp only [tstep, hterm, hea, hee0, hee1, hev0, hev1, haddr]; rfl
  intro r hr hpr0
  have hpr := hpr0
  rw [key, List.mem_map] at hr
  obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd0, rd1, hl1, hr0, hr1, hcase⟩ := stepRmwPair_split (k := g.k) (s := stOf mem pairs th) hin
  obtain ⟨f1, -, f2, -⟩ := loadUnits_frame [.two] 0 _ (s1, [rd0, rd1]) hl1
  rcases hcase with ⟨hne', hsame⟩ | ⟨h0, h1, s2, hs2, hsame⟩ | ⟨h0, h1, tw', pm, htw', hpm, hpl, hsame⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = false := by
      rw [hr0, hr1]
      cases e0 : (rd0.val == x0.val) <;> cases e1 : (rd1.val == x1.val) <;> simp_all
    simp only [hb]
    have hp1 : PromAbove s1 := PromAbove_lockS (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1i, -⟩ := hcell s1 [rd0, rd1] hl1 hp1
    exact ⟨Rf + Rs, ⟨ρ, η, cx, Rf, Rs, rfl, hE, hfail, htv, hi, rfl, retPw_eq hRP (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, MemInv_same (MemInv_lockS g.arch hm1i) hsame,
      Nat.le_refl _, Or.inl ⟨hsame.1.trans ((lockS_memP _ _).1.trans f1),
        hsame.2.2.2.1.trans ((lockS_memP _ _).2.trans f2)⟩⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = true := by
      rw [hr0, hr1]; simp [h0, h1]
    simp only [hb, ite_true]
    have hp2 : PromAbove s2 :=
      PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
    have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
    obtain ⟨hm1i, hst2⟩ := hcell s1 [rd0, rd1] hl1 hp1
    have hm1b := MemInv_bumpRel (MemInv_lockR g.arch (stOf mem pairs th) hm1i) (max (max (Promises.pairTop (stOf mem pairs th).pairs rd0.rts) rd0.view)
      (max (Promises.pairTop (stOf mem pairs th).pairs rd1.rts) rd1.view))
    have hlc := loadCoh_bump (max (max (Promises.pairTop (stOf mem pairs th).pairs rd0.rts) rd0.view)
      (max (Promises.pairTop (stOf mem pairs th).pairs rd1.rts) rd1.view)) (LoadCoh_load hl1 hp1 hm.2.1 ⟨c, hsto⟩)
    refine ⟨Rok + Rs, ⟨ρ, η, cok, Rok, Rs, rfl, hE, hok, htvok, hiok, rfl, hRPo⟩,
      MemInv_same (MemInv_lockS g.arch (MemInv_setRel (hst2 _ hm1b s2 hs2) (MemInv_lockR g.arch (stOf mem pairs th) hm1i).2.2.2.2.1)) hsame, ?_,
      Or.inr ⟨bumpRel (lockR g.arch (stOf mem pairs th) s1) _, s2, pw, A, rel, [.two], _, f1, f2, hs2, hsame.1.trans (lockS_memP _ _).1,
        hsame.2.2.2.1.trans (lockS_memP _ _).2, Or.inr ⟨hlc, hm1b.2.2.2.2.1, c, U, Rv, hsto, hat, hini, hna, hv,
          hwU, rfl, hRv⟩⟩⟩
    simp only [Res.add_apply]
    omega
  · exfalso
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hmc, _⟩ := stepRmwPair_memR hin (by decide) hpd
    have hp3 : th'.promises = th.promises := by
      rcases hmc with ⟨_, _, h⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h
    have hs1p : s1.promises = th.promises :=
      (TermMem.loadUnits_frame [.two] 0 (stOf mem pairs th) (s1, [rd0, rd1]) hl1).2.2.1
    have e := hsame.2.2.2.1
    rw [lockS_prom] at e
    simp only [pairFulS] at e
    rw [hp3, hs1p] at e
    rw [hs1p] at htw'
    have hl := congrArg List.length e
    have h1 := List.length_erase_of_mem htw'
    have h2 := List.length_erase_le (l := th.promises.erase tw') (a := tw' + 1)
    have h3 := List.length_pos_of_mem htw'
    omega

-- copied from TermStep.caspC_mid/caspLocC_mid; cellTargetP for the target
theorem casp_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {μ : Mode} {tw u : Ty} {i0 i1 j0 j1 : Idx} {Rf Rs Rok : Res} {xk : AllocLabel}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok tw) (ht : tw = .ptr μ u ∨ tw = .loc μ u) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hnv : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      EnvVal (CE η) (cl ρ η.wit 0 0 u) [n0, n1])
    (hvR : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      ∃ Rv, EnvValR (CE η) (cl ρ η.wit 0 0 u) [n0, n1] Rv ∧ Rv (.own xk) = 0)
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvR ρ η th.σs (ResumeR p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  obtain ⟨te0, hte0, hio0⟩ := hie0
  obtain ⟨rt0, x0, hee0, hx0, -⟩ := atom_num hi.1.2.1 hte0 hio0
  obtain ⟨te1, hte1, hio1⟩ := hie1
  obtain ⟨rt1, x1, hee1, hx1, -⟩ := atom_num hi.1.2.1 hte1 hio1
  obtain ⟨tv0, htv0, hjo0⟩ := hj0
  obtain ⟨rtv0, n0, hev0, hn0, -⟩ := atom_num hi.1.2.1 htv0 hjo0
  obtain ⟨tv1, htv1, hjo1⟩ := hj1
  obtain ⟨rtv1, n1, hev1, hn1, -⟩ := atom_num hi.1.2.1 htv1 hjo1
  obtain ⟨A, pw, rw, hea, haddr, -, hcell⟩ : ∃ A pw rw, evalAt th.env w = some (rw, [pw]) ∧
      addrOf pw = some A ∧ loadUnits g.arch pw A acq [.two] 0 (stOf mem pairs th) ≠ [] ∧
      ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw A acq [.two] 0 (stOf mem pairs th) → PromAbove s1 →
        MemInv g (CE η) s1 ∧ ∀ s1', MemInv g (CE η) s1' →
          ∀ s2, s2 ∈ storeUnits g.k g.arch pw A rel [.two] [n0, n1] 0 s1' → MemInv g (CE η) s2 := by
    rcases ht with rfl | rfl
    · obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := caspCell (acq := acq) (rel := rel) (g := g) (mem := mem)
        (pairs := pairs) hpk hμ hu (fun _ => hnv n0 n1 hn0 hn1) hi.1 hE htv hm
      exact ⟨⟨lab, 0⟩, pw, rw, hea, by simp [addrOf, hpw], hne, hcell⟩
    · exact caspLocCell (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hu
        (fun _ => hnv n0 n1 hn0 hn1) hi.1 hE htv hm
  have hus2 := pair_accs_cl (ρ := ρ) (wit := η.wit) hu
  obtain ⟨c, hsto, hat, hini⟩ := cellTargetP hi.1 hpk (by rcases ht with rfl | rfl <;> rfl) hμ
    (by rw [hus2]; simp) hea haddr
  obtain ⟨Rv, hv, hRv⟩ := hvR n0 n1 hn0 hn1
  exact caspA_out hterm hea haddr hee0 hee1 hev0 hev1 hcell hsto hat hini (by simp [wc, hus2])
    (fun N e h => by rw [h] at hus2; simp [accs] at hus2) hv hRv hok htvok hiok hres hfail hi hE htv hm hRP hRPo

theorem wr2W_own (P : Proto2) (n : Nat) (vs : List WeakMem.Val) (l : AllocLabel) :
    (wr2 P n vs + Res.one (.wd n)) (.own l) = 0 := by
  unfold wr2
  split <;> simp [Res.add_apply, Res.one]

/-- `casp_out` at a protocol pair (`caspMove`, `caspTake`, `caspBump`). -/
theorem caspW_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx cok : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String}
    {ok fail : Expr} {tw : Ty} {r i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {Rf Rs Rok : Res}
    {xk : AllocLabel}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail) (hpk : cx.peek w = .ok tw)
    (hw : word2Of tw = some (r, P))
    (hsc : ∃ μ u, (tw = .ptr μ u ∨ tw = .loc μ u) ∧ (μ = .own ∨ μ = .pub) ∧
      ((∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P)))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hst : InState2 cx P j0 j1 c₂ k0' k1')
    (hok : TypedK p η cok ok) (htvok : TvOK cok)
    (hiok : FInvR ρ η th.σs (ResumeR p th.stack Rs) cok ((t, .unit, []) :: th.env) Rok)
    (hres : Rok (.own xk) ≤ Rf (.own xk)) (hfail : TypedK p η cx fail)
    (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hRPo : RetPw th.σs th.stack cok.ret) :
    RmwOut p g mem pairs th η xk ((Rf + Rs) (.own xk)) := by
  obtain ⟨μ, u, ht, hμ, -⟩ := hsc
  have hu' : u = .word2 r P := by
    rcases ht with rfl | rfl <;> cases u <;> simp [word2Of] at hw <;> obtain ⟨rfl, rfl⟩ := hw <;> rfl
  subst hu'
  have hu : (∃ r' P', Ty.word2 r P = .word2 r' P') ∨ (∃ r' P', Ty.word2 r P = .epair r' P') := .inl ⟨_, _, rfl⟩
  obtain ⟨R, ws, hvr⟩ := pairRef_vr (g := g) (mem := mem) (pairs := pairs) hpk ht hμ hu hi.1 hE htv hm
  have hpwf : pwf2 P = true := by simp only [VR] at hvr; exact hvr.1
  have hsat : Sat cx.facts ρ := hi.1.1
  refine casp_out hterm hpk ht hμ hu hie0 hie1 hj0 hj1
    (fun n0 n1 hn0 hn1 => storeWord2_val hpwf hsat hst hn0 hn1) (fun n0 n1 hn0 hn1 => ?_)
    hok htvok hiok hres hfail hi hE htv hm hRP hRPo
  have hvs : [n0, n1].map (·.val) = [.num (ev ρ j0), .num (ev ρ j1)] := by simp [hn0, hn1]
  refine ⟨wr2 P (ev ρ r) ([n0, n1].map (·.val)) + Res.one (.wd (ev ρ r)), ⟨?_, by simp [cl, Valid]⟩,
    wr2W_own _ _ _ _⟩
  simp only [cl, clI_zero]
  exact VRR_word2_of hpwf hvs (InP2_of_st hsat hst)

-- copied from TermStep.tstepMC_casp/tstepMC_caspLoc; holding/credit/mint lines deleted
theorem tgt_casp {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (ht : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail) (hRP : RetPw th.σs th.stack cx.ret) : Tgt p g x n (CE η) mem pairs th := by
  have hsc' : StepScope cx (.casp acq rel w e0 e1 v0 v1 t ok fail) :=
    stepScope_of (by rw [← ht]; exact hS.sc) (fun _ _ _ h => by cases h)
  have hi := hS.hF
  have hE := hS.hE
  have htv := hS.tv
  have hm := hS.hm
  have hRL := RLink_of hE.2.1 hE.2.2
  refine tgt_rmw hS (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [ht] at h; cases h) ?_
  have hT0 := hS.hT
  have hCk0 := hS.ck
  rw [ht] at hT0 hCk0
  cases TermA4.CkW_inv_casp hCk0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    obtain ⟨μ, u, ht', hμ, -⟩ := hsc' _ hp
    obtain ⟨r, P⟩ : ∃ r P, epairOf _ = some (r, P) := ⟨_, _, hwe⟩
    have hu' : ∃ r P, u = .epair r P := by
      rcases ht' with rfl | rfl <;> cases u <;> simp [epairOf] at hwe <;> exact ⟨_, _, rfl⟩
    obtain ⟨r, P, rfl⟩ := hu'
    have hu : (∃ r' P', Ty.epair r P = .word2 r' P') ∨ (∃ r' P', Ty.epair r P = .epair r' P') := .inr ⟨_, _, rfl⟩
    obtain ⟨R, ws, hvr⟩ := pairRef_vr (g := g) (mem := mem) (pairs := pairs) hp ht' hμ hu hi.1 hE htv hm
    have hpwf : pwfE P = true := by simp only [VR] at hvr; exact hvr.1
    have hiok := bindR hb hi hRL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    refine casp_out ht hp ht' hμ hu hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 => storeEPair_val hpwf ⟨_, _, hn0, hn1⟩) (fun n0 n1 hn0 hn1 => ?_) hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hRP (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
    refine ⟨.zero, ⟨?_, by simp [cl, Valid]⟩, rfl⟩
    simp only [cl, clI_zero, VRR]
    exact ⟨⟨hpwf, _, _, by rw [List.map_cons, List.map_cons, List.map_nil, hn0, hn1]⟩, trivial⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' hep hbump _ hb hok hfail =>
    have hiok := bindR (rt := .unit) (ws := []) hb hi hRL rfl (Lay_etok_unit rfl)
    exact caspW_out ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | caspMove hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' hb hok hfail =>
    have hiok := bindR hb hi hRL (show VRR ρ η .unit (shp .unit) [] .zero from rfl) (unit_Lay _)
    exact caspW_out ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
  | caspTake hp hw hie0 hie1 hj0 hj1 hsti hcl hst hcl' hh _ hh' _ hb hok hfail =>
    have hiok := bindR (rt := .unit) (ws := []) (R := .one (.rg _)) hb hi hRL rfl (Lay_etok_unit rfl)
    exact caspW_out ht hp hw (hsc' _ hp) hie0 hie1 hj0 hj1 hst hok.tk
      (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1 hiok (by simp [Res.add_apply, Res.one]) hfail.tk hi hE htv hm hRP (retPw_eq hS.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))

/-! ## Boxed sums: a box allocation at a fresh label -/

/-- A box allocation at the fresh label keeps the private holding (the new label is not in Σ). -/
theorem memHeldP_box {g : G} {E : TEnv} {s : St} {HP : Res} {us : List Acc} {ws : List Word} {r : St × Word}
    (hm : MemInv g E s) (hH : MemHeldP E s HP)
    (hr : r ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i s.nalloc) us ws s) (B : Box) (F : Ts) :
    MemHeldP (seeBoxE E (freshLabel g.lbase g.n g.i s.nalloc) B F) (if g.boxFence then fenceS r.1 .st else r.1) HP := by
  have hnone := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hbnone : E.box (freshLabel g.lbase g.n g.i s.nalloc) = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hpfn : E.pfr (freshLabel g.lbase g.n g.i s.nalloc) = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2
  obtain ⟨hg, hsub, -, -, hful⟩ := alloc_growsP hm.2.2.1 r hr
  have hQ : ∀ l, Priv E l → l ≠ freshLabel g.lbase g.n g.i s.nalloc := fun l h e => by
    obtain ⟨⟨c, hc, -⟩, -⟩ := h
    rw [e, hnone] at hc; cases hc
  have key : MemHeldP (seeBoxE E (freshLabel g.lbase g.n g.i s.nalloc) B F) r.1 HP := by
    refine TermOwnHeldQ.memHeldOn_tr hH (fun l => ?_) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun l hq => by simp [seeBoxE, hQ l hq]) rfl rfl
      (fun l hq o w hw => LatestNP_growsAtF hg (fun t h => hsub.subset h) hful (hQ l hq) hw)
      (fun h => ValOfR_mono (η₁ := E) (η₂ := seeBoxE E (freshLabel g.lbase g.n g.i s.nalloc) B F) rfl rfl
        (fun _ _ h => h) (fun _ => Nat.le_refl _) h
        (hP := fun l f h' => by
          have hne : l ≠ freshLabel g.lbase g.n g.i s.nalloc := fun e => by rw [e, hpfn] at h'; cases h'
          simp only [seeBoxE, hne, ↓reduceIte]; exact h')
        (hB := fun l B' h' => by
          have hne : l ≠ freshLabel g.lbase g.n g.i s.nalloc := fun e => by rw [e, hbnone] at h'; cases h'
          simp only [seeBoxE, hne, ↓reduceIte]; exact h'))
    by_cases e : l = freshLabel g.lbase g.n g.i s.nalloc
    · subst e
      refine ⟨fun h => ?_, fun h => absurd rfl (hQ _ h)⟩
      have h2 := h.2
      simp [seeBoxE] at h2
    · simp only [Priv, OwnL, seeBoxE, e, ↓reduceIte]
  split
  · exact TermOwnHeldQ.memHeldOn_eqs key rfl rfl
  · exact key

/-- A boxed-sum result: some environment with Σ kept, the frame at `T`, `MemInv`, and the private
holding of `s0` carried. -/
def BoxRes (p : Prog) (g : G) (η : TEnv) (s0 : St) (T : Res) (th' : TTh) (S' : St) : Prop :=
  ∃ E, ThInvRE p E th' T ∧ MemInv g E S' ∧ E.sto = (CE η).sto ∧
    (∀ HP, MemHeldP (CE η) s0 HP → MemHeldP E S' HP) ∧ Ext (CE η) E ∧ E.ini = (CE η).ini

/-- Every taken result of a boxed-sum step is a `BoxRes`. -/
def BoxOut (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (η : TEnv) (T : Res) : Prop :=
  ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
    BoxRes p g η (stOf mem pairs th) T r.2.2 (stOf r.1 r.2.1 r.2.2)

theorem tgt_box {p : Prog} {g : G} {x : AllocLabel} {n : Nat} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res} (hX : Src p g x n mem pairs th ρ η cx Rf Rs HP)
    (hnb : ∀ E1, BumpIf th E1)
    (h : BoxOut p g mem pairs th η (Rf + Rs)) : Tgt p g x n (CE η) mem pairs th := by
  intro r hr hpa
  obtain ⟨E, hT, hm, hsto, hH, hXE, hini⟩ := h r hr hpa
  exact ⟨E, Rf + Rs, HP, hT, hm, hH HP hX.hH, fun l c hc => hX.nie l c (by rw [← hsto]; exact hc),
    by rw [hsto]; exact hX.sto, hX.le,
    TermOwnX2.anchStep_gen hXE (hnb E) (fun _ _ h _ => by rw [← hsto]; exact h)
      (fun _ _ => by rw [hini]; exact Nat.le_max_left _ _) (fun l h0 hl => absurd (by rw [hsto]; exact h0) hl)⟩

-- copied from TermStep.tstepMR_inlB; own-key output, no `MemHeldL`
theorem inlB_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRR ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    BoxOut p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close th.σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed (.sum rt (close th.σs τ)) = true := by simp [isBoxed, sumHead, hS]
  have hRa : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num j) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum rt (close th.σs τ), [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  intro r hr _
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  let B : Box := ⟨j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm hn hbf hal hnw.symm
  simp only at hpw
  subst hpw
  obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
  have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
  have eqw : VEq ws q' := eq1.symm.trans eq'.vals
  have hv2 : VRR ρ η'.unsee t (shp rt) q' R :=
    VRR_ext hE.2.1.unsee hE.2.2.unsee (Ext_unsee hx) (VRR_store hE.2.1 hE.2.2 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
      (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VRR_up _ _ _ _ _ hwq hv))
  have hvr : VRR ρ η' (.sum t τ) (shp (.sum rt (close th.σs τ))) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxL (B := B) hS hRa rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) hj hq' hv2
      (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
      (by show ((armsOf (.sum rt (close th.σs τ)))[j]?).bind wc = some (p0.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hnw, List.length_map])
  have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
    (Lay_box ⟨hshape, hsk, hwc, hval, hly⟩ hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_box hm hH hal B _, TermOwnX2.ext_CE hx, rfl⟩

-- copied from TermStep.tstepMR_inrB; own-key output, no `MemHeldL`
theorem inrB_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hv : VRR ρ η t (shp rt) ws R) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    BoxOut p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  let τc := close th.σs τ
  let n := (armsOf τc).length
  have harmS : (armsOf (.sum τc rt))[n + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed (.sum τc rt) = true := by simp [isBoxed, sumHead, τc, hS]
  have hRb : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num (n + j)) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum τc rt, [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box (t := Ty.sum (close th.σs τ) rt) (j := (armsOf (close th.σs τ)).length + j) hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  intro r hr _
  rw [key, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  let B : Box := ⟨n + j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm hn hbf hal hnw.symm
  simp only at hpw
  subst hpw
  obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
  have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
  have eqw : VEq ws q' := eq1.symm.trans eq'.vals
  have hv2 : VRR ρ η'.unsee t (shp rt) q' R :=
    VRR_ext hE.2.1.unsee hE.2.2.unsee (Ext_unsee hx) (VRR_store hE.2.1 hE.2.2 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
      (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VRR_up _ _ _ _ _ hwq hv))
  have hvr : VRR ρ η' (.sum τ t) (shp (.sum τc rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxR (B := B) hS hRb rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) (Nat.le_add_right _ _)
      (by show ofArm rt (n + j - n) _ = _; rw [Nat.add_sub_cancel_left]; exact hq') hv2
      (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
      (by show ((armsOf (.sum τc rt))[n + j]?).bind wc = some (p0.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hnw, List.length_map])
  have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
    (TermSound.Lay_boxR ⟨hshape, hsk, hwc, hval, hly⟩ hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_box hm hH hal B _, TermOwnX2.ext_CE hx, rfl⟩

-- copied from TermStep.tstepMR_inlBB; own-key output, no `MemHeldL`, no nonemptiness
theorem inlBB_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hvV : VR ρ η t (shp rt) ws) (hv : VRR ρ η t (shp rt) ws R)
    (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    BoxOut p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hvV
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let S := Ty.sum rt (close th.σs τ)
  have harmS : (armsOf S)[B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S r1.2.1 r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num B0.tag) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  intro r hr hpr0
  rw [key, List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    have hpa' := hpr0
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
    exact injM_pa hpl1 hr2 hpa'
  obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
  rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
  have hm1 : MemInv g (CE η) s1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
  have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
  let lbl := freshLabel g.lbase g.n g.i s1.nalloc
  let V := s1.vs.vRelSt
  let B : Box := ⟨B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm1 hn hbf hal hlen
  simp only at hpw
  subst hpw
  have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2
  have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
  let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
  have hv0 : VRR ρ η' t (vsh 0 (shp rt)) [w] R := by rw [vsh_zero rt hrb]; exact VRR_ext hE.2.1 hE.2.2 hx hv
  have hv1 : VRR ρ η' t (vsh 0 (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_ren (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
      (by simp [η', TEnv.withSto, hne0, hB0]) (by simp [η', TEnv.withSto])
      (by simpa [η', TEnv.withSto] using hsto0)
      (by simp [η', TEnv.withSto, hini0]) rfl (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
      (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
      (by simp [η', TEnv.withSto, hini0])
  have hvr : VRR ρ η' (.sum t τ) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxLB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) hj hv1
      (by show ((armsOf S)[B0.tag]?).bind wc = some (p1.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hlen, List.length_map])
  have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
    (Lay_box hl hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_box hm1 (TermOwnHeldQ.memHeldOn_eqs hH e1 e4) hal B _, TermOwnX2.ext_CE hx, rfl⟩

-- copied from TermStep.tstepMR_inrBB; own-key output, no `MemHeldL`, no nonemptiness
theorem inrBB_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → TypedK p η c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (rt, ws)) (hvV : VR ρ η t (shp rt) ws) (hv : VRR ρ η t (shp rt) ws R)
    (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    BoxOut p g mem pairs th η (Rf + Rs) := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hvV
  let n := (armsOf (close th.σs τ)).length
  let S := Ty.sum (close th.σs τ) rt
  have harmS : (armsOf S)[n + B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S (n + r1.2.1) r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num (n + B0.tag)) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  intro r hr hpr0
  rw [key, List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    have hpa' := hpr0
    obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
    exact injM_pa hpl1 hr2 hpa'
  obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
  rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
  have hm1 : MemInv g (CE η) s1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
  have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
  let lbl := freshLabel g.lbase g.n g.i s1.nalloc
  let V := s1.vs.vRelSt
  let B : Box := ⟨n + B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm1 hn hbf hal hlen
  simp only at hpw
  subst hpw
  have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2
  have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
  let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
  have hv0 : VRR ρ η' t (vsh 0 (shp rt)) [w] R := by rw [vsh_zero rt hrb]; exact VRR_ext hE.2.1 hE.2.2 hx hv
  have hv1 : VRR ρ η' t (vsh n (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_ren (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
      (by simp [η', TEnv.withSto, hne0, hB0]) (by simp [η', TEnv.withSto])
      (by simpa [η', TEnv.withSto] using hsto0)
      (by simp [η', TEnv.withSto, hini0]) (show B0.tag + n = (n + B0.tag) + 0 by omega) (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
      (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
      (by simp [η', TEnv.withSto, hini0])
  have hvr : VRR ρ η' (.sum τ t) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_boxRB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withSto]) (Or.inl hBS) (Nat.le_add_right _ _) hv1
      (by show ((armsOf S)[n + B0.tag]?).bind wc = some (p1.map (bumpW V)).length
          rw [harmS]; simp [wc, hus, hlen, List.length_map])
  have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hvr
    (TermSound.Lay_boxR hl hS)) (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he.ext hx, htv', hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, by rw [hCE]; exact hm', rfl,
    fun HP hH => by rw [hCE]; exact memHeldP_box hm1 (TermOwnHeldQ.memHeldOn_eqs hH e1 e4) hal B _, TermOwnX2.ext_CE hx, rfl⟩

-- copied from TermStep.case_armNBR; own-key output, no `MemHeldL`
theorem caseArmNB_out {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 q1 : List Word} {R Rr Rf Rs : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOK p η)
    (hm1 : MemInv g (CE η) s1) {S0 : St} (hH1 : ∀ HP, MemHeldP (CE η) S0 HP → MemHeldP (CE η) s1 HP)
    (hty : isBoxed ty = false) (hq : ofArm ty j p1 = some q1) (hlay : Lay th.σs u ty q1)
    (hvr : VRR ρ η u (shp ty) q1 R) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    ∀ r2 ∈ injM g s1 ty j p1,
      BoxRes p g η S0 (Rf + Rs) (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) r2.1 := by
  rw [injM_nbB hty, hq]
  intro r2 hr2
  simp [ol] at hr2; subst hr2
  have hf := FInvR_mono (bindR hb hi1 (RLink_of hE.2.1 hE.2.2) hvr hlay) (res_swap_le hle)
  exact ⟨CE η, ⟨ρ, η, c', Rf, Rs, rfl, hE, he, htv, by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩, hm1, rfl, hH1, Ext_refl (Coh_CE η) (CohR_CE η), rfl⟩

-- copied from TermStep.case_armBR; own-key output, no `MemHeldL`
theorem caseArmB_out {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 : List Word} {us : List Acc} {w : Word}
    {x0 : Address} {B0 : Box} {s0 : Nat} {R Rr Rf Rs : Res}
    (hb : c₁.bind xv u = .ok c') (he : TypedK p η c' e') (htv : TvOK c')
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf) (hE : EnvOK p η)
    (hm1 : MemInv g (CE η) s1) {S0 : St} (hH1 : ∀ HP, MemHeldP (CE η) S0 HP → MemHeldP (CE η) s1 HP)
    (hn : 0 < g.n) (hbf : g.boxFence = true) (hty : isBoxed ty = true) (hus : (armsOf ty)[j]?.bind accs = some us)
    (hlen : p1.length = nWords us) (hw : w.val = .loc x0 0) (hB0 : η.box x0.label = some B0)
    (hsto0 : η.sto x0.label = none) (hini0 : η.ini x0.label = 0) (ht : B0.tag = j + s0)
    (hWp : WLe B0.pay p1) (hv : VRR ρ η u (vsh s0 (shp ty)) [w] R) (hlay : ∀ pw, Lay th.σs u ty [pw]) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    ∀ r2 ∈ injM g s1 ty j p1,
      BoxRes p g η S0 (Rf + Rs) (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) r2.1 := by
  rw [injM_box hty hus]
  intro r2 hr2
  rw [List.mem_map] at hr2
  obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr2
  let lbl := freshLabel g.lbase g.n g.i s1.nalloc
  let V := s1.vs.vRelSt
  let B : Box := ⟨j, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
  obtain ⟨hm', hpw⟩ := MemInv_boxF (us := us) hm1 hn hbf hal hlen
  simp only at hpw
  subst hpw
  have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
  have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2
  have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
  let η' := η.withSto η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
    (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
  have hx : Ext η η' := Ext_withSto hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
    (hP := fun l f h => by
      have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
    (hB := fun l B' h => by
      have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
      simp only [hne, ↓reduceIte]; exact h)
  have hcr' : CohR η' := hx.2.2.2.2.2.2.2.2.2.2.1
  have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
  have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withSto], s'.vs.vWr, by simp [η', TEnv.withSto], Nat.le_refl _⟩
  have hv0 : VRR ρ η' u (vsh s0 (shp ty)) [w] R := VRR_ext hE.2.1 hE.2.2 hx hv
  have hv1 : VRR ρ η' u (vsh 0 (shp ty)) [cst (.loc ⟨lbl, 0⟩ 0)] R :=
    VRR_ren (B1 := B0) (B2 := B) hx.1 hcr' hw rfl rfl
      (by simp [η', TEnv.withSto, hne0, hB0]) (by simp [η', TEnv.withSto])
      (by simpa [η', TEnv.withSto] using hsto0)
      (by simp [η', TEnv.withSto, hini0]) (by show B0.tag + 0 = j + s0; omega)
      (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS) (bh_shp ty hty) hv0
      (by simp [η', TEnv.withSto, hini0])
  rw [vsh_zero ty hty] at hv1
  have hf := FInvR_mono (bindR hb (FInvR_ext hE.2.1 hE.2.2 hx hi1) (RLink_of hx.1 hcr') hv1 (hlay _))
    (res_swap_le hle)
  exact ⟨CE η', ⟨ρ, η', c', Rf, Rs, rfl, ⟨hE.1, hx.1, hcr'⟩, he, htv, by simpa [withS] using hf, rfl, retPw_eq hRP1 (by first | rfl | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu) | exact (use_ret hu :))⟩,
    by rw [hCE]; exact hm', rfl, fun HP hH => by rw [hCE]; exact memHeldP_box hm1 (hH1 HP hH) hal B _, TermOwnX2.ext_CE hx, rfl⟩

-- copied from TermStep.tstepMR_caseB; own-key output, no `MemHeldL`, no nonemptiness
theorem caseB_out {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} {c₁ c₂ c₃ : Cx}
    {ra rb : Ty} {ws : List Word} {R Rr Rf Rs : Res} (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hb1 : c₁.bind x u = .ok c₂) (he1 : TypedK p η c₂ e₁) (htv1 : TvOK c₂)
    (hb2 : c₁.bind y v = .ok c₃) (he2 : TypedK p η c₃ e₂) (htv2 : TvOK c₃)
    (hi1 : FInvR ρ η th.σs (ResumeR p th.stack Rs) c₁ th.env Rr) (hle : R + Rr ≤ Rf)
    (hea : evalAt th.env a = some (.sum ra rb, ws)) (hvV : VR ρ η (.sum u v) (shp (.sum ra rb)) ws)
    (hvR : VRR ρ η (.sum u v) (shp (.sum ra rb)) ws R)
    (hl : Lay th.σs (.sum u v) (.sum ra rb) ws) (hS : (Ty.sum ra rb).tier = .boxed)
    (hsg : sig (.sum ra rb) = sig (cl ρ η.wit 0 0 (.sum u v)))
    (hE : EnvOK p η) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) :
    BoxOut p g mem pairs th η (Rf + Rs) := by
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  have hrb : isBoxed (.sum ra rb) = true := by simp [isBoxed, sumHead, hS]
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operand hE.2.1 hbi hrb hsg hvV
  have hv' := hvR
  simp only [VRR, shp] at hv'
  obtain ⟨n0, Ra, Rb, hR, hv'⟩ := hv'
  simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have htl : (Ty.sum (lnorm ra) (lnorm rb)).tier = .boxed := by
    rw [← hS]; exact tier_lnorm (.sum ra rb)
  have hv3 := hv'.resolve_right (fun ⟨j, p, hd, _, _⟩ => by rw [htl] at hd; simp [decodeArm] at hd)
  obtain ⟨-, x1, s0, B, hx1, -, hB, hn1, -, -, hA, hB'⟩ := hv3
  rw [wc_boxed hS] at hn1
  have hs0 : s0 = 0 := by simp at hn1; omega
  subst hs0
  simp only [List.map_cons, List.map_nil, hw, List.cons.injEq, and_true] at hx1
  cases hx1
  rw [hB0, Option.some.injEq] at hB
  subst hB
  have la : (armsOf (lnorm ra)).length = (armsOf ra).length := by rw [armsOf_lnorm, List.length_map]
  simp only [Nat.sub_zero, Nat.zero_add, la, isBoxed_lnorm, shp_lnorm] at hA hB'
  have hsg2 : Ty.sum (sig ra) (sig rb) = Ty.sum (sig (cl ρ η.wit 0 0 u)) (sig (cl ρ η.wit 0 0 v)) := hsg
  simp only [Ty.sum.injEq] at hsg2
  have hs := hl.2.1
  simp only [close, substTs, skel, etok, Ty.sum.injEq] at hs
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨-, -, -, -, hly⟩ := hl
  simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
  have layB : ∀ (ty : Ty) (t : Ty), isBoxed ty = true → etok (skel ty) = etok (skel (close th.σs t)) →
      etok (lyt 0 ty) = etok (lyt 0 (close th.σs t)) → ∀ pw, Lay th.σs t ty [pw] := by
    intro ty t hty hk hy pw
    refine ⟨fun us hu => ?_, hk, by rw [wc_isBoxed ty hty]; simp, Valid_boxed ty _ hty, hy⟩
    have h1 := wc_isBoxed ty hty
    simp only [wc, hu, Option.map_some, Option.some.injEq] at h1
    simp [h1]
  let s := stOf mem pairs th
  obtain ⟨-, hpr⟩ := projM_own (g := g) (s := s) (t := .sum ra rb) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have hlen : ∀ p1 : List Word, WLe B0.pay p1 → p1.length = nWords us := fun p1 h => h.length.symm.trans hnw.symm
  intro r hr hpr0
  simp only [tstep, hterm, hea] at hr
  rw [List.mem_flatMap] at hr
  obtain ⟨r1, h1, hr⟩ := hr
  have hp1 : PromAbove r1.1 := by
    obtain ⟨f1, f2⟩ := (hpr r1 h1).1
    have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
    have hpa' := hpr0
    try simp only at hr
    split at hr
    · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
    · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
  obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
  have hm1 := MemInv_load hm e1 e2 (LoadCoh_rd hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
  have hH1 : ∀ HP, MemHeldP (CE η) s HP → MemHeldP (CE η) r1.1 HP := fun HP h =>
    TermOwnHeldQ.memHeldOn_eqs h e1 e4
  obtain ⟨s1, j1, p1⟩ := r1
  simp only at htag hWp hm1 hH1
  subst htag
  by_cases hj : B0.tag < (armsOf ra).length
  · simp only [hj, ite_true, List.mem_map] at hr
    obtain ⟨r2, hr2, rfl⟩ := hr
    cases hty : isBoxed ra with
    | false =>
        obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hA hj).2 hty
        obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
          case_arm_nbR hE.2.1 hE.2.2 hty hsg2.1 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
        exact caseArmNB_out hb1 he1 htv1 hi1 hle hE hm1 hH1 hty hq1 ⟨hs1, hsa, hw1, hv1, hly.1⟩ hvr1 hRP1 r2 hr2
    | true =>
        have harmA : (armsOf ra)[B0.tag]? = some arm := by
          rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_left hj]
        exact caseArmB_out (hbf := hbf) (s0 := 0) hb1 he1 htv1 hi1 hle hE hm1 hH1 hn hty (by rw [harmA]; exact hus)
          (hlen p1 hWp) hw hB0 hsto0 hini0 (by omega) hWp ((hA hj).1 hty) (layB ra u hty hsa hly.1) hRP1 r2 hr2
  · have hj' : (armsOf ra).length ≤ B0.tag := by omega
    simp only [hj, ite_false, List.mem_map] at hr
    obtain ⟨r2, hr2, rfl⟩ := hr
    cases hty : isBoxed rb with
    | false =>
        obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hB' hj').2 hty
        obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ :=
          case_arm_nbR hE.2.1 hE.2.2 hty hsg2.2 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
        exact caseArmNB_out hb2 he2 htv2 hi1 hle hE hm1 hH1 hty hq1 ⟨hs1, hsb, hw1, hv1, hly.2⟩ hvr1 hRP1 r2 hr2
    | true =>
        have harmB : (armsOf rb)[B0.tag - (armsOf ra).length]? = some arm := by
          rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_right hj']
        exact caseArmB_out (hbf := hbf) (s0 := (armsOf ra).length) hb2 he2 htv2 hi1 hle hE hm1 hH1 hn hty
          (by rw [harmB]; exact hus) (hlen p1 hWp)
          hw hB0 hsto0 hini0 (by omega) hWp ((hB' hj').1 hty) (layB rb v hty hsb hly.2) hRP1 r2 hr2

-- copied from TermStep.tstepMR_inlT; dispatch into `Tgt`
theorem tgt_inl {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : Src p g xl n mem pairs th ρ η cx Rf Rs HP) {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : Tgt p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkL := hX.ck
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop hX.tv
    cases hop with
    | inl _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum t τ) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useR hu hX.hF hX.hE.2.2
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum t τ) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · apply tgt_box hX (TermOwnX2.bumpIf_nb hterm)
        cases hrb : isBoxed rt with
        | false => exact inlB_out hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK hX.tv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu hX.tv).2.1
            exact inlBB_out hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl) hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · have h : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs (.sum t' τ)).tier ≠ .boxed :=
          fun t' c₁' hu' => by
            rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
            rw [← hsk]; exact hS
        exact tgt_frame hP hX (by rw [hterm]; exact h) (same_inlR hterm h hX.hT hX.hF) hPS hSub hSig

-- copied from TermStep.tstepMR_inrT; dispatch into `Tgt`
theorem tgt_inr {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : Src p g xl n mem pairs th ρ η cx Rf Rs HP) {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : Tgt p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkL := hX.ck
  rw [hterm] at hT0 hCkL
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    obtain ⟨c', -, hop, he, hck, -⟩ := TermA4.CkW_let hCkL
    have htv' := OpT_TvOK hP hop hX.tv
    cases hop with
    | inr _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum τ t) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useR hu hX.hF hX.hE.2.2
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum τ t) = .ok c'' → TypedK p η c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨⟨he, hck⟩, htv'⟩
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · apply tgt_box hX (TermOwnX2.bumpIf_nb hterm)
        cases hrb : isBoxed rt with
        | false => exact inrB_out hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hv hl hS hrb hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK hX.tv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu hX.tv).2.1
            exact inrBB_out hterm hX.gn hc' ⟨c', hb⟩ hi1 hle hea hvV hv hl hS hrb
              (lay_closed hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl) hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu)))
      · have h : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs (.sum τ t')).tier ≠ .boxed :=
          fun t' c₁' hu' => by
            rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
            rw [← hsk]; exact hS
        exact tgt_frame hP hX (by rw [hterm]; exact h) (same_inrR hterm h hX.hT hX.hF) hPS hSub hSig

-- copied from TermStep.tstepMR_caseT; dispatch into `Tgt`
theorem tgt_case {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {xl : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hX : Src p g xl n mem pairs th ρ η cx Rf Rs HP) {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : Tgt p g xl n (CE η) mem pairs th := by
  have hT0 := hX.hT
  have hCkC := hX.ck
  rw [hterm] at hT0 hCkC
  cases hT0 with
  | case hu hb1 he1 hb2 he2 =>
    obtain ⟨u, v, c₁, c₂, c₃, hu, hb1, he1, hb2, he2⟩ : ∃ u v c₁ c₂ c₃,
        cx.use a = .ok (.sum u v, c₁) ∧ c₁.bind x u = .ok c₂ ∧ Typed p c₂ e₁ ∧
        c₁.bind y v = .ok c₃ ∧ Typed p c₃ e₂ := ⟨_, _, _, _, _, hu, hb1, he1, hb2, he2⟩
    have hck12 := TermA4.CkW_case hCkC hu hb1 hb2
    obtain ⟨rt, ws, R, Rr, hea, hvV, hl, hv, hi1, hle⟩ := useR hu hX.hF hX.hE.2.2
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have htv12 := case_TvOK hu hb1 hb2 hX.tv
      have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK hX.tv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu hX.tv).2.1
      have hsg := lay_closed (ρ := ρ) hX.hF.1.2.2.2.1 hX.hF.1.2.2.2.2.1 ho htb hl
      exact tgt_box hX (TermOwnX2.bumpIf_nl fun _ _ _ h => by rw [hterm] at h; cases h) (caseB_out hterm hX.gn hb1 ⟨he1, hck12.1⟩ htv12.1 hb2 ⟨he2, hck12.2⟩ htv12.2 hi1 hle hea hvV hv hl hS hsg
        hX.hE hX.hm hX.bf (retPw_eq hX.rp (by first | exact (use_ret hu :) | exact (bind_ret hb :) | exact (bind_ret hb).trans (use_ret hu))))
    · have hnb : ∀ t' c₁', cx.use a = .ok (t', c₁') → (close th.σs t').tier ≠ .boxed := fun t' c₁' hu' => by
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← tier_of_eskel hl.2.1]; exact hS
      exact tgt_frame hP hX (by rw [hterm]; exact hnb) (same_caseR hterm hnb hX.hT hX.ck hX.hF hX.hE hX.tv) hPS hSub hSig

/-! ## The dispatch -/

/-- The K4 terms (package 4's heads). -/
def EasyK4 : Expr → Prop
  | .let_ _ (.inl _ _) _ | .let_ _ (.inr _ _) _ | .case _ _ _ _ _ => True
  | .let_ _ (.intoRgn _ _) _ | .let_ _ (.mkTicket _ _ _ _ _) _ | .let_ _ (.claim _ _) _ => True
  | .let_ _ (.publish _) _ | .let_ _ (.mkWord _ _ _ _) _ | .let_ _ (.mkWord2 _ _ _ _ _) _ => True
  | .let_ _ (.mkEPair _ _ _ _) _ | .cas _ _ _ _ _ _ _ _ | .casp _ _ _ _ _ _ _ _ _ _ => True
  | .let_ _ (.ldp _ _ _ _) _ | .let_ _ (.stp _ _ _ _ _) _ | .let_ _ (.fetch _ _ _ _ _) _ => True
  | _ => False

theorem tgt_easy {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {g : G} {x : AllocLabel} {n : Nat} {mem : Memory}
    {pairs : List Ts} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs HP : Res}
    (hS : Src p g x n mem pairs th ρ η cx Rf Rs HP) (h : EasyK4 th.term) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    Tgt p g x n (CE η) mem pairs th := by
  have hsc := hS.sc
  cases ht : th.term with
  | let_ y op e =>
    rw [ht] at h hsc
    cases op with
    | inl τ a => exact tgt_inl hP hS ht hPS hSub hSig
    | inr τ a => exact tgt_inr hP hS ht hPS hSub hSig
    | intoRgn rn a =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | mkTicket a1 a2 a3 a4 a5 =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | claim a1 a2 =>
      exact (scopeD_vac hsc (fun h => h) (fun _ _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h)).elim
    | publish a => exact tgt_publish hP hS ht hPS
    | mkWord a1 a2 a3 a4 => exact tgt_keep hS (mkWord_step ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | mkWord2 a1 a2 a3 a4 a5 => exact tgt_keep hS (mkWord2_step ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | mkEPair a1 a2 a3 a4 => exact tgt_keep hS (mkEPair_step ht hP hS.hT hS.ck hS.hF hS.hE hS.tv hRP hPS)
    | ldp a1 a2 a3 a4 => exact tgt_ldp hP hS ht hRP hPS
    | stp a1 a2 a3 a4 a5 => exact tgt_stp hS hP ht hRP
    | fetch a1 a2 a3 a4 a5 => exact tgt_fetch hP hS ht hRP
    | _ => exact False.elim h
  | cas acq rel w e v t ok fail => exact tgt_cas hS ht hRP
  | casp acq rel w e0 e1 v0 v1 t ok fail => exact tgt_casp hS ht hRP
  | case a y1 e1 y2 e2 => exact tgt_case hP hS ht hPS hSub hSig
  | _ => rw [ht] at h; exact False.elim h

theorem easyK4_of_pkg {e : Expr} (h : TermOwnX2.exprPkg e = 4) : EasyK4 e := by
  cases e with
  | let_ y op e => cases op <;> simp [TermOwnX2.exprPkg, TermOwnX2.opPkg] at h <;> trivial
  | _ => first | trivial | simp [TermOwnX2.exprPkg] at h

/-- **The deliverable**: every package-4 thread step keeps `OwnXLe` at the same bound. -/
theorem ownXStep_k4 [WrIniC] {p : Prog} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {x : AllocLabel} (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : ∀ n, TermOwnX2.OwnXStepPkg p k arch i x n 4 := by
  intro n E0 c0 c0' th hth hq hsc hw hvI hI hs hc
  exact ownXLe_of_src hth hsc hw hvI hI hs hc fun ρ η cx Rf Rs HP hS => tgt_easy hP hS (easyK4_of_pkg hq) hS.rp hPS hSub hSig

end TermOwnK4

#print axioms TermOwnK4.tgt_frame
#print axioms TermOwnK4.pub_step
#print axioms TermOwnK4.pubBuf_step
#print axioms TermOwnK4.memHeldP_shrink
#print axioms TermOwnK4.tgt_publish
#print axioms TermOwnK4.ownXPub1
#print axioms TermOwnK4.mkWord_step
#print axioms TermOwnK4.mkWord2_step
#print axioms TermOwnK4.mkEPair_step
#print axioms TermOwnK4.tgt_easy
#print axioms TermOwnK4.ownXStep_k4
#print axioms TermOwnK4.totStep_own_le
#print axioms TermOwnK4.ownXLe_of_src
#print axioms TermOwnK4.tgt_same
#print axioms TermOwnK4.tgt_pstore
#print axioms TermOwnK4.tgt_stp
#print axioms TermOwnK4.tgt_rmw
#print axioms TermOwnK4.tgt_fetch
#print axioms TermOwnK4.tgt_cas
#print axioms TermOwnK4.tgt_casp
#print axioms TermOwnK4.memHeldP_box
#print axioms TermOwnK4.tgt_box
#print axioms TermOwnK4.inlB_out
#print axioms TermOwnK4.inrB_out
#print axioms TermOwnK4.inlBB_out
#print axioms TermOwnK4.inrBB_out
#print axioms TermOwnK4.caseArmNB_out
#print axioms TermOwnK4.caseArmB_out
#print axioms TermOwnK4.caseB_out
#print axioms TermOwnK4.tgt_inl
#print axioms TermOwnK4.tgt_inr
#print axioms TermOwnK4.tgt_case

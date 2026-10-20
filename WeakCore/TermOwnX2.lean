import WeakCore.TermMainDefs
import WeakCore.TermOwnKey
import WeakCore.TermBlkZ
import WeakCore.TermOwnNet

/-!
# TermOwnX2 (own-key layer, package K0v2): `OwnXLe` and its base lemmas

`OwnXLe p k arch E0 i x n c`: thread `i` at `c` has the
resourceful frame invariant (`ThInvRE`), `MemInv` and a **private** holding (`MemHeldP`, the holding
on `Priv E` cells) at some environment `E` where `x` is allocated (`E.sto x ≠ none`: no fresh mint
of `x`), the box fence is on, and the frame plus private holding
carry the own key of `x` at most `n` times.  No credits, no full `MemHeld`, no `pfr ≠ none`.

* `ownXLe_start` (n = 1): from `SysInvN` via `TermOwnNet.ownNet_one`.  No new clause.
* `ownXLe_start_pub` (n = 0): at a published (`pubd`) cell via `SysInvN.ownPub`.
* `OwnXLe.use_ne` (n = 0): no own-mode use reaches `x`.
* N route: at a cell with a frontier memory's holding carries no own key (`memHeldS_own_zero`).
* P route: `proj_own_le`, the per-step projection at one key, any bound `n`.
* `OwnXPub1`: the publish of `x` takes 1 to 0, private form (statement; proved in `TermOwnK4`).
* Run: `OwnXStepT`/`OwnXStepP` in the `invAtX_stepW` shape (window `ScopeAt ∧ NoHoldPub3` at the
  source only) and `ownXLe_run` via `run_ind_win`.

**Copied core (dedupe when W is ported to g249b):** `PubWinT3`, `PubWinS3`, `NoHoldPub3`
(W/TermPubW L266, W/TermRunW L14–22) and `run_ind_win` (W/TermNoHoldA L117).

**Hazard:** G-c must not use `ownXLe_run` (its window premise comes from `certWinC`; circular).
-/

namespace TermOwnX2
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Copied window predicates and run induction (from W; dedupe on port) -/

/-- (copy of W `PubWinT3`) The step-level window premise, only at a planted-unseen published cell. -/
def PubWinT3 (E : TEnv) (s : St) (th : TTh) : Prop :=
  ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
    ws.map (·.val) = [.loc ad 0] → ∀ f, E.pfr ad.label = some f → ¬ E.seen ad.label → PubWin E s ad.label

/-- (copy of W `PubWinS3`) -/
def PubWinS3 (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∀ ρ η cx, EnvOK p η → Typed p cx th.term → TvOK cx → FInv ρ η th.σs (Resume p th.stack) cx th.env →
    MemInv g (CE η) (stOf mem pairs th) → PubWinT3 (CE η) (stOf mem pairs th) th

/-- (copy of W `NoHoldPub3`) -/
def NoHoldPub3 (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (c : Cfg) : Prop :=
  ∀ th, c.ths[i]? = some th → PubWinS3 p (gOf p k arch c i) c.mem c.pairs th

/-- (copy of W `run_ind_win`) Forward induction along a certificate run carrying `Inv`, whose step
preservation needs `Q` at the source only. -/
theorem run_ind_win {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {Inv Q : Cfg → Prop} {c : Cfg}
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → Inv c0 → Q c0)
    (hstep : ∀ c0 c0', Solo p k arch i c c0 → Inv c0 → Q c0 → c0' ∈ threadSteps p k arch c0 i →
      Certified p k arch c0' i → Inv c0')
    (hprom : ∀ c0 a v w, Solo p k arch i c c0 → Inv c0 → w < c0.mem.size →
      Certified p k arch (promise c0 i a v w) i → Inv (promise c0 i a v w))
    (h0 : Inv c) {c2 : Cfg} (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) : Inv c2 ∧ Q c2 := by
  suffices key : ∀ c1, Solo p k arch i c c1 → Inv c1 → ∀ {c2}, Solo p k arch i c1 c2 → Certified p k arch c2 i →
      Inv c2 ∧ Q c2 from key c (.refl _) h0 h hc2
  intro c1 hc1 hI c2 h12 hc2
  induction h12 with
  | refl => exact ⟨hI, hQ _ hc1 hc2 hI⟩
  | thread hs hrest ih =>
    have hc0 := certified_back (.thread hs hrest) hc2
    exact ih (solo_trans hc1 (.thread hs (.refl _)))
      (hstep _ _ hc1 hI (hQ _ hc1 hc0 hI) hs (certified_back hrest hc2)) hc2
  | prom a v w hw hrest ih =>
    exact ih (solo_trans hc1 (.prom a v w hw (.refl _))) (hprom _ a v w hc1 hI hw (certified_back hrest hc2)) hc2

/-! ## The invariant -/

/-- Every cell type of a code view is `∀`-free at value positions (`StoNI` for a `TEnv`). -/
def StoNIE (E : TEnv) : Prop := ∀ l cl, E.sto l = some cl → noIallV cl.ty = true

theorem stoNIE_cut {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} (h : StoNI Eg) : StoNIE (Cut Eg i S) :=
  fun l cl hl => h l cl (cutSto_some.1 (by rw [← Cut_sto]; exact hl)).1

/-- `StoNIE` along a step footprint: old cells unchanged, fresh cells carry `noIallV`. -/
theorem stoNIE_efoot {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (hf : EFootB W g E E' s s') (h : StoNIE E) : StoNIE E' := by
  intro l cl hl
  rcases hf.2.2.1 l with he | ⟨-, T, hT, ⟨-, -, hn, -⟩, -⟩
  · exact h l cl (he ▸ hl)
  · rw [hT] at hl; cases hl; exact hn

/-! ## (certWin-D) The anchor along the own-key run

`OwnXLe` carries `Ext E0 E ∧ AnchR E0 E0 E s` at its anchor `E0` (the cut the certificate's window
`NoHoldPubA` is anchored at).  A step conclusion carries `AnchStep`: the anchor moves from the
source environment to the result's, given the source's fresh-label fact and the step's write
locations (`WrLoc`, supplied once by the dispatchers from `WrIniC`). -/

/-- The plain frame of a resourceful one (as in `ThInvRE.thInvE`). -/
theorem finv_of {p : Prog} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {cx : Cx} {Rf Rs : Res} (htv : TvOK cx)
    (hF : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf) :
    FInv ρ η th.σs (Resume p th.stack) cx th.env :=
  FInvR_FInv htv.2.2.2.2.2.2.2
    (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs E rd ws R h) hF

/-- (A″) The step's write locations at every anchor, with the memory grown. -/
def WrLocG (g : G) (E E' : TEnv) (s s' : St) : Prop :=
  s.mem.size ≤ s'.mem.size ∧ ∀ Eu, WrLocA2 Eu g E E' s s'

/-- **`AnchR` along an environment change** that keeps `sto` at the labels with a frontier, the
frontiers, the thread, `seen` (monotone) and `rini` (monotone), and raises `ini` only up to `rini`; the
result's non-promise messages lie where `WrLocG` says. -/
theorem anchR_gen {g : G} {E0 E E' : TEnv} {s s' : St} (h : AnchR E0 E0 E s) (hfr : FreshLP g E s)
    (hm' : MemInv g E' s') (hwl : WrLocG g E E' s s') (hsub : ∀ l c, E0.sto l = some c → E.sto l = some c)
    (hsto : ∀ l c, E'.sto l = some c → E'.pfr l ≠ none → E.sto l = some c)
    (hpk : ∀ l f, E.pfr l = some f → E'.pfr l = some f) (htid : E'.tid = E.tid)
    (hsn : ∀ l, E.seen l → E'.seen l) (hri : ∀ l, E.rini l ≤ E'.rini l)
    (hini : ∀ l, E.sto l ≠ none → E'.ini l ≤ max (E.ini l) (E'.rini l))
    (hnew : ∀ l, E.sto l = none → E'.sto l ≠ none → (∃ c, E'.sto l = some c ∧ c.owner = some E'.tid) ∧ E'.pfr l = none) : AnchR E0 E0 E' s' := by
  obtain ⟨hA, hL, hR, hP, hK⟩ := h
  refine ⟨?_, ?_, ?_, fun l c N e us f hc' ho hty hus hw hN hf => Nat.lt_of_lt_of_le
      (hP l c N e us f (hsto l c hc' (by rw [hpk l f (hK l f hf)]; exact fun h => by cases h))
        (by rw [← htid]; exact ho) hty hus hw hN hf) hwl.1,
    fun l f hf => hpk l f (hK l f hf)⟩
  · intro l hl
    have h3 := hri l
    by_cases hEs : E.sto l = none
    · -- a cell new at this change: private, so `ini ≤ rini` (hidden units)
      obtain ⟨⟨c, hc, ho⟩, hp⟩ := hnew l hEs hl
      have := iniLe_of_hid hm'.2.2.2.2.2.1 hc ho hp
      omega
    · have h1 := hini l hEs
      have h2 := hA l hEs
      omega
  · intro l h0 ⟨c, hc', hown'⟩
    by_cases hpf' : E'.pfr l = none
    · exact iniLe_of_hid hm'.2.2.2.2.2.1 hc' hown' hpf'
    · have hc := hsto l c hc' hpf'
      have h1 := hL l h0 ⟨c, hc, by rw [← htid]; exact hown'⟩
      have h2 := hini l (by rw [hc]; exact fun h => by cases h)
      have h3 := hri l
      omega
  · intro l c N e us j hc' hown' hns' hty hus hw hjN hall
    by_cases hpf' : E'.pfr l = none
    · refine riniMem_priv hm'.2.2.2.1.2 hpf' hc' hown' hty hus hw hjN fun o h1 h2 => ?_
      obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
      exact ⟨t, m, ht, hm, hl, hv⟩
    · exact riniMemA_old hL hR hP hK hfr (hwl.2 (noPfr E0)) rfl (hri l) hpf' (hsto l c hc' hpf')
        (by rw [← htid]; exact hown') (fun h => hns' (hsn l h)) hty hus hw hjN hall

/-- **`AnchR` with the environment kept**: the result's non-promise messages lie where `WrLocG` says. -/
theorem anchR_same {g : G} {E0 E : TEnv} {s s' : St} (h : AnchR E0 E0 E s) (hfr : FreshLP g E s)
    (hm' : MemInv g E s') (hwl : WrLocG g E E s s') : AnchR E0 E0 E s' :=
  by
  obtain ⟨hA, hL, hR, hP, hK⟩ := h
  refine ⟨hA, hL, ?_, fun l c N e us f h1 h2 h3 h4 h5 h6 h7 => Nat.lt_of_lt_of_le (hP l c N e us f h1 h2 h3 h4 h5 h6 h7) hwl.1, hK⟩
  intro l c N e us j hc hown hns hty hus hw hjN hall
  by_cases hpf : E.pfr l = none
  · refine riniMem_priv hm'.2.2.2.1.2 hpf hc hown hty hus hw hjN fun o h1 h2 => ?_
    obtain ⟨t, m, ht, hm, hl, hv, -⟩ := hall o h1 h2
    exact ⟨t, m, ht, hm, hl, hv⟩
  · exact riniMemA_old hL hR hP hK hfr (hwl.2 (noPfr E0)) rfl (Nat.le_refl _) hpf hc hown hns hty hus hw hjN hall

/-- **The anchor step** of a step conclusion: from source `E`, `s` to result `E'`, `s'`, every anchor
`E0` of the source (`Ext` and `AnchR`) is one of the result, given the source's fresh labels and the
step's write locations (when a `bufInit` leaves its count at `E'`). -/
def AnchStep (g : G) (th : TTh) (E E' : TEnv) (s s' : St) : Prop :=
  ∀ E0, Ext E0 E → AnchR E0 E0 E s → FreshLP g E s → MemInv g E' s' → (BumpIf th E' → WrLocG g E E' s s') →
    Ext E0 E' ∧ AnchR E0 E0 E' s'

/-- **(iii) `AnchStep` along an environment change** meeting `anchR_gen`'s side conditions. -/
theorem anchStep_gen {g : G} {th : TTh} {E E' : TEnv} {s s' : St} (hX : Ext E E') (hb : BumpIf th E') (hsto : ∀ l c, E'.sto l = some c → E'.pfr l ≠ none → E.sto l = some c)
    (hini : ∀ l, E.sto l ≠ none → E'.ini l ≤ max (E.ini l) (E'.rini l))
    (hnew : ∀ l, E.sto l = none → E'.sto l ≠ none → (∃ c, E'.sto l = some c ∧ c.owner = some E'.tid) ∧ E'.pfr l = none) : AnchStep g th E E' s s' :=
  fun _ hx0 hA hfr hm' hw => ⟨Ext_trans hx0 hX, anchR_gen hA hfr hm' (hw hb) (fun l c h => hx0.2.2.2.2.1 l c h) hsto
    hX.2.2.2.2.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2.2.2.1 hX.rini hini hnew⟩

/-- **(iii′) An allocation at a fresh label** `lbl` (no frontier there, nothing else changed). -/
theorem anchStep_fresh {g : G} {th : TTh} {E E' : TEnv} {s s' : St} {lbl : AllocLabel} (hX : Ext E E')
    (hb : BumpIf th E') (hsto : ∀ l, l ≠ lbl → E'.sto l = E.sto l) (hpf : E'.pfr lbl = none)
    (hini : ∀ l, l ≠ lbl → E'.ini l = E.ini l) (h0 : E.sto lbl = none)
    (hpv : (∃ c, E'.sto lbl = some c ∧ c.owner = some E'.tid) ∧ E'.pfr lbl = none) : AnchStep g th E E' s s' :=
  anchStep_gen hX hb
    (fun l c h hp => by
      by_cases hl : l = lbl
      · subst hl; exact absurd hpf hp
      · rw [← hsto l hl]; exact h)
    (fun l hl => by
      have hne : l ≠ lbl := fun e => hl (by rw [e]; exact h0)
      rw [hini l hne]; exact Nat.le_max_left _ _)
    (fun l hs hl => by
      by_cases e : l = lbl
      · subst e; exact hpv
      · exact absurd ((hsto l e).trans hs) hl)

/-- **(i) The environment kept**, memory written (a non-`bufInit` step). -/
theorem anchStep_same {g : G} {th : TTh} {E : TEnv} {s s' : St} (hnb : ∀ E1, BumpIf th E1) :
    AnchStep g th E E s s' :=
  fun _ hx0 hA hfr hm' hw => ⟨hx0, anchR_same hA hfr hm' (hw (hnb E))⟩

/-- **(i′) The environment and every non-promise message kept.** -/
theorem anchStep_keep {g : G} {th : TTh} {E : TEnv} {s s' : St}
    (hmem : ∀ (t : Nat) (m : Msg), t ∉ s'.promises → s'.mem[t]? = some m → t ∉ s.promises ∧ s.mem[t]? = some m)
    (hsz : s.mem.size ≤ s'.mem.size) : AnchStep g th E E s s' :=
  fun _ hx0 hA _ _ _ => ⟨hx0, anchR_keep hA hmem hsz⟩

/-- `anchR_keep` with memory and promises equal. -/
theorem anchR_eqs {E0 E : TEnv} {s s' : St} (h : AnchR E0 E0 E s) (e1 : s'.mem = s.mem)
    (e2 : s'.promises = s.promises) : AnchR E0 E0 E s' :=
  anchR_keep h (fun _ _ ht hm => ⟨by rw [← e2]; exact ht, by rw [← e1]; exact hm⟩) (by rw [e1]; exact Nat.le_refl _)

/-- `anchStep_keep` with memory and promises equal. -/
theorem anchStep_eqs {g : G} {th : TTh} {E : TEnv} {s s' : St} (e1 : s'.mem = s.mem)
    (e2 : s'.promises = s.promises) : AnchStep g th E E s s' :=
  fun _ hx0 hA _ _ _ => ⟨hx0, anchR_eqs hA e1 e2⟩

/-- **(ii) The environment grown, `sto` and `ini` kept**, memory and promises equal (a `publish`). -/
theorem anchStep_shrink {g : G} {th : TTh} {E E1 : TEnv} {s s' : St} (hX : Ext E E1) (hsto : E1.sto = E.sto)
    (hini : E1.ini = E.ini) (e1 : s'.mem = s.mem) (e2 : s'.promises = s.promises) : AnchStep g th E E1 s s' :=
  fun _ hx0 hA hfr hm' _ => ⟨Ext_trans hx0 hX, anchR_gen hA hfr hm'
    ⟨by rw [e1]; exact Nat.le_refl _, fun _ _ _ ht hm => .inl ⟨by rw [← e2]; exact ht, by rw [← e1]; exact hm⟩⟩
    (fun l c h => hx0.2.2.2.2.1 l c h) (fun _ _ h _ => by rw [← hsto]; exact h)
    hX.2.2.2.2.2.2.1 hX.2.2.2.1 hX.2.2.2.2.2.2.2.1 hX.rini (fun _ _ => by rw [hini]; exact Nat.le_max_left _ _)
    (fun l h0 hl => absurd (by rw [hsto]; exact h0) hl)⟩

/-- A step whose term is a `let` of an op other than `bufInit` leaves no count. -/
theorem bumpIf_nb {th : TTh} {x : String} {op : Op} {e : Expr} (h : th.term = .let_ x op e)
    (hop : ∀ b i v, op ≠ .bufInit b i v := by intro _ _ _ h; cases h) : ∀ E1, BumpIf th E1 := by
  intro _ _ b i v _ ht
  rw [h] at ht
  simp only [Expr.let_.injEq] at ht
  exact (hop b i v ht.2.1).elim

/-- A step whose term is not a `let` leaves no count. -/
theorem bumpIf_nl {th : TTh} (h : ∀ x op e, th.term ≠ .let_ x op e) : ∀ E1, BumpIf th E1 :=
  fun _ x _ _ _ e ht => (h x _ e ht).elim

/-- A `bufInit`'s count from the counts at its evaluated buffer and index. -/
theorem bufBump {th : TTh} {E' : TEnv} {x : String} {b i v : At} {e : Expr} {rt rti : Ty} {w wi : Word}
    {ad : Address} {n : Nat} (hterm : th.term = .let_ x (.bufInit b i v) e) (hea : evalAt th.env b = some (rt, [w]))
    (hwv : w.val = .loc ad 0) (hei : evalAt th.env i = some (rti, [wi])) (hn : numOf [wi] = some n)
    (h1 : n + 1 ≤ E'.ini ad.label) (h2 : n + 1 ≤ E'.rini ad.label) : BumpIf th E' := by
  refine bumpIf_of hterm fun rt' w' ad' rti' wi' n' he' hw' hei' hn' => ?_
  rw [hea] at he'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at he'
  obtain ⟨-, rfl⟩ := he'
  rw [hwv] at hw'
  cases hw'
  rw [hei] at hei'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hei'
  obtain ⟨-, rfl⟩ := hei'
  rw [hn] at hn'
  cases hn'
  exact ⟨h1, h2⟩

/-- A `bumpIni` raises `ini` only up to the equally bumped `rini`. -/
theorem bumpIni_iniLe (ini rini : AllocLabel → Nat) (l0 : AllocLabel) (m : Nat) (l : AllocLabel) :
    bumpIni ini l0 m l ≤ max (ini l) (bumpIni rini l0 m l) := by
  by_cases hl : l = l0
  · subst hl; rw [bumpIni_self, bumpIni_self]; omega
  · rw [bumpIni_other _ _ _ _ hl, bumpIni_other _ _ _ _ hl]; exact Nat.le_max_left _ _

/-- `Ext` of the code views. -/
theorem ext_CE {η η' : TEnv} (hx : Ext η η') : Ext (CE η) (CE η') :=
  ⟨Coh_CE η', rfl, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2.1, hx.2.2.2.2.2.2.1, hx.2.2.2.2.2.2.2.1,
    hx.2.2.2.2.2.2.2.2.1, Nat.le_refl _, CohR_CE η', hx.rini⟩

/-- A resourceful frame's environment is a code view, hence `Ext` of itself. -/
theorem ext_RE {p : Prog} {E : TEnv} {th : TTh} {Tot : Res} (h : ThInvRE p E th Tot) : Ext E E := by
  obtain ⟨ρ, η, cx, Rf, Rs, rfl, -⟩ := h
  exact Ext_refl (Coh_CE η) (CohR_CE η)

/-- **The dispatchers' write-location hypothesis** (`WrIniC.wrA` + `wrLocA2_of`). -/
theorem wrHyp [WrIniC] {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {r : Memory × List Ts × TTh} {E' : TEnv} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hsc : ScopeD th.σs cx th.term) (hvr : ∀ (a : At) (rt : Ty) (ws : List Word) (w : Word), evalAt th.env a = some (rt, ws) → w ∈ ws → w.view ≤ w.rts)
    (hr : r ∈ tstep g mem pairs th) :
    BumpIf th E' → WrLocG g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) :=
  fun hb => ⟨(TermLiveProps.tstep_ext g mem pairs th r hr).mem.size, wrLocA2_of (WrIniC.wrA hE hT htv hi hm hsc hvr hr) hb⟩


/-- (copy of W/TermNoHoldA `publish_own`) A typed `publish` names one of the thread's own cells. -/
theorem publish_own_cell {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {x : String} {a : At}
    {e : Expr} {rt : Ty} {ws : List Word} {ad : Address}
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hterm : th.term = .let_ x (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad 0]) : ∃ c, η.sto ad.label = some c ∧ c.owner = some η.tid := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
  cases hop with
  | publish hu hsh hb =>
    obtain ⟨u, c₁, hu, -, -⟩ : ∃ u c₁, cx.use a = .ok (.ptr .own u, c₁) ∧
        Ty.sharedOKIn c₁.ke (.ptr .pub u) = true ∧ c₁.bind x (.ptr .pub u) = .ok _ := ⟨_, _, hu, hsh, hb⟩
    obtain ⟨-, rt', ws', hea', hv, -⟩ := use_FInv hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VR] at hv
    obtain ⟨ad', c, hws', -, hsto, -, hmode, -⟩ := hv
    rw [hws] at hws'
    simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
    subst hws'
    exact ⟨c, hsto, hmode⟩
  | publishBuf hu hsh hb =>
    obtain ⟨n, k, u, c₁, hu, -, -⟩ : ∃ n k u c₁, cx.use a = .ok (.refine (.loc .own (.array n u)) (.ini k), c₁) ∧
        Ty.sharedOKIn c₁.ke (.loc .pub (.array n u)) = true ∧
        c₁.bind x (.refine (.loc .pub (.array n u)) (.ini k)) = .ok _ := ⟨_, _, _, _, hu, hsh, hb⟩
    obtain ⟨-, rb, wsb, hea', hvb, -⟩ := use_FInv hu hi
    rw [hea] at hea'
    cases hea'
    simp only [VR] at hvb
    obtain ⟨hv, -⟩ := hvb
    rcases hv with ⟨hnull, -, -⟩ | ⟨ad', c, U, hws', hsto, -, -, hmode, -⟩
    · rw [hws] at hnull; simp at hnull
    · rw [hws] at hws'
      simp only [List.cons.injEq, WeakMem.Val.loc.injEq, and_true] at hws'
      subst hws'
      exact ⟨c, hsto, hmode⟩

/-- **The own-key bound at `x`** (F1): frame plus private holding carry `own x` at most `n` times. -/
def OwnXLe (p : Prog) (k : Promises.Knobs) (arch : Arch) (E0 : TEnv) (i : Nat) (x : AllocLabel) (n : Nat)
    (c : Cfg) :
    Prop :=
  ∃ th E Tot HP, c.ths[i]? = some th ∧ ThInvRE p E th Tot ∧
    MemInv (gOf p k arch c i) E (stOf c.mem c.pairs th) ∧ MemHeldP E (stOf c.mem c.pairs th) HP ∧
    (gOf p k arch c i).boxFence = true ∧ StoNIE E ∧ E.sto x ≠ none ∧ Tot (.own x) + HP (.own x) ≤ n ∧
    Ext E0 E ∧ AnchR E0 E0 E (stOf c.mem c.pairs th)

theorem OwnXLe.mono {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n m : Nat}
    {c : Cfg} (h : OwnXLe p k arch E0 i x n c) (hnm : n ≤ m) : OwnXLe p k arch E0 i x m c :=
  let ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hs, hle, hx, hA⟩ := h
  ⟨th, E, Tot, HP, hth, hT, hm, hP, hb, hn, hs, Nat.le_trans hle hnm, hx, hA⟩

/-- At `n = 0` the frame part carries no `own x`. -/
theorem OwnXLe.rf_zero {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c : Cfg}
    (h : OwnXLe p k arch E0 i x 0 c) :
    ∃ th, c.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf (.own x) = 0 := by
  obtain ⟨th, E, Tot, HP, hth, ⟨ρ, η, cx, Rf, Rs, -, hE, hTy, -, hFI, hsum, -⟩, -, -, -, -, -, hle, -⟩ := h
  have h3 := congrArg (fun R : Res => R (.own x)) hsum
  simp only [Res.add_apply] at h3
  exact ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy.1, hFI, by omega⟩

/-- **No own-mode use reaches `x`** at `n = 0` (`use_own_ne`). -/
theorem OwnXLe.use_ne {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {c : Cfg}
    (h : OwnXLe p k arch E0 i x 0 c) :
    ∃ th, c.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x := by
  obtain ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy, hFI, h0⟩ := h.rf_zero
  exact ⟨th, hth, ρ, η, cx, Rf, Rs, hE, hTy, hFI, fun a t c₁ rt ws ad g hu ht hea hws =>
    use_own_ne hu hFI hE ht h0 hea hws⟩

/-! ## The start -/

theorem lt_size_of {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) : i < c.ths.size := by
  rcases Nat.lt_or_ge i c.ths.size with h | h
  · exact h
  · rw [Array.getElem?_eq_none h] at hth; cases hth

/-- `x` is in thread `i`'s cut (any `seen`). -/
theorem cut_sto_ne {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {x : AllocLabel} {cl : Cell}
    (hsto : Eg.sto x = some cl) (hin : cl.owner = some i ∨ Eg.pfr x ≠ none) : (Cut Eg i S).sto x ≠ none := by
  have : cutSto Eg i x = some cl := by
    refine cutSto_some.2 ⟨hsto, hin.imp id fun h => ?_⟩
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 h
    exact ⟨f, hf⟩
  rw [Cut_sto, this]
  exact fun h => by cases h

/-- (runAgree) **`OwnXLe` at any bound of the thread's own-key count** at a `SysInvN`
configuration, at a cell `x` in thread `i`'s cut: witness the cut, `Tot i`, `HP i`. -/
theorem ownXLe_start_le {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {x : AllocLabel} {cl : Cell} {n : Nat} {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hsto : Eg.sto x = some cl) (hin : cl.owner = some i ∨ Eg.pfr x ≠ none)
    (hle : (Tot i + HP i) (.own x) ≤ n) : OwnXLe p k arch (Cut Eg i S) i x n c := by
  obtain ⟨hRE, -, hm, hP, -, -⟩ := hS
  simp only [Res.add_apply] at hle
  exact ⟨th, Cut Eg i S, Tot i, HP i, hth, hRE, hm, hP, hinv.bf, stoNIE_cut hinv.stoNI, cut_sto_ne hsto hin, hle, ext_RE hRE,
    anchR_start hm (hinv.riniCoh i th S hth) (fun l cl f hs hp => hinv.frlt l cl f (cutSto_sub hs) hp)⟩

/-- **`OwnXLe` at `n = 1`** at a `SysInvN` configuration (`ownNet_one`), at a cell `x` in thread
`i`'s cut (its own cell, or a shared one): witness the cut, `Tot i`, `HP i`. -/
theorem ownXLe_start {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {x : AllocLabel} {cl : Cell} {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db)
    (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) (hsto : Eg.sto x = some cl) (hin : cl.owner = some i ∨ Eg.pfr x ≠ none) :
    OwnXLe p k arch (Cut Eg i S) i x 1 c :=
  ownXLe_start_le hinv hth hS hsto hin
    (Nat.le_trans (Nat.le_add_right _ _) (TermOwnNet.ownNet_one hinv x (lt_size_of hth)))

/-- **`OwnXLe` at `n = 0`** at a published cell (`SysInvN.ownPub`). -/
theorem ownXLe_start_pub {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {x : AllocLabel} {S : AllocLabel → Prop} (hinv : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hth : c.ths[i]? = some th)
    (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S)
    (hpub : Eg.pubd x) (hsto : Eg.sto x ≠ none) : OwnXLe p k arch (Cut Eg i S) i x 0 c := by
  obtain ⟨hpf, hz⟩ := hinv.ownPub x hpub
  have hzi := (hz hsto).1 i th hth
  obtain ⟨hRE, -, hm, hP, -, -⟩ := hS
  simp only [Res.add_apply] at hzi
  obtain ⟨cl, hcl⟩ := Option.ne_none_iff_exists'.1 hsto
  exact ⟨th, Cut Eg i S, Tot i, HP i, hth, hRE, hm, hP, hinv.bf, stoNIE_cut hinv.stoNI, cut_sto_ne hcl (.inr hpf), by omega, ext_RE hRE,
    anchR_start hm (hinv.riniCoh i th S hth) (fun l cl f hs hp => hinv.frlt l cl f (cutSto_sub hs) hp)⟩

/-! ## No own key at a cell with a frontier (N route) -/

/-- A value of an own-free type carries no own key. -/
theorem valOfR_own_zero {E : TEnv} {T : Ty} {ws : List Word} {R : Res} (hT : Ty.noOwnIn [] T = true)
    (h : ValOfR E T ws R) (l : Nat) : R (.own l) = 0 :=
  TermBlkZ.VRR_own_zero l T [] (CE E.unsee) (fun _ => 0) (shp T) ws R hT (fun _ _ _ _ h => False.elim h)
    (fun _ _ _ _ h => False.elim h) h.1

/-- A cell of an own-free type carries no own key. -/
theorem cellOKR_own_zero {E : TEnv} {n nr : Nat} {T : Ty} {vals : List Word} {R : Res}
    (hT : Ty.noOwnIn [] T = true) (h : CellOKR E n nr T vals R) (l : Nat) : R (.own l) = 0 := by
  rcases h with ⟨-, h⟩ | ⟨N, e, us, Rs, hTe, -, -, -, hlen, rfl, hj⟩
  · exact valOfR_own_zero hT h l
  · subst hTe
    have he := noOwn_array hT
    refine Classical.byContradiction fun h0 => ?_
    obtain ⟨Rj, hm, h1⟩ := TermOwnKey.sum_ne h0
    obtain ⟨j, hjl, hjv⟩ := List.getElem_of_mem hm
    have hj' := hj j Rj (by omega) (by rw [List.getElem?_eq_getElem hjl, hjv])
    by_cases hz : nr ≤ j ∧ nWords us = 0
    · rw [hj'.1 hz.1 hz.2] at h1; exact h1 rfl
    · have hor : j < nr ∨ 0 < nWords us := by
        rcases Nat.lt_or_ge j nr with h | h
        · exact .inl h
        · right; rcases Nat.eq_zero_or_pos (nWords us) with h' | h'
          · exact absurd ⟨h, h'⟩ hz
          · exact h'
      exact h1 (valOfR_own_zero he (hj'.2 hor) l)

/-- **The holding at a cell with a frontier carries no own key** (`PubCpl`'s `noOwnIn`). -/
theorem heldEntry_pfr_own_zero {g : G} {E : TEnv} {s : St} {l : AllocLabel} {f : Ts} {R : Res}
    (hm : MemInv g E s) (hf : E.pfr l = some f) (h : HeldEntry E s l R) (x : Nat) : R (.own x) = 0 := by
  obtain ⟨hn, hs⟩ := h
  cases hc : E.sto l with
  | none => rw [hn hc]; rfl
  | some cl =>
    obtain ⟨vals, -, hok⟩ := hs cl hc
    exact cellOKR_own_zero (MemInv_noOwnT hm hc hf) hok x

/-- A holding on labels with frontiers carries no own key. -/
theorem memHeldOn_pfr_own_zero {g : G} {Q : AllocLabel → Prop} {E : TEnv} {s : St} {H : Res}
    (hm : MemInv g E s) (hQ : ∀ l, Q l → ∃ f, E.pfr l = some f) (h : MemHeldOn Q E s H) (x : Nat) :
    H (.own x) = 0 := by
  obtain ⟨L, Rl, -, -, hq, rfl, hR⟩ := h
  refine Classical.byContradiction fun h0 => ?_
  obtain ⟨R, hmR, h1⟩ := TermOwnKey.sum_ne h0
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hmR
  obtain ⟨f, hf⟩ := hQ l (hq l hl)
  exact h1 (heldEntry_pfr_own_zero hm hf (hR l hl) x)

/-- **The shared holding carries no own key.** -/
theorem memHeldS_own_zero {g : G} {E : TEnv} {s : St} {H : Res} (hm : MemInv g E s) (h : MemHeldS E s H)
    (x : Nat) : H (.own x) = 0 :=
  memHeldOn_pfr_own_zero hm (fun _ h => h) h x

/-- **A holding's own key is at a private cell's entry**: splitting off the shared part
(`MemHeld_splitOn`), the own key of `x` lives in the private (no-frontier) part. -/
theorem memHeld_own_priv {g : G} {E : TEnv} {s : St} {H : Res} (hm : MemInv g E s) (h : MemHeld E s H)
    (x : Nat) : ∃ HP, MemHeldOn (fun l => E.pfr l = none) E s HP ∧ H (.own x) = HP (.own x) := by
  obtain ⟨H1, H2, rfl, h1, h2⟩ := MemHeld_splitOn (fun l => E.pfr l = none) h
  have z := memHeldOn_pfr_own_zero hm (fun l hl => Option.ne_none_iff_exists'.1 hl) h2 x
  refine ⟨H1, h1, ?_⟩
  simp only [Res.add_apply, z, Nat.add_zero]

/-! ## The key projection (P route) -/

/-- **The per-step projection at one key, bound `n`**: from a step bound `Tot' + H' ≤ Rf + Rs + H`. -/
theorem proj_own_le {Tot' H' Rf Rs H : Res} {x : AllocLabel} {n : Nat} (hle : Tot' + H' ≤ Rf + Rs + H)
    (h0 : (Rf + Rs) (.own x) + H (.own x) ≤ n) : Tot' (.own x) + H' (.own x) ≤ n := by
  have h1 := Res.le_def.1 hle (.own x)
  simp only [Res.add_apply] at h1 h0
  omega

/-- The projection with frame terms `A`, `B` on either side, `B` own-free (`tstepMC` shape). -/
theorem proj_own_le4 {Tot' H' A B Rf Rs H : Res} {x : AllocLabel} {n : Nat} (hle : Tot' + H' + A ≤ Rf + Rs + H + B)
    (h0 : (Rf + Rs) (.own x) + H (.own x) ≤ n) (hB : B (.own x) = 0) : Tot' (.own x) + H' (.own x) ≤ n := by
  have h1 := Res.le_def.1 hle (.own x)
  simp only [Res.add_apply] at h1 h0
  omega

/-- A full holding's private part is at most it at every key. -/
theorem memHeld_priv_le {E : TEnv} {s : St} {H : Res} (h : MemHeld E s H) :
    ∃ HP, MemHeldP E s HP ∧ ∀ key, HP key ≤ H key := by
  obtain ⟨H1, H2, rfl, h1, -⟩ := MemHeld_splitOn (Priv E) h
  exact ⟨H1, h1, fun key => by simp only [Res.add_apply]; omega⟩

/-! ## Shared helper: the resourceful frame at an extended environment -/

/-- **`ThInvRE` moves along an extension** to any code view `E'` (`CE E' = E'`), e.g. the footprint
environment of `tstep_footprint(W)`, where `MemInv'` holds.  Frame-only steps: `tstepR_step` gives
`ThInvRE` at the old `CE η`; this lifts it to `E'` (same `Tot'`). -/
theorem thInvRE_ext {p : Prog} {E E' : TEnv} {th : TTh} {Tot : Res} (h : ThInvRE p E th Tot) (hx : Ext E E')
    (hE' : CE E' = E') : ThInvRE p E' th Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, rfl, hE, hTy, htv, hFI, hsum⟩ := h
  have hext : Ext η (η.withSto E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini) :=
    Ext_withSto hE.2.1 hx.2.2.2.2.1 hx.2.2.2.2.2.1 hx.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.1 hx.2.2.2.2.2.2.2.2.1
      (Nat.le_refl _) E'.fp E'.rini hx.rini
  refine ⟨ρ, η.withSto E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini, cx, Rf, Rs, ?_,
    ⟨hE.1, Coh_withSto hE.2.1 _ _ _ _ _ _ _ _, CohR_withSto hE.2.1 _ _ _ _ _ _ _ _⟩, hTy, htv,
    FInvR_ext hE.2.1 hE.2.2 hext hFI, hsum⟩
  have e1 : E'.prog = η.prog := hx.2.2.1
  have e2 : E'.tid = η.tid := hx.2.2.2.1
  rw [← hE']
  simp only [CE, TEnv.withSto, e1, e2]

/-! ## The publish of `x` (n = 1 → 0): obligation for package 4

`ownXLe_publish` (via `publish_ownZero`, needing full `MemHeld`/`PromCrK`/`OwnSide`) is withdrawn: it
reintroduced F1.  The private form below is the publish case at `x = ad.label` with the sharp bound:
the frame consumes `ownW .own ws = one (own x)`; `Tot (own x) ≥ 1` gives `HP (own x) = 0`; `x` leaves
`Priv`, other private entries are unchanged (publish leaves memory unchanged). -/

/-- **The publish step of `x`** (n = 1 → 0), private form; proved in `TermOwnK4`. -/
def OwnXPub1 (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) : Prop :=
  ∀ (E0 : TEnv) (c c' : Cfg) (th : TTh) (y : String) (a : At) (e : Expr) (rt : Ty) (ws : List Word) (ad : Address) (g' : Nat),
    ScopeAt p i c → NoHoldPubA p k arch E0 E0 i c → TermViewInv.ViewInv c → OwnXLe p k arch E0 i x 1 c →
    c' ∈ threadSteps p k arch c i → Certified p k arch c' i → c.ths[i]? = some th →
    th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g'] →
    ad.label = x → OwnXLe p k arch E0 i x 0 c'

/-! ## The run (fills the step obligations) -/

/-- The thread-step obligation (F2, `invAtX_stepW` shape): window at the source only. -/
def OwnXStepT (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 c0', ScopeAt p i c0 → NoHoldPubA p k arch E0 E0 i c0 → TermViewInv.ViewInv c0 → OwnXLe p k arch E0 i x n c0 →
    c0' ∈ threadSteps p k arch c0 i → Certified p k arch c0' i → OwnXLe p k arch E0 i x n c0'

/-- The promise-step obligation (F2). -/
def OwnXStepP (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 a v w, OwnXLe p k arch E0 i x n c0 → w < c0.mem.size → Certified p k arch (promise c0 i a v w) i →
    OwnXLe p k arch E0 i x n (promise c0 i a v w)

/-- **`OwnXLe` along a certified solo run** (`run_ind_win`, `Q = ScopeAt ∧ NoHoldPub3`).
Do not use for G-c (`certWinC` supplies `hQ`; circular). -/
theorem ownXLe_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel} {n : Nat}
    {c c2 : Cfg} (hT : OwnXStepT p k arch i x n) (hPr : OwnXStepP p k arch i x n)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0 ∧ NoHoldPubA p k arch E0 E0 i c0)
    (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLe p k arch E0 i x n c) (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) :
    OwnXLe p k arch E0 i x n c2 :=
  (run_ind_win (Q := fun c0 => ScopeAt p i c0 ∧ NoHoldPubA p k arch E0 E0 i c0 ∧ TermViewInv.ViewInv c0)
    (fun c0 h1 h2 _ => ⟨(hQ c0 h1 h2).1, (hQ c0 h1 h2).2, TermViewInv.viewInv_solo hvI h1⟩)
    (fun c0 c0' _ hI hq hs hc => hT E0 c0 c0' hq.1 hq.2.1 hq.2.2 hI hs hc)
    (fun c0 a v w _ hI hw hc => hPr E0 c0 a v w hI hw hc) h0 h hc2).1

/-! ## Package split of the thread-step obligation (the packages deliver, `TermOwnK5` assembles) -/

/-- The package owning an op: 2 = own-cell loads/stores/xchg, 3 = buffer ops, 4 = word/pub/cas/
ldp/stp/sum ops, 1 = everything else (frame/control). -/
def opPkg : Op → Nat
  | .load _ _ | .store _ _ _ _ | .xchg _ _ | .loadAt _ _ | .loadAtF _ _ _ => 2
  | .bufInit _ _ _ | .xchgAt _ _ _ | .xchgAtF _ _ _ _ | .stl _ _ _ | .stlw _ _ _ _ | .ldl _ _
  | .ldlw _ _ _ | .new _ | .newBuf _ _ => 3
  | .inl _ _ | .inr _ _ | .publish _ | .intoRgn _ _ | .mkWord _ _ _ _ | .mkWord2 _ _ _ _ _
  | .mkEPair _ _ _ _ | .mkTicket _ _ _ _ _ | .claim _ _ | .fetch _ _ _ _ _ | .ldp _ _ _ _
  | .stp _ _ _ _ _ => 4
  | _ => 1

/-- The package owning a thread's next term (by its head). -/
def exprPkg : Expr → Nat
  | .let_ _ op _ => opPkg op
  | .case _ _ _ _ _ | .cas _ _ _ _ _ _ _ _ | .casp _ _ _ _ _ _ _ _ _ _ => 4
  | _ => 1

theorem exprPkg_cases (e : Expr) : exprPkg e = 1 ∨ exprPkg e = 2 ∨ exprPkg e = 3 ∨ exprPkg e = 4 := by
  cases e with
  | let_ x op e => cases op <;> simp [exprPkg, opPkg]
  | _ => simp [exprPkg]

/-- **Package `q`'s deliverable**: `OwnXStepT` at sources whose thread-`i` term is in package `q`. -/
def OwnXStepPkg (p : Prog) (k : Promises.Knobs) (arch : Arch) (i : Nat) (x : AllocLabel) (n q : Nat) : Prop :=
  ∀ (E0 : TEnv) c0 c0' th, c0.ths[i]? = some th → exprPkg th.term = q →
    ScopeAt p i c0 → NoHoldPubA p k arch E0 E0 i c0 → TermViewInv.ViewInv c0 → OwnXLe p k arch E0 i x n c0 →
    c0' ∈ threadSteps p k arch c0 i → Certified p k arch c0' i → OwnXLe p k arch E0 i x n c0'

theorem mem_threadSteps_th {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) : ∃ th, c.ths[i]? = some th := by
  unfold threadSteps at h
  cases hth : c.ths[i]? with
  | none => rw [hth] at h; exact absurd h List.not_mem_nil
  | some th => exact ⟨th, rfl⟩

/-- **Assembly of the thread-step obligation** from the four package deliverables. -/
theorem ownXStepT_of_pkgs {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} {n : Nat}
    (h1 : OwnXStepPkg p k arch i x n 1) (h2 : OwnXStepPkg p k arch i x n 2)
    (h3 : OwnXStepPkg p k arch i x n 3) (h4 : OwnXStepPkg p k arch i x n 4) : OwnXStepT p k arch i x n := by
  intro E0 c0 c0' hsc hw hvI hI hs hc
  obtain ⟨th, hth⟩ := mem_threadSteps_th hs
  rcases exprPkg_cases th.term with e | e | e | e
  · exact h1 E0 c0 c0' th hth e hsc hw hvI hI hs hc
  · exact h2 E0 c0 c0' th hth e hsc hw hvI hI hs hc
  · exact h3 E0 c0 c0' th hth e hsc hw hvI hI hs hc
  · exact h4 E0 c0 c0' th hth e hsc hw hvI hI hs hc

end TermOwnX2

#print axioms TermOwnX2.run_ind_win
#print axioms TermOwnX2.OwnXLe.mono
#print axioms TermOwnX2.anchR_gen
#print axioms TermOwnX2.anchStep_same
#print axioms TermOwnX2.wrHyp
#print axioms TermOwnX2.ownXLe_start_le
#print axioms TermOwnX2.OwnXLe.use_ne
#print axioms TermOwnX2.ownXLe_start
#print axioms TermOwnX2.ownXLe_start_pub
#print axioms TermOwnX2.valOfR_own_zero
#print axioms TermOwnX2.cellOKR_own_zero
#print axioms TermOwnX2.heldEntry_pfr_own_zero
#print axioms TermOwnX2.memHeldOn_pfr_own_zero
#print axioms TermOwnX2.memHeldS_own_zero
#print axioms TermOwnX2.memHeld_own_priv
#print axioms TermOwnX2.proj_own_le
#print axioms TermOwnX2.proj_own_le4
#print axioms TermOwnX2.memHeld_priv_le
#print axioms TermOwnX2.cut_sto_ne
#print axioms TermOwnX2.stoNIE_cut
#print axioms TermOwnX2.stoNIE_efoot
#print axioms TermOwnX2.thInvRE_ext
#print axioms TermOwnX2.ownXLe_run
#print axioms TermOwnX2.exprPkg_cases
#print axioms TermOwnX2.ownXStepT_of_pkgs

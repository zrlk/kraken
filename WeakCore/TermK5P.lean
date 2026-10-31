import WeakCore.TermK5Defs
import WeakCore.TermK5V

/-!
# TermK5P: the producers' step lemmas for `PfrProvE` (S1b, stage (iii))

The typed runs (`TermIni.solo_typedXHP`, `TermNoHold.solo_typedXFP`) carry
`TermK5Defs.PfrProvE` along `run_inv`, choosing the step's ghosts per step:
`g.pf := PubAt th` (a step changes a frontier of a `Σ` cell only at a `publish` naming it, `PfrG`)
and `g.zf ⊇ PubZ E0 E` (a start own cell published in the run keeps its count, `IniFixZ`).
`tstep_footprintK` is the footprint with the published frontier set (`TermStep.tstep_footprintP`);
`pfrProv_thread`/`pfrProv_prom` keep `PfrProvE` along a thread/promise step.
-/

namespace TermK5P

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermTyped TermGlob TermOwnG0Defs TermK5Defs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (S1b) The start own cells unpublished at the start and published in `E`. -/
def PubZ (E0 E : TEnv) (l : AllocLabel) : Prop :=
  ∃ c F, E0.sto l = some c ∧ c.owner = some E0.tid ∧ E0.pfr l = none ∧ E.pfr l = some F

theorem soloNP_snocT {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {r : AllocLabel} {c c0 c0' : Cfg}
    (h : SoloNP p k arch i r c c0) (hs : c0' ∈ threadSteps p k arch c0 i)
    (hn : ∀ th, c0.ths[i]? = some th → ¬ PubAt th r) : SoloNP p k arch i r c c0' := by
  revert hs hn
  induction h with
  | refl => intro hs hn; exact .thread hs hn (.refl _)
  | thread hs1 hn1 _ ih => intro hs hn; exact .thread hs1 hn1 (ih hs hn)
  | prom a v w hw _ ih => intro hs hn; exact .prom a v w hw (ih hs hn)
  | ext hs1 _ ih => intro hs hn; exact .ext hs1 (ih hs hn)

theorem soloNP_snocP {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {r : AllocLabel} {c c0 : Cfg}
    {a : Address} {v : WeakMem.Val} {w : Ts} (h : SoloNP p k arch i r c c0) (hw : w < c0.mem.size) :
    SoloNP p k arch i r c (promise c0 i a v w) := by
  revert hw
  induction h with
  | refl => intro hw; exact .prom a v w hw (.refl _)
  | thread hs1 hn1 _ ih => intro hw; exact .thread hs1 hn1 (ih hw)
  | prom a1 v1 w1 hw1 _ ih => intro hw; exact .prom a1 v1 w1 hw1 (ih hw)
  | ext hs1 _ ih => intro hw; exact .ext hs1 (ih hw)

/-- (S1b) The start: nothing published yet. -/
theorem pfrProvE_start (p : Prog) (k : Promises.Knobs) (arch : Arch) (j : Nat) (H : AllocLabel → Nat → Ts → Prop)
    (E0 : TEnv) (st : Cfg) : PfrProvE p k arch j H E0 st st E0 :=
  fun _ _ _ _ h0 => .inl ⟨h0, .refl _⟩

/-- (S1b) **The footprint with the publish recorded**: `tstep_footprint` at a thread step whose
ghost `g.pf` admits the `publish` labels (`hgp`); at a `publish` naming `l` the new environment has
a frontier at `l` (`tstep_footprintP`; off a `publish` there is no such `l`). -/
theorem tstep_footprintK {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hZ : ∀ l, BufInitOn th l → ¬ g.zf l) (hgp : ∀ l, PubAt th l → g.pf l) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ ∀ l, PubAt th l → E'.pfr l ≠ none := by
  have hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label :=
    fun y a e rt ws ad h1 h2 h3 => hgp _ ⟨y, a, e, rt, ws, ad, h1, h2, h3, rfl⟩
  by_cases hpub : ∃ x a e, th.term = .let_ x (.publish a) e
  · obtain ⟨x, a, e, hterm⟩ := hpub
    have h := tstep_footprintP (hDy := hDy) (hPb := hPb) (hRP := hRP) (hPS := hPS) hP hsc hT hi hE htv hm hwin hterm
    refine ⟨h.1, fun r hr _ => ?_⟩
    obtain ⟨E', hF, hx, h1, h2, hD⟩ := h.2 r hr
    refine ⟨E', hF, hx, h1, h2, fun l hl => ?_⟩
    obtain ⟨y, a', e', rt, ws, ad, h3, h4, h5, rfl⟩ := hl
    exact hD y a' e' rt ws ad h3 h4 h5
  · have h := tstep_footprint (hDy := hDy) (hZ := ZOK_of_not hZ) (hPb := hPb) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hRP hPS hSub hSig hTy
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', hF, hx, h1, h2⟩ := h.2 r hr hpa
    refine ⟨E', hF, hx, h1, h2, fun l hl => ?_⟩
    obtain ⟨y, a', e', -, -, -, h3, -⟩ := hl
    exact absurd ⟨y, a', e', h3⟩ hpub

/-- (certWin-D) **`tstep_footprintK` with the count a `bufInit` leaves** (`TermTyped.BumpIf`):
`TermTyped.tstep_footprintB` at a `bufInit` (no `publish` label), `tstep_footprintK` elsewhere. -/
theorem tstep_footprintKQ {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hZ : ∀ l, BufInitOn th l → ¬ g.zf l) (hgp : ∀ l, PubAt th l → g.pf l) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ (∀ l, PubAt th l → E'.pfr l ≠ none) ∧
        TermTyped.BumpIf th E' := by
  by_cases hb : ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e
  · obtain ⟨x, bb, ib, v, e, hterm⟩ := hb
    have h := TermTyped.tstep_footprintB (hDy := hDy) hP hT hi hE htv hm (ZOK_of_not hZ) hRP hPS hterm
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', h1, h2, h3, h4, h5⟩ := h.2 r hr hpa
    refine ⟨E', h1, h2, h3, h4, fun l hl => ?_, TermTyped.bumpIf_of hterm h5⟩
    obtain ⟨y, a', e', -, -, -, h6, -⟩ := hl
    rw [hterm] at h6; cases h6
  · have h := tstep_footprintK (hDy := hDy) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hZ hgp hRP hPS hSub hSig hTy
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', h1, h2, h3, h4, h5⟩ := h.2 r hr hpa
    exact ⟨E', h1, h2, h3, h4, h5, fun x bb ib v e ht => (hb ⟨x, bb, ib, v, e, ht⟩).elim⟩

#print axioms TermK5P.tstep_footprintKQ

/-- `tstep_footprintK` with `NewCellSto` of its witness (route (a): the consumers' `tyRun_thread` link). -/
theorem tstep_footprintKN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hZ : ∀ l, BufInitOn th l → ¬ g.zf l) (hgp : ∀ l, PubAt th l → g.pf l) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ (∀ l, PubAt th l → E'.pfr l ≠ none) ∧
        NewCellSto g ρ η th E' := by
  have hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label :=
    fun y a e rt ws ad h1 h2 h3 => hgp _ ⟨y, a, e, rt, ws, ad, h1, h2, h3, rfl⟩
  by_cases hpub : ∃ x a e, th.term = .let_ x (.publish a) e
  · obtain ⟨x, a, e, hterm⟩ := hpub
    have h := tstep_footprintP (hDy := hDy) (hPb := hPb) (hRP := hRP) (hPS := hPS) hP hsc hT hi hE htv hm hwin hterm
    refine ⟨h.1, fun r hr _ => ?_⟩
    obtain ⟨E', hF, hx, h1, h2, hD⟩ := h.2 r hr
    refine ⟨E', hF, hx, h1, h2, fun l hl => ?_, NewCellSto_vac fun x' a' T e' he => by rw [hterm] at he; cases he⟩
    obtain ⟨y, a', e', rt, ws, ad, h3, h4, h5, rfl⟩ := hl
    exact hD y a' e' rt ws ad h3 h4 h5
  · have h := tstep_footprintN (hDy := hDy) (hZ := ZOK_of_not hZ) (hPb := hPb) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hRP hPS hSub hSig hTy
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', hF, hx, h1, h2, hN⟩ := h.2 r hr hpa
    refine ⟨E', hF, hx, h1, h2, fun l hl => ?_, hN⟩
    obtain ⟨y, a', e', -, -, -, h3, -⟩ := hl
    exact absurd ⟨y, a', e', h3⟩ hpub

/-- `tstep_footprintKQ` with `NewCellSto` of its witness. -/
theorem tstep_footprintKQN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hZ : ∀ l, BufInitOn th l → ¬ g.zf l) (hgp : ∀ l, PubAt th l → g.pf l) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ (∀ l, PubAt th l → E'.pfr l ≠ none) ∧
        TermTyped.BumpIf th E' ∧ NewCellSto g ρ η th E' := by
  by_cases hb : ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e
  · obtain ⟨x, bb, ib, v, e, hterm⟩ := hb
    have h := TermTyped.tstep_footprintB (hDy := hDy) hP hT hi hE htv hm (ZOK_of_not hZ) hRP hPS hterm
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', h1, h2, h3, h4, h5⟩ := h.2 r hr hpa
    refine ⟨E', h1, h2, h3, h4, fun l hl => ?_, TermTyped.bumpIf_of hterm h5,
      NewCellSto_vac fun x' a T e' he => by rw [hterm] at he; cases he⟩
    obtain ⟨y, a', e', -, -, -, h6, -⟩ := hl
    rw [hterm] at h6; cases h6
  · have h := tstep_footprintKN (hDy := hDy) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hZ hgp hRP hPS hSub hSig hTy
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', h1, h2, h3, h4, h5, hN⟩ := h.2 r hr hpa
    exact ⟨E', h1, h2, h3, h4, h5, fun x bb ib v e ht => (hb ⟨x, bb, ib, v, e, ht⟩).elim, hN⟩

#print axioms TermK5P.tstep_footprintKN
#print axioms TermK5P.tstep_footprintKQN

/-- (S1b) A `bufInit` of the run's current thread is at none of the run's published start own
cells: their publish point (`PfrProvE`'s right branch) and `hZp` (from `TermK5R.bufInitPubFR`). -/
theorem pubZ_noBufInit {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E : TEnv} {st c0 : Cfg} {th : TTh}
    (hP : PfrProvE p k arch i H E0 st c0 E)
    (hZp : ∀ c1 th1 c1' l cl, SoloNP p k arch i l st c1 → c1.ths[i]? = some th1 → PubAt th1 l →
      c1' ∈ threadSteps p k arch c1 i → Solo p k arch i c1' c0 → E0.sto l = some cl →
      cl.owner = some E0.tid → E0.pfr l = none → ¬ BufInitOn th l) :
    ∀ l, BufInitOn th l → ¬ PubZ E0 E l := by
  intro l hb hz
  obtain ⟨cl, F, hc0, ho, hp0, hEF⟩ := hz
  rcases hP l cl hc0 ho hp0 with ⟨hn, -⟩ | ⟨F', c1, th1, c1', -, hsolo, hth1, hpub, hs1, h1c, -⟩
  · rw [hn] at hEF
    cases hEF
  · exact hZp c1 th1 c1' l cl hsolo hth1 hpub hs1 h1c hc0 ho hp0 hb

/-- (S1b) **`PfrProvE` along a thread step** `c0 → c0'` (thread `th → th'`, environment
`E → E'`, footprint at a `g` with `g.pf ⊆ PubAt th` and `PubZ E0 E ⊆ g.zf`):
- unpublished, the step not at a `publish` naming `l`: the frontier stays none (`PfrG`), `SoloNP`
  extends;
- unpublished, the step at a `publish` naming `l`: the frontier is set (`hD`), `c0` is the publish
  point, and the new units' witnesses lie at most `th'.vWr = th.vWr` (`hU`, `hvw`);
- published: the frontier stays (`pfr` changes only from none), the count stays (`IniFixZ`), and the
  run after the publish extends. -/
theorem pfrProv_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E E' : TEnv} {st c0 c0' : Cfg} {th th' : TTh} {g : G}
    {n0 v0 : Nat} {s s' : St}
    (hP : PfrProvE p k arch i H E0 st c0 E) (hF : Foot g E E' s s') (hb : FrBound E0 n0 v0 E)
    (hgp : ∀ l, g.pf l → PubAt th l) (hz : ∀ l, PubZ E0 E l → g.zf l)
    (hD : ∀ l, PubAt th l → E'.pfr l ≠ none)
    (hs : c0' ∈ threadSteps p k arch c0 i) (hth : c0.ths[i]? = some th)
    (hvw : ∀ l, PubAt th l → th'.vs.vWr = th.vs.vWr)
    (hU : ∀ l c, E0.sto l = some c → c.owner = some E0.tid → ∀ N e us, c.ty = .array (.lit N) e →
      accs e = some us → ∀ o, o < E'.ini l * nWords us → ¬ o < E0.ini l * nWords us →
        ∃ τ, τ ≤ th'.vs.vWr ∧ H l o τ) :
    PfrProvE p k arch i H E0 st c0' E' := by
  intro l c hc0 ho hp0
  have hc : E.sto l = some c := (hb.2.2.2.1.2 l c hc0).1
  have hnf : ¬ FreshIn g s.nalloc s'.nalloc l := fun hl => by rw [(hF.2 l hl).1] at hc; cases hc
  rcases hP l c hc0 ho hp0 with ⟨hn, hsolo⟩ | ⟨F, c1, th1, c1', hEF, hsolo, hth1, hpub, hs1, h1c, hu⟩
  · by_cases hpl : PubAt th l
    · rcases hq : E'.pfr l with _ | F
      · exact absurd hq (hD l hpl)
      · refine .inr ⟨F, c0, th, c0', rfl, hsolo, hth, hpl, hs, .refl _, fun N e us hT hus o ho1 ho2 => ?_⟩
        rw [← hvw l hpl]
        exact hU l c hc0 ho N e us hT hus o ho1 ho2
    · have he : E'.pfr l = E.pfr l := Classical.byContradiction fun hne =>
        hpl (hgp l (hF.1.pfrG l (fun h => by rw [hc] at h; cases h) hne))
      refine .inl ⟨by rw [he]; exact hn, soloNP_snocT hsolo hs fun th0 h0 => ?_⟩
      rw [hth] at h0
      cases h0
      exact hpl
  · have he : E'.pfr l = some F := by
      rcases hF.1.2.2.2.2.2.1 l with e | ⟨h0, -⟩ | ⟨hl, -⟩
      · rw [e]; exact hEF
      · rw [hEF] at h0; cases h0
      · exact absurd hl hnf
    have hini : E'.ini l = E.ini l := (hF.1.iniFixZ l c F (hz l ⟨c, F, hc0, ho, hp0, hEF⟩) hnf hc hEF).1
    refine .inr ⟨F, c1, th1, c1', he, hsolo, hth1, hpub, hs1, solo_trans h1c (.thread hs (.refl _)),
      fun N e us hT hus o ho1 ho2 => ?_⟩
    rw [hini] at ho1
    exact hu N e us hT hus o ho1 ho2

/-- An extern move extends a `SoloNP` run (it is never a `publish`). -/
theorem soloNP_snocE {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {r : AllocLabel} {c c0 c0' : Cfg}
    (h : SoloNP p k arch i r c c0) (hs : c0' ∈ extSteps c0 i) : SoloNP p k arch i r c c0' := by
  revert hs
  induction h with
  | refl => intro hs; exact .ext hs (.refl _)
  | thread hs1 hn1 _ ih => intro hs; exact .thread hs1 hn1 (ih hs)
  | prom a v w hw _ ih => intro hs; exact .prom a v w hw (ih hs)
  | ext hs1 _ ih => intro hs; exact .ext hs1 (ih hs)

/-- An extern move keeps the publish provenance. -/
theorem pfrProv_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E : TEnv} {st c0 c0' : Cfg}
    (hP : PfrProvE p k arch i H E0 st c0 E) (hs : c0' ∈ extSteps c0 i) : PfrProvE p k arch i H E0 st c0' E := by
  intro l c hc0 ho hp0
  rcases hP l c hc0 ho hp0 with ⟨hn, hsolo⟩ | ⟨F, c1, th1, c1', hEF, hsolo, hth1, hpub, hs1, h1c, hu⟩
  · exact .inl ⟨hn, soloNP_snocE hsolo hs⟩
  · exact .inr ⟨F, c1, th1, c1', hEF, hsolo, hth1, hpub, hs1, solo_trans h1c (.ext hs (.refl _)), hu⟩

/-- (S1b) **`PfrProvE` along a promise step** (the environment is kept). -/
theorem pfrProv_prom {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat}
    {H : AllocLabel → Nat → Ts → Prop} {E0 E : TEnv} {st c0 : Cfg} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hP : PfrProvE p k arch i H E0 st c0 E) (hw : w < c0.mem.size) :
    PfrProvE p k arch i H E0 st (promise c0 i a v w) E := by
  intro l c hc0 ho hp0
  rcases hP l c hc0 ho hp0 with ⟨hn, hsolo⟩ | ⟨F, c1, th1, c1', hEF, hsolo, hth1, hpub, hs1, h1c, hu⟩
  · exact .inl ⟨hn, soloNP_snocP hsolo hw⟩
  · exact .inr ⟨F, c1, th1, c1', hEF, hsolo, hth1, hpub, hs1, solo_trans h1c (.prom a v w hw (.refl _)), hu⟩

end TermK5P

#print axioms TermK5P.soloNP_snocT
#print axioms TermK5P.soloNP_snocP
#print axioms TermK5P.soloNP_snocE
#print axioms TermK5P.pfrProv_ext
#print axioms TermK5P.pfrProvE_start
#print axioms TermK5P.tstep_footprintK
#print axioms TermK5P.pubZ_noBufInit
#print axioms TermK5P.pfrProv_thread
#print axioms TermK5P.pfrProv_prom

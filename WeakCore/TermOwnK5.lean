import WeakCore.TermOwnX2
import WeakCore.TermOwnHeldQ
import WeakCore.TermOwnK1
import WeakCore.TermCertScope
import WeakCore.TermOwnK2
import WeakCore.TermOwnK3
import WeakCore.TermOwnK4

/-!
# TermOwnK5 (own-key layer, package K5 prep): the publish chain and the assembled step

K2–K4 are discharged by their deliverables (`TermOwnK2.ownXStep_k2`, `TermOwnK3.ownXStep_k3`,
`TermOwnK4.ownXStep_k4`, `TermOwnK4.ownXPub1`); every theorem here is unconditional in them.

* `ownXStepT_all`: `OwnXStepT` at every `n` (`ownXStepT_of_pkgs`).
* `ownXLe_pub_chain`: `OwnXLe 1` at a run start, a solo run to a `publish` of
  `x`, the publish step, and a solo run on to a certified `c2` give `OwnXLe 0` at `c2`
  (`ownXLe_run` 1 → `OwnXPub1` → `ownXLe_run` 0); `ownXLe_pub_noOwnUse` adds `use_ne`.
* `ownXLe0_run_noOwnUse` / `ownXLe0_prom_noOwnUse`: the `n = 0` runs (start-published cell, from
  a reachable configuration or from its promise step).
* Window premise `hQ` (`ScopeAt ∧ NoHoldPub3` along the run) from the `CertScopeC/CertWinC` (thread
  step) or `CertScopeP/CertWinP` (promise step) fields: `winQC`, `winQP`.

**Circularity (G-c = (B)).** `hQ` is read off the `certWinC`/`certWin` fields, so no lemma of this
module may be used to discharge those fields (or `CertFreshC`, which feeds them via
`certWinC_of_fresh`).

`publish_own_cell` (the copy of W/TermNoHoldA L20 `publish_own`) now lives in `TermOwnX2`.
-/

namespace TermOwnK5
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnK1 TermCertScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The window premise from the certificate fields -/

/-- **The window along a thread step's certificate runs** (from the source `c`), from the fields. -/
theorem winQC {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    {S : AllocLabel → Prop} (hS : ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S) :
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAt p i c1 ∧ NoHoldPubA p k arch (Cut Eg i S) (Cut Eg i S) i c1 :=
  fun c1 h1 h2 => ⟨hsc X c1 h1 h2, hw X S hS c1 h1 h2⟩

/-- **The window along a promise step's certificate runs** (from `promise c j a v w`). -/
theorem winQP {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (Y : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {S : AllocLabel → Prop} (hS : ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S) :
    ∀ c1, Solo p k arch j (promise c j a v w) c1 → Certified p k arch c1 j →
      ScopeAt p j c1 ∧ NoHoldPubA p k arch (Cut Eg j S) (Cut Eg j S) j c1 :=
  fun c1 h1 h2 => ⟨hsc Y c1 h1 h2, (hw Y).1 S hS c1 h1 h2⟩

/-! ## The assembled thread step -/

/-- **`OwnXStepT` at every bound**, and the K2–K4 deliverables. -/
theorem ownXStepT_all [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : ∀ n, OwnXStepT p k arch i x n :=
  fun n => ownXStepT_of_pkgs (ownXStep_k1 hP hPS hSub hSig n) (TermOwnK2.ownXStep_k2 hP hPS n)
    (TermOwnK3.ownXStep_k3 hP hPS n) (TermOwnK4.ownXStep_k4 hP hPS hSub hSig n)

/-! ## The publish chain (R1) -/

/-- **The Solo split at the publish of `x`**: `OwnXLe 1` at `c`, a solo run to `c1`, the publish
step `c1 → c1'` of `x`, and a solo run on to a certified `c2` give `OwnXLe 0` at `c2`. -/
theorem ownXLe_pub_chain [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c c1 c1' c2 : Cfg} {th : TTh} {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word}
    {ad : Address} {g' : Nat}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0 ∧ NoHoldPubA p k arch E0 E0 i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLe p k arch E0 i x 1 c) (hTA : TermTyped.TidAt i c E0) (h1 : Solo p k arch i c c1) (hs : c1' ∈ threadSteps p k arch c1 i)
    (hth : c1.ths[i]? = some th) (hterm : th.term = .let_ y (.publish a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    (h2 : Solo p k arch i c1' c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : OwnXLe p k arch E0 i x 0 c2 := by
  have hT : ∀ n, OwnXStepT p k arch i x n := ownXStepT_all hP hPS hSub hSig
  have hpub : OwnXPub1 p k arch i x := TermOwnK4.ownXPub1 hP hPS
  have hc1' : Certified p k arch c1' i := certified_back h2 hc2
  have hc1 : Certified p k arch c1 i := certified_back (.thread hs h2) hc2
  have hI1 := ownXLe_run (hT 1) (ownXStepP_all 1) hQ hvI h0 hTA h1 hc1
  obtain ⟨hsc1, hw1⟩ := hQ c1 h1 hc1
  have hI1' := hpub E0 c1 c1' th y a e rt ws ad g' hsc1 hw1 (TermViewInv.viewInv_solo hvI h1) hI1 hs hc1' hth hterm hea hws hx
  exact ownXLe_run (hT 0) (ownXStepP_all 0) (fun c0 h3 h4 => hQ c0 (solo_trans h1 (.thread hs h3)) h4)
    (TermViewInv.viewInv_thread (TermViewInv.viewInv_solo hvI h1) hs) hI1'
    (TermTyped.tidAt_thread hs (TermTyped.tidAt_solo h1 hTA)) h2 hc2

/-- **No own use of `x` after its publish** (the chain plus `use_ne`), with the packages. -/
theorem ownXLe_pub_noOwnUse [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c c1 c1' c2 : Cfg} {th : TTh} {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word}
    {ad : Address} {g' : Nat} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0 ∧ NoHoldPubA p k arch E0 E0 i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLe p k arch E0 i x 1 c) (hTA : TermTyped.TidAt i c E0) (h1 : Solo p k arch i c c1) (hs : c1' ∈ threadSteps p k arch c1 i)
    (hth : c1.ths[i]? = some th) (hterm : th.term = .let_ y (.publish a) e)
    (hea : evalAt th.env a = some (rt, ws)) (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = x)
    (h2 : Solo p k arch i c1' c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ th, c2.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x :=
  (ownXLe_pub_chain hP hQ hvI h0 hTA h1 hs hth hterm hea hws hx h2 hc2 hPS hSub hSig).use_ne

/-! ## The `n = 0` runs (a cell published at the run start) -/

/-- **No own use of a start-published `x`** along a thread's certified solo run. -/
theorem ownXLe0_run_noOwnUse [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c c2 : Cfg} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hQ : ∀ c0, Solo p k arch i c c0 → Certified p k arch c0 i → ScopeAt p i c0 ∧ NoHoldPubA p k arch E0 E0 i c0) (hvI : TermViewInv.ViewInv c)
    (h0 : OwnXLe p k arch E0 i x 0 c) (hTA : TermTyped.TidAt i c E0) (h : Solo p k arch i c c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ th, c2.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x :=
  (ownXLe_run (ownXStepT_all hP hPS hSub hSig 0) (ownXStepP_all 0) hQ hvI h0 hTA h hc2).use_ne

/-- **No own use of a start-published `x`** along the certificate of a promise step. -/
theorem ownXLe0_prom_noOwnUse [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {E0 : TEnv} {i : Nat} {x : AllocLabel}
    {c c2 : Cfg} {a : Address} {v : WeakMem.Val} {w : Ts} [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hQ : ∀ c0, Solo p k arch i (promise c i a v w) c0 → Certified p k arch c0 i →
      ScopeAt p i c0 ∧ NoHoldPubA p k arch E0 E0 i c0) (hvI : TermViewInv.ViewInv (promise c i a v w))
    (h0 : OwnXLe p k arch E0 i x 0 c) (hTA : TermTyped.TidAt i c E0) (hw : w < c.mem.size) (h : Solo p k arch i (promise c i a v w) c2)
    (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∃ th, c2.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x :=
  ownXLe0_run_noOwnUse hP hQ hvI
    (ownXStepP_all 0 E0 c a v w h0 hw (certified_back h hc2)) (TermTyped.tidAt_prom hTA) h hc2 hPS hSub hSig

/-! ## A. `bufInitIni`, published case (restated fields: the bufInit's buffer handle names `m.loc.label`) -/

/-- **`SW` inversion at a `bufInit`** (supplies the restated fields' target premise from `hsw`): the
written location lies in the cell the buffer handle names. -/
theorem sw_bufInit_label {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {loc : Address} {val : WeakMem.Val}
    {y : String} {bb ib v : At} {e : Expr} (hterm : th.term = .let_ y (.bufInit bb ib v) e)
    (h : SW g mem pairs th loc val) :
    ∀ rt w' ad g0, evalAt th.env bb = some (rt, [w']) → w'.val = .loc ad g0 → ad.label = loc.label := by
  intro rt w' ad g0 he hw'
  rcases h with ⟨x', op, e', ht, hw⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, -⟩
  · rw [hterm] at ht
    cases ht
    rcases hw with ⟨pw, b, rel, us, ws, j, w, hU, -, -, hloc, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, hop, -⟩
    · obtain ⟨-, t, t1, t2, iws, μ, u, j', a0, μ', n, e'', ψ, hbb, -, -, -, -, ha0, -, -, hb⟩ := hU
      rw [he] at hbb
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hbb
      obtain ⟨-, rfl⟩ := hbb
      simp only [addrOf, hw', Option.some.injEq] at ha0
      subst ha0
      subst hloc
      subst hb
      rfl
    · cases hop
  · rw [hterm] at ht; cases ht

/-- A `bufInit` under "no own use of `x`" does not target `x` (its buffer handle is own-typed). -/
theorem bufInit_ne_of_use {p : Prog} {th : TTh} {x : AllocLabel} {y : String} {bb ib v : At} {e : Expr}
    (hterm : th.term = .let_ y (.bufInit bb ib v) e)
    (h : ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧ FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad g] → ad.label ≠ x) :
    ∀ rt w' ad g0, evalAt th.env bb = some (rt, [w']) → w'.val = .loc ad g0 → ad.label ≠ x := by
  obtain ⟨ρ, η, cx, Rf, Rs, -, hT, -, hne⟩ := h
  intro rt w' ad g0 he hw'
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
    cases hop with
    | bufInit hu hb _ _ _ _ _ _ =>
      exact hne bb _ _ rt [w'] ad g0 hu (.inr ⟨_, _, _, hb⟩) he (by simp [hw'])

/-- **BufInitIniF, published case**: along the certificate of a promise step, a `bufInit` of the
promiser does not target a start-published cell. -/
theorem bufInitIniF_pub [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {l : AllocLabel}
    (hsc : CertScopeP p k arch Sp Init MintOK c0) (hw : CertWinP p k arch Sp Init MintOK c0)
    (Y : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) (hpub : Eg.pubd l) (hsto : Eg.sto l ≠ none)
    {c1 : Cfg} {th1 : TTh} {y : String} {bb ib v' : At} {e : Expr}
    (h1 : Solo p k arch j (promise c j a v w) c1) (hc1 : Certified p k arch c1 j)
    (hth1 : c1.ths[j]? = some th1) (hterm : th1.term = .let_ y (.bufInit bb ib v') e) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ rt w' ad g0, evalAt th1.env bb = some (rt, [w']) → w'.val = .loc ad g0 → ad.label ≠ l := by
  obtain ⟨S, hS⟩ := Y.inv.thr j th Y.hth
  obtain ⟨th2, hth2, h⟩ := ownXLe0_prom_noOwnUse hP (winQP hsc hw Y hS) (TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 Y.run) Y.hw)
    (ownXLe_start_pub Y.inv Y.hth hS hpub hsto) (TermMain.tidAt_cut Y.inv j S) Y.hw h1 hc1 hPS hSub hSig
  obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
  exact bufInit_ne_of_use hterm h

/-- **BufInitIniT, published case**: after the thread step that publishes `l` (an own cell of `i`), a
`bufInit` along its certificate does not target `l`.  (A step that newly shares `l` by a plant is
G-b.) -/
theorem bufInitIniT_pub [WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {l : AllocLabel} {cl : Cell}
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hsto : Eg.sto l = some cl) (hown : cl.owner = some i)
    {y : String} {a : At} {e : Expr} {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat}
    (hterm : th.term = .let_ y (.publish a) e) (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g']) (hx : ad.label = l)
    {c1 : Cfg} {th1 : TTh} {y' : String} {bb ib v' : At} {e' : Expr}
    (h1 : Solo p k arch i c' c1) (hc1 : Certified p k arch c1 i) (hth1 : c1.ths[i]? = some th1)
    (hterm1 : th1.term = .let_ y' (.bufInit bb ib v') e') (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ rt w' ad' g0, evalAt th1.env bb = some (rt, [w']) → w'.val = .loc ad' g0 → ad'.label ≠ l := by
  obtain ⟨S, hS⟩ := X.inv.thr i th X.hth
  obtain ⟨th2, hth2, h⟩ := ownXLe_pub_noOwnUse hP (winQC hsc hw X hS) (TermViewInv.viewInv_run hV0 X.run)
    (ownXLe_start X.inv X.hth hS hsto (.inl hown)) (TermMain.tidAt_cut X.inv i S) (.refl _) X.hc' X.hth hterm hea hws hx h1 hc1 hPS hSub hSig
  obtain rfl : th2 = th1 := Option.some.inj (hth2.symm.trans hth1)
  exact bufInit_ne_of_use hterm1 h

end TermOwnK5

#print axioms TermOwnK5.winQC
#print axioms TermOwnK5.winQP
#print axioms TermOwnK5.ownXStepT_all
#print axioms TermOwnK5.ownXLe_pub_chain
#print axioms TermOwnK5.ownXLe_pub_noOwnUse
#print axioms TermOwnK5.ownXLe0_run_noOwnUse
#print axioms TermOwnK5.ownXLe0_prom_noOwnUse
#print axioms TermOwnK5.sw_bufInit_label
#print axioms TermOwnK5.bufInit_ne_of_use
#print axioms TermOwnK5.bufInitIniF_pub
#print axioms TermOwnK5.bufInitIniT_pub

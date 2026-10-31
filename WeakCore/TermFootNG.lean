import WeakCore.TermFootNF

/-! # TermFootNG ((X) FootNC): the footprint with `FootNCE` on the witness

`tstep_footprintK_nc`: `TermK5P.tstep_footprintK` (hypotheses verbatim) with `FootNCE (CE η) E' r`
added to its `∃ E'`.  Off `AllocT`, from `tstep_footprintK` and `tstep_nalloc`; at `AllocT`
(never a `publish` or a `CapT` term), from `tstepMF_stepN` (the `TermFootNF` producers).
-/

namespace TermFootNG
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermTyped TermGlob TermOwnG0Defs TermK5Defs TermK5P TermFootNC TermFootNP TermFootNF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- **(X) `tstepMF_step` with `FootNCE (CE η) E' r` on the witness.** -/
theorem tstepMF_stepN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ThInvMFQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  by_cases hAl : AllocT th.term
  rotate_left
  · have h := tstepMF_step (hDy := hDy) (hPS := hPS) (hSub := hSub) (hSig := hSig) (hTy := hTy) (hZ := hZ) (hPb := hPb) (hbf := hbf) hP hp hn hnd hsc hT hi hE htv hm hpx hwin hRP
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', hF, h1⟩ := h.2 r hr hpa
    exact ⟨E', footNC_efoot hF (Nat.le_of_eq (tstep_nalloc hAl r hr)), hF, h1⟩
  have hmS : ∀ {r : Memory × List Ts × TTh}, ThInvMFQ (QF (CE η) g th.nalloc r.2.2) p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 →
      ThInvMFQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
    fun h => ThInvMFQ.mono (fun _ hs => footNC_sto hs.1) h
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc hAl
  cases hT0 with
  | let_ hop _ =>
    cases hop
    case inl =>
      have h := tstepM_inlTN (hDy := hDy) (hPS := hPS) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP
      exact ⟨h.1, fun r hr hpa => hmS (h.2 r hr hpa)⟩
    case inr =>
      have h := tstepM_inrTN (hDy := hDy) (hPS := hPS) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP
      exact ⟨h.1, fun r hr hpa => hmS (h.2 r hr hpa)⟩
    case new => exact paW <| tstepM_newN (hDy := hDy) (hPS := hPS) ht hsc hP hn hT hi hE htv hm hRP
    case newBuf => exact paW <| tstepM_newBufN (hDy := hDy) (hPS := hPS) ht hsc hP hn hT hi hE htv hm hRP
    all_goals exact hAl.elim
  | case =>
    have h := tstepM_caseTN (hDy := hDy) (hPS := hPS) (hbf := hbf) ht hn hT hi hE htv hm hpx hRP
    exact ⟨h.1, fun r hr hpa => hmS (h.2 r hr hpa)⟩
  | _ => exact hAl.elim

/-- **(X) `TermK5P.tstep_footprintK` with `FootNCE (CE η) E' r` on the witness.** -/
theorem tstep_footprintK_nc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : ScopeD th.σs cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hZ : ∀ l, BufInitOn th l → ¬ g.zf l) (hgp : ∀ l, PubAt th l → g.pf l) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ Ext (CE η) E' ∧
        ThInvE p E' r.2.2 ∧ MemInv g E' (stOf r.1 r.2.1 r.2.2) ∧ (∀ l, PubAt th l → E'.pfr l ≠ none) ∧
        FootNCE (CE η) E' r := by
  by_cases hAl : AllocT th.term
  rotate_left
  · have h := tstep_footprintK (hDy := hDy) (hPS := hPS) (hSub := hSub) (hSig := hSig) (hTy := hTy) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hZ hgp hRP
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', hF, hx, h1, h2, h3⟩ := h.2 r hr hpa
    exact ⟨E', hF, hx, h1, h2, h3, footNC_efoot hF.1 (Nat.le_of_eq (tstep_nalloc hAl r hr))⟩
  have hne : ∀ x op e, th.term = .let_ x op e → AllocOp op := fun x op e h => by rw [h] at hAl; exact hAl
  have hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label :=
    fun y a e rt ws ad h1 h2 h3 => hgp _ ⟨y, a, e, rt, ws, ad, h1, h2, h3, rfl⟩
  have hsc0 : StepScope cx th.term := by
    rcases hsc with hsc | ⟨-, hc⟩
    · exact hsc
    · obtain ⟨x, op, e, h, hc, -⟩ := capT_inv hc
      have := hne x op e h
      cases op <;> first | exact this.elim | exact hc.elim
  have h := tstepMF_stepN (hDy := hDy) (hPS := hPS) (hSub := hSub) (hSig := hSig) (hTy := hTy) (hZ := ZOK_of_not hZ) (hPb := hPb) (hbf := hbf) hP hp hn hnd hsc0 hT hi hE htv hm hpx hwin hRP
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨E', hq, hF, h1, h2⟩ := h.2 r hr hpa
  have hF' : Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, hce, _⟩ := h1
    subst hce; exact Foot_ext hF'
  refine ⟨E', hF', hx, h1, h2, fun l hl => ?_, hq⟩
  obtain ⟨y, a', e', -, -, -, h3, -⟩ := hl
  exact absurd (hne _ _ _ h3) id

#print axioms tstepMF_stepN
#print axioms tstep_footprintK_nc


end TermFootNG

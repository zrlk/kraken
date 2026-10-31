import WeakCore.TermFootBP0

/-! # TermFootNCB (FootNCB): the footprint with `FootNCE` and `FootB1` on one witness

`tstep_footprintK_ncB`: `TermFootNG.tstep_footprintK_nc` (hypotheses verbatim) with clause (1) of
`FootBP` (`TermFootBP0.FootB1 g th.nalloc th.env r E'`) added on the same witness `E'`.  Off `AllocT`
the allocation count is kept (`footB1_nalloc`); at `new`/`newBuf` the new binding counts no word
(`footB1_new`/`footB1_newBuf`); at the (re-)boxing `inl`/`inr`/`case`, the `TermFootNF` producers'
witness boxes every allocated label (`QF`, `BoxFr`).
-/

namespace TermFootNCB
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermTyped TermGlob TermOwnG0Defs TermK5Defs TermK5P TermFootNC TermFootNP TermFootNF TermFootNG
open TermFootBP0
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem footB1_boxFr {g : G} {n : Nat} {env : Env} {r : Memory × List Ts × TTh} {E' : TEnv}
    (h : BoxFr g n r.2.2 E') : FootB1 g n env r E' :=
  fun l hl _ _ _ _ _ => .inl (h l hl)

/-- **(FootNCB) `tstepMF_stepN` at `AllocT`, with `FootNCE` and `FootB1` on the witness.** -/
theorem tstepMF_stepNB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    (hAl : AllocT th.term) (hP : ProgT p) (hn : 0 < g.n)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hPS : PwSkel) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ThInvMFQ (fun E' => (FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') ∧ NewCellSto g ρ η th E') p g (CE η)
        (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hmS : ∀ {r : Memory × List Ts × TTh}, (∀ x a T e, th.term ≠ .let_ x (.new a (some T)) e) → ThInvMFQ (QF (CE η) g th.nalloc r.2.2) p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 →
      ThInvMFQ (fun E' => (FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E') ∧ NewCellSto g ρ η th E') p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
    fun hv h => ThInvMFQ.mono (fun _ hs => ⟨⟨footNC_sto hs.1, footB1_boxFr hs.2⟩, NewCellSto_vac hv⟩) h
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc hAl
  cases hT0 with
  | let_ hop _ =>
    cases hop
    case inl =>
      have h := tstepM_inlTN (hDy := hDy) (hPS := hPS) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP
      exact ⟨h.1, fun r hr hpa => hmS (fun _ _ _ _ h' => by rw [ht] at h'; cases h') (h.2 r hr hpa)⟩
    case inr =>
      have h := tstepM_inrTN (hDy := hDy) (hPS := hPS) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP
      exact ⟨h.1, fun r hr hpa => hmS (fun _ _ _ _ h' => by rw [ht] at h'; cases h') (h.2 r hr hpa)⟩
    case new =>
      have h := tstepM_newNN (hDy := hDy) (hPS := hPS) ht hsc hP hn hT hi hE htv hm hRP
      exact ⟨h.1, fun r hr _ => ThInvMFQ.mono (fun _ hq => ⟨⟨hq.1, footB1_new ht hr⟩, hq.2⟩) (h.2 r hr)⟩
    case newBuf =>
      have h := tstepM_newBufN (hDy := hDy) (hPS := hPS) ht hsc hP hn hT hi hE htv hm hRP
      exact ⟨h.1, fun r hr _ => ThInvMFQ.mono (fun _ hq => ⟨⟨hq, footB1_newBuf ht hr⟩, NewCellSto_vac (fun _ _ _ _ h' => by rw [ht] at h'; cases h')⟩) (h.2 r hr)⟩
    all_goals exact hAl.elim
  | case =>
    have h := tstepM_caseTN (hDy := hDy) (hPS := hPS) (hbf := hbf) ht hn hT hi hE htv hm hpx hRP
    exact ⟨h.1, fun r hr hpa => hmS (fun _ _ _ _ h' => by rw [ht] at h'; cases h') (h.2 r hr hpa)⟩
  | _ => exact hAl.elim

/-- **(FootNCB) `TermFootNG.tstep_footprintK_nc` with `FootB1 g th.nalloc th.env r E'` on the witness.** -/
theorem tstep_footprintK_ncB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
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
        FootNCE (CE η) E' r ∧ FootB1 g th.nalloc th.env r E' ∧ TermTyped.BumpIf th E' ∧
        NewCellSto g ρ η th E' := by
  by_cases hAl : AllocT th.term
  rotate_left
  · by_cases hbi : ∃ x bb ib v e, th.term = .let_ x (.bufInit bb ib v) e
    · obtain ⟨x, bb, ib, v, e, hterm⟩ := hbi
      have h := TermTyped.tstep_footprintB (hDy := hDy) hP hT hi hE htv hm (ZOK_of_not hZ) hRP hPS hterm
      refine ⟨h.1, fun r hr hpa => ?_⟩
      obtain ⟨E', hF, hx, h1, h2, h5⟩ := h.2 r hr hpa
      refine ⟨E', hF, hx, h1, h2, fun l hl => ?_, footNC_efoot hF.1 (Nat.le_of_eq (TermFootNC.tstep_nalloc hAl r hr)),
        footB1_nalloc (Nat.le_of_eq (TermFootNC.tstep_nalloc hAl r hr)), TermTyped.bumpIf_of hterm h5,
        NewCellSto_vac (fun _ _ _ _ h' => by rw [hterm] at h'; cases h')⟩
      obtain ⟨y, a', e', -, -, -, h6, -⟩ := hl
      rw [hterm] at h6; cases h6
    have h := tstep_footprintK_nc (hDy := hDy) (hPS := hPS) (hSub := hSub) (hSig := hSig) (hTy := hTy) hP hp hn hnd hsc hT hi hE htv hm hbf hpx hwin hZ hgp hRP
    refine ⟨h.1, fun r hr hpa => ?_⟩
    obtain ⟨E', hF, hx, h1, h2, h3, h4⟩ := h.2 r hr hpa
    exact ⟨E', hF, hx, h1, h2, h3, h4, footB1_nalloc (Nat.le_of_eq (TermFootNC.tstep_nalloc hAl r hr)),
      fun x bb ib v e ht => (hbi ⟨x, bb, ib, v, e, ht⟩).elim,
      NewCellSto_vac (fun _ _ _ _ h' => hAl (by rw [h']; trivial))⟩
  have hne : ∀ x op e, th.term = .let_ x op e → AllocOp op := fun x op e h => by rw [h] at hAl; exact hAl
  have hsc0 : StepScope cx th.term := by
    rcases hsc with hsc | ⟨-, hc⟩
    · exact hsc
    · obtain ⟨x, op, e, h, hc, -⟩ := capT_inv hc
      have := hne x op e h
      cases op <;> first | exact this.elim | exact hc.elim
  have h := tstepMF_stepNB (hDy := hDy) (hPS := hPS) hAl hP hn hsc0 hT hi hE htv hm hbf hpx hRP
  refine ⟨h.1, fun r hr hpa => ?_⟩
  obtain ⟨E', ⟨⟨hq, hb⟩, hN⟩, hF, h1, h2⟩ := h.2 r hr hpa
  have hF' : Foot g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := ⟨hF, fun l hl => fresh_blank hm hl⟩
  have hx : Ext (CE η) E' := by
    obtain ⟨_, η', _, hce, _⟩ := h1
    subst hce; exact Foot_ext hF'
  refine ⟨E', hF', hx, h1, h2, fun l hl => ?_, hq, hb, fun x bb ib v e ht => absurd (hne _ _ _ ht) id, hN⟩
  obtain ⟨y, a', e', -, -, -, h3, -⟩ := hl
  exact absurd (hne _ _ _ h3) id

#print axioms footB1_boxFr
#print axioms tstepMF_stepNB
#print axioms tstep_footprintK_ncB

end TermFootNCB

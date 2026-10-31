import WeakCore.TermFootNP

/-! # TermFootNK ((X) FootNC): the credited thread step with `FootNCE` on the witness

`tstepMCF_stepKN`: `tstepMCF_stepK` (statement verbatim) with `FootNCE (CE η) E' r` on the witness.
Off `AllocT`, from `tstepMCF_stepK` and `tstep_nalloc` (`footNC_efoot`); at a frame-only `AllocT`
term (unboxed `inl`/`inr`/`case`) likewise, the count kept by `Same`; at the others, from the
`TermFootNP` producers.
-/

namespace TermFootNK
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece TermPlant TermFootNC
  TermFootNP
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- `ThInvMCFS` at a result keeping the allocation count carries `FootNCE`. -/
theorem mcfs_addFoot {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {r : Memory × List Ts × TTh} {Tot H : Res} {cr db : Ts → Res}
    (h : ThInvMCFS p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H cr db)
    (hn : r.2.2.nalloc ≤ th.nalloc) :
    ThInvMCFSQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H cr db :=
  let ⟨E', h0, hr⟩ := h
  ⟨E', footNC_efoot h0 hn, h0, hr⟩

/-- A frame-only allocating term (unboxed `inl`/`inr`/`case`) keeps the allocation count. -/
theorem frame_nalloc {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat}
    {η : TEnv} {Rf Rs : Res} (hA : AllocT th.term) (hR : StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) :
    ∀ r ∈ tstep g mem pairs th, r.2.2.nalloc ≤ th.nalloc := by
  generalize ht : th.term = t0 at hA hR
  cases t0 with
  | let_ x op e =>
    cases op
    case inl τ a => exact fun r hr => Nat.le_of_eq (same_inlR ht hR hT hi r hr).2.2.2.2
    case inr τ a => exact fun r hr => Nat.le_of_eq (same_inrR ht hR hT hi r hr).2.2.2.2
    case new => exact hR.elim
    case newBuf => exact hR.elim
    all_goals exact hA.elim
  | case a x e₁ y e₂ => exact fun r hr => Nat.le_of_eq (same_caseR ht hR hT hCk hi hE htv r hr).2.2.2.2
  | _ => exact hA.elim

/-- `mc_ofKF` keeping `Q` on the witness. -/
theorem mc_ofKFQ {Q : TEnv → Prop} {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : TTh} {η : TEnv} {Tot H' Rf Rs H F : Res} {cr db : Ts → Res}
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hK : ThInvMKQ Q p g (CE η) (stOf mem pairs th) Sp mem' pairs' th' Tot H')
    (hms : MintStepN g η (stOf mem pairs th) (stOf mem' pairs' th') .zero F) (hle : Tot + H' ≤ Rf + Rs + H + F) :
    ∃ Tot H' C F, ThInvMCFSQ Q p g (CE η) (stOf mem pairs th) Sp mem' pairs' th' Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf mem' pairs' th') C F ∧
      Tot + H' + pSum (stOf mem' pairs' th') cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf mem' pairs' th') db + F := by
  obtain ⟨E, hq, hF, hSK, hBV, hT, hm', hH', hk⟩ := hK
  obtain ⟨hC', e1, e2⟩ := CrKeep_pack (MemInv_promLt hm) (MemInv_nodup hm) hk cr db hC
  refine ⟨Tot, H', .zero, F, ⟨E, hq, hF, (by seenT), (by boxT), hT, hm', hH', hC'⟩, hms, ?_⟩
  rw [e1, e2]
  intro k
  have h1 := hle k
  simp only [Res.add_apply, Res.zero_apply] at h1 ⊢
  omega

/-- `cN` with a result-dependent `Q` on the witness. -/
theorem cNQ {Q : Memory × List Ts × TTh → TEnv → Prop} {Sp : AllocLabel → List Res} {t : Expr} {p : Prog} {g : G}
    {mem : Memory} {pairs : List Ts} {th : TTh} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (Q r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (Q r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt t C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  ⟨h.1, fun r hr hpa => let ⟨Tot, H', C, F, h1, h2, h3⟩ := h.2 r hr hpa
    ⟨Tot, H', C, F, h1, h2.toM, h2.claimAt _, h3⟩⟩

/-- Lifting an allocating `TermFootNP` producer (`new`/`newBuf`) to credits. -/
theorem mc_liftFN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res} {l : AllocLabel}
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th,
      ∃ Tot H', ThInvMKQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧
        FreshIn g (stOf mem pairs th).nalloc (stOf r.1 r.2.1 r.2.2).nalloc l ∧
        Tot + H' ≤ Rf + Rs + H + Res.one (.own l)) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  ⟨h.1, fun r hr _ => by
    obtain ⟨Tot, H', hK, hf, hle⟩ := h.2 r hr
    exact mc_ofKFQ hm hC hK (.alloc hf (FreshIn_sto hm.2.2.2.1 hf)) hle⟩

/-- Lifting a sto-keeping `TermFootNP` producer (`inl`/`inr`/`case`) to credits. -/
theorem mc_liftSN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ Tot H', ThInvMKQ (StoEq (CE η)) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' ∧
        Tot + H' ≤ Rf + Rs + H) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧
      MintStepN g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F :=
  ⟨h.1, fun r hr hp => by
    obtain ⟨Tot, H', hK, hle⟩ := h.2 r hr hp
    exact mc_ofKQ hm hC (ThInvMKQ.mono (fun _ hs => footNC_sto hs) hK) hle⟩

/-- **(X) The credited thread step with `FootNCE` on the witness.** -/
theorem tstepMCF_stepKN {Sp : AllocLabel → List Res} {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeldL (CE η) (stOf mem pairs th) H Sp)
    (hpx : PAx g mem pairs th) (hC : PromCr (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th) (hnvp : OwnOpT cx th.term → OwnNVPF (CE η) (stOf mem pairs th))
    (hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hRF : OwnFrontierRMWT (CE η) (stOf mem pairs th) th.term) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ∃ Tot H' C F,
      ThInvMCFSQ (fun E' => FootNCE (CE η) E' r) p g (CE η) (stOf mem pairs th) Sp r.1 r.2.1 r.2.2 Tot H' cr db ∧ MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAt th.term C F ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr + pSum (stOf mem pairs th) db + C ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db + F := by
  by_cases hAl : AllocT th.term
  rotate_left
  · have h0 := tstepMCF_stepK (hDy := hDy) (hZ := hZ) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hnvp hnp hfo hRF hrmw hbf hRP hPS hSub hSig hTy
    refine ⟨h0.1, fun r hr hpa => ?_⟩
    obtain ⟨Tot, H', C, F, h1, h2⟩ := h0.2 r hr hpa
    exact ⟨Tot, H', C, F, mcfs_addFoot h1 (Nat.le_of_eq (tstep_nalloc hAl r hr)), h2⟩
  by_cases hR : StepScopeR th.σs cx th.term
  · have h0 := tstepMC_frame (hDy := hDy) hP hp hnd hR hT hCk hi hE htv hm hH hC hRP hPS hSub hSig
    have hna := frame_nalloc (g := g) (mem := mem) (pairs := pairs) hAl hR hT hCk hi hE htv
    refine ⟨h0.1, fun r hr _ => ?_⟩
    obtain ⟨Tot, H', C, F, h1, h2⟩ := h0.2 r hr
    exact ⟨Tot, H', C, F, mcfs_addFoot h1 (hna r hr), h2⟩
  have hsc' := hsc.resolve_right hR
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc' hAl
  cases hT0 with
  | let_ hop _ =>
    cases hop
    case inl => exact cNQ <| mc_liftSN hm hC <| tstepMR_inlTN (hDy := hDy) (hbf := hbf) (hpx := hpx) ht hP hn hT hCk hi hE htv hm hH hRP hPS
    case inr => exact cNQ <| mc_liftSN hm hC <| tstepMR_inrTN (hDy := hDy) (hbf := hbf) (hpx := hpx) ht hP hn hT hCk hi hE htv hm hH hRP hPS
    case new => exact cNQ <| mc_liftFN hm hC <| tstepMR_newN (hDy := hDy) ht hsc' hP hn hT hCk hi hE htv hm hH hRP hPS
    case newBuf => exact cNQ <| mc_liftFN hm hC <| tstepMR_newBufN (hDy := hDy) ht hsc' hP hn hT hCk hi hE htv hm hH hRP hPS
    all_goals exact hAl.elim
  | case => exact cNQ <| mc_liftSN hm hC <| tstepMR_caseTN (hDy := hDy) (hbf := hbf) (hpx := hpx) ht hn hT hCk hi hE htv hm hH hRP hPS
  | _ => exact hAl.elim

/-- **(X) `tstepMCF_stepTKA_zf` with `FootNCE (CE η) E' r` on the witness.** -/
theorem tstepMCF_stepTKA_zfN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db : Ts → Res}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    (hT : Typed p cx th.term) (hCk : TermA4.CkW p η.wit cx th.term) (hi : FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf)
    (hE : EnvOK p η) (htv : TvOK cx) (hm : MemInv g (CE η) (stOf mem pairs th))
    (hH : MemHeld (CE η) (stOf mem pairs th) H)
    (hpx : PAx g mem pairs th) (hC : PromCrK (CE η) (stOf mem pairs th) cr db)
    (hia : StoreIall ρ η cx th)
    (hdw : StoreCrZ η cx (stOf mem pairs th) th)
    (hwp : ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf mem pairs th) ad.label)
    (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hfo : FpOK (CE η) (stOf mem pairs th)) (hrmw : NoPlantRMW (CE η) th) (hbf : g.boxFence = true)
    {Ok : Memory × List Ts × TTh → Prop}
    (hpo : OwnFrOp (CE η) cx th → ∀ lab c, (CE η).sto lab = some c → c.owner = some (CE η).tid →
      (CE η).pfr lab ≠ none → OpTgt th lab → PlantOp g mem pairs th (CE η) cr Ok lab c)
    (hni : OpNI cx th)
    (hclo : ∀ lab c, (CE η).sto lab = some c → Clo c.ty)
    (hbi : ∀ x b i v e, th.term = .let_ x (.bufInit b i v) e →
      (∀ rt w ad rti wi n, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 →
        evalAt th.env i = some (rti, [wi]) → numOf [wi] = some n → (CE η).pfr ad.label ≠ none →
        (CE η).rc ad.label ≤ n → n < (CE η).ini ad.label) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∀ o, PredU (CE η) ⟨ad.label, o⟩ → ∃ h, FirstW (stOf mem pairs th).mem ⟨ad.label, o⟩ h ∧
        h ∈ (stOf mem pairs th).promises ∧ ∀ t m, t ∈ (stOf mem pairs th).promises →
          (stOf mem pairs th).mem[t]? = some m → m.loc = ⟨ad.label, o⟩ →
          (stOf mem pairs th).vs.coh ⟨ad.label, o⟩ < t → h ≤ t) ∧
      (∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → (CE η).pfr ad.label ≠ none →
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hRP : RetPw th.σs th.stack cx.ret) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KeepQRS (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ FootNCE (CE η) E' r)
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) := by
  by_cases hAl : AllocT th.term
  rotate_left
  · have h := tstepMCF_stepTKA_zf (hDy := hDy) (hz0 := hz0) (hPb := hPb) (Ok := Ok) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia
      hdw hwp hwin hfo hrmw hbf hpo hni hclo hbi hRP hPS hSub hSig hTy hown1
    refine ⟨h.1, fun r hr hpa hok => ?_⟩
    obtain ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', hq, hF, hR⟩, hR2⟩ := h.2 r hr hpa hok
    exact ⟨Tot, H', C, F, cr', db', Gd, plh,
      ⟨E', ⟨hq.1, hq.2.1, hq.2.2, footNC_efoot hF (Nat.le_of_eq (tstep_nalloc hAl r hr))⟩, hF, hR⟩, ⟨hR2.1, hR2.2.1, hR2.2.2.1, hR2.2.2.2.1, hR2.2.2.2.2.1⟩⟩
  have hne : ∀ x op e, th.term = .let_ x op e → AllocOp op := fun x op e h => by rw [h] at hAl; exact hAl
  have hO : ¬ OwnOpT cx th.term := by
    rintro (⟨x, e, ⟨a, v, h⟩ | ⟨b, i, v, h⟩ | ⟨b, i, q, v, h⟩ | ⟨b, wi, jl, v, h⟩ | ⟨b, i, v, h⟩ | ⟨b, i, v, h⟩⟩ |
      ⟨x, rel, a, v, tok, e, u, h, -⟩) <;> exact hne _ _ _ h
  have hps : ¬ PubShape cx th := fun ⟨x, rel, a, v, tok, e, u, h, _⟩ => hne _ _ _ h
  have hnp : ∀ x a e, th.term ≠ .let_ x (.publish a) e := fun x a e h => hne _ _ _ h
  have hnb : ∀ x b i v e, th.term ≠ .let_ x (.bufInit b i v) e := fun x b i v e h => hne _ _ _ h
  have hnopA : opAtomP th.term = none := by
    generalize th.term = t0 at hAl
    cases t0 with
    | let_ x op e => cases op <;> first | rfl | (simp only [AllocT, AllocOp] at hAl)
    | _ => rfl
  have hZ2 : ZOK { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) th := by
    intro l _ hzl x b i v e ht rt w ad rti wi n h1 h2 h3 h4 hl hpf hrc
    subst hl
    have hlo := (hbi x b i v e ht).1 rt w ad rti wi n h1 h2 h3 h4 hpf hrc
    exact ⟨hlo, Nat.lt_of_lt_of_le hlo hzl.2⟩
  obtain ⟨Sp, hHL⟩ := hH.toS
  have hC' := PromCrP_drop hC.toP
  have hK0 := tstepMCF_stepKN (hDy := hDy) (g := { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l })
    (hZ := hZ2) hP hp hn hnd hsc hT hCk hi hE htv hm hHL hpx hC' hia hdw (fun h => absurd h hO) hnp hfo
    (fun h => absurd (Or.inl h) hO) hrmw hbf hRP hPS hSub hSig hTy
  have hV := repinCovU_stepK (g := { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l })
    (mem := mem) (pairs := pairs) hsc hT hi hE htv hO hps
  refine ⟨hK0.1, fun r hr hpa _ => ?_⟩
  obtain ⟨Tot, H', C, F, h1, h2, hcl, h3⟩ := hK0.2 r hr hpa
  obtain ⟨cr', hA, hsw, -⟩ := ThInvMCFSQ.toKA (th0 := th) h1
    (TermLiveProps.tstep_ext { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l }
      mem pairs th r hr).prom
  obtain ⟨E', hq, hF, hR⟩ := (ThInvMCFSQK.mono (Q' := fun E' => BiOut th E' ∧
    KeepQRS (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' (fun _ => .zero) ∧ FootNCE (CE η) E' r)
    (fun E' hk => ⟨biOut_nb hnb, keepQRS_of_keepQ hk.2 (covS_nil (hV r hr E')) (fulP_nop hnopA) (rcKeepP_nop hnopA) (pubKeep_np hnp), hk.1⟩) hA).toFQK
  refine ⟨Tot, H', C, F, cr', db, [], fun _ => .zero, ⟨E', ⟨hq.1, hq.2.1, hF.iniFixZ, hq.2.2⟩, efootDrop hz0 hF, hR⟩,
    mintStepDrop h2, ClaimAtP.of_not hcl (fun x a e h => hnp x a e h), Drop_nil,
    le_plh0 (G_nil (Res.le_def.2 fun k => ?_)), fun h => absurd h hps⟩
  have e1 := h3 k
  have e2 := hsw k
  simp only [Res.add_apply] at e1 e2 ⊢
  omega

#print axioms frame_nalloc
#print axioms tstepMCF_stepKN
#print axioms tstepMCF_stepTKA_zfN

#print axioms mcfs_addFoot
#print axioms mc_ofKFQ
#print axioms cNQ
#print axioms mc_liftFN
#print axioms mc_liftSN

end TermFootNK

import WeakCore.TermFootBPK
import WeakCore.TermPlantBI

/-! # TermFootBPKB (BI): the R4 stepper with the `bufInit`-at-`rc` pool consumed

`tstepMCF_stepTKA_zfNBB`: `TermPoolR4.StepPlProd`'s statement with the pool premise `hbiP`
(`TermPlant.HbiP`, after `hRP`) and `KeepQRSB` (cover without the `bufInit`-at-`rc` exclusion) in
the witness.  From `TermFootBPK.tstepMCF_stepTKA_zfNBC` at `KP := KeepQRSB`: the non-allocating,
non-`publish` step is `TermPlant.tstepMCF_stepTKA_zfB`; at `publish`/allocating terms `KeepQRS`
lifts (`keepQRSB_of_nb`, not a `bufInit`). -/

namespace TermFootBPKB
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermPiece TermPlant TermFootNC
  TermFootNP TermFootNK TermFootBP0 TermFootBPP
open TermOwnG0Defs
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open TermFootBPK

theorem tstepMCF_stepTKA_zfNBBN {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db cr₁ : Ts → Res}
    {cr₀ plb plf : Ts → Res}
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
      (CE η).pfr lab ≠ none → OpTgt th lab → PlantOp g mem pairs th (CE η) cr₁ Ok lab c)
    (hle : ∀ r ∈ tstep g mem pairs th, Ok r → ∀ t m, t ∈ (stOf mem pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
      mem[t]? = some m → (∀ f mf, f ∈ FpAt (CE η) ⟨m.loc.label, 0⟩ → mem[f]? = some mf → mf.loc.label = m.loc.label → t < f) →
      cr₁ t ≤ cr t)
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
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η))
    (hRP : RetPw th.σs th.stack cx.ret)
    (hbiP : HbiP g mem pairs th η H cr cr₀ plb plf db Ok) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KeepQRSB (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ FootNCE (CE η) E' r ∧ FootBP g E' th r ∧ NewCellSto g ρ η th E')
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
        (¬ PubShape cx th → Gd = []) :=
  tstepMCF_stepTKA_zfNBCN (hDy := hDy) (KP := fun r E' cr' plh =>
      KeepQRSB (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh) (hz0 := hz0) (hPb := hPb) (Ok := Ok)
    hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia hdw hwp hwin hfo hrmw hbf hbi hPS hSub hSig hTy hRP hown1
    (fun _ _ _ _ hnb hK => keepQRSB_of_nb hnb hK)
    (fun _ _ => tstepMCF_stepTKA_zfB (hDy := hDy) (hz0 := hz0) (hPb := hPb) (Ok := Ok) hP hp hn hnd hsc hT hCk hi hE htv hm hH hpx hC hia
      hdw hwp hwin hfo hrmw hbf hpo (fun _ => hle) hni hclo hbi hbiP hRP hPS hSub hSig hTy hown1)

/-- (BI) **The R4 stepper producer with the `bufInit`-at-`rc` pool consumed.** -/
theorem tstepMCF_stepTKA_zfNBB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {Rf Rs H : Res} {cr db cr₁ : Ts → Res}
    {cr₀ plb plf : Ts → Res}
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
      (CE η).pfr lab ≠ none → OpTgt th lab → PlantOp g mem pairs th (CE η) cr₁ Ok lab c)
    (hle : ∀ r ∈ tstep g mem pairs th, Ok r → ∀ t m, t ∈ (stOf mem pairs th).promises → t ∉ (stOf r.1 r.2.1 r.2.2).promises →
      mem[t]? = some m → (∀ f mf, f ∈ FpAt (CE η) ⟨m.loc.label, 0⟩ → mem[f]? = some mf → mf.loc.label = m.loc.label → t < f) →
      cr₁ t ≤ cr t)
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
        ∃ Sp, MemHeldL (CE η) (stOf mem pairs th) H Sp ∧ SlotPayS (CE η) (stOf mem pairs th) Sp cr db ad.label)) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η))
    (hRP : RetPw th.σs th.stack cx.ret)
    (hbiP : HbiP g mem pairs th η H cr cr₀ plb plf db Ok) (hown1 : PubLe1 th Rf Rs H := by assumption)
    (hz0 : ∀ l, ¬ g.zf l := by exact fun _ h => h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      (OwnFrOp (CE η) cx th → r.1 = mem) ∧ Ok r → ∃ Tot H' C F cr' db' Gd plh,
      ThInvMCFQK (fun E' => BiOut th E' ∧ KeepQRSB (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) th cr cr' plh ∧
          IniFixZ { g with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l } (CE η) E'
            (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ FootNCE (CE η) E' r ∧ FootBP g E' th r)
        p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 Tot H' cr' db' ∧
      MintStep g η (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) C F ∧ ClaimAtP th C F ∧
      Drop (CE η) (stOf mem pairs th) Gd ∧
      Tot + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf mem pairs th) db + C + Res.sum (Gd.map GdE.R) +
          pSum (stOf r.1 r.2.1 r.2.2) plh ≤
        Rf + Rs + H + pSum (stOf mem pairs th) cr + pSum (stOf r.1 r.2.1 r.2.2) db' + F ∧
      (PubShape cx th → GdCovT (CE η) (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) Gd th) ∧
        (¬ PubShape cx th → Gd = [])  :=
  let h := tstepMCF_stepTKA_zfNBBN (hDy := hDy) (hz0 := hz0) (hPb := hPb) (Ok := Ok) hP hp hn hnd hsc hT hCk hi hE htv hm hH
    hpx hC hia hdw hwp hwin hfo hrmw hbf hpo hle hni hclo hbi hPS hSub hSig hTy hRP hbiP hown1
  ⟨h.1, fun r hr hpa hok =>
    let ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', hq, hR⟩, hR2⟩ := h.2 r hr hpa hok
    ⟨Tot, H', C, F, cr', db', Gd, plh, ⟨E', ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1⟩, hR⟩, hR2⟩⟩

#print axioms tstepMCF_stepTKA_zfNBB

end TermFootBPKB

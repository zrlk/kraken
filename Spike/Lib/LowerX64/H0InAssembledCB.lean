/-
**`H0In` for a program with a setup block, assembled, at the setup call's
known frame condition** (x86-64; the twin of
`Spike/Lib/LowerA64/H0InAssembledCBA.lean`): `h0In_setup_assembled` /
`h0In_setup_assembledC` (`Spike/Lib/LowerX64/H0InAssembled.lean`,
`Spike/Lib/LowerX64/H0InAssembledC.lean`) over `h0In_of_setupFNPB`
(`Spike/Lib/LowerX64/H0InSetupB.lean`), the setup call `hS` at
`SetupCallWSB` with the callee's frame condition `SetupGF`
(`Spike/Lib/Rt/X64MainSSB.lean`), so the setup function's bottom frame is
known (`SetupBot`, `Spike/Lib/LowerX64/SetupBot.lean`). On x86-64 the
ghost's top is `TOP - 8` (the `callq` into `scc_rt_main` pushed its return
address), as in `h0_ofPlaceOK_setupFRB`.

- `h0In_setup_assembledFB`: `h0In_setup_assembled` at `SetupCallWSB` / `SetupGF`.
- `h0In_setup_assembledCB`: `h0In_setup_assembledC` at `SetupCallWSB` / `SetupGF`.
-/
import Spike.Lib.LowerX64.H0InAssembledC
import Spike.Lib.LowerX64.H0InSetupB

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open A9NoSpawn Scc.Cert.WideX64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2)
open Spike.Lib.X64.Rt (SetupCode SetupCallWSB SetupGF MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR
  rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC arOf marshal)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt
  (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (Spike.Lib.LowerNode.imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSX`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSX h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
  (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

/-- **`H0In` for a program with a setup block, assembled, at the setup
call's known frame condition** (`h0In_setup_assembled` through
`h0In_of_setupFNPB`): the setup call `hS` at `SetupCallWSB` with the
callee's frame condition `SetupGF`. Open: as `h0In_setup_assembled`. -/
theorem h0In_setup_assembledFB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hE : E.Ok (lay2 Λ p)) {L : Int}
    (hp0 : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) (fun _ => none) C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    (hfnB : Scc.Cert.Rt.X64.blockAtB (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (setupMC (setupWords2 p)).fn 0 Spike.Lib.X64.Flow.xHead = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    (hPostS : ∀ c rs, SPostC p (fun _ => none) ty C0 c rs → CFactsC c ∧ MainCtlC c [])
    (hPost : ∀ c fs v, UPostRF p (fun _ => none) c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hOff : (RS TOP).Off (-16) ∧ ∀ j < (setupMC (setupWords2 p)).sw, (RS TOP).Off (-24 - 8 * (j : Int)))
    (hme : ∀ y t ws, TermRun.lookupE (C0).env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep (fun _ => none) ws[k].val (TP0).toBitVec.toNat)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hL2 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 ZU1 ⟨TOP - 8#64, TP0, C0⟩
        (TP0).toBitVec))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p C0 cE fr)
    (hD8 : 8 ≤ D1) {chk entry : Label} {Zs lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hproS : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC (setupWords2 p)).setup chk entry Zs lim Lg zl zf z1 z2
      zs ps = true)
    (hphS : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC (setupWords2 p)).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hlcS : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 ZU2
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
      (UPostRF p (fun _ => none)) ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0) :
    H0In h E El Dt := by
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2 h hp hs'
  have htl := tail_setup_of_accepted2 h hp hs'
  have hsw := (setupIn_sw_eq h htl hc).1
  have hPlS := hPlS_ofSPostC (Λ := lay2 Λ p) (lbl := fun _ => none) (p := p) (ty := ty)
    (exe := (Ly).exe) (endPc := (Ly).endPc) (F := FS TOP) (Ly).lab
    (sc := setupMC (setupWords2 p)) (g := ⟨TOP - 8#64, TP0, C0⟩) (x0 := (TP0).toBitVec)
    (by simp only [setupMC]; omega) (Spike.Lib.LowerNode.simpleTy_of_accepted2 hp ty hty)
    (valWords_of_rtCodeOkS h hp hty hc) hOff hme
  exact h0In_of_setupFNPB h hE hp0 hf0 hov hC0 hpl0 hL hLm hL8 htl hc
    (hstk_of_placeOKAt h hp hs') hfnB hD10 hD18 hD20 hD28
    hPostS (fun _ _ _ h => h) hPost hPlS hL1 hL2 hZM hZS hZU hS hcall (hPS_framed (p := p)) hD8 hproS hphS hlcS hU

/-- **`H0In` for a program with a setup block, assembled, its code facts
discharged, at the setup call's known frame condition**
(`h0In_setup_assembledC` through `h0In_setup_assembledFB`): the setup call
`hS` at `SetupCallWSB` with the callee's frame condition `SetupGF`. Open: as
`h0In_setup_assembledC`. -/
theorem h0In_setup_assembledCB {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hE : E.Ok (lay2 Λ p)) {L : Int}
    (hp0 : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) (fun _ => none) C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    (hPost : ∀ c fs v, UPostRF p (fun _ => none) c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hOff : (RS TOP).Off (-16) ∧ ∀ j < (setupMC (setupWords2 p)).sw, (RS TOP).Off (-24 - 8 * (j : Int)))
    (hme : ∀ y t ws, TermRun.lookupE (C0).env y = some (t, ws) → ∀ k (hk : k < ws.length),
      ValRep (fun _ => none) ws[k].val (TP0).toBitVec.toNat)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hL2 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (TOP - 8#64 - 8#64 - (setupMC (setupWords2 p)).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWSB (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).setup (setupMC (setupWords2 p)).Z D1 ZU1 (SRetR (fun _ => none) ty)
      ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec C0 TP0
      (SetupGF p (Ly).lab ((MSS J) []) (RS v) (FS v) (setupMC (setupWords2 p)) D1 ZU1 ⟨TOP - 8#64, TP0, C0⟩
        (TP0).toBitVec))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p C0 cE fr)
    (hD8 : 8 ≤ D1)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2 ZU2
      (SetupArgs (SPostC p (fun _ => none) ty C0) (setupMC (setupWords2 p)).sw (TP0).toBitVec)
      (UPostRF p (fun _ => none)) ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec TP0) :
    H0In h E El Dt := by
  obtain ⟨chk, entry, Zs, lim, Lg, zl, zf, z1, z2, zs, ps, hproS, hphS, hlcS⟩ :=
    setupCode_ofPlaceOK hp hty h (Spike.Lib.LowerNode.imms2Me Λ p) (setupWords2 p)
  exact h0In_setup_assembledFB h hp hty hE hp0 hf0 hov hC0 hpl0 hL hLm hL8 (mainHead_ofPlaceOK hp h _)
    hD10 hD18 hD20 hD28 (postS_setupTerm (th02_term_setup hty _)) hPost hOff hme hL1 hL2 hZM hZS hZU hS hcall hD8
    hproS hphS hlcS hU

end Assembled

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.LowerX64.h0In_setup_assembledFB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0In_setup_assembledFB

/--
info: 'Spike.Lib.LowerX64.h0In_setup_assembledCB' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms h0In_setup_assembledCB

end Spike.Lib.LowerX64

/-
**The setup frame's bottom keys' exits** (AArch64; the twin of
`Spike/Test/X64Hello1BotH.lean`): `H1OpenA.hbot`'s per-key shape `ExitStk`
(`Spike/Lib/LowerA64/ResumeStk2.lean`) at a setup bottom key (`SetupBot`,
`Spike/Test/A64Hello1CxOkH.lean`'s `BotH` shape) at any family `J0` of the
key and any segment world `W`, memory side `ms` and labels `lbl` (a
landing's extended placement): `setupBot_exitStkMT`
(`Spike/Lib/LowerA64/SetupBotM.lean`) at the post `SPostC` of the key's
block's return type, the frame pop `hPS_framed`, the region facts from
`Bounds2A`.

- `exitStk_ofSetupBotBA`: the exits from the key's exits inside `W` (`hW`),
  `scc_rt_main`'s segment from `mainS0` at that post (`h0`) and the aborts'
  (`hAb`);
- `exitStk_ofBotHA`: the same at a `BotH` key, `h0` at each of its witnesses;
- `BotHRA`, `exitStk_ofBotHRA`: a `BotH` key at the `rodata` block, `h0` only there;
- `h0_ofMainS0LA`: `h0` at the setup type at a reachable placement (`mainS0_segL`), `main`'s call `hU` open;
- `exitStk_ofBotHRL`: the exits at a `BotHRA` key at a reachable placement, `hW`, `hAb`, `hU` open.
-/
import Spike.Lib.LowerA64.SetupBotM
import Spike.Test.A64Hello1CxOkH
import Spike.Lib.LowerA64.SetupCall2
import Spike.Lib.LowerA64.ResumeCxLBP
import Spike.Lib.LowerA64.MainS0L
import Spike.Lib.LowerA64.H0InAssembledCVBAF
import Spike.Lib.LowerA64.HPlSOfSPostC
import Spike.Lib.LowerA64.MainExitF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 swFSL mainS0)
open Spike.Lib.LowerNode (setupWords2 compiled2 imms2Me)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB's address. -/
local notation "X0" => pinA (Ly).lab + 0#64 + 8#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (X0)

set_option hygiene false in
/-- The switch region's frame condition at the private memory's `WordsNone`,
below the top `v` (`BotH`'s). -/
local notation "FS" v:max => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s code facts'). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1InLandA`'s). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (Spike.Lib.AllocReach.IN (Ar) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (`H1InLandA`'s). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (Spike.Lib.AllocReach.IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- A context's code at the saved return address (`fnCode2OfPMe`'s). -/
local notation "CD" ra:max =>
  CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra)

set_option hygiene false in
/-- The `j`th block's code facts (`ElH`'s). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

/-- **The exits at a setup bottom key** (`H1OpenA.hbot`'s per-key shape,
the twin of `X64Hello1BotH`'s `exitStk_ofSetupBotB`): at a key `k` the
setup frame's (`SetupBot` at the key's memory side `MSS J0 []`, any `J0`),
at the bounds `Bounds2A` it was taken at, the exits `ExitStk` reach `Q`
inside `W`, given the key's exits at its block's return type inside `W`
(`hW`), `scc_rt_main`'s segment from `mainS0` at the post `SPostC` of that
type (`h0`) and the aborts' segment (`hAb`). The block's return type is the
one `P` gives at `k.j` (no block, no exits). `scc_rt_main`'s return label
`sp0` is the setup call's `e0 + 4` by `mainSIn`'s label gap; the frame's
size from `setupMC_Z`; the frame pop by `hPS_framed`. -/
theorem exitStk_ofSetupBotBA (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    {W : FragS isaLSE2} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {Q : FragS isaLSE2} {P : Prog} {Ab₀ : FragS isaLSE2}
    {J0 : InvS} {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat} {v : BitVec 64}
    {k : StkKey} {fs : List TermRun.Frame}
    (hBd : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM)
    (hB : SetupBot p (Ly).lab ((MSS J0) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        W s c fs)
    (hAb : SegWS W K p lbl ms Ab₀ Q)
    (h0 : ∀ d, P[k.j]? = some d → SegWS W K p lbl ms
      ((At (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (mainS0 (Ly).lab (setupMC (setupWords2 p)) (SPostC p lbl d.retTy C0) ⟨TOP, TP0, C0⟩ (X0))).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hD10, -, -, -, hL1, -⟩ := hBd
  cases hj : P[k.j]? with
  | none =>
    exact hAb.mono_pre fun _ _ _ ⟨_, _, _, ⟨_, hd, _⟩, _⟩ => by rw [hj] at hd; cases hd
  | some d =>
    have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) (rtCodeOkS_setupWords2A h hp hs)).1
    have hZ := setupMC_Z _ hsw
    have hin := Spike.Lib.A64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2A h hp hs)
    simp only [Spike.Lib.A64.Rt.mainSIn, Bool.and_eq_true] at hin
    obtain ⟨⟨⟨⟨⟨-, -⟩, hg0⟩, -⟩, -⟩, -⟩ := hin
    haveI := (Ly).valid
    have esp0 : (Ly).lab (setupMC (setupWords2 p)).sp0 = (Ly).lab (setupMC (setupWords2 p)).e0 + 4 :=
      (Scc.Cert.Rt.A64.label_labelGap (Ly).lays hg0).trans rfl
    refine setupBot_exitStkMT (PostS := SPostC p lbl d.retTy C0) hD10 (by rw [hZ]; omega) (by rw [hZ]; omega)
      (show -L ≤ _ by omega) (show (0 : Int) ≤ 0 by decide) hB esp0 ?_ hW hAb (h0 d hj)
    rintro ty ⟨d', hd', rfl⟩ cE fr c rs hct hR
    rw [hj] at hd'
    cases hd'
    exact hPS_framed cE fr c rs hct hR

/-- **`exitStk_ofSetupBotBA` at a `BotH` key** (`H1OpenA.hbot`'s per-key
shape at `Bot := BotH h`; the twin of `X64Hello1BotH`'s `exitStk_ofBotH`):
`h0` at each of `BotH`'s witnesses. -/
theorem exitStk_ofBotHA (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    {W : FragS isaLSE2} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {Q : FragS isaLSE2} {P : Prog} {Ab₀ : FragS isaLSE2}
    {k : StkKey} {fs : List TermRun.Frame}
    (hB : BotH h k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, P[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        W s c fs)
    (hAb : SegWS W K p lbl ms Ab₀ Q)
    (h0 : ∀ (J0 : InvS) (L D1 : Int) (fS : Nat) (v : BitVec 64) (D2 : Int) (lS lM : String) (nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      SetupBot p (Ly).lab ((MSS J0) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs →
      ∀ d, P[k.j]? = some d → SegWS W K p lbl ms
        ((At (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
          (mainS0 (Ly).lab (setupMC (setupWords2 p)) (SPostC p lbl d.retTy C0) ⟨TOP, TP0, C0⟩ (X0))).at []) Q) :
    SegWS W K p lbl ms (ExitStk p P lbl (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  obtain ⟨⟨J0, L, D1, fS, v, D2, lS, lM, nS, fM, nM, hBd, hSB⟩, -⟩ := hB
  exact exitStk_ofSetupBotBA h hp hs hBd hSB hW hAb (h0 J0 L D1 fS v D2 lS lM nS fM nM hBd hSB)

/-- **`hello1`'s bottom keys at the setup block**: a `BotH` key, whose block
is `rodata` (`CxOkH`'s), so its return type is the setup result's and
`main`'s call `hU` exists at the key's post. `BotH` carries the block
itself; `BotHRA` names it at the setup block (the twin of `BotHR`). -/
abbrev BotHRA (k : StkKey) (fs : List TermRun.Frame) : Prop :=
  BotH h k fs

/-- **`exitStk_ofBotHA` at a `BotHRA` key** (`H1OpenA.hbot`'s per-key shape
at `Bot := BotHRA h`): `h0` only at the key's `rodata` block. -/
theorem exitStk_ofBotHRA (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true)
    {W : FragS isaLSE2} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {Q : FragS isaLSE2} {Ab₀ : FragS isaLSE2}
    {k : StkKey} {fs : List TermRun.Frame}
    (hB : BotHRA h k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 p)[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p lbl (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        W s c fs)
    (hAb : SegWS W K p lbl ms Ab₀ Q)
    (h0 : ∀ (J0 : InvS) (L D1 : Int) (fS : Nat) (v : BitVec 64) (D2 : Int) (lS lM : String) (nS fM nM : Nat),
      Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      SetupBot p (Ly).lab ((MSS J0) []) (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs →
      ∀ d, (compiled2 p)[k.j]? = some d → d.name = "rodata" → SegWS W K p lbl ms
        ((At (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
          (mainS0 (Ly).lab (setupMC (setupWords2 p)) (SPostC p lbl d.retTy C0) ⟨TOP, TP0, C0⟩ (X0))).at []) Q) :
    SegWS W K p lbl ms (ExitStk p (compiled2 p) lbl (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  obtain ⟨-, d', hd', hn⟩ := id hB
  refine exitStk_ofBotHA h hp hs hB hW hAb fun J0 L D1 fS v D2 lS lM nS fM nM hBd hSB d hd => ?_
  have e := Option.some.inj (hd.symm.trans hd')
  subst e
  exact h0 J0 L D1 fS v D2 lS lM nS fM nM hBd hSB d hd hn

/-- **A setup bottom key's `h0` at the setup type** (`mainS0_segL` at the
segment world `W2R J Dt L0 ls` of a reachable placement `L0`, `ls`): at the
bounds `Bounds2A`, `scc_rt_main`'s segment from `mainS0` at the post
`SPostC p L0 ty C0` of the setup result `ty`, given `main`'s call `hU` at
`L0`, `ls` (`mainCallWSF_ofVacHMVAFL`'s shape at the first stack's top).
The code facts from the placement check (`setupIn_sw_eq`, `mainPhS_of_tab`,
`hstkA_of_placeOKAt`, the setup's and `main`'s prologues); the start
control's facts at `L0` (`Start2C0A`); the marshalling block placed
(`hPlS_ofSPostC`); `main`'s exit at `UPostRF` (`uPostRF_exit`); the limit
word at depth from `hR`. -/
theorem h0_ofMainS0LA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {J : InvS} {Dt : State → Prop} {L0 : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    (hR : Spike.Lib.AllocReach.Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat} (hBd : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM)
    (hU : Spike.Lib.A64.Rt.MainCallWSF (W2R J Dt L0 ls) (KT) p L0 (MSR J L0 ls) (Ly).exe (Ly).endPc
      (swR (TOP) (-L) 0) (FS (TOP)) (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2
      (Int64.ofInt (fM : Int)) (Spike.Lib.A64.Rt.SetupArgs (SPostC p L0 ty C0) (setupMC (setupWords2 p)).sw (X0))
      (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0))
    (v : BitVec 64) {Q : FragS isaLSE2} :
    SegWS (W2R J Dt L0 ls) (KT) p L0 (MSR J L0 ls)
      ((At (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
        (mainS0 (Ly).lab (setupMC (setupWords2 p)) (SPostC p L0 ty C0) ⟨TOP, TP0, C0⟩ (X0))).at []) Q := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hLm, hL8, -, -, hD20, hD28, -, hL2, -, -, hZU, hOff⟩ := hBd
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hc := rtCodeOkS_setupWords2A h hp hs
  have htl := tail_setup_of_accepted2A h hp hs
  obtain ⟨hsw, hrt⟩ := setupIn_sw_eq h htl hc
  have hpro : ∀ {fn chk entry : _} {Z lim : Int64} {Lg : _}
      {ps : List (XReg × Int64)},
      prologueIn (Ly).prog fn chk entry Z lim Lg ps = true → chk ∉ Spike.Lib.A64.AllocG.abLabs →
      PosOff (Ly).prog (Ly).lab ((Ly).lab fn) := by
    intro fn chk entry Z lim Lg ps hpr hl
    simp only [prologueIn, Bool.and_eq_true] at hpr
    have hb := posOff_of_blockAt (lab := (Ly).lab) hpr.1.1.1.1.2 hl (i := 0) (by simp [chkHead])
    rw [show 4 * (0 + 0) = 4 * 0 from rfl, ofNat4_zero] at hb
    exact posOff_of_labelGap (Ly).lays hpr.1.1.1.1.1 hb
  obtain ⟨chkF, entryF, ZF, limF, LgF, psF, hproF, hlF⟩ := mainPro_ofPlaceOK hp h (setupWords2 p)
  obtain ⟨chk, entry, Zs, lim, Lg, ps, hproS, -, hlS⟩ := setupCode_ofPlaceOK hp hty h (imms2Me Λ p) (setupWords2 p)
  have hPlS := hPlS_ofSPostC (Λ := lay2 Λ p) (lbl := L0) (p := p) (ty := ty)
    (exe := (Ly).exe) (endPc := (Ly).endPc)
    (F := swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) (TOP)) (Ly).lab
    (sc := setupMC (setupWords2 p)) (g := ⟨TOP, TP0, C0⟩) (x0 := X0)
    (by simp only [setupMC]; omega) (Spike.Lib.LowerNode.simpleTy_of_accepted2 hp ty hty)
    (valWords_of_rtCodeOkSA h hp hty hc) hOff (hme_start2A h hty L0)
  have hPS := postS_setupTerm (p := p) (lbl := L0) (ty := ty) (c0 := C0) (th02_term_setup hty _)
  exact mainS0_segL h (imms2Me Λ p) (lbl0 := L0) (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hLm hL8 hsw hc
    (Spike.Lib.A64.Rt.mainPhS_of_tab h _ hrt)
    ⟨".L1_scc_rt_main.stack_grow", 0, hstkA_of_placeOKAt h hp hs, by decide, ofNat4_zero _⟩
    (hpro hproS hlS) (hpro hproF hlF) hD20 hD28 hL2 hR hZU (hC0_start2A h hty L0) (hov_start2A hty _)
    (fun c rs h => (hPS c rs h).1) ⟨hf0_start2A hty _, hov_start2A hty _, hpl0_start2A h hty L0⟩
    (fun c rs h => (hPS c rs h).2) (fun _ _ _ h => h.2) hPlS hU
    (fun s c fs v hP hAt => uPostRF_exit _ _ s c fs v hP.1 hAt) v

/-- **The exits at a `BotHRA` key at a reachable placement** (`exitStk_ofBotHRA`
with `h0` by `h0_ofMainS0LA`): at the segment world `W2R J Dt L0 ls`, given
the key's exits inside it (`hW`), the aborts' segment (`hAb`), the `rodata`
block's return type the setup result's (`hret`) and `main`'s call at `L0`,
`ls` at every bounds (`hU`). -/
theorem exitStk_ofBotHRL (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hret : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → d.retTy = ty)
    {J : InvS} {Dt : State → Prop} {L0 : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    (hR : Spike.Lib.AllocReach.Reach (Ar) (fun _ => none) (fun _ => 0) L0 ls)
    {Q Ab₀ : FragS isaLSE2} {k : StkKey} {fs : List TermRun.Frame} (hB : BotHRA h k fs)
    (hW : ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 p)[k.j]? = some d ∧ d.retTy = ty) → ∀ s c,
      ExitC2SL p L0 (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty (fun _ _ _ => False) s c fs →
        (W2R J Dt L0 ls) s c fs)
    (hAb : SegWS (W2R J Dt L0 ls) (KT) p L0 (MSR J L0 ls) Ab₀ Q)
    (hU : ∀ (L D1 D2 : Int) (lS lM : String) (fS nS fM nM : Nat), Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM →
      Spike.Lib.A64.Rt.MainCallWSF (W2R J Dt L0 ls) (KT) p L0 (MSR J L0 ls) (Ly).exe (Ly).endPc
        (swR (TOP) (-L) 0) (FS (TOP)) (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2
        (Int64.ofInt (fM : Int)) (Spike.Lib.A64.Rt.SetupArgs (SPostC p L0 ty C0) (setupMC (setupWords2 p)).sw (X0))
        (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
        ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0)) :
    SegWS (W2R J Dt L0 ls) (KT) p L0 (MSR J L0 ls) (ExitStk p (compiled2 p) L0 (Ly).exe (Ly).endPc k fs Ab₀) Q := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  refine exitStk_ofBotHRA h hp hs hB hW hAb fun _ L D1 fS v D2 lS lM nS fM nM hBd _ d hd hn => ?_
  rw [hret _ d hd hn]
  exact h0_ofMainS0LA h hp hty hR hBd (hU L D1 D2 lS lM fS nS fM nM hBd) v

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.exitStk_ofSetupBotBA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.exitStk_ofSetupBotBA

/-- info: 'Spike.Lib.LowerA64.exitStk_ofBotHA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.exitStk_ofBotHA

/-- info: 'Spike.Lib.LowerA64.exitStk_ofBotHRA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.exitStk_ofBotHRA

/-- info: 'Spike.Lib.LowerA64.h0_ofMainS0LA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.h0_ofMainS0LA

/-- info: 'Spike.Lib.LowerA64.exitStk_ofBotHRL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.exitStk_ofBotHRL

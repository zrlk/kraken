/-
**`hello1`'s bottom keys' exits inside the segment world** (AArch64): the
premise `hW` of `hello1_hbotA` (`Spike/Test/A64Hello1HBot.lean`). At a
`BotHRA` key's exit (`ExitC2SL`'s return disjunct at the setup frame), the
setup function's return pops its one frame to `scc_rt_main`'s `mainS0`
(`setupBot_popM`, the frame pop `hPS_framed`); there `W2` holds by the
segment `h0_ofMainS0LA` at the extended placement (its entry inside its
world), and `w2_ofPopped` carries it back to the exit's pair: the popped
control (the setup call's continuation, `postS_setupTerm`) neither
allocates nor overflows, the exit's pair is free of `ZBad` (a `ret` over
the setup frame) and placed (`RetJS.placed`, the setup frame by
`framesPlaced_setup`).

- `w2_ofSetupBotA`: `W2` at a setup bottom key's exit, at any `Accepted2` program;
- `hello1_hWBotA`: `hello1_hbotA`'s `hW`;
- `hello1_hbotA'`: `hello1_hbotA` closed by `hello1_hWBotA`.
-/
import Spike.Test.A64Hello1HBot
import Spike.Lib.LowerA64.W2Pop
import Spike.Lib.LowerA64.SetupBotPop
import Spike.Lib.LowerA64.PlacedRetJS
import Spike.Lib.LowerA64.FramesPlacedSetup

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.LowerNode (compiled2 hello1o_accepted2 setupWords2)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Rt (rtF setupMC)

section Assembled

open Kraken.Promising.Lower.A64
open Scc.Cert.WideA64
open Spike.Lib.A64.Rt (rS0 swFSL mainS0)
open Spike.Lib.LowerNode (imms2Me)

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

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
/-- The allocator's arena of the output. -/
local notation "ArP" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1InLandA`'s). -/
local notation "W2P" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (ArP)
    (Spike.Lib.AllocReach.IN (ArP) (fun _ => none) (fun _ => 0) J) Dt (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (`H1InLandA`'s). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (ArP) (Spike.Lib.AllocReach.IN (ArP) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

/-- **`W2` at a setup bottom key's exit** (the per-state shape of
`hello1_hbotA`'s `hW`, at any `Accepted2` program): at a `SetupBot` key
(any key memory side `ms0`) at the bounds `Bounds2A`, at its exit's return
disjunct at the setup result type `ty` and a reachable placement `L0`,
`ls`, `W2` inside `W2P J Dt L0 ls`: the pop to `mainS0` (`setupBot_popM`,
`hPS_framed`), `W2` there by `h0_ofMainS0LA`'s segment (`main`'s call
`hU`), back by `w2_ofPopped` (the popped control by `postS_setupTerm`, the
exit's `ret` placed by `RetJS.placed`, the setup frame by
`framesPlaced_setup`). -/
theorem w2_ofSetupBotA (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {J : InvS} {Dt : State → Prop} {L0 : WeakMem.AllocLabel → Option Nat} {ls : WeakMem.AllocLabel → Nat}
    (hR : Spike.Lib.AllocReach.Reach (ArP) (fun _ => none) (fun _ => 0) L0 ls)
    {L D1 D2 : Int} {lS lM : String} {fS nS fM nM : Nat} (hBd : Bounds2A cfg p (Ly) L D1 D2 lS lM fS nS fM nM)
    (hU : Spike.Lib.A64.Rt.MainCallWSF (W2P J Dt L0 ls) (KT) p L0 (MSR J L0 ls) (Ly).exe (Ly).endPc
      (swR (TOP) (-L) 0) (FS (TOP)) (setupMC (setupWords2 p)).fn (setupMC (setupWords2 p)).Z D2
      (Int64.ofInt (fM : Int)) (Spike.Lib.A64.Rt.SetupArgs (SPostC p L0 ty C0) (setupMC (setupWords2 p)).sw (X0))
      (fun c fs v => UPostRF p L0 c fs v ∧ MainCtlV (lay2 Λ p) L0 c fs v)
      ((Ly).lab (setupMC (setupWords2 p)).sp1).toBitVec (TP0))
    {ms0 : MemSide isaLSE2} {v : BitVec 64} {k : StkKey} {fs : List TermRun.Frame}
    (hSB : SetupBot p (Ly).lab ms0 (Ly).exe (Ly).endPc (swR v (-L) 0) (FS v)
      (setupMC (setupWords2 p)) D1 (Int64.ofInt fS) ⟨TOP, TP0, C0⟩ (X0) k fs)
    {c0 : Ctl} {s : State} {c : Ctl}
    (hA : ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
      At (Ly).exe (Ly).endPc k.R k.F ((retNSL p L0 k.fp k.ra c0' ty).withTp k.tp) s c) :
    (W2P J Dt L0 ls) s c fs := by
  have hs : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  -- the region facts, as `exitStk_ofSetupBotBA`'s
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hD10, -, -, -, hL1, -⟩ := id hBd
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs) (rtCodeOkS_setupWords2A h hp hs)).1
  have hZ := setupMC_Z _ hsw
  have hin := Spike.Lib.A64.Rt.mainSIn_of_okS (rtCodeOkS_setupWords2A h hp hs)
  simp only [Spike.Lib.A64.Rt.mainSIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨-, -⟩, hg0⟩, -⟩, -⟩, -⟩ := hin
  haveI := (Ly).valid
  have esp0 : (Ly).lab (setupMC (setupWords2 p)).sp0 = (Ly).lab (setupMC (setupWords2 p)).e0 + 4 :=
    (Scc.Cert.Rt.A64.label_labelGap (Ly).lays hg0).trans rfl
  -- the pop to `mainS0`
  obtain ⟨cE, fr, c'', rfl, hct, -, hAt⟩ := setupBot_popM (PostS := SPostC p L0 ty C0)
    hD10 (by rw [hZ]; omega) (by rw [hZ]; omega) (show -L ≤ _ by omega) (show (0 : Int) ≤ 0 by decide) esp0
    hSB hPS_framed hA
  -- `W2` at the popped pair, from `scc_rt_main`'s segment
  have hW0 : (W2P J Dt L0 ls) s c'' [] := by
    obtain ⟨inv, hP, hiW, -⟩ := h0_ofMainS0LA h hp hty hR hBd hU v (Q := fun _ _ _ => False)
    exact hiW s c'' [] (hP s c'' [] ⟨hAt, rfl⟩)
  -- the popped control's facts
  obtain ⟨-, -, -, -, σ0, -, -, hP0, -⟩ := hAt
  have hC := postS_setupTerm (th02_term_setup hty _) c'' σ0.regs hP0
  -- the exit's facts
  obtain ⟨c0', -, -, -, -, -, σ, hAbs, -, ⟨⟨hJ, -⟩, -⟩, -⟩ := hA
  obtain ⟨a, -, -, -, -, -, hta, -⟩ := id hJ
  -- the setup frame
  obtain ⟨dr, hf, -⟩ := Spike.Lib.LowerNode.rodata_of_setupOf hp hty
  have hc0t := th02_term_setup hty (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))
  have hct' := callTo_setupTerm (p := p) (c0 := C0) hc0t (by simp only [th02, hty]; rfl) hf
  obtain ⟨-, rfl⟩ := CallTo.unique hct hct'
  refine w2_ofPopped (Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp) hW0 hC.1.noAlloc hC.2.2
    (List.cons_ne_nil _ _) ⟨by rw [hta]; trivial, fun fr hfr => ?_⟩ ?_
  · rw [List.mem_singleton] at hfr
    subst hfr
    have h0 := (hf0_start2A hty (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).1
    rw [hc0t] at h0
    exact h0.2
  · obtain ⟨B, hFP⟩ := framesPlaced_setup h hp hty hct' s
    exact .of_placedS (PlacedS.ofFrames (RetJS.placed hJ _ hAbs.regs)
      (FramesPlaced.mono_lbl (fun _ _ h0 => by cases h0) hFP.toFramesPlaced))

end Assembled

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout: any layout at which the placement check passes (`h`). -/
local notation "LeA" => Λx

/-- The compiler's output for the program. -/
local notation "OA" => Out.ofEmitted (Scc.Lower.A64.lowerAll SccCertificate.config P1A)

section Hello1

variable (h : placeOKAt SccCertificate.placeCfg (lay2 LeA P1A) OA = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me LeA P1A)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 LeA P1A)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (`H1RestAW`'s). -/
local notation "W2R" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (Ly)) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A)
    (Spike.Lib.A64.PhRec.own (Ly)) (Spike.Lib.A64.Rt.rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- The extended placement's labels. -/
local notation "LU" => Spike.Lib.AllocReach.upd L l b

set_option hygiene false in
/-- The extended placement's sizes. -/
local notation "LN" => Spike.Lib.AllocReach.updN ls l n

set_option hygiene false in
/-- The start's frame condition: the private memory loading no runtime word and `rtF`. -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- `hello1o`'s landings at the bottom keys `BotHRA`. -/
local notation "ElR" => ElA h (fnCode2OfPMe hello1o_accepted2 h LeA) (CxOkH h hello1o_accepted2) (BotHRA h)

/-- **`hello1`'s bottom keys' exits inside `W2R`** (`hello1_hbotA`'s `hW`):
at a `BotHRA` key's exit, the pop to `mainS0` (`setupBot_popM` with
`hPS_framed`), `W2` there from `h0_ofMainS0LA`'s segment (`main`'s call by
`hello1_hUAFL`), carried back by `w2_ofPopped`. -/
theorem hello1_hWBotA {E : Entry} :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHRA h k fs → ∀ c0 ty, k.G0 c0 → (∃ d, (compiled2 P1A)[k.j]? = some d ∧ d.retTy = ty) →
        ∀ s c, ExitC2SL P1A (LU) (Ly).exe (Ly).endPc k.R k.F k.fp k.ra k.tp c0 fs ty
          (fun _ _ _ => False) s c fs → (W2R J (LU) (LN)) s c fs := by
  intro J _ L ls l b n hR hl hAL k fs hB c0 ty _ hty' s c hE
  obtain ⟨⟨J0, L', D1, fS, v, D2, lS, lM, nS, fM, nM, hBd, hSB⟩, d', hd', hn⟩ := hB
  obtain ⟨d, hd, rfl⟩ := hty'
  cases Option.some.inj (hd.symm.trans hd')
  rw [Spike.Lib.LowerNode.rodata_retTy_compiled2 hello1o_accepted2 hello1_htyA.choose_spec hd hn] at hE
  exact w2_ofSetupBotA h hello1o_accepted2 hello1_htyA.choose_spec (.step hR hl hAL) hBd
    (hello1_hUAFL h hBd J (.step hR hl hAL) _) hSB (hE.resolve_right id).2

/-- **`hello1_hbotA` closed**: its `hW` by `hello1_hWBotA`. -/
theorem hello1_hbotA' {E : Entry} :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
        ∀ s c fs, StartsSA h E (WNF) (ElR) (fun _ => True) (ab2 P1A (Ly).lab) L ls s c fs → J L ls s c fs) →
      ∀ L ls l b n, Reach (Ar) (fun _ => none) (fun _ => 0) L ls → L l = none →
        Spike.Lib.HeapLand.AllocLand (Ar).heap (Ar).cells b n →
      ∀ k fs, BotHRA h k fs →
        SegWS (W2R J (LU) (LN)) (TakeK ((Ly).lab StackTake.siteL) (Spike.Lib.A64.Rt.rS0 (Ly))) P1A
          (LU)
          (msOfAX (lay2 LeA P1A) (Spike.Lib.A64.PhRec.μ (Ly)) P1A Spike.Lib.LowerNode.IsNum (G2 h P1A)
            (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
            (ab2 P1A (Ly).lab) (LU) (LN))
          (ExitStk P1A (compiled2 P1A) (LU) (Ly).exe (Ly).endPc k fs (GA (CxOkH h hello1o_accepted2)))
          fun _ _ _ => False :=
  hello1_hbotA h (hello1_hWBotA h)

end Hello1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.w2_ofSetupBotA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.w2_ofSetupBotA

/-- info: 'Spike.Lib.LowerA64.hello1_hWBotA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hWBotA

/-- info: 'Spike.Lib.LowerA64.hello1_hbotA'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hbotA'

/-
**`H0In` from the setup-block start** (x86-64): `h0_ofPlaceOK_setupFN` at
the instance `Closed2At` fixes. `W2At` / `MSAt` at the immediates
`imms2Me Λ p`, `rd := True`, `ls0 := 0` and the abort `ab2` are by
definition `Closed2At`'s `W2R … none 0` / `MSR … none 0`, and the start
`At … (entryN0 c0)` at `FE := rtF Ly` and `c0` the program's start control
(`th02` at `meW2`) is `S0X`; so no transport is needed. `FE`'s premises are
`rtF_stable` and `rtF_takeMem` at `rS0_sub`.

- `h0In_of_setupFN`: `H0In` from `h0_ofPlaceOK_setupFN`'s other inputs,
  its two `W2`-side calls (`hS`, `hU`) for every frame invariant `J`
  holding at the starts.
- `h0In_of_setupFNP`: the same with `scc_rt_main`'s code facts from the
  placement check (A11 at the given `sw`: `setupIn_sw_eq`, `mainPhS_of_tab`)
  and the positions off the write abort from the code: the stack-growth
  stub's label in the code (`hstk`, decided per output: A11 does not
  check it), the setup's head from its prologue (`hproS`) and the user
  function's head (`hfnB`), the labels decided off the write abort.
-/
import Spike.Lib.LowerX64.Closed2At
import Spike.Lib.LowerX64.RtMainXN
import Spike.Lib.LowerX64.SetupSw
import Spike.Lib.LowerX64.RtStartXOf

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
open Spike.Lib.LowerNode (FrOk2 ZBad)
open Spike.Lib.X64.Rt (SetupCode SetupCallWS MainCallWSF MainSW SetupArgs swFSL mainSIn oU rS0 entryR rtF setupMC
  rtCodeOkS mainS0R mainSRR CFactsC arOf marshal)

section Setup

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) o)).term, (th02 p (meW2 (lay2 Λ p) o)).env, none⟩ : Ctl)

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

/-- **`H0In` from the setup-block start**: `h0_ofPlaceOK_setupFN` at
`FE := rtF Ly`, `rd := True`, `ls0 := 0`, `ab := ab2` and the program's
start control, its `W2`-side calls `hS`, `hU` at every frame invariant
holding at the starts. -/
theorem h0In_of_setupFN {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hE : E.Ok (lay2 Λ p)) {lbl0 : Lbl} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) lbl0 C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    {sw : Nat} (hsw : sw < 6) (hc : rtCodeOkS (Ly).prog (setupMC sw) = true)
    (hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw))
    (hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow))
    (hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup))
    (hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn))
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hPlS : BlkW (fun s c => Placed (lay2 Λ p) lbl0 s c ∧ PlacedS (lay2 Λ p) (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).sp0).toBitVec C0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p C0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p C0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hD8 : 8 ≤ D1) {chk entry : Label} {Zs lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hproS : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true)
    (hphS : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hlS : (setupMC sw).setup ∉ Spike.Lib.X64.AllocG.abLabs) (hlcS : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2
      (SetupArgs PostS (setupMC sw).sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64))) :
    H0In h E El Dt :=
  ⟨fun J hJ => h0_ofPlaceOK_setupFN h (Spike.Lib.LowerNode.imms2Me Λ p) (rd := Spike.Lib.LowerNode.IsNum)
    (J := J) (Dt := Dt)
    (ls0 := fun _ => 0) (ab := ab2 p (Ly).lab) hE (fun _ hm => hm) (Spike.Lib.X64.Rt.rtF_stable _ hE)
    (fun _ _ hm => Spike.Lib.X64.Rt.rtF_takeMem _ (Spike.Lib.X64.Rt.rS0_sub _) hm) hp hf0 hov hC0 hpl0 hL hLm hL8
    hsw hc hph hgrow hset hfn hD10 hD18 hD20 hD28 hPostS hPU hPost hPlS hL1 hL2 hZM hZS hZU (hS J hJ) hcall hPS hD8
    hproS hphS hlS hlcS (hU J hJ)⟩

/-- **`H0In` from the setup-block start, the runtime's code facts from the
placement check** (`h0In_of_setupFN`): at a `.setup` tail (`hs`) and the
runtime's code at `setupMC sw` (`hc`, A11 then gives `sw < 6` and
`MainPhS`), the stack-growth stub's label in the code (`hstk`), the setup's
head from its prologue (`hproS`) and the user function's head (`hfnB`) at
their labels' offset `0`, both labels off the write abort by `decide`. -/
theorem h0In_of_setupFNP {E : Entry} {El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {Dt : State → Prop} (hE : E.Ok (lay2 Λ p)) {lbl0 : Lbl} {L : Int}
    (hp : ProgNoS ZBad p) (hf0 : FrOk2 C0 []) (hov : ¬ OvfReady C0) (hC0 : CFacts (lay2 Λ p) lbl0 C0)
    (hpl0 : ∀ s, PlacedS (lay2 Λ p) (fun _ => none) s C0 [])
    (hL : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0)
    (hs : o.place.tail = .setup) {sw : Nat} (hc : rtCodeOkS o.prog (setupMC sw) = true)
    (hstk : Scc.Cert.Rt.X64.InRunB o.prog ".Lscc_rt_main.stk" 0)
    (hfnB : Scc.Cert.Rt.X64.blockAtB o.prog (setupMC sw).fn 0 Spike.Lib.X64.Flow.xHead = true)
    {D1 D2 : Int} (hD10 : 0 ≤ D1) (hD18 : D1 % 8 = 0) (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU1 ZU2 : Int64}
    {PostR PostS : Ctl → Reg64s → Prop} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    (hPostS : ∀ c rs, PostS c rs → CFactsC c ∧ MainCtlC c [])
    (hPU : ∀ c fs v, Post c fs v → UPostRF p (fun _ => none) c fs v)
    (hPost : ∀ c fs v, Post c fs v → MainCtlN (lay2 Λ p) (fun _ => none) c fs)
    (hPlS : BlkW (fun s c => Placed (lay2 Λ p) lbl0 s c ∧ PlacedS (lay2 Λ p) (fun _ => none) s c []) (fun _ _ => False)
      (Ly).exe (Ly).endPc ((swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
        (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) (stacksA (Ly).lab + 0#64 + 16384#64) m ∧
        CallerCells (swR (stacksA (Ly).lab + 0#64 + 16384#64) (-L) 0) (-8 - 0) (8 - L) 8 m)
      (mainS0R (Ly).lab (setupMC sw) PostS
        ⟨stacksA (Ly).lab + 0#64 + 16384#64 - 8#64, tpOf (pinA (Ly).lab + 0#64 + 8#64), C0⟩
        (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec)
      (marshal (setupMC sw).sw (setupMC sw).fn))
    (hL1 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D1 ≤ L) (hL2 : 8 + 8 + (setupMC sw).Z.toInt + 8 + D2 ≤ L)
    (hZM : (Ly).stacksA.toNat + 4096 ≤
      (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec).toNat)
    (hZS : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU1.toBitVec).toNat)
    (hZU : (Ly).stacksA.toNat + 4096 ≤ (stacksA (Ly).lab + 0#64 + 16384#64 - 8#64 - 8#64 - (setupMC sw).Z.toBitVec -
      8#64 - 8#64 - ZU2.toBitVec).toNat)
    (hS : ∀ J : InvS, StJ J → ∀ v, SetupCallWS (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).setup (setupMC sw).Z D1 ZU1 PostR ((Ly).lab (setupMC sw).sp0).toBitVec C0
      (tpOf (pinA (Ly).lab + 0#64 + 8#64)))
    (hcall : ∃ cE fr, Spike.Lib.X64.Flow.CallTo p C0 cE fr)
    (hPS : ∀ cE fr c rs, Spike.Lib.X64.Flow.CallTo p C0 cE fr → PostR c rs →
      ∃ c'', FrameRun p (c, [fr]) (c'', []) ∧ PostS c'' rs)
    (hD8 : 8 ≤ D1) {chk entry : Label} {Zs lim : Int64} {Lg : Label} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)}
    (hproS : Spike.Lib.X64.Flow.prologueIn (Ly).prog (setupMC sw).setup chk entry Zs lim Lg zl zf z1 z2 zs ps = true)
    (hphS : blkPh (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (fun _ => false) (Ly).lab
      ((Ly).lab (setupMC sw).setup + Int64.ofNat 0) 0 Spike.Lib.X64.Flow.xHead = true)
    (hlcS : chk ∉ Spike.Lib.X64.AllocG.abLabs)
    (hU : ∀ J : InvS, StJ J → ∀ v, MainCallWSF (W2S J) (TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))) p
      (fun _ => none) (MSS J) (Ly).exe (Ly).endPc
      ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)
      (fun m => swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64)
          (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m ∧
        CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)
      (setupMC sw).fn (setupMC sw).Z D2 ZU2
      (SetupArgs PostS (setupMC sw).sw (tpOf (pinA (Ly).lab + 0#64 + 8#64)).toBitVec) Post
      ((Ly).lab (setupMC sw).sp1).toBitVec (tpOf (pinA (Ly).lab + 0#64 + 8#64))) :
    H0In h E El Dt := by
  obtain ⟨hsw, hrt⟩ := setupIn_sw_eq h hs hc
  have hph : MainPhS (Spike.Lib.X64.PhRec.okPc (Ly)) (Spike.Lib.X64.PhRec.ph (Ly)) (Ly).lab (setupMC sw) :=
    mainPhS_of_tab (Ly) (Spike.Lib.X64.Rt.PhRecOf.hlab_ofPlaceOK h _) hrt fun _ hf => hf
  have hlS : (setupMC sw).setup ∉ Spike.Lib.X64.AllocG.abLabs := by simp only [setupMC]; decide
  have hlF : (setupMC sw).fn ∉ Spike.Lib.X64.AllocG.abLabs := by simp only [setupMC]; decide
  have hgrow : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).grow) :=
    ⟨".Lscc_rt_main.stk", 0, hstk, by decide, by simp [setupMC]⟩
  have hhd : Scc.Cert.Rt.X64.blockAtB (Ly).prog (setupMC sw).setup 0 Spike.Lib.X64.Flow.xHead = true := by
    simp only [Spike.Lib.X64.Flow.prologueIn, Bool.and_eq_true] at hproS
    exact hproS.1.1.1.1.1.2
  have hset : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).setup) := by
    have h' := posOff_of_blockAtB (lab := (Ly).lab) hhd hlS (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h'
  have hfn : PosOff (Ly).prog (Ly).lab ((Ly).lab (setupMC sw).fn) := by
    have h' := posOff_of_blockAtB (cells := (Ly).prog) (lab := (Ly).lab) hfnB hlF (by decide)
    rwa [Spike.Lib.X64.Flow.ofNat_zero'] at h'
  exact h0In_of_setupFN h hE hp hf0 hov hC0 hpl0 hL hLm hL8 hsw hc hph hgrow hset hfn hD10 hD18 hD20 hD28
    hPostS hPU hPost hPlS hL1 hL2 hZM hZS hZU hS hcall hPS hD8 hproS hphS hlS hlcS hU

end Setup

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.h0In_of_setupFN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0In_of_setupFN

/-- info: 'Spike.Lib.LowerX64.h0In_of_setupFNP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h0In_of_setupFNP

end Spike.Lib.LowerX64

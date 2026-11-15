/-
**`main`'s call at the bare start from `main`'s segment** (x86-64; the twin
of the AArch64 `mainCallWSF_bareSeg` and `userCallWSF_of_mainCallWSF` in
`Spike/Lib/LowerA64/G1NoSetupCall.lean` and
`Spike/Lib/LowerA64/G1NoSetupCallStmt.lean`): for an `Accepted2` program
without a setup block, `scc_rt_main` (`bareMC`) calls `main` directly;
`main`'s call `MainCallWSF` at the arguments `fun c _ => c = c0` is
`mainCallWSF_ofPlaceOKHMVCR0`'s (`Spike/Lib/LowerX64/G1NoSetupCallA.lean`)
with the construct premise `MainSeg2`'s at the context facts `MainCx2`
(`mainCx2_bare`, `Spike/Lib/LowerX64/G1NoSetupCall.lean`), the entry
control the start control `c0`.

- `mainSig_bare2`: without a setup block `main` takes the unit and returns
  `Int`;
- `userCallWSF_of_mainCallWSF`: the entry `uN0` at the ghost `c0` is `uNM`
  at the arguments `fun c _ => c = c0`, so `MainCallWSF` there is
  `UserCallWSF`;
- `mainCallWSF_bareSeg`: `main`'s call `MainCallWSF` at the switch region's
  frame condition with `WordsNone`, from `MainSeg2` (`Bounds0X`'s bounds).
-/
import Spike.Lib.LowerX64.G1NoSetupCall
import Spike.Lib.LowerX64.G1NoSetupCallA
import Spike.Test.X64Hello1HU

namespace Spike.Lib.LowerX64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Flow.Ret0
open Scc.Sem (Range ValRep)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerS (InvS)
open Spike.Lib.X64.Rt (RuntimeLayout bareMC rS0 MainCallWSF UserCallWSF swFSL)

/-- **Without a setup block `main` takes the unit and returns `Int`**
(`main2` at `setupOf p = none`). -/
theorem mainSig_bare2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) (hs : Scc.Lower.setupOf p = none) {d : Decl}
    (hfd : p.find? (·.name == "main") = some d) : d.argTy = .unit ∧ d.retTy = .int := by
  have hds : Scc.Lower.decls2 [] (Scc.Lower.setupOf p) (Scc.Lower.hasPrint p) p = true := by
    simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.2
  have hn : d.name = "main" := by simpa using List.find?_some hfd
  obtain ⟨E', hE'⟩ := decl2_of_decls2 hds d (List.mem_of_find?_eq_some hfd)
  have hpe : Scc.Lower.isPrintExt d = false := by simp [Scc.Lower.isPrintExt, hn]
  have hnl : (Scc.Lower.hasPrint p && "main" == "printL") = false := by
    rw [show ("main" == "printL") = false by decide, Bool.and_false]
  simp only [Scc.Lower.decl2, hpe, hn, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true] at hE'
  rw [hnl] at hE'
  simp only [Bool.false_eq_true, ↓reduceIte] at hE'
  unfold Scc.Lower.main2 at hE'
  rw [hs] at hE'
  simp only [Bool.and_eq_true, beq_iff_eq] at hE'
  exact ⟨hE'.1.2, hE'.1.1.2⟩

/-- **`MainCallWSF` at the arguments `c = c0` is `UserCallWSF` at the ghost
`c0`**: at a ghost with `g.c0 = c0`, `uN0`'s invariant is `uNM`'s at
`fun c _ => c = c0`. -/
theorem userCallWSF_of_mainCallWSF {W : FragS isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {fn : Label} {Z : Int64} {D : Int} {ZU : Int64} {Post : Ctl → List TermRun.Frame → BitVec 64 → Prop}
    {ra : BitVec 64} {c0 : Ctl} {tp : UInt64}
    (h : MainCallWSF W K p lbl ms exe endPc R F fn Z D ZU (fun c _ => c = c0) Post ra tp) :
    UserCallWSF W K p lbl ms exe endPc R F fn Z D ZU Post ra c0 tp := by
  intro F' hR hF hFF g hra hc0 htp
  subst hc0
  exact h F' hR hF hFF g hra htp

section Generic

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- `W2At` at `Closed2At`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max => MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The stack take at the first stack's range. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- `scc_rt_main`'s callee region of the switch region at depth `L`, below
the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top
`v`, the caller's cells outside `RS v`. -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (stacksA (Ly).lab + 0#64 + 16384#64) (limA (tpOf (pinA (Ly).lab + 0#64 + 8#64))) v m) ∧
  CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- `main`'s code (`fnCode2OfPMe`'s choice, at the theorem's immediates). -/
local notation "FC" => fnCode2OfPMe hp h Λ j d hd

set_option hygiene false in
/-- The ghosts at `main`'s frame: the controls a frame run reaches from the entry control `cP` at no frame. -/
local notation "GM" cP:max => fun c => Spike.Lib.FrameRunM p (cP, []) (c, [])

/-- **`main`'s call at `WordsNone ∧ swFSL` from `main`'s segment without a
setup block** (the bare twin of `mainCallWSF_ofMainSeg2F`): off the first
stack's top no state is in the frame condition; at it,
`mainCallWSF_ofPlaceOKHMVCR0` at `main`'s code facts from the placement
check and `Accepted2` (`main` takes the unit and returns `Int`, held
returns from `mainRetOk`, `main`'s frame `fM` from the bounds' `main` row),
the callee frame's context facts `MainCx2` by `mainCx2_bare`, and
`CalleePre2R` and the constructs' segments from `MainSeg2` at the entry
control `c0` (`frOk2_c0`) and the ghosts `GM c0`. -/
theorem mainCallWSF_bareSeg {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true)
    (hs : Scc.Lower.setupOf p = none) (hm : Scc.Lower.mainRetOk p = true) (hcfg : CfgNeedOk pcfg = true)
    {L D : Int} {lM : String} {fM nM : Nat}
    (hB : Bounds0X cfg p sizes labelOffs (Ly) L D lM fM nM) (J : InvS) (HM : MainSeg2 h hp Dt J)
    (v : BitVec 64) :
    MainCallWSF (W2S J) (KT) p (fun _ => none) (MSS J) (Ly).exe (Ly).endPc (RS v) (FS v)
      bareMC.fn bareMC.Z D (Int64.ofInt (fM : Int)) (fun c _ => c = Spike.Lib.X64Consumer.c0)
      (fun c fs v => UPostRF p (fun _ => none) c fs v ∧ MainCtlV (lay2 Λ p) (fun _ => none) c fs v)
      ((Ly).lab bareMC.sp0).toBitVec TP0 := by
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    intro F' _ _ hFF _ _ _
    refine ⟨fun _ _ _ => False, fun s c fs hP => ?_, fun _ _ _ h => h.elim, fun _ _ _ h => h.elim⟩
    obtain ⟨⟨-, -, -, -, σ, -, hF, -⟩, -⟩ := hP
    exact hv (hFF _ hF).1.1.2.1.1
  obtain ⟨-, -, -, -, -, hrowM, -⟩ := id hB
  obtain ⟨d, hfd⟩ : ∃ d, p.find? (·.name == "main") = some d := by
    have hm' : p.any (·.name == "main") = true := by
      simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp; exact hp.1.1.1.1.1.1.1.1.2
    exact Option.isSome_iff_exists.mp
      (List.find?_isSome.mpr (List.any_eq_true.mp hm') : (p.find? (·.name == "main")).isSome)
  obtain ⟨hu, hint⟩ := mainSig_bare2 hp hs hfd
  obtain ⟨j, hd, hdn⟩ := Spike.Lib.LowerNode.main_compiled2 hfd
  have hok : Scc.Lower.heldRetOk d.body = true := by simpa [Scc.Lower.mainRetOk, hfd] using hm
  have hsub := Spike.Lib.X64.Rt.rS0_sub (Ly)
  obtain ⟨w, hLw, hna, hmem, hfr⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hna0 : (FC).na = 0 := by
    have hw := hLw.1
    rw [hu, show Scc.Obj.valWords .unit = some 0 from rfl] at hw
    rw [hna]; exact (Option.some.inj hw).symm
  have hframe : (FC).fr.size = fM := by
    rw [hfr]; exact hrowM _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hdn])
  refine mainCallWSF_ofPlaceOKHMVCR0 (Λv := lay2 Λ p) (CxOk := fun _ _ _ _ _ _ _ _ => True) hp h hd (FC)
    (fnCode2OfPMe_spec hp h Λ j d hd).2.2 (fnCode2OfPMe_spec hp h Λ j d hd).1 hint
    hok (hlitP_of_mainRetOk hm hfd) (mainUIn_bare2 h hp hs)
    (by rw [(FC).hfn, hdn]; rfl) (posOff_proL_main h hp hd) hu hfd hna0 (by rw [hframe]) ?_
    (fun m hm => hm.1.2.1.2) hsub (Spike.Lib.X64.Rt.fitS_of_sub _ hsub) (progNoS_zbad_of_accepted2 hp) ?_
  · rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1
  · intro F' hok' hst hFF g hra htp _
    have hC := mainCx2_bare h hp hs hcfg hB hv hok' hst hFF hra htp
    obtain ⟨Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩ := HM j d hd hdn _ F' g _ hC frOk2_c0
    rw [htp] at hab hC2 hL hN hP hCH hPH
    exact ⟨GM Spike.Lib.X64Consumer.c0, Ab, hab, hC2, hL, hN, hP, hCH, hPH, hA⟩

end Generic

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.mainSig_bare2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainSig_bare2

/-- info: 'Spike.Lib.LowerX64.userCallWSF_of_mainCallWSF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.userCallWSF_of_mainCallWSF

/-- info: 'Spike.Lib.LowerX64.mainCallWSF_bareSeg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.mainCallWSF_bareSeg

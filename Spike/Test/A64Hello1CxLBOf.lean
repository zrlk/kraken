/-
**The setup frame's base context `SetupCxLB` from the setup call's
premises** (AArch64): `SetupOpenA.hcx` at `CxOk0 := SetupCxLB`
(`Spike/Test/A64Hello1HsOf.lean`), the facts `CxLB` at the setup callee's
region `RC`, frame condition `F'`, frames `[fr]`, ghosts `GR g fr` and
aborts `AbU2`, from `PRE F' g fr` and the bounds (`Bounds2A`'s `fS ≤ nS`,
`nS + 48 + 208 ≤ D1`, the frame row `hrow`, the switch region's `L`).

Closed here: the region's facts (`hR`, `hal`, `hl`, `hh`, `hlo`, `hhi`,
`hFS`, `hFO` by `stackOff_callee`), the frame's cells in the region (`hrs`,
`regionOff_of_rsOf`), the setup frame placed (`hfp`: its only live word,
`me`'s, at the immediate `imms2Me_setupK`), the read words (`hrd`), the
labels (`hroom`, `hrg`, `hHW`: none placed), the ghosts (`hG0F` by
`FrOk2.runM`, `hG0` by `FrameRunM.trans`), the kernel's ABI (`hK`), the
heap aborts (`hAb`, `AbU2`'s right side). Left as premises: the private
memory loads no heap or static word (`hwn`) and the allocator's `W2`
instance (`hAW`).

- `setupCxLB_ofPreT`: `CxLB` at the setup frame at any walk predicate `T`
  and aborts `Ab'` from `PRE`, `hwn`, `hAW`, `hAb` at `T`;
- `setupCxLB_ofPre`: `SetupCxLB` at the setup frame from `PRE`, `hwn`,
  `hAW` (`setupCxLB_ofPreT` at `TailAt2`, `hAb` by `AbU2`'s right side).
-/
import Spike.Test.A64Hello1HsOf
import Spike.Lib.LowerA64.HeldRes
import Spike.Lib.LowerA64.FramesPlacedSetup

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf bareMC swFSL)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.AllocReach (IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The program's start control (`S0A`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (swR v (-L) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0

set_option hygiene false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

/-- **`setupCxLB_ofPre` at any walk predicate `T` and aborts `Ab'`**
(`CxLB`'s `hAW` and `hAb` the only fields reading the walk): `CxLB` at the
setup frame at `T` from the allocator's `W2` instance and the heap aborts'
states, from a call node `NbJcOf`, in `Ab'` at `T`. -/
theorem setupCxLB_ofPreT (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (v : BitVec 64) {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame} {T : Expr → Prop} {Ab' : FragS isaLSE2}
    (hR0 : (RC).OK) (hal : (RC).base.toNat % 16 = 0) (hF' : FStable (RC) F')
    (hFF : ∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m)
    (hct : Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr)
    (hwn : ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem)
    (hAW : AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (RC) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p) T
      (RetLk d.retTy))
    (hAb : ∀ (Jc : Spike.Lib.A64.Flow.AS → Ctl → Prop) (pcR : Int64) s c,
      NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).cx Jc →
      (∀ σ c', Jc σ c' → T c'.term) →
      At (Ly).exe (Ly).endPc (RC) F' (Spike.Lib.A64.Flow.NewBuf.nbX ((MSS J) [fr])
        (_root_.Executable.labels (Ly).exe).label (fun _ => none) (RC) (fnCode2OfPMe hp h Λ j d hd).cx.frame pcR Jc
        .abort) s c → Ab' s c [fr]) :
    CxLB (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.A64.PhRec.GOf Ly M0)
      (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
      (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe (Ly).endPc (MSS J)
      (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra) (imms2Me Λ p) T (RetLk d.retTy) (RC) F' [fr] g.fp g.ra (TP0)
      (GR g fr) Ab' := by
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo0 : (RC).lo ≤ -((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) := by
    show -D1 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (RC).hi := Int.le_refl _
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  exact {
    hR := hR0
    hal := hal
    hl := by show (-D1) % 8 = 0; omega
    hh := by show (0 : Int) % 8 = 0; rfl
    hlo := by show -D1 ≤ -((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) + -160 - 48; rw [hframe]; omega
    hhi := hhi
    hFS := hF'
    hFO := by
      intro m hm
      obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
      subst hv
      have hok : (swR (TOP) (-L) 0).OK := by
        rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
      have h8 : (swR (TOP) (-L) 0).base.toNat % 8 = 0 := by
        show (TOP).toNat % 8 = 0
        rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
      exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl)
        (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
    hrs := fun _ _ hr => regionOff_of_rsOf (fnCode2OfPMe hp h Λ j d hd).hf hlo0 hhi hr
    hfp := fun s _ => framesPlaced_setup h hp hty hct s
    hrd := by
      intro w
      dsimp only [MSAt]
      generalize ab2 p _ = ab
      cases ab <;> exact fun hw => hw
    hroom := fun _ _ hl => nomatch hl
    hrg := fun _ _ hl => nomatch hl
    hwn := hwn
    hHW := fun _ _ _ _ hl => nomatch hl
    hG0F := fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2A hty _))
    hG0 := fun _ _ h1 h2 => h1.trans h2
    hK := msOfAX_K_abi
    hAW := hAW
    hAb := hAb }

/-- **`SetupOpenA.hcx` at `SetupCxLB`** (`CxLB` at the setup frame): at the
setup callee's region `RC`, a frame condition `F'` with the setup call's
facts (`hR0`, `hal`, `hF'`, `hFF`), the start's call of the setup block
leaving `fr` (`hct`), the bounds (`hfS`, `hnS`, the switch region's `L`,
the frame row `hrow`), `CxLB` at the frames `[fr]`, ghosts `GR g fr` and
aborts `AbU2`, given that the private memory loads no heap or static word
(`hwn`) and the allocator's `W2` instance (`hAW`). -/
theorem setupCxLB_ofPre (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (v : BitVec 64) {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame}
    (hR0 : (RC).OK) (hal : (RC).base.toNat % 16 = 0) (hF' : FStable (RC) F')
    (hFF : ∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m)
    (hct : Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr)
    (hwn : ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem)
    (hAW : AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).cx
      (CdCLE OP (Spike.Lib.A64.PhRec.okPc LY0) (Spike.Lib.A64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.A64.PhRec.GOf Ly M0) (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (RC) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p) (TailAt2 p j)
      (RetLk d.retTy)) :
    SetupCxLB h hp Dt J hd j (RC) F' [fr] g.fp g.ra (TP0) (GR g fr)
      (AbU2 p (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr] g.fp g.ra (GR g fr)) := by
  exact setupCxLB_ofPreT h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hR0 hal hF' hFF hct hwn hAW
    fun Jc pcR _ _ hJ _ hA => .inr ⟨rfl, Jc, pcR, hJ, hA⟩

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.setupCxLB_ofPreT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupCxLB_ofPreT

/-- info: 'Spike.Lib.LowerA64.setupCxLB_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupCxLB_ofPre

end Spike.Lib.LowerA64

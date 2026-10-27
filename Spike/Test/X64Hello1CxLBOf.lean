/-
**The setup frame's base context `SetupCxLB` from the setup call's
premises** (x86-64; the twin of `Spike/Test/A64Hello1CxLBOf.lean`):
`SetupOpen.hcx` at `CxOk0 := SetupCxLB` (`Spike/Test/X64Hello1HsOf.lean`),
the facts `CxLB` in the rebased setup callee's region `rbR RC`, frame
condition `F'`, frames `[fr]` and ghosts `GR g fr`, from `PRE F' g fr` and
the bounds (`Bounds2`'s `fS + 8 ≤ nS`, `nS + 48 + 208 ≤ D1`, the frame row
`hrow`, the switch region's `L`).

Closed here: the region's facts (`hR`, `hR8`, `hl`, `hh`, `hlo`, `hhi`,
`hFS` by `rbR_ok`, `rbR_base`, `rbR_fstable`; `hFO` by `stackOff_callee`
twice and `stackOff_rbR`), the frame's cells in the region (`hrs`,
`regionOff_of_rsOf`), the setup frame placed (`hfp`, `framesPlaced_setup`),
the read words (`hrd`), the labels (`hroom`, `hrg`, `hHW`: none placed), the
ghosts (`hG0F` by `FrOk2.runM`, `hG0` by `FrameRunM.trans`), the kernel's
ABI (`hK`). Left as premises: the private memory loads no heap or static
word (`hwn`), the allocator's `W2` instance (`hAW`) and, unlike the AArch64
twin (whose aborts are `AbU2`), the heap aborts' states in the aborts `Ab`
(`hAb`; the x86-64 `AbAl` is pending).

- `setupCxLB_ofPreT`: `CxLB` at the setup frame at any walk predicate `T`
  from `PRE`, `hwn`, `hAW`, `hAb` at `T`;
- `setupCxLB_ofPre`: `SetupCxLB` at the setup frame from `PRE`, `hwn`,
  `hAW`, `hAb` (`setupCxLB_ofPreT` at `TailAt2`).
-/
import Spike.Test.X64Hello1HsOf
import Spike.Lib.LowerX64.HeldRes

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable At)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Flow.NewBuf (nbX)
open Spike.Lib.X64.Rt (setupMC rS0 arOf swFSL)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (IN)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates (`fnCode2OfP`'s). -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.X64.PhRec.m0Of (Ly).Λ OP
  (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The switch region's frame condition, below the top `v`. -/
local notation "FS" v:max => (fun m => swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m ∧
  CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

/-- **`setupCxLB_ofPre` at any walk predicate `T`** (`CxLB`'s `hAW` and
`hAb` the only fields reading it): `CxLB` at the setup frame at `T`, from
the allocator's `W2` instance and the heap aborts' states at `T`. -/
theorem setupCxLB_ofPreT (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (v : BitVec 64) {L D1 : Int} {fS nS : Nat} (hfS : fS + 8 ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame} {Ab' : FragS isa} {T : Expr → Prop}
    (hR0 : (RC).OK) (hR8 : (RC).base.toNat % 8 = 0) (hF' : FStable (RC) F')
    (hFF : ∀ m, F' m → (FS v) m ∧
      CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m)
    (hct : Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr)
    (hwn : ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem)
    (hAW : AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
      T (RetLk d.retTy))
    (hAb : ∀ (Jc : Spike.Lib.X64.AS → Ctl → Prop) (pcR : Int64) s c,
      NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).fr Jc →
      (∀ σ c', Jc σ c' → T c'.term) →
      At (Ly).exe (Ly).endPc (rbR (RC)) F' (nbX ((MSS J) [fr]) (_root_.Executable.labels (Ly).exe).label
        (fun _ => none) (rbR (RC)) (fnCode2OfPMe hp h Λ j d hd).fr.size pcR Jc .abort) s c → Ab' s c [fr]) :
    CxLB (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (Spike.Lib.X64.PhRec.GOf Ly M0)
      (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (arOf (Ly).Λ)
      (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ly).lab (KT) (Ly).exe (Ly).endPc (MSS J)
      (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra) (imms2Me Λ p) T (RetLk d.retTy) (rbR (RC)) F' [fr] g.fp g.ra (TP0)
      (GR g fr) Ab' := by
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo1 : (RC).lo ≤ -8 := by show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ (RC).hi := by show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hlo0 : (rbR (RC)).lo ≤ -((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) := by
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (rbR (RC)).hi := by show (0 : Int) ≤ 8 + 8; decide
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  exact {
    hR := rbR_ok hR0 hlo1 hhi1
    hR8 := by omega
    hl := by show (-D1 + 8) % 8 = 0; omega
    hh := by show ((8 : Int) + 8) % 8 = 0; decide
    hlo := by
      show -D1 + 8 ≤ -((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) - 8 + -160 - 32; rw [hframe]; omega
    hhi := by show (16 : Int) ≤ 8 + 8; decide
    hFS := rbR_fstable hR0 hlo1 hhi1 hF'
    hFO := by
      intro m hm
      refine stackOff_rbR hR0 hlo1 hhi1 ?_
      have H := hFF m hm
      have hv := H.1.1.1.1
      subst hv
      have hok : (swR (TOP) (-L) 0).OK := by
        rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
      have htop8 : (TOP).toNat % 8 = 0 := by
        rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
      have hR1 : (RS (TOP)).OK :=
        Region.callee_ok hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
          (by show _ ≤ (0 : Int); omega)
      have hb1 : ((RS (TOP)).base.toNat : Int) = (TOP).toNat - 8 :=
        Region.callee_base hok (by show -L ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      have hb8 : (RS (TOP)).base.toNat % 8 = 0 := by omega
      exact Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
        (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
        (by show _ < (8 : Int); omega) (by omega)
        (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
          (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
          (by show _ < (0 : Int); omega) (by decide) H.1.1.2 H.1.2)
        H.2
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
    hG0F := fun _ hc0 => FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2 hty _))
    hG0 := fun _ _ h1 h2 => h1.trans h2
    hK := msOfAX_K_abi
    hAW := hAW
    hAb := hAb }

/-- **`SetupOpen.hcx` at `SetupCxLB`** (`CxLB` at the setup frame): at the
setup callee's region `RC`, a frame condition `F'` with the setup call's
facts (`hR0`, `hR8`, `hF'`, `hFF`), the start's call of the setup block
leaving `fr` (`hct`), the bounds (`hfS`, `hnS`, the switch region's `L`,
the frame row `hrow`), `CxLB` in the rebased region `rbR RC` at the frames
`[fr]`, ghosts `GR g fr` and aborts `Ab'`, given that the private memory
loads no heap or static word (`hwn`), the allocator's `W2` instance
(`hAW`) and the heap aborts' states, from a call node `NbJcOf`, in `Ab'`
(`hAb`). -/
theorem setupCxLB_ofPre (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    {Dt : State → Prop} (J : InvS) (v : BitVec 64) {L D1 : Int} {fS nS : Nat} (hfS : fS + 8 ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 8 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    (hrow : ∀ f, f ∈ (Scc.Lower.X64.lowerAll cfg p).low.ir.funcs → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" → (frOf (Scc.Lower.X64.lowerAll cfg p).low.ir f).size = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    {F' : MachineData → Prop} {g : WcG} {fr : TermRun.Frame} {Ab' : FragS isa}
    (hR0 : (RC).OK) (hR8 : (RC).base.toNat % 8 = 0) (hF' : FStable (RC) F')
    (hFF : ∀ m, F' m → (FS v) m ∧
      CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m)
    (hct : Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr)
    (hwn : ∀ m, F' m → Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem)
    (hAW : AllocW2At p (fun _ => none) (fun _ => 0) (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
      (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec g.ra))
      ((fnCode2OfPMe hp h Λ j d hd).Bl g.ra)
      (fun lbl lsize s c => W2 (Ly).Λ (Spike.Lib.X64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum
        (Spike.Lib.X64.PhRec.GOf Ly M0) (Spike.Lib.X64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly))
        (arOf (Ly).Λ) (IN (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J) Dt (Ab (Ly).lab) lbl lsize s c [fr])
      (KT) (Ly).exe (Ly).endPc (rbR (RC)) F' ((MSS J) [fr]) g.fp g.ra (TP0) (GR g fr) (imms2Me Λ p)
      (TailAt2 p j) (RetLk d.retTy))
    (hAb : ∀ (Jc : Spike.Lib.X64.AS → Ctl → Prop) (pcR : Int64) s c,
      NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).fr Jc →
      (∀ σ c', Jc σ c' → TailAt2 p j c'.term) →
      At (Ly).exe (Ly).endPc (rbR (RC)) F' (nbX ((MSS J) [fr]) (_root_.Executable.labels (Ly).exe).label
        (fun _ => none) (rbR (RC)) (fnCode2OfPMe hp h Λ j d hd).fr.size pcR Jc .abort) s c → Ab' s c [fr]) :
    SetupCxLB h hp Dt J hd j (RC) F' [fr] g.fp g.ra (TP0) (GR g fr) Ab' := by
  exact setupCxLB_ofPreT h hp hty J v hfS hnS hL0 hLm hL8 hD18 hL1 hrow hd hn hR0 hR8 hF' hFF hct hwn hAW hAb

end Assembled

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.setupCxLB_ofPreT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupCxLB_ofPreT

/-- info: 'Spike.Lib.LowerX64.setupCxLB_ofPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupCxLB_ofPre

end Spike.Lib.LowerX64

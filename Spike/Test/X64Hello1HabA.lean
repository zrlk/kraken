/-
**`hello1`'s setup frame's buffer allocations' heap aborts never end**
(x86-64): `SetupOpen.habA` (`Spike/Test/X64Hello1HS.lean`) from
`heapAb_seg` (`Spike/Lib/LowerX64/HeapAbX.lean`) at every call node
invariant and landing pc of `AbAl2` (`SegWS.exists_pre`), in the setup
call's rebased callee region (`rbR_facts`, `rbR_base`, `stackOff_rbR`, the
region facts as `hS_ofOpen`'s), the setup frame placed
(`framesPlaced_setup`), the memory side's aborts and kernel and arena
(`MSAt`'s; its units at most the source's, `arena_ofWords_units_le`).

Left open: the write tail at the heap stub's `write` (`hDtH`), and the setup frame's
size bound against the callee's depth (`hD`: the allocator's frame and the
dispatcher's below the setup frame; `Bounds2` gives it).

- `hello1_habA`: `SetupOpen.habA` from the above.
-/
import Spike.Lib.LowerX64.HeapAbX
import Spike.Test.X64Hello1HS

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
open Spike.Lib.X64.Flow.Ret0 (LimOk WcG CallerCells limA)
open Spike.Lib.X64.Flow.NewBuf (nbX allocAbortDepth)
open Spike.Lib.LowerNode (FrOk2 ZBad setupWords2 compiled2)
open Spike.Lib.X64.Rt (swFSL rS0 setupMC)

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)

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

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises (`X64Hello1HS`'s `PRE`). -/
local notation "PRE" F':max g:max fr:max => (RC).OK ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option linter.unusedVariables false in
/-- **`SetupOpen.habA` at `hello1`'s shape**: the buffer allocations' heap
abort exits at the setup frame never end inside `W2` (`heapAb_seg` at each
call node invariant and landing pc, `SegWS.exists_pre`): off the first
stack's top no state is in the frame condition (`swFSL`); at it, the
rebased callee region's facts as `hS_ofOpen`'s, the setup frame placed
(`framesPlaced_setup`), `MSAt`'s aborts, kernel, arena and units; open:
the heap stub's `write` tail (`hDtH`), the frame's room (`hD`). -/
theorem hello1_habA {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) {L D1 : Int} (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hD : ((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) + 208 ≤ D1)
    (J : InvS) (v : BitVec 64)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F''
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s) :
    ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
        (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False) := by
  rintro F' _ fr ⟨hR0, hF', hFF, -, -, hct, -⟩
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs ⟨-, Jc, pcR, -, ⟨-, -, -, -, σ, -, hF, -⟩⟩
    exact hv (hFF _ hF).1.1.1.1
  subst hv
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
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
  have hbc := Region.callee_base (hi' := 8) (kc := -8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0)
    (lo' := -D1) hR1 (by show 8 - L ≤ _; omega) (by omega) (by show _ < (8 : Int); omega)
  have hlo0 : ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤
      -8 - ((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) := by
    show -D1 ≤ _; omega
  have hhi0 : (8 : Int) ≤ ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
    show (8 : Int) ≤ 8; exact Int.le_refl _
  have hFO0 : ∀ m, F' m → StackOff (rS0 (Ly))
      ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8) m := fun m hm =>
    Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L) % 8 = 0; omega)
      (by show (8 : Int) % 8 = 0; decide) (by show 8 - L ≤ _; omega) (by omega)
      (by show _ < (8 : Int); omega) (by omega)
      (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L) % 8 = 0; omega)
        (by show (0 : Int) % 8 = 0; rfl) (by show -L ≤ _; omega) (by omega)
        (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2 (hFF m hm).1.2)
      (hFF m hm).2
  obtain ⟨hF2, hR2, -, -⟩ := rbR_facts hF' hR0 hlo0 hhi0
  have hb2 := rbR_base hR0 (by omega) (by omega)
  refine SegWS.exists_pre (P := fun (q : (Spike.Lib.X64.AS → Ctl → Prop) × Int64) s c fs => fs = [fr] ∧
      NbJcOf (Spike.Lib.LowerNode.imms2Me Λ p) (fun _ => none)
        (fnCode2OfPMe hp h Λ j d hd).fr q.1 ∧
      Spike.Lib.X64.At (Ly).exe (Ly).endPc (rbR ((RS (TOP)).callee
          (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)) F'
        (nbX ((MSS J) [fr]) (_root_.Executable.labels (Ly).exe).label (fun _ => none)
          (rbR ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8))
          (fnCode2OfPMe hp h Λ j d hd).fr.size q.2 q.1 .abort) s c)
      (fun ⟨Jc, pcR⟩ => ?_) |>.mono_pre fun s c fs ⟨hfs, Jc, pcR, hJ, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
  by_cases hJc : NbJcOf (Spike.Lib.LowerNode.imms2Me Λ p) (fun _ => none)
    (fnCode2OfPMe hp h Λ j d hd).fr Jc
  case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p) (rS := rS0 (Ly))
  refine (heapAb_seg h (Spike.Lib.LowerNode.imms2Me Λ p) (Λw := (Ly).Λ) (fs := [fr]) (pcR := pcR)
    (fnCode2OfPMe hp h Λ j d hd).hf hJc hR2
    (by omega) (by simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame, rbR, Region.callee]; omega)
    (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
    (by simp only [rbR, Region.callee]; omega) hF2
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _))
    (fun m hm => stackOff_rbR hR0 (by omega) (by omega) (hFO0 m hm))
    (fun s _ => framesPlaced_setup h hp hty hct s) ?_ ?_ ?_ ?_ ?_ hDtH _).mono_pre ?_
  · intro n τ us hus
    dsimp only [MSAt]; generalize ab2 p _ = ab
    cases ab <;>
      (show (Spike.Lib.X64.Rt.arOf (Ly).Λ).units n τ ≤ _
       unfold Spike.Lib.X64.Rt.arOf; exact arena_ofWords_units_le hus)
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · rintro s c fs ⟨rfl, -, hA⟩
    exact ⟨hA, rfl⟩

end Assembled

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_habA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_habA

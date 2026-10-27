/-
**`hello1`'s setup frame's buffer allocations' heap aborts never end**
(AArch64; the twin of `Spike/Test/X64Hello1HabA.lean`): `SetupPreA.habA`
(`Spike/Test/A64Hello1SetupOpenOf.lean`) from `heapAb_seg`
(`Spike/Lib/LowerA64/HeapAbA.lean`) at every call node invariant and
landing pc of `AbAl2` (`SegWS.exists_pre`), in the setup call's callee
region (the region facts as `setupCxLB_ofPre`'s), the setup frame placed
(`framesPlaced_setup`), the memory side's aborts and kernel and arena
(`MSAt`'s; its units at most the source's, `Arena.ofWords_units_le`).

Left open: the write tail at the heap stub's `write` (`hDtH`; trivial at
`Dt := fun _ => True`) and the setup frame's room below the callee's depth
(`hD`: the allocator's frame and the dispatcher's below the setup frame;
`Bounds2A` gives it, `hello1_habAB`).

- `hello1_habA`: `SetupPreA.habA` from the above;
- `hello1_habAB`: from the bounds' `fS ≤ nS`, `nS + 48 + 208 ≤ D1` and the frame row.
-/
import Spike.Lib.LowerA64.HeapAbA
import Spike.Test.A64Hello1SetupOpenOf

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL rtF)
open Spike.Lib.A64.WriteAb (Ab)
open Spike.Lib.LowerNode (setupWords2 compiled2 TailAt2 imms2Me addFreeT)
open Spike.Lib.A64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Flow.NewBuf (nbX allocAbortDepth)

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
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The output's code. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ OP (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).secs

set_option hygiene false in
/-- `W2At` at `Closed2AtA`'s instance. -/
local notation "W2S" J:max => W2At h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum (rS0 (Ly)) J Dt (fun _ => 0)

set_option hygiene false in
/-- `MSAt` at `Closed2AtA`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- The frame invariant `J` holds at the starts (`StartsSA`). -/
local notation "StJ" J:max => ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
  ∀ s c fs, StartsSA h E (rtF (Ly)) El Dt (ab2 p (Ly).lab) L ls s c fs → J L ls s c fs

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
set_option linter.unusedVariables false in
/-- The ghosts at the setup frame. -/
local notation "GR" g:max fr:max => fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's segment's premises (`SetupOpenA.hcx`'s `PRE`). -/
local notation "PRE" F':max g:max fr:max => (RC).OK ∧ (RC).base.toNat % 16 = 0 ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (swR v (-L) 0) (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).e0 + 4).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.A64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option linter.unusedVariables false in
/-- **`SetupPreA.habA`** (`heapAb_seg` at each call node invariant and
landing pc of `AbAl2`): the setup call's callee region `RC`, its facts
from `PRE` and the bounds, the first stack off it (`stackOff_callee`), the
setup frame placed (`framesPlaced_setup`), `MSAt`'s units at most the
source's (`Arena.ofWords_units_le`), cells, counter, aborts and kernel;
open: the room `hD` and the heap stub's `write` tail `hDtH`. -/
theorem hello1_habA {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) {L D1 : Int} (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0) (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hD : ((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) + 208 ≤ D1)
    (J : InvS) (v : BitVec 64)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s) :
    ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
        (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False) := by
  rintro F' _ fr ⟨hR0, hal, hF', hFF, -, -, hct, -⟩
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hFO : ∀ m, F' m → StackOff (rS0 (Ly)) (RC) m := by
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
  refine SegWS.exists_pre (P := fun (q : (Spike.Lib.A64.Flow.AS → Ctl → Prop) × Int64) s c fs => fs = [fr] ∧
      NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).cx q.1 ∧
      At (Ly).exe (Ly).endPc (RC) F'
        (nbX ((MSS J) [fr]) (_root_.Executable.labels (Ly).exe).label (fun _ => none) (RC)
          (fnCode2OfPMe hp h Λ j d hd).cx.frame q.2 q.1 .abort) s c)
      (fun ⟨Jc, pcR⟩ => ?_) |>.mono_pre fun s c fs ⟨hfs, Jc, pcR, hJ, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
  by_cases hJc : NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).cx Jc
  case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
  refine (heapAb_seg h (imms2Me Λ p) (Λw := (Ly).Λ) (fs := [fr]) (pcR := pcR)
    (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h16 hJc hR0 hal
    (by simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; show -D1 ≤ _; omega)
    (by show (0 : Int) ≤ 0; exact Int.le_refl _) (by show (-D1) % 8 = 0; omega)
    (by show (0 : Int) % 8 = 0; rfl) hF'
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO
    (fun s _ => framesPlaced_setup h hp hty hct s) ?_ ?_ ?_ ?_ ?_ hDtH _).mono_pre ?_
  · intro n τ us hus
    dsimp only [MSAt]; generalize ab2 p _ = ab
    cases ab <;>
      (show (arOf (Ly).Λ).units n τ ≤ _
       unfold arOf; exact Arena.ofWords_units_le hus)
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  · exact msOfAX_K_abi
  · rintro s c fs ⟨rfl, -, hA⟩
    exact ⟨hA, rfl⟩

set_option linter.unusedVariables false in
/-- **`SetupPreA.habA` from the bounds** (`hello1_habA`): the setup
function's frame `fS` (`fnCode2OfPMe_spec2`, the frame row `hrow`), the
room below it from `Bounds2A`'s `hfS`, `hnS`; open: the heap stub's
`write` tail (`hDtH`). -/
theorem hello1_habAB {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) {L D1 : Int} {fS nS : Nat} (hfS : fS ≤ nS)
    (hnS : (nS : Int) + 48 + 208 ≤ D1) (hL0 : 0 ≤ L) (hLm : L ≤ 16384) (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    (hrow : ∀ f fi, (f, fi) ∈ (Scc.Lower.A64.lowerAll cfg p).low.ir.funcs.zipIdx → f.checkStack = true →
      f.name = Scc.Lower.Names.user "rodata" →
        (Scc.Cert.Code1A64.ctxOf (Scc.Lower.A64.lowerAll cfg p).low.ir fi f).frame = fS)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) (hn : d.name = "rodata")
    (J : InvS) (v : BitVec 64)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s) :
    ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
      SegWS (W2S J) (KT) p (fun _ => none) (MSS J)
        (AbAl2 (MSS J) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False) := by
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  exact hello1_habA h hp hty hL0 hLm hL8 hD18 hL1 hd (by rw [hframe]; omega) J v hDtH

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_habA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_habA

/-- info: 'Spike.Lib.LowerA64.hello1_habAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_habAB

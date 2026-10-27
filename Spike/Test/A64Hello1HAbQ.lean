/-
**`hello1`'s landing contexts' aborts never end** (AArch64): `H1RestA.hAbQ`
at `hello1`'s contexts `CxOkH` (`Spike/Test/A64Hello1CxOkH.lean`), at any
landing's placement. Each context's aborts `AbU2` are stated at the start
world (the family `MSS J'` and no label placed) while the segment runs at
the landing's (`MSR J L' ls'`, `L'`): `Call.OK` does not transfer between
the two (its header condition reads the free range, which shrinks as labels
are placed), so the heap abort exits run by `heapAb_segX`
(`Spike/Lib/LowerA64/HeapAbSwA.lean`), the node at the start world, its
slot placement moved to `L'` by `SlotRepAt.mono_lbl`; the overflow aborts
are empty (`rodata` is addition-free, `abortN2_none_addFree`).

Left open: the write tail at the heap stub's `write` (`hDtH`; trivial at
`Dt := fun _ => True`).

- `hello1_habAX`: `AbAl2` of the setup frame at the start world, as a
  segment at any placement `L'`, `ls'` (`hello1_habA` at `heapAb_segX`);
- `cxOkH_hAbQA`: `H1RestA.hAbQ`'s segment at `CxOkH`'s aborts (`GA`), `rodata`
  addition-free;
- `hello1_hAbQA`: the same at `hello1o`.
-/
import Spike.Lib.LowerA64.HeapAbSwA
import Spike.Lib.LowerA64.AllocW2Full
import Spike.Test.A64Hello1HabA
import Spike.Test.A64Hello1SetupAb
import Spike.Test.A64Hello1H1Of

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


set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.A64.PhRec.μ (Ly)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in `H1RestA`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.A64.PhRec.own (Ly))
    (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (as in `H1RestA`). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option linter.unusedVariables false in
/-- **The setup frame's heap abort exits at the start world, at a landing's
placement** (`hello1_habA` at `heapAb_segX`): `AbAl2` at the family `MSS J'`
and no label placed, as a segment at the rows' memory side `MSR J L' ls'`
and placement `L'`; the setup frame placed at `L'` from no label
(`framesPlacedInI_mono_lbl`); open: the room `hD` and the heap stub's
`write` tail `hDtH`. -/
theorem hello1_habAX {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) {L D1 : Int} (hL0 : 0 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0) (hL1 : (setupMC (setupWords2 p)).Z.toInt + D1 ≤ L)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hD : ((fnCode2OfPMe hp h Λ j d hd).cx.frame : Int) + 208 ≤ D1)
    (J J' : InvS) (L' : Lbl) (ls' : Lsize) (v : BitVec 64)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s) :
    ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PRE F' g fr →
      SegWS (W2R J Dt L' ls') (KT) p L' (MSR J L' ls')
        (AbAl2 (MSS J') (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (RC) F' [fr]) (fun _ _ _ => False) := by
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
        (nbX ((MSS J') [fr]) (_root_.Executable.labels (Ly).exe).label (fun _ => none) (RC)
          (fnCode2OfPMe hp h Λ j d hd).cx.frame q.2 q.1 .abort) s c)
      (fun ⟨Jc, pcR⟩ => ?_) |>.mono_pre fun s c fs ⟨hfs, Jc, pcR, hJ, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
  by_cases hJc : NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).cx Jc
  case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
  refine (heapAb_segX h (imms2Me Λ p) (Λw := (Ly).Λ) (fs := [fr]) (pcR := pcR) (lbl := L')
    (fnCode2OfPMe hp h Λ j d hd).hf (fnCode2OfPMe hp h Λ j d hd).h16 hJc (by intro _ _ h'; cases h')
    hR0 hal
    (by simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; show -D1 ≤ _; omega)
    (by show (0 : Int) ≤ 0; exact Int.le_refl _) (by show (-D1) % 8 = 0; omega)
    (by show (0 : Int) % 8 = 0; rfl) hF'
    (Spike.Lib.A64.Rt.rS0_sub _) (Spike.Lib.A64.Rt.fitS_of_sub _ (Spike.Lib.A64.Rt.rS0_sub _)) hFO
    (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      framesPlacedInI_mono_lbl (by intro _ _ h'; cases h') hB)
    (ms := MSR J L' ls') (msN := (MSS J') [fr]) ?_ ?_ ?_ ?_ ?_ hDtH _).mono_pre ?_
  · intro n τ us hus
    dsimp only [MSAt]; generalize ab2 p _ = ab
    cases ab <;>
      (show (arOf (Ly).Λ).units n τ ≤ _
       unfold arOf; exact Arena.ofWords_units_le hus)
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  · exact msOfAX_K_abi
  · rintro s c fs ⟨rfl, -, hA⟩
    exact ⟨hA, rfl⟩

set_option linter.unusedVariables false in
/-- **`H1RestA.hAbQ`'s segment at `CxOkH`'s aborts** (at any placement
`L'`, `ls'`): each context `CxOkH` carries is the setup frame's at some
family `J'`, its aborts `AbU2` the overflow aborts of `rodata` (none: the
block addition-free, `hrod`, `abortN2_none_addFree`) and its heap abort
exits (`hello1_habAX`, the room from `CxOkH`'s bounds and frame row); open:
the heap stub's `write` tail `hDtH`. -/
theorem cxOkH_hAbQA {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty)
    (hrod : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s)
    (J : InvS) (L' : Lbl) (ls' : Lsize) :
    SegWS (W2R J Dt L' ls') (KT) p L' (MSR J L' ls') (GA (CxOkH h hp)) (fun _ _ _ => False) := by
  refine SegWS.exists_pre fun j => SegWS.exists_pre fun R => SegWS.exists_pre fun F => SegWS.exists_pre fun fs =>
    SegWS.exists_pre fun fp => SegWS.exists_pre fun ra => SegWS.exists_pre fun tp => SegWS.exists_pre fun G0 =>
    SegWS.exists_pre fun Ab => ?_
  by_cases hc : CxOkH h hp j R F fs fp ra tp G0 Ab
  case neg => exact SegWS.empty fun _ _ _ h' => hc h'.1
  obtain ⟨d, hd, L, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow, hPRE, -, -,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  refine SegWS.mono_pre (SegWS.or_pre ?_ ?_) fun s c fs h' => h'.2
  · exact SegWS.empty fun s c' _ ⟨_, _, _, hA⟩ => abortN2_none_addFree (hrod j d hd hn) hd s c' hA
  · obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
    have hframe : (fnCode2OfPMe hp h Λ j d hd).cx.frame = fS := by
      rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
    exact hello1_habAX h hp hty hL0 hLm hL8 hD18 hL1 hd (by rw [hframe]; omega) J J' L' ls' v hDtH F g fr hPRE

/-- **`hello1o`'s `H1RestA.hAbQ`** (`cxOkH_hAbQA` at
`hello1_rodata_addFree`); open: the heap stub's `write` tail `hDtH`. -/
theorem hello1_hAbQA {Dt : State → Prop} (hP : p = Spike.Test.Hello1MainSrc.hello1o)
    (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F''
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s)
    (J : InvS) (L' : Lbl) (ls' : Lsize) :
    SegWS (W2R J Dt L' ls') (KT) p L' (MSR J L' ls') (GA (CxOkH h hp)) (fun _ _ _ => False) := by
  subst hP
  exact cxOkH_hAbQA h hp hty hello1_rodata_addFree hDtH J L' ls'

end Assembled

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.hello1_habAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_habAX

/-- info: 'Spike.Lib.LowerA64.cxOkH_hAbQA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.cxOkH_hAbQA

/-- info: 'Spike.Lib.LowerA64.hello1_hAbQA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hello1_hAbQA

/-
**`hello1`'s landing contexts' aborts never end** (x86-64; the twin of
`Spike/Test/A64Hello1HAbQ.lean`): `H1OpenXW.hAb` and `H1OpenXW.hAbQ`
(`Spike/Lib/LowerX64/H1InLandW.lean`) at `hello1`'s contexts `CxOkH`
(`Spike/Test/X64Hello1CxOkH.lean`) and the aborts `GX (CxOkH h hp)`
(`Spike/Lib/LowerX64/H1GX.lean`), at any landing's placement. Each
context's aborts `AbU2` are stated at the start world (the family `MSS J'`
and no label placed) while the segment runs at the landing's (`MSR J L' ls'`,
`L'`), so the heap abort exits run by `heapAb_segX`
(`Spike/Lib/LowerX64/HeapAbXS.lean`), the node at the start world, its slot
placement moved to `L'` by `SlotRepAt.mono_lbl`; the overflow aborts are
empty (`rodata` is addition-free, `abortN2_none_addFreeX`).

Left open: the write tail at the heap stub's `write` (`hDtH`; trivial at
`Dt := fun _ => True`).

- `abortN2_none_addFreeX`: no state at an addition-free block's abort node,
  at any placed labels;
- `hello1_habAX`: `AbAl2` of the setup frame at the start world, as a
  segment at any placement `L'`, `ls'` (`hello1_habA` at `heapAb_segX`);
- `cxOkH_hAbQ`: `H1OpenXW.hAbQ`'s segment at `GX (CxOkH h hp)`, `rodata`
  addition-free;
- `hello1_hAbQ`: the same at `hello1o`.
-/
import Spike.Lib.LowerX64.HeapAbXS
import Spike.Lib.LowerX64.LevelMono2
import Spike.Lib.LowerX64.H1GX
import Spike.Test.X64Hello1HabA
import Spike.Test.X64Hello1CxOkH

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region FrameRun)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Flow.NewBuf (nbX allocAbortDepth)
open Spike.Lib.X64.Rt (swFSL rS0 setupMC arOf)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.LowerNode (setupWords2 compiled2 TailAt2 imms2Me addFreeT tailOf_addFree)
open Spike.Lib.AllocReach (Reach IN)

/-- **No state at an addition-free block's abort node**, at any placed
labels `lbl` (`abOf2_seg_addFree`'s argument): its source controls are at an
addition (`OvfReady`) on the walk (`TailAt2`), and the `j`th compiled
block's body `addFreeT` (`hno`) has none. -/
theorem abortN2_none_addFreeX {p : Prog} {j : Nat} {d : Decl} (hno : addFreeT d.body = true)
    (hd : (compiled2 p)[j]? = some d) {i : Expr → String → Nat → Option Nat}
    {lbl : WeakMem.AllocLabel → Option Nat} {fr : Scc.Emit.X64.Frame} {lab : Label → Int64} {fp ra : BitVec 64}
    {c0 : Ctl} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    (s : State) (c : Ctl) :
    ¬ Spike.Lib.X64.At exe endPc R F (abortN2 i (TailAt2 p j) p lbl fr lab fp ra c0) s c := by
  rintro ⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hT⟩, -⟩, -⟩
  obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
  exact tailOf_addFree (hT d hd) hno x a b e he

section Assembled

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  {sizes : List Nat} {labelOffs : List (String × Nat)}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.X64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The record's marks. -/
local notation "Mk" => Spike.Lib.X64.PhRec.μ (Ly)

set_option hygiene false in
/-- The program's start control (`S0X`'s). -/
local notation "C0" => (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).term,
  (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs))).env, none⟩ : Ctl)

set_option hygiene false in
/-- `MSAt` at `Closed2At`'s instance (the nodes' abort `ab2`). -/
local notation "MSS" J:max =>
  MSAt h (imms2Me Λ p) p Spike.Lib.LowerNode.IsNum J (ab2 p (Ly).lab) (fun _ => 0)

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in `H1InLandW`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (as in `H1InLandW`). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The switch region at depth `L`, below the top `v`. -/
local notation "RS" v:max => ((swR v (-L) 0).callee (-8 - 0) (8 - L) 8)

set_option hygiene false in
/-- The first TCB. -/
local notation "TP0" => tpOf (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- The switch region's frame condition with `WordsNone`, below the top `v` (`CxOkH`'s). -/
local notation "FS" v:max => (fun m => (Spike.Lib.DmemPriv.WordsNone (Ly).Λ m.dmem ∧
  swFSL L (rS0 (Ly)) (TOP) (limA (TP0)) v m) ∧ CallerCells (swR v (-L) 0) (-8 - 0) (8 - L) 8 m)

set_option hygiene false in
/-- The setup call's callee region. -/
local notation "RC" => (RS v).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8

set_option hygiene false in
set_option linter.unusedVariables false in
/-- The setup call's premises as `CxOkH` carries them. -/
local notation "PREH" F':max g:max fr:max => (RC).OK ∧ (RC).base.toNat % 8 = 0 ∧ FStable (RC) F' ∧
  (∀ m, F' m → (FS v) m ∧ CallerCells (RS v) (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8 m) ∧
  g.ra = ((Ly).lab (setupMC (setupWords2 p)).sp0).toBitVec ∧ g.tp = TP0 ∧
  Spike.Lib.X64.Flow.CallTo p C0 g.c0 fr ∧ (RC).base = g.sp

set_option linter.unusedVariables false in
/-- **The setup frame's heap abort exits at the start world, at a landing's
placement** (`hello1_habA` at `heapAb_segX`): `AbAl2` at the family `MSS J'`
and no label placed, as a segment at the rows' memory side `MSR J L' ls'`
and placement `L'`; off the first stack's top no state is in the frame
condition; the setup frame placed at `L'` from no label
(`FramesPlacedInI.mono_lbl`); open: the room `hD` and the heap stub's
`write` tail `hDtH`. -/
theorem hello1_habAX {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty) {L D1 : Int} (hL0 : 8 ≤ L) (hLm : L ≤ 16384)
    (hL8 : L % 8 = 0) (hD18 : D1 % 8 = 0)
    (hL1 : 8 + 8 + (setupMC (setupWords2 p)).Z.toInt + 8 + D1 ≤ L)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d)
    (hD : ((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) + 208 ≤ D1)
    (J J' : InvS) (L' : Lbl) (ls' : Lsize) (v : BitVec 64)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F''
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s) :
    ∀ (F' : MachineData → Prop) (g : WcG) (fr : TermRun.Frame), PREH F' g fr →
      SegWS (W2R J Dt L' ls') (KT) p L' (MSR J L' ls')
        (AbAl2 (MSS J') (fun _ => none) (fnCode2OfPMe hp h Λ j d hd) (rbR (RC)) F' [fr]) (fun _ _ _ => False) := by
  rintro F' _ fr ⟨hR0, -, hF', hFF, -, -, hct, -⟩
  -- off the first stack's top, no state is in the switch region's frame condition (`swF`)
  refine (Classical.em (v = TOP)).elim (fun hv => ?pos) (fun hv => ?neg)
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs ⟨-, Jc, pcR, -, ⟨-, -, -, -, σ, -, hF, -⟩⟩
    exact hv (hFF _ hF).1.1.2.1.1
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
        (by show _ < (0 : Int); omega) (by decide) (hFF m hm).1.1.2.2 (hFF m hm).1.2)
      (hFF m hm).2
  obtain ⟨hF2, hR2, -, -⟩ := rbR_facts hF' hR0 hlo0 hhi0
  have hb2 := rbR_base hR0 (by omega) (by omega)
  refine SegWS.exists_pre (P := fun (q : (Spike.Lib.X64.AS → Ctl → Prop) × Int64) s c fs => fs = [fr] ∧
      NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).fr q.1 ∧
      Spike.Lib.X64.At (Ly).exe (Ly).endPc (rbR ((RS (TOP)).callee
          (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)) F'
        (nbX ((MSS J') [fr]) (_root_.Executable.labels (Ly).exe).label (fun _ => none)
          (rbR ((RS (TOP)).callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8))
          (fnCode2OfPMe hp h Λ j d hd).fr.size q.2 q.1 .abort) s c)
      (fun ⟨Jc, pcR⟩ => ?_) |>.mono_pre fun s c fs ⟨hfs, Jc, pcR, hJ, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
  by_cases hJc : NbJcOf (imms2Me Λ p) (fun _ => none) (fnCode2OfPMe hp h Λ j d hd).fr Jc
  case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
  refine (heapAb_segX h (imms2Me Λ p) (Λw := (Ly).Λ) (fs := [fr]) (pcR := pcR) (lbl := L')
    (fnCode2OfPMe hp h Λ j d hd).hf hJc (by intro _ _ h'; cases h') hR2
    (by omega) (by simp only [allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame, rbR, Region.callee]; omega)
    (by simp only [rbR, Region.callee]; omega) (by simp only [rbR, Region.callee]; omega)
    (by simp only [rbR, Region.callee]; omega) hF2
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _))
    (fun m hm => stackOff_rbR hR0 (by omega) (by omega) (hFO0 m hm))
    (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      FramesPlacedInI.mono_lbl (by intro _ _ h'; cases h') hB)
    (ms := MSR J L' ls') (msN := (MSS J') [fr]) ?_ ?_ ?_ ?_ ?_ hDtH _).mono_pre ?_
  · intro n τ us hus
    dsimp only [MSAt]; generalize ab2 p _ = ab
    cases ab <;>
      (show (arOf (Ly).Λ).units n τ ≤ _
       unfold arOf; exact arena_ofWords_units_le hus)
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · dsimp only [MSAt]; generalize ab2 p _ = ab; cases ab <;> rfl
  · generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  · exact msOfAX_K_abi
  · rintro s c fs ⟨rfl, -, hA⟩
    exact ⟨hA, rfl⟩

set_option linter.unusedVariables false in
/-- **`H1OpenXW.hAbQ`'s segment at `GX (CxOkH h hp)`** (at any placement
`L'`, `ls'`): each context `CxOkH` carries is the setup frame's at some
family `J'`, its aborts `AbU2` the overflow aborts of `rodata` (none: the
block addition-free, `hrod`, `abortN2_none_addFreeX`) and its heap abort
exits (`hello1_habAX`, the room from `CxOkH`'s bounds and frame row); open:
the heap stub's `write` tail `hDtH`. -/
theorem cxOkH_hAbQ {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) {ty : Ty}
    (hty : Scc.Lower.setupOf p = some ty)
    (hrod : ∀ (j : Nat) (d : Decl), (compiled2 p)[j]? = some d → d.name = "rodata" → addFreeT d.body = true)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F''
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s)
    (J : InvS) (L' : Lbl) (ls' : Lsize) :
    SegWS (W2R J Dt L' ls') (KT) p L' (MSR J L' ls') (GX (CxOkH h hp)) (fun _ _ _ => False) := by
  refine SegWS.exists_pre fun j => SegWS.exists_pre fun R => SegWS.exists_pre fun F => SegWS.exists_pre fun fs =>
    SegWS.exists_pre fun fp => SegWS.exists_pre fun ra => SegWS.exists_pre fun tp => SegWS.exists_pre fun G0 =>
    SegWS.exists_pre fun Ab => ?_
  by_cases hc : CxOkH h hp j R F fs fp ra tp G0 Ab
  case neg => exact SegWS.empty fun _ _ _ h' => hc h'.1
  obtain ⟨d, hd, L, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow, hPRE, -, -,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  refine SegWS.mono_pre (SegWS.or_pre ?_ ?_) fun s c fs h' => h'.2
  · exact SegWS.empty fun s c' _ ⟨_, _, _, hA⟩ => abortN2_none_addFreeX (hrod j d hd hn) hd s c' hA
  · obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
    have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
      rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
    exact hello1_habAX h hp hty hL0 hLm hL8 hD18 hL1 hd (by rw [hframe]; omega) J J' L' ls' v hDtH F g fr hPRE

/-- **`hello1o`'s `H1OpenXW.hAbQ`** (`cxOkH_hAbQ` at
`hello1_rodata_addFree`); open: the heap stub's `write` tail `hDtH`. -/
theorem hello1_hAbQ {Dt : State → Prop} (hP : p = Spike.Test.Hello1MainSrc.hello1o)
    (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hDtH : ∀ (R' : Region) (F'' : MachineData → Prop) c s c', Spike.Lib.X64.At (Ly).exe (Ly).endPc R' F''
      (Spike.Lib.X64.Abort.N (Ly).lab Spike.Lib.X64.Abort.heap c .sys) s c' → Dt s)
    (J : InvS) (L' : Lbl) (ls' : Lsize) :
    SegWS (W2R J Dt L' ls') (KT) p L' (MSR J L' ls') (GX (CxOkH h hp)) (fun _ _ _ => False) := by
  subst hP
  exact cxOkH_hAbQ h hp hty hello1_rodata_addFree hDtH J L' ls'

end Assembled

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_habAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_habAX

/-- info: 'Spike.Lib.LowerX64.cxOkH_hAbQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.cxOkH_hAbQ

/-- info: 'Spike.Lib.LowerX64.hello1_hAbQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hAbQ

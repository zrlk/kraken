/-
**`H1RestXW.hAW` at `hello1`'s landing contexts** (x86-64; the twin of
`Spike/Test/A64Hello1HAW.lean`): at every context `CxOkH` (the setup frame
of the block `rodata`, `Spike/Test/X64Hello1CxOkH.lean`), the rebased
region's bound below the allocator's frame and the returned base's store
`AllocStoreAt` inside `W2` at every reachable placement, from
`allocStore_w2` at each allocation of the body (`H1RestXW`,
`Spike/Lib/LowerX64/H1RestXW.lean`).

The region's facts are `PRE`'s and the bounds' (as `setupCxLB_ofPre`, in
the rebased region `rbR`), the frame `[fr]` placed at no label
(`framesPlaced_setup`) and so at every placement (`framesPlacedInI_mono_lbl`),
the walk's facts at the continuation from the allocation's resumption facts
(`PtC2.newBufW`), the ghosts `FrOk2` along the setup frame's run.

- `hAW_CxOkHX`: `H1RestXW.hAW` at `CxOkH`, given the setup type and the
  bodies' one-word elements (`H1OpenXW.hTn`'s shape);
- `hAW_H1RestXW`: the field's shape (`H1RestXW.hAW`) at any start premise
  and return address;
- `hello1_hAW`: any `H1RestXW` at `hello1o` with its `hAW` replaced by
  `hAW_H1RestXW` at `hello1_hty`, `hello1_hTn` (the field closed, a check).
-/
import Spike.Test.X64Hello1CxOkH
import Spike.Test.X64Hello1H1Of
import Spike.Test.X64Hello1ClosedAt2B
import Spike.Lib.LowerX64.H1RestXW
import Spike.Lib.LowerX64.AllocW2Full
import Spike.Lib.LowerX64.AllocW2AtOf
import Spike.Lib.LowerX64.HeldRes

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (swR FStable)
open Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Ret0 (WcG CallerCells limA)
open Spike.Lib.X64.Rt (setupMC rS0 swFSL rtF)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 TailAt2 imms2Me)
open Spike.Lib.AllocReach (Reach IN)

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
/-- **The start's frame condition**: the runtime's words unloaded and no
heap or image word loaded (`H1RestXW`'s). -/
local notation "WNF" => fun m => Spike.Lib.DmemPriv.WordsNone (Ly).Λ (MachineData.dmem m) ∧ rtF (Ly) m

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J` (as in `H1RestXW`). -/
local notation "W2R" J:max Dt:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (Spike.Lib.X64.PhRec.own (Ly))
    (rS0 (Ly)) (Spike.Lib.X64.PhRec.Tk (Ly)) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J) Dt
    (Spike.Lib.X64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2` (as in `H1RestXW`). -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Mk) p Spike.Lib.LowerNode.IsNum (G2 h p) (fun s _ => Spike.Lib.X64.PhRec.own (Ly) s) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The runtime's layout of the output at the compiler's immediates. -/
local notation "LY0" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Scc.Lower.imms2Of p)

set_option hygiene false in
/-- The output's program. -/
local notation "OP" => Scc.Cert.PlaceOK.Out.prog (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

/-- **`H1RestXW.hAW` at the setup frame's contexts `CxOkH`**: at every
family `J`, reachable placement `L`, `ls` and context `CxOkH` of the `j`th
block, the rebased region `rbR RC` below the allocator's frame (`-D1 + 8`
past the frame row `fS + 8 ≤ nS` and `nS + 48 + 208 ≤ D1`) and at every
allocation of the body the returned base's store inside `W2`
(`allocStore_w2`: the region's facts from `PRE` and the bounds, `hFO` by
`stackOff_callee` twice and `stackOff_rbR`, the frame `[fr]` placed at no
label and so at every placement, the continuation's walk facts by
`PtC2.newBufW`, `elem2` by `hTn`, `FrOk2` along the setup frame's run). -/
theorem hAW_CxOkHX (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {Dt : State → Prop} (J : InvS) :
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : (compiled2 p)[j]? = some d) R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab →
      (rbR R).lo ≤ -Spike.Lib.X64.Flow.NewBuf.allocAbortDepth ((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
        (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT (LY0).exe (LY0).endPc (rbR R) F ((MSR J L ls) fs) fp ra tp
        G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) := by
  intro L ls _ j d hd R F fs fp ra tp G0 Ab hc
  obtain ⟨d', hd', L', D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hR8, hF', hFF, -, -, hct, -⟩, -, -, rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  obtain ⟨w, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (fnCode2OfPMe hp h Λ j d hd).fr.size = fS := by
    rw [hcx]; exact hrow _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hpN := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hlo1 : ((swR v (-L') 0).callee (-8 - 0) (8 - L') 8
      |>.callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).lo ≤ -8 := by
    show -D1 ≤ -8; omega
  have hhi1 : (0 : Int) ≤ ((swR v (-L') 0).callee (-8 - 0) (8 - L') 8
      |>.callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8).hi := by
    show (0 : Int) ≤ 8; decide
  have hb := rbR_base hR0 hlo1 hhi1
  have hlo : (rbR ((swR v (-L') 0).callee (-8 - 0) (8 - L') 8
      |>.callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)).lo ≤
      -Spike.Lib.X64.Flow.NewBuf.allocAbortDepth ((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) := by
    simp only [Spike.Lib.X64.Flow.NewBuf.allocAbortDepth, Spike.Lib.X64.Flow.NewBuf.allocFrame]
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hlo0 : (rbR ((swR v (-L') 0).callee (-8 - 0) (8 - L') 8
      |>.callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)).lo ≤
      -((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) := by
    show -D1 + 8 ≤ _; rw [hframe]; omega
  have hhi : (0 : Int) ≤ (rbR ((swR v (-L') 0).callee (-8 - 0) (8 - L') 8
      |>.callee (-8 - (setupMC (setupWords2 p)).Z.toInt - 8 - 0) (-D1) 8)).hi := by
    show (0 : Int) ≤ 8 + 8; decide
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2 h hp hs') (rtCodeOkS_setupWords2 h hp hs')).1
  have hZ := setupMC_Z _ hsw
  refine ⟨hlo, ?_⟩
  intro c0 pc kk x cn τ e env n lits cs bufs tk kv en em hh hc0 hT hfr _ _ _ hpt
  obtain ⟨-, -, -, -, -, hIt, hIc, hlbe⟩ := PtC2.newBufW hpt
  intro lw off zs zc z k _ hoff _ _ _ hCd' lbl' lsize' hl' _
  have hI := Spike.Lib.X64.PhRec.instOk_ofPlaceOK h (Scc.Lower.imms2Of p) (rS := rS0 (Ly))
  exact allocStore_w2 hI (printIn_of_placeOKAt h) (abortIn_of_placeOKAt h) (fnCode2OfPMe hp h Λ j d hd).hf
    (fnCode2OfPMe hp h Λ j d hd).h1 (rbR_ok hR0 hlo1 hhi1) (by omega) hlo
    (by show (16 : Int) ≤ 8 + 8; decide) (by show (-D1 + 8) % 8 = 0; omega)
    (by show ((8 : Int) + 8) % 8 = 0; decide)
    (Spike.Lib.X64.Rt.rS0_sub _) (Spike.Lib.X64.Rt.fitS_of_sub _ (Spike.Lib.X64.Rt.rS0_sub _))
    (by
      intro m hm
      refine stackOff_rbR hR0 hlo1 hhi1 ?_
      have H := hFF m hm
      have hv := H.1.1.2.1.1
      subst hv
      have hok : (swR (TOP) (-L') 0).OK := by
        rw [Spike.Lib.X64.Rt.stacksA_lab0]; exact Spike.Lib.X64.Rt.rt_hokD _ (by omega) hLm
      have htop8 : (TOP).toNat % 8 = 0 := by
        rw [Spike.Lib.X64.Rt.stacksA_lab0]; have := Spike.Lib.X64.Rt.rt_h16 (Ly); omega
      have hR1 : ((swR (TOP) (-L') 0).callee (-8 - 0) (8 - L') 8).OK :=
        Region.callee_ok hok (by show -L' ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
          (by show _ ≤ (0 : Int); omega)
      have hb1 : (((swR (TOP) (-L') 0).callee (-8 - 0) (8 - L') 8).base.toNat : Int) = (TOP).toNat - 8 :=
        Region.callee_base hok (by show -L' ≤ _; omega) (by omega) (by show _ < (0 : Int); omega)
      have hb8 : ((swR (TOP) (-L') 0).callee (-8 - 0) (8 - L') 8).base.toNat % 8 = 0 := by omega
      exact Spike.Lib.X64.Rt.stackOff_callee hR1 hb8 (by show (8 - L') % 8 = 0; omega)
        (by show (8 : Int) % 8 = 0; decide) (by show 8 - L' ≤ _; omega) (by omega)
        (by show _ < (8 : Int); omega) (by omega)
        (Spike.Lib.X64.Rt.stackOff_callee hok htop8 (by show (-L') % 8 = 0; omega)
          (by show (0 : Int) % 8 = 0; rfl) (by show -L' ≤ _; omega) (by omega)
          (by show _ < (0 : Int); omega) (by decide) H.1.1.2.2 H.1.2)
        H.2)
    (rbR_fstable hR0 hlo1 hhi1 hF') hpN
    (fun _ _ hr => regionOff_of_rsOf (fnCode2OfPMe hp h Λ j d hd).hf hlo0 hhi hr)
    (fun s _ => (framesPlaced_setup h hp hty hct s).imp fun _ hB =>
      framesPlacedInI_mono_lbl (fun _ _ hl => by cases hl) hB)
    (hTn j d hd x cn τ e hT) hfr hl' (fun h => nomatch h)
    (FrOk2.runM hpN hc0 (FrOk2.step hpN (hct.step []) (hf0_start2 hty _))) hoff hCd' hIt hIc hlbe

/-- **`H1RestXW.hAW` at `CxOkH`** in the field's shape (`hAW_CxOkHX`, the
family's start premise and the return address's phase unused): at the code
`fnCode2OfPMe`, any entry `E`, bottoms `Bot` and write tail `Dt`. -/
theorem hAW_H1RestXW (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (hTn : ∀ j d, (compiled2 p)[j]? = some d →
      ∀ x cn τ e, TailAt2 p j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    {E : Entry} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop} :
    ∀ J : InvS, (∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
      ∀ s c fs, StartsSX h E (WNF) (ElX h (fnCode2OfPMe hp h Λ) (CxOkH h hp) Bot) Dt (ab2 p (Ly).lab)
        L ls s c fs → J L ls s c fs) →
    ∀ L ls, Reach (Ar) (fun _ => none) (fun _ => 0) L ls →
    ∀ j d (hd : (compiled2 p)[j]? = some d) R F fs fp ra tp G0 Ab, CxOkH h hp j R F fs fp ra tp G0 Ab →
      Spike.Lib.X64.PhRec.ph LY0 (Int64.ofBitVec ra).toBitVec.toNat =
        Spike.Lib.X64.PhRec.ph LY0 ((LY0).lab raL).toBitVec.toNat →
      (rbR R).lo ≤ -Spike.Lib.X64.Flow.NewBuf.allocAbortDepth ((fnCode2OfPMe hp h Λ j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (fnCode2OfPMe hp h Λ j d hd).lcx (fnCode2OfPMe hp h Λ j d hd).fr
        (CdCLE OP (Spike.Lib.X64.PhRec.okPc LY0) (Spike.Lib.X64.PhRec.ph LY0) (LY0).lab (Int64.ofBitVec ra))
        ((fnCode2OfPMe hp h Λ j d hd).Bl ra)
        (fun L ls s c => (W2R J Dt L ls) s c fs) KT (LY0).exe (LY0).endPc (rbR R) F ((MSR J L ls) fs) fp ra tp
        G0 (imms2Me Λ p) (TailAt2 p j) (RetLk d.retTy) :=
  fun J _ L ls hR j d hd R F fs fp ra tp G0 Ab hc _ =>
    hAW_CxOkHX h hp hty hTn J L ls hR j d hd R F fs fp ra tp G0 Ab hc

end Assembled

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`hello1`'s `H1RestXW.hAW`** at every placement check of `hello1o`'s
output at `ld`'s layout, every entry `E`, bottoms `Bot` and write tail `Dt`:
any `H1RestXW` with its `hAW` replaced by `hAW_H1RestXW` at `hello1_hty`,
`hello1_hTn`. -/
theorem hello1_hAW (h : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true)
    {E : Entry} {Bot : StkKey → List TermRun.Frame → Prop} {Dt : State → Prop} :
    (H : H1RestXW h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
      (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) Bot Dt) →
    H1RestXW h E (fnCode2OfPMe Spike.Lib.LowerNode.hello1o_accepted2 h Le)
      (CxOkH h Spike.Lib.LowerNode.hello1o_accepted2) Bot Dt :=
  fun H => { H with
    hAW := hAW_H1RestXW h Spike.Lib.LowerNode.hello1o_accepted2 hello1_hty.choose_spec hello1_hTn }

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hAW_CxOkHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hAW_CxOkHX

/-- info: 'Spike.Lib.LowerX64.hAW_H1RestXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hAW_H1RestXW

/-- info: 'Spike.Lib.LowerX64.hello1_hAW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_hAW

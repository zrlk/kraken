/-
**The landing contexts' aborts at a reachable placement end nowhere**
(AArch64): `AbLUStmt` (`Spike/Lib/LowerA64/G1H1Stmt.lean`) for any
`Accepted2` program with a setup block. Each landing context `CxOkH`
(`Spike/Test/A64Hello1CxOkH.lean`) is the setup frame's: region `RC` below
the switch region's top, frames `[fr]`, ghosts along the setup frame's run.
Its aborts `AbU2` at the placement `L`, `ls` (the rows' memory side and the
labels there) are the two abort kinds of `abCxL_seg`
(`Spike/Lib/LowerA64/G1AbG2L.lean`), each a single-placement segment:

- the overflow label by `ovfAb_segF` at `L` (no addition-freedom needed:
  the block's overflow code from `ovfFacts_me` when the walk reaches a `+`);
- the heap abort exits by `heapAb_seg` at `L`.

The region's facts come from `CxOkH`'s setup call premises and bounds (as
`cxCore2_setup`'s), the setup frame placed at `L` from no label
(`framesPlaced_setup`, `framesPlacedInI_mono_lbl`), its environment the
start's (`envSmall_C0`), the room `fS + 48 ≤ nS + 48 + 208 ≤ D1`; the
write tail is `fun _ => True`.

- `abLU_seg`: one landing context's aborts at `L`, `ls`;
- `abLUStmt`: `AbLUStmt`.
-/
import Spike.Lib.LowerA64.G1H1Stmt
import Spike.Lib.LowerA64.G1AbG2
import Spike.Lib.LowerA64.G1SetupCx
import Spike.Lib.LowerA64.FramesPlacedSetup
import Spike.Lib.LowerA64.AllocW2Full

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Rt (setupMC rS0 arOf swFSL)
open Spike.Lib.LowerNode (FrOk2 setupWords2 compiled2 imms2Me TailAt2)
open Spike.Lib.AllocReach (Reach IN)
open Spike.Lib.A64.Flow.NewBuf (nbX allocAbortDepth)

section AbL

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The allocator's arena of the output. -/
local notation "Ar" => Spike.Lib.A64.Rt.arOf (lay2 Λ p)

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
/-- **`W2` at the record** at a placement `L`, `ls`, over `IN … J`, at the write tail `fun _ => True`. -/
local notation "W2T" J:max L:max ls:max =>
  fun s c fs => W2 (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (Spike.Lib.A64.PhRec.own (Ly)) (rS0 (Ly)) (Spike.Lib.A64.PhRec.Tk (Ly)) (Ar)
    (IN (Ar) (fun _ => none) (fun _ => 0) J) (fun _ => True) (Spike.Lib.A64.WriteAb.Ab (Ly).lab) L ls s c fs

set_option hygiene false in
/-- **The rows' memory side at the record** at the nodes' abort `ab2`. -/
local notation "MSR" J:max L:max ls:max =>
  msOfAX (lay2 Λ p) (Spike.Lib.A64.PhRec.μ (Ly)) p Spike.Lib.LowerNode.IsNum (G2 h p)
    (fun s _ => Spike.Lib.A64.PhRec.own (Ly) s) (Ar) (IN (Ar) (fun _ => none) (fun _ => 0) J)
    (ab2 p (Ly).lab) L ls

set_option hygiene false in
/-- The take's step relation at the record. -/
local notation "KT" => TakeK ((Ly).lab StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th block's code facts. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **One landing context's aborts at a placement end nowhere**: at a
landing context `CxOkH` of the `j`th compiled block, its aborts `AbU2` at
the placement `L`, `ls`: the overflow label by `ovfAb_segF`, the heap abort
exits by `heapAb_seg`, both at `L` in the setup frame's region `R`. -/
theorem abLU_seg (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty)
    (J : InvS) (L : Lbl) (ls : Lsize) {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region}
    {F : MachineData → Prop} {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {Ab : FragS isaLSE2} (hc : CxOkH h hp j R F fs fp ra tp G0 Ab) :
    SegWS (W2T J L ls) (KT) p L (MSR J L ls) (AbU2 p (MSR J L ls) L (FC j d hd) R F fs fp ra G0)
      fun _ _ _ => False := by
  obtain ⟨d', hd', LD, D1, fS, nS, v, g, fr, J', hn, hfS, hnS, hL0, hLm, hL8, hD18, hL1, hrow,
    ⟨hR0, hal, hF', hFF, -, -, hct, -⟩, -, -, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hc
  obtain rfl : d = d' := Option.some.inj (hd.symm.trans hd')
  have hs' : (Scc.Lower.setupOf p).isSome = true := by rw [hty]; rfl
  have hsw := (setupIn_sw_eq h (tail_setup_of_accepted2A h hp hs') (rtCodeOkS_setupWords2A h hp hs')).1
  have hZ := setupMC_Z _ hsw
  have hpz := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub _ hsub
  obtain ⟨w, fi, -, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hframe : (FC j d hd).cx.frame = fS := by
    rw [hcx]; exact hrow _ _ hmem rfl (by show Scc.Lower.Names.user d.name = _; rw [hn])
  have hFO : ∀ m, F m → StackOff (rS0 (Ly))
      ((swR v (-LD) 0).callee (-(setupMC (setupWords2 p)).Z.toInt) (-D1) 0) m := by
    intro m hm
    obtain ⟨⟨⟨hv, -⟩, hoff⟩, hcc⟩ := hFF m hm
    subst hv
    have hok : (swR (TOP) (-LD) 0).OK := by
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.rt_hokD _ hL0 hLm
    have h8 : (swR (TOP) (-LD) 0).base.toNat % 8 = 0 := by
      show (TOP).toNat % 8 = 0
      rw [Spike.Lib.A64.Rt.stacksA_lab0]; have := Spike.Lib.A64.Rt.rt_h16 (Ly); omega
    exact Spike.Lib.A64.Flow.Ret0.Inst.stackOff_callee hok h8 (by show (-LD) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl)
      (by show -LD ≤ _; omega) (by omega) (by show _ < (0 : Int); omega) (by omega) hoff hcc
  have hfp : ∀ s : State, F s.st.1 → ∃ B, FramesPlacedInI (lay2 Λ p) L s [fr] B := fun s _ =>
    (framesPlaced_setup h hp hty hct s).imp fun _ hB => framesPlacedInI_mono_lbl (by intro _ _ h'; cases h') hB
  have hfr : fr.env = (⟨(th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).term,
      (th02 p (meW2 (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)))).env, none⟩ : Ctl).env := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, rfl⟩ := hct
    rfl
  have hes : ∀ f ∈ [fr], Spike.Lib.EnvSmall f.env := by
    intro f hf
    rw [List.mem_singleton] at hf
    subst hf
    rw [hfr]
    exact envSmall_C0 hp hty
  have hma : ∀ s : State, (∃ k a, (Spike.Lib.A64.PhRec.μ (Ly)).abortAt k = some a ∧ pcOf s = a) →
      ((MSR J L ls) [fr]).abortAt s := by
    generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  refine SegWS.or_pre ?_ ?_
  · -- the overflow label
    refine (SegWS.exists_pre (P := fun c0 s c fs' => (fun c => Spike.Lib.FrameRunM p (g.c0, [fr]) (c, [fr])) c0 ∧
        (Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc _ F
          (abortN2 (imms2Me Λ p) (TailAt2 p j) p L (FC j d hd).cx
            (_root_.Executable.labels (Ly).exe).label g.fp g.ra c0)).at [fr] s c fs') fun c0 => ?_).mono_pre
      fun s c fs' ⟨hfs, c0, hg, hA⟩ => ⟨c0, hg, hA, hfs⟩
    by_cases hg : Spike.Lib.FrameRunM p (g.c0, [fr]) (c0, [fr])
    case neg => exact SegWS.empty fun _ _ _ h' => hg h'.1
    refine (ovfAb_segF h (imms2Me Λ p) (FC j d hd).hf (FC j d hd).h16
      (fnCode2OfPMe_spec hp h Λ j d hd).2.2.1 (ovfFacts_me hp h Λ hd (imms2Me Λ p)) hR0 hal
      (by show -D1 ≤ _; rw [hframe]; omega) (by show (0 : Int) ≤ 0; exact Int.le_refl _)
      (by show (-D1) % 8 = 0; omega) (by show (0 : Int) % 8 = 0; rfl) hF' hsub hfit hFO hpz hfp
      (abortN2_slotRepAt fun _ _ _ _ => rfl)
      (FrOk2.runM hpz hg (FrOk2.step hpz (hct.step []) (hf0_start2A hty _))) hes hma msOfAX_K_abi
      (fun _ _ _ _ _ _ => trivial) _).mono_pre
      fun _ _ _ h' => h'.2
  · -- the heap abort exits
    refine (SegWS.exists_pre (P := fun (q : (AS → Ctl → Prop) × Int64) s c fs' => fs' = [fr] ∧
        NbJcOf (imms2Me Λ p) L (FC j d hd).cx q.1 ∧
        Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc _ F (nbX ((MSR J L ls) [fr]) (_root_.Executable.labels (Ly).exe).label
          L _ (FC j d hd).cx.frame q.2 q.1 .abort) s c) fun ⟨Jc, pcR⟩ => ?_).mono_pre
      fun s c fs' ⟨hfs, Jc, pcR, hJ, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
    by_cases hJc : NbJcOf (imms2Me Λ p) L (FC j d hd).cx Jc
    case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
    refine (heapAb_seg h (imms2Me Λ p) (Λw := lay2 Λ p) (fs := [fr]) (pcR := pcR)
      (FC j d hd).hf (FC j d hd).h16 hJc hR0 hal
      (by simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; show -D1 ≤ _; rw [hframe]; omega)
      (by show (0 : Int) ≤ 0; exact Int.le_refl _) (by show (-D1) % 8 = 0; omega)
      (by show (0 : Int) % 8 = 0; rfl) hF' hsub hfit hFO hfp ?_ ?_ ?_ hma msOfAX_K_abi
      (fun _ _ _ _ _ _ => trivial) _).mono_pre ?_
    · intro n τ us hus
      generalize ab2 p _ = ab
      cases ab <;>
        (show (arOf (Ly).Λ).units n τ ≤ _
         unfold arOf; exact Arena.ofWords_units_le hus)
    · generalize ab2 p _ = ab; cases ab <;> rfl
    · generalize ab2 p _ = ab; cases ab <;> rfl
    · rintro s c fs' ⟨rfl, -, hA⟩
      exact ⟨hA, rfl⟩

/-- **`AbLUStmt`** for any `Accepted2` program with a setup block: at each
landing context (`abLU_seg`), no state at a tuple failing `CxOkH`. -/
theorem abLUStmt (hp : Scc.Lower.Accepted2 p = true) {ty : Ty} (hty : Scc.Lower.setupOf p = some ty) :
    AbLUStmt h hp := by
  intro J L ls _
  unfold AbLU
  refine SegWS.exists_pre fun j => SegWS.exists_pre fun d => SegWS.exists_pre fun hd =>
    SegWS.exists_pre fun R => SegWS.exists_pre fun F => SegWS.exists_pre fun fs =>
    SegWS.exists_pre fun fp => SegWS.exists_pre fun ra => SegWS.exists_pre fun tp =>
    SegWS.exists_pre fun G0 => SegWS.exists_pre fun Ab => ?_
  by_cases hc : CxOkH h hp j R F fs fp ra tp G0 Ab
  case neg => exact SegWS.empty fun _ _ _ h' => hc h'.1
  exact (abLU_seg h hp hty J L ls hd hc).mono_pre fun _ _ _ h' => h'.2

end AbL

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.abLU_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.abLU_seg

/-- info: 'Spike.Lib.LowerA64.abLUStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.abLUStmt

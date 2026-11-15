/-
**Every context's aborts never end at a reachable placement** (AArch64):
`AbG2L` (`Spike/Lib/LowerA64/G1FnSpecL.lean`, the aborts of every context
with `CxCore2L` at the placement `L`, `ls`) as a segment to the empty
fragment inside `W2AtL … L ls`, as `abG2_seg`
(`Spike/Lib/LowerA64/G1AbG2.lean`) at the start's placement: the three
abort kinds' segments (`ovfAb_segF`, `heapAb_seg`, `printAb_segP`) take the
placement as a parameter, the frames placed at `L` (`CxCore2L.hfp`).

- `abCxL_seg`: one context's aborts never end;
- `abG2L_seg`: every context's.
-/
import Spike.Lib.LowerA64.G1FnSpecL
import Spike.Lib.LowerA64.G1AbG2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks Range)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib (Region FrameRunM)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff limA pinA)
open Spike.Lib.A64.Flow.NewBuf (nbX allocAbortDepth)
open Spike.Lib.A64.Rt (rS0 arOf)
open Spike.Lib.LowerNode (FrOk2 ZBad compiled2 TailAt2 imms2Me IsNum printFrame)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.AllocReach (IN Reach)

section G2L

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- `W2AtL` at `Closed2AtA`'s instance, at the placement `L`, `ls`. -/
local notation "W2L" J:max L:max ls:max => W2AtL h (imms2Me Λ p) p IsNum (rS0 (Ly)) J Dt (fun _ => 0) L ls

set_option hygiene false in
/-- `MSAtL` at `Closed2AtA`'s instance (the nodes' abort `ab2`), at the
placement `L`, `ls`. -/
local notation "MSL" J:max L:max ls:max => MSAtL h (imms2Me Λ p) p IsNum J (ab2 p (Ly).lab) (fun _ => 0) L ls

set_option hygiene false in
/-- The take's outside moves. -/
local notation "KT" => Spike.Lib.A64.Flow.Ret0.TakeK ((Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) (rS0 (Ly))

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **One context's aborts never end at a reachable placement**
(`AbG2L`'s body at a context with `CxCore2L`): `abCx_seg` at the placement
`L`, `ls`, the frames placed at `L`. -/
theorem abCxL_seg {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) (hRo : Room2OwnStmt h hp) (J : InvS)
    (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s)
    {j : Nat} {d : Decl} (hd : (compiled2 p)[j]? = some d) {R : Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    (hC : CxCore2L h hp Dt J L ls j R F fs fp ra tp G0) :
    SegWS (W2L J L ls) (KT) p L (MSL J L ls)
      (fun s c fs' =>
        (fs' = fs ∧ ∃ c0, G0 c0 ∧ At (Ly).exe (Ly).endPc R F
            (abortN2 (imms2Me Λ p) (TailAt2 p j) p L (FC j d hd).cx
              (_root_.Executable.labels (Ly).exe).label fp ra c0) s c) ∨
         (fs' = fs ∧ ∃ (Jc : AS → Ctl → Prop) (pcR : Int64),
            NbJcOf (imms2Me Λ p) L (FC j d hd).cx Jc ∧
            (∀ σ c', Jc σ c' → TailAt2 p j c'.term) ∧
            At (Ly).exe (Ly).endPc R F (nbX ((MSL J L ls) fs) (_root_.Executable.labels (Ly).exe).label
              L R (FC j d hd).cx.frame pcR Jc .abort) s c) ∨
         (∃ c0 x is a e c1, G0 c0 ∧ TailAt2 p j (.let_ x (.call "print" is a []) e) ∧
            fs' = printFrame x e c1 :: fs ∧
            At (Ly).exe (Ly).endPc R F (printNAS (_root_.Executable.labels (Ly).exe).label (FC j d hd).cx
              L (imms2Me Λ p) x e c1) s c))
      (fun _ _ _ => False) := by
  by_cases hm : ∃ m, F m
  case neg =>
    refine SegWS.empty ?_
    rintro s c fs' (⟨_, _, _, hA⟩ | ⟨_, _, _, _, _, hA⟩ | ⟨_, _, _, _, _, _, _, _, _, hA⟩)
    all_goals exact hm ⟨_, at_F hA⟩
  obtain ⟨m, hm⟩ := hm
  have hes := hC.hes m hm
  have hlo := hRo j d hd 256 R.lo (hC.room d hd)
  have hpz := Spike.Lib.LowerNode.progNoS_zbad_of_accepted2 hp
  have hsub := Spike.Lib.A64.Rt.rS0_sub (Ly)
  have hfit := Spike.Lib.A64.Rt.fitS_of_sub _ hsub
  have hma : ∀ fs1, ∀ s : State, (∃ k a, (Spike.Lib.A64.PhRec.μ (Ly)).abortAt k = some a ∧ pcOf s = a) →
      ((MSL J L ls) fs1).abortAt s := by
    intro fs1
    dsimp only [MSAtL]; generalize ab2 p _ = ab; cases ab <;> exact fun _ h' => h'
  refine SegWS.or_pre ?_ (SegWS.or_pre ?_ ?_)
  · -- the overflow label
    refine (SegWS.exists_pre (P := fun c0 s c fs' => G0 c0 ∧ (At (Ly).exe (Ly).endPc R F
        (abortN2 (imms2Me Λ p) (TailAt2 p j) p L (FC j d hd).cx
          (_root_.Executable.labels (Ly).exe).label fp ra c0)).at fs s c fs') fun c0 => ?_).mono_pre
      fun s c fs' ⟨hfs, c0, hg, hA⟩ => ⟨c0, hg, hA, hfs⟩
    by_cases hg : G0 c0
    case neg => exact SegWS.empty fun _ _ _ h' => hg h'.1
    refine (ovfAb_segF h (imms2Me Λ p) (FC j d hd).hf (FC j d hd).h16
      (fnCode2OfPMe_spec hp h Λ j d hd).2.2.1 (ovfFacts_me hp h Λ hd (imms2Me Λ p)) hC.hR hC.hal
      (by omega) hC.hhi hC.hl hC.hh hC.hFS hsub hfit hC.hFO hpz hC.hfp
      (abortN2_slotRepAt fun _ _ _ _ => rfl) (hC.hG0F c0 hg) hes (hma fs) msOfAX_K_abi hDtO _).mono_pre
      fun _ _ _ h' => h'.2
  · -- the heap abort exits
    refine (SegWS.exists_pre (P := fun (q : (AS → Ctl → Prop) × Int64) s c fs' => fs' = fs ∧
        NbJcOf (imms2Me Λ p) L (FC j d hd).cx q.1 ∧
        At (Ly).exe (Ly).endPc R F (nbX ((MSL J L ls) fs) (_root_.Executable.labels (Ly).exe).label
          L R (FC j d hd).cx.frame q.2 q.1 .abort) s c) fun ⟨Jc, pcR⟩ => ?_).mono_pre
      fun s c fs' ⟨hfs, Jc, pcR, hJ, _, hA⟩ => ⟨⟨Jc, pcR⟩, hfs, hJ, hA⟩
    by_cases hJc : NbJcOf (imms2Me Λ p) L (FC j d hd).cx Jc
    case neg => exact SegWS.empty fun _ _ _ h' => hJc h'.2.1
    refine (heapAb_seg h (imms2Me Λ p) (Λw := (Ly).Λ) (fs := fs) (pcR := pcR)
      (FC j d hd).hf (FC j d hd).h16 hJc hC.hR hC.hal
      (by simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame]; omega)
      hC.hhi hC.hl hC.hh hC.hFS hsub hfit hC.hFO hC.hfp ?_ ?_ ?_ (hma fs) msOfAX_K_abi hDtH _).mono_pre ?_
    · intro n τ us hus
      try dsimp only [MSAtL]
      generalize ab2 p _ = ab
      cases ab <;>
        (show (arOf (Ly).Λ).units n τ ≤ _
         unfold arOf; exact Arena.ofWords_units_le hus)
    · try dsimp only [MSAtL]
      generalize ab2 p _ = ab; cases ab <;> rfl
    · try dsimp only [MSAtL]
      generalize ab2 p _ = ab; cases ab <;> rfl
    · rintro s c fs' ⟨rfl, -, hA⟩
      exact ⟨hA, rfl⟩
  · -- the output call's aborts
    refine (SegWS.exists_pre (P := fun (q : Ctl × String × List String × CoreTerm.At × Expr × Ctl) s c fs' =>
        G0 q.1 ∧ TailAt2 p j (.let_ q.2.1 (.call "print" q.2.2.1 q.2.2.2.1 []) q.2.2.2.2.1) ∧
        (At (Ly).exe (Ly).endPc R F (printNAS (_root_.Executable.labels (Ly).exe).label (FC j d hd).cx
          L (imms2Me Λ p) q.2.1 q.2.2.2.2.1 q.2.2.2.2.2)).at
          (printFrame q.2.1 q.2.2.2.2.1 q.2.2.2.2.2 :: fs) s c fs') fun ⟨c0, x, is, a, e, c1⟩ => ?_).mono_pre
      fun s c fs' ⟨c0, x, is, a, e, c1, hg, hT, hfs, hA⟩ => ⟨⟨c0, x, is, a, e, c1⟩, hg, hT, hA, hfs⟩
    by_cases hgT : G0 c0 ∧ TailAt2 p j (.let_ x (.call "print" is a []) e)
    case neg => exact SegWS.empty fun _ _ _ h' => hgT ⟨h'.1, h'.2.1⟩
    obtain ⟨hg, hT⟩ := hgT
    have he : NoS ZBad e :=
      (noS_of_tailOf (hT d hd) (hpz d (List.mem_filter.1 (List.mem_of_getElem? hd)).1)).2
    refine (printAb_segP h (imms2Me Λ p) (it := imms2Me Λ p) (e := e) (FC j d hd).hf (FC j d hd).h16
      hC.hR hC.hal (by omega) hC.hhi hC.hl hC.hh hC.hFS hsub hfit hC.hFO hpz rfl he
      (hC.hG0F c0 hg).2 hC.hfp (hma _) msOfAX_K_abi hDtW _).mono_pre
      fun _ _ _ h' => h'.2.2

/-- **Every context's aborts never end at a reachable placement** (`AbG2L`
as a segment to the empty fragment inside `W2AtL … L ls`): at each context
(`abCxL_seg`), no state at a tuple failing `CxCore2L`. The placement's
`Reach` (`hre`) is `CxCore2L.hre` at every context, unused here. -/
theorem abG2L_seg {Dt : State → Prop} (hp : Scc.Lower.Accepted2 p = true) (hRo : Room2OwnStmt h hp) (J : InvS)
    (L : WeakMem.AllocLabel → Option Nat) (ls : WeakMem.AllocLabel → Nat)
    (_hre : Reach (arOf (Ly).Λ) (fun _ => none) (fun _ => 0) L ls)
    (hDtO : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.overflow c .svc) s c' → Dt s)
    (hDtW : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.write c .svc) s c' → Dt s)
    (hDtH : ∀ (R' : Region) (F' : MachineData → Prop) c s c', At (Ly).exe (Ly).endPc R' F'
      (A64.Abort.N (Ly).lab A64.Abort.heap c .svc) s c' → Dt s) :
    SegWS (W2L J L ls) (KT) p L (MSL J L ls) (AbG2L h hp Dt J L ls) (fun _ _ _ => False) := by
  unfold AbG2L
  refine SegWS.exists_pre fun j => SegWS.exists_pre fun d => SegWS.exists_pre fun hd =>
    SegWS.exists_pre fun R => SegWS.exists_pre fun F => SegWS.exists_pre fun fs =>
    SegWS.exists_pre fun fp => SegWS.exists_pre fun ra => SegWS.exists_pre fun tp =>
    SegWS.exists_pre fun G0 => ?_
  by_cases hC : CxCore2L h hp Dt J L ls j R F fs fp ra tp G0
  case neg => exact SegWS.empty fun _ _ _ h' => hC h'.1
  exact (abCxL_seg h hp hRo J L ls hDtO hDtW hDtH hd hC).mono_pre fun _ _ _ h' => h'.2

end G2L

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.abCxL_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.abCxL_seg

/-- info: 'Spike.Lib.LowerA64.abG2L_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.abG2L_seg

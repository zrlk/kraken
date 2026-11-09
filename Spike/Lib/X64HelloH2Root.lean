/-
**`h2`'s statement at hello's root** (x86-64; twin of `Spike/Lib/A64HelloH2Root.lean`; the hello twin of wake's
`h1Stmt_box`): `X64HelloH2Box.h2Stmt_box` at the root's premises `P : HelloRootPrem (Ly) LB`, the take site
`a := lab siteL`, the refusal `ClH`, with

- the box's landing `Box := BoxMH … (P.G …) l' b' (slWsH l) n' ∧ KeepUn.U r1Of` (`hmid`'s pre; a `GsH1` landing with
  `r1Of` unmapped is one by `RootHP.boxMH_landingRH`);
- `hmid` by `HelloRootPremX.hmid`, `CP := CloneMidH …`;
- `hCP` by `X64HelloH2CP.hCP_of`, its `hCI` by `RootHP.hCI_RH` (the root's ghosts `P.G = GJ1RH (Ly) (upd LB l b) l`,
  `GJ1H` with the region and frame condition pinned, so that `HelloRootPrem.hP` is `RootHP.hP_ofG`'s), its `hSeg` by
  `X64HelloCloneSeg.cloneSegH_of_mid` (the first stack in the address space, `X64WakeHClC.hbd_W`);
- `Ref := RefH.RefH …`, `hret` by `RefH.hret_H`, `hseg` by `RefH.seg_refH` at the refusal path's obligations
  `hobl`.

The level `P.W2` stays generic (at the root it is `HelloW2.W2H`); its fence's extra fact is `X2H` (`hX2`), the level's
extra fact at the clone the child's stack private (`hWc`, `Ret0.StackM r1Of`); the take site is off the clone's pc
(`hna_H`, decided offsets). Nothing here reads the child's memory side.

- `hna_H`: the clone's `syscall` is not the take site.
- `h2Stmt_rootG`: the statement at any start level, given `hmid`; `h2Stmt_rootX` at `HelloRootPremX.hmid` (the root
  at the self words).

## Unlike AArch64

- `hna_H` reads both pcs off the root's labels `hlab` (`.Lwc_main.x3 + 94`, the take site's label; `cvH`), so it
  takes `hlab` rather than the output's program (AArch64: `PlaceW.hlab_ofPlaceW` at `codeOf 0`).
- `hCP_of`'s `hSeg` (the clone's segment-end facts) is a premise on x86-64; it is `cloneSegH_of_mid` at `GJ1RH`.
  Its `hFp` (the parent's saved frame pointer at the clone frame) is `X64HelloHfp.hfp_of_parts` at `RootHP.hpin_RH`.
-/
import Spike.Lib.X64HelloRootHP
import Spike.Lib.X64HelloRefH
import Spike.Lib.X64HelloRootPrem
import Spike.Lib.X64HelloCloneSeg
import Spike.Lib.X64HelloWcClonePc
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64HelloHfp

namespace Spike.Lib.X64.HelloPh.H2Root

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (FragS SegWS)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64ConsumerA (TakeCKS)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.PreChild (r1Of)
open Spike.Lib.X64HelloPreA (H2StmtH clonePcH)
open Spike.Lib.X64HelloHMid (BoxMH CloneMidH slWsH)
open Spike.Lib.X64HelloH2Inv (X2H inv2H)
open Spike.Lib.X64.HelloPh.RootHP (GJ1RH)
open Spike.Lib.X64.HelloPh.RefH (RefH RefOblH)
open Spike.Lib.X64.HelloPh (HelloRootPrem HelloRootPremG ClH lbl2H lo)
open Spike.Lib.X64.HelloPh.WcW (cvH clone_inCvH lab_cvH)
open Spike.Lib.X64WakeLoadT (L0T)
open Scc.Cert.Rt.X64 (codeT_eq)

/-- **The clone's `syscall` is not the take site**: at labels placing hello's cells at `lo` (`hlab`), the clone's
pc is `.Lwc_main.x3 + 94` and the take site its label, at offsets that differ. -/
theorem hna_H {L : RuntimeLayout}
    (hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → L.lab l = Int64.ofNat x) :
    clonePcH L ≠ (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have hc := clone_inCvH
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hs, hb⟩, -⟩ := hc
  have e : clonePcH L = cvH ".Lwc_main.x3" + 94 := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp hs
    have ey : cvH ".Lwc_main.x3" = y := by simp [cvH, hy]
    rw [ey] at hb ⊢
    show (L.lab ".Lwc_main.x3" + 94).toBitVec.toNat = y + 94
    rw [hlab _ y hy]
    show (BitVec.ofNat 64 y + BitVec.ofNat 64 94).toNat = y + 94
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have hst := lab_cvH hlab (l := Spike.Lib.X64.Flow.Ret0.StackTake.siteL)
    (by rw [← codeT_eq]; decide +kernel) (by unfold cvH; rw [← codeT_eq]; decide +kernel)
  rw [e, hst]
  unfold cvH; rw [← codeT_eq]; decide +kernel

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The take site. -/
local notation "AT" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The level's sizes. -/
local notation "S2" => fun (l : WeakMem.AllocLabel) (n : Nat) (l' : WeakMem.AllocLabel) (n' : Nat) =>
  Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64ConsumerA.updN ls0 l n) l' n'

/-- **`H2StmtH` at hello's root at any start level** (see the module doc), given `hmid`
(`HelloRootPremX.hmid`). -/
theorem h2Stmt_rootG {WS} (P : HelloRootPremG WS (Ly) (LB)) {ls0 : Lsize}
    (hmid : ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H P.ar (LB) l b n l' b' n' →
      SegWS (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs) (TakeCKS (AT) (ClH (Ly)))
        Spike.Lib.X64HelloSrc.helloSrc (lbl2H (LB) l b l' b') (P.ms2 l b n l' b' n')
        (fun s c fs => BoxMH (Ly) (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
          Spike.Lib.X64.KeepUn.U (r1Of (Ly).lab) s ∧ fs = [])
        (CloneMidH (Ly) P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n') l' b' (slWsH l) n'))
    /- the fence's extra fact is `X2H` at the level's placement and sizes -/
    (hX2 : P.X2 = fun l b n l' b' n' => X2H (Ly) (AT) (Ly).endPc (lbl2H (LB) l b l' b') ((S2) l n l' n'))
    /- the root's ghosts are `GJ1RH` (`GsH1`'s pin, the region and frame condition the real run's) -/
    (hG : P.G = fun l b _ _ _ _ => GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l)
    /- the level's extra fact at the clone: the child's stack private -/
    (hWc : ∀ l b n l' b' n' s c, P.Wc l b n l' b' n' s c → Spike.Lib.X64.Flow.Ret0.StackM (r1Of (Ly).lab) s.st.1)
    /- the refusal path's obligations inside the level -/
    (hobl : ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H P.ar (LB) l b n l' b' n' →
      RefOblH (Ly) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n'
        (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs) (TakeCKS (AT) (ClH (Ly)))
        (lbl2H (LB) l b l' b') (P.ms2 l b n l' b' n')) :
    H2StmtH P.W2 (TakeCKS (AT) (ClH (Ly))) P.ar (LB) P.ms2 (Ly) (Ly).endPc
      (fun l b n l' b' n' s c => BoxMH (Ly) (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
        Spike.Lib.X64.KeepUn.U (r1Of (Ly).lab) s)
      (inv2H P.W2 (TakeCKS (AT) (ClH (Ly))) P.ms2 (Ly) (AT) (Ly).endPc (LB) ls0) := by
  refine Spike.Lib.X64HelloH2Box.h2Stmt_box (ls0 := ls0) P.ar
    (CP := fun l b n l' b' n' => CloneMidH (Ly) P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n')
      l' b' (slWsH l) n')
    (Ref := fun l b n l' b' n' => RefH (Ly) P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n')
      l' b' (slWsH l) n')
    (fun l b n l' b' n' hl hb hl' hb' => ?_) (fun l b n l' b' n' hl hb hl' hb' => ?_)
    (fun l b n l' b' n' _ _ _ _ s c fs h r hr => Spike.Lib.X64.HelloPh.RefH.hret_H h r hr)
    (fun l b n l' b' n' hl hb hl' hb' => ?_)
  · have h := hmid l b n l' b' n' ⟨hl, hb, hl', hb'⟩
    rw [hX2] at h
    exact h.mono_pre fun s c fs ⟨⟨hB, hU⟩, hfs⟩ => ⟨hB, hU, hfs⟩
  · intro s c fs h
    have hci := Spike.Lib.X64.HelloPh.RootHP.hCI_RH hpw i0 (F0 := P.F0) (W := P.W2 l b n l' b' n')
      (Wc := P.Wc l b n l' b' n') (b' := b') (n' := n') hl hl'
    rw [hG] at h
    have hbd : (Ly).stacksA.toNat + 32768 < 2 ^ 64 := by
      have := Spike.Lib.X64WakeHClC.hbd_W hpw (IH)
      rwa [(Ly).lab_stacks] at this
    exact Spike.Lib.X64HelloH2CP.hCP_of P.hp P.hsub (hna_H P.hlab) (hWc l b n l' b' n') hci
      (fun s c fs h => Spike.Lib.X64HelloCloneSeg.cloneSegH_of_mid hbd h)
      (fun s c fs h _ _ _ _ _ _ hat => Spike.Lib.X64HelloHfp.hfp_of_parts h Spike.Lib.X64.HelloPh.RootHP.hpin_RH hat)
      s c fs h
  · have h := Spike.Lib.X64.HelloPh.RefH.seg_refH (W := P.W2 l b n l' b' n') (Wc := P.Wc l b n l' b' n')
      P.hp (P.hK2 _ _ _ _ _ _ ⟨hl, hb, hl', hb'⟩)
      (hobl l b n l' b' n' ⟨hl, hb, hl', hb'⟩)
    rw [hX2] at h
    exact h

/-- **`H2StmtH` at hello's root at the self words** (`h2Stmt_rootG` at `HelloRootPremX.hmid`, given the worker's
TCB word off the counters and `ntA`). -/
theorem h2Stmt_rootX (P : Spike.Lib.X64.HelloPh.HelloRootPremX (Ly) (LB)) {ls0 : Lsize}
    (hW : Spike.Lib.X64HelloOwnLift.tcbWH (Ly) ∉
      [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab])
    (hX2 : P.X2 = fun l b n l' b' n' => X2H (Ly) (AT) (Ly).endPc (lbl2H (LB) l b l' b') ((S2) l n l' n'))
    (hG : P.G = fun l b _ _ _ _ => GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l)
    (hWc : ∀ l b n l' b' n' s c, P.Wc l b n l' b' n' s c → Spike.Lib.X64.Flow.Ret0.StackM (r1Of (Ly).lab) s.st.1)
    (hobl : ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H P.ar (LB) l b n l' b' n' →
      RefOblH (Ly) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n'
        (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs) (TakeCKS (AT) (ClH (Ly)))
        (lbl2H (LB) l b l' b') (P.ms2 l b n l' b' n')) :
    H2StmtH P.W2 (TakeCKS (AT) (ClH (Ly))) P.ar (LB) P.ms2 (Ly) (Ly).endPc
      (fun l b n l' b' n' s c => BoxMH (Ly) (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
        Spike.Lib.X64.KeepUn.U (r1Of (Ly).lab) s)
      (inv2H P.W2 (TakeCKS (AT) (ClH (Ly))) P.ms2 (Ly) (AT) (Ly).endPc (LB) ls0) :=
  h2Stmt_rootG hpw i0 P (fun _ _ _ _ _ _ hf => Spike.Lib.X64.HelloPh.HelloRootPremX.hmid P hW hf) hX2 hG hWc hobl

end Spike.Lib.X64.HelloPh.H2Root

/-- info: 'Spike.Lib.X64.HelloPh.H2Root.h2Stmt_rootG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Root.h2Stmt_rootG

/-- info: 'Spike.Lib.X64.HelloPh.H2Root.h2Stmt_rootX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Root.h2Stmt_rootX

/-- info: 'Spike.Lib.X64.HelloPh.H2Root.hna_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.H2Root.hna_H

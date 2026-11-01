/-
**`h2`'s statement at hello's root** (AArch64; the assembly; the hello twin of
wake's `h1Stmt_box` at `WakeOPremW`): `HelloH2Box.h2Stmt_box` at the root's premises `P : HelloRootPrem (Ly) LB`,
the take site `a := lab siteL`, the refusal `ClH`, with

- the box's landing `Box := BoxMH … (P.G …) l' b' (slWsH l) n' ∧ KeepUn.U r1Of` (`hmid`'s pre; a `GsH1` landing with
  `r1Of` unmapped is one by `RootHP.boxMH_landingRH`, `RootHP.hland2_boxMRU`);
- `hmid` by `HelloRootPrem.hmid`, `CP := CloneMidH …`;
- `hCP` by `HelloH2CP.hCP_of`, its `hCI` by `RootHP.hCI_RH` (the root's ghosts `P.G = GJ1RH (Ly) (upd LB l b) l`,
  `GJ1H` with the region and frame condition pinned, so that `HelloRootPrem.hP` is `RootHP.hP_of`);
- `Ref := RefH.RefH …`, `hret` by `RefH.hret_H`, `hseg` by `RefH.seg_refH` at the refusal path's obligations
  `hobl`.

The level `P.W2` stays generic (at the root it is `HelloW2.W2H`); its fence's extra fact is `X2H` (`hX2`), the level's
extra fact at the clone the child's stack private (`hWc`, `Ret0.StackM r1Of`); the take site is off the clone's pc
(`hna_H`, decided offsets). Nothing here reads the child's memory side.

- `codeOf_sp6H`, `codeOf_siteH`, `hna_H`: the clone's `svc` is not the take site.
- `h2Stmt_root`: the statement.
-/
import Spike.Lib.A64HelloRootHP
import Spike.Lib.A64HelloRefH
import Spike.Lib.A64HelloRootPrem
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64HelloCloneSeg
import Spike.Lib.A64WakeHClW

namespace Spike.Lib.A64.HelloPh.H2Root

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (FragS SegWS)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.PreChild (r1Of)
open Spike.Lib.HelloPreA (H2StmtH clonePcH)
open Spike.Lib.HelloHMid (BoxMH CloneMidH slWsH)
open Spike.Lib.HelloH2Inv (X2H inv2H)
open Spike.Lib.A64.HelloPh.RootHP (GJ1RH)
open Spike.Lib.A64.HelloPh.RefH (RefH RefOblH)
open Spike.Lib.A64.HelloPh (HelloRootPrem ClH lbl2H)
open Spike.Lib.WakeLoadT (L0T)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The take site. -/
local notation "AT" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The level's sizes. -/
local notation "S2" => fun (l : WeakMem.AllocLabel) (n : Nat) (l' : WeakMem.AllocLabel) (n' : Nat) =>
  Spike.Lib.A64ConsumerA.updN (Spike.Lib.A64ConsumerA.updN ls0 l n) l' n'

/-- The clone's `.sp6` (the `svc` 25 instructions past it) in hello's program at `0`. -/
theorem codeOf_sp6H :
    Scc.Cert.Link.A64.codeOf 0 SccCode.helloProg (Spike.Lib.A64.Flow.Worker.Hello.Child.pfxM ++ ".sp6") =
      some 5692 := by
  decide +kernel

/-- The take site in hello's program at `0`. -/
theorem codeOf_siteH :
    Scc.Cert.Link.A64.codeOf 0 SccCode.helloProg Spike.Lib.A64.Flow.Ret0.StackTake.siteL = some 1928 := by
  decide +kernel

/-- **The clone's `svc` is not the take site** (`WakeSrcCtl.cloneAt_ne_site`'s twin): both labels resolved in
hello's program at offsets that differ. -/
theorem hna_H (ho : o.prog = SccCode.helloProg) : clonePcH (Ly) ≠ ((AT)).toBitVec.toNat := by
  have h1 := Spike.Lib.PlaceW.hlab_ofPlaceW hpw IH _ ((Ly).Λ.code.lo + 5692)
    (by rw [ho, Spike.Lib.WakeSrcCtl.codeOf_base, codeOf_sp6H]; rfl)
  have h2 := Spike.Lib.PlaceW.lab_toNat hpw IH (l := Spike.Lib.A64.Flow.Ret0.StackTake.siteL)
    (a := (Ly).Λ.code.lo + 1928) (by rw [ho, Spike.Lib.WakeSrcCtl.codeOf_base, codeOf_siteH]; rfl)
  have hend := Spike.Lib.PlaceW.codeEnd_lt hpw IH
  have hs : (SccCode.helloProg.map Directive.fakeSize).sum = 6060 := by decide +kernel
  rw [ho] at hend; unfold Scc.Sem.A64.codeEnd at hend; rw [hs] at hend
  unfold clonePcH Spike.Lib.HelloPreA.cloneAtH
  change ((Ly).lab _ + _).toBitVec.toNat ≠ ((Ly).lab _).toBitVec.toNat
  rw [h1, h2, Spike.Lib.A64.Rt.PhOfTab.toNat_add]
  omega

/-- **`H2StmtH` at hello's root** (see the module doc). -/
theorem h2Stmt_root (P : HelloRootPrem (Ly) (LB)) {ls0 : Lsize}
    /- the fence's extra fact is `X2H` at the level's placement and sizes -/
    (hX2 : P.X2 = fun l b n l' b' n' => X2H (Ly) (AT) (Ly).endPc (lbl2H (LB) l b l' b') ((S2) l n l' n'))
    /- the root's ghosts are `GJ1RH` (`GsH1`'s pin, the region and frame condition the real run's) -/
    (hG : P.G = fun l b _ _ _ _ => GJ1RH (Ly) (Spike.Lib.A64ConsumerA.upd (LB) l b) l)
    /- the level's extra fact at the clone: the child's stack private -/
    (hWc : ∀ l b n l' b' n' s c, P.Wc l b n l' b' n' s c → Spike.Lib.A64.Flow.Ret0.StackM (r1Of (Ly).lab) s.st.1)
    /- row: B8-h2-refObl. The refusal path's obligations inside the level. -/
    (hobl : ∀ l b n l' b' n', Spike.Lib.A64.HelloPh.Fresh2H P.ar (LB) l b n l' b' n' →
      RefOblH (Ly) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n'
        (fun s c fs => P.W2 l b n l' b' n' s c fs ∧ P.X2 l b n l' b' n' s c fs) (TakeCKS (AT) (ClH (Ly)))
        (lbl2H (LB) l b l' b') (P.ms2 l b n l' b' n')) :
    H2StmtH P.W2 (TakeCKS (AT) (ClH (Ly))) P.ar (LB) P.ms2 (Ly) (Ly).endPc
      (fun l b n l' b' n' s c => BoxMH (Ly) (P.msB l b n) P.F0 (P.G l b n l' b' n') l' b' (slWsH l) n' s c ∧
        Spike.Lib.A64.KeepUn.U (r1Of (Ly).lab) s)
      (inv2H P.W2 (TakeCKS (AT) (ClH (Ly))) P.ms2 (Ly) (AT) (Ly).endPc (LB) ls0) := by
  refine Spike.Lib.HelloH2Box.h2Stmt_box (ls0 := ls0) P.ar
    (CP := fun l b n l' b' n' => CloneMidH (Ly) P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n')
      l' b' (slWsH l) n')
    (Ref := fun l b n l' b' n' => RefH (Ly) P.F0 (P.G l b n l' b' n') (P.W2 l b n l' b' n') (P.Wc l b n l' b' n')
      l' b' (slWsH l) n')
    (fun l b n l' b' n' hl hb hl' hb' => ?_) (fun l b n l' b' n' hl hb hl' hb' => ?_)
    (fun l b n l' b' n' _ _ _ _ s c fs h r hr => Spike.Lib.A64.HelloPh.RefH.hret_H h r hr)
    (fun l b n l' b' n' hl hb hl' hb' => ?_)
  · have h := P.hmid (l := l) (b := b) (n := n) (l' := l') (b' := b') (n' := n') ⟨hl, hb, hl', hb'⟩
    rw [hX2] at h
    exact h.mono_pre fun s c fs ⟨⟨hB, hU⟩, hfs⟩ => ⟨hB, hU, hfs⟩
  · intro s c fs h
    have hci := Spike.Lib.A64.HelloPh.RootHP.hCI_RH hpw i0 (F0 := P.F0) (W := P.W2 l b n l' b' n')
      (Wc := P.Wc l b n l' b' n') (b' := b') (n' := n') hl hl'
    rw [hG] at h
    have hbd : (Ly).stacksA.toNat + 32768 < 2 ^ 64 := Spike.Lib.WakeHClW.hbd_W hpw (IH) P.hsub
    exact Spike.Lib.HelloH2CP.hCP_of P.hp P.hsub (hna_H hpw i0 P.hp) (hWc l b n l' b' n') hci
      (fun s c fs h => Spike.Lib.HelloCloneSeg.cloneSegH_of_mid hbd h) s c fs h
  · have h := Spike.Lib.A64.HelloPh.RefH.seg_refH (W := P.W2 l b n l' b' n') (Wc := P.Wc l b n l' b' n')
      P.hp (P.hK2 _ _ _ _ _ _ ⟨hl, hb, hl', hb'⟩)
      (hobl l b n l' b' n' ⟨hl, hb, hl', hb'⟩)
    rw [hX2] at h
    exact h

end Spike.Lib.A64.HelloPh.H2Root

/-- info: 'Spike.Lib.A64.HelloPh.H2Root.h2Stmt_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.H2Root.h2Stmt_root

/-- info: 'Spike.Lib.A64.HelloPh.H2Root.hna_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.H2Root.hna_H

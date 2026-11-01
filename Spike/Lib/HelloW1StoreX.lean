/-
**The store phase's further facts at hello's worker side** (C4, relation
half, check-in 6; the bridge in `Spike/Lib/HelloW1Store.lean`,
`Spike/Lib/HelloW1StoreC.lean`, `Spike/Lib/HelloW1StoreZ.lean`):
`WStoreX` at `HelloWorkerRR.QIR`/`helloDR`, on the worker's memory side
`HelloMsW.msWH` (`HelloMs.msH` with `print`'s byte step and the write abort's
justification; the segment premise `hseg` at `msWH` itself) and location data
`helloP`, and so wake's `WCompat` at
`relW`.

- `wstoreX_IR`: `WStoreX` at `QIR`, with the placement pinned to the spawn's
  (`lbl w := (SR w).lbl`), the memory side `fun w _ => msWH L G SR w` on every
  frame, `Pa w := helloP abi μ (helloLocs …)` and `Λ := L.Λ`. Closed here:
  `atUnpk`, `atTexit`, `lbl` (`rfl`), `K`, `G`, `own` (`HelloMs`, the owned
  words of `wakeOwn` being none), `mpW` (`mpW1_H`), `noProm` (`noProm1_H`),
  `noAbW` (`noAbW_IR` from `ZStoreOk`), `ownInstr` (`WakeOwn.ownInstr`),
  `ownSys` (`rfl`), `tid0` (`WakeM0.tid0_of`). Open: `ZStoreOk` and the spawn
  rows' `cT`, `cTin`, `cTfoot`, `cSfrz`, `footLab`, `Spos`, `mainLive`.
- `wcompat_relW_IR`: `WakeW1.WCompat` at `relW (QIR …) (helloDR …)` from
  `hC_IR`'s `WCompatH` and `wstoreX_IR`.
-/
import Spike.Lib.HelloW1StoreZ
import Spike.Lib.HelloMsW

namespace Spike.Lib.HelloW1Store

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc Spike.Lib.Inv2Core
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.HelloInst (helloP)
open Spike.Lib.HelloMs (msH helloLocs)
open Spike.Lib.HelloMsW (msWH)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)

section IRX

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (L : RuntimeLayout) (G : ι → Loc → Val → Prop)
  (SR : ι → SpawnRec) (P Z X : ι → FragS isaLSE2)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (SR w).lbl (fun _ => msWH L G SR w)
    (P w) (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
  (cT : ι → Loc) (cS : ι → WeakMem.Address) {pT : ι → Loc} {passT : State → Prop} {M : WakeM0.MSide ι}
  {r0 r1 : ι → Range}

/-- `helloDR` on hello's memory side, placed at the spawn's labels. -/
noncomputable abbrev helloDH : WSideH ι :=
  HelloWorkerRR.helloDR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWH L G SR w) P Z X (fun _ _ => rfl) hseg
    cw bufL nB mB

/-- `QIR` at `helloDH` and `helloP`'s location data. -/
noncomputable abbrev QIH : WakeRel :=
  HelloWorkerRR.QIR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWH L G SR w) P Z X (fun _ _ => rfl) hseg
    cw bufL nB mB arch R1 cT cS pT (fun w => helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w)))
    G passT M r0 r1

/-- **`WStoreX` at hello's worker side** (`QIH`, `helloDH`; the placement
pinned to the spawn's, `lbl w := (SR w).lbl`). Open: `ZStoreOk` at the
segment's `Z` (with `hcw`), the spawn rows (`cT`, `cTin`, `cTfoot`, `cSfrz`,
`footLab`), `Spos` and `mainLive`. -/
theorem wstoreX_IR (hcw : ∀ w, ∃ cS, (cw w).val = .loc cS 0) (hZ : ZStoreOk exe Z)
    (hcT : ∀ w, ∃ a, cT w = wordLoc a ∧ wordAddr (SR w).lbl (cS w) = some a ∧
      (cS w).offset < (SR w).lsize (cS w).label)
    (hcTin : ∀ w, Consumer1.LocIn L.Λ.shared (cT w))
    (hcTfoot : ∀ w, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 (cT w))
    (hcSfrz : ∀ w, ¬ (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).frzS (cS w))
    (hSpos : ∀ w, 0 < (SR w).S)
    (hfootLab : ∀ w Lc, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 Lc →
      InLabel (SR w).lbl (SR w).lsize Lc → Lc = cT w)
    (hmainLive : ∀ t s, (QIH exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (arch := arch) (R1 := R1) (μ := μ)
      (pT := pT) (passT := passT) (M := M) (r0 := r0) (r1 := r1)).Post L.Λ t s → t.2.exited = none →
      SrcSem.mainExit s = []) :
    WStoreX (QIH exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (arch := arch) (R1 := R1) (μ := μ)
        (pT := pT) (passT := passT) (M := M) (r0 := r0) (r1 := r1))
      (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) μ L.Λ (AbW exe) where
  atUnpk := rfl
  atTexit := rfl
  lbl _ := rfl
  K _ := rfl
  G _ := rfl
  own _ _ := rfl
  mpW := mpW1_H L G SR cT cS
  noAbW := noAbW_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWH L G SR w) P Z X (fun _ _ => rfl) hseg
    cw bufL nB mB hcw hZ
  ownInstr w s _ tree _ _ _ := WakeOwn.ownInstr w s tree
  ownSys _ _ _ _ _ _ _ _ _ := rfl
  cT := hcT
  cTin := hcTin
  cTfoot := hcTfoot
  cSfrz := hcSfrz
  Spos := hSpos
  footLab := hfootLab
  noProm := noProm1_H L SR cT cS
  mainLive := hmainLive
  tid0 _ tm sm _ _ h := WakeM0.tid0_of (tm := tm) (sm := sm) h

/-- **Wake's compatibility facts at `relW` on hello's worker side**:
`wcompat_relW` from `HelloWorkerRR.hC_IR`'s `WCompatH` and `wstoreX_IR`,
with `hcw` from `cwv` and `NoWrite` from `noWrite_IR`. Open: `hC_IR`'s
`cwv`, `pass`, and `wstoreX_IR`'s premises but `hcw`. -/
theorem wcompat_relW_IR [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    (cwv : ∀ w, (cw w).val = .loc (cS w) 0)
    (pass : HelloW1.PassH (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) passT)
    (hZ : ZStoreOk exe Z)
    (hcT : ∀ w, ∃ a, cT w = wordLoc a ∧ wordAddr (SR w).lbl (cS w) = some a ∧
      (cS w).offset < (SR w).lsize (cS w).label)
    (hcTin : ∀ w, Consumer1.LocIn L.Λ.shared (cT w))
    (hcTfoot : ∀ w, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 (cT w))
    (hcSfrz : ∀ w, ¬ (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).frzS (cS w))
    (hSpos : ∀ w, 0 < (SR w).S)
    (hfootLab : ∀ w Lc, (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 Lc →
      InLabel (SR w).lbl (SR w).lsize Lc → Lc = cT w)
    (hmainLive : ∀ t s, (QIH exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (arch := arch) (R1 := R1) (μ := μ)
        (pT := pT) (passT := passT) (M := M) (r0 := r0) (r1 := r1)).Post L.Λ t s → t.2.exited = none →
      SrcSem.mainExit s = []) :
    WakeW1.WCompat (relW (QIH exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (arch := arch) (R1 := R1) (μ := μ)
        (pT := pT) (passT := passT) (M := M) (r0 := r0) (r1 := r1))
        (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) (fun w => ⟨cS w, cwv w⟩)
        (noWrite_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWH L G SR w) P Z X (fun _ _ => rfl) hseg
          cw bufL nB mB (fun w => ⟨cS w, cwv w⟩) hZ))
      (wsideW (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) (fun w => ⟨cS w, cwv w⟩)
        (noWrite_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWH L G SR w) P Z X (fun _ _ => rfl) hseg
          cw bufL nB mB (fun w => ⟨cS w, cwv w⟩) hZ)) μ L.Λ arch :=
  wcompat_relW
    (HelloWorkerRR.hC_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWH L G SR w) P Z X (fun _ _ => rfl) hseg
      cw bufL nB mB hl hend hμ cwv pass)
    (wstoreX_IR exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (fun w => ⟨cS w, cwv w⟩) hZ hcT hcTin hcTfoot
      hcSfrz hSpos hfootLab hmainLive)
    (fun w t t' s s' s0 p h hw a b c d e hW =>
      ⟨HelloWorkerRR.krh_permit w t t' s s' s0 p h.1 a b c d (by simp only [SrcSem.traceOf, e]),
        HelloKRE.lk_wr0 (by rw [a]; exact hw) hW⟩)

end IRX

/-- info: 'Spike.Lib.HelloW1Store.wcompat_relW_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wcompat_relW_IR


end Spike.Lib.HelloW1Store

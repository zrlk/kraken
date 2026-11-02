/-
**The store phase's further facts at hello's worker side** (relation
half; the bridge in `Spike/Lib/X64HelloW1Store.lean`,
`Spike/Lib/X64HelloW1StoreC.lean`, `Spike/Lib/X64HelloW1StoreZ.lean`):
`WStoreX` at `X64HelloWorkerRR.QIR`/`helloDR`, on the worker's memory side
`X64HelloOwnLift.msWHX` (`X64HelloMsW.msWH`, i.e. `X64HelloMs.msH` with `print`'s byte step and the write
abort's justification, owning the worker's TCB self word `tcbWH`; the segment premise `hseg` at `msWHX`
itself) and location data `helloP`, and so wake's `WCompat` at
`relW`.

- `wstoreX_IR`: `WStoreX` at `QIR`, with the placement pinned to the spawn's
  (`lbl w := (SR w).lbl`), the memory side `fun w _ => msWHX L G SR w` on every
  frame, `Pa w := helloP abi μ (helloLocs …)` and `Λ := L.Λ`. Closed here:
  `atUnpk`, `atTexit`, `lbl` (`rfl`), `K`, `G`, `own` (`rfl`: `helloQ`'s thread 1 words
  are the worker side's), `mpW` (`mpW1_H`), `noProm` (`noProm1_H`),
  `noAbW` (`noAbW_IR` from `ZStoreOk`), `ownInstr` (`hZW` at the segment's `Z`, by `z_of_wiS`, as
  `X64WakeW1.OwnInstrW.ownInstr_of`), `ownSys` (`rfl`), `tid0` (`X64WakeM0.tid0_of`). Hypotheses:
  `ZStoreOk`, `hZW` and the spawn rows' `cT`, `cTin`, `cTfoot`, `cSfrz`, `footLab`, `Spos`, `mainLive`.
- `wcompat_relW_IR`: `X64WakeW1.WCompat` at `relW (QIR …) (helloDR …)` from
  `hC_IR`'s `WCompatH` (the worker's word covered by `X64HelloMs.ownCov1_H`; disjoint from main's, which is
  `tcbM`'s alone by `hownM`, by `tcbM_ne_tcbWH`) and `wstoreX_IR`.

`hZW` (the store phase's instructions write off `tcbWH`'s word) is an open premise: it is discharged at
`AssemblyRS` by the worker fragment's `OwnW (tcbWH)` conjunct (in progress); it does not follow from `Z`.

x86-64 twin of `Spike/Lib/HelloW1StoreX.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the layout premise is `Scc.Cert.Rt.X64.Lays` at the placed cells
`SccCode.helloCells` (not `helloProg`), as in `X64HelloWorkerRR.hC_IR`, and `helloP` is
`X64HelloInst.helloP`.
-/
import Spike.Lib.X64HelloW1StoreZ
import Spike.Lib.X64HelloMsW
import Spike.Lib.X64OwnWNodes

namespace Spike.Lib.X64HelloW1Store

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc Spike.Lib.Inv2Core
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.HelloSegTCSX (SegTCSX)
open Spike.Lib.X64.Flow.Worker (NNH AbW)
open Spike.Lib.X64HelloInst (helloP)
open Spike.Lib.X64HelloMs (msH helloLocs)
open Spike.Lib.X64HelloOwnLift (msWHX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Scc.Cert.Rt.X64 (Lays endOf)

section IRX

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (L : RuntimeLayout) (G : ι → Loc → Val → Prop)
  (SR : ι → SpawnRec) (P Z X : ι → FragS isa)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (SR w).lbl (fun _ => msWHX L G SR w)
    (P w) (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)
  {arch : WeakMem.Arch} {R1 : Cfg → TermRun.Cfg → Prop} {μ : Marks}
  (cT : ι → Loc) (cS : ι → WeakMem.Address) {pT : ι → Loc} {passT : State → Prop} {M : X64WakeM0.MSide ι}
  {r0 r1 : ι → Range}

/-- `helloDR` on hello's memory side, placed at the spawn's labels. -/
noncomputable abbrev helloDH : WSideH ι :=
  X64HelloWorkerRR.helloDR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg
    cw bufL nB mB

/-- `QIR` at `helloDH` and `helloP`'s location data. -/
noncomputable abbrev QIH : WakeRel :=
  X64HelloWorkerRR.QIR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg
    cw bufL nB mB arch R1 cT cS pT (fun w => helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w)))
    G passT M r0 r1

/-- **`WStoreX` at hello's worker side** (`QIH`, `helloDH`; the placement
pinned to the spawn's, `lbl w := (SR w).lbl`). Hypotheses: `ZStoreOk` at the
segment's `Z` (with `hcw`), the spawn rows (`cT`, `cTin`, `cTfoot`, `cSfrz`,
`footLab`), `Spos` and `mainLive`. -/
theorem wstoreX_IR (hcw : ∀ w, ∃ cS, (cw w).val = .loc cS 0) (hZ : ZStoreOk exe Z)
    (hZW : ∀ w s c, Z w s c [] → c.hold = none → StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH L) s c)
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
  noAbW := noAbW_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg
    cw bufL nB mB hcw hZ
  ownInstr w s c tree hW hns he := by
    show Consumer1.OwnTree (fun _ => [(⟨X64HelloOwnLift.tcbWH L, 8⟩, (X64HelloOwnLift.tcbWH L).setWidth 128)])
      [(⟨X64HelloOwnLift.tcbWH L, 8⟩, (X64HelloOwnLift.tcbWH L).setWidth 128)] tree
    have hz := z_of_wiS hcw (fun w s c fs h => (X64HelloWorkerRR.helloDR_inv exe endPc SR (fun w => (SR w).lbl)
      (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg cw bufL nB mB w s c fs h).2.2) hW
    exact .inl ⟨(Consumer1.allInv_true tree).mono fun _ _ => rfl,
      Consumer1.writeTree_mono (fun l _ hl v hm => by
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        exact hl hm.1) (hZW w s c hz hW.2.1 hW.2.2.1 hns tree he)⟩
  ownSys _ _ _ _ _ _ _ _ _ := rfl
  cT := hcT
  cTin := hcTin
  cTfoot := hcTfoot
  cSfrz := hcSfrz
  Spos := hSpos
  footLab := hfootLab
  noProm := noProm1_H L SR cT cS
  mainLive := hmainLive
  tid0 _ tm sm _ _ h := X64WakeM0.tid0_of (tm := tm) (sm := sm) h

/-- **Wake's compatibility facts at `relW` on hello's worker side**:
`wcompat_relW` from `X64HelloWorkerRR.hC_IR`'s `WCompatH` and `wstoreX_IR`,
with `hcw` from `cwv` and `NoWrite` from `noWrite_IR`. Hypotheses: `hC_IR`'s
`cwv`, `pass`, and `wstoreX_IR`'s premises but `hcw`. -/
theorem wcompat_relW_IR [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hl : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    (cwv : ∀ w, (cw w).val = .loc (cS w) 0)
    (pass : X64HelloW1.PassH (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) passT)
    (hZ : ZStoreOk exe Z)
    (hZW : ∀ w s c, Z w s c [] → c.hold = none → StoreT c.term →
      Spike.Lib.X64.Flow.Worker.Wake.OwnW.OwnW (X64HelloOwnLift.tcbWH L) s c)
    /- main's side owns `tcbM`'s word alone -/
    (hownM : ∀ w s, (M.ms w).own s = [(⟨Spike.Lib.X64.WakePh.tcbM L, 8⟩, (Spike.Lib.X64.WakePh.tcbM L).setWidth 128)])
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
    X64WakeW1.WCompat (relW (QIH exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (arch := arch) (R1 := R1) (μ := μ)
        (pT := pT) (passT := passT) (M := M) (r0 := r0) (r1 := r1))
        (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) (fun w => ⟨cS w, cwv w⟩)
        (noWrite_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg
          cw bufL nB mB (fun w => ⟨cS w, cwv w⟩) hZ))
      (wsideW (helloDH exe endPc L G SR P Z X hseg cw bufL nB mB) (fun w => ⟨cS w, cwv w⟩)
        (noWrite_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg
          cw bufL nB mB (fun w => ⟨cS w, cwv w⟩) hZ)) μ L.Λ arch :=
  wcompat_relW
    (X64HelloWorkerRR.hC_IR exe endPc SR (fun w => (SR w).lbl) (fun w _ => msWHX L G SR w) P Z X (fun _ _ => rfl) hseg
      cw bufL nB mB hl hend hμ cwv pass (fun w s _ Lc v h =>
        X64HelloMs.ownCov1_H (L := L) (SR := SR) (μ := μ) cT cS w s Lc v h)
      (fun w s0 s _ Lc v v' h0 h1 => by
        rw [hownM] at h0
        simp only [msWHX, X64WakeOwnX.msXW, List.mem_singleton, Prod.mk.injEq] at h0 h1
        exact X64HelloMs.tcbM_ne_tcbWH L (congrArg Loc.addr (h0.1.symm.trans h1.1))))
    (wstoreX_IR exe endPc L G SR P Z X hseg cw bufL nB mB cT cS (fun w => ⟨cS w, cwv w⟩) hZ hZW hcT hcTin hcTfoot
      hcSfrz hSpos hfootLab hmainLive)
    (fun w t t' s s' s0 p h hw a b c d e hW =>
      ⟨X64HelloWorkerRR.krh_permit w t t' s s' s0 p h.1 a b c d (by simp only [SrcSem.traceOf, e]),
        X64HelloKRE.lk_wr0 (by rw [a]; exact hw) hW⟩)

end IRX

/-- info: 'Spike.Lib.X64HelloW1Store.wcompat_relW_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wcompat_relW_IR


end Spike.Lib.X64HelloW1Store

/-- info: 'Spike.Lib.X64HelloW1Store.wstoreX_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1Store.wstoreX_IR

/-
**The store phase's pc facts from the worker segment's control fact**
(C4, relation half, check-in 5; the bridge in `Spike/Lib/HelloW1Store.lean`,
`Spike/Lib/HelloW1StoreC.lean`; the worker side `HelloWorkerRR.helloDR`):
the bridge's `NoWrite` and `WStoreX.noAbW` from one premise on the control
fact `Z` of the worker's segment (`helloDR`'s `hseg`).

- `ZStoreOk exe Z`: at a pair of `Z w` on no frame, at a store-phase control
  with no hold, the state is outside the abort-write phase `AbW exe` and at
  no `write(1, …)` system call. The worker's store-phase pcs (`stlr`,
  `swpal`, `exit`'s `svc`) are none of `scc_rt_abort_write`'s labels and
  issue no `write`; the concrete `Z` pairs them with the store-phase terms.
- `noWrite_of_Z`, `noAbW_of_Z`: any worker side whose invariant holds `Z`
  up to a pending frame run (`Pend`) has `NoWrite` and `noAbW` under
  `ZStoreOk` (a store-phase control on no frame has no frame run).
- `noWrite_IR`, `noAbW_IR`: so at `helloDR` (`helloDR_inv`).
- `mpW1_H`, `noProm1_H`: `WStoreX.mpW` and `noProm` (the worker's, thread
  `1`) at hello's memory side `HelloMs.msH` and location data `helloP`.
-/
import Spike.Lib.HelloW1StoreC
import Spike.Lib.HelloWorkerRR
import Spike.Lib.HelloMs

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
open Spike.Lib.A64.Rt (RuntimeLayout)

/-! ## The premise on the control fact -/

/-- **The store phase's pc facts, on the segment's control fact `Z`**
(discharged at the concrete `Z`): at a pair of `Z w` on no
frame, at a store-phase control with no hold, the state is outside the
abort-write phase and at no `write(1, …)` system call. -/
def ZStoreOk {ι : Type} (exe : _root_.Executable) (Z : ι → FragS isaLSE2) : Prop :=
  ∀ w s c, Z w s c [] → c.hold = none → StoreT c.term →
    ¬ AbW exe s ∧ ∀ buf n, abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)

section Generic

variable {ι : Type} {exe : _root_.Executable} {Z : ι → FragS isaLSE2} {D : WSideH ι}

/-- At a store-phase pair of `WiS`, `Z` holds on no frame (its pending frame
run is empty). -/
theorem z_of_wiS (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0)
    (hinv : ∀ w s c fs, D.Wi w s c fs → Pend helloSrc (Z w) s c fs) {w : ι} {s : isaLSE2.State} {c : Ctl}
    (h : WiS D w s c) : Z w s c [] := by
  obtain ⟨cS, hcS⟩ := hcw w
  obtain ⟨hW, -, hS, hE⟩ := h
  obtain ⟨c', fs', hr, hz⟩ := hinv w s c [] hW
  have := frameRun_storeT_eq hr hS hE hcS
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  exact hz

/-- **`NoWrite` from `ZStoreOk`.** -/
theorem noWrite_of_Z (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hK : ∀ w, (D.ms w []).K = some abi)
    (hinv : ∀ w s c fs, D.Wi w s c fs → Pend helloSrc (Z w) s c fs) (hZ : ZStoreOk exe Z) : NoWrite D := by
  intro w s c h K buf n hK' ha
  rw [hK w] at hK'
  cases hK'
  exact (hZ w s c (z_of_wiS hcw hinv h) h.2.1 h.2.2.1).2 buf n ha

/-- **`WStoreX.noAbW` from `ZStoreOk`.** -/
theorem noAbW_of_Z (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0)
    (hinv : ∀ w s c fs, D.Wi w s c fs → Pend helloSrc (Z w) s c fs) (hZ : ZStoreOk exe Z) :
    ∀ w s c, WiS D w s c → ¬ AbW exe s :=
  fun w s c h => (hZ w s c (z_of_wiS hcw hinv h) h.2.1 h.2.2.1).1

end Generic

/-! ## At `helloDR` -/

section IR

variable {ι : Type} (exe : _root_.Executable) (endPc : Int64) (SR : ι → SpawnRec)
  (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → List TermRun.Frame → MemSide isaLSE2)
  (P Z X : ι → FragS isaLSE2) (hK : ∀ w fs, (ms w fs).K = some abi)
  (hseg : ∀ w, SegTCSX (fun s c fs => NNH exe endPc s ∧ Z w s c fs) (X w) helloSrc (lbl w) (ms w) (P w)
    (fun _ _ _ => False))
  (cw : ι → TermRun.Word) (bufL : ι → WeakMem.AllocLabel) (nB mB : ι → Nat)

/-- **`NoWrite` at `helloDR`**, from `ZStoreOk` at its segment's `Z`. -/
theorem noWrite_IR (hcw : ∀ w, ∃ cS, (cw w).val = .loc cS 0) (hZ : ZStoreOk exe Z) :
    NoWrite (HelloWorkerRR.helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) :=
  noWrite_of_Z hcw (fun w => hK w [])
    (fun w s c fs h => (HelloWorkerRR.helloDR_inv exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).2.2) hZ

/-- **`WStoreX.noAbW` at `helloDR`**, from `ZStoreOk` at its segment's
`Z`. -/
theorem noAbW_IR (hcw : ∀ w, ∃ cS, (cw w).val = .loc cS 0) (hZ : ZStoreOk exe Z) :
    ∀ w s c, WiS (HelloWorkerRR.helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) w s c → ¬ AbW exe s :=
  noAbW_of_Z hcw
    (fun w s c fs h => (HelloWorkerRR.helloDR_inv exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).2.2) hZ

end IR

/-! ## The worker's memory-side facts at `msH` -/

section Ms

variable {ι : Type} (L : RuntimeLayout) (G : ι → Loc → Val → Prop) (SR : ι → SpawnRec)

/-- **`WStoreX.mpW` at `msH`, `helloP`** (thread `1`'s footprint: as
`HelloMs.mpW_H`'s thread `0`). -/
theorem mpW1_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w Lc, (msH L G SR w).mp Lc true →
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).foot 1 Lc ∧
        ¬ InLabel (SR w).lbl (SR w).lsize Lc ∧ Consumer1.LocIn L.Λ.shared Lc :=
  fun _ _ h => ⟨.inr (.inl ⟨h.1, h.2⟩), (h.2 rfl).2, (h.2 rfl).1⟩

/-- **`WStoreX.noProm` at `helloP`** (thread `1`). -/
theorem noProm1_H {μ : Marks} (cT : ι → Loc) (cS : ι → WeakMem.Address) :
    ∀ w x (t : Thread isaLSE2) mem,
      (helloP abi μ (helloLocs L (SR w).lbl (SR w).lsize (cT w) (cS w))).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 1) 1 t mem → t.prom = [] :=
  fun _ _ _ _ hn hc => WakeP.noProm_prom hn hc

end Ms

/-- info: 'Spike.Lib.HelloW1Store.noWrite_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noWrite_IR

/-- info: 'Spike.Lib.HelloW1Store.noAbW_IR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms noAbW_IR

end Spike.Lib.HelloW1Store

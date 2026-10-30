import Spike.Test.WakeLinkedA64A1
import Spike.Test.WakeLinkedA64A2
import Spike.Test.WakeLinkedA64A4
import Spike.Test.WakeLinkedA64A6
import Spike.Test.WakeLinkedA64A8
import Spike.Lib.WakeFinalCAW

/-!
# `wake.w` on AArch64 at the linked executable's layout `Λe`

The root statement `WakeFinalCAW.wake_finalCA_genWP` instantiated at the
layout `Λe` of `wake.w`'s `ld.lld` executable (`WakeLinkedA64Elf`: path, SHA,
`Λe`), with the root's immediate table `i := WakeFinalCAW.iW Λe`, the dummy
heap word as `cT` and the data's constant ranges.

Decided at `Λe` (each by `decide +kernel`, or from a library fact):

* `placeW_e`: `PlaceW placeCfg Λe outLit` from A1, A2, A4, A6, A8
  (`WakeLinkedA64A1` … `A8`, one module each);
* `hlo` (`.text` at `WakePh.lo = 0x210550`), `hstat`, `hnz` (`NtZ`);
* at `Le := ofPlaceW placeW_e (iW Λe)`: `hpin2`, `hinit2`, `hsub1`, and
  `hwide` (`WakeW1.WorkerSide.wake_exeWide`, `outLit.prog = wakeProg`);
* `hc` (`WakeFinalCAO.ctrZ_cert`).

`wake_linked` is `CorrectE 2` at `Le.Λ` for every budget with the
certificate's heap cells, from the loader check `hP` (the trust boundary,
also checked by evaluation below) and the open per-entry premises `OpenW`.
-/

namespace Spike.Test.WakeLinkedA64

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open SccCertificate (asm outLit placeCfg)
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Rt (RuntimeLayout)

/-- **`PlaceW` at the executable's layout** (A1, A2, A4, A6, A8). -/
theorem placeW_e : PlaceW placeCfg Λe outLit := ⟨wake_a1, wake_a2, wake_a4, wake_a6, wake_a8⟩

/-- The root's immediate table at `Λe`. -/
noncomputable abbrev ie : CoreTerm.Expr → String → Nat → Option Nat := WakeFinalCAW.iW Λe

/-- The placed runtime layout at `Λe`. -/
noncomputable abbrev Le : RuntimeLayout := RuntimeLayout.ofPlaceW placeW_e ie

/-- `.text` at `WakePh.lo`. -/
theorem hlo : Λe.code.lo = Spike.Lib.A64.WakePh.lo := by decide +kernel

/-- No static words. -/
theorem hstat : Λe.static = fun _ => none := rfl

/-- `scc_rt_nthreads` starts at `0`. -/
theorem hnz : WakeOInit.NtZ Λe outLit = true := by decide +kernel

/-- The first TCB's 168 bytes fit the pinned region. -/
theorem hpin2 : Le.pinA.toNat + 168 ≤ Le.Λ.pinned.lo + Le.Λ.pinned.size := by decide +kernel

/-- The second TCB's limit word starts at `0`. -/
theorem hinit2 : (Spike.Lib.A64.PhRec.m0Of Le.Λ outLit.prog outLit.secs).initVal
    ⟨Spike.Lib.WakeGOf2.lim2A Le, 8⟩ = 0 := by decide +kernel

/-- The child's stack range lies in the stack pool. -/
theorem hsub1 : (WakeOSide.r1W placeW_e ie).Sub Le.Λ.stackPool := by
  -- the kernel does not reduce the executable's label lookup: through `lab_stacks`
  have h := Le.lab_stacks
  unfold Scc.Sem.Range.Sub WakeOSide.r1W Spike.Lib.A64.Rt.PreChild.r1Of RuntimeLayout.lab
  rw [h]
  decide +kernel

/-- The executable is in the wide fragment. -/
theorem hwide : Scc.Cert.WideA64.ExeWide Le.exe := by
  show Scc.Cert.WideA64.ExeWide (Scc.Sem.A64.threadAt Scc.Sem.Entry.linux _ outLit.prog _).exe
  rw [WakeSpawnRP.outLit_prog]
  exact WakeW1.WorkerSide.wake_exeWide _ _ _

-- The loader check holds (evaluation; `wake_linked` takes it as `hP`).
#guard Scc.Cert.Link.A64.parsesTo asm outLit.prog outLit.secs

/-- **wake.w's AArch64 statement at the linked executable's layout**: the
root at `Λe`, every layout instance fact decided; open the loader check `hP`
and the per-entry premises `OpenW`. -/
theorem wake_linked {arch : WeakMem.Arch} {B : Budget}
    (ls0 : Entry → Lsize) (Ctx : Entry → FragS isaLSE2)
    (frM : Entry → TermRun.Frame) (inv0 : Entry → FragS isaLSE2)
    (inv1 : Entry → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2)
    (hP : Scc.Cert.Link.A64.parsesTo asm outLit.prog outLit.secs = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hO : ∀ E : Entry, E.Ok Le.Λ → WakeFinalCAW.OpenW placeW_e ie (fun _ => WakeHG.cTW placeW_e ie) ls0 Ctx frM inv0 inv1 arch
      (WakeAssemblyR.MR placeW_e ie (WakeSpawnRP.parsed_outLit hP).1)
      (fun _ => WakeOSide.r0W placeW_e ie) (fun _ => WakeOSide.r1W placeW_e ie) E) :
    CorrectE 2 (wakeS arch) Le.Λ B asm :=
  WakeFinalCAW.wake_finalCA_genWP (hp := placeW_e) (i := ie) (cT := fun _ => WakeHG.cTW placeW_e ie)
    (ls0 := ls0) (Ctx := Ctx) (frM := frM) (inv0 := inv0) (inv1 := inv1) hP hlo hstat hpin2 hinit2 hwide hsub1
    WakeFinalCAO.ctrZ_cert hnz hB hO (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

end Spike.Test.WakeLinkedA64

/-- info: 'Spike.Test.WakeLinkedA64.wake_linked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedA64.wake_linked

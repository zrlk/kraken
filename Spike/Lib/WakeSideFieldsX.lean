/-
**The worker side's fields of `WCompat`, from segments keeping `wakeZX`**
(AArch64): `WakeSideFields.sideF_of` at the extended
fragment `ZX.wakeZX` (`Spike/Lib/A64WakeZX.lean`; `seg_childPreNNA` with
`ZX.childThrZA_X` and `ZX.cZA_X`), alongside the `wakeZE` one, which stays
as it was. `hZ` is `wakeZX`'s `wakeZE` conjunct's first half. The listing is
wake.w's certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `sideF_ofX`: `SideF` at `D := side lbl ms P hK h cw S`, `h` keeping
  `wakeZX`.
- `sideF_ofXv`: the same with the pointer words given by their values
  only (`(cw w).val`; the spawned kid's words are bumped, not `cst`).
- `side_hhalt1X`: `WakeAssembly`'s `hhalt1` at that side.
- `side_hmapWX`: `WakeAssembly`'s `hmapW` at that side (`WakeMappedRow.hW_of`
  with `WakeLabMapped.labMapped_flagB` from `wakeZX`'s flag pointer).
-/
import Spike.Lib.WakeSideFields
import Spike.Lib.A64WakeZX
import Spike.Lib.WakeLabMapped

namespace Spike.Lib.WakeW1.WorkerSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64.Flow.Worker (NN NNZ)
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **the fields at the worker's side** of segments keeping `wakeZX`. -/
theorem sideF_ofX {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q : WakeRel} {μ : Scc.Sem.Marks} {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat}
    {cS : WeakMem.Address}
    {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isaLSE2} {P : Q.ι → Frag isaLSE2}
    {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc (wakeZX Λ lbl' cS exe kp)) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    (hl : ∀ w, lbl w = (Q.SR w).lbl) (hc : ∀ w, cw w = TermRun.cst (.loc (Q.C w).cS 0))
    (hS : ∀ w, S w = (Q.SR w).S) :
    SideF Q (side lbl ms P hK h cw S) μ where
  lbl := side_lbl hl
  K := side_K
  wide := wide_of side_nnw
  noSite := noSite_of side_nnw hp hend hμ
  sysExec := sysExec_of side_nnw
  sysOk := sysOk_of side_nnw
  cwv := side_cwv hc
  S := side_S hS
  hZ w s c hw := (side_z w s c hw).1.1

/-- info: 'Spike.Lib.WakeW1.WorkerSide.sideF_ofX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sideF_ofX

/-- **the fields at the worker's side** of segments keeping `wakeZX`,
the pointer words by their values (`hc`). -/
theorem sideF_ofXv {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q : WakeRel} {μ : Scc.Sem.Marks} {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat}
    {cS : WeakMem.Address}
    {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isaLSE2} {P : Q.ι → Frag isaLSE2}
    {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc (wakeZX Λ lbl' cS exe kp)) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    (hl : ∀ w, lbl w = (Q.SR w).lbl) (hc : ∀ w, (cw w).val = .loc (Q.C w).cS 0)
    (hS : ∀ w, S w = (Q.SR w).S) :
    SideF Q (side lbl ms P hK h cw S) μ where
  lbl := side_lbl hl
  K := side_K
  wide := wide_of side_nnw
  noSite := noSite_of side_nnw hp hend hμ
  sysExec := sysExec_of side_nnw
  sysOk := sysOk_of side_nnw
  cwv := hc
  S := side_S hS
  hZ w s c hw := (side_z w s c hw).1.1

/-- info: 'Spike.Lib.WakeW1.WorkerSide.sideF_ofXv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sideF_ofXv

/-- **`hhalt1` at the side** of segments keeping `wakeZX`. -/
theorem side_hhalt1X {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    {ι : Type} {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → MemSide isaLSE2} {P : ι → Frag isaLSE2}
    {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc (wakeZX Λ lbl' cS exe kp)) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : ι → TermRun.Word} {S : ι → Nat} (hend : endPc = endOf exe wakeProg kp) :
    ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → Scc.Sem.A64.abi.atSys s = true → (isaLSE2.exec s).isSome :=
  Spike.Lib.A64.Flow.Worker.Wake.ZX.hhalt1_ofX hend (cOf := id) fun w s c hw => (side_inv w s c hw).1

/-- **`hmapW` at the side** of segments keeping `wakeZX` (flag `cS`): the
memory sides' `mp` mapped in `K0 Λ0` (`hmp`), `cS`'s label placed at `b`
under every `lbl w` (`hl`), its word `cT` shared (`hT`, `hsh`). -/
theorem side_hmapWX {exe : _root_.Executable} {endPc : Int64} {kp : Nat}
    {Λ Λ0 : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    {ι : Type} {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → MemSide isaLSE2} {P : ι → Frag isaLSE2}
    {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc (wakeZX Λ lbl' cS exe kp)) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : ι → TermRun.Word} {S : ι → Nat} {cT : Loc} {b : Nat}
    (hmp : ∀ w L wr, (ms w).mp L wr → Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ0) wr L = true)
    (hl : ∀ w, lbl w cS.label = some b) (hT : cT = Scc.Sem.wordLoc (b + 8 * cS.offset))
    (hsh : Spike.Lib.Consumer1.LocIn Λ0.shared cT) :
    ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → Scc.Sem.A64.abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Scc.Sem.Kernel.Touches (fun l w => Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ0) w l = false) e :=
  Spike.Lib.WakeMappedRow.hW_of side_K hmp fun w s c hw =>
    Spike.Lib.WakeLabMapped.labMapped_flagB (Spike.Lib.A64.Flow.Worker.Wake.ZX.labPtr (side_z w s c hw))
      (hl w) hT hsh

end Spike.Lib.WakeW1.WorkerSide

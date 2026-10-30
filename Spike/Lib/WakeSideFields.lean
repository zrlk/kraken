/-
**The worker side's fields of `WCompat`, at once** (AArch64): the worker side's fields of `Spike.Lib.WakeW1.WCompat`, as
`WakeAssembly.wCompat_of` takes them (`lbl`, `K`, `wide`,
`noSite`, `sysExec`, `sysOk`, `cwv`, `S`, and `pass`'s `hZ`), bundled
(`SideF`) and proved for the worker's side `WorkerSide.side` of a family of
child segments keeping `Z := EndOff.wakeZE exe kp` (`wakePass` and off the
program's end; `sideF_of`). The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `SideF Q D μ`: the fields, each with the type of `wCompat_of`'s
  hypothesis of the same name.
- `sideF_of`: at `D := side lbl ms P hK h cw S` (`h` keeping `wakeZE`,
  `seg_childPreNN` with `EndOff.childThrZE` and `EndOff.cZE`; `hZ` is its
  first half), given the placements (`hl`), the
  pointer words (`hc`), the sizes (`hS`), the loaded layout and the marks'
  link to its labels (`hp`, `hend`, `hμ`; `wake_hμ` for the canonical
  target).
- `side_hhalt1`: `WakeAssembly`'s `hhalt1` at the side (`EndOff.hhalt1_of`).

`pass`'s other premise, `hpT : ∀ w, (Q.C w).passT = wakePassT`, is the flag
records' data, not the side's.
-/
import Spike.Lib.WakeWorkerSide
import Spike.Lib.A64WakeEndOff

namespace Spike.Lib.WakeW1.WorkerSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64.Flow.Worker (NN NNZ)
open Spike.Lib.A64.Flow.Worker.Wake.Pass (wakePass wakePassT)
open Spike.Lib.A64.Flow.Worker.Wake.EndOff (wakeZE)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)

/-- **the fields of `WCompat`** for the side `D` at marks `μ`, each with
the type of `WakeAssembly.wCompat_of`'s hypothesis of the same name. -/
structure SideF (Q : WakeRel) (D : WSide Q.ι) (μ : Scc.Sem.Marks) : Prop where
  lbl : ∀ w, D.lbl w = (Q.SR w).lbl
  K : ∀ w, (D.ms w).K = some Scc.Sem.A64.abi
  wide : ∀ w s c, D.Wi w s c → Scc.Cert.WideA64.WideSt s
  noSite : ∀ w s c, D.Wi w s c → Scc.Sem.Kernel.siteAt Scc.Sem.A64.abi μ s = none
  sysExec : ∀ w s c t, D.Wi w s c → Scc.Sem.A64.abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m
  sysOk : ∀ w s c call, D.Wi w s c → Scc.Sem.A64.abi.atSys s = true →
    Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) = some call →
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v)
  cwv : ∀ w, (D.cw w).val = .loc (Q.C w).cS 0
  S : ∀ w, D.S w = (Q.SR w).S
  hZ : ∀ w s c, D.Wi w s c → wakePass s c

/-- **the fields at the worker's side** of segments keeping `wakeZE`. -/
theorem sideF_of {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {Q : WakeRel} {μ : Scc.Sem.Marks}
    {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isaLSE2} {P : Q.ι → Frag isaLSE2}
    {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc (wakeZE exe kp)) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
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
  hZ w s c hw := (side_z w s c hw).1

/-- info: 'Spike.Lib.WakeW1.WorkerSide.sideF_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sideF_of

/-- **`hhalt1` at the side** of segments keeping `wakeZE`: at a system call
the worker's instruction runs. -/
theorem side_hhalt1 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    {ι : Type} {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → MemSide isaLSE2} {P : ι → Frag isaLSE2}
    {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc (wakeZE exe kp)) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : ι → TermRun.Word} {S : ι → Nat} (hend : endPc = endOf exe wakeProg kp) :
    ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → Scc.Sem.A64.abi.atSys s = true → (isaLSE2.exec s).isSome :=
  Spike.Lib.A64.Flow.Worker.Wake.EndOff.hhalt1_of hend (cOf := id) fun w s c hw => (side_inv w s c hw).1

end Spike.Lib.WakeW1.WorkerSide

/-
**hello.w on x86-64: a state off the `nop`s is off the transfer sites** (`WCompat.noSite`, `WCompatH.noSite`;
the twin of `Spike/Lib/A64HelloSites.lean` and `Spike/Lib/A64HelloSitesH.lean`). The kernel's transfer sites
are the labels `scc_rt_take_site` and `scc_rt_release_site` (`Scc.Lower.Names`), each a `nop` in hello's
listing (`SccCode.helloCells`, decided by `decide +kernel` on `blockAt`). So in any valid layout `exe` of the
listing, a state `NN exe endPc` or `NNP Sy exe endPc` (at a cell other than a `nop`; the system call's
condition plays no part) is at neither label.

The link from the labels to the loaded program's marks `μ` is the instantiation's (`hμ`).

- `nopB`, `hello_sites`: both sites are a `nop` in `helloCells`.
- `nn_ne_nop`, `nn_ne_site`, `siteAt_none_of_nn`: at `NN` (wake's worker condition).
- `nnP_ne_nop`, `nnP_ne_site`, `siteAt_none_of_nnP`: at `NNP Sy` (so at `NNH`, hello's worker side).

Unlike AArch64, the `nop` is the one-byte `op64 (.nop _)` cell, decided over the byte-sized cells
`helloCells` (AArch64: `SI.nop.toDir` over `helloProg`), closed by `codeAt_blockAt_lays` and
`Scc.Sem.X64.atNop_of_cellAt` (as `Spike/Lib/X64WakeSites.lean`); the `NN` and `NNP` forms share one module.
-/
import Spike.Lib.X64HelloNN
import Spike.Lib.X64HelloCode
import Scc.Lower.Term

namespace Spike.Lib.X64.HelloSites

open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)
open Spike.Lib.X64.Flow.Worker (NN NNP)

/-- `nop`, one byte. -/
def nopB : List (Directive × Nat) := (parse("nop")).zip [1]

/-- **Both transfer sites are a `nop`** in hello's listing. -/
theorem hello_sites : blockAt SccCode.helloCells Scc.Lower.Names.takeSite 0 0 nopB = true ∧
    blockAt SccCode.helloCells Scc.Lower.Names.releaseSite 0 0 nopB = true := by decide +kernel

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {Sy : Scc.Sem.Kernel.Call → Prop}

/-- A label whose block is a `nop` is not the pc of an `NNP Sy` state. -/
theorem nnP_ne_nop {l : Label} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) (hb : blockAt SccCode.helloCells l 0 0 nopB = true)
    {s : State} (h : NNP Sy exe endPc s) : s.st.2 ≠ (_root_.Executable.labels exe).label l := by
  intro hpc
  obtain ⟨he, hn, hnop, -⟩ := h
  have hc := codeAt_blockAt_lays hp he (hn.trans hend) hb
  have hcell := hc.cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])
  rw [Scc.Sem.X64.atNop_of_cellAt hcell] at hnop
  exact Bool.noConfusion hnop

/-- **An `NNP Sy` state's pc is neither transfer site's label.** -/
theorem nnP_ne_site (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {s : State} (h : NNP Sy exe endPc s) :
    s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.takeSite ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite :=
  ⟨nnP_ne_nop hp hend hello_sites.1 h, nnP_ne_nop hp hend hello_sites.2 h⟩

/-- **An `NNP Sy` state is at no transfer site** of marks `μ` whose sites are the two labels' addresses
(`hμ`, the instantiation's link). -/
theorem siteAt_none_of_nnP {μ : Scc.Sem.Marks} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    {s : State} (h : NNP Sy exe endPc s) : Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi μ s = none := by
  obtain ⟨ht, hr⟩ := nnP_ne_site hp hend h
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨?_, ?_⟩
  · rw [hμ.1]; intro he
    exact ht (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))
  · rw [hμ.2]; intro he
    exact hr (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))

/-- A label whose block is a `nop` is not the pc of an `NN` state. -/
theorem nn_ne_nop {l : Label} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) (hb : blockAt SccCode.helloCells l 0 0 nopB = true)
    {s : State} (h : NN exe endPc s) : s.st.2 ≠ (_root_.Executable.labels exe).label l := by
  intro hpc
  obtain ⟨he, hn, hnop, -⟩ := h
  have hc := codeAt_blockAt_lays hp he (hn.trans hend) hb
  have hcell := hc.cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])
  rw [Scc.Sem.X64.atNop_of_cellAt hcell] at hnop
  exact Bool.noConfusion hnop

/-- **An `NN` state's pc is neither transfer site's label.** -/
theorem nn_ne_site (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {s : State} (h : NN exe endPc s) :
    s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.takeSite ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite :=
  ⟨nn_ne_nop hp hend hello_sites.1 h, nn_ne_nop hp hend hello_sites.2 h⟩

/-- **An `NN` state is at no transfer site** of marks `μ` whose sites are the two labels' addresses. -/
theorem siteAt_none_of_nn {μ : Scc.Sem.Marks} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    {s : State} (h : NN exe endPc s) : Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi μ s = none := by
  obtain ⟨ht, hr⟩ := nn_ne_site hp hend h
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨?_, ?_⟩
  · rw [hμ.1]; intro he
    exact ht (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))
  · rw [hμ.2]; intro he
    exact hr (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))

end Spike.Lib.X64.HelloSites

/--
info: 'Spike.Lib.X64.HelloSites.siteAt_none_of_nnP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloSites.siteAt_none_of_nnP

/--
info: 'Spike.Lib.X64.HelloSites.siteAt_none_of_nn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloSites.siteAt_none_of_nn

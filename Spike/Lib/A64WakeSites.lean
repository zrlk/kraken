/-
**wake.w on AArch64: a state off the `nop`s is off the transfer sites**
(`WCompat.noSite`). The kernel's transfer sites are the
labels `scc_rt_take_site` and `scc_rt_release_site` (`Scc.Lower.Names`),
each a `nop` in the certificate's listing (`wakeProg`;
decided by `decide +kernel` on `blockAt`). In any valid layout `exe` laying
the program out, a state `NN exe endPc` (at a cell other than a `nop`) is at
neither label.

The link from the labels to the loaded program's marks `μ` (`μ.site k` is
the label's address: `Scc.Sem.A64.resolve_of_parsed`, as `ret0_marks`) is
the instantiation's (`hμ` of `siteAt_none_of_nn`).

- `wake_sites`: both sites are a `nop` in `wakeProg`.
- `nn_ne_site`: an `NN` state's pc is neither site's label.
- `siteAt_none_of_nn`: at marks whose sites are the labels' addresses, an
  `NN` state is at no transfer site (`Kernel.siteAt abi μ s = none`).
-/
import Spike.Lib.A64WakeNN
import Spike.Lib.A64WakeLabels
import Scc.Lower.Term

namespace Spike.Lib.A64.Flow.Worker

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt codeAt_blockAt)
open Spike.Lib.A64.WakeLabels (wakeProg)

/-- **Both transfer sites are a `nop`** in wake's listing. -/
theorem wake_sites : blockAt wakeProg Scc.Lower.Names.takeSite 0 [SI.nop.toDir] = true ∧
    blockAt wakeProg Scc.Lower.Names.releaseSite 0 [SI.nop.toDir] = true := by decide +kernel

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- A label whose block is a `nop` is not the pc of an `NN` state. -/
theorem nn_ne_nop {l : Label} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hb : blockAt wakeProg l 0 [SI.nop.toDir] = true) {s : State} (h : NN exe endPc s) :
    s.st.2 ≠ (_root_.Executable.labels exe).label l := by
  intro hpc
  obtain ⟨he, hn, hnop, -⟩ := h
  have hc := codeAt_blockAt hp he (hn.trans hend) hb
  have hcell : CellAt s SI.nop.toDir 4 := hc.cell (j := 0) rfl rfl rfl (by rw [hpc, ofNat4_zero, ofNat4_zero])
  rw [Scc.Sem.A64.atNop_of_cellAt hcell] at hnop
  exact Bool.noConfusion hnop

/-- **An `NN` state's pc is neither transfer site's label.** -/
theorem nn_ne_site (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {s : State}
    (h : NN exe endPc s) :
    s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.takeSite ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite :=
  ⟨nn_ne_nop hp hend wake_sites.1 h, nn_ne_nop hp hend wake_sites.2 h⟩

/-- **An `NN` state is at no transfer site** of marks `μ` whose sites are
the two labels' addresses (`hμ`, the instantiation's link). -/
theorem siteAt_none_of_nn {μ : Scc.Sem.Marks} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    {s : State} (h : NN exe endPc s) : Scc.Sem.Kernel.siteAt Scc.Sem.A64.abi μ s = none := by
  obtain ⟨ht, hr⟩ := nn_ne_site hp hend h
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨?_, ?_⟩
  · rw [hμ.1]; intro he
    exact ht (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))
  · rw [hμ.2]; intro he
    exact hr (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))

end Spike.Lib.A64.Flow.Worker

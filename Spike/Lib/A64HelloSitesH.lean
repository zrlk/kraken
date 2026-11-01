/-
**hello.w on AArch64: a state off the `nop`s is off the transfer sites, any
system-call condition** (`WCompatH.noSite`): the
restatement of `Spike/Lib/A64HelloSites.lean`'s `nn_ne_site` and
`siteAt_none_of_nn` over `NNP Sy` (`Spike/Lib/A64HelloNN.lean`; the system
call's condition plays no part), so at `NNH`, the worker side's states.

- `nnP_ne_nop`, `nnP_ne_site`, `siteAt_none_of_nnP`: `Sites`' lemmas at
  `NNP Sy`.
-/
import Spike.Lib.A64HelloSites
import Spike.Lib.A64HelloNN

namespace Spike.Lib.A64.Flow.Worker.Hello.Sites

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt codeAt_blockAt)
open SccCode (helloProg)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {Sy : Scc.Sem.Kernel.Call → Prop}

/-- A label whose block is a `nop` is not the pc of an `NNP Sy` state. -/
theorem nnP_ne_nop {l : Label} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hb : blockAt helloProg l 0 [SI.nop.toDir] = true) {s : State} (h : NNP Sy exe endPc s) :
    s.st.2 ≠ (_root_.Executable.labels exe).label l := by
  intro hpc
  obtain ⟨he, hn, hnop, -⟩ := h
  have hc := codeAt_blockAt hp he (hn.trans hend) hb
  have hcell : CellAt s SI.nop.toDir 4 := hc.cell (j := 0) rfl rfl rfl (by rw [hpc, ofNat4_zero, ofNat4_zero])
  rw [Scc.Sem.A64.atNop_of_cellAt hcell] at hnop
  exact Bool.noConfusion hnop

/-- **An `NNP Sy` state's pc is neither transfer site's label.** -/
theorem nnP_ne_site (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {s : State}
    (h : NNP Sy exe endPc s) :
    s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.takeSite ∧
      s.st.2 ≠ (_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite :=
  ⟨nnP_ne_nop hp hend hello_sites.1 h, nnP_ne_nop hp hend hello_sites.2 h⟩

/-- **An `NNP Sy` state is at no transfer site** of marks `μ` whose sites
are the two labels' addresses (`siteAt_none_of_nn`'s `hμ`). -/
theorem siteAt_none_of_nnP {μ : Scc.Sem.Marks} (hp : Lays exe helloProg kp)
    (hend : endPc = endOf exe helloProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat)
    {s : State} (h : NNP Sy exe endPc s) : Scc.Sem.Kernel.siteAt Scc.Sem.A64.abi μ s = none := by
  obtain ⟨ht, hr⟩ := nnP_ne_site hp hend h
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨?_, ?_⟩
  · rw [hμ.1]; intro he
    exact ht (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))
  · rw [hμ.2]; intro he
    exact hr (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (Option.some.inj he).symm))

end Spike.Lib.A64.Flow.Worker.Hello.Sites

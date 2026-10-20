/-
**The public statement of message passing** (AArch64, `MpTrees.mpWriter`,
`MpTrees.mpReader`): a wrapper of `Mp.mp_armv8` (`SLR/MpAdequacy.lean`) whose
hypotheses mention only the two layouts, the flag and data addresses `f`,
`d`, the two thread states and the flag's initial value.

- The writer's ghost token `W` of `Params` is chosen here: `⟨0, 5⟩` (never
  4 bytes wide, so distinct from both words). It occurs neither in the
  program's accesses nor in the conclusion.
- The data word's initial value is not needed: the data load can only read
  the writer's store (the conclusion holds whatever the initial data is).
- The thread-state hypotheses are `StartW f d`, `StartR f d`: `FrameW` /
  `FrameR` and position `0`, without the ghost parameter.
- Two layouts: a `Layout` assigns sizes by directive index and the two
  programs have their labels at different indices, so no single `Layout` is
  `ValidLayout` for both (`SLR/MpPure.lean`).

`mp_concrete'` re-derives `MpConcrete.mp_concrete` through the wrapper.

`StartW`, `StartR`, `ghostParams` and their lemmas are in `SLR/MpSpec.lean`
(moved unchanged, so that the EnvG route need not import this
file).
-/
import Kraken.Promising.SLR.MpConcrete
import Kraken.Promising.SLR.MpSpec

namespace Kraken.Promising.SLR.MpPublic

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees
open Kraken.Promising.SLR.Mp

/-- **Message passing for AArch64 under `Arch.armv8`**, public form.

For valid layouts `lW` of `mpWriter` and `lR` of `mpReader` and addresses
`f ≠ d`: if thread `0` is the writer and thread `1` the reader, each at its
start with `X0 = f`, `X1 = d` (`StartW`, `StartR`), and the initial memory
has the flag word `⟨f, 4⟩` at `0` (an absent entry counts as `0`), then every
configuration `Reachable` under `Arch.armv8` that is final has the reader's
`W4` at `1` and the data word `⟨d, 4⟩` at `1`.

What is and is not covered:
- The locations are the undeclared 4-byte footprints `⟨f, 4⟩`, `⟨d, 4⟩`
  (`decls = {}`).
- `f ≠ d` does not exclude overlapping words (e.g. `f = d + 2`). The model
  treats distinct `Loc`s as independent, so the conclusion is only
  meaningful for disjoint words.
- Conclusions are about final configurations only (every thread halted, no
  outstanding promise). Runs in which the reader spins forever never become
  final and are not constrained; no fairness is assumed. A faulting step has
  no successor, so a run that faults never becomes final.
- Faults: faults are not covered by this theorem. What exists:
  `NoFaultRule` is proved for both rules (`mpRuleW_noFault`,
  `mpRuleR_noFault`, `SLR/MpNoFault.lean`); fault-freedom of the whole
  program reduces to the open statement `ErasedWitness`
  (`noFaultTheorem_of_erasedWitness`, `SLR/Sim/CertExtOpen.lean`), which is
  not proved. Unlike the two spinlocks, MP has no explorer fault check
  (no `SLR/MpFaults.lean`). -/
theorem mp_public {fuel : Nat} (lW lR : _root_.Layout) [Executable.ValidLayout (lW mpWriter)]
    [Executable.ValidLayout (lR mpReader)] (f d : BitVec 64) (hfd : f ≠ d)
    {sW sR : isa.State} {initMem : List (Loc × Val)}
    (hW : StartW (layout := lW) f d sW) (hR : StartR (layout := lR) f d sR)
    (hF0 : (Config.init [sW, sR] initMem).mem.initVal ⟨f, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [sW, sR] initMem) cfg)
    (hf : cfg.final = true) :
    (∃ t, cfg.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      cfg.mem.finalVal ⟨d, 4⟩ = 1#128 :=
  mp_armv8 lW lR (ghostParams f d) (ghostParams_mpLocs hfd) (StartW.frame (layout := lW) hW)
    (StartR.frame (layout := lR) hR) hF0 hc hf

/-! ## The concrete instance through the public theorem -/

section Concrete

open Kraken.Promising.SLR.MpConcrete

section
attribute [local instance] wLayout

theorem writer0_start : StartW flagAddr dataAddr writer0 :=
  let h := writer0_frame.1
  ⟨h.exe, h.decls, h.endPc, writer0_frame.2, h.x0, h.x1, h.df, h.dd⟩

end

section
attribute [local instance] rLayout

theorem reader0_start : StartR flagAddr dataAddr reader0 :=
  let h := reader0_frame.1
  ⟨h.exe, h.decls, h.endPc, reader0_frame.2, h.x0, h.x1, h.df, h.dd⟩

end

/-- **Message passing** for the concrete writer and reader, derived from
`mp_public` (the statement of `MpConcrete.mp_concrete`). -/
theorem mp_concrete' {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writer0, reader0] initMemMp) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal Pmp.Dt = 1#128 :=
  mp_public wLayout rLayout flagAddr dataAddr (by decide) writer0_start reader0_start (by decide) hc hf

end Concrete

end Kraken.Promising.SLR.MpPublic

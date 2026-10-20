/-
**Concrete instances of the AArch64 public theorems**: non-vacuity of their
start hypotheses. Each `*_concrete`
corollary fixes layouts (text at `0x100000` / `0x200000`, each directive its
`fakeSize`, as `SLR/MpConcrete.lean`), the flag at `0x1000`, the data at
`0x1100`, the initial memory `[flag ↦ 0, data ↦ 0]`, and start states with
`X0 = flag`, `X1 = data`; every hypothesis is discharged by `decide`, `rfl` or
`simp` (no `native_decide`).

- `takeMp_envG_concrete` (`TakeMp.takeMp_envG`; `StartT`, endPc `addrOf 7`);
- `mp_envG'_concrete` (`MpLink.mp_envG'` (`EnvG/MpEnvGPublic2.lean`); `mp_envG` already has
  `MpEnvGPublic.mp_concrete_envG`);
- `mp_fence_envG_concrete` (`FenceEnvMp.mp_fence_envG`), plus the check that
  `MpFenceConcrete.mp_fence_concrete` is literally an instance of it.
-/
import Kraken.Promising.SLR.EnvG.TakeMpPublic
import Kraken.Promising.SLR.EnvG.MpEnvGPublic2
import Kraken.Promising.SLR.EnvG.FenceEnvMpPublic
import Kraken.Promising.SLR.MpFenceConcrete

namespace Kraken.Promising.SLR.EnvG.ConcreteA64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.MpTrees Kraken.Promising.SLR.Mp
open Kraken.Promising.SLR.MpConcrete
open Kraken.Promising.SLR.EnvG.TakeMp

/-! ## `takeMp_envG` -/

/-- The writing reader's layout: text at `0x200000`, each directive its
`fakeSize`. -/
@[reducible] def tLayout : _root_.Layout := Kraken.Layout.ofSize 0x200000 Directive.fakeSize takeReader

theorem tLayout_cells : ((tLayout takeReader).2.map (·.2)) = [0, 4, 4, 4, 4, 4, 0] := by decide

instance tValid : Executable.ValidLayout (tLayout takeReader) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The writing reader's initial state: `X0 = flag`, `X1 = data`, at
`0x200000` (the label `spin`), halting at the end of its text
(`0x200000 + 20`). -/
def treader0 : AArch64.State where
  exe := tLayout takeReader
  endPc := 0x200000 + 20
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100 } }, 0x200000)

section
attribute [local instance] tLayout

theorem treader0_start : StartT flagAddr dataAddr treader0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, ?_, ?_⟩ <;>
    simp [treader0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ, flagAddr, dataAddr]

end

/-- **Message passing with a writing reader**, concrete instance of
`takeMp_envG`: every reachable final configuration has the reader's `W4` at
`43` and the data word at `43`. -/
theorem takeMp_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writer0, treader0] initMemMp) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal Pmp.Dt = 43#128 :=
  takeMp_envG wLayout tLayout flagAddr dataAddr (by decide) MpPublic.writer0_start treader0_start (by decide) hc hf

/-! ## `mp_envG'` -/

/-- **Message passing on `EnvG` (relPure route)**, concrete instance of
`MpLink.mp_envG'` (`EnvG/MpEnvGPublic2.lean`) (the configuration of `MpConcrete.mp_concrete`). -/
theorem mp_envG'_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writer0, reader0] initMemMp) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal Pmp.Dt = 1#128 :=
  MpLink.mp_envG' wLayout rLayout flagAddr dataAddr (by decide) MpPublic.writer0_start MpPublic.reader0_start
    (by decide) hc hf

/-! ## `mp_fence_envG` -/

open Kraken.Promising.SLR.MpFenceConcrete in
/-- **Message passing with a fence-released writer, on `EnvG`**, concrete
instance of `FenceEnvMp.mp_fence_envG` (the configuration of
`MpFenceConcrete.mp_fence_concrete`). -/
theorem mp_fence_envG_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [fwriter0, reader0] initMemMp) c) (hf : c.final = true) :
    (∃ t, c.threads[1]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 1) ∧
      c.mem.finalVal Pmp.Dt = 1#128 :=
  FenceEnvMp.mp_fence_envG (lW := fLayout) (lR := rLayout) flagAddr dataAddr (by decide) fwriter0_start
    MpPublic.reader0_start (by decide) hc hf

/-- `mp_fence_concrete` and `mp_fence_envG_concrete` have the same statement
(`mp_fence_envG` has `mp_fence`'s type, so the old concrete instance
transfers). -/
example : type_of% @MpFenceConcrete.mp_fence_concrete = type_of% @mp_fence_envG_concrete := rfl

end Kraken.Promising.SLR.EnvG.ConcreteA64

#print axioms Kraken.Promising.SLR.EnvG.ConcreteA64.takeMp_envG_concrete
#print axioms Kraken.Promising.SLR.EnvG.ConcreteA64.mp_envG'_concrete
#print axioms Kraken.Promising.SLR.EnvG.ConcreteA64.mp_fence_envG_concrete

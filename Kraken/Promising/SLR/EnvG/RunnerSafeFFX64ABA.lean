/-
**`treiber_aba_tagged.kl` (x64): runner-exact safety concrete, and safety ∧
program-level fault freedom**. Convenience theorems only.

- `VecABA.x64_treiber_aba_tagged_runner_safe_faultFree`: the x64 vector proofs'
  `x64_treiber_aba_tagged_never` (the `.kl`'s `~exists` clause is
  impossible in every final configuration reachable under `Arch.tso`; its
  rules already carry the threads' declarations) paired with the value-invariant
  fault-freedom proofs'
  `x64_treiber_aba_tagged_runner_faultFree` (`Config.FaultFree`, any
  architecture, promises included), at the union of their hypotheses minus
  three: the stack hypotheses `A ∉ stack₀`, `A, B ∉ stack₁` of the safety
  theorem follow from the fault-freedom side's `Split abaS sᵢ.st.1.dmem`
  (`split_get_none`).
- `VecABA.Concrete.x64_treiber_aba_tagged_runner_concrete`: the safety
  theorem at the value-invariant fault-freedom proofs' runner instance
  (`abaLayoutV`, threads `abaP0V`,
  `abaP1V` with declarations `abaDeclsV`, initial memory `abaInitMemV`;
  `codeMatches`/`runnerMatches` checked in `MemValsX64ABAConcrete.lean`).
  Every hypothesis is discharged by `decide`/`rfl` or the value-invariant
  fault-freedom proofs' lemmas
  (`symV_*`, `abaThreadV_start`, `stk_get_none`).
- `VecABA.Concrete.x64_treiber_aba_tagged_runner_safe_faultFree_concrete`:
  both at that instance.
-/
import Kraken.Promising.SLR.EnvG.MemValsX64ABAConcrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

namespace Kraken.Promising.X64.EnvG.VecABA

/-- A start memory split from `abaS` has no byte at `A` or `B`. -/
theorem split_get_none [_root_.Layout] {m : DataMem} (hs : Split abaS m) :
    m.get? (symV "A") = none ∧ m.get? (symV "B") = none :=
  ⟨hs (symV "A") ⟨symV "A", 8, by simp, by simp⟩, hs (symV "B") ⟨symV "B", 8, by simp, by simp⟩⟩

/-- **`treiber_aba_tagged.kl` with the runner's declarations: the ABA
outcome is impossible, and no step faults.** For every valid layout of the
image in which `head` is 16-aligned and `A`, `B` are distinct and non-null,
both threads with sized declarations `ds` agreeing on `abaS`, thread `0`
from `p0` and thread `1` from `p1` on private stacks split from `abaS`, and
the initial memory `head = {A, 0}`, `A.next = B`, `B.next = 0` (`IV`). -/
theorem x64_treiber_aba_tagged_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout abaImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hal : isAligned 16 (symV "head") = true) (hA : symV "A" ≠ 0) (hB : symV "B" ≠ 0)
    (hAB : symV "A" ≠ symV "B") (hag : ds.AgreesOn abaS)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)} (h0 : StartV ds "p0" s0) (h1 : StartV ds "p1" s1)
    (hs0 : Split abaS s0.st.1.dmem) (hs1 : Split abaS s1.st.1.dmem)
    (hiv : IV abaP (Config.init [s0, s1] initMem).mem) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init [s0, s1] initMem) cfg → cfg.final = true →
      ¬ ∃ t0 t1, cfg.threads[0]? = some t0 ∧ cfg.threads[1]? = some t1 ∧
        t0.st.st.1.regs.get64 .r12 = symV "A" ∧ t0.st.st.1.regs.get64 .r13 = symV "B" ∧
        t1.st.st.1.regs.get64 .r13 = symV "B") ∧
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  ⟨fun _ hc hf => x64_treiber_aba_tagged_never hsz hal hA hB hAB h0 h1 (split_get_none hs0).1
      (split_get_none hs1).1 (split_get_none hs1).2 hiv hc hf,
    x64_treiber_aba_tagged_runner_faultFree hsz hal hag h0 h1 hs0 hs1 hiv⟩

end Kraken.Promising.X64.EnvG.VecABA

namespace Kraken.Promising.X64.EnvG.VecABA.Concrete

open Kraken.Promising.X64.EnvG.VecABA

section
attribute [local instance] abaLayoutV

set_option maxRecDepth 20000

/-- **`treiber_aba_tagged.kl`: the ABA outcome
`0:r12 = A ∧ 0:r13 = B ∧ 1:r13 = B` is impossible**, under `Arch.tso`,
from the runner's exact configuration (threads `abaP0V`, `abaP1V` on their
stacks with the runner's declarations `abaDeclsV`, initial memory
`abaInitMemV`; `A = 0x1000100`, `B = 0x1000200`). -/
theorem x64_treiber_aba_tagged_runner_concrete {fuel : Nat} {cfg : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [abaP0V, abaP1V] abaInitMemV) cfg) (hf : cfg.final = true) :
    ¬ ∃ t0 t1, cfg.threads[0]? = some t0 ∧ cfg.threads[1]? = some t1 ∧
      t0.st.st.1.regs.get64 .r12 = 0x1000100 ∧ t0.st.st.1.regs.get64 .r13 = 0x1000200 ∧
      t1.st.st.1.regs.get64 .r13 = 0x1000200 := by
  have h := x64_treiber_aba_tagged_never (layout := abaLayoutV) abaDeclsV_sized
    (by rw [symV_head]; decide) (by rw [symV_A]; decide) (by rw [symV_B]; decide)
    (by rw [symV_A, symV_B]; decide)
    (abaThreadV_start (by decide) "p0" _ (by rw [labV_at 0]; decide))
    (abaThreadV_start (by decide) "p1" _ (by rw [labV_at 14]; decide))
    (stk_get_none (by decide) (by rw [symV_A]; decide)) (stk_get_none (by decide) (by rw [symV_A]; decide))
    (stk_get_none (by decide) (by rw [symV_B]; decide))
    (by
      show IV ⟨symV "head", symV "A", symV "B"⟩ _
      rw [symV_head, symV_A, symV_B]; simp only [Config.init_mem]
      exact ⟨by decide, by decide, by decide⟩)
    hc hf
  rwa [symV_A, symV_B] at h

/-- **`treiber_aba_tagged.kl` from the runner's exact configuration: the
ABA outcome is impossible (under `Arch.tso`), and no step faults (under any
architecture).** -/
theorem x64_treiber_aba_tagged_runner_safe_faultFree_concrete {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init [abaP0V, abaP1V] abaInitMemV) c → c.final = true →
      ¬ ∃ t0 t1, c.threads[0]? = some t0 ∧ c.threads[1]? = some t1 ∧
        t0.st.st.1.regs.get64 .r12 = 0x1000100 ∧ t0.st.st.1.regs.get64 .r13 = 0x1000200 ∧
        t1.st.st.1.regs.get64 .r13 = 0x1000200) ∧
    Config.FaultFree (I := isa) A fuel (Config.init [abaP0V, abaP1V] abaInitMemV) :=
  ⟨fun _ hc hf => x64_treiber_aba_tagged_runner_concrete hc hf,
    x64_treiber_aba_tagged_runner_faultFree_concrete⟩

end

end Kraken.Promising.X64.EnvG.VecABA.Concrete

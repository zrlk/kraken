/-
**`treiber2_arm.kl` (AArch64) never faults at the runner's declarations**
`treiber2_arm_envG_runner_faultFree` and its
concrete instance `treiber2_arm_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included). The proof is `MemValsA64Treiber2`'s for `treiber2.kl`
with the Arm-minimal worker `treiber2ArmWorker` (push `ldr`/`casl`, pop
`ldar`/`cas`): the value invariant is the same, and is reused from there
(`Treiber2ValLA`, `Treiber2ValVA`, `treiber2GA`, `treiber2SA`,
`treiber2ValA_cas`, `memValsA_treiber2_init`):

- `L`: the words `top`, `n0 + 8` and `n1 + 8`;
- `V`: `0`, `n0` or `n1` (low 64 bits).

A worker writes its own node to `top` and the `top` it read to its node's
link (push), then the link it read to `top` (pop); a non-zero `top` it reads
is `n0` or `n1`, so its loads stay inside the layout
(`treiber2ArmWorker_val`: `vcgen` in the counted `inv S G`, register tables
only). Access kinds (plain or acquire loads, release or plain CAS) do not
matter to the value environment. The initial memory must give the three `L`
words the value `0`; at the runner's configuration that is `decide`.

Phase-1 limit: single-access trees (`treiber2ArmWorker_phase1F`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2
import Kraken.Promising.SLR.EnvG.A64Treiber2ArmRunner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken.Promising.SLR.EnvG.Treiber2 (Treiber2ValLA Treiber2ValVA treiber2GA treiber2SA treiber2EnvA
  treiber2ValA_cas memValsA_treiber2_init treiber2DeclsD_sized treiber2InitMemD)
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

set_option mvcgen.warning false
set_option experimental.vcgen true

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ArmWorker)]

local instance treiber2ArmWorker.envVal : CodeEnv := ⟨layout treiber2ArmWorker⟩

/-- The worker's value table: `X0 = top`, `X1` its node, no private 8- or
4-byte word. -/
abbrev workAValTable (t n0 n1 n : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (treiber2EnvA t n0 n1)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ (lb = "worker" ∨ lb = "push" ∨ lb = "pop" ∨ lb = "done")

/-- **The `treiber2_arm` worker in the value environment** (counted,
partial), for its node `n ∈ {n0, n1}`: a non-zero `top` it reads is a node,
so its loads are at that node's link and data word; its `casl`/`cas` write
its node and the link it read. -/
theorem treiber2ArmWorker_val (t n0 n1 n : BitVec 64) (hn : n = n0 ∨ n = n1) :
    PartialTripleEnv (SharedEnv.counted (treiber2EnvA t n0 n1))
      (fun s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none))
      treiber2ArmWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workAValTable t n0 n1 n) (hP := by funext s g; simp [workAValTable])
  cfg_cases_env [treiber2ArmWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, Treiber2ValLA, Treiber2ValVA]; done)
  -- push: `str x2, [x1, #8]` of the `top` read by the plain `ldr`
  case vc4 =>
    rename_i _ hld _
    simp [hd8, hx0] at hld
    obtain ⟨v, ⟨hst, -⟩, rfl⟩ := hld
    have hv : Treiber2ValVA n0 n1 v := hst (.inl rfl)
    simp only [Treiber2ValVA] at hv
    rcases hn with rfl | rfl <;> simp_all [SharedEnv.inv, Reg64s.setXReg, Treiber2ValLA, Treiber2ValVA]
  -- push: `casl` writes the worker's node
  case vc7 =>
    rename_i hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx1, Treiber2ValLA]
    exact fun old _ => treiber2ValA_cas (hn.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) old
  -- push: a failed `casl` loops to `push` (counter progress)
  case vc8 =>
    rename_i hld hst hcas _
    simp [hx1, hd8] at hst hld
    obtain ⟨rfl, hst2⟩ := hst
    obtain ⟨_, ⟨-, h1⟩, -⟩ := hld
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inl rfl)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h2 := hcas.2
    simp only [SharedEnv.tick_rmw] at h1 h2
    omega
  -- pop: `cbz` to `done`
  case vc4 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inr rfl))⟩, .inl (by decide)⟩
  case vc9 =>
    rename_i s σ0 v σ1 hnz rng x4 σ2 hld hld2 _
    have hv : Treiber2ValVA n0 n1 v := by simpa [hx0, Treiber2ValLA] using hld.1
    simp [Reg64s.setXReg] at hnz
    have hx2 : v.setWidth 64 = n0 ∨ v.setWidth 64 = n1 := hv.resolve_left hnz
    have hd8' : ∀ a : BitVec 64, Mem.loadInt s.dmem (a + 8#64) 8 = none := fun a => hd8 _
    rcases hx2 with hx2 | hx2 <;>
    · simp [Reg64s.setXReg, hx2, hd8', SharedEnv.inv, Treiber2ValLA] at hld2
      obtain ⟨w, ⟨hw, -⟩, rfl⟩ := hld2
      simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx2, Treiber2ValLA]
      exact fun old _ => treiber2ValA_cas hw old
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    simp [hd8] at hld2
    have h12 : σ1.2 ≤ σ2.2 := by
      obtain ⟨_, ⟨_, h⟩, _⟩ := hld2
      omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inl rfl))⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc13 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inr (.inr rfl))⟩, .inl (by decide)⟩
  all_goals done

end Worker

/-! ## The specification and the theorem -/

section Spec

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2ArmWorker)]

/-- Both `treiber2_arm` workers' value specification: the worker image,
ending at `done`. -/
def treiber2ArmValSpecA (t n0 n1 : BitVec 64) : ValSpecA (treiber2GA t n0 n1) :=
  ValSpecA.ofProgram (treiber2GA t n0 n1) (treiber2SA t n0 n1) treiber2ArmWorker treiber2ArmWorker_noPairs
    treiber2ArmWorker_rmwLive treiber2ArmWorker_noFault
    fun st he hd tree hex => rootOnlyDA_of_phase1ShapeF (treiber2ArmWorker_phase1F st he hd tree hex)

/-- **A `treiber2_arm` worker's start state holds the specification**, for
its node `n ∈ {n0, n1}`, with declarations `ds`. -/
theorem treiber2ArmValSpecA_start {t n0 n1 n : BitVec 64} (hn : n = n0 ∨ n = n1) {d : BitVec 32} {ds : Decls}
    {s : isa.State} (h : WithDeclsD ds (StartWA t n d) s) : (treiber2ArmValSpecA t n0 n1).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := h
  letI : CodeEnv := ⟨layout treiber2ArmWorker⟩
  exact holdsD_inv_of_partialTripleEnv (st := s) (treiber2ArmWorker_val t n0 n1 n hn).uncount rfl hS.exe hds
    hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, hS.d4⟩

end Spec

/-- **No reachable configuration of the verbatim `treiber2_arm.kl` workers
with the runner's declarations has a faulting step** (one layout `l` for
both, as the runner sets them up), for strict sized `ds` agreeing on `top`
and both nodes' data words and links, and an initial memory with `top`,
`n0 + 8` and `n1 + 8` at `0`. Any data words `d0 d1`. -/
theorem treiber2_arm_envG_runner_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiber2ArmWorker)] {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64)
    (hag : ds.AgreesOnA (treiber2SA t n0 n1)) {d0 d1 : BitVec 32} {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartWA (layout := l) t n0 d0) s0)
    (h1 : WithDeclsD ds (StartWA (layout := l) t n1 d1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (fun _ => treiber2ArmValSpecA (layout := l) t n0 n1)
    (fun _ => ds) (fun _ => hsz) (fun _ => hag) (memValsA_treiber2_init hT0 hN0 hN1)
    (init_threads_of2 (treiber2ArmValSpecA_start (.inl rfl) h0) (treiber2ArmValSpecA_start (.inr rfl) h1))

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr) in
set_option maxRecDepth 8192 in
/-- **`treiber2_arm.kl` never faults**, from the runner's exact
configuration (`[wWorkerDA0, wWorkerDA1]` with the runner's declarations,
initial memory `treiber2InitMemD`; `runnerMatchesDA`), under any
architecture. -/
theorem treiber2_arm_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [wWorkerDA0, wWorkerDA1] treiber2InitMemD) :=
  treiber2_arm_envG_runner_faultFree wLayoutA treiber2DeclsD_sized topAddr n1Addr n2Addr (by decls_agrees_on_a)
    (withDeclsD_of rfl wWorkerA0_start) (withDeclsD_of rfl wWorkerA1_start)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)

end Kraken.Promising.SLR.EnvG.Treiber2Arm

#print axioms Kraken.Promising.SLR.EnvG.Treiber2Arm.treiber2_arm_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.Treiber2Arm.treiber2_arm_envG_runner_faultFree_concrete

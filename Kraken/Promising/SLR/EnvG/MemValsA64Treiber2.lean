/-
**`treiber2.kl` (AArch64) never faults at the runner's declarations**
`treiber2_envG_runner_faultFree` and its
concrete instance `treiber2_envG_runner_faultFree_concrete`, program-level
`Config.FaultFree` from the runner's start states under any architecture
(promises included).

Each worker pops a node it read from `top` and loads that node's link
`[X2, #8]` and data word `[X2]`; no fixed-layout address run covers that.
Both workers get **value specifications** (`MemValsA64.ValSpecA`) over
`inv S G` at the layout `treiber2SA top n0 n1` (`top`, each node's data word
and link), with

- `L` (`Treiber2ValLA`): the words `top`, `n0 + 8` and `n1 + 8`;
- `V` (`Treiber2ValVA n0 n1`): `0`, `n0` or `n1` (low 64 bits).

A worker writes its own node to `top` and the `top` it read to its node's
link (push), then the link it read to `top` (pop); a non-zero `top` it reads
is `n0` or `n1`, so its loads stay inside the layout
(`treiber2DWorker_val_at`: `vcgen` in the counted `inv S G`, register tables
only). The initial memory must give the three `L` words the value `0`; at
the runner's configuration that is `decide`.

Phase-1 limit: single-access trees (`treiber2DWorker_phase1F`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Runner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber2

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The locations of the value invariant: `top` and both nodes' links. -/
def Treiber2ValLA (t n0 n1 : BitVec 64) : Loc → Prop := fun l =>
  l = ⟨t, 8⟩ ∨ l = ⟨n0 + 8, 8⟩ ∨ l = ⟨n1 + 8, 8⟩

/-- The values of the value invariant: the empty stack `0` or a node. -/
def Treiber2ValVA (n0 n1 : BitVec 64) : Val → Prop := fun v =>
  v.setWidth 64 = 0 ∨ v.setWidth 64 = n0 ∨ v.setWidth 64 = n1

/-- The value condition. -/
abbrev treiber2GA (t n0 n1 : BitVec 64) : Loc → Val → Prop := fun l v =>
  Treiber2ValLA t n0 n1 l → Treiber2ValVA n0 n1 v

/-- The workers' layout: `top`, then each node's data word and link. -/
abbrev treiber2SA (t n0 n1 : BitVec 64) : SharedEnv.Layout :=
  [(t, 8), (n0, 4), (n0 + 8, 8), (n1, 4), (n1 + 8, 8)]

/-- The workers' environment. -/
abbrev treiber2EnvA (t n0 n1 : BitVec 64) : SharedEnv := SharedEnv.inv (treiber2SA t n0 n1) (treiber2GA t n0 n1)

/-- A 64-bit compare-and-swap writing a `V`-value writes a `V`-value
(`MemValsA64.rmwOpBits_cas_val`). -/
theorem treiber2ValA_cas {n0 n1 c y : BitVec 64} (hy : y = 0 ∨ y = n0 ∨ y = n1) :
    ∀ old v, rmwOpBits 64 (fun old => if old = c then some y else none) old = some v →
      Treiber2ValVA n0 n1 v :=
  rmwOpBits_cas_val (P := fun x => x = 0 ∨ x = n0 ∨ x = n1) hy

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2DWorker)]

local instance treiber2DWorker.envVal : CodeEnv := ⟨layout treiber2DWorker⟩

/-- The worker's value table: `X0 = top`, `X1` its node, no private 8- or
4-byte word. -/
abbrev workValTable (t n0 n1 n : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (treiber2EnvA t n0 n1)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (∀ a, Mem.loadInt s.dmem a 4 = none) ∧ (lb = "worker" ∨ lb = "push" ∨ lb = "pop" ∨ lb = "done")

/-- **The worker in the value environment** (counted, partial), for its node
`n ∈ {n0, n1}`: a non-zero `top` it reads is a node, so its loads are at that
node's link and data word; its `casal`s write its node and the link it
read. -/
theorem treiber2DWorker_val (t n0 n1 n : BitVec 64) (hn : n = n0 ∨ n = n1) :
    PartialTripleEnv (SharedEnv.counted (treiber2EnvA t n0 n1))
      (fun s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
        (∀ a, Mem.loadInt s.dmem a 4 = none))
      treiber2DWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workValTable t n0 n1 n) (hP := by funext s g; simp [workValTable])
  cfg_cases_env [treiber2DWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hd4, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, Treiber2ValLA, Treiber2ValVA]; done)
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx1, Treiber2ValLA]
    exact fun old _ => treiber2ValA_cas (hn.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) old
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hd8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], by simp [hd4],
      .inr (.inl rfl)⟩, .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
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

open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

/-- The initial memory satisfies the value invariant when `top`, `n0 + 8`
and `n1 + 8` start at `0` (no messages yet). -/
theorem memValsA_treiber2_init {t n0 n1 : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hT0 : (Config.init states initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init states initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init states initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    MemVals (Treiber2ValLA t n0 n1) (Treiber2ValVA n0 n1) (Config.init states initMem).mem := by
  refine ⟨fun l hl => ?_, fun ts w h _ => ?_⟩
  · rcases hl with rfl | rfl | rfl
    · simp only [Treiber2ValVA, hT0]; simp
    · simp only [Treiber2ValVA, hN0]; simp
    · simp only [Treiber2ValVA, hN1]; simp
  · simp [Memory.get?, Config.init] at h

section Spec

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2DWorker)]

/-- Both workers' value specification: the worker image, ending at `done`. -/
def treiber2ValSpecA (t n0 n1 : BitVec 64) : ValSpecA (treiber2GA t n0 n1) :=
  ValSpecA.ofProgram (treiber2GA t n0 n1) (treiber2SA t n0 n1) treiber2DWorker treiber2DWorker_noPairs
    treiber2DWorker_rmwLive treiber2DWorker_noFault
    fun st he hd tree hex => rootOnlyDA_of_phase1ShapeF (treiber2DWorker_phase1F st he hd tree hex)

/-- **A worker's start state holds the specification**, for its node
`n ∈ {n0, n1}`, with declarations `ds`. -/
theorem treiber2ValSpecA_start {t n0 n1 n : BitVec 64} (hn : n = n0 ∨ n = n1) {d : BitVec 32} {ds : Decls}
    {s : isa.State} (h : WithDeclsD ds (StartWD t n d) s) : (treiber2ValSpecA t n0 n1).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := h
  letI : CodeEnv := ⟨layout treiber2DWorker⟩
  exact holdsD_inv_of_partialTripleEnv (st := s) (treiber2DWorker_val t n0 n1 n hn).uncount rfl hS.exe hds
    hS.endPc hS.pc ⟨0, hS.x0, hS.x1, hS.d8, hS.d4⟩

end Spec

/-- **No reachable configuration of the verbatim `treiber2.kl` workers with
the runner's declarations has a faulting step** (one layout `l` for both, as
the runner sets them up), for strict sized `ds` agreeing on `top` and both
nodes' data words and links, and an initial memory with `top`, `n0 + 8` and
`n1 + 8` at `0`. -/
theorem treiber2_envG_runner_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiber2DWorker)] {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64)
    (hag : ds.AgreesOnA (treiber2SA t n0 n1)) {d0 d1 : BitVec 32} {s0 s1 : isa.State}
    {initMem : List (Loc × Val)} (h0 : WithDeclsD ds (StartWD (layout := l) t n0 d0) s0)
    (h1 : WithDeclsD ds (StartWD (layout := l) t n1 d1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (fun _ => treiber2ValSpecA (layout := l) t n0 n1) (fun _ => ds)
    (fun _ => hsz) (fun _ => hag) (memValsA_treiber2_init hT0 hN0 hN1)
    (init_threads_of2 (treiber2ValSpecA_start (.inl rfl) h0) (treiber2ValSpecA_start (.inr rfl) h1))

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr) in
set_option maxRecDepth 8192 in
/-- **`treiber2.kl` never faults**, from the runner's exact configuration
(`[wWorkerD0, wWorkerD1]` with the runner's declarations, initial memory
`treiber2InitMemD`), under any architecture. -/
theorem treiber2_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [wWorkerD0, wWorkerD1] treiber2InitMemD) :=
  treiber2_envG_runner_faultFree wLayout2D treiber2DeclsD_sized topAddr n1Addr n2Addr (by decls_agrees_on_a)
    (withDeclsD_of rfl wWorker0_start) (withDeclsD_of rfl wWorker1_start)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)

end Kraken.Promising.SLR.EnvG.Treiber2

#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_envG_runner_faultFree_concrete

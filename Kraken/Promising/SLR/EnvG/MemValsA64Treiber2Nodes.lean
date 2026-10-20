/-
**`treiber2_nodes.kl` (AArch64) never faults at the runner's declarations**
`treiber2_nodes_envG_runner_faultFree` and its
concrete instance `treiber2_nodes_envG_runner_faultFree_concrete`,
program-level `Config.FaultFree` from the runner's start states under any
architecture (promises included).

As `MemValsA64Treiber2` without the data word: both threads run the whole
image `treiber2NImage` under the value condition `treiber2GA` (`L`: `top`,
`n0 + 8`, `n1 + 8`; `V`: `0`, `n0`, `n1`) at the layout `treiber2NSA top n0
n1` (`top` and both links). A non-zero `top` a worker reads is a node, so
its link load `[X2, #8]` stays inside the layout (`treiber2NImage_val`:
`vcgen` in the counted `inv S G`, register tables only).

Phase-1 limit: single-access trees (`treiber2NImage_phase1F`).
-/
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2NodesRunner

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.Treiber2

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- The nodes workers' layout: `top` and both nodes' links. -/
abbrev treiber2NSA (t n0 n1 : BitVec 64) : SharedEnv.Layout := [(t, 8), (n0 + 8, 8), (n1 + 8, 8)]

/-- The nodes workers' environment. -/
abbrev treiber2NEnvA (t n0 n1 : BitVec 64) : SharedEnv :=
  SharedEnv.inv (treiber2NSA t n0 n1) (treiber2GA t n0 n1)

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2NImage)]

local instance treiber2NImage.envVal : CodeEnv := ⟨layout treiber2NImage⟩

/-- The image's value table: `X0 = top`, `X1` the thread's node, no private
8-byte word. -/
abbrev workNValTable (t n0 n1 n : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (treiber2NEnvA t n0 n1)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none) ∧
    (lb = "worker" ∨ lb = "push" ∨ lb = "pop" ∨ lb = "done")

/-- **The image in the value environment** (counted, partial), for the
thread's node `n ∈ {n0, n1}`. -/
theorem treiber2NImage_val (t n0 n1 n : BitVec 64) (hn : n = n0 ∨ n = n1) :
    PartialTripleEnv (SharedEnv.counted (treiber2NEnvA t n0 n1))
      (fun s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧ (∀ a, Mem.loadInt s.dmem a 8 = none))
      treiber2NImage (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workNValTable t n0 n1 n) (hP := by funext s g; simp [workNValTable])
  cfg_cases_env [treiber2NImage]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hd8, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
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
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inl rfl)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc4 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr (.inr rfl))⟩,
      .inl (by decide)⟩
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
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr (.inl rfl))⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc11 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], by simp [hd8], .inr (.inr (.inr rfl))⟩,
      .inl (by decide)⟩
  all_goals done

end Worker

/-! ## The specification and the theorem -/

open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD withDeclsD_of)

section Spec

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2NImage)]

/-- Both threads' value specification: the image, ending at `done`. -/
def treiber2NValSpecA (t n0 n1 : BitVec 64) : ValSpecA (treiber2GA t n0 n1) :=
  ValSpecA.ofProgram (treiber2GA t n0 n1) (treiber2NSA t n0 n1) treiber2NImage treiber2NImage_noPairs
    treiber2NImage_rmwLive treiber2NImage_noFault
    fun st he hd tree hex => rootOnlyDA_of_phase1ShapeF (treiber2NImage_phase1F st he hd tree hex)

/-- `worker`'s address is the start of the image. -/
theorem labN_worker_zero : labN "worker" = (layout treiber2NImage).addrOf 0 :=
  Program.label_addrOf_drop treiber2NImage_wf.nodup (by decide) (by decide)

/-- **A thread's start state holds the specification**, for its node
`n ∈ {n0, n1}`, with declarations `ds`. -/
theorem treiber2NValSpecA_start {t n0 n1 n : BitVec 64} (hn : n = n0 ∨ n = n1) {ds : Decls} {s : isa.State}
    (h : WithDeclsD ds (StartWN t n) s) : (treiber2NValSpecA t n0 n1).HoldsD ds s := by
  obtain ⟨hds, hS⟩ := h
  letI : CodeEnv := ⟨layout treiber2NImage⟩
  exact holdsD_inv_of_partialTripleEnv (st := s) (treiber2NImage_val t n0 n1 n hn).uncount rfl hS.exe hds
    (hS.endPc.trans labN_done) (hS.pc.trans labN_worker_zero) ⟨0, hS.x0, hS.x1, hS.d8⟩

end Spec

/-- **No reachable configuration of the verbatim `treiber2_nodes.kl` threads
with the runner's declarations has a faulting step** (one layout `l` for
both), for strict sized `ds` agreeing on `top` and both links, and an
initial memory with `top`, `n0 + 8` and `n1 + 8` at `0`. -/
theorem treiber2_nodes_envG_runner_faultFree {A : Arch} {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l treiber2NImage)] {ds : Decls} (hsz : ds.StrictSized) (t n0 n1 : BitVec 64)
    (hag : ds.AgreesOnA (treiber2NSA t n0 n1)) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : WithDeclsD ds (StartWN (layout := l) t n0) s0) (h1 : WithDeclsD ds (StartWN (layout := l) t n1) s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    (hN0 : (Config.init [s0, s1] initMem).mem.initVal ⟨n0 + 8, 8⟩ = 0)
    (hN1 : (Config.init [s0, s1] initMem).mem.initVal ⟨n1 + 8, 8⟩ = 0) :
    Config.FaultFree A fuel (Config.init [s0, s1] initMem) :=
  a64_faultFree_of_valSpecs (fun _ _ => Iff.rfl) (fun _ => treiber2NValSpecA (layout := l) t n0 n1) (fun _ => ds)
    (fun _ => hsz) (fun _ => hag) (memValsA_treiber2_init hT0 hN0 hN1)
    (init_threads_of2 (treiber2NValSpecA_start (.inl rfl) h0) (treiber2NValSpecA_start (.inr rfl) h1))

open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr) in
set_option maxRecDepth 8192 in
/-- **`treiber2_nodes.kl` never faults**, from the runner's exact
configuration (`[wNWorkerD0, wNWorkerD1]` with the runner's declarations,
initial memory `treiber2NInitMemD`), under any architecture. -/
theorem treiber2_nodes_envG_runner_faultFree_concrete {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init [wNWorkerD0, wNWorkerD1] treiber2NInitMemD) :=
  treiber2_nodes_envG_runner_faultFree wLayout2N treiber2NDeclsD_sized topAddr n1Addr n2Addr
    (by decls_agrees_on_a) (withDeclsD_of rfl wNWorker0_start) (withDeclsD_of rfl wNWorker1_start)
    (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) (by simp only [Config.init]; decide)

end Kraken.Promising.SLR.EnvG.Treiber2

#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_nodes_envG_runner_faultFree
#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_nodes_envG_runner_faultFree_concrete

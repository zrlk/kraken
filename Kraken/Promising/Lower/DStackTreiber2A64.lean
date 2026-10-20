/-
**Demo: the `treiber2.kl` worker beside a private
stack.**

`MemValsA64Treiber2.treiber2DWorker_val` asks the worker's private memory to
be empty at every 8- and 4-byte word (`∀ a, Mem.loadInt s.dmem a 8 = none`),
so it says nothing about a thread with a stack in `dmem`.
`treiber2DWorker_val_heapOff` is the same specification under
`HeapOff (Covers (treiber2SA t n0 n1)) s.dmem` instead: `dmem` may map
anything except the bytes of `top` and the two nodes. The proof is the
original's, with each `loadInt dmem a n = none` side condition at a layout
address taken from
`HeapOff.loadInt_none_of_mem`, and the one through a loaded pointer from the
source obligation `PtrsInHeap` (`treiber2_ptrsInHeap`: a pointer cell holds
null or a node). The table carries `HeapOff` unchanged; the run lemmas of
`Lower/DStackA64.lean` say why that is sound for any program.
-/
import Kraken.Promising.SLR.EnvG.MemValsA64Treiber2
import Kraken.Promising.Lower.DStack

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.AArch64.EnvG Kraken.Promising.SLR.EnvG.Treiber2
open Kraken.DStack

namespace Kraken.DStack.Treiber2A64

set_option mvcgen.warning false
set_option experimental.vcgen true

/-- **The source obligation for `treiber2`**: a pointer cell (`top`, a
node's link) holds null or a node. Here it is the value invariant itself. -/
theorem treiber2_ptrsInHeap (t n0 n1 : BitVec 64) :
    PtrsInHeap (Treiber2ValLA t n0 n1) (treiber2GA t n0 n1) (fun p => p = n0 ∨ p = n1) :=
  fun _ _ hl hg => hg hl

section Worker

variable [layout : _root_.Layout] [Executable.ValidLayout (layout treiber2DWorker)]

local instance treiber2DWorker.envHeap : CodeEnv := ⟨layout treiber2DWorker⟩

/-- The worker's table: `X0 = top`, `X1` its node, the layout off `dmem`. -/
abbrev workHeapTable (t n0 n1 n : BitVec 64) :
    Label → MachineData → (SharedEnv.counted (treiber2EnvA t n0 n1)).State → Prop :=
  fun lb s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧
    HeapOff (SharedLayout.Covers (treiber2SA t n0 n1)) s.dmem ∧
    (lb = "worker" ∨ lb = "push" ∨ lb = "pop" ∨ lb = "done")

/-- **The worker in the value environment beside a private stack**
(counted, partial): `treiber2DWorker_val` with `dmem` free off the layout. -/
theorem treiber2DWorker_val_heapOff (t n0 n1 n : BitVec 64) (hn : n = n0 ∨ n = n1) :
    PartialTripleEnv (SharedEnv.counted (treiber2EnvA t n0 n1))
      (fun s _ => s.regs.X0.toBitVec = t ∧ s.regs.X1.toBitVec = n ∧
        HeapOff (SharedLayout.Covers (treiber2SA t n0 n1)) s.dmem)
      treiber2DWorker (fun _ _ => True) (fun _ _ _ => False) := by
  apply MachineWP.cfgEnv_partial (workHeapTable t n0 n1 n) (hP := by funext s g; simp [workHeapTable])
  cfg_cases_env [treiber2DWorker]
  all_goals intro s₀ g₀
  all_goals vcgen
  all_goals obtain ⟨⟨hx0, hx1, hH, hT⟩, rfl, rfl⟩ := ‹(_ ∧ _) ∧ _ = _ ∧ _ = _›
  all_goals have ht8 := hH.loadInt_none_of_mem (a := t) (n := 8) (by simp) (by decide)
  all_goals have h08 := hH.loadInt_none_of_mem (a := n0 + 8) (n := 8) (by simp) (by decide)
  all_goals have h18 := hH.loadInt_none_of_mem (a := n1 + 8) (n := 8) (by simp) (by decide)
  all_goals have h04 := hH.loadInt_none_of_mem (a := n0) (n := 4) (by simp) (by decide)
  all_goals have h14 := hH.loadInt_none_of_mem (a := n1) (n := 4) (by simp) (by decide)
  all_goals have hn8 := hH.loadInt_none_of_mem (a := n + 8) (n := 8) (by rcases hn with rfl | rfl <;> simp) (by decide)
  all_goals have hn4 := hH.loadInt_none_of_mem (a := n) (n := 4) (by rcases hn with rfl | rfl <;> simp) (by decide)
  -- The worker's addresses carry `8#64`; the layout's, `8`.
  all_goals replace h08 : Mem.loadInt _ (n0 + 8#64) 8 = none := h08
  all_goals replace h18 : Mem.loadInt _ (n1 + 8#64) 8 = none := h18
  all_goals replace hn8 : Mem.loadInt _ (n + 8#64) 8 = none := hn8
  all_goals simp only [SharedEnv.counted_step, SharedEnv.counted_ok] at *
  all_goals try (simp_all [SharedEnv.inv, Reg64s.setXReg, Treiber2ValLA, Treiber2ValVA]; done)
  case vc8 =>
    rename_i s σ0 v σ1 rng dm σ2 hld hst _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, -⟩ := hst
    simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx1, Treiber2ValLA]
    exact fun old _ => treiber2ValA_cas (hn.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr)) old
  case vc9 =>
    rename_i s σ0 v σ1 rng dm σ2 old σ3 hbr hld hst hcas _
    simp [hx1, hn8] at hst
    obtain ⟨rfl, hst2⟩ := hst
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], hH, .inr (.inl rfl)⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc4 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], hH, .inr (.inr (.inr rfl))⟩,
      .inl (by decide)⟩
  case vc9 =>
    rename_i s σ0 v σ1 hnz rng x4 σ2 hld hld2 _
    have hv : Treiber2ValVA n0 n1 v := by simpa [hx0, Treiber2ValLA] using hld.1
    simp [Reg64s.setXReg] at hnz
    have hx2 := (treiber2_ptrsInHeap t n0 n1 ⟨t, 8⟩ v (.inl rfl) fun _ => hv).resolve_left hnz
    rcases hx2 with hx2 | hx2 <;>
    · simp [Reg64s.setXReg, hx2, h08, h18, SharedEnv.inv, Treiber2ValLA] at hld2
      obtain ⟨w, ⟨hw, -⟩, rfl⟩ := hld2
      simp [SharedEnv.inv, Reg64s.setXReg, hx0, hx2, Treiber2ValLA]
      exact fun old _ => treiber2ValA_cas hw old
  case vc10 =>
    rename_i s σ0 v σ1 hnz rng v4 σ2 old σ3 hbr hld hld2 hcas _
    have hv : Treiber2ValVA n0 n1 v := by simpa [hx0, Treiber2ValLA] using hld.1
    simp [Reg64s.setXReg] at hnz
    have hx2 := (treiber2_ptrsInHeap t n0 n1 ⟨t, 8⟩ v (.inl rfl) fun _ => hv).resolve_left hnz
    have h12 : σ1.2 ≤ σ2.2 := by
      rcases hx2 with hx2 | hx2 <;>
      · simp [Reg64s.setXReg, hx2, h08, h18] at hld2
        obtain ⟨_, ⟨_, h⟩, _⟩ := hld2
        omega
    refine Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], hH, .inr (.inr (.inl rfl))⟩,
      .inr fun ⟨_, hg⟩ => ?_⟩
    subst hg
    have h1 := hld.2; have h2 := hcas.2
    simp only [SharedEnv.tick_load, SharedEnv.tick_rmw] at h1 h2
    omega
  case vc13 =>
    exact Table.ofLabelsEnv_at ⟨by decide, ⟨by simp [hx0], by simp [hx1], hH, .inr (.inr (.inr rfl))⟩,
      .inl (by decide)⟩
  all_goals done

end Worker

end Kraken.DStack.Treiber2A64

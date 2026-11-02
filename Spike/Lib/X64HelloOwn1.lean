/-
**hello.w's worker-owned words on x86-64** (the worker rows' ownership facts): `Own1H Q D` states what the worker's
print- and emit-phase rows read of `Q.own w 1`, in place of the equation `Q.own = X64WakeOwn.wakeOwn` (no owned
word). The worker may then own its TCB's self word `⟨W, 8⟩ ↦ W` (`X64WakeOwnX.wakeOwnXW`), which it reads through
`%fs:0`.

- `Own1H`: the worker's owned words are constant (over its state and source frames, `const`), never a runtime
  write's target (`mp`), and not the flag word `cT` (`cT`, the worker's one plain store and its promise). `cT` is
  guarded by the memory relation over the spawn's placement because only that relation (`Inv2Core.mem`) places the
  flag in `heap ∪ data`, off the pinned TCB words; the record's own facts (`GhOK`) place it only in `shared`.
- `PartsH.ownOk1`, `ownDisj1`, `ownCov1`: `Inv2Core`'s thread-1 facts at any state and frames (by `const`).
- `own1H_XW`: `Own1H` at `wakeOwnXW T W` for a worker side `msXW _ W T W` (`ownMpXW`'s narrowing) whose flag word
  is not `⟨W, 8⟩`.

## Differences from the AArch64 version

Unlike AArch64, where the worker reads its thread pointer from `tpidr_el0` and owns no word (the rows take
`Q.own = wakeOwn`), the x86-64 worker owns its TCB word, so the rows take `Own1H` (at hello's instance
`own1H_XW`, `X64HelloAssemblyRV`).
-/
import Spike.Lib.X64HelloW1
import Spike.Lib.X64WakeOwnXW

namespace Spike.Lib.X64HelloOwn1

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.Inv2Core
open Spike.Lib.X64HelloW1 (WSideH PartsH)
open Spike.Lib.X64WakeOwnX (OffTcb msXW offTcb_self wakeOwnXW)

/-- **The worker's owned words as its rows read them**: constant over the worker's state and source frames, never
the target of a runtime write of the worker's memory side, and not the flag word. -/
structure Own1H (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) : Prop where
  /-- The worker's owned words do not depend on its state or source frames. -/
  const : ∀ w s fs s' fs', Q.own w 1 s' fs' = Q.own w 1 s fs
  /-- No owned word is a runtime write's target. -/
  mp : ∀ w fs s L v, (L, v) ∈ Q.own w 1 s fs → ¬ (D.ms w fs).mp L true
  /-- The flag word (the worker's `store rel c 1`) is not owned, under the memory relation of the spawn's placement
  (`Inv2Core.mem`; it places the flag in `heap ∪ data`). -/
  cT : ∀ w ts tm sm tp sp s fs v, MemRelP Λ (Q.SR w).lbl (Q.SR w).lsize ts tm sm tp [] sp →
    ((Q.C w).cT, v) ∉ Q.own w 1 s fs

section Parts

variable {Q : WakeRel} {D : WSideH Q.ι} {Λ : Scc.Sem.Layout} {w : Q.ι} {t : Cfg} {s : TermRun.Cfg}
  {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- The worker's owned words, at any state and frames, read as their values. -/
theorem _root_.Spike.Lib.X64HelloW1.PartsH.ownOk1 (ho : Own1H Q D Λ) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (st : isa.State) (fs : List TermRun.Frame) : ExtRows.OwnOk (Q.own w 1 st fs) t.1.mem t1.prom := by
  have : ExtRows.OwnOk (Q.own w 1 t1.st s1.stack) t.1.mem t1.prom := by simpa using h.core.own1
  rwa [ho.const w st fs t1.st s1.stack] at this

/-- The worker's owned words, at any state and frames, are none of main's. -/
theorem _root_.Spike.Lib.X64HelloW1.PartsH.ownDisj1 (ho : Own1H Q D Λ) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (st : isa.State) (fs : List TermRun.Frame) :
    ∀ L v v', (L, v) ∈ Q.own w 0 t0.st s0.stack → (L, v') ∈ Q.own w 1 st fs → False := by
  intro L v v' h0 h1
  rw [ho.const w t1.st s1.stack st fs] at h1
  exact h.core.own_disj L v v' (by simpa using h0) (by simpa using h1)

/-- The worker's owned words, at any state and frames, are in its cover set. -/
theorem _root_.Spike.Lib.X64HelloW1.PartsH.ownCov1 (ho : Own1H Q D Λ) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (st : isa.State) (fs : List TermRun.Frame) : ∀ L v, (L, v) ∈ Q.own w 1 st fs → (Q.P w).cov 1 L := by
  intro L v h1
  rw [ho.const w t1.st s1.stack st fs] at h1
  exact h.core.own_cov 1 L v (by decide) (by simpa using h1)

end Parts

section Inst

variable {Q : WakeRel} {D : WSideH Q.ι} {Λ : Scc.Sem.Layout}

/-- **`Own1H` at `wakeOwnXW T W`**: the worker's memory side is `msXW _ W T W` (its runtime writes off `⟨W, 8⟩`) and
its flag word is not `⟨W, 8⟩` under the memory relation. -/
theorem own1H_XW {T W : BitVec 64} (hown : Q.own = wakeOwnXW T W) {ms : Q.ι → List TermRun.Frame → MemSide isa}
    (hms : ∀ w fs, D.ms w fs = msXW (ms w fs) W T W)
    (hcT : ∀ w ts tm sm tp sp, MemRelP Λ (Q.SR w).lbl (Q.SR w).lsize ts tm sm tp [] sp → (Q.C w).cT ≠ ⟨W, 8⟩) :
    Own1H Q D Λ where
  const _ _ _ _ _ := by rw [hown]; rfl
  mp w fs s L v h := by
    rw [hown, X64WakeOwnX.wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rw [hms w fs]
    rintro ⟨-, h⟩
    exact offTcb_self W (h rfl).2
  cT w ts tm sm tp sp s fs v hm h := by
    rw [hown, X64WakeOwnX.wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at h
    exact hcT w ts tm sm tp sp hm h.1

end Inst

end Spike.Lib.X64HelloOwn1

/-- info: 'Spike.Lib.X64HelloW1.PartsH.ownOk1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.PartsH.ownOk1

/-- info: 'Spike.Lib.X64HelloW1.PartsH.ownDisj1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.PartsH.ownDisj1

/-- info: 'Spike.Lib.X64HelloW1.PartsH.ownCov1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloW1.PartsH.ownCov1

/-- info: 'Spike.Lib.X64HelloOwn1.own1H_XW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwn1.own1H_XW

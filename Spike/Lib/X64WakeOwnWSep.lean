/-
**The worker's TCB word off the child's shared writes** (x86-64;
X64-OwnW-sep): the premises `hA : A ≠ W` and
`hB : B + 16#64 ≠ W` of `Flow.Worker.Wake.OwnW.thrZA_own`
(`Spike/Lib/X64OwnWNodes.lean`), where `W = tcb2 = pinA + 104` is the
worker's TCB word. In the child at `seg_childPreNNA'`, `A = ofNat cA` is
the flag cell's address (`%r12`) and `B = ofNat meW` is main's `ThreadId`
word (`%rbx`), whose `+ 16` is the word `scc_rt_unpark`'s `xchgq` writes.

- `ne_of_heap_wordOk`: a heap address is not a runtime word (`wordOk`:
  `data` or `pinned`, both disjoint from the heap in a well-formed layout).
- `tcb2_wordOk_W`: `tcb2` is a runtime word at `ofPlaceWX` (A13's data
  part, `tcb2_mem_spawnWords`).
- `flag_ne_tcb2_W`: `hA` at `ofPlaceWX` for a flag cell in the heap.
- `unpark_ne_tcb2`: `hB` for `B` main's TCB `tcbM = pinA + 8`
  (`tcbM + 16 = pinA + 24`).

**Deviations.** None. `htp` (`tp + 24#64 ≠ W`) is a premise, discharged in
`X64WakeZXA` from `tp = W`. The child's facts that `cA` is in the heap and
that `meW` is `tcbM` are premises here; the assembly supplies them (the
flag's `ValRep` at the arena, main's `ThreadId` word).
-/
import Spike.Lib.X64WakeOwnT2W

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)

/-- **A heap address is not a runtime word**: `wordOk` puts the word's
first byte in `data` or `pinned`, both disjoint from the heap. -/
theorem ne_of_heap_wordOk {Λ : Scc.Sem.Layout} (hwf : Λ.WF) {W : BitVec 64}
    (hW : Scc.Cert.Rt.X64.wordOk Λ W = true) {c : Nat} (hc64 : c < 2 ^ 64) (hc : Λ.heap.contains c) :
    BitVec.ofNat 64 c ≠ W := by
  intro he
  have hcW : c = W.toNat := by rw [← he, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc64]
  unfold Scc.Cert.Rt.X64.wordOk at hW
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hW
  have h0 := hW.2 0 (by simp)
  obtain ⟨-, -, -, hdh, -, -, -, -, hhp, -⟩ := hwf.disjoint
  simp only [Scc.Sem.Range.contains, Scc.Sem.Range.Disjoint] at hc hdh hhp h0
  omega

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

/-- **`tcb2` is a runtime word at `ofPlaceWX`** (A13's data part). -/
theorem tcb2_wordOk_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    Scc.Cert.Rt.X64.wordOk (Ly).Λ (tcb2 (Ly)) = true := by
  have hm := tcb2_mem_spawnWords (Ly)
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true] at hA13
  obtain ⟨⟨⟨⟨⟨-, hok⟩, -⟩, -⟩, -⟩, -⟩ := hA13
  exact List.all_eq_true.mp hok (tcb2 (Ly)) (List.mem_cons_of_mem _ hm)

/-- **`hA` at `ofPlaceWX`**: a flag cell in the heap is not the worker's
TCB word. -/
theorem flag_ne_tcb2_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) {cA : Nat}
    (hc64 : cA < 2 ^ 64) (hc : (Ly).Λ.heap.contains cA) : BitVec.ofNat 64 cA ≠ tcb2 (Ly) :=
  ne_of_heap_wordOk (PlaceWX.wf_link_of_placeWX i h) (tcb2_wordOk_W h i hA13) hc64 hc

/-- **`hB`**: `scc_rt_unpark`'s word `B + 16` for `B` main's TCB is not the
worker's TCB word (`pinA + 24 ≠ pinA + 104`). -/
theorem unpark_ne_tcb2 {L : RuntimeLayout} {B : BitVec 64} (hB : B = tcbM L) : B + 16#64 ≠ tcb2 L := by
  subst hB; intro he; bv_omega

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.ne_of_heap_wordOk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.ne_of_heap_wordOk

/-- info: 'Spike.Lib.X64.WakePh.flag_ne_tcb2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.flag_ne_tcb2_W

/-- info: 'Spike.Lib.X64.WakePh.unpark_ne_tcb2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.unpark_ne_tcb2

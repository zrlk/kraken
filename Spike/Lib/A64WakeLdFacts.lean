/-
**`WakeWcW1I.wcMainW_wf`'s loader facts at `ofPlaceW`** (wake.w, AArch64):
the second TCB's header `pinA + 96` and id word `t2 + 56 = pinA + 160` are
words of A13's `spawnWords` (`Spawn.A64.a13data`, a check of the concrete
layout), so apart from the four counters and `scc_rt_nthreads` and mapped;
`scc_rt_pinned_next` is mapped (A8's `words_mapped`).

- `spawn_fact`: a word of `spawnWords pinA` is none of the four counters and
  `ntA`, and is mapped.
- `hhdr_W`, `hmP_W`, `hmH_W`, `htid1_W`, `htid3_W`: `wcMainW_wf`'s `hhdr`,
  `hmP`, `hmH`, `htidW.1` and `htidW.2.2`.
-/
import Spike.Lib.A64WakeStartPlaceLy
import Spike.Lib.A64WakeOwn2
import Spike.Lib.A64WakeWcSp3Seg

namespace Spike.Lib.A64.WakePh.LdFacts

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Rt.Reserve (ntA)
open Spike.Lib.A64.Flow.WakeWc (t2)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceW`. -/
local notation "Ly" => RuntimeLayout.ofPlaceW hp i

/-- Two words apart are distinct. -/
private theorem ne_of_sep {a b : BitVec 64} (h : Scc.Cert.Rt.A64.WordSep a b) : a ≠ b := fun he => by
  unfold Scc.Cert.Rt.A64.WordSep at h; rw [he] at h; omega

/-- **A word of A13's `spawnWords`** is none of the four counters and
`scc_rt_nthreads` (A13's separations), and is mapped (`wordOk`). -/
theorem spawn_fact (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) {a : BitVec 64}
    (ha : a ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA) (w : Bool) :
    a ∉ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab] ∧
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) w ⟨a, 8⟩ = true := by
  have hnt := StartPlaceLy.ntA_W hp i hA13
  simp only [Scc.Cert.Spawn.A64.a13data, Bool.and_eq_true, List.all_cons, List.all_eq_true,
    decide_eq_true_eq, List.pairwise_cons] at hA13
  have hs : ∀ b ∈ (Ly).rtWords, a ≠ b := fun b hb => ne_of_sep (hA13.1.1.1.2.2 a ha b hb)
  have hn : a ≠ ntA (Ly).lab := fun he => ne_of_sep (hA13.1.2.1 a ha) (hnt ▸ he).symm
  have hw := hA13.1.1.1.1.2.2 a ha
  simp only [Scc.Cert.Rt.A64.wordOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true] at hw
  refine ⟨?_, Spike.Lib.A64Consumer.mapped_K0_of_mem fun j hj => hw.2 j hj⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨hs _ (Ly).pn_mem, hs _ (Ly).lock_mem, hs _ (Ly).freeN_mem, hs _ (Ly).next_mem, hn⟩

/-- The second TCB's header is a word of `spawnWords`. -/
theorem hdr_mem : (Ly).pinA + 80#64 + 16#64 ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨2, List.mem_range.2 (by decide), by rw [BitVec.add_assoc]; rfl⟩

/-- The second TCB's id word is a word of `spawnWords`. -/
theorem tid_mem : t2 (Ly).lab + 56#64 ∈ Scc.Cert.Spawn.A64.spawnWords (Ly).pinA :=
  List.mem_map.2 ⟨10, List.mem_range.2 (by decide), by
    show _ = Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 104#64 + 56#64
    rw [(Ly).lab_pin, BitVec.add_assoc]; rfl⟩

/-- **`hhdr`**: the second TCB's header apart from the counters and `ntA`. -/
theorem hhdr_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    (Ly).pinA + 80#64 + 16#64 ∉ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab] :=
  (spawn_fact hp i hA13 (hdr_mem hp i) true).1

/-- **`hmP`**: `scc_rt_pinned_next` mapped writable (A8's `words_mapped`). -/
theorem hmP_W : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨(Ly).pnA, 8⟩ = true :=
  Spike.Lib.A64Consumer.mapped_K0_of_mem ((Ly).words_mapped _ (Ly).pn_mem).2.2

/-- **`hmH`**: the second TCB's header mapped writable. -/
theorem hmH_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨(Ly).pinA + 96#64, 8⟩ = true :=
  BitVec.add_assoc (Ly).pinA 80#64 16#64 ▸ (spawn_fact hp i hA13 (hdr_mem hp i) true).2

/-- **`htidW.1`**: the second TCB's id word mapped writable. -/
theorem htid1_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (Ly).Λ) true ⟨t2 (Ly).lab + 56#64, 8⟩ = true :=
  (spawn_fact hp i hA13 (tid_mem hp i) true).2

/-- **`htidW.2.2`**: the second TCB's id word is none of `own2a`'s words. -/
theorem htid3_W (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true) :
    ∀ w, (⟨t2 (Ly).lab + 56#64, 8⟩, w) ∉ Spike.Lib.A64.WakePh.own2a (Ly) (ntA (Ly).lab) 0 := by
  intro w hw
  have h := (spawn_fact hp i hA13 (tid_mem hp i) true).1
  simp only [Spike.Lib.A64.WakePh.own2a, Spike.Lib.A64.WakePh.ownV, List.mem_cons, List.not_mem_nil, or_false,
    Prod.mk.injEq, Loc.mk.injEq] at hw h
  rcases hw with ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ | ⟨⟨e, -⟩, -⟩ <;> exact h (by simp [e])

end Spike.Lib.A64.WakePh.LdFacts

/-- info: 'Spike.Lib.A64.WakePh.LdFacts.hhdr_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.LdFacts.hhdr_W

/-- info: 'Spike.Lib.A64.WakePh.LdFacts.hmP_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.LdFacts.hmP_W

/-- info: 'Spike.Lib.A64.WakePh.LdFacts.hmH_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.LdFacts.hmH_W

/-- info: 'Spike.Lib.A64.WakePh.LdFacts.htid1_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.LdFacts.htid1_W

/-- info: 'Spike.Lib.A64.WakePh.LdFacts.htid3_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.LdFacts.htid3_W

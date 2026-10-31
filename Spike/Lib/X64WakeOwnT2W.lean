/-
**The worker's TCB word off `ownGX`'s words at wake's placed layout**
(x86-64): `X64WakeOwnT2.tcb2_notGX`'s / `ownSW_disj`'s premise
`hW` at `RuntimeLayout.ofPlaceWX h i`, `a` the nthreads word
(`Rt.Reserve.ntA`):

- `tcb2_mem_spawnWords`: `tcb2 = pinA + 104` is A13's fourth spawn word
  (`spawnWords pinA`, `80 + 8 * 3`).
- `tcb2_notG_W`: `tcb2` is none of the counters (A13's data part keeps every
  spawn word clear of the runtime's words) and not `ntA` (A13's spawn words
  are pairwise separate, `ntA` their head).

Deviations: none from the plan; like `X64WakeOwnSW.tcbM_ne_ntA_W` the
separation is A13's data part (`hA13`), `PlaceWX` has no A13.
-/
import Spike.Lib.X64WakeOwnT2
import Spike.Lib.X64WakeOwnSW

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Rt.Reserve (ntA)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX h i

private theorem ne_of_sep' {a b : BitVec 64} (hs : Scc.Cert.Rt.X64.WordSep a b) : a ≠ b := fun he => by
  subst he; unfold Scc.Cert.Rt.X64.WordSep at hs; omega

/-- **`tcb2` is a spawn word** (A13's `spawnWords`, index 3). -/
theorem tcb2_mem_spawnWords (L : RuntimeLayout) : tcb2 L ∈ Scc.Cert.Spawn.X64.spawnWords L.pinA := by
  unfold Scc.Cert.Spawn.X64.spawnWords
  exact List.mem_map.mpr ⟨3, List.mem_range.mpr (by decide), rfl⟩

/-- **The worker's TCB word is none of the counters nor `scc_rt_nthreads`**
at `ofPlaceWX`, given A13's data part. -/
theorem tcb2_notG_W (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) :
    tcb2 (Ly) ∉ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA, ntA (Ly).lab] := by
  have hnt := ntA_W h i hA13
  have hm := tcb2_mem_spawnWords (Ly)
  simp only [Scc.Cert.Spawn.X64.a13data, Bool.and_eq_true, decide_eq_true_eq] at hA13
  obtain ⟨⟨⟨⟨⟨-, -⟩, hold⟩, -⟩, hpw⟩, -⟩ := hA13
  have hsep : ∀ b ∈ (Ly).rtWords, Scc.Cert.Rt.X64.WordSep (tcb2 (Ly)) b := by
    intro b hb
    have := List.all_eq_true.mp hold (tcb2 (Ly)) (List.mem_cons_of_mem _ hm)
    exact of_decide_eq_true (List.all_eq_true.mp this b hb)
  have hnt' : tcb2 (Ly) ≠ ntA (Ly).lab := by
    rw [hnt]
    exact (ne_of_sep' ((List.pairwise_cons.mp hpw).1 _ hm)).symm
  simp only [List.mem_cons, List.mem_nil_iff, or_false, not_or]
  exact ⟨ne_of_sep' (hsep _ (Ly).pn_mem), ne_of_sep' (hsep _ (Ly).lock_mem),
    ne_of_sep' (hsep _ (Ly).freeN_mem), ne_of_sep' (hsep _ (Ly).next_mem), hnt'⟩

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.tcb2_mem_spawnWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb2_mem_spawnWords

/-- info: 'Spike.Lib.X64.WakePh.tcb2_notG_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.tcb2_notG_W

/-
**The spinlock's ghost locations and initial facts, ISA-neutral**
.

- `ghostSys N l c`: the system with the ghost locations of
  `SwpPublic.ghostParams` (`K j = ⟨0, 2j + 5⟩`, `F j = ⟨0, 2j + 6⟩`);
  `ghostSys_spinLocs`: its `SpinLocs` from `l ≠ c`.
- `threadRes_fresh'`: the initial thread resource is `Fresh`.
- `world_spinGhost'`: the `World` facts of the initial ghost.
- `spin_counter_core`: the shared shell of the spinlock counter
  theorems (zero threads, `l ≠ c`, `Spinlock.adequacy`); `spinGhost_pure_lk`,
  `spinGhost_pure_c`: the initial ghost's purity facts.

Used by the CAS lock (`CasSmoke.cas_counter_envG`, `EnvG/CasPublic.lean`)
and, through aliases, by the x64 xchg lock (`EnvG/X64SpinPublicG.lean`).
-/
import Kraken.Promising.SLR.SpinCommon
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

/-! ## The ghost locations and the initial state -/

/-- The system with the ghost locations chosen as in
`SwpPublic.ghostParams`: `K j = ⟨0, 2j + 5⟩`, `F j = ⟨0, 2j + 6⟩` (never 4
bytes wide). -/
def ghostSys (N : Nat) (l c : BitVec 64) : Sys where
  N := N
  Lk := ⟨l, 4⟩
  C := ⟨c, 4⟩
  K j := ⟨0, 2 * j + 5⟩
  F j := ⟨0, 2 * j + 6⟩

/-- The ghost fields of `SpinLocs` hold for `ghostSys`; only `l ≠ c` is
needed. -/
theorem ghostSys_spinLocs {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) :
    SpinLocs (ghostSys N l c).N (ghostSys N l c).Lk (ghostSys N l c).C (ghostSys N l c).K (ghostSys N l c).F where
  lk_c h := hlc (congrArg Loc.addr h)
  k_lk j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this
  k_c j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this
  f_lk j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this
  f_c j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this
  k_f i _ j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this; omega
  k_inj i _ j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this; omega
  f_inj i _ j _ h := by have := congrArg Loc.bytes h; simp [ghostSys] at this; omega

/-- The initial thread resource is `Fresh`. -/
theorem threadRes_fresh' {P : Sys} {tid : Nat} {m : Memory} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (htid : tid < P.N) : Fresh P tid (threadRes m P.N P.Lk P.K P.F tid) := by
  have h1 := hL.k_lk tid htid
  have h2 := hL.f_lk tid htid
  have h3 := hL.k_f tid htid tid htid
  have hN : (0 : Rat) ≤ 1 / (P.N : Rat) := Rat.le_of_lt (one_div_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) htid))
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [threadRes, Res.initOf, Perm.init, threadFrac, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      ite_true, ite_false] <;> grind

/-- The world facts of the spinlock's initial ghost. -/
theorem world_spinGhost' {P : Sys} {pool : Res} (hLC : P.Lk ≠ P.C) : World P (spinGhost P.Lk P.φ pool) :=
  ⟨spinGhost_rel_Lk, fun v => by simp only [spinGhost, Ne.symm hLC, ite_false]; exact Pred.emp_pure v,
    0, spinGhost_upd_Lk, by rw [spinGhost_acqTab_length]; exact Nat.zero_lt_one, spinGhost_acqPred_zero⟩

/-! ## The counter theorem's shared shell -/

/-- **`counter = N` for a spinlock on `ghostSys N l c`, from the run's
final facts**: the shared shell of the ten spinlock counter
theorems (`CasSmoke.cas_counter_envG`, `SwplLock.swpl_counter_envG`, their
`…_runner` forms, and the x64 `x64_spin…`/`x64_cmpx…` public, verbatim and
runner forms). The disjointness gives `l ≠ c`; no thread gives the initial
counter; otherwise `hrun` (a `final_of_…` theorem at the initial erasure
`erase_init_lockPred`) delivers the final erasure, a ghost above the initial
one and every thread's `Post`, and `Spinlock.adequacy` counts. -/
theorem spin_counter_core {I : ISA} {A : Arch} {fuel : Nat} (N : Nat) {l c : BitVec 64}
    (hdisj : Decls.overlaps l 4 c 4 = false) {states : List I.State} {initMem : List (Loc × Val)}
    (hN : states.length = N) (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    {cfg : Config I} (hc : Reachable A fuel (Config.init states initMem) cfg) (hf : cfg.final = true)
    (hrun : l ≠ c → 0 < N → (∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) cfg →
        (spinGhost ⟨l, 4⟩ (lockPred N ⟨l, 4⟩ ⟨c, 4⟩ (ghostSys N l c).K (ghostSys N l c).F)
          (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)).Le g' →
        cfg.threads.size = states.length → (∀ tid, cfg.Done tid → Post N ⟨l, 4⟩ (ghostSys N l c).K (rF' tid)) →
        cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) → cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N := by
  have hlc : l ≠ c := by intro h; rw [h] at hdisj; simp [Decls.overlaps] at hdisj
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · obtain rfl : states = [] := List.length_eq_zero_iff.mp hN
    obtain rfl : cfg = Config.init [] initMem := Reachable.eq_of_init_nil hc
    simpa [Memory.finalVal, Config.init] using hC0
  exact hrun hlc hN0 fun _ _ E' hle hsize hB =>
    adequacy E' hf (hsize.trans hN) hN0 hle spinGhost_rel_Lk spinGhost_upd_Lk
      (by rw [spinGhost_acqTab_length]; exact Nat.zero_lt_one) spinGhost_acqPred_zero poolSpec_lockPred
      fun i hi => hB i (Config.final_done hf (by rw [hsize, hN]; exact hi))

/-- The initial ghost's purity predicate at the lock: `lockPred`'s values
(the nonzero 32-bit ones) are pure. -/
theorem spinGhost_pure_lk {N : Nat} {l c : BitVec 64} (pool : Res) (v : Val) (hv : BitVec.setWidth 32 v ≠ 0) :
    Pred.Pure ((spinGhost (ghostSys N l c).Lk (ghostSys N l c).φ pool).rel ⟨l, 4⟩) v := by
  show Pred.Pure ((spinGhost (ghostSys N l c).Lk _ _).rel (ghostSys N l c).Lk) v
  rw [spinGhost_rel_Lk]; exact lockPred_pure hv

/-- The initial ghost's purity predicate at the counter is trivial. -/
theorem spinGhost_pure_c {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (pool : Res) (v : Val) :
    Pred.Pure ((spinGhost (ghostSys N l c).Lk (ghostSys N l c).φ pool).rel ⟨c, 4⟩) v := by
  have hLc : (⟨c, 4⟩ : Loc) ≠ (ghostSys N l c).Lk := Ne.symm (ghostSys_spinLocs (N := N) hlc).lk_c
  simp only [spinGhost, hLc, ite_false]; exact Pred.emp_pure v

end Kraken.Promising.SLR.EnvG.CasSmoke

/-
**The AArch64 spinlock counter** (`spinlock_swp2.kl`'s `worker`,
`swpWorker`) under `Arch.armv8`: `N` workers end with `counter = N` at every
reachable final configuration.

`swp_counter` assembles `counter_of_theorem1Pure`:

- Theorem 1′'s scope (`NTFree`) by `Config.ntFree_armv8`;
- (O5) by `swp_promisePure` (`SLR/SwpPure.lean`);
- the workers' `NPSafe` by `swp_npsafeX` (`SLR/SwpRuleX.lean`) from the
  initial `Inv` (`swp_inv_init`) at the initial resources `threadRes` and
  ghost `spinGhost` of `counter_init` (`SLR/SpinInitRes.lean`, which
  discharges initial erasure and `PoolSpec`), modulo the open cell
  obligations `HardCellsX`.

Open hypotheses: `HardCellsX` (the resource cells, `prepay` and the lift);
`swp_counter_armv8_of_cells` discharges Theorem 1′ by `theorem1IIPure`
(`SLR/Theorem1Final.lean`). `SLR/SwpFinal.lean` discharges `HardCellsX`
(`swp_counter_armv8`).
-/
import Kraken.Promising.SLR.SwpRuleX
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.Theorem1Final

namespace Kraken.Promising.SLR.SwpInv

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.AArch64.Examples.InvEnv
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SwpTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout swpWorker)]

omit layout hv in
theorem init_get?_thread {states : List isa.State} {initMem : List (Loc × Val)} {i : Nat} {t : Thread isa}
    (h : (Config.init states initMem : Config isa).threads[i]? = some t) :
    ∃ s, states[i]? = some s ∧ t = Thread.init s :=
  Config.init_get?_thread h

/-- **The initial invariant** of a worker at the start of the text with a
`Fresh` resource. -/
theorem swp_inv_init {P : Params} {tid : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {r : Res} {g : Ghost} {s : isa.State} (hs : states[tid]? = some s) (hF : Frame P s) (hp : AtPos s 0)
    (hW : World P g) (hr : Fresh P tid r) (hL : LockWritesIn P r (Config.init states initMem).mem) :
    Inv P tid True (Config.init states initMem) r g := by
  refine ⟨hW, Thread.init s, ?_, hF, hL, 1, ?_, ⟨hr, fun f hf => ?_⟩, fun h => absurd h (by decide),
    fun f hf => ?_⟩
  · simp [Config.init, hs]
  · show s.st.2 = _
    rw [addrOf_label (i := 0) (l := "worker") rfl]; exact hp
  · simp [Thread.init, Views.getFwd] at hf
  · simp [Thread.init, Views.getFwd] at hf

omit layout hv in
/-- The initial thread resource is `Fresh`. -/
theorem threadRes_fresh {P : Params} {tid : Nat} {m : Memory} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (htid : tid < P.N) : Fresh P tid (threadRes m P.N P.Lk P.K P.F tid) := by
  have h1 := hL.k_lk tid htid
  have h2 := hL.f_lk tid htid
  have h3 := hL.k_f tid htid tid htid
  have hN : (0 : Rat) ≤ 1 / (P.N : Rat) := by
    rw [Rat.div_def, Rat.one_mul, Rat.inv_def]
    exact Rat.divInt_nonneg (by omega) (Rat.num_nonneg.mpr Rat.natCast_nonneg)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [threadRes, Res.initOf, Perm.init, threadFrac, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3,
      ite_true, ite_false] <;> grind

omit layout hv in
/-- The initial thread resource writes only the initial messages. -/
theorem threadRes_lockWritesIn {P : Params} {tid : Nat} {m : Memory} :
    LockWritesIn P (threadRes m P.N P.Lk P.K P.F tid) m := by
  intro p hp
  have : p.2 = 0 := by
    obtain ⟨-, rfl⟩ := hp
    rfl
  rw [this]; exact Nat.zero_le _

omit layout hv in
/-- The world facts of the spinlock's initial ghost. -/
theorem world_spinGhost {P : Params} {pool : Res} (hLC : P.Lk ≠ P.C) :
    World P (spinGhost P.Lk P.φ pool) :=
  ⟨spinGhost_rel_Lk, fun v => by simp only [spinGhost, Ne.symm hLC, ite_false]; exact Pred.emp_pure v,
    0, spinGhost_upd_Lk, by rw [spinGhost_acqTab_length]; exact Nat.zero_lt_one, spinGhost_acqPred_zero⟩

/-- **`counter = N` for the AArch64 spinlock workers** under `Arch.armv8`,
from the initial state of `SLR/SpinInitRes.lean` (`counter_init`), modulo
Theorem 1′ and the resource cells (`HardCellsX`). -/
theorem swp_counter {fuel : Nat} (hT : Theorem1IIPure (I := isa) Arch.armv8 fuel) (P : Params)
    (hL : SpinLocs P.N P.Lk P.C P.K P.F) (H : ∀ tid, tid < P.N → HardCellsX P Arch.armv8 tid)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ (tid : Nat) (s : isa.State), states[tid]? = some s → Frame P s ∧ AtPos s 0)
    (hN : states.length = P.N) (hN0 : 0 < P.N)
    (hC0 : (Config.init states initMem).mem.initVal P.C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal P.Lk = 0)
    {c : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal P.C = BitVec.ofNat 128 P.N := by
  have hne : P.c ≠ P.l := fun h => hL.lk_c (by simp [Params.Lk, Params.C, h])
  refine counter_init hT hL hN hN0 hC0 hLk0 (fun _ hc' => Config.ntFree_armv8 hc') ?_ ?_ hc hf
  · refine swp_promisePure P hne (fun l v hb => ?_) (fun tid t ht => ?_)
    · by_cases hl : l = P.Lk
      · subst hl
        rw [spinGhost_rel_Lk]
        exact lockPred_pure fun hv => hb ⟨rfl, hv⟩
      · simp only [spinGhost, hl, ite_false]
        exact Pred.emp_pure v
    · obtain ⟨s, hs, rfl⟩ := init_get?_thread ht
      obtain ⟨hF, hp⟩ := hst tid s hs
      exact swpReach_start hF hp
  · intro tid htid n m
    obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
    obtain ⟨hF, hp⟩ := hst tid s hs
    refine swp_npsafeX P Arch.armv8 tid (H tid (hN ▸ htid)) n m
      ⟨swp_inv_init hs hF hp (world_spinGhost hL.lk_c) (threadRes_fresh hL (hN ▸ htid))
        threadRes_lockWritesIn, fun ts h => absurd h (pend_init ts), fun t ht ts hts => ?_⟩
    obtain ⟨s', -, rfl⟩ := init_get?_thread ht
    cases hts

/-- **`counter = N` for the AArch64 spinlock workers** under `Arch.armv8`
with Theorem 1′ discharged (`theorem1IIPure`), modulo the resource cells
(`HardCellsX`). -/
theorem swp_counter_armv8_of_cells {fuel : Nat} (P : Params) (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (H : ∀ tid, tid < P.N → HardCellsX P Arch.armv8 tid) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ (tid : Nat) (s : isa.State), states[tid]? = some s → Frame P s ∧ AtPos s 0)
    (hN : states.length = P.N) (hN0 : 0 < P.N)
    (hC0 : (Config.init states initMem).mem.initVal P.C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal P.Lk = 0)
    {c : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal P.C = BitVec.ofNat 128 P.N :=
  swp_counter (theorem1IIPure Arch.armv8 fuel) P hL H hst hN hN0 hC0 hLk0 hc hf

end Kraken.Promising.SLR.SwpInv

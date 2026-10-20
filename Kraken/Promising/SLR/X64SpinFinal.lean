/-
**The x64 spinlock counter** (`X64SpinTrees.spinWorker`, x64 `spinlock2`)
under `Arch.tso`: `N` workers end with `counter = N` at every reachable final
configuration, modulo the open resource cells `HardCellsX`
(`SLR/X64SpinRule.lean`). The x64 twin of `SLR/SwpAdequacy.lean`.

`x64_counter_spin_of_cells` assembles `Spinlock.x64_counter_init`
(`SLR/X64SpinAdequacy.lean`):

- Theorem 1′ by `theorem1IIPure` (`SLR/Theorem1Final.lean`);
- its scope and (O5) inside `x64_counter_init` (`spinWorker_ntFree`,
  `spin_promisePure`);
- the workers' `NPSafe` by `spin_npsafeX` from the initial `InvX`
  (`spin_inv_init`, no pending marks) at the initial resources `threadRes`
  and ghost `spinGhost`.
-/
import Kraken.Promising.SLR.X64SpinRule
import Kraken.Promising.SLR.X64SpinAdequacy
import Kraken.Promising.SLR.Theorem1Final

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

omit layout hv in
theorem init_get?_thread {states : List isa.State} {initMem : List (Loc × Val)} {i : Nat} {t : Thread isa}
    (h : (Config.init states initMem : Config isa).threads[i]? = some t) :
    ∃ s, states[i]? = some s ∧ t = Thread.init s :=
  Config.init_get?_thread h

/-- **The initial invariant** of a worker at the start of the text with a
`Fresh` resource. -/
theorem spin_inv_init {P : Params} {tid : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    {r : Res} {g : Ghost} {s : isa.State} (hs : states[tid]? = some s) (hF : Frame P s) (hp : AtPos s 0)
    (hW : World P.sys g) (hr : FreshN P tid r)
    (hL : LockWritesIn P.sys r (Config.init states initMem).mem) :
    Inv P tid True (Config.init states initMem) r g := by
  refine ⟨hW, Thread.init s, ?_, hF, hL, 1, ?_, ⟨hr, fun f hf => ?_⟩,
    fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
  · simp [Config.init, hs]
  · show s.st.2 = _
    rw [addrOf_label (i := 0) (l := "worker") rfl]; exact hp
  · simp [Thread.init, Views.getFwd] at hf

omit layout hv in
/-- The initial thread resource is `Fresh`. -/
theorem threadRes_fresh {P : Params} {tid : Nat} {m : Memory} (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (htid : tid < P.N) : Fresh P.sys tid (threadRes m P.N P.Lk P.K P.F tid) := by
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
    LockWritesIn P.sys (threadRes m P.N P.Lk P.K P.F tid) m := by
  intro p hp
  have : p.2 = 0 := by
    obtain ⟨-, rfl⟩ := hp
    rfl
  rw [this]; exact Nat.zero_le _

omit layout hv in
/-- The world facts of the spinlock's initial ghost. -/
theorem world_spinGhost {P : Params} {pool : Res} (hLC : P.Lk ≠ P.C) :
    World P.sys (spinGhost P.Lk P.φ pool) :=
  ⟨spinGhost_rel_Lk, fun v => by simp only [spinGhost, Ne.symm hLC, ite_false]; exact Pred.emp_pure v,
    0, spinGhost_upd_Lk, by rw [spinGhost_acqTab_length]; exact Nat.zero_lt_one, spinGhost_acqPred_zero⟩

/-- **`counter = N` for the x64 spinlock workers** under `Arch.tso`, from the
initial state of `SLR/SpinInitRes.lean`, modulo the resource cells
(`HardCellsX`). Theorem 1′ is `theorem1IIPure`. -/
theorem x64_counter_spin_of_cells {fuel : Nat} (P : Params) (hL : SpinLocs P.N P.Lk P.C P.K P.F)
    (H : ∀ tid, tid < P.N → HardCellsX P Arch.tso tid) {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ (tid : Nat) (s : isa.State), states[tid]? = some s → Frame P s ∧ AtPos s 0)
    (hN : states.length = P.N) (hN0 : 0 < P.N)
    (hC0 : (Config.init states initMem).mem.initVal P.C = 0)
    (hLk0 : (Config.init states initMem).mem.initVal P.Lk = 0)
    {c : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) c) (hf : c.final = true) :
    c.mem.finalVal P.C = BitVec.ofNat 128 P.N := by
  have hs : ∀ s ∈ states, SpinPc s := by
    intro s hs
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hs
    obtain ⟨hF, hp⟩ := hst i _ (List.getElem?_eq_getElem hi)
    exact ⟨hF.exe, hF.decls, hp ▸ pcOk_addrOf (by omega)⟩
  refine x64_counter_init (theorem1IIPure Arch.tso fuel) hs hL hN hN0 hC0 hLk0 ?_ hc hf
  intro tid htid n m
  obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
  obtain ⟨hF, hp⟩ := hst tid s hs
  refine spin_npsafeX P Arch.tso tid (H tid (hN ▸ htid)) n m
    ⟨spin_inv_init hs hF hp (world_spinGhost hL.lk_c) ⟨threadRes_fresh hL (hN ▸ htid), hN ▸ htid⟩
      threadRes_lockWritesIn, fun ts h => absurd h (pend_init ts), fun t ht ts hts => ?_⟩
  obtain ⟨s', -, rfl⟩ := init_get?_thread ht
  cases hts

end Kraken.Promising.SLR.X64SpinInv

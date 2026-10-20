/-
**The CAS spinlock on `EnvG`, the public theorem**:
`cas_counter_envG`, `counter = N` for `N` CAS spinlock workers
(`casTtasWorker`, the worker of `spinlock_cas2.kl`) under `Arch.armv8`, in
the shape of `SwpPublic.swp_counter_public`, with no extra hypotheses.

- **Start** (`casInv_init`): the rule's invariant at `Config.init` from
  `StartState`: `invG_init` at `σInit` with the spinlock's initial resources
  and ghost (`threadRes`, `spinGhost … (poolRes …)`, `SLR/SpinInitRes.lean`),
  `QA64` from `casWorker_envG` by `qa64_of_partialTripleEnv`.
- **`NPSafe`**: `NPSafe.of_ruleRX` at `casRule_envG` (`EnvG/CasLink.lean`).
- **Assembly** as `MpEnvGPublic2.mp_envG'`: `final_of_relPureSafely`
  (purity from `casPureSpec_holds`, `EnvG/CasRelPure.lean`), initial erasure
  `erase_init_lockPred`, and the counting argument `Spinlock.adequacy`
  (`SLR/Adequacy.lean`) at the final erasure.

Local copies (the originals are stated over the AArch64 SWP `Params`):
`ghostSys`/`ghostSys_spinLocs` (`SwpPublic.ghostParams(_spinLocs)`),
`threadRes_fresh'` (`SwpInv.threadRes_fresh`), `world_spinGhost'`
(`SwpInv.world_spinGhost`), `reachable_nil'` (private in `SwpPublic`). The
first four are ISA-neutral and live in `EnvG/SpinStart.lean` (moved
unchanged; the x64 spinlock aliases them).
-/
import Kraken.Promising.SLR.EnvG.CasLink
import Kraken.Promising.SLR.EnvG.CasRelPure
import Kraken.Promising.SLR.EnvG.RelPureEnvA64
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.EnvG.SpinStart

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

/-! ## The ghost locations and the initial state -/

/-- The initial thread resource holds no counter share. -/
theorem threadRes_C {P : Sys} {tid : Nat} {m : Memory} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (htid : tid < P.N) :
    ((threadRes m P.N P.Lk P.K P.F tid).wr P.C).q = 0 := by
  simp only [threadRes, Res.initOf, Perm.init, threadFrac, Ne.symm hL.lk_c, Ne.symm (hL.k_c tid htid),
    Ne.symm (hL.f_c tid htid), ite_false]
  grind

/-- The initial thread resource writes only the initial message of the
lock, `0`. -/
theorem threadRes_lkZero {P : Sys} {tid : Nat} {m : Memory} (h0 : m.initVal P.Lk = 0) :
    LkZero P (threadRes m P.N P.Lk P.K P.F tid) := by
  rintro p ⟨-, rfl⟩
  exact h0

/-! ## The start -/

section Start

variable [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)]

/-- **The worker's initial invariant** (thread `tid` of `N`). -/
theorem casInv_init {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N)
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartState l c s) (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (casRule_envG (ghostSys N l c) tid).Inv True (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes (Config.init states initMem).mem N ⟨c, 4⟩ (ghostSys N l c).K)) := by
  letI : CodeEnv := ⟨layout casTtasWorker⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  refine invG_init hs rfl (qa64_of_partialTripleEnv
    (casWorker_envG (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc hst.pc
    ⟨0, hst.x0, hst.x1, hst.dl, hst.dc, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid,
      threadRes_C hL htid, by simp [σInit, Views.getFwd], threadRes_lkZero hLk0⟩)

end Start

/-! ## The theorem -/

/-- With no threads, nothing steps: the initial configuration is the only
reachable one (a copy of `SwpPublic`'s private `reachable_nil`). -/
theorem reachable_nil' {A : Arch} {fuel : Nat} {initMem : List (Loc × Val)} {cfg : Config isa}
    (h : Reachable A fuel (Config.init [] initMem) cfg) : cfg = Config.init [] initMem := by
  cases h with
  | refl => rfl
  | step hs _ => simp [succs, succsL, Config.init] at hs

/-- **`counter = N` for the AArch64 CAS spinlock workers, on `EnvG`**, public
form (the shape of `SwpPublic.swp_counter_public`; see there for what is and
is not covered: undeclared 4-byte footprints, `hdisj` for the model's
mixed-size gap, final configurations only, `N < 2 ^ 32` for the 32-bit
counter).

For every valid layout of `casTtasWorker` (the worker of
`spinlock_cas2.kl`: `casa` acquire, `ldr` test-and-test-and-set spin, plain
increment, `stlr wzr` release), every number of threads `N < 2 ^ 32` and all
addresses `l`, `c` whose 4-byte words are disjoint: if `states` consists of
`N` threads, each at the start of the worker with `X0 = l`, `X1 = c`
(`StartState`), and the initial memory has the lock and counter words at
`0`, then every configuration `Reachable` under `Arch.armv8` that is final
has the counter word at `N`.

Proved by the EnvG route: one `vcgen` call per worker (`casWorker_envG`),
`ThreadRuleRX.ofSafelyEnvG` (`casRule_envG`), purity by `vcgen`
(`casPureSpec_holds`), `final_of_relPureSafely` and `Spinlock.adequacy`.
No-fault for the worker's rule: `casRule_envG_noFault`. -/
theorem cas_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout casTtasWorker)] {fuel : Nat}
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartState l c s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafely Arch.armv8 fuel (B := fun _ r _ => Post N ⟨l, 4⟩ (ghostSys N l c).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N)
      (fun _ hc' => Config.ntFree_armv8 hc')
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0) pend_init (fun _ => casPureSpec _)
      (fun tid s hs => casPureSpec_holds (spinGhost_pure_lk _) (spinGhost_pure_c hlc _)
        (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (casInv_init hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.SLR.EnvG.CasSmoke

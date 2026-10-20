/-
**The x64 xchg spinlock on `EnvG`, the public theorem**: `x64_spin_counter_envG`, `counter = N` for `N` x64 spinlock workers
(`spinWorkerG`, the worker of `spinlock2.kl`) under `Arch.tso`, in the shape
of `X64SpinPublic.x64_counter_public`.

- **Start** (`spinInv_init`): the rule's invariant at `Config.init` from
  `StartStateG`: `invGRX_init` at `σInitX` with the spinlock's initial
  resources and ghost (`threadRes`, `spinGhost … (poolRes …)`,
  `SLR/SpinInitRes.lean`), `QX64` from `spinWorkerG_envG` by
  `qx64_of_partialTripleEnv`.
- **`NPSafe`**: `NPSafe.of_ruleRX` at `spinRule_envG` (`EnvG/X64SpinLink.lean`).
- **Assembly** as `X64MpPublic.x64_mp_public`: `final_of_relPureSafelyQX_tso`
  (scope and purity at once from the all-release specification
  `spinNoNTSpec`, `EnvG/X64SpinRelPure.lean`), initial erasure
  `erase_init_lockPred`, and the counting argument `Spinlock.adequacy`
  (`SLR/Adequacy.lean`) at the final erasure, as `CasPublic.cas_counter_envG`.

Local copies of `CasPublic` (an AArch64-importing file): `ghostSys`,
`ghostSys_spinLocs`, `threadRes_fresh'`, `world_spinGhost'`,
`reachable_nil'`. The first four are now aliases of the ISA-neutral
originals in `EnvG/SpinStart.lean`; `reachable_nil'` stays a copy
(its statement is about x64 `Config isa`).
-/
import Kraken.Promising.SLR.EnvG.X64SpinLink
import Kraken.Promising.SLR.EnvG.X64SpinRelPure
import Kraken.Promising.SLR.SpinInitRes
import Kraken.Promising.SLR.EnvG.SpinStart
import Kraken.Promising.SLR.EnvG.Alias

namespace Kraken.Promising.X64.EnvG.SpinPublicG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.SpinRelPure
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

/-! ## The ghost locations and the initial state (copies of `CasPublic`) -/

/-! `ghostSys`, `ghostSys_spinLocs`, `threadRes_fresh'`, `world_spinGhost'`:
statement-preserving aliases (`hoist_alias`, `EnvG/Alias.lean`) of the
ISA-neutral originals in `EnvG/SpinStart.lean`. -/

hoist_alias [
  Kraken.Promising.SLR.EnvG.CasSmoke.ghostSys ↦ Kraken.Promising.X64.EnvG.SpinPublicG.ghostSys,
  Kraken.Promising.SLR.EnvG.CasSmoke.ghostSys_spinLocs ↦ Kraken.Promising.X64.EnvG.SpinPublicG.ghostSys_spinLocs,
  Kraken.Promising.SLR.EnvG.CasSmoke.threadRes_fresh' ↦ Kraken.Promising.X64.EnvG.SpinPublicG.threadRes_fresh',
  Kraken.Promising.SLR.EnvG.CasSmoke.world_spinGhost' ↦ Kraken.Promising.X64.EnvG.SpinPublicG.world_spinGhost']

/-- With no threads, nothing steps: the initial configuration is the only
reachable one (a copy of `SwpPublic`'s private `reachable_nil`). -/
theorem reachable_nil' {A : Arch} {fuel : Nat} {initMem : List (Loc × Val)} {cfg : Config isa}
    (h : Reachable A fuel (Config.init [] initMem) cfg) : cfg = Config.init [] initMem := by
  cases h with
  | refl => rfl
  | step hs _ => simp [succs, succsL, Config.init] at hs

/-- The initial thread resource writes only the lock's initial message `0`,
so `LkLe` holds at any views. -/
theorem threadRes_lkLe {P : Sys} {tid : Nat} {m : Memory} (h0 : m.initVal P.Lk = 0) (vs : Views) :
    LkLe P (threadRes m P.N P.Lk P.K P.F tid) vs :=
  LockVC.threadRes_lkLe h0 vs

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- **The x64 spinlock worker at its start**, with lock address `l` and
counter address `c`: the laid-out `spinWorkerG` at its first cell, no
declarations, `%rdi = l`, `%rsi = c`, and neither word's bytes in the
private memory (`Split`, the x64 link's side condition; it gives the
`Mem.loadInt … = none` facts of `X64SpinPublic.StartState`). -/
structure StartStateG (l c : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout spinWorkerG
  decls : s.decls = {}
  endPc : s.endPc = (layout spinWorkerG).addrOf spinWorkerG.length
  pc : s.st.2 = (layout spinWorkerG).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = l
  rsi : s.st.1.regs.get64 .rsi = c
  split : Split [(l, 4), (c, 4)] s.st.1.dmem

omit layout in
theorem split_dl {l c : BitVec 64} {m : DataMem} (h : Split [(l, 4), (c, 4)] m) : Mem.loadInt m l 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

omit layout in
theorem split_dc {l c : BitVec 64} {m : DataMem} (h : Split [(l, 4), (c, 4)] m) : Mem.loadInt m c 4 = none :=
  h.loadInt_none (by simp) (by decide) (by decide)

theorem StartStateG.frame {l c : BitVec 64} {s : State} (h : StartStateG l c s) : FrameX l c s.st.1 :=
  ⟨h.rdi, h.rsi, split_dl h.split, split_dc h.split⟩

variable [Executable.ValidLayout (layout spinWorkerG)]

/-- The initial ghost of `N` workers (`spinGhost` with the pool). -/
noncomputable abbrev ghost0 (N : Nat) (l c : BitVec 64) (m : Memory) : Ghost :=
  spinGhost ⟨l, 4⟩ (ghostSys N l c).φ (poolRes m N ⟨c, 4⟩ (ghostSys N l c).K)

/-- **The worker's initial invariant** (thread `tid` of `N`). -/
theorem spinInv_init {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N)
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartStateG l c s) (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (spinRule_envG (ghostSys N l c) tid l c (ghost0 N l c (Config.init states initMem).mem).rel).Inv True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (ghost0 N l c (Config.init states initMem).mem) := by
  letI : CodeEnv := ⟨layout spinWorkerG⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  refine invGRX_init hs rfl (qx64_of_partialTripleEnv
    (spinWorkerG_envG (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc
    hst.pc hst.split
    ⟨0, hst.frame, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_, threadRes_lkLe hLk0 _⟩)
  intro f hf
  simp [σInitX, Views.getFwd] at hf

end Start

/-! ## Scope and purity -/

/-- The worker's all-release specification. -/
noncomputable def spinNoNTSpec (layout : _root_.Layout) [Executable.ValidLayout (layout spinWorkerG)]
    (l c : BitVec 64) : RelPureSpecQX Arch.tso fun _ _ => False :=
  RelPureSpecQX.ofProgram (layout := layout) [(l, 4), (c, 4)] (spinS_le16 l c) spinWorkerG fun _ _ => ∃ _ : Nat, True

/-- **The all-release specification holds at a start state.** -/
theorem spinNoNTSpec_holds (layout : _root_.Layout) [Executable.ValidLayout (layout spinWorkerG)]
    {l c : BitVec 64} {s : isa.State} (h : StartStateG (layout := layout) l c s) :
    (spinNoNTSpec layout l c).Holds s := by
  letI : CodeEnv := ⟨layout spinWorkerG⟩
  exact RelPureSpecQX.holds_of_partialTripleEnv (layout := layout) (spinWorkerG_noNT (layout := layout) l c).uncount
    rfl h.exe h.decls h.endPc h.pc h.split ⟨0, h.frame⟩

/-! ## The theorem -/

/-- **`counter = N` for the x64 xchg spinlock workers under `Arch.tso`, on
`EnvG`**, public form (the shape of `X64SpinPublic.x64_counter_public`; see
there for what is and is not covered: undeclared 4-byte footprints, `hdisj`
for the model's mixed-size gap, final configurations only, `N < 2 ^ 32` for
the 32-bit counter).

For every valid layout of `spinWorkerG` (the worker of `spinlock2.kl`:
test-and-test-and-set with a plain-load spin, `xchgl` acquire, plain
increment, plain-store release `movl $0`), every number of threads
`N < 2 ^ 32` and all addresses `l`, `c` whose 4-byte words are disjoint: if
`states` consists of `N` threads, each at the start of the worker with
`%rdi = l`, `%rsi = c` and neither word in its private memory
(`StartStateG`), and the initial memory has the lock and counter words at
`0`, then every configuration `Reachable` under `Arch.tso` that is final has
the counter word at `N`.

Proved by the EnvG route: one `vcgen` call for the worker
(`spinWorkerG_envG`), `ThreadRuleRX.ofSafelyEnvGRX` (`spinRule_envG`), the
all-release specification by `vcgen` (`spinWorkerG_noNT`),
`final_of_relPureSafelyQX_tso` and `Spinlock.adequacy`. No-fault for the
worker's rule: `spinRule_envG_noFault`. -/
theorem x64_spin_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout spinWorkerG)] {fuel : Nat}
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateG l c s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  CasSmoke.spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyQX_tso fuel (B := fun _ r _ => Post N ⟨l, 4⟩ (ghostSys N l c).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N)
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0)
      pend_init (fun _ => spinNoNTSpec layout l c)
      (fun _ s hs => spinNoNTSpec_holds layout (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact NPSafe.of_ruleRX _ n m _ _ _ _
          (spinInv_init hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0))
      hc hf hfin

end Kraken.Promising.X64.EnvG.SpinPublicG

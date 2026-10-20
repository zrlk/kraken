/-
**The x64 `lock cmpxchg` spinlock on `EnvG`, the public theorem**
`x64_cmpx_counter_envG`, `counter = N` for `N` x64
`lock cmpxchg` spinlock workers (`cmpxWorkerG`, the worker of
`spinlock_cmpxchg2.kl`) under `Arch.tso`, in the shape of
`X64SpinPublicG.x64_spin_counter_envG`, **with the explicit hypothesis
`hchain : Theorem1FChain (I := isa) Arch.tso fuel`**.

Why the hypothesis: the acquire `lock cmpxchgl` is a release-kind RMW under
`Arch.tso` that may fail, so the worker's rule is a `ThreadRuleRXF`
(`EnvG/X64CmpxLink.lean`) and gives `NPSafeF`, not `NPSafe`. Theorem 1′ for
`NPSafeF` is the open `Theorem1FChain` (`EnvG/RmwFailRule.lean`), pending a
change to the chain. The instance needed is
exactly `Theorem1FChain (I := isa) Arch.tso fuel` (the x64 ISA, `Arch.tso`,
the `fuel` of the `Reachable` hypothesis), consumed by
`final_of_relPureSafelyQX_tsoF` at `B := fun _ r _ => Post …`. Once the
chain lands, `hchain` is discharged for every `fuel` and the theorem is
unconditional. **Closed**: `theorem1FChain`
(`EnvG/RmwFailChain.lean`) proves `Theorem1FChain`, and
`x64_cmpx_counter_envG'` (`EnvG/X64CmpxFinal.lean`) is the unconditional
theorem.

- **Start** (`cmpxInv_init`): `invGFX_init` at `σInitX` with the spinlock's
  initial resources and ghost, `QX64` from `cmpxWorkerG_envG`.
- **`NPSafeF`** (`cmpx_npSafeF`): `NPSafeF.of_ruleRXF` at `cmpxRule_envGF`.
- **No-fault**: `cmpxRule_envGF_noFault` (`NoFaultRuleF`, unconditional).
- **Assembly**: `final_of_relPureSafelyQX_tsoF` (the `F` copy of
  `final_of_relPureSafelyQX_tso`: `hchain` in place of `theorem1IIPure`,
  `promisePure_of_relWrites` and the all-release specification
  `cmpxNoNTSpec`; moved, same name, to `EnvG/RelPureEnvX64F.lean`),
  `erase_init_lockPred`, `Spinlock.adequacy`.

Reused from `X64SpinPublicG`: `ghostSys`, `ghostSys_spinLocs`,
`threadRes_fresh'`, `world_spinGhost'`, `reachable_nil'`, `threadRes_lkLe`,
`split_dl`, `split_dc`, `ghost0`.
-/
import Kraken.Promising.SLR.EnvG.X64CmpxLink
import Kraken.Promising.SLR.EnvG.X64CmpxRelPure
import Kraken.Promising.SLR.EnvG.X64SpinPublicG
import Kraken.Promising.SLR.EnvG.RelPureEnvX64F

namespace Kraken.Promising.X64.EnvG.CmpxPublic

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
open Kraken.Promising.X64.EnvG Kraken.Promising.X64.EnvG.Spin Kraken.Promising.X64.EnvG.SpinLink
open Kraken.Promising.X64.EnvG.Cmpx Kraken.Promising.X64.EnvG.CmpxLink Kraken.Promising.X64.EnvG.CmpxRelPure
open Kraken.Promising.X64.EnvG.SpinRelPure Kraken.Promising.X64.EnvG.SpinPublicG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon Kraken.Promising.SLR.EnvG.X64Spin

/-! ## The start -/

section Start

variable [layout : _root_.Layout]

/-- **The x64 `lock cmpxchg` spinlock worker at its start**
(`X64SpinPublicG.StartStateG` for `cmpxWorkerG`). -/
structure StartStateC (l c : BitVec 64) (s : State) : Prop where
  exe : s.exe = layout cmpxWorkerG
  decls : s.decls = {}
  endPc : s.endPc = (layout cmpxWorkerG).addrOf cmpxWorkerG.length
  pc : s.st.2 = (layout cmpxWorkerG).addrOf 0
  rdi : s.st.1.regs.get64 .rdi = l
  rsi : s.st.1.regs.get64 .rsi = c
  split : Split [(l, 4), (c, 4)] s.st.1.dmem

theorem StartStateC.frame {l c : BitVec 64} {s : State} (h : StartStateC l c s) : FrameX l c s.st.1 :=
  ⟨h.rdi, h.rsi, split_dl h.split, split_dc h.split⟩

variable [Executable.ValidLayout (layout cmpxWorkerG)]

/-- **The worker's initial invariant** (thread `tid` of `N`). -/
theorem cmpxInv_init {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N)
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartStateC l c s) (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) :
    (cmpxRule_envGF (ghostSys N l c) tid l c (ghost0 N l c (Config.init states initMem).mem).rel).Inv True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (ghost0 N l c (Config.init states initMem).mem) := by
  letI : CodeEnv := ⟨layout cmpxWorkerG⟩
  have hL := ghostSys_spinLocs (N := N) hlc
  have hN0 : 0 < N := Nat.lt_of_le_of_lt (Nat.zero_le _) htid
  refine invGFX_init hs rfl (qx64_of_partialTripleEnv
    (cmpxWorkerG_envG (ghostSys N l c) tid l c rfl rfl hL hN0 htid hN32).uncount rfl hst.exe hst.decls hst.endPc
    hst.pc hst.split
    ⟨0, hst.frame, world_spinGhost' hL.lk_c, threadRes_fresh' hL htid, ?_, threadRes_lkLe hLk0 _⟩)
  intro f hf
  simp [σInitX, Views.getFwd] at hf

/-- **`NPSafeF` for every worker at the initial configuration**
(`NPSafeF.of_ruleRXF` at `cmpxRule_envGF`). -/
theorem cmpx_npSafeF {N : Nat} {l c : BitVec 64} (hlc : l ≠ c) (hN32 : N < 2 ^ 32) {tid : Nat} (htid : tid < N)
    {states : List isa.State} {initMem : List (Loc × Val)} {s : isa.State} (hs : states[tid]? = some s)
    (hst : StartStateC l c s) (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0) (n m : Nat) :
    NPSafeF (model isa) Arch.tso (fun _ r _ => Post N ⟨l, 4⟩ (ghostSys N l c).K r) tid n m True
      (Config.init states initMem)
      (threadRes (Config.init states initMem).mem N ⟨l, 4⟩ (ghostSys N l c).K (ghostSys N l c).F tid)
      (ghost0 N l c (Config.init states initMem).mem) :=
  NPSafeF.of_ruleRXF _ n m _ _ _ _ (cmpxInv_init hlc hN32 htid hs hst hLk0)

end Start

/-! ## Scope and purity -/

/-- The worker's all-release specification. -/
noncomputable def cmpxNoNTSpec (layout : _root_.Layout) [Executable.ValidLayout (layout cmpxWorkerG)]
    (l c : BitVec 64) : RelPureSpecQX Arch.tso fun _ _ => False :=
  RelPureSpecQX.ofProgram (layout := layout) [(l, 4), (c, 4)] (spinS_le16 l c) cmpxWorkerG fun _ _ => ∃ _ : Nat, True

/-- **The all-release specification holds at a start state.** -/
theorem cmpxNoNTSpec_holds (layout : _root_.Layout) [Executable.ValidLayout (layout cmpxWorkerG)]
    {l c : BitVec 64} {s : isa.State} (h : StartStateC (layout := layout) l c s) :
    (cmpxNoNTSpec layout l c).Holds s := by
  letI : CodeEnv := ⟨layout cmpxWorkerG⟩
  exact RelPureSpecQX.holds_of_partialTripleEnv (layout := layout) (cmpxWorkerG_noNT (layout := layout) l c).uncount
    rfl h.exe h.decls h.endPc h.pc h.split ⟨0, h.frame⟩

/-! ## The theorem -/

/-- **`counter = N` for the x64 `lock cmpxchg` spinlock workers under
`Arch.tso`, on `EnvG`**, public form, **conditional on
`Theorem1FChain (I := isa) Arch.tso fuel`** (`hchain`; see the module
docstring; proved by `theorem1FChain`, unconditional form
`x64_cmpx_counter_envG'`). Otherwise the statement of `X64SpinPublicG.x64_spin_counter_envG`
(see `X64SpinPublic.x64_counter_public` for what is and is not covered:
undeclared 4-byte footprints, `hdisj` for the model's mixed-size gap, final
configurations only, `N < 2 ^ 32` for the 32-bit counter).

For every valid layout of `cmpxWorkerG` (the worker of
`spinlock_cmpxchg2.kl`: a bare `lock cmpxchgl` acquire loop, expected `0`,
new `1`; plain increment; plain-store release `movl $0`), every number of
threads `N < 2 ^ 32` and all addresses `l`, `c` whose 4-byte words are
disjoint: if `states` consists of `N` threads, each at the start of the
worker with `%rdi = l`, `%rsi = c` and neither word in its private memory
(`StartStateC`), and the initial memory has the lock and counter words at
`0`, then every configuration `Reachable` under `Arch.tso` that is final has
the counter word at `N`.

Proved by the EnvG `F` route: one `vcgen` call for the worker
(`cmpxWorkerG_envG`, failing and succeeding `lock cmpxchgl` both VCs),
`ThreadRuleRXF.ofSafelyEnvGFX` (`cmpxRule_envGF`), the all-release
specification by `vcgen` (`cmpxWorkerG_noNT`),
`final_of_relPureSafelyQX_tsoF` and `Spinlock.adequacy`. No-fault for the
worker's rule: `cmpxRule_envGF_noFault`. -/
theorem x64_cmpx_counter_envG [layout : _root_.Layout] [Executable.ValidLayout (layout cmpxWorkerG)] {fuel : Nat}
    (hchain : Theorem1FChain (I := isa) Arch.tso fuel)
    (N : Nat) (l c : BitVec 64) (hdisj : Decls.overlaps l 4 c 4 = false) (hN32 : N < 2 ^ 32)
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateC l c s) (hN : states.length = N)
    (hC0 : (Config.init states initMem).mem.initVal ⟨c, 4⟩ = 0)
    (hLk0 : (Config.init states initMem).mem.initVal ⟨l, 4⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.tso fuel (Config.init states initMem) cfg)
    (hf : cfg.final = true) :
    cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N :=
  CasSmoke.spin_counter_core N hdisj hN hC0 hc hf fun hlc hN0 hfin =>
    final_of_relPureSafelyQX_tsoF hchain (B := fun _ r _ => Post N ⟨l, 4⟩ (ghostSys N l c).K r)
      (Φ := fun cfg => cfg.mem.finalVal ⟨c, 4⟩ = BitVec.ofNat 128 N)
      (erase_init_lockPred (C := ⟨c, 4⟩) _ (ghostSys_spinLocs hlc) hN hN0 hC0 hLk0)
      pend_init (fun _ => cmpxNoNTSpec layout l c)
      (fun _ s hs => cmpxNoNTSpec_holds layout (hst s (List.mem_of_getElem? hs)))
      (fun tid htid n m => by
        obtain ⟨s, hs⟩ : ∃ s, states[tid]? = some s := ⟨_, List.getElem?_eq_getElem htid⟩
        exact cmpx_npSafeF hlc hN32 (hN ▸ htid) hs (hst s (List.mem_of_getElem? hs)) hLk0 n m)
      hc hf hfin

end Kraken.Promising.X64.EnvG.CmpxPublic

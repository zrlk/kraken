# EnvG on x64: known gaps 

Status: the x64 link (`X64LiveRun.lean`, `X64Link.lean`, `RelPureEnvX64.lean`,
`X64VCGen.lean`) and x64 message passing under `Arch.tso`
(`X64MpPublic.x64_mp_public`, with a concrete instance
`Concrete.x64_mp_public_concrete` in `ConcreteX64.lean`, so
`StartWX`/`StartRX` are satisfiable) are proved; so are the x64 `xchg` spinlock and
the x64 `lock cmpxchg` spinlock (below; `Theorem1FChain` is proved), and x64 MP with an unlocked `incl` release on `EnvGLRX`
(`MpInc.x64_mp_incl_envG`, concrete `Concrete.x64_mp_incl_envG_concrete`),
and the x64 Treiber stack on `EnvGCX` with failing `lock cmpxchgq` releases
(`TreiberX.x64_treiber_pp_envG`, concrete
`ConcreteTreiberX.x64_treiber_pp_envG_concrete`).
Open points:

## Restriction to a layout

x64 thread proofs are in `EnvGX A tid pl S = (EnvG isa A tid pl).within S`,
not bare `EnvG`. The thread's private memory must map no byte of `S`
(`Split S`), and `S` must have locations of at most 16 bytes (`Le16 S`). The
reason is the x64 adapter: non-atomic vector accesses are split into mapped
8-byte pieces first, while `AllEnv` sends every piece of an unmapped access to
the environment.

### Loads at a loaded address need a covering layout

`within S` checks every access against `S` (`AccessIn`), also outside the
clean flag. The x64 Treiber popper loads `8(%rax)` and `(%rax)` where `rax`
is the value it read from `top`: under the clean flag that is `n1`, but on
the erased (unclean) paths `rax` is arbitrary, so no finite layout of the
stack's words admits these loads. The popper therefore runs on `sAll`
(`X64TreiberVC.lean`: every 4- and 8-byte location, `@[irreducible]`,
2 ^ 65 entries; use `mem_sAll4`, `mem_sAll8`, `sAll_le16`, never `decide`
or `whnf` it). `Split sAll d` holds exactly when `d` maps no byte
(`split_sAll`), so `StartPopX` asks for an empty private memory (the
popper's table carries `∀ a, loadInt dmem a 8 = none` and the same at 4
bytes). This is a model limit, not a property of the program: any x64
thread that dereferences a shared pointer needs it (a pointer-chasing
thread with private data would need a layout that covers every shared
location but none of its own). A64 `EnvGC` has no layout and is not
affected.

## An x64 lock

Status:

- **`xchg`: done.** `X64SpinPublicG.x64_spin_counter_envG` (`counter = N` for
  `N` workers of `spinlock2.kl` under `Arch.tso`, the shape of
  `X64SpinPublic.x64_counter_public`) goes through
  `ThreadRuleRX.ofSafelyEnvGRX` (`X64SpinLink.spinRule_envG`), with
  `RelRmwGiveOk` (in `Res.only (pl.gives …)` form after the old links: no claimed
  slot of a planned-release RMW is given away), the RMW claim fact
  (`RmwFacts` `¬ Claimed`) and the release split
  `Plan.Split.share2D` (`SplitD.lean`). `lock xadd` is total as well and
  would take the same route; it has no example. (Since the x64 ticket lock proof the ticket
  locks' `lock xadd` is proved on another route, the dispenser environment
  `EnvGTDR`: `TicketX.ticket3_counter_envG_verbatim`, below.)
- **`lock cmpxchg`: done** (unconditional). Under `Arch.tso` every
  x64 RMW is release-kind (`plainRmw := .acqRel`), and a failing in-flight
  release RMW is outside `Phase1ShapeR` (the `RmwRelSmoke` limit), so the
  worker goes through the `F` link `ThreadRuleRXF.ofSafelyEnvGFX`
  (`X64RmwFail.lean`, `dirs_phase1FX` accepts `lock cmpxchg`) and gets
  `NPSafeF` (`CmpxLink.cmpxRule_envGF`, no-fault `cmpxRule_envGF_noFault`
  unconditional). `CmpxPublic.x64_cmpx_counter_envG` (`spinlock_cmpxchg2.kl`)
  has `x64_spin_counter_envG`'s shape plus the explicit hypothesis
  `hchain : Theorem1FChain (I := isa) Arch.tso fuel`, consumed by
  `CmpxPublic.final_of_relPureSafelyQX_tsoF` (`RelPureEnvX64F.lean`). The
  Theorem 1′ chain change proves `Theorem1FChain`
  (`theorem1FChain`, `RmwFailChain.lean`), and
  `CmpxPublic.x64_cmpx_counter_envG'` (`X64CmpxFinal.lean`) is the
  unconditional theorem.
- **RMW releases that give something away: done.** The x64 links of
  the claim-conditional environments are in `X64RmwGhostLink.lean`:
  `ThreadRuleRX.ofSafelyEnvGRCX` (`EnvGC`) and
  `ThreadRuleRXGS.ofSafelyEnvGTRCX` (`EnvGTC`, taking loads), with no-fault
  rules (`noFaultRule_ofSafelyEnvGRCX_struct`,
  `noFaultRule_ofSafelyEnvGTRCX_struct`, unconditional in promises). Every
  x64 RMW claims: all x64 RMW events have kind `.acqRel` (`plainRmw :=
  .acqRel` under `Arch.tso`), and `ClaimOk A .acqRel` holds unconditionally
  (`claimOk_acqRel`, `claimSlotsC_acqRel`), so `claimSlotsC = claimedSlots`.
  Only the give-from-own half of the claim-conditional extension matters on x64: no
  `RelRmwGiveOk`, no `Plan.Whole`. A take followed by a giving `xchg` is
  proved end to end: `RelayX.mp_relay3_xchg_envG` (`mp_relay3_xchg.kl`). The x64 take route's
  `ofSafelyEnvGTX` rejects RMWs (`Phase1TreeX`); use `ofSafelyEnvGTRCX`
  (`Phase1TreeRX`, `dirs_phase1RX`) for take + RMW threads.
- **Unlock** by a plain `mov` is a release store under `Arch.tso` (covered:
  `X64MpSmoke.vc_w2`).
- **Per-program cost:**
  - State each VC at an address and value given by equations
    (`X64MpVCGen.vc_*_ok` / `vc_*_step`): simp cannot rewrite the access
    inside an `env.step` hypothesis.
  - Supply `Split` start facts.
  - `testl`, `xchgl`, `addl $i`, `movl $i` and `lock cmpxchgl` (32-bit) have
    `vcgen` rules (`MachineWP.*32*_spec`, `Kraken/MachineWP.lean`,
    `Kraken/EnvVCGen.lean`).
  - After `dirs_phase1X` / `dirs_no_fault`, close the `if` nested inside
    `toEv` of a conditional jump with `by_cases s.status.zf`.

## Load-then-release trees and vector-load faults

- **Unlocked read-modify-writes of a shared location** (`incl (m)`,
  `addl $i,(m)`, … without `lock`: a plain load, then a plain store, which is
  a release under `Arch.tso`): neither phase 1 (two accesses) nor phase 2
  (`NoRelWrite`). **Covered** by the sibling environment `EnvGLR`
  (`LREnv.lean`; its loads keep `cl` and do not assert `ClAt`, which an
  in-flight release would make unjustifiable) and its x64 link
  `ThreadRuleRX.ofSafelyEnvGLRX` (`LRX64.lean`; shape tactic `dirs_lrX`).
  Smoke `LRX64Smoke.lean`: shapes; the env rule `inc32_shared`; VC
  `incRelX_tripleEnv`; rule, no-fault, initial invariant. Limits: an
  `EnvGLR` load gives no clean-erasure knowledge; the store after the loads
  goes to one location on every path; a release-kind RMW (every `lock` op)
  stays on `ofSafelyEnvGRX`/`…RCX`/`…FX`. First multi-thread use: x64 MP
  with an `incl (flag)` release (`X64/mp_incl.kl`,
  `MpInc.x64_mp_incl_envG`; below). (`ticketlock2.kl`, whose
  release is an `incl`, is proved without this link: the x64 `incl` ticket lock proof, the x64 ticket lock proof below.)
- **A release whose value depends on an `EnvGLR` load**. A planned
  release must be impure at its value (`StoreOk`) after *every* load outcome
  the env offers, and `ok` never consults `cl`. So the writer of
  `mp_incl.kl` cannot use the load's value: neither "the loaded flag is 0
  from the full write permission" (that needs `ClAt`, which `EnvGLR` drops)
  nor a plan entry `val := none` with MP's `flagPred` works (the load of
  `0xFFFFFFFF` makes `incl` write `0`, where `flagPred` is pure). `Pred.Pure`
  depends on the value only, so no value-only predicate is impure at every
  `incl` result and pure at the initial `0`. **Worked around** in
  `X64MpIncSpec.lean`: `flagPredI v _ V r := (V ≠ 0 ∨ low32 v ≠ 0) → Good`
  (impure everywhere, trivial at view `0`), with the initial flag message in
  release mode and one empty slot for the reader's acquire id
  (`mpGhostI`; `erase_mpIncInit` is an instance of `erase_initGhostAcq`,
  `SLR/InitGhost.lean`, since `erase_initGhost` forbids held acquire ids at
  release-mode locations). Plan entry `val := none`. The reader's VCs are
  the instance at `φI` of the reader generic over the flag predicate
  (`FlagLaw`; `WorldRI`, `vc_r*I`, `mpReaderIX_envGP`, `hB_RI`). The final flag value (`[f]=1` in the
  `.kl`) is not proved; it would need the loaded value. The same applies to
  any release that stores a loaded value plus something (e.g. ticket
  `owner+1`).
  **Closed for whole-entry writers** by the sibling env
  `EnvGLRV` (`LRVal*.lean`): its loads add `ClAtV` (cl-knowledge about the
  *actual* resource that `Inflight` relates to the virtual one), so a load
  under full permission determines the loaded value (`X_of_read_clAtV`).
  Link `ThreadRuleRX.ofSafelyEnvGLRVX` (extra hypothesis: whole plan
  entries). `MpIncV.x64_mp_incl_envGV` = `x64_mp_incl_envG` (same
  hypotheses) plus `finalVal ⟨f,4⟩ = 1`. Still open: split release entries,
  and release RMWs whose value matters (ticket `next` via `lock xadd`; the
  ticket locks avoid it through the dispenser, the x64 ticket lock proof below).
- **Vector loads read in pieces are not statically fault-free** (a piece
  crossing a 64-byte line faults; `dirs_no_fault` fails on the load-then-release design's `movups`
  smoke). **Conditionally covered** (`MultiX64Align.lean`): fault-free where
  an environment fitting `S` runs the directive (`DirsNoFaultEnvX`), given
  `Al8 S` (every 8-byte location of `S` is 8-aligned; the first piece is
  always asked of the environment, and 8-aligned pieces never cross a line):
  `noFaultRule_ofSafelyEnvG2X_env`, instance
  `MultiSmoke.movupsLoadRule_noFault`. Vector *stores* stay out (release-kind
  multi-write trees); `storePieces_noFault_al8` is there for them.

## The x64 SPSC ring

`SpscX.x64_spsc_envG` (`X64SpscPublic.lean`) proves `X64/spsc_queue.kl`
for all layouts. Points where it departs from the `.kl` or from the plan
(the verbatim companion `SpscAbs.x64_spsc_envG_verbatim`, and its
`_runner` form, have since closed the register-operand departure):

- **Symbols as registers**: `(tail)` and `(head)` are `(%rdi)` and
  `(%rsi)` (the spinlock2 / X64Spin precedent); the rest of the code,
  including `rbx = buf0` and the `(%rbx,%rdx,1)` slot addressing, is
  verbatim (`X64SpscProg.lean`). The properties are on the low 32 bits
  (`r12d`, `r13d`, `r14d`).
- **Empty private memories**: `StartPX`/`StartCX` ask that each thread's
  private memory map no byte. The all-release side (`spscNoNTSpecX`,
  `X64SpscRelPure.lean`) runs on `sAll` (the slot address is a register
  value), and `Split sAll` needs an empty memory (as `StartPopX`, above).
  The `.kl`'s threads have no private data, so this is met.
- **Design: `EnvGLRV` is neither needed nor sufficient.** The planned route
  was the in-flight-aware value environment `EnvGLRVX`. It is not needed:
  under `Arch.tso` the plain `movl` stores are release stores, and the
  plain loads of the indices take what the matching release gave
  (`EnvGTX`, `step_loadFactsT`). It is not sufficient: slot `buf0` must
  return to the producer. The consumer's `head := 1` store is a planned
  release giving `B0` and the token `GB` (`consPlan`, predicate `psiH`),
  and the producer takes them back at its `pfull` spin in round 3. An
  `EnvGLRV` release tracks a value; it does not hand over resources. The
  ownership round trip uses two ghost tokens, `GA` and `GB`
  (`X64SpscSpec.lean`). They tell the two `tail := 1` messages apart in
  `psiT`, and each disjunct is excluded by the token the reader still
  holds.
- **Copies / hoist candidates**: `X64SpscRead.lean`'s `read_own`
  (exact own-location read for any erasure), `spin_read`, `LoadKeep`,
  `SpinAt` and `OkPred` are generic in the plan and layout of `EnvGTX` and
  could move to a shared take-route read module. The `…_at` restatements
  of `X64SpscVCGen.lean` repeat `X64TakeMpVCGen`'s pattern, and a generic
  `subst` wrapper would remove them. `X64SpscPublic.spsc_final` follows the
  shape of `TakeMp.takeMp_finalX`.

## Copies to hoist

Hoisted (names and statements unchanged):

- `X64VCGen.lean`'s `FenceLe` / `SharedEnv.FenceMonoX` /
  `envMonoX_lift_spec` are aliases of the neutral `VCGenCommon.lean` ones.
- The CAS lock helpers copied into `X64SpinPublicG` are aliases of
  `SpinStart.lean` (`reachable_nil'` stays a copy: its statement is about
  x64 `Config isa`).
- The 32-bit `vcgen` rules of `X64SpinSpecs` / `X64CmpxSpecs` are aliases of
  the `MachineWP` rules.
- `Cmpx.rmw_fail_getFwd` is the x64 instance of `envG_rmw_fail_getFwd`
  (`RmwFailFwd.lean`).

Still copies, so that x64 files import no AArch64 module:

- `X64MpSpec.lean` copies the neutral half of `SLR/MpInv.lean` and
  `SLR/MpInit.lean`, plus `Mp.slot_of_seen` and `Mp.mp_final`. It covers
  `Params`, `MpLocs`, `Good`, `flagPred`, `WorldW`/`WorldR`, `Own0`/`Own1`,
  `mpGhost`/`mpRes` and `erase_mpInit`, with data value `42` and the reader's
  result in `rbx`. Not hoisted: the AArch64 statements hardcode the data
  value (`1#128`), so a parametrised module would change existing statements.
- Hoisted (the x64 names are now `hoist_alias` aliases of the
  ISA-neutral originals): `X64Link.lean`'s `noFaultRule_ofEnvGR_structX`,
  `InvGR.q_atX` (→ `LinkRNoFault.lean`) and map lemmas (→ `TreeMap.lean`);
  `MultiX64.lean`'s map lemmas and `noFaultRule_ofEnvG2_structX`
  (→ `MultiCommon.lean`); `X64RmwGhostLink.lean`'s `…I` names (`EnvGTCI`,
  `LinkHypsTRCI`, `ThreadRuleRXGS.ofEnvGTRCI`, …; → `RmwGhostTakeCore.lean`,
  the neutral half of `RmwGhostTake.lean`) and `noFaultRule_ofEnvGRC_structX`
  (→ `LinkRNoFault.lean`).
- Hoisted: `X64SpinVC.lean`'s lock predicates and lemmas
  (`LkLe`, `GoodC`, `Acq.*`, `H1`–`H3`, `QEnd`, `fresh_join`, `LkLe.*`,
  `vc_ld_c`/`vc_st_c`'s bodies; → `LockVC.lean`, shared with the AArch64
  `SwplLockVC.lean`), `X64RmwGhostVCGen.lean`'s `envGC_*X`/`envGTCI_*X`
  simp lemmas and `step_*FactsTCX` (→ `RmwGhostVCGenCommon.lean`), and
  `X64RmwFail.phase1ShapeF_map` (→ `RmwFailRuleLink.lean`).
- `X64RelayXchgSpec.lean` / `X64RelayXchgPublic.lean` copy the relay proof's
  `flag43`, `takeEff_wr_q_ge`, `relayParams`/`relayGhost`/`relayRes`,
  `erase_relayInit` and `relay_final` (with x64 `Params` and `ebx`). Not
  hoisted: only `flag43` (+ `_pure`/`_impure`) and `takeEff_wr_q_ge` are
  ISA-neutral (~25 lines); the rest is typed at each side's own `RP`/`Params`
  (`SLR.Mp.Params` vs `X64.EnvG.Mp.Params`) and `Config isa`.

- the x64 Treiber proof: `TreiberVCCommon.lean` is the ISA-neutral half of the Treiber proof's
  AArch64 `TreiberVC.lean` (table predicates and VCs generic in `I` and
  `A`, the compare-and-swap as `CasMatch`); the AArch64 file is not yet an
  instance of it (existing statements unchanged), so ~400 lines are
  duplicated. Also duplicated: `hB_pushX`/`hB_popX`/the final
  argument of `x64_treiber_pp_envG` vs the Treiber proof's (only `EStateX` and the
  result registers differ).
- Hoisted: `tParamsX` is an alias of the neutral
  `TreiberCommon.tParamsC` and `tLocs_tPX` an instance of `tLocs_tParamsC`
  (the Treiber proof's `tParams`/`tLocs_tP` are still copies); `TreiberX.prop_ite` is
  an alias of `Kraken.Promising.prop_ite` and the `dirs_no_faultX` macro is
  gone: both `dirs_no_fault` tactics close `je`'s `CondCode.interp` flag
  test with `prop_ite`; `CmpxPublic.final_of_relPureSafelyQX_tsoF'` moved to
  `RelPureEnvX64F.lean` (the x64 default for `NPSafeF` rules).

## Absolute operands rewritten to register operands

Several x64 proofs prove the `.kl` code with absolute symbol operands
(`(lock)`, `(counter)`, `(tail)`, `(head)`) replaced by register operands
(`(%rdi)`, `(%rbx)`, …) and a start hypothesis that the register holds the
symbol's address: `X64SpinPublicG.x64_spin_counter_envG` (`spinlock2.kl`),
`Dekker.x64_dekker_public` (`dekker_mfence.kl`, `(counter)` → `(%rbx)`),
and the x64 SPSC proof work in progress (`(tail)`/`(head)` → `(%rdi)`/`(%rsi)`).
The proved program is therefore not verbatim.

**Partly fixed.** `EnvVCGenAbs` (absolute-operand `@[spec]` rules),
`EnvCfgAbs` (`cfgEnv_partial_at`: a fragment inside the runner's whole
code + data image) and `X64ImageNoFault`. Verbatim companions over every
layout of the runner image, with concrete runner instances
(`codeMatches`/`runnerMatches`): `SpinAbs.x64_spin_counter_envG_verbatim`
(`spinlock2.kl`), `CmpxAbs.x64_cmpx_counter_envG_verbatim`
(`spinlock_cmpxchg2.kl`, unconditional), `DekkerAbs.x64_dekker_public_verbatim`
(`dekker_mfence.kl`). **Still not verbatim**: `treiber_pp`, `mp_incl`,
`spsc_queue`, `mp_relay3_xchg` (VCGen only for the first two; blockers: phase-1
shape over every cell of the image, exit label followed by code). All x64
theorems assume `decls = {}` while the runner has non-empty decls.
(Both since closed: verbatim `TreiberAbs.x64_treiber_pp_envG_verbatim`,
`MpInclAbs.x64_mp_incl_envGV_verbatim`, `SpscAbs.x64_spsc_envG_verbatim`,
`RelayAbs.mp_relay3_xchg_envG_verbatim`; the runner's declarations by the declarations proofs,
below. Index: `Examples/LockFree/THEOREMS.md`.)

**The x64 adjacency proofs.** The x64 adjacency link `EnvGCAdjX` (`EnvG/X64AdjLink.lean`:
`ThreadRuleRXF.ofSafelyEnvGFCAdjX`, no-fault, start) and 64-bit absolute rules
(`Kraken/EnvVCGenAbs64.lean`: `movq (sym),%r`, `movq %r,(sym)`,
`lock cmpxchgq %r,(sym)`) give `Treiber2X.x64_treiber2_envG_verbatim`
(`treiber2.kl` verbatim over every layout of the runner image; concrete
instance `X64Treiber2Concrete.lean`). The symbols' distinctness and
non-nullness are hypotheses (discharged by `decide` in the instance);
`decls = {}` as above. Duplicated (hoist candidates): `X64Treiber2Hist.lean`
is a verbatim copy of `Treiber2Hist.lean`, `X64Treiber2Ghost`/`Final`/`VC`
copies of the Treiber node proof's at link offset `0` without a data word (the AArch64
files import `RmwGhostVCGen`, so x64 cannot import them).

**The x64 MS queue proof.** `MsQueueX.x64_msqueue2_envG_verbatim`
(`X64MsQueue2Public.lean`): `msqueue2.kl` verbatim over every layout of the
runner image on `EnvGCAdjX` (mask link `X64MsQueueMaskAdj.lean`), property
`1:r12=n1 ∧ 1:r13=n2`; concrete instance `X64MsQueue2Concrete.lean`. New rule
`mov_reg_imm_label_spec` (`movq $sym,%r`) in `Kraken/EnvVCGenAbs64b.lean`.
Gaps: the runner's `initMem` locations are unsized (bytes 0); the instance
uses sized 8-byte locations (as `X64Treiber2Concrete`). `decls = {}` as above.
Proof devices: the ghost tracks tokens rather than data words, and a rank
invariant on `head` replaces the `next ≠ 0` check.

`MsQueue3X.x64_msqueue3_envG_verbatim` (`X64MsQueue3Public.lean`):
`msqueue3.kl` verbatim (one enqueuer, two try-once dequeuers), the `.kl`'s
five outcomes of `(1:r12, 2:r12)`; concrete instance
`X64MsQueue3Concrete.lean`. Same gaps as `msqueue2`. Proof devices: message
thread ids are unconstrained for other threads, so each dequeuer owns a pop
token that its `head` swing must give to the swung message's slot
(`Params.trk`/`HW` in msqueue2's `form`, which `paramsV` turns off), and each
thread holds a never-given mark (`markT`) that separates the threads' `hB`
disjuncts at the final erasure.

**The declarations proofs: the runner's declarations.** Every x64 verbatim theorem
assumed `decls = {}`, while the runner's threads carry the `.kl` header's
declarations, which are semantic (`exec` resolves each access through
`Decls.resolve`). Closed in two steps:

- the eleven `.kl` headers with verbatim theorems are **typed** (`uint32_t`
  for `movl` words, `uint64_t` for `movq` words; `treiber_pp`'s node `n1` is
  `uint32_t`, its 8-byte `next` at `n1 + 8` undeclared), so the runner is
  strict and sized (`Decls.Sized`); the code blocks and the verdicts are
  unchanged (re-run: same verdict and configuration count for every file,
  `msqueue3` 6,562,872 and `spinlock3` 3,106,483 included);
- `EnvG/X64DeclsLink.lean`: `QX64MD` (the masked invariant with
  `decls = ds`) and the D forms of every link family the verbatim theorems
  use (`…XMD`: plain, `R`, `F`, `FC`, `FCAdj`, `LRV`, `T`, `TRC`), the purity
  side (`RelPureSpecQX.HoldsD`, `final_of_relPureSafelyQX_tso{,F,S}D`), on
  the x64 vector proofs' `X64VecDeclsFault` bridge (`exec_underDecls`: under strict sized
  declarations a thread's tree is its `decls = {}` tree with the mixed-size
  accesses turned into faults, which every tree judgment and phase-1 shape
  absorbs). No condition on the code: register-valued addresses included.

Runner-exact companions, each a `*_runner` theorem beside the verbatim one
(same statement, `decls = ds` with `ds.Sized`) and a concrete instance from
the runner's own threads and initial memory (`runnerMatchesD` compares
`exe`, pc, end, registers, private memory, **declarations**, no promise,
the initial memory and no message): `X64SpinAbsRunner.lean` (`spinlock2`,
`spinlock3`), `X64CmpxAbsRunner.lean` (`spinlock_cmpxchg2/3`),
`DekkerAbsRunner.lean`, `X64TreiberAbsRunner.lean`, `X64Treiber2Runner.lean`,
`X64MpInclAbsRunner.lean`, `X64SpscAbsRunner.lean`, `X64RelayAbsRunner.lean`,
`X64MsQueue2Runner.lean`, `X64MsQueue3Runner.lean`. The `msqueue2/3` gap
"the runner's `initMem` locations are unsized" is closed by the typing.

No-fault at `decls = ds` (was "not covered" here):
`underDecls` makes a mixed-size access a fault, and excluding it needs the
dynamic fact that the thread's accesses are at declared footprints. Every
`QX64MD` invariant already carries that fact for its layout `S`, because its
`Safely` judgment is over `E.within S` (every access exactly an
`S`-location). `EnvG/X64NoFaultD.lean`, `noFault_QX64MD_rootD`: a
single-access tree whose root access is an `S`-location (the run lemma with
the judgment `rootInJ`) is fault-free re-resolved against declarations that
agree on `S` (`Decls.AgreesOn ds S`), given the existing `DirsNoFaultCode` at
`{}`. `X64NoFaultDMpIncl.lean` extends this to trees whose later accesses
repeat the root's location (`RootSameD`: `incl`). There are family wrappers
for every `…XMD` constructor, and the tactic `decls_agrees_on` closes the
concrete agreement goals. `*_runner_noFault` theorems (rule-level, like the
`decls = {}` `_noFault` rules), each with a `_concrete` instance at the
runner's declarations:
- `X64NoFaultDLocks.lean`: `SpinAbs.x64_spin_counter_envG_runner_noFault`,
  `CmpxAbs.x64_cmpx_counter_envG_runner_noFault`,
  `DekkerAbs.x64_dekker_public_runner_noFault`,
  `TicketX.ticket3_counter_envG_runner_noFault`;
- `X64NoFaultDMp.lean`: `SpscAbs.x64_spsc_envG_runner_noFault`,
  `RelayAbs.mp_relay3_xchg_envG_runner_noFault`,
  `TreiberAbs.x64_treiber_pp_pusher_runner_noFault` (pusher only);
- `X64NoFaultDMpIncl.lean`: `MpInclAbs.x64_mp_incl_envGV_runner_noFault`
  (writer and reader).

**Program-level fault freedom at `decls = ds`.** The
`*_runner_noFault` theorems above are rule-level. `Config.FaultFree` (no
configuration reachable under any architecture, promises included, has a
faulting step) now holds from the runner's start states, by a **value
reachability invariant** run beside the chain rather than inside it (no
`modelX` extension, no SLR, no ghost state):
- `EnvG/MemVals.lean` (ISA-neutral): `MemVals L V m` (every message to an
  `L`-location, and every initial value of one, is in `V`), the tree
  judgment `ValX` (the stateless `SharedEnv.valEnv L V`: writes at `L` carry
  `V` values, reads at `L` deliver them), `runTree_valX`, `certWrite_valX`
  (promises), `Reachable.valInv`, `faultFree_of_valInv`;
- `EnvG/MemValsX64.lean`: value specifications `ValSpecX` (a `Safely`
  judgment in `(valEnv L V).within S`), `x64_faultFree_of_valSpecs` (through
  `noFault_QX64MD_rootD`), and at `L = ∅` `x64_faultFree_of_relPureSpecsQXD`
  (the existing all-release purity specifications, no memory hypothesis);
- `EnvG/X64FaultFreeFixed.lean` (fixed layouts, `L = ∅`):
  `spinlock2/3`, `spinlock_cmpxchg2/3`, `dekker_mfence`, `ticketlock3`,
  `mp_relay3_xchg`, `mp_incl` (`*_runner_faultFree`, `_concrete`/`_concreteN`);
- the pointer programs, re-run (`vcgen`) in the value environment over a
  fixed node layout: `EnvG/MemValsTreiberPP.lean`
  (`x64_treiber_pp_envG_runner_faultFree`; `L` = `top`, `n1 + 8`, `V` =
  `0`, `n1`), `EnvG/MemValsTreiber2.lean`
  (`x64_treiber2_envG_runner_faultFree`; `L` = `top`, `n1`, `n2`, `V` = `0`,
  `n1`, `n2`), `EnvG/MemValsMsQueue.lean`
  (`x64_msqueue2_envG_runner_faultFree`, `x64_msqueue3_envG_runner_faultFree`;
  `L` = `head`, `tail` and the node words, `V` = `0`, `s`, `n1`, `n2`), each
  with a `_concrete` instance at the runner's threads, declarations and
  initial memory (the `MemVals` hypothesis by `decide`).
  The msqueue layout contains the null word `(0, 8)`: a value invariant
  cannot exclude a dequeuer swinging `head` to a stale `0` `next` (the queue
  invariant `head ≠ tail ⇒ head.next ≠ 0` is relational), so the proof
  covers a dereference of `0`, an undeclared footprint that overlaps no
  declaration (no fault).

The value-invariant fault-freedom proofs closed the two programs left open here.
`spsc_queue.kl`: `SpscAbs.x64_spsc_envG_runner_faultFree` (concrete
`SpscAbs.Concrete.x64_spsc_envG_runner_faultFree_concrete`,
`EnvG/MemValsX64Spsc.lean`). `L = ∅` does not suffice: the slot address
`buf0 + (i << 8)` depends on the loaded index, so `L` = `head`, `tail`
(4 bytes) and `V` = low word `0` or `1` (both indices wrap with `andl $1`).
It needs the hypothesis `SpscLocs spscP` (the slots are not the indices).
`treiber_aba_tagged.kl`: see the x64 vector proofs section. Phase-1 limit throughout:
single-access trees (`mp_incl`: same-location).
Combined: `*_runner_safe_faultFree` (with `_concrete` or
`_concreteN`, `EnvG/RunnerSafeFFX64.lean`) states the existing runner
conclusion (every final configuration reachable under `Arch.tso`) ∧
`Config.FaultFree` at the union of the two theorems' hypotheses, for
spinlock, spinlock_cmpxchg, dekker_mfence, ticketlock3, mp_relay3_xchg,
mp_incl, spsc_queue, treiber_pp, treiber2 and msqueue2/3.
`treiber_aba_tagged.kl` (`EnvG/RunnerSafeFFX64ABA.lean`):
`VecABA.x64_treiber_aba_tagged_runner_safe_faultFree` and the runner
concrete `VecABA.Concrete.x64_treiber_aba_tagged_runner_concrete`.
Lake does not track `include_str` inputs: after a `.kl` edit the concretes
must be rebuilt by hand (their oleans were removed here); `X64AbsDeclsCheck`
and `X64SpinConcrete` now record the sized runner shape (`runnerDeclsSized`,
`statesMatch` at 4-byte words), the legacy `runnerDecls` evals read `false`.

**The x64 ticket lock proof: the x64 ticket locks.** `ticketlock3.kl` is proved
verbatim: `TicketX.ticket3_counter_envG_verbatim` (`decls = {}`, every
layout of the runner image) and `TicketX.ticket3_counter_envG_runner`
(strict sized `ds`; concrete `TicketX.Concrete.ticket3_counter_envG_runner_concrete3`
from the runner's exact configuration), `EnvG/TicketX{Pure,VC,VCGen,Public,Runner}.lean`.
Its release `addl $1,%ecx; movl %ecx,(owner)` stores the spin's loaded value
plus one, which is the ticket at the `jne` exit, so every tree is
single-access and the existing `EnvGTDR` link covers it; the purity and
dispenser phases are an x64 copy of `dispPure` (`dispPureX`,
`ticket_counter_ofX`). No-fault: `ruleTk3_noFault` at `decls = {}`,
`TicketX.ticket3_counter_envG_runner_noFault` at `decls = ds` (`X64NoFaultDLocks.lean`). `ticketlock2.kl` (release `incl (owner)`) is proved
by the x64 `incl` ticket lock proof outside the SLR link: `TicketX2.ticket2_counter_envG_verbatim` /
`_runner` / `Concrete.ticket2_counter_envG_runner_concrete2`
(`EnvG/TicketX2{Run,Env,Reach,Final}.lean`, `EnvG/X64Ticket2{VCGen,Public,Runner}.lean`; fault freedom
`TicketX2.ticket2_counter_envG_runner_faultFree`, `EnvG/X64Ticket2FaultFree.lean`):
a per-thread invariant on the timestamps of the thread's accesses in the
Promising memory, kept by every reachable step, and a final counting
argument.

## Vector code with declarations

`decls = {}` is lifted for vector code: `X64VecDecls.exec_declsAgree` turns
a thread run with declarations into one without them, provided the
declarations agree on every cell of the image (`CellsDeclsAgree`). The proofs
that use this bridge are `VecPublish.x64_publish_movdqa_verbatim` (with
`_faultFree` and `_concrete` instances, using the runner's decls) and
`VecABA.x64_treiber_aba_tagged_never` (`treiber_aba_tagged.kl` verbatim:
`cmpxchg16b`, strict sized decls; files `X64VecTreiberABA*.lean`).

**Fault-freedom of `treiber_aba_tagged.kl`.** With typed
declarations (`head` 16 bytes, `A`/`B` 8 bytes), an access that straddles
or splits a declared location faults (mixed-size), and the node load
`movq (%rax),%rbx` and the push's store `movq %rax,(%r12)` go through
pointers read from `head`. The ABA link (`QX64VecDAdj`) has no layout, so
the "never" theorem says nothing about faults. Fault-freedom is proved
separately, by the value-invariant fault-freedom proofs route:
`VecABA.x64_treiber_aba_tagged_runner_faultFree` (concrete
`VecABA.Concrete.x64_treiber_aba_tagged_runner_faultFree_concrete` from the
runner's exact configuration, with `codeMatches`/`runnerMatches`). Files:
`EnvG/MemValsX64ABARun.lean` (runs), `MemValsX64ABA.lean`,
`MemValsX64ABAConcrete.lean`.
- The existing scalar `ValSpecX` is enough. The image is piece-free (the
  `movdqa`s are atomic), so no vector value specification is needed.
- `p0`/`p1` are re-run in `(valEnv L V).within abaS` with `L` = `head`
  (16 bytes), `A`, `B` (8 bytes), and `V` = values whose low quadword is
  `0`, `A` or `B` (the tag is free). The tables are `Stk` with `A`, `B`
  off the stack, plus thread `1`'s popped node `r12 ∈ {0, A, B}`
  (`≠ 0` at `p1push1`).
- `movdqa`/`cmpxchg16b` fault when unaligned, so the image is only
  `DirsNoFaultEnvX` (`abaImageV_noFaultEnv`). The generic
  `noFault_valSpecD_env` / `x64_faultFree_of_valSpecs_env` are twins of the
  existing `noFault_valSpecD` / `x64_faultFree_of_valSpecs` and are candidates to move into `MemValsX64.lean`.
- Hypotheses: each thread's start memory is split from `abaS` (`Split`),
  plus `StartV`, `head` 16-aligned, `ds` agreeing on `abaS`, and `IV`. No
  distinctness or non-null hypotheses.

Other limits:
- The thread's stack range is the domain of its initial private memory
  (`domS`).
- The ABA "never" theorem is stated over every valid layout, with symbol
  distinctness, non-nullness and `head`'s alignment as hypotheses. Its
  concrete runner instance is
  `VecABA.Concrete.x64_treiber_aba_tagged_runner_concrete`
  (`EnvG/RunnerSafeFFX64ABA.lean`); the fault-freedom theorem's is in
  `MemValsX64ABAConcrete`.
- `cas16_shape` (`X64VecTreiberABAImage`) is a workaround: `simp` on the
  `cmpxchg16b` interpretation times out.

## Not done

- No `.S` test (MP is multi-threaded).
- No `.S` test for the Treiber stack either (two threads).
- No `.S` test for the SPSC ring (two threads).

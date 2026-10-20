# The whole-thread environment `EnvG`: entry points

`SLR/EnvG/` proves a thread's SLR rule (`ThreadRuleRX`, hence `NPSafe` and
Theorem 1′) from one `vcgen`-style judgment of the thread's program in the
environment `EnvG I A tid pl` (`Env.lean`). Each file starts with a docstring; this
page only lists where to start.

**Phase-1 limits** (apply to every route below): trees with a single access;
acquire on the read side only; releases are *stores* (`Phase1Shape` needs
`¬ effRelRmw`; the `…R` routes lift this for release RMWs whose plan entry is
whole and claim nothing given away, the claim-conditional `…RC`/`…TRC`
routes for total release RMWs, including release-only ones and ones whose
plan gives something away (a release RMW still cannot forward what it
claims), and the `…F` routes for release RMWs that may fail); with promises,
no-fault needs `EnvGAnswersAt` (the `_struct` forms need only fault-free
code).

## Rule links (program judgment → `ThreadRuleRX`)

| Route | Name | File |
|---|---|---|
| ISA-neutral core | `ThreadRuleRX.ofEnvG (H : LinkHyps A tid pl Q) hB`, `npSafe_of_envG` | `RuleLink.lean` |
| ISA-neutral, release RMWs | `ThreadRuleRX.ofEnvGR` (`LinkHypsR`) | `RuleLink.lean` |
| AArch64 | `ThreadRuleRX.ofSafelyEnvG`, `AArch64.EnvG.npSafe_of_safelyEnvG` | `A64Link.lean` |
| AArch64, release RMWs | `ThreadRuleRX.ofSafelyEnvGR` | `A64LinkR.lean` |
| x64 (`EnvGX = (EnvG …).within S`) | `ThreadRuleRX.ofSafelyEnvGX`, `ofSafelyEnvGRX` | `X64Link.lean` (gaps: `X64_KNOWN_GAPS.md`) |
| fence release (`dmb ish; str`), guard `GHyb rel` | `ThreadRuleRXG.ofEnvGHyb` (`FenceEnv.lean`); AArch64 `ThreadRuleRXG.ofSafelyEnvGHyb`, `AArch64.EnvG.npSafeP_hyb_of_safelyEnvG_S` | `FenceEnvA64.lean` |
| take rule (write after acquire load, option (S)), old-style rules | `NPSafeP.of_ruleRXGS`, `theorem1IIPure_G₀_S` | `SLR/TakeRuleThread.lean` |
| take route on `EnvGT` (non-forwarded acquire loads take their slot) | ISA-neutral `ThreadRuleRXGS.ofEnvGT` (`TakeRuleLink.lean`); AArch64 `ThreadRuleRXGS.ofSafelyEnvGT`, `npSafeP_of_safelyEnvGT` (`TakeA64Link.lean`); no-fault `noFaultRule_ofSafelyEnvGT_struct` (`TakeA64Rule.lean`); assembly `final_of_relPureSafelyS` (`TakeFinal.lean`) | `Take*.lean` |
| x64 take route (`EnvGTX = (EnvGT …).within S`) | `ThreadRuleRXGS.ofSafelyEnvGTX`, `npSafeP_of_safelyEnvGTX`, no-fault `noFaultRule_ofSafelyEnvGTX_struct`, start `invGTX_init` (`TakeX64Link.lean`); assembly `final_of_relPureSafelyQX_tsoS` (`TakeX64Final.lean`). Loads and stores only: `Phase1TreeX` rejects x64 RMWs | `TakeX64*.lean` |
| cumulative take route on `EnvGTU` (a non-forwarded acquire load of `(l, tr)` takes the thread's slots of `(l, ts)` for **every** `ts ≤ tr`: a reader that skips a release still collects its slot) | core `takeUpTo`, `takeUpTo_spec`, `takeUpTo_eq_takeAll` (the `EnvGT` take is the no-skip case), `takeUpTo_wr_full`, `takeUpTo_held` (`TakeUAll.lean`); env `EnvGTU`, `LoadOutTU`, `loadFactsTU_wr_full` (`TakeUEnv.lean`); ISA-neutral `ThreadRuleRXGS.ofEnvGTU`, `npSafeP_of_envGTU` (`TakeURuleLink.lean`); AArch64 `ThreadRuleRXGS.ofSafelyEnvGTU`, `npSafeP_of_safelyEnvGTU`, `noFaultRule_ofSafelyEnvGTU_struct`, `invGTU_init` (`TakeUA64.lean`); x64 `ofSafelyEnvGTUX`, `npSafeP_of_safelyEnvGTUX`, `noFaultRule_ofSafelyEnvGTUX_struct`, `invGTUX_init` (`TakeUX64.lean`); smoke `TakeUSkip.skipReader_npSafeP` | `TakeU*.lean` |
| AArch64 masked image, guarded exit (a thread runs the whole `.kl` image; its `Safely` judgment is over a mask `e'` of the image `e`: the other roles' code and the cell behind the exit label are data cells, so the halt and the phase-1 shape are the mask's) | core `MaskOf`, `Program.maskKeep`, `maskOf_layout`, `instrStepEnv_of_mask`, `Safely.of_mask`, `exec_of_mask` (`A64MaskCore.lean`); `MachineWP.cfgEnv_partial_at`, `Program.PlacedIn.of_placedE`, `Program.last_of_check`, `not_instrStepEnv_of_byteArray` (`A64MaskCfg.lean`); invariant `QA64M` and the families `ThreadRuleRXGS.ofSafelyEnvGTUM`/`npSafeP_of_safelyEnvGTUM`/`noFaultRule_ofSafelyEnvGTUM`/`invGTUM_init` (`EnvGTU`), `ofSafelyEnvGTM` (`EnvGT`), `ThreadRuleRX.ofSafelyEnvGM` (`EnvG`), `ThreadRuleRXF.ofSafelyEnvGFCM` (`EnvGC` failing RMWs) (`A64MaskLink.lean`); the whole-image AArch64 proofs: `ThreadRuleRXF.ofSafelyEnvGFCAdjM` (`EnvGCAdj`, `A64MaskAdj.lean`), `ThreadRuleRXGS.ofSafelyEnvGTRCM` (`EnvGTC`, `A64MaskTC.lean`), runs over any placed `[CodeEnv]` `MachineWP.PartialTripleEnv.of_runAt(T)`, `MsQueue.cfgEnv_partial_rank_at` (`A64MaskRunAt.lean`), image helpers `label_addrOf_succ_maskKeep`, `Safely.atImageLabels`, `RelPureSpec.toEnd` (`A64MaskHelpers.lean`), runner checks `A64Whole.codeIs`/`runnerIs` (`A64WholeRunner.lean`) | `A64Mask*.lean` (AArch64 copy of the x64 absolute-address mask proofs' `X64Mask*`) |
| take route with release RMWs | ISA-neutral `ThreadRuleRXGS.ofEnvGTR`, `npSafeP_of_envGTR` (`TakeRLink.lean`); AArch64 `ThreadRuleRXGS.ofSafelyEnvGTR`, `npSafeP_of_safelyEnvGTR`, `noFaultRule_ofSafelyEnvGTR_struct`, `invGTR_init` | `TakeRA64Link.lean` |
| claim-conditional env `EnvGC` (claims only under `ClaimOk`, gives from own resource; no `RelRmwGiveOk`, no `Plan.Whole`): release-only RMWs (`swpl`, `ldaddl`) and giving RMW releases | ISA-neutral `ThreadRuleRX.ofEnvGRC` (`LinkHypsRC`), `npSafe_of_envGRC` (`RmwGhostRule.lean`); AArch64 `ThreadRuleRX.ofSafelyEnvGRC`, `npSafe_of_safelyEnvGRC`, `noFaultRule_ofSafelyEnvGRC_struct`, `invGRC_init` (`RmwGhostA64.lean`); refinement `envG_ok_toC`, `envGC_step_toG` (`RmwGhost.lean`) | `RmwGhost*.lean` |
| the same with taking loads, `EnvGTC` | ISA-neutral `ThreadRuleRXGS.ofEnvGTRC` (`LinkHypsTRC`), `npSafeP_of_envGTRC`; AArch64 `ThreadRuleRXGS.ofSafelyEnvGTRC`, `npSafeP_of_safelyEnvGTRC`, `noFaultRule_ofSafelyEnvGTRC_struct`, `invGTRC_init` | `RmwGhostTake.lean` |
| x64 `EnvGC` / `EnvGTC` (every x64 RMW is `.acqRel` and claims: `claimSlotsC_acqRel`; a giving `xchg`/`lock xadd` gives from own resource) | `ThreadRuleRX.ofSafelyEnvGRCX`, `npSafe_of_safelyEnvGRCX`, `noFaultRule_ofSafelyEnvGRCX_struct`, `invGRCX_init`; `ThreadRuleRXGS.ofSafelyEnvGTRCX`, `npSafeP_of_safelyEnvGTRCX`, `noFaultRule_ofSafelyEnvGTRCX_struct`, `invGTRCX_init`; start `qx64C_of_partialTripleEnv`, `qx64TC_of_partialTripleEnv` | `X64RmwGhostLink.lean` (holds an ISA-neutral copy `EnvGTCI` of the `RmwGhostTake` core, hoist candidate) |
| load-then-release: sibling env `EnvGLR` (`LREnv.lean`: `EnvG` whose loads keep `cl`, no `ClAt`), trees `LRShape` = phase 1, phase 2, or loads then one store, always to one location (x64 `incl (m)`, `addl $i,(m)`: a release under `Arch.tso`); no release RMW | ISA-neutral `ThreadRuleRX.ofEnvGLR` (`LinkHypsLR`), `npSafe_of_envGLR`, `noFaultRule_ofEnvGLR_struct` (`LRRule.lean`; link `nodeSimLR_envGLR`, `LRLink.lean`); x64 (`EnvGLRX = (EnvGLR …).within S`) `ThreadRuleRX.ofSafelyEnvGLRX`, `npSafe_of_safelyEnvGLRX`, `noFaultRule_ofSafelyEnvGLRX_struct`, shape tactic `dirs_lrX`, start `qx64LR_of_partialTripleEnv`, `invGLRX_init` (`LRX64.lean`) | `LR*.lean` |
| `F` route: in-flight release RMWs that may fail (`casal`, x64 `lock cmpxchg`) | `NPSafeF`, `StepFul`, `NPSafe.toF`, `ThreadRuleRXF`, `NPSafeF.of_ruleRXF` (`RmwFailRule.lean`); ISA-neutral `ThreadRuleRXF.ofEnvGF`, `NoFaultRuleF` (`RmwFailRuleLink.lean`); AArch64 `ThreadRuleRXF.ofSafelyEnvGF`, `dirs_phase1F` (`A64RmwFail.lean`); x64 `ThreadRuleRXF.ofSafelyEnvGFX`, `dirs_phase1FX` (`X64RmwFail.lean`) | `RmwFail*.lean`, `A64RmwFail.lean`, `X64RmwFail.lean` |
| x64 `F`×`C`: `EnvGCX` with failing `lock cmpxchg` releases that give from own resource (the x64 counterpart of `ofSafelyEnvGFC`) | `ThreadRuleRXF.ofSafelyEnvGFCX`, `npSafeF_of_safelyEnvGFCX`, `noFaultRuleF_ofSafelyEnvGFCX_struct`, start `invGFCX_init` (with `qx64C_of_partialTripleEnv`); assembly `CmpxPublic.final_of_relPureSafelyQX_tsoF'` (`final_of_relPureSafelyQX_tsoF` with `theorem1FChain`) | `X64RmwFailGhost.lean` |

**Closed on the `F` route:** the rules give `NPSafeF`, not
`NPSafe`. Theorem 1′ for `NPSafeF` is `Theorem1FChain` (`RmwFailRule.lean`;
`theorem1IIPure_of_F` is proved from it), now a theorem: `theorem1FChain`
(`RmwFailChain.lean`), from the Theorem 1′ chain's step guard
(`StepGuard`, `NPSafePS`, `theorem1IIPureS'`). Theorems stated
with `Theorem1FChain` as an explicit hypothesis are kept; their unconditional
forms discharge it with `theorem1FChain` (e.g.
`CmpxPublic.x64_cmpx_counter_envG'`).

**Ticket dispenser (design prototype, not on the EnvG route yet):**
`SLR/LoadClaim.lean`, `LoadClaimErase.lean`, `LoadClaimChain.lean`
(`EraseT`, `TicketInv`, `EraseT.rmwHand`, `takeEraseLawT`): the load claim
an `ldadda` ticket lock needs. Theorem 1′ over the extended erasure,
`Theorem1IIPureX'` (`theorem1IIPure'_of_X`: the existing statement is its
instance at `X = ⊤`), is proved: `theorem1IIPureX'` and the
ticket instance `theorem1IIPureT` (`LoadClaimFinal.lean`). Nothing imports these files.

The AArch64 routes take `pl.Valid`, `e.rmwLive`, `Phase1Tree A e`, the
postcondition facts (`hpost`, `hstuck`, `hB`) and a judgment
`Safely (e.instrStepEnv (EnvGA A tid pl)) post`.

## Purity (Theorem 1′ condition (C)) on the same judgment

- `SharedEnv.relPure A rel` (`RelPureEnv.lean`; AArch64 `RelPureEnvA64.lean`,
  x64 `RelPureEnvX64.lean`): `RelWrites` from a judgment in a purity env.
- `SharedEnv.relPureF A rel` (`FenceEnvPure.lean`, `FenceEnvPureA64.lean`):
  the fence-aware form (`RelWritesF`), for `GHyb`.
- x64 under `Arch.tso`: `final_of_relPureSafelyQX_tso` (`RelPureEnvX64.lean`)
  gives scope and purity at once from all-release specifications;
  `CmpxPublic.final_of_relPureSafelyQX_tsoF` (`RelPureEnvX64F.lean`) is the same
  for `NPSafeF` rules, with `Theorem1FChain` as a hypothesis (proved:
  `theorem1FChain`).

## No-fault

- `noFaultRule_ofEnvG` under `EnvGAnswersAt` (`RuleNoFault.lean`; open for
  threads with promises); AArch64 `noFaultRule_ofSafelyEnvG`
  (`A64NoFault.lean`); promise-free threads `noFault_ofSafelyEnvG_promFree`.
- Structural forms `noFaultRule_of…_struct` (`Answers.lean`,
  `A64Answers.lean`, `A64LinkR.lean`, `X64Link.lean`).
- x64 vector loads in pieces (a piece crossing a cache line faults, so
  `dirs_no_fault` rejects them): environment forms
  `noFaultRule_ofSafelyEnvG{X,2X,LRX}_env` from `DirsNoFaultEnvX S e`
  (fault-free wherever an environment fitting `S` runs the directive), with
  the layout hypothesis `Al8 S` (every 8-byte location of `S` 8-aligned) for
  `movups` (`MultiX64Align.lean`; instance
  `MultiSmoke.movupsLoadRule_noFault`, `MultiX64AlignSmoke.lean`).
- Program-level, at the runner's declarations (x64): `Config.FaultFree`
  from a value invariant, `faultFree_of_valInv` (`MemVals.lean`),
  `x64_faultFree_of_valSpecs` (`MemValsX64.lean`); the `*_runner_faultFree`
  theorems in `X64FaultFreeFixed.lean`, `MemValsTreiberPP.lean`,
  `MemValsTreiber2.lean`, `MemValsMsQueue.lean`, `MemValsX64Spsc.lean`
  (`spsc_queue.kl`) and `MemValsX64ABA.lean` (`treiber_aba_tagged.kl`, with
  `x64_faultFree_of_valSpecs_env` for the alignment-faulting `movdqa` /
  `cmpxchg16b`; runs `MemValsX64ABARun.lean`, concrete
  `MemValsX64ABAConcrete.lean`).
- Safety ∧ program-level fault freedom in one statement:
  `*_runner_safe_faultFree` with `_concrete`/`_concreteN`,
  `RunnerSafeFFA64.lean` (14 AArch64 families, including `treiber2_arm`,
  whose fault freedom is `MemValsA64Treiber2Arm.lean`) and
  `RunnerSafeFFX64.lean` (11 x64 families). Each is the pair of the existing
  `*_runner` and `*_runner_faultFree` theorems.

## `vcgen` on `EnvG`

`EnvG` is not `Skips`: fences change views and fence bits. `FenceLe` and the
class `SharedEnv.FenceMono` are in `VCGenCommon.lean` (ISA-neutral); the rule
`envMono_lift_spec` is in `A64VCGen.lean`, x64's `envMonoX_lift_spec` in
`X64VCGen.lean` (whose `FenceLe`/`FenceMonoX` are aliases of the neutral
ones). Simp set: `Simp.lean`. For `EnvGT`: `TakeVCGen.lean`. For `EnvGC`/`EnvGTC`:
`RmwGhostVCGen.lean`, with `@[simp]` `ok`/`step`, `FenceMono` instances,
`step_*FactsTC`, `claimSlotsC_armv8_rel`, and the start lemmas
`qa64C_of_partialTripleEnv`/`qa64TC_of_partialTripleEnv`. `SWP`/`LD<op>` use
the generic `swp_shared_spec`/`ldop_shared_spec`. x64 `EnvGCX`/`EnvGTCX`:
`X64RmwGhostVCGen.lean` (`@[simp]` `ok`/`step`, `step_*FactsTCX`,
`fenceMonoX_le_envGCX`/`fenceMonoX_le_envGTCX`). Every `Skips` or `FenceMono`
environment permits every fence (`FenceInv (fun _ => True)`):
`FenceInvTrue.lean`. `MOVZ`/`MOVK` per-directive phase-1 and no-fault facts,
generic in the immediate (for texts whose immediates `dirs_phase1F` cannot
unfold): `A64MovImm.lean`. x64 environment refinement (`Safely.refine`: more
permissions needed, fewer outcomes) and the value-restricted purity environment
`relInvX`: `X64EnvRefine.lean`.

## Example programs

Per-program lines (`wc -l` of the listed files, one-time library and shared
common modules excluded):

| Program | Public theorem | Files | Lines |
|---|---|---|---|
| MP (AArch64) | `MpLink.mp_envG'` | `MpSmoke`, `MpSmokeVCGen`, `MpLink`, `MpRelPure`, `MpEnvGPublic(2)` | 687 |
| MP (x64, `Arch.tso`) | `X64MpPublic.x64_mp_public` | `X64Mp*` (incl. the copied spec `X64MpSpec`) | 1069 |
| CAS spinlock (TTAS) | `CasSmoke.cas_counter_envG` | `Cas*` | 1167 |
| MP with `dmb ish; str` writer | `FenceEnvMp.mp_fence_envG` (type of `MpFence.mp_fence`) | `FenceEnvMp`, `FenceEnvMpPublic` | 326 |
| MP with a writing reader (take route) | `TakeMp.takeMp_envG` | `TakeMp`, `TakeMpVCGen`, `TakeMpRelPure`, `TakeMpPublic` | 620 |
| the same through the `TR` link | `TakeMp.takeMp_envGR` (`= takeMp_envG` by `rfl`) | `TakeRSmoke` | 144 |
| x64 MP with a writing reader (take route, `Arch.tso`) | `X64TakeMpPublic.x64_takeMp_public` | `X64TakeMp`, `X64TakeMpVCGen`, `X64TakeMpRelPure`, `X64TakeMpPublic` | 699 |
| x64 `xchg` spinlock (`spinlock2.kl`) | `X64SpinPublicG.x64_spin_counter_envG` | `X64SpinLink`, `X64SpinPublicG`, `X64SpinRelease`, `X64SpinRelPure`, `X64SpinVCGen`, `X64SpinVC` | 1249 |
| three-thread relay, `stlr` relay (`mp_relay3.kl`) | `Relay.mp_relay3_envG` | `RelaySpec`, `RelayVCGen`, `RelayRelPure`, `RelayPublic` | 1095 |
| the same, the three threads running the whole `.kl` image (the runner's executable, one layout; the writer over its mask through `ThreadRuleRX.ofSafelyEnvGM`, the relay over its mask through `ThreadRuleRXGS.ofSafelyEnvGTM`, the dead `NOP`s at `wdone`/`rdone` masked; the reader at the trivial mask) | `Relay.mp_relay3_envG_whole` (concrete: `Relay.mp_relay3_envG_whole_concrete`, with `codeMatchesW`, `runnerMatchesW`); no-fault `relayRuleW3_noFault`, `relayRuleY3_noFault`, `relayRuleD3_noFault` | `A64WholeRelayVCGen`, `A64WholeRelayPublic`, `A64WholeRelayConcrete` (on top of the `Relay*`/`Mp*` files; link `A64Mask*` excluded) | 1107 |
| the same, `swpl` relay (`mp_relay3_swpl.kl`; `EnvGTC`) | `Relay.mp_relay3_swpl_envG` | `RelaySwplSpec`, `RelaySwplVCGen`, `RelaySwplRelPure`, `RelaySwplPublic` (reuse the `Relay*` files above) | 535 |
| the same, the three threads running the whole `.kl` image (the runner's executable, one layout; every role over its own mask: the writer through `ThreadRuleRX.ofSafelyEnvGM`, the relay through `ThreadRuleRXGS.ofSafelyEnvGTRCM`, the reader through `ThreadRuleRXGS.ofSafelyEnvGTM`; the writer's and the reader's runs are `A64WholeRelayVCGen`'s `writerT3_envG_at`, `readerT3_envGT_at`, `writerT3_relPure_at`, `readerT3_relPure_at`) | `Relay.mp_relay3_swpl_envG_whole` (concrete: `Relay.mp_relay3_swpl_envG_whole_concrete`, with `codeMatchesWS`, `runnerMatchesWS`); no-fault `relayRuleWS3_noFault`, `relayRuleYS3_noFault`, `relayRuleDS3_noFault` | `A64WholeRelaySwpl`, `A64WholeRelaySwplConcrete` (on top of the `RelaySwpl*`/`A64WholeRelay*` files; generic `A64MaskTC` excluded) | 750 |
| the same, x64 `xchg` relay (`X64/mp_relay3_xchg.kl`; `EnvGTCX`, `Arch.tso`) | `RelayX.mp_relay3_xchg_envG` (concrete: `Concrete.mp_relay3_xchg_envG_concrete`) | `X64RelayXchgSpec`, `X64RelayXchgVCGen`, `X64RelayXchgRelPure`, `X64RelayXchgPublic`, `X64RelayXchgConcrete` (link/vcgen library `X64RmwGhostLink`, `X64RmwGhostVCGen` excluded) | 1328 |
| SWP spinlock released by `swpl` (`spinlock_swpl2.kl`; `EnvGC`; first lock with an RMW release) | `SwplLock.swpl_counter_envG` | `SwplLockSmoke`, `SwplLockVC`, `SwplLockVCGen`, `SwplLockRelPure`, `SwplLockPublic` (reuse `xlockPlan` of `X64SpinRelease`) | 945 |
| SWP spinlock, `stlr` release (`spinlock_swp2.kl`; `EnvGC`; the statement of the cell-route `SwpPublic.swp_counter_public`, `swp_counter_envG_type_eq`) | `SwpEnvG.swp_counter_envG` (runner-exact `swp_counter_envG_runner`, no-fault `swp_counter_envG_runner_noFault`, `_faultFree`: `A64SwpRunner`, `A64SwpNoFault`) | `SwpEnvGSmoke`, `SwpEnvGVC`, `SwpEnvGVCGen`, `SwpEnvGRelPure`, `SwpEnvGPublic` (reuse the `swpl` lock's `E`, table predicates and VCs; new: `vc_stlr`, `storeOk_of_storeKind`) | 547 |
| Treiber stack push/pop (`treiber_pp.kl`; EnvGC with failing release RMWs, `casal`) | `Treiber.treiber_pp_envG` (concrete: `ConcreteTreiber.treiber_pp_envG_concrete`) | `TreiberGhost`, `TreiberVC`, `TreiberSmoke`, `TreiberVCGen`, `TreiberRelPure`, `TreiberPublic`, `ConcreteTreiber` (F×C link library `RmwFailGhostLink`/`Rule`, `A64RmwFailGhost`, `A64RmwFailFinal` excluded) | 1709 |
| the same, both threads running the whole `.kl` image (the runner's executable; the pusher over its mask through `ThreadRuleRXF.ofSafelyEnvGFCM`, the dead `NOP` at `pdone` masked; the popper at the trivial mask) | `Treiber.treiber_pp_envG_whole` (concrete: `Treiber.treiber_pp_envG_whole_concrete`, with `codeMatchesW`, `runnerMatchesW`); no-fault `pushRuleW_noFault`, `popRuleW_noFault` | `A64WholeTreiberVCGen`, `A64WholeTreiberPublic`, `A64WholeTreiberConcrete` (on top of the `Treiber*` files; link `A64Mask*` excluded) | 940 |
| two-thread Treiber stack, 2 × (push own node, pop) (`treiber2_nodes.kl`; `EnvGCAdj`, the adjacency link; node frozen at the push, history of `top` at the final erasure) | `Treiber2.treiber2_nodes_envG` (concrete: `ConcreteTreiber2.treiber2_nodes_envG_concrete`) | `Treiber2Ghost`, `Treiber2Hist`, `Treiber2Final`, `Treiber2VC`, `Treiber2Smoke`, `Treiber2VCGen`, `Treiber2RelPure`, `Treiber2Public`, `ConcreteTreiber2` (reuse `Treiber*` lemmas, e.g. `casOp64`, `initVal_eq`, `WriteSnap`; link `AdjSpike*` excluded) | 2490 |
| the same, both threads running the whole `.kl` image (the `code` block with its `worker:` label, one layout; adjacency link at the image, no mask) | `Treiber2.treiber2_nodes_envG_whole` (concrete: `Treiber2.treiber2_nodes_envG_whole_concrete`, with `codeMatchesW`, `runnerMatchesW`); no-fault `wRuleN_noFault` | `A64WholeTreiber2Nodes` (on top of the `Treiber2*` files) | 603 |
| the same with the data word (`treiber2.kl`: `str w9` before the push, `ldr w11` after the pop) | `Treiber2.treiber2_envG` (concrete: `ConcreteTreiber2Data.treiber2_envG_concrete`) | `Treiber2DataVC`, `Treiber2DataVCGen`, `Treiber2DataRelPure`, `Treiber2DataPublic`, `ConcreteTreiber2Data` (on top of the `treiber2_nodes` files) | 934 |
| the same, both threads running the whole `.kl` image (the block is `treiber2DWorker`: `treiber2_envG` at one layout) | `Treiber2.treiber2_envG_whole` (concrete: `Treiber2.treiber2_envG_whole_concrete`, with `runnerMatchesW`) | `A64WholeTreiber2` (on top of the `Treiber2Data*` files) | 106 |
| Michael–Scott queue, 1 enqueue ∥ 1 dequeue (`msqueue1.kl`; `EnvGCAdj`; ½/½ split of `head`/`tail`, the dequeuer holds the acquire id `0` of the four queue words, the node frozen at its link, helping `casal`s release by provenance; zero-step back edge `cbz x5, deq1a` by the ranked CFG rule `cfgEnv_partial_rank`) | `MsQueue.msqueue1_envG` (concrete: `ConcreteMsQueue.msqueue1_envG_concrete`) | `MsQueueGhost`, `MsQueueFinal`, `MsQueueVC`, `MsQueueSmoke`, `MsQueueCfg`, `MsQueueVCGen`, `MsQueueRelPure`, `MsQueuePublic`, `ConcreteMsQueue` (reuse `Treiber*`/`Treiber2*` lemmas, e.g. `casOp64`, `initVal_eq`, `slot_read`) | 2461 |
| the same, both threads running the whole `.kl` image (the runner's executable, one layout; both roles over their masks through `ThreadRuleRXF.ofSafelyEnvGFCAdjM`, the dead `NOP`s at `pdone`/`ddone1` masked; the MS queue proof's runs reused unchanged as `enq_envGCAdj_at`, `deq_envGCAdj_at`, `enq_relPure_at`, `deq_relPure_at`) | `MsQueue.msqueue1_envG_whole` (concrete: `MsQueue.msqueue1_envG_whole_concrete`, with `codeMatchesWQ1`, `runnerMatchesWQ1`); no-fault `enqRuleQ1_noFault`, `deqRuleQ1_noFault` | `A64WholeMsQueue1`, `A64WholeMsQueue1Concrete` (on top of the `MsQueue*` files; generic `A64MaskRunAt`, `A64MaskAdj`, `A64MaskHelpers`, `A64WholeRunner` excluded) | 486 |
| Michael–Scott queue, 2 enqueues ∥ 2 dequeues by one thread each (`msqueue2.kl`, `1:X10=1 ∧ 1:X11=2`; `EnvGCAdj`; msqueue1's plan per phase, the two nodes frozen in turn, the tail's forwarding time bounded by the enqueuer's `vwNew` (`FwdT`), FIFO order recovered at the final erasure from the two `head` swings) | `MsQueue.msqueue2_envG` (concrete: `ConcreteMsQueue2.msqueue2_envG_concrete`) | `MsQueue2Ghost`, `MsQueue2Final`, `MsQueue2Smoke`, `MsQueue2VC`, `MsQueue2VCGen`, `MsQueue2RelPure`, `MsQueue2Public`, `ConcreteMsQueue2` (on top of the `MsQueue*` files above) | 2804 |
| the same, both threads running the whole `.kl` image (as msqueue1's; runs `enq2_envGCAdj_at`, `deq2_envGCAdj_at`, `enq2_relPure_at`, `deq2_relPure_at`) | `MsQueue.msqueue2_envG_whole` (concrete: `MsQueue.msqueue2_envG_whole_concrete`, with `codeMatchesWQ2`, `runnerMatchesWQ2`); no-fault `enqRuleQ2_noFault`, `deqRuleQ2_noFault` | `A64WholeMsQueue2`, `A64WholeMsQueue2Concrete` | 530 |
| Michael–Scott queue, 2 enqueues ∥ 2 competing dequeuers, one dequeue each (`msqueue3.kl`, `(1:X10=1 ∧ 2:X10=2) ∨ (1:X10=2 ∧ 2:X10=1)`; `EnvGCAdj`; msqueue2's protocol unchanged, ½/¼/¼ split of `head`/`tail`, dequeuer 1 holds the acquire ids, dequeuer 2 a token `tokD2`; the two swings differ by writer tid, so msqueue2's `head_pair` gives uniqueness) | `MsQueue.msqueue3_envG` (concrete: `ConcreteMsQueue3.msqueue3_envG_concrete`) | `MsQueue3Ghost`, `MsQueue3Final`, `MsQueue3VC`, `MsQueue3Smoke`, `MsQueue3VCGen`, `MsQueue3RelPure`, `MsQueue3Public`, `ConcreteMsQueue3` (on top of the `MsQueue*`/`MsQueue2*` files) | 1328 |
| the same, the three threads running the whole `.kl` image (as msqueue1's, three masks; runs `enq2_envGCAdj_at`, `deqA3_envGCAdj_at`, `deqB3_envGCAdj_at`, `enq2_relPure_at`, `deq_relPure_at`, `deqB_relPure_at`) | `MsQueue.msqueue3_envG_whole` (concrete: `MsQueue.msqueue3_envG_whole_concrete`, with `codeMatchesWQ3`, `runnerMatchesWQ3`); no-fault `enqRuleQ3_noFault`, `deqARuleQ3_noFault`, `deqBRuleQ3_noFault` | `A64WholeMsQueue3`, `A64WholeMsQueue3Concrete` | 645 |
| x64 unlocked `incl (%rdi)` (smoke, one thread; `EnvGLRX`; the counter's value is not tracked, `B := True`) | `LRSmoke.incRelX_rule`, `incRelX_noFault`, `incRelX_inv_init`; VC `incRelX_tripleEnv` (env rule `inc32_shared`) | `LRX64Smoke` (env rule in `LRX64VCGen`) | 187 |
| x64 MP with an unlocked `incl` release (`X64/mp_incl.kl`; writer on `EnvGLRX`, first end-to-end `ofSafelyEnvGLRX` use; new flag predicate `flagPredI`, initial flag message in release mode) | `MpInc.x64_mp_incl_envG` (concrete: `Concrete.x64_mp_incl_envG_concrete`) | `X64MpIncSpec`, `X64MpInc`, `X64MpIncVCGen`, `X64MpIncLink`, `X64MpIncRelPure`, `X64MpIncPublic`, `X64MpIncConcrete` (reuse `X64MpSpec`/`X64MpSmoke`/`X64MpLink`/`X64MpRelPure`/`X64MpPublic` names and the reader program) | 1012 |
| x64 `lock cmpxchg` spinlock (`spinlock_cmpxchg2.kl`) | `CmpxPublic.x64_cmpx_counter_envG'` (unconditional; `x64_cmpx_counter_envG` takes `Theorem1FChain`) | `X64CmpxLink`, `X64CmpxPublic`, `X64CmpxFinal`, `X64CmpxRelPure`, `X64CmpxVCGen`, `X64CmpxVC` | 591 |
| x64 Treiber stack push/pop (`X64/treiber_pp.kl`; `EnvGCX` with failing `lock cmpxchgq` releases, `Arch.tso`; popper on the covering layout `sAll`) | `TreiberX.x64_treiber_pp_envG` (concrete: `ConcreteTreiberX.x64_treiber_pp_envG_concrete`); no-fault `pushRuleX_noFault`, `popRuleX_noFault` | `X64TreiberSmoke`, `X64TreiberVC`, `X64TreiberVCGen`, `X64TreiberRelPure`, `X64TreiberPublic`, `X64TreiberConcrete` (reuse `TreiberGhost` unchanged; ISA-neutral VCs `TreiberVCCommon` (482) and the link `X64RmwFailGhost` (141) excluded) | 1328 |
| x64 Dekker with `mfence` (`X64/dekker_mfence.kl`; store-buffering mutual exclusion; `EnvGX`, `Arch.tso`, empty plan; no SC-fence logic: memory-order facts `SBFact`/`sb_exclusion`; `(counter)` addressed as `(%rbx)`, see X64_KNOWN_GAPS) | `Dekker.x64_dekker_public`; no-fault `dkRule_noFault` | `DekkerSmokeX`, `DekkerVCX`, `DekkerVCGenX`, `DekkerLinkX`, `DekkerRelPureX`, `DekkerPublicX` (ISA-neutral `DekkerCore` 199, `DekkerFinal` 200 excluded) | 1127 |
| x64 SPSC ring (`X64/spsc_queue.kl`; plain `mov`s only, `EnvGTX`, `Arch.tso`; both threads on the take route; `buf0` handed back to the producer by the consumer's `head := 1` release plan) | `SpscX.x64_spsc_envG` (concrete: `SpscX.x64_spsc_envG_concrete`); no-fault `prodRule_noFault`, `consRule_noFault` | `X64SpscProg`, `X64SpscWP`, `X64SpscRelPure`, `X64SpscSpec`, `X64SpscRead`, `X64SpscVC`, `X64SpscVCGen`, `X64SpscPublic`, `X64SpscConcrete` | 2924 |
| AArch64 SPSC ring (`AArch64/spsc_queue.kl`; `LDAR`/`STLR` monotone counters, `EnvGTU`, `Arch.armv8`; both threads on the cumulative take route, the consumer may skip `tail := 1`; per-thread image) | `SpscA.a64_spsc_envG` (concrete: `SpscA.a64_spsc_envG_concrete`, with `codeMatches`); no-fault `prodRule_noFault`, `consRule_noFault` | `A64SpscProg`, `A64SpscSpec`, `A64SpscRead`, `A64SpscVCP`, `A64SpscVCC`, `A64SpscVCGen`, `A64SpscRelPure`, `A64SpscPublic`, `A64SpscConcrete` | 2771 |
| the same, both threads running the whole `.kl` image (the runner's executable; the producer over its mask, the dead `NOP` at `pdone` masked) | `SpscA.a64_spsc_envG_whole` (concrete: `SpscA.a64_spsc_envG_whole_concrete`, with `codeMatchesW`, `runnerMatchesW`); no-fault `prodRuleW_noFault`, `consRuleW_noFault` | `A64SpscWholeVCGen`, `A64SpscWholePublic`, `A64SpscWholeConcrete` (on top of the `A64Spsc*` files; link `A64Mask*` excluded) | 1026 |
| ticket lock (`ticketlock2.kl`: `ldadda` hand-out, `ldar` spin, `stlr` release; `EnvGTD`, first end-to-end use of the dispenser route `theorem1IIPureX_G₀_S_singleRmw`) | `TicketLock.ticket_counter_envG` (no fault: `tkRule_noFault`) | `TicketLockGhost`, `TicketLockVC`, `TicketLockSmoke`, `TicketLockVCGen`, `TicketLockPure` (purity + dispenser phases in one env, `dispPure`), `TicketLockPublic` | 1844 |
| ticket lock with an `ldaddal` hand-out (`ticketlock_al2.kl`, `ticketlock_al3.kl`; `EnvGTDR`: the ticket RMW may be release-kind, `next` never released by the plan; `Phase1TreeR`) | `TicketLock.ticket_al_counter_envG` (no fault: `tkRuleAl_noFault`; concrete: `ConcreteTicketAl.ticket_al_counter_envG_concreteN`/`concrete2`/`concrete3`, with `codeMatches`, `runnerMatches`) | `TicketAlSmoke` (with `vc_ldaddal`), `TicketAlVCGen`, `TicketAlPure`, `TicketAlPublic`, `ConcreteTicketAl` (reuse the `TicketLock*` files; link library `TicketREnv`, `TicketRLink`, `TicketRRuleLink`, `TicketRA64Link` excluded, 1354) | 702 |
| x64 ticket lock, verbatim (`X64/ticketlock3.kl`: `lock xaddl` hand-out on `(next)`, plain-load spin on `(owner)`, plain-store release of the loaded `owner` + 1; `EnvGTDRX`, `Arch.tso`; the runner image with its data trailer; no declarations, or the runner's strict sized ones) | `TicketX.ticket3_counter_envG_verbatim`, `TicketX.ticket3_counter_envG_runner` (no fault at `decls = {}`: `ruleTk3_noFault`; at `decls = ds`: `TicketX.ticket3_counter_envG_runner_noFault`, `X64NoFaultDLocks`; concrete: `TicketX.Concrete.ticket3_counter_envG_runner_concrete3`, with `codeMatchesTk3`, `runnerMatchesTk3`) | `TicketXPure` (`dispPureX`, `ticket_counter_ofX`), `TicketXVC`, `TicketXVCGen`, `TicketXPublic`, `TicketXRunner` (reuse `TicketLockGhost`, `TicketLockVC`, the link `TicketRX64Link`) | 1447 |
| x64 ticket lock with an unlocked `incl (owner)` release, verbatim (`X64/ticketlock2.kl`: `lock xaddl` hand-out on `(next)`, plain-load spin on `(owner)`, `incl (owner)` release, a load and a store; `Arch.tso`; the runner image with its data trailer; no declarations, or the runner's strict sized ones; not through the SLR link: a per-thread invariant on the timestamps of the thread's accesses, kept by every reachable step, and a final counting argument) | `TicketX2.ticket2_counter_envG_verbatim`, `TicketX2.ticket2_counter_envG_runner` (concrete: `TicketX2.Concrete.ticket2_counter_envG_runner_concrete2`, with `codeMatchesTk2`, `runnerMatchesTk2`; fault freedom: `TicketX2.ticket2_counter_envG_runner_faultFree`, `_runner_safe_faultFree`, with concretes) | `TicketX2Run` (`RunSim`, `TreeJ.runJ`), `TicketX2Env` (`tk2Env`, `JTk`, `runSim`), `TicketX2Reach` (`inv_reachable`), `TicketX2Final` (`FinW.finalVal`), `X64Ticket2VCGen` (`inc32_abs_shared_spec`, `tk2WorkerV_envG`), `X64Ticket2Public`, `X64Ticket2Runner`, `X64Ticket2FaultFree` | 2414 |
| x64 MP with an unlocked `incl` release, final flag value (`X64/mp_incl.kl`, `[f]=1`; writer on `EnvGLRVX`, loads with in-flight-aware `ClAtV`) | `MpIncV.x64_mp_incl_envGV` (hypotheses of `x64_mp_incl_envG`) | `LRValMpInc`, `LRValMpIncPublic` (library `LRValEnv`, `LRValLink`, `LRValRule`, `LRValRead`, `LRValX64`, `LRValX64VCGen` excluded, 884) | 426 |

## Shared helpers

- `Split.lean` (`Plan.Split.share`), `SplitD.lean` (`Plan.Split.shareD`: a
  share given takes the write set along; used by the CAS lock;
  `Plan.Split.share2D`: with a second, clamped location; used by the x64
  xchg lock).
- `SpinStart.lean`: the spinlock's ghost locations (`ghostSys`) and initial
  facts, shared by the CAS and x64 xchg locks.
- `MpEnvGStart.lean` (start and `NPSafe` of the MP rules) and
  `SLR/MpSpec.lean` (MP's start, initial ghost/erasure, `mp_final`): what the
  EnvG MP theorems need without the old hand-proved MP rules;
  `MpEnvGCheck.lean` holds the `type_of%` check against `mp_public`.
- `RuleLink.lean`: `InvGR.prepay_of_okAt`, the prepay body shared by
  `InvGR.prepay` (`EnvG`) and `InvGR.prepayTR` (`EnvGT`).
- x64 `vcgen` rules for 32-bit `add`/`test`/`xchg`/`mov $i`/`lock cmpxchg`
  are in `Kraken/MachineWP.lean` / `Kraken/EnvVCGen.lean`
  (`MachineWP.*32*_spec`, incl. `MachineWP.lock_cmpxchg32_shared_spec`).
- `Alias.lean`: `hoist_alias`, statement-preserving aliases used when an ISA
  copy is replaced by the neutral original.
- `RmwFailFwd.lean`: `envG_rmw_fail_getFwd` (a failed RMW keeps the
  forwarding items), shared by the CAS lock, the `casal` smoke and the x64
  cmpxchg lock.
- `SLR/StoreHelpers.lean`: `total_max_of_slot` / `total_max_of_thread` (a
  slot or thread holding all of `x` holds the total's maximal write).
- `TakeFinalCommon.lean`: `final_of_relWritesJS` (adequacy with taking
  threads); x64's `final_of_relWritesJSX` is an alias.
- `TakeNoFault.lean`: `NoFaultRuleS` (no-fault rule for `ThreadRuleRXGS`);
  x64's `NoFaultRuleSX` is an alias.
- `TakeVCGenCommon.lean`: the `EnvGT` simp set, its `FenceMono` instance and
  `takeEff_of_not_acq`; `TakeVCGen` (AArch64) re-exports it, x64's `X`
  lemmas in `TakeX64VCGen` are aliases.
- `post_of_halted_env` (`A64Link.lean`, `X64Link.lean`): `done` from a
  `Safely` judgment in any environment; every `post_of_halted_Q…` is a
  one-line application.
- `ConcreteX64Layout.lean`: the `.kl` runner's x64 text layout `klLayout` and
  the decidable `validLayout_of_cells`; `ConcreteCommon.lean`:
  `Config.init_mem` (`@[simp]`).
- `RmwGhostTakeCore.lean`: the ISA-neutral half of `RmwGhostTake.lean`
  (`EnvGTC`, `nodeSimT2_envGTC`, `LinkHypsTRC`, `InvGR.wpTRC`/`prepayTRC`,
  `ThreadRuleRXGS.ofEnvGTRC`); x64's `…I` names in `X64RmwGhostLink`
  (`EnvGTCI`, `LinkHypsTRCI`, `ThreadRuleRXGS.ofEnvGTRCI`, …) are aliases.
- `LinkRNoFault.lean`: `InvGR.q_at`, `noFaultRule_ofEnvGR_struct`,
  `noFaultRule_ofEnvGRC_struct`; x64's `InvGR.q_atX`,
  `noFaultRule_ofEnvGR_structX`, `noFaultRule_ofEnvGRC_structX` are aliases.
- `TreeMap.lean` (phase-1 shapes) and `MultiCommon.lean` (phase-2 shapes,
  `noFaultRule_ofEnvG2_struct`): the `EvTree.map` closure lemmas
  (`accessFree_map`, …, `phase1ShapeR_map`, `multiAccessS_map`,
  `noRelWrite_map`, `phase2Shape_map`; names in `AArch64.EnvG` for history);
  the `X64.EnvG` copies are aliases.
- `RuleLink.lean`: `InvG.prepay_of_firstStoreG`, the first-store prepay body
  generic in the link hypotheses (`valid` + the store permission);
  `InvG.prepay_of_firstStore{,2,3}` (`LinkHyps`/`LinkHyps2`/`LinkHyps3`) are
  instances.
- `LockVC.lean`: the swap-acquire spinlock's ISA-neutral table predicates and
  counter VCs (`LkLe`, `GoodC`, `Acq.*`, `H1`–`H3`, `QEnd` + `fence`,
  `fresh_join`, `LkLe.*`, `threadRes_lkLe`, `vc_ld_cG`/`vc_st_cG` from the
  Out/Facts interface at any `Arch`); the x64 xchg lock (`X64SpinVC`) and the
  `swpl` lock (`SwplLockVC`) alias or instantiate them.
- `X64MpSpec.lean` … `X64MpLink.lean`: the x64 MP reader generic over the
  flag predicate (`FlagLaw`: impure and `Good` at a non-zero low word;
  `WorldRG`, `MpPostG`, `slot_of_seenG`, `mp_finalG`, `R1G`/`R3G`/`R4G`,
  `vc_r*G`, `mpReaderX_envGPG`, `hB_RG`); `flagPred` (`x64_mp_public`) and
  `flagPredI` (`x64_mp_incl_envG`) are the instances (`flagPred_law`,
  `flagPredI_law`).
- `RmwGhostVCGenCommon.lean`: the `EnvGC`/`EnvGTC` simp set, step facts and
  `FenceMono` instances (the neutral half of `RmwGhostVCGen`); x64's
  `envGC_*X`, `envGTCI_*X`, `step_*FactsTCX` are aliases.
- `RmwFailRuleLink.lean`: `phase1ShapeF_map` (name in `AArch64.EnvG`); the
  x64 copy is an alias.
- `SLR/InitGhost.lean`: `initGhostAcq` / `erase_initGhostAcq`, initial
  erasure with **held acquire ids** at release-mode initial locations (no
  update ids); `MpInc.erase_mpIncInit` is an instance.
- `TreiberVCCommon.lean`: the Treiber stack's table predicates (`Pp`, `Pc`,
  `Pu0`, `Pu`, `Pd`, `GW`) and VCs (`vc_pop_*`, `vc_push_*`) over
  `EnvGC I A tid plan`, generic in the ISA and the architecture, the
  compare-and-swap given as `CasMatch op x y`; the x64 Treiber
  (`X64TreiberVC`) instantiates them at `cmpxOp64`, the Treiber proof's AArch64
  `TreiberVC.lean` at `casOp64` (`casOp64_casMatch`; the predicates
  unfold to the common ones at `isa`, memory/`GW` lemmas are aliases).
- `hoist_alias` (`Alias.lean`) also accepts a pair whose target already is
  an alias of its source, for renaming only (copies that mention an earlier
  alias, e.g. `EnvGTCI`).
- `TreiberVCCommon.lean`: `tParamsC` / `tLocs_tParamsC`, the parameters of
  `treiber_pp.kl` (either ISA) and their `TLocs`; x64's `tParamsX` is an
  alias and `tLocs_tPX` an instance. The Treiber proof's AArch64 `tParams` /
  `tLocs_tP` are still copies (same bodies).
- `Promising/SeqLinkTerm.lean`: `prop_ite` (a property of both branches of an
  `if`, at any `Decidable` instance). Both `dirs_no_fault` tactics
  (`EnvLinkTermX64.lean`, `EnvLinkTermAArch64.lean`) now run their first
  `simp` under `try` and close a leftover flag test (x64 `je`'s
  `CondCode.interp` instance) with it: the x64 Treiber proof's local `dirs_no_faultX`
  is gone and `TreiberX.prop_ite` is an alias.
- `RelPureEnvX64F.lean`: `CmpxPublic.final_of_relPureSafelyQX_tsoF'`, the
  unconditional x64 assembly step for `NPSafeF` rules (Theorem 1′ by
  `theorem1FChain`), moved from `X64RmwFailGhost.lean`.
- `SLR/StepRunCommon.lean`: `stepOne_run`, `optFence_mem_prom`,
  `succ_cases'` (one machine step as a run of the instruction's tree; an
  optional fence keeps memory and promises; `succs` as instruction or promise
  step), ISA-neutral, in `Kraken.Promising.SLR`. The ticket lock proof's
  `SingleRmw.*` copies are `hoist_alias`es of them.
- `AdjCore.lean`: the adjacent-RMW environment `EnvGCAdj` (`RmwOkCAdj`,
  `AdjAt`, `adj_of_readSuccs`, `envGCAdj_step_iff`, …) is the generic one:
  `RmwOkC.toCAdj` / `envGC_ok_toCAdj`, `TreeJLive.ofCAdj`,
  `NodeSimS2.ofCAdj`. `NodeRel.rmwC'` / `rmwRelC` (`RmwGhostLink`),
  `nodeSimS2F_envGC` (`RmwFailGhostLink`) and `InvGR.wpFC` /
  `prepay_of_okAtFC` (`RmwFailGhostRule`, via `LinkHypsFC.toFCAdj`) are
  instances of their `CAdj` versions.
- `RmwGhost.lean`: `prepayGenericRmw_of_ob`, the RMW prepay body with the
  obligation instantiated; `prepayGenericRmwC` and `prepayGenericRmwCAdj`
  (`AdjSpikeRule`) are instances.
- `AdjVCGenCommon.lean`: the `EnvGCAdj` simp set, `fenceInv_fenceLeCAdj` and
  its `FenceMono` instance (moved from `Treiber2VC`); `AdjVCGenA64.lean`:
  `safely_start_of_partialTripleEnv` (start in any environment), of which
  `qa64CAdj_of_partialTripleEnv` is an instance.
- `TreiberVCCommon.lean`, "Shared memory and step facts":
  `TreiberCommon.{prefix_append, WriteSnap.prefix, WriteSnap.tw_le,
  AnchorOk.prefix, read?_le_last, read?_mono, rmw_success_fwd,
  acq_pair_false, bv64_eq_of_sub_eq_zero}`; the Treiber proof copies are aliases
  or instances, the private `bv64_eq_of_sub_eq_zero` copies are gone.
- Ghost-exposing transports: `NodeRel.storeSG`, `NodeRel.rmwSG`
  (`LinkS.lean`), `NodeRel.loadTG` (`TakeLink.lean`) and `prepayGenericG`
  (`Prepay.lean`) state the originals' conclusions plus the ghost step
  (store: claims/acquire table/update ids kept, `u` grown; RMW: `rmwGhost`,
  read message unclaimed, env `coh l` above the read; load: `g` or the
  iterated take; prepay: `prepayGhost`). `storeS`/`rmwS`/`loadT`/
  `prepayGeneric` are re-proved from them, and the ticket link's
  `storeTD`/`rmwTD`/`loadTD`/`prepayGenericTD` (`TicketLink.lean`,
  `TicketRuleLink.lean`) are short transports of `TX` on top.
- `RuleLink.lean`: `CoreAt.prepay_of_firstStoreGX`, the first-store prepay
  body generic in the env's store judgment (side condition `Ex l`) and an
  erasure extension `Y`; `InvG.prepay_of_firstStoreG` (and so
  `InvG.prepayT`, `TakeRuleLink.lean`) and the ticket `InvGTD.prepay` are
  instances.
- Coherence helpers `readSuccs_getCoh_ne`, `writeSuccs_getCoh_ne`,
  `storeOut_getCoh_ne` (`LinkS.lean`) and `loadOutT_getCoh_ne`
  (`TakeLink.lean`), moved from `TicketLink.lean`.
- `DispenserPureA64.lean`: the single-RMW dispenser's purity-and-phase
  environment `dispPure`, `TreeJ.disp`, `DispSpec`, `dispSpec_step`,
  `DispSpec.ofProgram`, `DispSpec.holds_of_partialTripleEnv` (names in
  `TicketLock`), moved from `TicketLockPure.lean`.
- `TicketEnv.lean`: `EnvGTD`'s `FenceMono` instance, `fenceMono_le_envGTD`,
  `envGTD_step_*'` (names in `TicketLock`), moved from `TicketLockVC.lean`;
  `SLR/TicketX.lean`: `SingleRmw.XSame` (+ `refl`/`trans`/`append`/`get?`)
  and `Dispenser.CountInv.xsame`, moved from `DispenserRun`/`DispenserFresh`.
- Small shared facts: `EnvG.rmwOut_getFwd_ne` (`LockVC.lean`),
  `EnvG.takeAll_q_ge` / `EnvG.takeAll_q_slot` (`TakeAllWr.lean`), with the
  `TicketLock` names as aliases; `WriteSnap.get?_old'` / `get?_new'` moved to
  `Facts.lean` (the Treiber proof's `TreiberVC` copies are untouched);
  `Spinlock.sum_ite_inj` / `Spinlock.sum_add3` (`SLR/SpinInitRes.lean`) are
  public and `TicketLockGhost`'s private copies are gone;
  `SwplLock.read?_of_get?` is an alias of `SLR.read?_of_get?'`
  (`TreiberVCCommon`'s and `TreiberVC`'s copies are untouched).
- MsQueue, SPSC, cumulative take, Dekker and the x64 absolute-address programs:
  - `SpscCommon.lean`: the ISA-neutral SPSC ownership facts (`Full`, `Hold`,
    `KeepsFull`, `keepsFull_store`, `full_after`, `wr_after_ne`, …), reads
    under memory growth (`read?_le_last`, `read?_prefix`,
    `writeSnap_read?`) and `OkPred` (+ `refl`/`mono`); the `SpscX`/`SpscA`
    copies, `TakeUSkip.read?_prefix` and `Dekker.read?_le_last` are aliases.
  - `TakeUEnv.lean`: `takeEffU_keepsFull` (a cumulative take keeps a fully
    held location); `TakeUX64.takeEffU_wr_full` and `SpscA.takeEffU_full`
    are aliases.
  - `Kraken/EnvCfgAbs.lean`: `Program.after_last_of` (a fragment's
    `*_last` side condition by one `decide`; the 13 x64 verbatim-image
    `*_last` lemmas use it) and `Safely.uncountEnv` (`Safely.uncountV/T/M/S/R`
    are instances).
  - `X64TreiberAbsVCGen.lean`: `pusher_envGC_of` / `pusherFrag_last`, the
    pusher run in any code environment where `treiberPusherX` is placed;
    the image (`pusherV_envGC`) and mask (`pusherM_envGC'`) runs are
    instances.
  - Tactic macros: `cells_phase1X` (`X64MaskCore.lean`, the phase-1 cell
    script of the x64 mask fragments); `cells_lrX` (`LRX64.lean`,
    `dirs_lrX`'s per-cell script, unfolding `RelRegOrMem.interp`);
    `rel_ok`, `spsc_noNT_producer`, `spsc_noNT_consumer`
    (`X64SpscRelPure.lean`, shared with `X64SpscAbsVCGen`).
  - MsQueue: `erase_init_ghost2` (`MsQueue2Ghost.lean`; `erase_init2` /
    `erase_init3` are instances) and `wr_pair_false` (`MsQueueGhost.lean`;
    `tokE_pair_false` / `tokD2_pair_false` are instances).
- Masks, whole-image runs and the x64 MS queue:
  - `MaskCommon.lean`: the ISA-neutral part of the mask machinery
    (`Forall2` + `imp`/`map`, `forall₂_dropWhile`/`findSome?`/`of_getElem`/
    `getElem?`, `evTree_map_map`); the `X64MaskCore`/`A64MaskCore` names are
    aliases. (`CellMask`, `MaskOf`, `labels_mask`, `exec_of_mask`,
    `Program.maskKeep`, … stay per ISA: `Executable.labels`, `codeAt`,
    `instrStepEnv` and `Program` are per-ISA constants.)
  - Treiber runs over any `PlacedIn` code (`TreiberVCGen.lean`,
    `TreiberRelPure.lean`): `pusher_envGC_at`, `popper_envGC_at`,
    `treiberPusher_relPure_at`, `treiberPopper_relPure_at`; the per-thread
    triples (`PartialTripleEnv.of_runAtT`) and the whole-image runs of
    `A64WholeTreiberVCGen.lean` are instances (the scripts elaborate once).
  - `A64MaskHelpers.lean`: the plain-shape family `dirs_phase1_any`,
    `label_dirPhase1_any`, `byteArray_dirPhase1_any`,
    `phase1Tree_maskKeep_range`; the `SpscA`/`Relay`/`Treiber` whole-image
    copies are instances or aliases. `X64MaskLink.lean`: the x64 `F`
    counterpart `phase1TreeFX_maskKeep_range` (+ `label_dirPhase1FX_any`,
    `byteArray_dirPhase1FX_any`); the msqueue2/3 and Treiber mask shape
    proofs are instances.
  - `TreiberVCCommon.lean`: `rmw_snap_prefix`, `rmw_ghost`, `rmw_vle`,
    `rmw_res` at any ISA and architecture (`MsQueue`'s and `MsQueueX`'s
    copies are instances); `read?_le_last` is now `SpscCommon`'s.
  - MsQueue final steps: `msqueue{1,2,3}_final_of_hB` (`MsQueue*Public.lean`),
    shared by the per-thread and whole-image theorems.
  - X64 msqueue: `erase_init_ghostX` (`X64MsQueue2Ghost.lean`; `erase_init` /
    `MsQueue3X.erase_init3` are instances); the scoped tactics `d_cnt`,
    `p_absurd`, `cnt_all`, `msq_noNT_cases` of `MsQueueX`
    (`X64MsQueue2VCGen.lean`) serve msqueue3 too; the seven msqueue2/3 and
    treiber2 `*_last` lemmas use `Program.after_last_of`.
  - Tactic macro `cells_phase1FX` (`X64MaskCore.lean`): the per-cell
    `DirPhase1FX` script of the x64 verbatim images (five copies).
- Release-kind ticket RMWs, runners and declarations:
  - Generic RMW transports: `NodeRel.rmwSGP` (`LinkS.lean`; the written
    value is pure, either because the RMW is not an effective release,
    `rmwSG`, or because the plan never releases at the location, `rmwSGR`)
    and `NodeRel.rmwRelSGP` (`LinkR.lean`; the in-flight release RMW with the
    give-away condition at its own claimed slots, exposing the ghost step;
    `rmwRelS` and `rmwRelSG` are instances).
  - `TicketLock.vc_ldaddK` (`TicketLockVC.lean`): the ticket RMW VC in
    `EnvGTDR` for any acquiring kind; `vc_ldadda` (`EnvGTD`) and `vc_ldaddal`
    are instances.
  - Ticket lock workers: the scoped tactics `tk_worker_vcgen`
    (`TicketLockVCGen.lean`) and `tk_pure_vcgen` (`TicketLockPure.lean`) run
    the `vcgen` scripts of `tkWorker` and `tkWorkerAl`; `ticket_counter_of`
    (`TicketLockPublic.lean`) is the assembly behind `ticket_counter_envG`
    and `ticket_al_counter_envG`.
  - `FulfilAtomic.lean`: `atomic_of_append`, `fulfil_write_atomicTR` and
    `fulfil_write_atomic` (its second half), moved from `TicketRRuleLink`
    and `AdjSpike`.
  - `X64RunnerCommon.lean`: `runnerSameD`, `runnerMatchesDL`,
    `runnerMatchesDN`; the ten x64 `*Runner.lean` `runnerMatchesD` checks
    are instances.
  - `X64NoFaultD.lean`: no fault at the runner's declarations.
    `noFault_QX64MD_rootD`: the root access of a `QX64MD` thread's tree is an
    `S`-location (`within S`, the judgment `rootInJ`), so single-access trees
    are fault-free under declarations agreeing on `S` (`Decls.AgreesOn`).
    There are no-fault wrappers for every `…XMD` family and the tactic
    `decls_agrees_on`. The same-location
    extension (`RootSameD`) is in `X64NoFaultD.lean` (the
    single-access forms are its instances); `X64NoFaultDMpIncl.lean` has
    its per-cell check and the `EnvGLRV` family. The per-program
    `*_runner_noFault` theorems are in `X64NoFaultD{Locks,Mp,MpIncl}.lean`.
    The pointer programs are covered program-level by the value-invariant fault-freedom proofs (below).
  - `MemVals.lean`, `MemValsX64.lean`: **program-level**
    `Config.FaultFree` (every reachable configuration, any architecture,
    promises included) from a value reachability invariant `MemVals L V`
    (`Reachable.valInv`, `faultFree_of_valInv`) and per-thread value
    specifications `ValSpecX` in `(valEnv L V).within S`
    (`x64_faultFree_of_valSpecs`; at `L = ∅` from the purity specifications,
    `x64_faultFree_of_relPureSpecsQXD`). Instances with `_concrete` at the
    runner's configuration: `X64FaultFreeFixed.lean` (spinlock2/3,
    spinlock_cmpxchg2/3, dekker_mfence, ticketlock3, mp_relay3_xchg, mp_incl),
    `MemValsTreiberPP.lean`, `MemValsTreiber2.lean`, `MemValsMsQueue.lean`
    (msqueue2/3; VC script `msq_val_cases`). spsc and treiber_aba_tagged:
    the value-invariant fault-freedom proofs (`MemValsX64Spsc.lean`, `MemValsX64ABA*.lean`).
- The x64 ticket lock and the AArch64 declarations:
  - `DispenserPure.lean` (ISA-neutral): `TicketLock.dispPure` and
    `TicketLock.TreeJ.disp`, moved from `DispenserPureA64`;
    `TicketX.dispPureX` and `TicketX.TreeJ.dispX` are these definitions.
  - Ticket lock VCs generic in the architecture (`TicketLockVC.lean`, in
    `EnvGTDR`): `vc_ldaddKA`, `vc_ldarA`, `vc_ldrA`, `vc_strA`, `vc_stlrA`.
    `TicketLock`'s `Arch.armv8` VCs (`vc_ldaddK`, `vc_ldar`, `vc_ldr`,
    `vc_str`, `vc_stlr`) and `TicketX`'s `Arch.tso` VCs (`vcX_*`) are
    instances. `TicketLock.start_initG`: `start_init` and
    `TicketX.start_initX` are instances.
  - `TakeVCGenCommon.lean`: `takeEff_q_ge` and `takeEff_wr_fullG` (a load,
    take or no take, only adds to the write permissions and keeps a full
    one); `TicketX.takeEffX_q_ge` and `X64.EnvG.takeEff_wr_full` are
    instances.
  - `X64DeclsLink.linkHypsTDR_QX64MD` (masked, strict sized):
    `TicketX.linkHypsTDR_QX64MDX` is an instance.
  - Machine rules: `MachineWP.cmp32_reg_reg_spec` (`Kraken/MachineWP.lean`)
    and `MachineWP.lock_xadd32_abs_shared_spec` (`Kraken/EnvVCGenAbs.lean`),
    both `@[spec]`; `SpscX.cmp32_reg_reg_spec`,
    `MachineWP.cmp32_reg_reg_specX` and
    `MachineWP.lock_xadd32_abs_shared_specX` are instances (no longer
    `@[spec]`).
  - Declarations: `A64DeclsCommon.lean` (ISA-neutral) holds the originals;
    `X64VecDeclsFault`'s `Decls.Sized`, `Decls.resolve_ok_of_sized`,
    `EvTree.underDecls`, `EvTree.map_access`, `EvTree.map_underDecls`,
    `TreeJLive.underDecls`, `TreeJ.underDecls` (plain `def`s unfolding to these, or
    re-proved), and the twin shape lemmas of `X64VecDeclsLinkAdj` and
    `X64DeclsLink`, are instances of `Decls.StrictSized`, `EvTree.reresolve`,
    … .
- Runner-exact ticket locks, no fault at declarations, replayed steps:
  - `TicketCounterCore.lean` (ISA-neutral): `TicketLock.ticket_counter_core`,
    the ticket lock's assembly generic in the ISA, the architecture, the
    `NTFree` invariant and the per-thread phase cells `H tid b` (kept under
    `TreeJ.disp` at `tkGhost`'s purity predicate). `ticket_counter_of`,
    `ticket_counter_ofD` and `TicketX.ticket_counter_ofX` are
    instances. `TicketLock.tkSys` moved here; new `tkGhost_pure_x`/`_c`.
  - `DispenserPureA64.lean`: `DispSpec.HoldsD`, `DispSpec.holdsD_of_noDecls`
    and `dispSpec_stepD`, moved from `A64TicketRunner`.
  - `SpinStart.lean`: `CasSmoke.spin_counter_core`, the shell of the
    spinlock counter theorems (`l ≠ c`, zero threads, `Spinlock.adequacy`)
    around a `final_of_…` call; `spinGhost_pure_lk`/`_c`. The ten counter
    theorems (`cas_counter_envG`, `swpl_counter_envG`, their `_runner`
    forms; `x64_spin_counter_envG`, `x64_cmpx_counter_envG`, their
    `_verbatim` and `_runner` forms) are instances.
  - `X64NoFaultD.lean`: `EvTree.AtLocD`, `EvTree.RootSameD`,
    `noFault_underDecls_rootSameD`, `noFault_QX64MD_rootSameD` moved from
    `X64NoFaultDMpIncl` (the two definitions in the new
    `X64NoFaultDSame.lean`, so their equation lemmas keep their own `match`
    auxiliaries); `noFault_underDecls_rootD` and
    `noFault_QX64MD_rootD` are their instances (`rootSameD_of_rootOnlyD`).
  - `Promising/ReachCore.lean`: `reachStep_cases` (what a replayed step is);
    `reachStep_sound` and `Live.reachStep_instrBy` (`LiveReach`) are
    re-proved from it.
- Value-invariant fault freedom, AArch64 no fault at declarations:
  - `MemValsGen.lean` (ISA-neutral): `ValXA` (`ValX` with the store
    continuation asked only at `b = true ∨ xcl`), `ValX.toValXA`,
    `ValXA.mono` and the generic preservation lemmas `runTree_valXA`,
    `stepOne_valXA`, `threadNP_valXA`, `certWrite_valXA`,
    `Reachable.valInvA`, `faultFree_of_valInvA`, moved from
    `MemValsA64Core` (which now only forwards). The value-invariant fault-freedom proofs' `runTree_valX`,
    `stepOne_valX`, `threadNP_valX`, `certWrite_valX`, `Reachable.valInv`
    and `faultFree_of_valInv` are their instances (`ValX.toValXA`). The
    shared definitions (`valEnv`, `MemVals`, `ValX`, `memVals_write`,
    `ValInvAt`, …) moved to `MemValsBase.lean`, so `ValX` and `ValXA` keep
    their own `match` auxiliaries.
  - `NoFaultDCommon.lean` (ISA-neutral): the no-fault-at-declarations proofs' ISA-neutral originals,
    moved with their names: `Decls.AgreesAt`, `Decls.agreesAt_empty`,
    `EvTree.access_of_agreesAt` (from `X64VecDecls`), `Decls.AgreesOn`,
    `EvTree.RootInS`, `EvTree.RootOnlyD`, `accessFree_mapD`,
    `rootOnlyD_map`, `rootOnlyD_of_singleAccessS(2)`,
    `atLocD_of_accessFree`, `rootSameD_of_rootOnlyD` (from `X64NoFaultD`)
    and `noFault_reresolve_accessFree` (from `A64NoFaultDCommon`). New:
    `noFault_reresolve_atLocD` and `noFault_reresolve_rootSameD`, over
    `EvTree.reresolve`. x64's `noFault_underDecls_accessFreeD`, `…_atLocD`
    and `…_rootSameD` and AArch64's `noFault_reresolve_rootD` are instances.
    `A64NoFaultDCommon`'s twins (`Decls.AgreesAtA`, `Decls.AgreesOnA`,
    `EvTree.RootInSA`, `EvTree.RootOnlyDA`, `access_of_agreesAtA`,
    `accessFree_mapA`, `rootOnlyDA_map`, `rootOnlyDA_of_singleAccessS(2)`)
    are defined from, or proved by, the originals (same types and
    reducibility). `X64NoFaultDSame.lean` (`AtLocD`, `RootSameD`) is now
    ISA-neutral too.
  - `MemValsA64.lean`: `rmwOpBits_cas_val` (a 64-bit CAS writes its new
    value); `MsQueue.msqValA_cas`, `Treiber.treiberValA_cas` and
    `Treiber2.treiber2ValA_cas` are instances. `MsQueue.ValSpecA.ofImageA`
    and `MsQueue.holdsD_ofImageA` moved here from `MemValsA64MsQueue`
    (same names).
- Swap-lock runners and value-invariant fault freedom on x64:
  - `LockVC.lean` (ISA-neutral): `LockVC.vc_relG`, the xlock release VC
    (a write of `0` to `Lk`, `xlockPlan`'s split) from `H3`, for any ISA,
    architecture and store kind with the effective kind of a `tso` plain
    store; the outcome part asks only the ghost growing, the clean flag
    kept, and `xlockPlan`'s split above the coherence view of `Lk`.
    `X64Spin.vc_rel` (x64 `movl $0`), `SwplLock.vc_swpl` (`swpl`) and
    `SwpEnvG.vc_stlr` (`stlr`) are instances. `SwpEnvG.storeOk_of_storeKind`
    moved here (same name).
  - `MemValsX64.lean`: `DirsNoFaultCode.toEnvX` (statically fault-free
    non-data cells are fault-free where an environment runs them; a data
    cell has no environment step). The value-invariant fault-freedom proofs' alignment-tolerant
    `noFault_valSpecD_env` and `x64_faultFree_of_valSpecs_env` moved here
    from `MemValsX64ABA` (same names); `noFault_valSpecD` and
    `x64_faultFree_of_valSpecs` are their instances. `MemValsX64` now
    imports `MultiX64Align`.
- The x64 `incl` ticket lock and promise-free liveness:
  - `X64DeclsLink.lean`: `TicketX2.treeJ_of_QX64MD` (same name, moved from
    `X64Ticket2Public`), one instruction from `QX64MD` (strict sized
    declarations or none) under any tree judgment whose leaf condition holds
    at `QX64MD`. `relPureSpecQX_stepD`, `valSpecX_stepD` (`MemValsX64`) and
    `TicketX.dispSpecX_stepD` (`TicketXPure`) are its instances, through the
    reordering of their `HoldsD` into `QX64MD`.
  - `SLR/StepRunCommon.lean`: `stepOne_runK`, the successful outcomes of
    `stepOne` in full (the run of the tree from `stepOne`'s context, with
    state, promises, memory and log from the run, views but `vCAP`).
    `stepOne_run`, `TicketX2.stepOne_runV` and `Live.TicketStep.stepOne_out`
    are instances (`LiveTicketStep` now imports `StepRunCommon`).
  - `A64DeclsBridge.lean`: `exec_treeJ_of_safelyD`, the AArch64 twin of
    `treeJ_of_QX64MD` (one instruction from a `Safely` judgment with strict
    sized declarations, any tree judgment). `relPureSpec_stepD`
    (`A64DeclsLink`) and `TicketLock.dispSpec_stepD` (`DispenserPureA64`) are
    its instances.
  - `Promising/Rel.lean`: `Reachable.inv`, invariant induction over
    `Reachable` (a predicate kept by every `succs` step). `configInv_reachable`,
    `Reachable.valInvA` and `TicketX2.inv_reachable` use it.
  - Memory appends: `TicketX2.last_append`, `get?_append_new`, `append_snd`,
    `get?_append_cases` and `Dispenser.get?_append_cases` are instances of the
    existing `Memory.last_append`, `get?_append_last`, `append_time` and
    `get?_append_eq_some`.
  - `LiveTicketCex.lean`: generic lasso (`TicketCexG.LassoChecks`,
    `lassoG`, `lassoG_*`, `lassoTraceG`, `lasso_not_live`; same names, moved
    from `LiveTicketCexG`), with `lassoG_promiseFree`, `lassoG_weakFair`,
    `lassoG_weakFairInstr`. The runner-configuration lasso (`lasso_step`, …,
    `ticket_not_live_weakFair`) is its instance (`lasso_eq`, `lassoChecks`).
- Spinlock and x64 ticket-lock liveness (all ISA-neutral, under
  `Kraken/Promising/`):
  - `LiveSpinStep.lean`/`LiveSpinCommon.lean`: the instance-free
    `SpinStep.{wt_get, wt_tid, wt_ne, mem_frame, loc_ne}` and
    `SpinCommon.{evconst, step_or, adv, wt_self}` are the originals of
    `TicketInv.{wt_get, …, loc_ne}` and `TicketPF.{evconst, step_or, adv,
    wt_H}`, which keep their `ValidLayout (layout tkWorker)` instance
    arguments. New: `SpinCommon.pigeon` (`TicketInv.pigeon`,
    `TicketX64Inv.pigeon`) and `SpinCommon.size_eq` (the `size_eq` of
    `LiveSpin{Cas,Swp,X64Cmpx,X64Xchg}PF`). The four `getCoh_eq`
    (`TicketPF`, `TicketX64PF`, `SpinCasPF`, `SpinX64CmpxPF`) are
    `SpinSwpStep.getCoh_congr`; `LiveSpinCommon` now imports
    `LiveSpinSwpStep`.
  - RMW steps: `SpinStep.readLast_writeSuccs_exists` (new), the write half
    of an RMW reading the last write, at any architecture; `run_rmwo_exists`
    (`rmwFence = false`) and `TsoRmw.run_rmwo_tso_exists` (`true`, after the
    fence) use it. `SpinSwpStep.atomic_lastWrite_own` is
    `TsoRmw.rmw_reads_last`, `SpinSwpStep.spec_store_coh` is
    `TsoRmw.spec_store_coh` (same statement; both names kept, so with both
    namespaces open write `TsoRmw.spec_store_coh`), `coh_setCoh_le` is
    `Views.getCoh_le_setCoh`. `LiveSpinSwpStep` now imports `LiveTsoRmw`.
  - `LiveTrace.lean`: `Live.Spin.ProgressFrom` (same name, moved from the
    AArch64 file `LiveSpin.lean`), beside `LiveFrom`;
    `SpinX64Step.ProgressFromN` is defined as it. New: `PromiseBy.prom_ne`
    (`TicketCex.promiseBy_prom`, `TicketX64Cex.promiseBy_prom`).
  - `LiveLasso.lean` (new): the two-thread spin lasso generic in the ISA and
    the architecture (`Lasso.Spec`, `Spec.Checks`, `Spec.lasso`,
    `Spec.lasso_step`, …, `Spec.lasso_not_live`). `TicketCexG.lassoG_*`/
    `lasso_not_live` (at `lassoSpec`) and `TicketX64Cex.lassoX_*`/
    `lassoX_not_live` (at `lassoSpecX`) are its instances, through
    `LassoChecks(X).toSpec` and `lassoG_eq_spec`/`lassoX_eq_spec`.
- Program addresses, ticket-lock liveness and runner liveness:
  - Program addresses: `SLR/X64Trees.lean` (new; the x64 twin of the
    address part of `SLR/A64Trees.lean`): `layout_getElem`, `addrOf_step`,
    `addrOf_label`, `addrOf_ne_succ`, `addrOf_inj_gen` (generic in the
    per-program `isInstr`, which stays where it is), and the `x64cell`
    tactic macro. `SLR/A64Trees.lean` gains `addrOf_ne_succ`,
    `addrOf_inj_gen` and `a64cell`. The `addrOf_step`/`addrOf_label`/
    `addrOf_ne_succ`/`addrOf_inj` of `LiveX64TicketTrees`,
    `LiveX64Ticket2Trees`, `LiveSpinX64{Cmpx,Xchg}Trees`, `LiveTicketTrees`,
    `LiveSpinCasTrees`, `SLR/{X64Spin,Swp}Trees` and `LiveSpinSwpTrees`
    (`swpl_*`, `addrOf_ne_succ`, `addrOf_inj_gen`) are instances; their local
    `cell` macros expand to `x64cell`/`a64cell` (except `SLR/X64SpinTrees`,
    whose cell unfolding differs).
  - `LiveTicketGlobal.lean` (new, ISA-neutral): `TicketGlobal.TkFacts` (the
    ticket half of every ticket lock's `InvW`: `xmsg`, `tkLt`, `tkInj`,
    `tkSurj`), `TkFacts.frame` and `TkFacts.take` (with the pigeonhole).
    `tk_frame` and the ticket half of `inv_tkt` of `LiveTicketInv`,
    `LiveX64TicketInv` and `LiveX64Ticket2Inv` are instances.
  - `SpinCommon.trace_inv_of`: an invariant kept by every instruction step
    along a promise-free trace. The `trace_inv` of the three ticket and four
    spin `*Inv` files are instances.
  - `Live.memFair_lastWrite_false` (`LiveRank`): a reader of `l` that never
    catches up with the last write of `l` contradicts `MemFair`. The
    `stuck_false` of the four spin PF files and the `holder_false` of
    `LiveTicketPF`, `LiveX64TicketPF`, `LiveX64Ticket2PF` and `LiveTicketSem`
    are instances.
  - `Ticket2X64Inv.getCoh_eq` is `SpinSwpStep.getCoh_congr`;
    `Sem.withThread_get_self`/`withThread_get_ne` are `SpinStep.wt_tid`/
    `wt_ne`.
  - **Short-name clash** (not renamed): `spin_cmpx_live_pf_runnerN` and
    `spin_xchg_live_pf_runnerN` exist both in `Live.RunnerX64Spin`
    (declarations `ds`) and in `Live.SpinX64CmpxPF`/`Live.SpinX64XchgPF`
    (`decls = {}`). With both namespaces open, qualify them.
- Liveness on the semantic machine (ISA-neutral, under
  `Kraken/Promising/`):
  - `LiveSem.lean`, semantic traces: `TraceSem.{size_eq, step_prefix,
    prefix_le, get_le, same_or_instr, adv, instr_inf}` (dot notation on a
    `TraceSem A fuel I`; generic in the ISA, the architecture and, for
    `instr_inf`, the promise-drop bound `B`), `Sem.infOften_pigeon` and
    `Sem.stepSem_size`. The same-named lemmas of `TicketSem` and
    `SpinSemCas` (and `SpinSemCas.{inf_pigeon, size_stepSem}`) are
    instances, as is `Sem.weakFairInstrSem_of_weakFairSem`. Future x64
    copies (e.g. `step_prefix`/`same_or_instr`/`adv`) can be
    instances of the same `TraceSem.*` lemmas.
  - `LiveSem.lean`, solo runs: `ThreadNPn.mem_prefix`, `Sem.NACertG`,
    `Sem.nacertG_replay` (generic in the step invariant and the per-step
    replay), `Sem.instrEnabledSem_of_step`/`instrEnabledSem_of_nacertG`.
    `threadNPn_prefix`, `nacert_replay` and the tail of
    `instrEnabledSem_of` of `TicketSolo` and `SpinSemSolo` are instances;
    both `NACert`s unfold to `NACertG Arch.armv8` (bodies unchanged).
  - `SpinSem.ProgressFromSem` (same full name) is defined in `LiveSem.lean`
    beside `LiveFromSem`.
  - `LiveSemShape.lean` now holds `SpinSemShape.{mem_writeSuccs_c, readNext_vwOld, run_rmwo_p,
    spec_rmwo_p, replay_rmwo}` (same full names; `LiveSpinSemShape`
    forwards them). `SemShape.mem_writeSuccs`, `spec_rmw_p` and
    `replay_rmw` are their instances. `LiveSemShape` now imports
    `LiveSpinSwpStep`.
- x64 and SWP liveness on the semantic machine (ISA-neutral unless noted,
  under `Kraken/Promising/`):
  - `TraceSem.{step_prefix, prefix_le, get_le, same_or_instr, adv}` now also
    have `X64SemTicket` and `X64Sem2Ticket` instances (at `Arch.tso`; the
    old names keep their section layout instances), and both `getCoh_eq` are
    `SpinSwpStep.getCoh_congr`. New `TraceSem.{wt_self, get_persist}`
    (`SpinSemCas`'s are instances). `SpinSemSwpLive` uses the layout-free
    `TraceSem.*` lemmas instead of `SpinSemCas`'s at `casLayout`.
  - Solo runs: `threadNPn_prefix`, `nacert_replay` and the `fin` helper and
    tail of `instrEnabledSem_of` of `X64SemSolo`, `X64Sem2Solo` and
    `SpinSemSwpSolo` are instances of `ThreadNPn.mem_prefix`,
    `Sem.nacertG_replay`, `Sem.instrEnabledSem_of_step`/`_nacertG`; their
    `NACert`s unfold to `NACertG Arch.tso`/`NACertG Arch.armv8`.
    `X64SemStep.toNat_xv` (x64) is the layout-free `xv_toNat`.
  - `LiveSemShape.lean` now holds zero/gap/swap facts
    (same full names `SpinSemSwpSolo.{ZeroAt, ZNot, Gap, TopZ, ZeroAt.mono,
    ZNot.mono, Gap.mono, read_le, val_zero, read_zero, read_zero_gap,
    writeIn_le, run_swp_p, spec_swp_p, spec_load_w}`), so x64 files can use
    them; `run_swp_p` reuses `rmwPost_eqC`.
- x64 spinlock liveness on the semantic machine (ISA-neutral unless noted,
  under `Kraken/Promising/`):
  - `SpinX64SemCmpx.{wt_self, get_persist}` (x64) are instances of
    `TraceSem.*`. `SpinX64SemShape.replay_choose` (x64 TSO shape) is the
    generic form of the `replay_choose` of `SpinX64SemXchgSolo` and
    `SpinX64SemCmpxSolo` (both instances).
  - `LiveSemShape.lean`: the layout-free `SpinSemSwpSolo.{zeroAt_back,
    zNot_back, topZ_back, gap_back}` (`SpinSemSwpSolo`'s `ZeroAt.back` etc.,
    which keep their `[Layout]`, and `SpinX64SemXchgSolo`'s copies are
    instances); `SpinSemSwpInv.{get_new, get_none}` and
    `SpinSemSwpLive.{exists_least, exists_greatest}` moved here (same full
    names; `SpinX64SemXchgInv`/`SpinX64SemXchgLive` copies are instances).
  - `LiveWfInstr.lean`: `ThreadNP.stateInv` and `dropBounded_of_stateInv`
    (generic in the state invariant and the drop bound). The
    `threadNP_sinv`/`dropBounded_of_sinv` of `X64SemStep`, `X64Sem2Step`,
    `SpinX64SemCmpxSolo`, `SpinX64SemXchgSolo`, `SpinSemSolo`, `TicketDrop`
    and `SpinSemSwpSolo` are instances.

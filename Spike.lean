/-
The bridge spike: a Kraken run related to a WeakCore run on a two-thread
release/acquire program (`Spike/Bridge/FINDING.md`).

This root imports the ISA-independent part (relation, simulation, progress,
the spinning-reader variant, the per-construct judgement with its consumer,
`Spike.Lib.Thread`, the stack regions, `Spike.Lib.Region`, and the store
side of the memory relation, `Spike.Lib.Mem`; the per-IR-form environment
relation, `Spike.Lib.Form`; certification under a code semantics such as
`Kernel.certExec`, `Spike.Bridge.CertC`; the source thread's one-word
memory steps, `Spike.Lib.SrcMem`; the ISA-free part of the one-thread consumers,
`Spike.Lib.Consumer1`; segments under the typing guard,
`Spike.Lib.Typed`; the lowering's placements as word places, `Spike.Lib.Place`; runtime
read-modify-writes, `Spike.Lib.RtRmw`). The AArch64
and x64 halves (`Spike.Bridge.A64`, `Spike.Bridge.A64Loop`, `Spike.Lib.A64`, `Spike.Lib.A64Loop`,
`Spike.Lib.A64Block`, `Spike.Lib.A64Flow`, `Spike.Lib.A64Hello`, `Spike.Lib.A64Cfg`,
`Spike.Lib.A64Nodes`, `Spike.Lib.A64Switch`, `Spike.Lib.A64Dead`, `Spike.Lib.A64Abort`,
`Spike.Lib.A64Call`, `Spike.Lib.A64Print`, `Spike.Lib.A64PrintL`, `Spike.Lib.A64ExtToy` (a closed
`Correct` on the canonical target `canonical 1`, through `Scc.Sem.StepSim`), `Spike.Lib.A64ExtToy2`
(a refused `write` aborts at the `writeErr` site: `Correct`'s abort clause), `Spike.Lib.A64Typed`,
`Spike.Lib.A64Consumer`, `Spike.Lib.A64Correct` (`Correct` for a one-thread
program on `canonical 1` from node obligations), `Spike.Lib.A64PromShared` (`PromShared` from node
obligations), `Spike.Lib.A64CorrectP` (`Correct` with `PromShared` discharged),
`Spike.Lib.A64CorrectNW` (and `WriteNoProm` from `NoWrite`), `Spike.Lib.OvfAbort` (the overflow abort's
source justification), `Spike.Lib.CertClosed`, `Spike.Lib.A64TailNoFul` (`WriteNoProm` from a closed tail
after the `write`), `Spike.Lib.A64AbortW` (the overflow abort path inside `W`: the local
block, the dispatcher at code 1, the stub), `Spike.Lib.A64StubFacts` (`SFacts` at the stub's states),
`Spike.Test.A64StubFactsSat`, `Spike.Lib.AbortSrc` (the abort's source facts from `AbSrc`),
`Spike.Lib.A64AbortPlace` (`Placed` from `AbSrc`'s `SRep`), `Spike.Test.A64AbortPlaceSat`,
`Spike.Lib.A64PhRec` (the phase record: `InstOk` from the runtime's layout and A6), `Spike.Test.A64PhRec`,
`Spike.Lib.A64StubW` (the overflow stub's nodes inside `W` with `SFacts`, from `InstOk`), `Spike.Test.A64StubW`,
`Spike.Lib.SegLag` (a segment with the source control held back: `SegW.lag`), `Spike.Test.SegLag`,
`Spike.Lib.SegS` (segments at any call depth: `FrameRun`, `OutS`, `SegWS`), `Spike.Test.SegS`,
`Spike.Lib.SrcMemN` (the memory rows' source steps keeping the allocation count),
`Spike.Lib.SrcFrames` (source steps at any call depth: `LocalStepS`, `LocalRunS`, the frame steps),
`Spike.Lib.HookOK` (the source hooks the consumers accept, `HookOK P p`: none, or WeakCore's extern step
with no exit event in its event list; `HookOK.none`, `HookOK.wc`),
`Spike.Lib.AllocSrc` (the source `newBuf` step under `Inv1`: `src_newBuf_stepZ`, `newBufZero`),
`Spike.Lib.AllocRow` (the allocator's arena contract `ArenaOK` and the allocation row: `row_alloc`),
`Spike.Lib.AllocInv` (a one-thread run's allocation invariants: `CtrAt`, `FreshInv`, `AllocInv`),
`Spike.Lib.FreshSrc` (the source's next allocation label is fresh: `fresh_of_memRel`), `Spike.Lib.HeapAbort`
(the heap abort's source facts and justification: `HeapReady`, `abortJustified_heap_source`),
`Spike.Lib.A64ConsumerS` (the one-thread consumer at any call depth: `NodesS`, `RS`, `correctKS`),
`Spike.Lib.X64ConsumerS`, `Spike.Test.X64ConsumerS` (its x86-64 twin), `Spike.Lib.X64SegInstS`,
`Spike.Test.X64SegInstS` (the x86-64 twin of `A64SegInstS`), `Spike.Lib.X64CallS`,
`Spike.Lib.X64CallSA`,
`Spike.Test.X64CallS` (the x86-64 twins of `A64CallS` and `A64CallSA`: `call_ndS`, `call_nd_FWKS`, `call_ndSA`, the
frame-indexed `call_ndSF`),
`Spike.Lib.Rt.X64SegsS` (the x86-64 runtime's start chain at depth, `_start`'s call included: `entry_segWS'`,
`startU_segWS`), `Spike.Lib.X64SFactsS1` (`SFactsS.ofSFacts`, `.ofSFactsAt` on x86-64), `Spike.Lib.LowerX64.StartSegS`
(`x64_start_segWS`, region depth `D + 56`), `Spike.Test.X64StartSegS` (their axioms),
`Spike.Lib.LowerX64.UPostS`, `Spike.Test.LowerX64UPostS` (the user function's post with a frame run: `UPostS`,
`uPostS_exit`),
`Spike.Lib.X64PlacedS` (the suspended frames' placement, in stack slots through a call: `PlacedS.ofFrames`,
`FramesPlacedIn.push`, `.of_eq`; `EnvSmallS.push`),
`Spike.Lib.X64FramesPlacedI`, `Spike.Lib.X64SFactsAtS`, `Spike.Test.X64FramesPlacedI` (the frames placed in slots or
immediates through a call: `FramesPlacedInI`, `.push`, `.of_eq`, `.of_cKept`, `framesPlaced_callTo`,
`slotPlacedI_of_srep`; `SFactsS` at a real pair at depth for owned words of the frames: `SFactsS.ofSFactsAtO`,
`.ofSFactsAtI`),
`Spike.Lib.LowerX64.BodyWS1` (an `Accepted1` body's blocks at depth inside `BodyWS0`: `blkW_bodyS1`,
`bodyWS0_lag`), `Spike.Test.X64BodyWS1` (their axioms),
`Spike.Lib.LowerX64.BlocksC1`, `Spike.Test.LowerX64BlocksC1` (the x86-64 code of an `Accepted1` block with
calls, the twin of `LowerA64.BlocksC1`: `Emits`, `emitInst_call1_inv`, `emitInst_allIns`, `emitTerm_allIns`,
`instsCode_allIns`, `callBlk_code`, `callSite_run`, `callArgs_eq`), `Spike.Lib.LowerX64.BlocksC1Code`,
`Spike.Test.LowerX64BlocksC1Code` (the x86-64 code predicate of an
`Accepted1` block with calls, one arm per instruction: `CodeC`, `BlC`, `BlocksCodeC`; the `Cd` instance `CdC` and
`codeC_of_seg`, `cdOf_cdC`, `cdOf_blC`, `hgap_of_lays`; a call's return address in the phase `blC_ph`;
from the placement checks `codeC_block`, `blocksCodeC`, `entryCodeC`,
`fnCodeC`, `fnCodeC_of_fnPh1`, `fnCodeC_ofPlaceOK`, `hgap_ofPlaceOK`), `Spike.Lib.LowerX64.BodyC`,
`Spike.Test.LowerX64BodyC`
(a lowered `Accepted1` body with plain calls as one segment at fixed frames on x86-64, the calls assumed, the
nodes carrying the thread pointer: `bodyC_segS`, `ExitC`, `CallC`, `SubCd`, `RetOne`, `fresh_callC1`),
`Spike.Lib.LowerX64.NodeTp`, `Spike.Test.LowerX64NodeTp` (x86-64 body nodes carrying the thread pointer in the `%fs`
base `ND.withTp`, no covered instruction writing it `arun_fsBase`; the per-construct edges `BlkEdge` (`add_edge`,
`store_edge`, `sub_edge`, `br_edge`, `jmp_edge`, `ret_edge`) lifted to them: `BlkEdge.tp`, `BlkEdge.seg`,
`BlkW.withTp`, `BlkW.nodeW`), `Spike.Lib.LowerX64.FnC`, `Spike.Test.LowerX64FnC` (an
x86-64 function with calls, prologue then body: `prologue_body_segT`, `fnC_segS`; with a parameter's spill
`proInCP`, `prologue_body_segTP`, `fnC_segSP`), `Spike.Lib.LowerX64.ProgC`,
`Spike.Test.LowerX64ProgC` (every x86-64 function with plain calls one segment by the call order, the calls a premise:
`FnCode`, `FnSpecC`, `fnSpecC_of`, `fnSpecC_all`, by index `fnSpecC_allI`; `scc_rt_main`'s user function at depth
from its exits `userCallWS_of_exitC`; the prologue's spills `hps_of_spills`; `FnCode.monoT`),
`Spike.Lib.LowerX64.ProgCB`, `Spike.Test.LowerX64ProgCB` (every function's segment from the premises at the contexts:
the calls from `callC_of` at `CallPre`, the callees from their `FnSpecC` at `CalleePre`: `CalleePre.seg`,
`at_rsp0`, `fnSpecC_all_ofPre`), `Spike.Lib.LowerX64.CtxC`, `Spike.Test.LowerX64CtxC` (the functions' contexts
down the calls: `CtxB`, `rbR_base`, `calleeR_base`, a call keeping them `CtxB.call`, from `CalleeF` `CtxB.callF`
with the frames placed `framesPlaced_calleeF`, `FramesPlacedInI.cons1`, `envSmall_calleeF`, `lookupS_filter_ne`,
`lookupS_filter_eq`; the callee's entry node `rsOf_param`, `nj_callee`; the contexts `CxOkC`, the
abort fragment `AbC`, `CxOkC.hab`), `Spike.Lib.LowerX64.PreC`, `Spike.Test.LowerX64PreC`
(the premises at the contexts from the placement check, the code facts with no frames limit: `callPre_of`,
`CodeFactsS`,
`argTy_callee`, `calleePre_of`, `fnSpecC_all_ofPlaceOK`, `Pairwise2.get?`), `Spike.Lib.LowerX64.MainC`,
`Spike.Test.LowerX64MainC` (the user `main` from the placement check: the aborts at their contexts held back
never end `abC_lag`; `main`'s context, premises and return `mainCtxB`, `argTy_main`, `mainPre_of`, `uPostS_ret`;
`scc_rt_main`'s user function at depth `userMainSW_of`; the placement check's packaging
`userMainSW_ofPlaceOK` from `fnCodes_ofPlaceOK` (the code facts with no frames limit)),
`Spike.Lib.LowerX64.ProWS`, `Spike.Test.LowerX64ProWS` (a code
block's prologue inside the body's fragment at depth from its code facts: `proW_bodyS`, `spillsOk_of_hps`;
with saved registers inside `SFacts`, `proW_sfactsP`), `Spike.Lib.LowerX64.CallBlkW`, `Spike.Test.LowerX64CallBlkW`
(a call's blocks inside the body's fragment at depth: a covered `ret`-free block of the code `blkW_bodySC`, the
call's `callq` `blkW_callq`, the callee's entry `nodeW_calleeEntry`; the coverage `okBlk_argLoad`,
`noRet_argLoad`, `okBlk_xHead_call`), `Spike.Lib.LowerX64.CallNodes` (a call's nodes, the callee's
interface and the straight-line steps), `Spike.Lib.LowerX64.CallC`,
`Spike.Test.LowerX64CallC` (a plain call, no depth counter: `CallC`, `callC_of`; its walk `argP_seg`,
`calleeP_seg`, `retP_seg`), `Spike.Lib.LowerX64.BodyWSC`,
`Spike.Test.LowerX64BodyWSC` (the
body's construct blocks with calls inside the consumer's facts at depth: `blockAt_sub`, `cd1_of_subCdC`,
`hWbS_of`, `hWsS_of`), `Spike.Lib.LowerX64.FnCodeOf`,
`Spike.Test.LowerX64FnCodeOf` (every code block's `FnCode` from `placeOKAt`: `InWalkC`, `fresh_env1`,
`fnCode_ofPlaceOK`, `fnCode_ofPlaceOKR`),
`Spike.Lib.LowerX64.CalleeRow`, `Spike.Test.LowerX64CalleeRow` (a call site's rows of
the stack need table from `PlaceOK`, the twin of `LowerA64.CalleeRow`: `needOk1_row`, `mem_callees_func1`,
`hasAddChk_func1`,
`needOk1_of_fnPh1`, `calleeRow_of_fnPh1`, the frames `size + 8`, `sd + 8 + 8 + ng ≤ nd`; `calleeRow_name_of_fnPh1`
under the hypothesis `UserInj`), `Spike.Lib.LowerX64.EmitLabels`, `Spike.Lib.LowerX64.UserInj`,
`Spike.Test.LowerX64UserInj` (each function's label in scc's x86-64 code cells, in order: `PreP`, `textN`,
`emitFuncs_labels`, `lowerAll_cells`; distinct code block symbols from `PlaceOK`'s distinct labels:
`labs_nodup_of_labelsNodupL`, `user_inj_of_placeOK`, `userInj_of_placeOK`, `calleeRow_name_of_placeOK`),
`Spike.Lib.LowerX64.CalleeRoom`, `Spike.Test.LowerX64CalleeRoom` (a function's and its callees' stack room
from `PlaceOK` on the region's lower bound: `NeedRoomX`, `ownRoom_of_placeOK` (`lo ≤ -(sd + 8 + s)`),
`calleeRoom_of_placeOK` (the callee's room at `lo + sd + 16`), `mainRoom_of_row` (at `-needD fr n`, slack `40`)),
`Spike.Lib.LowerX64.LimRoom`, `Spike.Test.LowerX64LimRoom` (a function's and its callees' stack limit room
from `PlaceOK` at their entry `%rsp`s: `LimRoomX`, `frame_of_fnPh1`, `ownLim_of_placeOK`, `ownLimBv_of_placeOK` (the
prologue's `v ≤ rsp - 8 - size`), `calleeLim_of_placeOK`, `mainLim_of_rows`, `mainRow_of_placeOKAt`),
`Spike.Lib.LowerX64.MainD`,
`Spike.Test.LowerX64MainD` (`main`'s user depth `D` for `x64_start_segWS` from
`placeOKAt` and `CfgNeedOk`, no frame bound: `mainD_of_placeOKAt`),
`Spike.Lib.A64PlacedS` (the suspended frames placed in stack slots at depth: `FramesPlacedIn`, `PlacedS.ofFrames`,
`EnvSmallS.push`),
`Spike.Lib.A64SegInstS` (its obligations from one segment at any call depth: `SFactsS`, `inst_of_segWS`, `correctKSPE`),
`Spike.Lib.A64CallS` (a source call node: the callee's body in a pushed frame, `call_ndS`; its ghost frame
condition `CallGF`, `CallGF.ret`, `call_ndSG`),
`Spike.Lib.A64CallSA` (`call_ndS` with a callee that may abort, `call_ndSA`),
`Spike.Lib.Rt.A64SegsS` (the runtime's start chain at depth, the user function a `UserCallWS`: `startU_segWS`),
`Spike.Lib.Rt.A64ExitF` (`main`'s exit from pending frames: `MainExitF`, `exitGroup_of_mainExitF`,
`MainExitFA`, `MainExitFA.ofS`, `MainExitFA.ofF`, `exitGroup_of_mainExitFA`, `exitTail_segWSF`),
`Spike.Lib.A64CallSF` (a machine call node whose callee returns at any frames: `call_nd_FWKSF`; its ghost frame
condition named: `MainGFr`, `MainGFr.ret`, `call_nd_FWKSFG`),
`Spike.Lib.Rt.A64MainSSF` (`NxF`, `MainCallWSF`, `MainCallWS.toF`, `mainS_segWSF`, `mainES_segWSF`,
`startS_segWSF`: `main` returning at pending frames),
`Spike.Lib.Rt.A64MainS0` / `Spike.Lib.Rt.X64MainS0` (the latter imported by `Spike.X64`: `scc_rt_main` from
the marshalling block `mainS0` after the setup call's return, the user function and the `exit_group` tail:
`mainS0_segWSF`),
`Spike.Lib.Rt.X64MainS0Sw` (imported by `Spike.X64`: `mainS0_segWSF` at the switch region and its frame
condition, a setup bottom key's `h0`: `mainS0_segSwF`),
`Spike.Lib.Rt.A64MainSSB` (the setup block's call at its ghost frame condition: `SetupCallWSB`,
`SetupCallWS.toB`, `SetupCallWSB.toS`, `SetupGF`, `mainSC_segWSB`, `mainS_segWSFB`, `mainES_segWSFB`,
`startS_segWSFB`; `main`'s call at its ghost frame condition: `MainCallWSFB`, `MainCallWSF.toB`,
`MainCallWSFB.toF`, `MainGF`, `mainS_segWSFBM`),
`Spike.Lib.LowerA64.MainExitF` (`main`'s exit from its body's exits at pending frames: `UPostRF`,
`UPostRF.ofPost2`, `uPostRF_ret`, `uPostRF_exit`, `ExitC2SLF`, `mainCallWSF_of_exitC2SLF`),
`Spike.Lib.LowerA64.MainBot` (`main`'s callee at the bottom frame under `MainGFr`: `MainBot`, `mainBot_ofGF`,
`mainBot_seg`, `mainBot_segK`, `mainBot_exitStk`),
`Spike.Lib.LowerA64.SetupHCall` (the setup block's call is a source call, `hcall`: `callTo_setupTerm`,
`CallTo.unique`, `hcall_of_setupOf`, `hcall_setupStart`),
`Spike.Lib.LowerX64.SetupHCall` (x64 twin: `callTo_setupTerm`, `CallTo.unique`, `hcall_of_setupOf`,
`hcall_setupStart`),
`exitTail_segWSF`),
`Spike.Lib.SegLagSF` (`SegWS.lag` at any frames: `LagF`, `SegWS.lagF`; `main`'s source held at a callee's `ret`),
`Spike.Lib.SegLagSC` (`SegWS.lagF` with its side conditions at the held-back pairs: `SegWS.lagC`,
`QuietFrom`, `LagOk`, `qtail`, `quietFrom_heldAt`, `HeldAt`, `not_quietFrom_newBuf`),
`Spike.Lib.SegLagS` (a segment at depth with the source held back at depth 0: `SegWS.lag`, `LagS`, `MsAgree`,
`RtReads`, `ownIncl_of_indep`),
`Spike.Lib.SegGood1`, `Spike.Test.SegGood1` (a segment at depth from `Good1` pairs keeps them `Good1`:
`SegWS.good1`),
`Spike.Lib.Frames1` (an `Accepted1` program's frame runs reach only subterms of its bodies: `Good1`, `good1_run`),
`Spike.Lib.A64SFactsS1` (`SFactsS` at the empty frames from `SFacts` at a `Good1` pair: `SFactsS.ofSFacts`),
`Spike.Lib.LowerA64.StartSegS` (the loaded thread's run one segment at depth, any callee room `D`: `a64_start_segWS`),
`Spike.Lib.LowerA64.BodyWS1` (an `Accepted1` body's blocks inside the facts at depth: `BodyWS0`, `blkW_bodyS1`,
`bodyWS0_lag`),
`Spike.Lib.LowerA64.UPostS` (the user function's post at depth `UPostS`, `main`'s exit after a frame run `uPostS_exit`),
`Spike.Lib.LowerA64.NodeTp` (body nodes carrying the thread pointer `ND.withTp`, edges and block facts lifted
to them: `BlkEdge.tp`, `BlkW.withTp`, `BlkW.nodeW`),
`Spike.Lib.LowerA64.BodyC` (a lowered `Accepted1` body with calls one segment at the caller's frames, the call
call a premise: `bodyC_segS`, `CallC`, `ExitC`, `SubCd`, `codeC_*`, `SegWS.seq_left`),
`Spike.Lib.LowerA64.BlocksC2Code` (the code predicate of an `Accepted2` block: `CodeC2`, `InstsC2`,
`CodeC2_append`, `BlocksCodeC2`, the construct blocks `Kind2`),
`Spike.Lib.LowerA64.BlocksC2Seg` (an `Accepted2` block's code after its label gives `CodeC2`: `codeC2_of_seg`,
`codeC2_block` at `BlC2`, the call arm `callSeg`, `inst2_allIns`, `term2_allIns`, `CodeC2.mono`),
`Spike.Lib.LowerA64.AllocRa` (a call's return-address facts for its callee from `BlC2`: `blC2_hra`, and
`blC2_notAb` off the write abort's pcs by `pc_ne_of_inRun`),
`Spike.Lib.LowerA64.FnCode2Of` (each `Accepted2` compiled block's placement and code facts from `placeOKAt`:
`fnPh2_ofPlaceOK`, `fnCodeC2_of_fnPh2`, `fnCodeC2_ofPlaceOK` at `CodeC2`/`BlocksCodeC2` and `BlC2`),
`Spike.Lib.LowerA64.UserInj2` (distinct `Accepted2` compiled block symbols from `PlaceOK`: `user_inj2_of_placeOK`),
`Spike.Lib.LowerX64.BlocksC2Seg` (x64 `codeC2_of_seg`, `codeC2_block` at `BlC2`, the call arm `callSegX`,
`emitInst2_allIns`, `emitTerm2_allIns`, `emitInst_callN1_inv`/`emitInst_callN0_inv`, `CodeC2.mono`),
`Spike.Lib.LowerX64.FnCode2Of` (x64 `fnPh2_ofPlaceOK`, `fnCodeC2_of_fnPh2`, `fnCodeC2_ofPlaceOK`),
`Spike.Lib.LowerX64.FnCodeL` (x64 code at `CdCL`, off the write abort's labels: `codeC2_of_segL`,
`codeC2L_block`, `fnCodeC2L`, `fnCodeC2L_ofPlaceOK`; generic `CdCQ`, `codeC2_of_segQ` in `BlocksC2Seg`),
`Spike.Lib.LowerX64.UserInj2` (x64 `user_inj2_of_placeOK`),
`Spike.Lib.LowerA64.Body2Arms` (`CodeC2`'s arms: `codeC2_addChk`, `codeC2_subSat`, `codeC2_br`, `codeC2_ret`, a `ret`
of any number of words `codeC2_retN` via `retLoads`/`term_retN_inv`),
`Spike.Lib.Src.LitPt2` (an `Accepted2` body's walk facts: `LitPt` at the literal walk, `EnvTy2` at the
lowering's walk, `litPtB`/`litPt_of_B`, `prodOf_noRefProd`),
`Spike.Lib.Src.Walk2Of` (the walk facts of an `Accepted2` block from `Accepted2`: `callTs_ofAccepted2`,
`decl2_setup`, `walk_rel_decl'`, `walk_relB_decl`, `callArg_ofAccepted2`, `retOne_ofAccepted2`,
`walk2_ofAccepted2`, `locBaseReg_ofAccepted2`, `litPts_ofAccepted2`, `countsB_ofAccepted2`,
`xchgsB_ofAccepted2`), `Spike.Lib.LowerA64.Walk2Of` / `Spike.Lib.LowerX64.Walk2Of` (`RetOk` of an
`Accepted2` block of result `Int`: `retOk_ofAccepted2`),
`Spike.Lib.LowerA64.Node2` (the nodes of an `Accepted2` body at `NJB`: `bodyN2`, `pendN2`, `AbJ2`, `abortN2`,
`RetJ2`, `retN2`),
`Spike.Lib.LowerA64.Body2` (`body2_segS`'s premises at `bodyN2`: `CallC2`, `NewBufC`, `LaneC`, `PrintCallC`,
`ContC`, `LetAt`, the multi-word `ret`'s `RetOk`, `ExitC2`),
`Spike.Lib.LowerA64.Body2Seg` (the `Accepted2` body's induction from per-construct premises: `PtF`/`ContF`,
`AddC2`, `SubC2`, `PureMv2`, `SplitMv2`, `UnpackMv2`, `IfC2`, `RetC2`, `seg_cont`, `body2_segS_of`),
`Spike.Lib.LowerA64.Entry2` (`entry_atEC`: the loaded thread at `_start`'s node with any source control),
`Spike.Lib.LowerA64.Start2Facts` (`Obl2A`'s start facts at the loaded thread: `hst2_of`, `htk0_2`, `hab0_2`),
`Spike.Lib.LowerA64.Rest2OfA` (`Rest2A` from the start's and the landings' segments: `S0A`, `StartsSA`, `Open2A`,
`rest2A_of`),
`Spike.Lib.A64XchgSeg` (an exchange on AArch64 as one segment at any plain word load/store: `exec_ldrX`/`exec_strX`
for the register-offset form, `LdAt`/`StAt`, `holdLdG_ndW`, `xchgStG_ndW`, `XchgSeg.xchg_segW`; x86-64's in
`Spike.Lib.X64XchgSeg`), `Spike.Lib.LowerA64.XchgOff` (`ldrOff`/`strOff` in all three forms as a prefix and one
`LdAt`/`StAt` at `b + disp`: `ldrOff_form`, `strOff_form`),
`Spike.Lib.LowerA64.LaneSeg` (a lane store's two instructions as one exchange segment, the source side abstract:
`inst_xchgLoad_inv`, `inst_xchgStore_inv`, `CodeAt.append`, `XchgW`, `lane_segW`),
`Spike.Lib.LowerA64.LaneC2` (`LaneC` from `lane_segW`, `xchg_site`, `NJB.xchg2`: `insts_xchg`, `group_elem2`,
`HeapOffF`, `LaneH`, `laneC_of`),
`Spike.Lib.LowerA64.NewBufC2` (`NewBufC` from `newBuf_blkW` under `tpXa` and `SegW.keepTPN`, `NJB.newBuf2`:
`insts_newBuf`, `args3_step`, `nbJ1`, `AllocW2`, `nbArgs_seg`, `nbCall_seg`, `nbStore_seg`, `nbRet_seg`, `newBufC_of`;
the fresh-label route's tail from `Ea` at an extending label map: `nbJS`, `newBufC_tail`),
`Spike.Lib.LowerA64.PrintCallC2` (`PrintCallC` at `bodyN2`: `print_code`, `NJB.printUnit`, `printJL`, `printJ`,
`PrintBlkW`, `PrintW`, `PrintWE`, `printSys_src`, `printCallC_of`; the twin of `Spike.Lib.LowerX64.PrintCallC2`;
`print`'s states under frame conditions that know the call: `PrintSlots`, `PrintBlkW'`, `PrintW'`, `PrintWE'`,
`printCallC_of'`),
`Spike.Lib.LowerA64.HeldC`, `Spike.Lib.LowerA64.PrintCallC2H`, `Spike.Lib.A64CallSAH`,
`Spike.Lib.LowerA64.CallC2H` (the held return on AArch64, twins of the x86-64 modules: `HeldC`, `HeldCtl`,
`HeldC.lagF`, `CallC2H`, `PrintCallCH`; `printCallCH_of` with the hold node `printNRH` (`printCallCH_of'` at
`PrintW'`, `PrintWE'`); `call_ndSFH`;
`callC2H_of` from `callC2_of`'s premises and `hWH` at the result store's node `retCN2`, with `heldND`,
`calleeC_seg2H`, `resC_seg2H`, `resC_segS2H`),
`Spike.Lib.LowerA64.LagC2` (the non-call constructs' premises held back under `LagOk`: `addC2_lag`,
`subC2_lag`, `ifC2_lag`, `retC2_lag`, `pureMv2_lag`, `splitMv2_lag`, `unpackMv2_lag`, `contC_lag`),
`Spike.Lib.Src.PrintSite` (the output extern's operand at the call site, used by `printCallC_of`:
`groupL_ownSlice`, `printSite_of`),
`Spike.Lib.LowerA64.Body2SegOf` (the `Accepted2` body's construct premises from the edges and
the moves at `ofEnv2`: `addC2_of`, `subC2_of`, `ifC2_of`, `retC2_of`, `pureMv2_of`, `splitMv2_of`, `unpackMv2_of`,
`body2_segS`),
`Spike.Lib.LowerA64.Node2Edges` (the edges at `bodyN2`/`pendN2`, at `ofEnv2 env`: `add_edge2`, `sub_edge2`,
`store_edge2`, `br_edge2`, `jmp_edge2`, the one-word `ret_edge2`, any words' `ret_edgeN2`),
`Spike.Lib.Src.RetB` (the source facts at a callee's return for the caller: `RetB`, `RetB.frame`, the
layouts' `RetL`, `RetL.words`, `RetL.int`), `Spike.Lib.Src.GroupOpds` (a caller's facts at a call `EnvQ`;
`Fresh.ofEnv2`),
`Spike.Lib.LowerA64.RetNB` (`retN2` with `RetB`: `retNB`, `ExitC2B`, `ExitC2B.toC2`; x86-64's in
`Spike.Lib.LowerX64.RetNB`),
`Spike.Lib.LowerA64.CallC2` (`CallC2` from the call's code, blocks and callee segment at `EnvQ`: `csN2`,
`retCN2`, `exN2`, `CalleeF2`, `instsC2_call`, `argC_seg2`, `blC_seg2`, `calleeC_seg2`, `resC_seg2`, `callC2_of`;
x86-64's in `Spike.Lib.LowerX64.CallC2`),
`Spike.Lib.LowerA64.CtxC2` (the contexts at a call of an `Accepted2` body, from `CalleeF2`:
`slotPlacedI_of_slotRepAt`, `framesPlaced_calleeF2`, `envSmall_calleeF2`, `CtxB.callF2`; x86-64's in
`Spike.Lib.LowerX64.CtxC2`),
`Spike.Lib.FormE` (the symbolic relation up to a buffer's literal lengths, so a node follows a buffer the walk
allocated at `newBufTy`: `Ty.eraseLen`, `SRepE`, `sstepE_sound`, `srunE_sound`, `NodeJE`, `NodeJ.toE`,
`NodeJE.run`, `NodeJE.step`; back to `SRep` at the source's types: `SEnv.retype`, `SRepE.toSRep`; `NJB` is at
`NodeJE`),
`Spike.Lib.Src.EnvBGhost` (a new buffer at any label by a ghost memory, `NJB`'s `L`/`sm`/`B` being per-node
ghosts: `ghostMem`, `heapLit_ghostMem`, `labelsIn_ghostMem`, `EnvB.newBufG` (`EnvB.newBuf` without its one-thread
label and freshness), `close_elem2`, `eraseLen_newBuf`),
`Spike.Lib.Src.NJBNewBuf` (the node invariant past a buffer allocation at the allocator's label: `group_newBufTy`,
`opLit_newBuf`, `NodeJE.newBuf2`, `NJB.newBuf2` at `EnvB.newBufG`'s ghosts),
`Spike.Lib.Src.NodeJEMono` (the node invariant's representations carried to an extending label map:
`LocRep.mono_lbl`, `WordRep.mono_lbl`, `WordsRep.mono_lbl`, `SRepE.mono_lbl`, `NodeJE.mono_lbl`),
`Spike.Lib.Src.LevelMono2` (the source facts at a larger level: `LvlLe`, `lvlLe_upd` (a fresh label unplaced
and without size), `Reach.lsize_none`, `SlotRepAt.mono_lbl`, `AbSrcL.mono_lbl`, `EnvQ.mono`, `NJB.mono`),
`Spike.Lib.Src.NJLB2` (the edges' source facts at `NJB`: `NJB.litMask_one` at `ofEnv2`, `NJB.add_ovf_term`
(its abort's `AbSrcL` at `SEnv.retype`), `NJB.asLanesV`, `litMask_of_grp`),
`Spike.Lib.Src.NJLBEnv2` (the code-free moves at `ofEnv2`: `NJB.pure_move2`, `NJB.split_move2`,
`NJB.unpack_move2`; `sevalAt_ofEnv2L`, `sevalAt_ofEnv2_one` under `GrpL`; `envFr_sFr`, `group_opds`),
`Spike.Lib.LowerX64.Entry2` (`entry_atXEC`: the loaded thread at `_start`'s node with any source control),
`Spike.Lib.LowerX64.Start2Facts` (`Obl2X`'s start facts at the loaded thread: `hst2X_of`, `htk0X_2`,
`hab0X_2`),
`Spike.Lib.LowerX64.Rest2Of` (`Rest2X` from the start's and the landings' segments: `S0X`, `StartsSX`, `Open2X`,
`rest2X_of`),
`Spike.Lib.LowerX64.HeldTail` (`W2` at a pair held through `main`'s return tail, the last construct a call
returning its result or a literal: `HeldTail`, `frameRun_heldTail`, `placedS_heldTail`, `w2_heldTail`;
`BlkW.w2`'s parts there: `nodeJ_heldTail`, `w2Part_heldTail`; `notWrite1_of_abs`; `placedS_ret_reg`;
a tail block or node inside `W2` in one step: `Ret0`, `HeldS`, `blkW_heldTail`, `nodeW_heldTail`),
`Spike.Lib.LowerA64.HeldTail` (the AArch64 twin: `HeldTail`, `w2_heldTail`, `nodeJ_heldTail`, `w2Part_heldTail`,
`notWrite1_of_abs` at `x8 = 94`, `blkW_heldTail`, `nodeW_heldTail`),
`Spike.Lib.LowerX64.HeldTailExit` / `Spike.Lib.LowerA64.HeldTailExit` (the `exit_group` tail inside `HeldS`: its
stack store covered and its `syscall`/`svc` a fault, so no `WrAt`: `nodeW_noWr_syscall`, `xExitW_noWr`,
`xExitW_heldS`; `nodeW_noWr_svc`, `exitW_noWr`, `exitW_heldS`),
`Spike.Lib.LowerA64.HeldTailRet` / `Spike.Lib.LowerX64.HeldTailRet` (`HeldS`'s `Ret0` at a held callee's `ret`
from the result register: `ret0_of_frameStep`, `ret0_of_X0` / `ret0_of_rax`, `ret0_of_retCN2` / `ret0_of_retCP2`;
`RetReg`, `nodeW_ret0`, `blkW_ret0`),
`Spike.Lib.LowerX64.RetSFacts2` (`SFacts` at `dumN n` for a construct's or `main`'s `ret` block (`Kind2`) at a
node with the frame's offsets and the saved pair: `okBlk_kind2`, `hret_kind2`, `blkW_sfacts_k2P`, `blkW_sfacts_k2`,
`blkW_sfacts_ret2`, `blkW_heldTailN`'s `hS`),
`Spike.Lib.LowerA64.RetSFacts2` (the AArch64 twin at `main`'s `ret` block only: `okBlk_ret2`, `hret_ret2`,
`blkW_sfacts_ret2P`, `blkW_sfacts_ret2`),
`Spike.Lib.LowerA64.Kind2SFacts` (the AArch64 twin at every `Kind2` block: `hret_kind1`, `okBlk_kind2`,
`hret_kind2`, `blkW_sfacts_k2P`, `blkW_sfacts_k2`),
`Spike.Lib.LowerA64.CxBlk2Of` (a context's `Kind2` body and pending-store blocks inside `W2` at the
main-ret guard, the AArch64 twin of `Spike.Lib.LowerX64.CxBlk2Of`: `posOff_fall_subCdLE`, `blkW_abSt_k2`,
`blkW_w2K2`, `cxBlk2_ofW2`),
`Spike.Lib.LowerA64.UserAbR` / `Spike.Lib.LowerX64.UserAbR` (a user block ending in a `ret` keeps the write
abort's phase: `blkW_abSt_posR`, `blkW_abSt_subCdLR`),
`Spike.Lib.LowerA64.MainRetPos` / `Spike.Lib.LowerX64.MainRetPos` (`scc_rt_main`'s return point after `bl`/`call fn`
is off the write abort, the `ra` of `main`'s return block: `posOff_mainRetS`, `mainRetS_eq`, `posOff_mainRetU`,
`mainRetU_eq`),
`Spike.Lib.LowerA64.Body2SegHF` / `Spike.Lib.LowerX64.Body2SegHF` (`main`'s return tail with the source held at a
callee's `ret`: `heldRN`, `BlkEdge.heldRN`, `seg_heldRN`, `exitC2SLF_of_heldRN`, `heldRetOk_let`,
`HeldTailCX`, `body2_segS_ofXH`, `held_segX`; x64 `retSegH`, `heldTailCX_of`),
`Spike.Lib.LowerA64.HeldTailSlot` / `Spike.Lib.LowerX64.HeldTailSlot` (`HeldS`'s `Ret0` along `main`'s `ret b` block
from the frame's result cell: `wordRep_slot`, `RetSlot`, `nodeW_ret0_slot`, `blkW_ret0_slot`, `frameStep_of_heldRun`,
`retSlot_of_heldRun`; x64 `blkW_heldS`),
`Spike.Lib.LowerA64.RetHeldW` (`main`'s `ret b` block inside `W2` at the held frames: `NoStr`,
`arun_slot_of_noStr`, `retBlk_noStr`, `retBlk_slot`, `retSlot_heldRN`, `retHeld_hW`),
`Spike.Lib.LowerA64.RetHeldAb` (`main`'s `ret b` block keeps the write abort's phase at the held frames:
`fallBlk_retLoads`, `retBlk_fallR`, `retBlk_last`, `retBlk_pc_heldRN`, `retHeld_hab`),
`Spike.Lib.LowerX64.RetHeldW` (x64 twin of both, at any node: `RetI`, `RetD`, `retD_retDirs`, `retDirs_slot`,
`retDirs_last`, `retDirs_pc_bodyN2`, `retSlot_bodyN2`, `retHeld_hab`, `retHeld_hW`),
`Spike.Lib.LowerA64.HeldRes` / `Spike.Lib.LowerX64.HeldRes` (the held frame's result in a region cell, the
`hx` of `retHeld_hW` / `retSlot_bodyN2` at the held call: `lookupS_held`, `regionOff_of_rsOf`, `hx_held`),
`Spike.Lib.LowerA64.MainTailA` (`main`'s return tail at the held frames end to end, one segment to
`ExitC2SLF` from the walk's facts: `mainTailA_seg`),
`Spike.Lib.LowerA64.MainTailP` (the print arm, the source held at `print`'s `ret ()`: `heldRNU`,
`BlkEdge.heldRNU`, `exitC2SLF_of_heldRNU`, `blkW_ret0_nil`, `blkW_abSt_ret2`, `mainTailA_segP`, `heldP_segA`,
`heldTailCX_of`),
`Spike.Lib.LowerX64.MainTailP` (its x64 twin: `heldRNU`, `BlkEdge.heldRNU`, `exitC2SLF_of_heldRNU`,
`blkW_ret0_nil`, `mainTailX_segP`),
`Spike.Lib.LowerX64.MainTailX` (the x64 call arm: `main`'s `ret b` block at the held callee's `ret` to
`ExitC2SLF`, `mainTailX_segC`),
`Spike.Lib.LowerA64.RetS` / `Spike.Lib.LowerX64.RetS` (a `ret` read by its group placements, frame registers pinned:
`RetJS`, `retNS`, `RetJS.words`, `ret_edgeS`),
`Spike.Lib.LowerA64.Body2SegX` / `Spike.Lib.LowerX64.Body2SegX` (the body's segment at any exit `X`, and to
the exits by placements: `body2_segS_ofX` (a literal walk fact `Lk` at the `ret`), `ExitC2S`, `retC2S_of`,
`body2_segS_ofS`),
`Spike.Lib.LowerA64.RetSL` / `Spike.Lib.LowerX64.RetSL` (the exits by placements with the source facts for
the caller at the return type: `retNSL`, `ExitC2SL`, `.toS`, at `int` `.toB_int` via `RetJS.toJ2_int`;
`ret_edgeSL`, `retC2SL_of`, `body2_segS_ofSL` over the literal walk's `ret`s at the type's layout),
`Spike.Lib.LowerX64.MainExit2` (`main`'s exit from an `Accepted2` body's exits at `int`: `UPostR` (a frame
run from the pair's control to `RetV`), `RetJS.retV_int`, `uPostR_ret` (the return as `uNx`), `uPostR_exit`
(`MainExitS` under any memory side placing `Placed`), `userCallWS_of_exitC2SL`),
`Spike.Lib.LowerX64.MainCall2` (the user `main` after a setup block at depth from its exits:
`mainCallWS_of_exitC2SL`, `MainCallWS` at `UPostR`),
`Spike.Lib.LowerX64.MainExitF` (`main`'s exits held at pending frames: `UPostRF`, `uPostRF_ret`,
`uPostRF_exit` (`MainExitFA`), `ExitC2SLF`, `mainCallWSF_of_exitC2SLF`, `MainCallWSF` at `UPostRF`),
`Spike.Lib.LowerX64.MainBot` (the twin of `LowerA64.MainBot`, imported by `Spike.X64`: `MainBot`, `mainBot_ofGF`,
`mainBot_seg`, `mainBot_segK`, `mainBot_exitStk`),
`Spike.Lib.LowerA64.ProgC2` (every function of an `Accepted2` program one segment: `FnCode2`, `ProEdge2`,
`FnSpecC2`, `BodySpecC2` to `ExitC2SL`, `fnSpecC2_of_body`, `bodySpecC2_of`, `fnSpecC2_allI` over the call order,
`CalleePre2`; a plain call's callee segment `CalleePre2.segB`, `hcal_of`),
`Spike.Lib.Src.CallOrder2` (a plain call at a term still to lower in a compiled block's body, `TailOf`, every
point of the lowering walk one, `lowerEnvs2_tail`, names an earlier compiled block: `body2_tail`, `body2_callT`,
`body2_call`, `decl2_of_split`, `body2_of_compiled`, `callOrder2T`, `callOrder2`),
`Spike.Lib.Src.AddFree` (a body with no `let x = a + b` at a `TailOf` point: `addFreeT`, `tailOf_addFree`; no
overflow abort state at such a block),
`Spike.Lib.Src.HeldLit2` (under `heldRetOk` accepting a literal only after `print` with its one index, a literal
held tail follows `print`: `hlitP_of_heldRetOk`, `hlitP_of_mainRetOk`, `mainCallWSF_ofPlaceOKHV`'s `hlitP`),
`Spike.Lib.LowerA64.HordC2` / `Spike.Lib.LowerX64.HordC2` (`fnSpecC2_allI`'s call order at `compiled2 p`:
`hord_ofAccepted2`),
`Spike.Lib.Src.ParamsNodup` (a function's parameter registers are distinct: `regIdx_inj`, `paramsR_nodup`),
`Spike.Lib.LowerA64.ProEdge2Of` (`ProEdge2` from the prologue's spills: `SpillsAt`, `ParamSpillN`,
`paramSpillN_of_spills`, `frRegs_arg`, `proEdge2_of`, `proEdge2_ofSpills`),
`Spike.Lib.LowerX64.ProEdge2Of` (its x86-64 twin, the stores' cell sizes `zs`, `%rbp` at `-8`: `SpillsAt`,
`ParamSpillN`, `paramSpillN_of_spills`, `xFrRegs_arg`, `proEdge2_of`, `proEdge2_ofSpills`),
`Spike.Lib.Src.Entry2` (a plain callee's entry at the source: `entry2_rep`, `entry2_njB`, `entry2_slotRep`),
`Spike.Lib.LowerA64.ProEdge2Callee` / `Spike.Lib.LowerX64.ProEdge2Callee` (`ProEdge2` at a plain callee's entry
`calleeN` from the stack limit's facts: `spillAt_param`, `cE_of_callTo`, `proEdge2_ofCallee`),
`Spike.Lib.LowerA64.ProEdge2UN0` (`ProEdge2` at the setup function's entry `uN0`, a `Unit` parameter:
`proEdge2_ofUN0`; twin of the x64 file),
`Spike.Lib.Src.SliceGhost` (a slice relocated to a bounded ghost memory: `sliceL_ghost`),
`Spike.Lib.Src.Entry2M` (`main`'s entry after the setup block: `grpL_transport`, `entry2G_njB`,
`entry2G_slotRep`, `wordsRep_mainArg`, `wordsSmall_of_rep`, `slotRep_setupCont`),
`Spike.Lib.LowerA64.ProEdge2UNM` (`ProEdge2` at `main`'s entry `uNM` after the setup call: `spillsAt_rsOf`,
`argX_eq`, `proEdge2_ofUNM`),
`Spike.Lib.LowerX64.ProEdge2UNM` (its x86-64 twin, in `Spike.X64`: `spillsAt_rsOf`, `paramSpillN_rsOf`,
`argXs_getD`, `retXs_getD`, `proEdge2_ofUNM`),
`Spike.Lib.Src.Walk2Facts` (a compiled block's walk facts for `FnCode2`: `fresh_env2`, `compiled2_facts`,
`lcx2`, `lits2`, `TailAt2`, `Walk2Facts`, `walk2_src`, `walk2Facts_ofAccepted2`, `walk2_srcA`),
`Spike.Lib.Src.ContNR` (no bare `ret` after a `+`, a `-` or an `if`'s `else` at a held body's terms: `ContNR`,
`contNR_of_heldRetOk`, `contNR_of_tail`, `contNR_tailAt2`, `ContNR.qAdd`, `ContNR.qSub`, `ContNR.qIf`),
`Spike.Lib.LowerA64.FnCode2Build` / `Spike.Lib.LowerX64.FnCode2Build` (every compiled block's `FnCode2` from
the placement check at `CdCLE`/`BlC2L`: `fnCode2_ofPlaceOKR`, `fnCode2_ofPlaceOK`, `fnCode2Of`, `fnCode2Of_spec`),
`Spike.Lib.LowerX64.ProgC2` (its x86-64 twin: `FnCode2`, `entryN2`, `ProEdge2`, `proSeg2` into `rbR R`,
`BodyAt2`, `BodySpecC2`, `FnSpecC2` to `ExitC2SL` in `rbR R`, `fnSpecC2_of_body`, `rbR_facts`, `bodySpecC2_of`,
`CallIn2` over `TailOf`, `fnSpecC2_allI`, `CalleePre2`, `.segB`, `hcal_of`),
`Spike.Lib.LowerA64.BodyPt2` / `Spike.Lib.LowerX64.BodyPt2` (a compiled body's segment from any resumption
point of its lowering walk: `BodyPt`, `bodyPt_entry`, past a call / a buffer `BodyPt.call`, `BodyPt.newBuf`,
`bodyAtPt2`; with the walk facts stated directly: `BodyPtW`, `BodyPt.toW`, `bodyPtW_entry`, `BodyPtW.call`,
`BodyPtW.newBuf`, `bodyAtPt2W`),
`Spike.Lib.Src.Stk2` (records aligned with the source's frames, chained by a key: `StkOkL`, `.cons`, `.uncons`,
`.length_eq`, `.mono`; above some bottom frames: `StkOkB`, `.bot`, `.cons`, `.uncons`, `.mono`, `stkOkB_of_stkOkL`),
`Spike.Lib.LowerA64.Stk2` (the suspended frames of an `Accepted2` program, the levels' static stack invariant:
`StkFr`, `StkKey`, `StkLink`, `StkFrOk`, `StkOk` above bottom frames, `CxOkS`, `CxOkS.bot`, `CxOkS.call`,
`StkOk.uncons`, `StkFrOk.link`, the stack-depth bound `StkRoomA`, `stkRoomA_of_le`, `limOk_callee_ofStk`),
`Spike.Lib.LowerA64.LimLvl2` / `Spike.Lib.LowerX64.LimLvl2` (the stack limit's facts at any level: no placed
label covers a runtime word at a placement reachable in `arOf` (`rtFree_ofArena`, `rtFree_lvl_ofPlaceOK`), `LimOk`
under `msOfAX` at any frames (`limOk_toAXF`, `limOk_lvl_ofPlaceOK`), a callee's prologue limit facts at the bound
`StkRoomA` / `StkRoomX`: `limOk_callee_lvl`; the x86-64 twin imported by `Spike.X64`),
`Spike.Lib.LowerA64.LandStk2`, `Spike.Lib.LowerX64.LandStk2` (an allocation's landing with its suspended frames,
the levels' landing family: `LandStk`, `landStk_xa`; on x86-64 also the argument loads' code and the `callq`
at their sizes; the x86-64 twin imported by `Spike.X64`),
`Spike.Lib.LowerA64.MainExit2` (the user `main`'s exit from its `Accepted2` body's exits: `MainPost2`,
`retV_of_retJS_int`, `mainPost2_of_exit` from `ExitC2SL` at the empty frames, `mainExit2_of_retV`,
`mainExit2_of_post`: `mainS_segW`'s `hexit` under `msOfAX`),
`Spike.Lib.LowerA64.MainCall2` (the user `main` after a setup block at depth from its exits by placements:
`mainCallWS_of_exitC2SL`),
`Spike.Lib.LowerA64.SetupCall2` (the framed setup call from its body's exits, twin of the x64 file: `SRetR`,
`uPostSR_ret`, `setupCallWS_framed`, `SPostC`, `hPS_framed`),
`Spike.Lib.LowerA64.SetupCallC2` (`h0`'s `hS` from the setup function's `FnSpecC2` and its `CalleePre2` but
the edge, the edge by `proEdge2_ofUN0`: `setupCallWS_ofFnSpec`, `MainCallWSF.ofCtl`; the
x86-64 twin `Spike.Lib.LowerX64.SetupCallC2`),
`Spike.Lib.LowerA64.PlacedSPostC` (the setup call's continuation placed through the result registers, twin of
the x64 file: `SPostC.placed`, `SPostC.placedS`, `OffImm`, `regVal_idx`),
`Spike.Lib.LowerA64.HPlSOfSPostC` (the marshalling block's states placed after the setup call from `SPostC`,
twin of the x64 file: `argX_eq_argRegs`, `placeVal_slot`, `hPlS_ofSPostC`),
`Spike.Lib.LowerA64.RtMainXF` (`h0` with a setup block, `main` returning at pending frames: `MainCtlF`,
`rtM_w2F`, `ExitW.imp`, `hWx_ofPlaceOK`, `h0_ofPlaceOK_setupF`),
`Spike.Lib.LowerA64.RtMainXR` (option (b): `h0_ofPlaceOK_setupF` with the controls after the setup block and
at the post by their shape facts, placed per state at the marshalling block and the tail: `MainCtlC`, `rtM_w2R`,
`mainSW_ofPlaceOKR`, `hWx_ofPlaceOKR`, `h0_ofPlaceOK_setupFR`),
`Spike.Lib.LowerA64.RtMainXRB` / `Spike.Lib.LowerX64.RtMainXRB` (`h0_ofPlaceOK_setupFR` with the setup block's
`hS` at `SetupCallWSB` and the callee's frame condition `SetupGF`, through `startS_segWSFB`:
`h0_ofPlaceOK_setupFRB`),
`Spike.Lib.LowerA64.RtMainXNB` / `Spike.Lib.LowerX64.RtMainXNB` (`h0_ofPlaceOK_setupFN` with the setup block's
`hS` at `SetupCallWSB` and the callee's frame condition `SetupGF`, through `startS_segWSFB`:
`h0_ofPlaceOK_setupFNB`),
`Spike.Lib.LowerA64.RtMainXN` (the `exit_group` tail inside `W2` at held frames: `SFacts` at the start control,
the post's controls by `MainCtlN`: `BlkW.ofStar`, `NodeW.ofStar`, `exitW_sfactsAt`, `rtM_w2N`,
`hWx_ofPlaceOKN`, `h0_ofPlaceOK_setupFN`),
`Spike.Lib.LowerA64.CalleeRgn2` / `Spike.Lib.LowerX64.CalleeRgn2` (`CalleePre2`'s region bounds and the setup
call's return address at `scc_rt_main`'s calls: `calleeRgn`, `raOk_setup`),
`Spike.Lib.LowerA64.RaMain2` / `Spike.Lib.LowerX64.RaMain2` (`main`'s return address `.sp1` in the phase
anchor's phase, from the order `rtPass` checks the runtime's groups in: `rtPass_ord`, `codeOf_eq` /
`codeLabel_eq`, `phOf_eq`, `ph_sp1_of_rtCodeOkS`, `raOk_main`),
`Spike.Lib.LowerA64.ProW2` (`CalleePre2.hpro` at `W2`: the prologue keeps `x0`…`x7`, `SFacts` at the source
start's control, nothing written, the abort phase's facts from the check label off the write abort's, the
placement from the entry's argument registers: `ArgEq`, `ProW.w2`, `proW_placedS`, `proW_noWr`, `proW_w2`,
`proW_abSt`, `proW_abStC`, `proW_w2C`, `hpro_setup`, `hpro_main`; `hnr_setupArgs`: the setup arguments'
controls off a return; `hE_setupTerm`, `hnr_setupTerm`: at the start before a setup block),
`Spike.Lib.LowerX64.ProW2` (the x64 twin: the prologue keeps `%rdi`…`%r9`: `ArgEq`, `XProW.w2`,
`proW_placedS`, `proW_noWr`, `proW_w2`, `blkW_abSt_at`, `proW_abSt`, `proW_abStC`, `proW_w2C`, `hpro_setup`,
`hpro_main`, `hnr_setupArgs`, `hE_setupTerm`, `hnr_setupTerm`),
`Spike.Lib.LowerA64.HproOf` / `Spike.Lib.LowerX64.HproOf` (`CalleePre2.hpro` from `PlaceOK`: the record's
instance, the runtime's code, the prologue's facts `ProOK` and the abort phase `proW_abStC` from the placement
check, the overflow stub's position `hL` (unchecked) a premise, the entry's from `blocksOk`: `ProOK`,
`fnCode2_ofPlaceOKP`, `fnCode2OfP`, `hpro_setup_ofPlaceOK`, `hpro_main_ofPlaceOK`),
`Spike.Lib.LowerA64.LandHu` / `Spike.Lib.LowerX64.LandHu` (`landStk_hxa`'s units premise `hfu` at the arena
`arOf Λ`, its units saturating: `arOf_units_fit`),
`Spike.Lib.Rt.A64MarshalTake` (the marshalling block's prefix states: frame offsets, `x0`…`x(sw-1)` and the
frame's base cell as at its entry: `argX_inj`, `marshal_take`),
`Spike.Lib.SetupWords2` (the lowering's setup words at a setup block, `rodata`'s result's value words:
`valWords_setupWords2`), `Spike.Lib.LowerA64.SetupSw` / `Spike.Lib.LowerX64.SetupSw` (one `sw` at most passes
`rtCodeOkS`, by the marshalling block's label gap: `rtCodeOkS_sw_unique`; A11 at a `.setup` tail at any `sw` the
code passes: `setupIn_sw_eq`),
`Spike.Lib.LowerX64.SetupSwA12` (A11's setup words are the lowering's, from A12's code of `scc_rt_main`: its
setup return's store run against the marshalling block's, `mainCode_dirs`, `stRun_unique`, `sw_eq_of_cells`;
`sw_eq_setupWords2`, and `valWords_of_rtCodeOkS`, the setup result's value words, `hPlS_ofSPostC`'s `hw`),
`Spike.Lib.LowerX64.SetupTailOf` (`h0In_of_setupFNP`'s `hs`, `hc` from the placement check: the output's tail
`.setup`, `tail_setup_of_accepted2`; A11's code at `setupMC (setupWords2 p)`, `rtCodeOkS_setupWords2`),
`Spike.Lib.LowerX64.H0InAssembled` (`h0In_of_setupFNP` at the lowering's output with the library's inputs filled
in: tail, code, posts, the marshalling block's placement; `h0In_setup_assembled`),
`Spike.Lib.LowerA64.SetupTailOfA` (`h0InA_of_setupFNP`'s `hs`, `hc` from the placement check:
`tail_setup_of_accepted2A`, `rtCodeOkS_setupWords2A`), `Spike.Lib.LowerA64.H0InAssembledA` (`h0InA_of_setupFNP`
at the lowering's output with the library's inputs filled in: tail, code, posts, the marshalling block's
placement; `h0InA_setup_assembled`),
`Spike.Lib.LowerX64.StkOf` (A12's grow-stub check: `h0In_of_setupFNP`'s `hstk` from the
placement check, `inRunB_proL_of_fnOk1`, `posOff_proL_of_fnOk1`, `hstk_of_placeOKAt`),
`Spike.Lib.LowerA64.StkOfA` (its AArch64 twin: `h0InA_of_setupFNP`'s `hstk`, `stkHead_length`,
`inRun_proL_of_fnOk1`, `posOff_proL_of_fnOk1`, `hstkA_of_placeOKAt`),
`Spike.Lib.LowerX64.MainCallOf` (a context's premises for `main`'s call less the return address (`raOk_main`)
and the prologue (`hpro_main_ofPlaceOK`): `CalleePre2R`, `CalleePre2R.toPre`),
`Spike.Lib.LowerX64.PinnedTcb` (the first TCB is `Λ.pinned.lo + 8`: `rtA_pinned_of_placeOKAt` by `regionsTied` and
`lookup_loadSyms`; `me`'s start word `meW2_val_of_placeOKAt`, `valRep_meW2_of_placeOKAt`),
`Spike.Lib.LowerX64.CxBlk2Of` (a context's `Kind2` body and pending-store blocks inside `W2` at the guard, `CxBlk2`'s
fields: `blkW_abSt_k2`, `blkW_w2K2`, `cxBlk2_ofW2`),
`Spike.Lib.LowerX64.UserTgt` (`cxBlk2_ofW2`'s `hTg` from one check of the cells: every `jmp`/`jcc` of a user
function's run (`WcL`) to a labelled nonempty run off `abLabs`: `tgtOkB`, `tgOkB`, `posOff_of_tgtOkB`; a `Kind2`
block has no `call`: `noCallD_kindD2`, `noCall_kind2`; `hTg_of_tgOkB`),
`Spike.Test.X64Hello1TgOk` (x86-64: `hello1o`'s output passes `tgOkB`: `hello1_tgOkB`),
`Spike.Lib.LowerX64.MainHeldX` (`main`'s function segment to `ExitC2SLF` when its paths all end in a held return
tail, and `MainCallWSF … UPostRF` from it: `CalleePre2.segH`, `mainCallWSF_ofHeld`; under `placeOKAt`, the
prologue, `HeldTailCX` and the `CdCLE` code facts discharged: `mainCallWSF_ofPlaceOKH`),
`Spike.Lib.LowerX64.MainAbX` (`main`'s aborts never end under `placeOKAt`: the overflow label and an abort of
`print` inside `W2` at the write abort's phase, `ovfAb_seg`, `printAb_seg`, `MainAb`, `mainAb_seg`),
`Spike.Lib.LowerX64.PrintAbP` (an abort of `print` landing with the caller's slots, `printNAS`, never ends,
the source control's facts discharged: `printAb_segP`),
`Spike.Lib.LowerX64.Start2C0` (the start control's facts for `h0In_setup_assembled`: `hp0_start2`,
`hf0_start2`, `hov_start2`, `hC0_start2`, `hpl0_start2`, `hcall_start2`, `hme_start2` via `tp0_start2`),
`Spike.Lib.LowerA64.MainCallOf` (its AArch64 twin, the prologue's edge (`proEdge2_ofUNM`) also left out:
`CalleePre2R`, `CalleePre2R.toPre`),
`Spike.Lib.LowerA64.MainHeldA` (the AArch64 twin of `MainHeldX`, no rebased region: `CalleePre2.segH`,
`mainCallWSF_ofHeld`; under `placeOKAt` the prologue, its edge and `HeldTailCX` (`heldTailCX_of`) discharged:
`mainCallWSF_ofPlaceOKH`),
`Spike.Lib.LowerA64.HeldPostA` / `Spike.Lib.LowerX64.HeldPostX` (`main`'s held exits at `UPostRF ∧ Q`, `Q` from
the held pair's facts, e.g. `MainCtlV` by `heldCtlV`: `ExitC2SLFV`, `heldTailCX_ofV` / `heldTailCX_mainV`,
`mainCallWSF_ofHeldV`, `mainCallWSF_ofPlaceOKHV`; the x86-64 one imported by `Spike.X64`),
`Spike.Lib.LowerA64.HeldPostAV` / `Spike.Lib.LowerX64.HeldPostXV` (`HeldPostA` / `HeldPostX`'s producer at
`Q := MainCtlV`, `h0`'s `hU` form: `mainCtlV_held`, `mainCallWSF_ofPlaceOKHMV`; the x86-64 one imported by
`Spike.X64`),
`Spike.Lib.LowerA64.VacC2` / `Spike.Lib.LowerX64.VacC2` (construct premises that never fire at a walk predicate
meeting no such construct: `callC2_of_noCallee`, `callC2H_of_noCallee`, `laneC_of_noXchg`, `newBufC_of_noNewBuf`),
`Spike.Lib.LowerA64.AllocW2W2` (`AllocW2`'s caller blocks inside `W2` at `CdCLE` and `BlC`: the arguments' loads
`allocArgs_w2`, the `bl scc_rt_alloc` `allocBl_w2`, the call's premises `allocHq` from `CallMsOK`, the
returned base's store at the landing's placement `allocStore_w2` via `blkW_placedS_updX0`),
`Spike.Lib.LowerA64.AllocFnW2` (`scc_rt_alloc`'s nodes inside `W2`, `AllocW2`'s allocator field at `W₀ := W2`:
`allocNoSys`, `allocCtl`, `allocCtx_of` from `ctrRow_alloc`, `ctrRow_alloc_n4`, `allocCtx_n4`, `allocW2`; its
placement in the call's context `allocHP`, `slotRep_nbJ1`; at the rows' memory side `msOfAX_fields`,
`ctrRow_msOfAX`, `allocW2X`; the counter add's landing in a `StartsS` family `pendA_of_selfN`),
`Spike.Lib.A64AllocTail` (`scc_rt_alloc`'s tail from the add's successor `n4`, no back edge to the counter: the
nodes `TN`, `AllocWT`, `AllocW.tail`, the segments `seg_allocW_tailA`, `seg_allocW_tail`),
`Spike.Lib.LowerA64.AllocTailW2` (the tail inside `W2` without the counter context: `AllocWT.imp`, `allocNoCtrT`,
`allocW2T`, `allocW2TX`),
`Spike.Lib.LowerA64.AllocHeldW2` (the counter add's held pair carries its own segment, `pendA_of_selfN`'s `hQ`:
the tail to its heap abort alone `seg_allocW_tailA`, left into the caller's region, the abort path; `N_msOfAX`,
`callOK_msOfAX`, `code_msOfAX`, `HeldAb`, `leaveOk_of_allocCtx`, `allocHeld_seg`, `allocHeld_sg2`, `allocHeld_nr`),
`Spike.Lib.LowerA64.AllocFieldW2` (`AllocW2`'s allocator field at `W₀ := W2` for one call: the frame condition
in the allocator's region `fstable_allocCtx`, `stackOff_allocCtx`, the call's control `frOk2_allocCtx`,
`allocW2_w2` from `allocW2X`, `allocHP` and the held landing by `allocHeld_sg2`; the field for every call
`allocW2_field`, its stub from the code-free `StubHN`),
`Spike.Lib.LowerA64.AllocW2Full` (a buffer allocation's full `AllocW2` at `W₀ := W2`, `allocW2_w2Full`, from the
loads', `bl`'s and store's `BlkW`, `allocHq` and `allocW2_field`; the frames placed at more labels),
`Spike.Lib.LowerA64.AllocW2AtOf` (`allocW2At_of`: `AllocW2At` at `CdCLE`/`BlC2L` from `allocW2_w2Full`'s
allocation-independent premises and a per-allocation `AllocPtW` bundle; `PtC2.newBufW` reads a `let newBuf`'s facts),
`Spike.Lib.LowerA64.ArCallMs` (the runtime's `arOf` arena: `CallMsOK` at `msOfAX … (arOf Λ)` with its counter and
heap bytes, `hmem_arOf`/`hno_arOf`/`hlt_arOf`/`h64_arOf` for `allocW2At_of`),
`Spike.Test.A64Hello1AllocPt` (`hello1`'s per-allocation premises of `allocW2At_of` at `rodata`'s `newBuf`:
`hello1_rodata_nbTailA`, `hello1_rodata_packLeafA`, `hello1_rodata_count2A`, `hello1_hnrA`, `hello1_haccA`,
`hello1_rodata_hdrA`, `hello1_rodata_huA`),
`Spike.Test.A64Hello1AllocPtH` (`AllocPtW`'s walk fields `hleaf`, `hu`, `hacc`, `hnr` at `rodata`'s allocation
from its `PtC2`: `hello1_rodata_ptA`, `hello1_rodata_fieldsA`, `hello1_ptFieldsA` at `OpenAPtA`'s instance),
`Spike.Lib.LowerA64.StackBounds2A` / `Spike.Lib.LowerX64.StackBounds2` (`h0In(A)_setup_assembled`'s switch depth
`L`, callee rooms `D1`, `D2` and stack bounds from the placement check: A11's `Z` is `scc_rt_main`'s frame by the
stack check's head (`mainZ_eq_frame(A)`), the callees' rows (`calleeRow(A)`), `stackBounds2(A)`; each room
`needDR(X)` adds the deepest runtime routine's depth `rtMax(A|X)`, as `needOk1` sends runtime calls to the headroom),
`Spike.Lib.LowerX64.HproSetupP` (the setup call's prologue with the caller's `me` placed at `imms2Me`'s `setupK`
immediate: `placedS_setupCall`, `hpro_setup_ofPlaceOKP`, `setupCallWS_ofPlaceOK`),
`Spike.Lib.LowerX64.SetupCallB2` (the twin of `LowerA64.SetupCallB2`: `setupCallWSB_framed`,
`setupCallWSB_ofFnSpec`, `setupCallWSB_ofPlaceOK`),
`Spike.Lib.LowerX64.HSAssembled` (`h0In_setup_assembled`'s `hS` at the instance from `setupCallWS_ofPlaceOK`:
`hS_assembled`),
`Spike.Lib.LowerA64.AbortSeg2` / `Spike.Lib.LowerX64.AbortSeg2` (an `Accepted2` body's abort exits as segments
with frames into any fragment: `ovfSeg2` at `abortN2`, `heapAbSeg2` at `nbX … .abort`, the code from `abortIn`,
the nodes' states inside `W` premises `StubON`, `StubHN`),
`Spike.Lib.LowerX64.Node2Edges` (x86-64 edges at `bodyN2`: `add_edge2`, `sub_edge2`, `store_edge2`, `br_edge2`,
`jmp_edge2`, a `ret` of up to six words `ret_edgeN2` via `getOps_rw`/`retBlk`),
`Spike.Lib.LowerX64.Body2SegOf` (the x86-64 `Accepted2` body's construct premises from the edges: the edges
at `ofEnv2` with the leaf facts from the node `add_edge2E`, `sub_edge2E`, `br_edge2E`; `addC2_of`, `subC2_of`,
`ifC2_of`, `retC2_of`, the moves; `body2_segS`, and to the exits by placements `body2_segSS`),
`Spike.Lib.LowerX64.NewBufC2` (x86-64 `NewBufC` from `newBuf_blkW` under `tpXa` and `SegW.keepTPN`, the store
at `%rbp` by `NJB.newBuf2`: `instsC2_newBuf`, `args3_step`, `nbJ1`, `AllocW2`, `nbArgs_seg`, `nbCall_seg`,
`nbStore_seg`, `nbRet_seg`, `newBufC_of`; the fresh-label route's tail from `Ea` at an extending label map:
`nbJS`, `newBufC_tail`),
`Spike.Lib.LowerX64.NbNone` (x86-64 `CxLB`'s allocation fields at a walk with no allocation's `let`:
`allocW2At_noNb`, `nbAb_noNb`),
`Spike.Lib.LowerX64.AllocW2W2` (x86-64 `AllocW2`'s parts at `W2`: the arguments' loads `allocArgs_w2`
(`fallBlk_getOp`, `fallBlk_args3`, `noSlotWr_args3`, `endJ_of_fallBlk`), the `callq` `allocBl_w2`
(`posOff_allocEntry`), `fallBlk_stDir`, `endJ_stDir`, `allocStore_w2`, the returned base's store from the landing
`nbJS` inside `W2`; the call's premises `CallMsOK`, `Call.OK.ofMs`, `allocHq`),
`Spike.Lib.LowerX64.AllocFnW2` (x86-64 `scc_rt_alloc`'s nodes inside `W2`: `nodeW_noSys1`, `blkW_noSysB`,
`allocNoSys`, `allocCtl`, `allocCtx_of`, `ctrRow_alloc_n4`, `allocCtx_n4`, `allocW2`; its placement in the
call's context `allocHP`, `slotRep_nbJ1`; at the rows' memory side `msOfAX_fields`, `ctrRow_msOfAX`,
`allocW2X`; the counter add's landing in a `StartsS` family `pendA_of_selfN`),
`Spike.Lib.X64AllocTail` (x86-64 `scc_rt_alloc`'s tail from the add's successor `c2`, no back edge to the
counter: the nodes `TN`, `AllocWT`, `AllocW.tail`, the segments `seg_allocW_tailA`, `seg_allocW_tail`),
`Spike.Lib.LowerX64.AllocTailW2` (the tail inside `W2` without the counter context: `AllocWT.imp`, `allocNoCtrT`,
`allocW2T`, `allocW2TX`),
`Spike.Lib.LowerX64.AllocHeldW2` (x86-64: the counter add's held pair carries its own segment, `pendA_of_selfN`'s
`hQ`: the tail to its heap abort alone `seg_allocW_tailA`, left into the caller's region, the abort path;
`N_msOfAX`, `callOK_msOfAX`, `HeldAb`, `leaveOk_of_allocCtx`, `allocHeld_seg`, `allocHeld_sg2`, `allocHeld_nr`),
`Spike.Lib.LowerX64.AllocFieldW2` (x86-64 `AllocW2`'s allocator field at `W2`: the frame condition in the
allocator's region `fstable_allocCtx`, `stackOff_allocCtx`, the call's control `frOk2_allocCtx`, `allocW2_w2`,
`allocW2_field`),
`Spike.Lib.LowerX64.AllocW2Full` (x86-64 buffer allocation's full `AllocW2` at `W₀ := W2` at `CdCLE` and `BlC2L`,
`allocW2_w2Full`, the per-call premises at every `callq` pc and size; `framesPlacedInI_mono_lbl`),
`Spike.Lib.LowerX64.AllocW2AtOf` (x86-64 `allocW2At_of`: `AllocW2At` at `CdCLE`/`BlC2L` from `allocW2_w2Full`'s
allocation-independent premises and `AllocPtW` at each allocation; `PtC2.newBufW`),
`Spike.Lib.LowerX64.ArCallMs` (x86-64 twin of `LowerA64.ArCallMs`: `CallMsOK` at the runtime's `arOf` arena,
`hmem_arOf`/`hno_arOf`/`hlt_arOf`/`h64_arOf` for `allocW2At_of`),
`Spike.Lib.LowerX64.AllocStore` (x86-64 `AllocStoreAt`: `AllocW2At`'s returned base's store alone, the field the
landings' segment reads at every placement; `AllocW2At.store`),
`Spike.Lib.LowerA64.CallIface` (the callee's interface at a call: `CallG`, `calleeN`, `ArgV`, `CalleeF`
(x86-64's shape, `.inF`, `.callerCells`)),
`Spike.Lib.LowerA64.CallSite` (call-site helpers: `seg_blk1`, a slot store's run `arun_spStr1`, `ofs_eq`/`ofs_le`,
`frJ_upd`, `getOp_ne_nil`),
`Spike.Lib.LowerA64.BodyW` (a lowered body's blocks inside `SFacts`: `fn0_seg`'s `hWb`/`hWs`, `bodyPhOk`),
`Spike.Test.LowerA64BodyW`, `Spike.Lib.Quiet0` (an `Accepted0` start's controls are `Quiet`: `hQ`),
`Spike.Lib.Quiet1` (so are a one-block `Accepted1` start's: `quiet_of_accepted1main`),
`Spike.Lib.LowerA64.UserW` (the user `main`'s prologue inside `SFacts`: `fn0_seg`'s `hWp`, `ProPh`),
`Spike.Lib.LowerA64.UserCall` (the user `main` as `scc_rt_main`'s user function: `UserCallW`, `UPost`),
`Spike.Lib.LowerA64.AbortCall` (a lowered function's overflow abort inside `SFacts`: `hab_of`, `userCallW_main`),
`Spike.Test.LowerA64AbortCall`,
`Spike.Lib.LowerA64.StartU` (`main`'s exit `uPost_exit`, `MainUW.dt`, `swUW_gen_dt`, `userCallW_sw`),
`Spike.Test.LowerA64StartU`,
`Spike.Lib.LowerA64.AbortOfPlaceOK` (the overflow exit call's site premises from `placeOK`: `sites7`,
`hrel_ofPlaceOK`, `htk_ofPlaceOK`, `hk_ofPlaceOK`, `hKex_ofPlaceOK`, `hms_ofPlaceOK`, `userCallW_main_ofPlaceOK`),
`Spike.Test.LowerA64AbortOfPlaceOK`,
`Spike.Lib.LowerA64.StartSeg` (the loaded thread's run as one segment inside `SFacts … Dt`: `a64_start_segW`,
`startAllUW_gen` and `_start`'s block as temporary premises), `Spike.Test.LowerA64StartSeg`,
`Spike.Test.LowerA64UserW`, `Spike.Lib.LowerA64.OvfCode` (the local overflow block's code from A9: `ovfBlk = Local.lb`),
`Spike.Lib.LowerA64.OvfDt` (the overflow stub's write tail `OvfDt`, closed under certification:
`tailNoFul_ovf`), `Spike.Test.LowerA64OvfDt`,
`Spike.Lib.LowerA64.PhCheck` (A9's phase part, `fnPhOk`), `Spike.Lib.LowerA64.PhOfPlaceOK` (`ProPh` and `bodyPhOk`
from `PlaceOK`: `userPh_of_placeOK`), `Spike.Test.LowerA64PhCheck` (`fnPhAll` on `ret0.w`, negatives),
`Spike.Lib.LowerA64.MainCode` (the user `main`'s lowered function and code from `PlaceOK`: `mainCode_ofPlaceOK`),
`Spike.Lib.LowerA64.MainPh`, `Spike.Test.LowerA64MainPh` (the user `main`'s code and phase facts from `PlaceOK`:
`mainPh_ofPlaceOK`, `lab_ofPlaceOK`; on `ret0.w`, negatives),
`Spike.Lib.SrcP1` (the compiler theorems' single-thread source parameters `srcP1`),
`Spike.Lib.Accepted0Src` (an `Accepted0` program has no memory operation: `accepted0_noMem`),
`Spike.Lib.A64Accepted0Safe` (`hsafe` for every `Accepted0` program: `safe_of_accepted0`; x64:
`Spike.Lib.X64Accepted0Safe`),
`Spike.Lib.Accepted1Src`, `Spike.Lib.A64Accepted1Safe` (the same for a one-block `Accepted1` program:
`accepted1main_noMem`, `safe_of_accepted1main`),
`Spike.Lib.Accepted1NoMem`, `Spike.Test.Accepted1NoMem` (an `Accepted1` program with calls has no memory
operation: `body1_noMemE`, `decls1_noMem`, `accepted1_noMem`; x64 `hsafe` at any depth from it:
`Spike.Lib.X64Accepted1SafeS`, `safeS_of_accepted1`; its AArch64 twin `Spike.Lib.A64Accepted1SafeS`),
`Spike.Lib.DepthFactsS`, `Spike.Test.DepthFactsS` (the source halves of `SFactsS` through a call bracket,
both ISAs: `SrcCallTo` (`CallTo` by `id`), `good1_callTo`, `good1_retTo`, `envSmallS_callTo`, `envSmallS_retTo`,
`envNum_entry`, `cell_of_good1`, `noAlloc_of_good1`, `noRet_cons`),
`Spike.Lib.LowerA64.Correct` (the AArch64 compiler theorem with its open work as hypotheses:
`a64_lower_correct`; at a certificate's facts: `a64_scc_correct`; the loaded thread at `_start`'s node:
`entry_at`; at every admissible entry state: `a64_lower_correctE`, `a64_scc_correctE`, `a64_scc_correctE_text`
(`Scc.Sem.A64.CorrectE`), `entry_atE`; closed, `hgen` discharged by `startAllUW_gen` (`hgen_ofPlaceOK`):
`a64_scc_correctE_closed`, `a64_scc_correctE_text_closed`; at any layout `Λ` passing `placeOKAt`, with no static
label: `a64_scc_correctE_closedAt`, `a64_scc_correctE_text_closedAt`), `Spike.Test.LowerA64Correct`,
`Spike.Test.A64SccCorrect` (it at `ret0`'s certificate, also at the witness entry state `witness_ok_ofPlaceOK`;
the closed theorem there too), `Spike.Test.A64Hello1SccCorrect` (the closed theorem does not reach `hello1`'s
certificate: three declarations, not `Accepted0`, `placeOK` false; x64: `Spike.Test.X64Hello1SccCorrect`),
`Spike.Test.Ret0ReleaseA64`, `Spike.Test.Ret0ReleaseX64` (the release theorems: `ret0.w`'s text is
`CorrectE` at every admissible entry state, at any layout `Λ` passing `placeOKAt` (`ret0_correct`), given the parse
check `hpa`; on AArch64 also at the certificate's layout (`ret0_correct_tables`)),
`Spike.Test.A64StaticImmsOverride`, `Spike.Test.X64StaticImmsOverride` (the release layout's override of `static` and
`imms` changes nothing the target reads: loader, labels, marks, `InLayout`, `Entry.Ok`, `WF`, `placeOKAt`),
`Spike.Test.Ret0LinkedX64` (the x64 release theorem at the layout read off the GNU-`ld` executable linked
from the certificate's text: `placeOKAt` decided there), `Spike.Test.Ret0LinkedA64` (the AArch64 twin at
the `ld.lld` executable linked from the certificate's text, `.rodata` below the code: `placeOKAt` decided there),
`Spike.Test.Hello1LinkedA64` (`hello1.w` at its `ld.lld` executable, the layout `hello1_finalCA` is stated at:
A1–A9, A11, A12 and `codeFills` hold, so `placeOKAt` holds; A2 refuses a `.rodata` label named like a code label
below the code, `noClash`),
`Spike.Test.Call1LinkedA64` (`call1.w`, in `Accepted1`: two code blocks, a call, an `if`; at its `ld.lld`
executable `placeOKAt` holds, A12 included; one instruction of the callee perturbed fails A12 but not A9),
`Spike.Test.Call1LinkedX64` (the x86-64 twin at its GNU-`ld` executable: `placeOKAt` holds, A12 included; one
instruction of the callee perturbed fails A12 but not A9),
`Spike.Test.A64SccNegative`, `Spike.Test.X64SccNegative` (release checks at `ret0`'s certificate: the theorem's
layout loads the listing and its run exits 42; the listing with `40` made `41` parses to the corrupted program, which
fails A9, so `placeOK` is false; `Spike/Gen/drift.sh` checks the generated files against scc's output),
`Spike.Test.A64CorrectE`, `Spike.Test.X64CorrectE` (`Scc.Sem.Entry.Ok`, the release statement's entry condition
(`Scc/Sem/CorrectE.lean`), decided at `ret0`'s layout: the witness stack and `Entry.linux` pass, misaligned,
small, high and overlapping stacks fail),
`Spike.Lib.A64Place`,
`Spike.Lib.A64AllocNodes`, `Spike.Lib.A64CtrRow` (the counter add node's consumer `CtrRow`),
`Spike.Lib.A64Alloc` (the allocator `scc_rt_alloc` as one segment), `Spike.Lib.A64Ret` (a function's
return block), `Spike.Lib.A64Prologue` (the stack-checked prologue, the `exit_group` tail),
`Spike.Lib.A64Marshal` (a `print` call's marshalling), `Spike.Lib.A64CodeSegs` (the prologue, the tail
and the runtime's entry from checks on a program), `Spike.Lib.A64Ret0Segs` (them for `ret0.w`),
`Spike.Lib.A64Ret0AllocTcb` (`ret0.w`'s TCB allocator block by block),
`Spike.Lib.A64Ret0StackTake` (its stack allocator),
`Spike.Lib.A64Ret0ThreadInit` (its thread setup),
`Spike.Lib.A64Ret0Mem` (`ret0.w`'s layout-decided memory-side premises of `start_seg`),
`Spike.Lib.A64Hello1Segs` (`hello1.w`'s runtime and compiled functions' segments inside `W`),
`Spike.Lib.A64Hello1Body` (`hello1.w`'s `wc_main` body with its `print` call inside `W`),
`Spike.Lib.A64Hello1Rodata` (`hello1.w`'s `wc_rodata` around its allocator call inside `W`),
`Spike.Lib.A64Hello1Main` (`hello1.w`'s `scc_rt_main` across its calls inside `W`),
`Spike.Lib.A64Hello1Mem` (`hello1.w`'s loaded thread, runtime words and their layout-decided facts),
`Spike.Lib.A64Hello1I` (`hello1.w`'s labels, phases, owned words and marks; its states inside `SFacts`),
`Spike.Test.A64Hello1Phase` (its take's phase and owned words against the run, step by step),
`Spike.Test.A64Ret0Offs` (`ret0.w`'s and `hello1.w`'s block offsets, generated by `Scc.Cert.Blocks.offsA64`),
`Spike.Test.A64Ret0PlaceOK`, `Spike.Test.A64Hello1PlaceOK` (`ret0.w`'s, `hello1.w`'s code checks from one
`Scc.Cert.PlaceOK.A64.placeOK` each),
`Spike.Lib.Rt.A64LayoutOfPlaceOK` (the runtime's layout of an output passing `placeOKAt` at a layout `Λ`,
from `Scc.Cert.PlaceOK.A64.atTables` at the tables' layout; `ret0.w`'s against
the hand one),
`Spike.Lib.Rt.A64ArenaOfPlaceOK` (the allocator's arena `arOf Λ` of an output passing `placeOKAt`: `Arena.OK`,
in the heap region, aligned, starting zero `arOf_ok`, `arOf_sub`, `arOf_al`, `arOf_init`, `arOf_z0`, `arOf_c0`,
the counter in `.data` given its zeroed item `CtrZ`), `Spike.Lib.Rt.CtrZSecs`, `Spike.Lib.Rt.A64CtrZOfEmitted`,
`Spike.Test.A64CtrZOfEmitted` (`CtrZ` of every successful lowering's output and of every output passing
`placeOKAt`: `ctrZ_ofEmitted`, `ctrZ_ofPlaceOK`), `Spike.Test.A64ArenaOfPlaceOK` (`hello1.w`'s `CtrZ`, its
`arOf` the hand arena's),
`Spike.Lib.A64W0G` (the states before and after the allocation at any layout, marks, owned words, write abort's
phase and arena: `W0`, `W1`, `hW0`, `hW1`), `Spike.Lib.A64AllocG` (`scc_rt_alloc`'s obligations at any instance
from `InstOk` and A7's `allocIn`: `allocArena`, `allocCtr`), `Spike.Lib.A64AllocPh` (`scc_rt_alloc`'s phase check
`allocPhOk`, its labels `allocLabs`, `allocPhOk_congr`; free of segment proofs, read by A7),
`Spike.Lib.A64AllocGSt` (`allocPc`, `allocAbortW`, `allocSt` at any instance passing `allocPhOk`),
`Spike.Lib.A64AllocAbOk` (`scc_rt_alloc`'s target check `allocAbOk`, its labels `allocAbLabs`,
`allocAbOk_congr`; free of segment proofs, for A7),
`Spike.Lib.A64AllocGAb` (`allocAb` at any instance passing `allocPhOk` and `allocAbOk`),
`Spike.Lib.A64PrintG` (`printPc`, `printNoWr`, `printSt`: `scc_rt_print`'s block states at any instance
passing `printIn`, `printPhOk`),
`Spike.Lib.A64PrintGAb` (`printAb`: `scc_rt_print`'s block states keep the write abort's phase, its tests
in it exactly at a refusal; `blkW_abOff`, `blkW_abKeep` by position),
`Spike.Lib.A64PrintGSvc` (`printSvcSt`, `printSvcStP`, `printSvcAb`, `printSvcWe`: `scc_rt_print`'s `write` call
carries `SFactsSt` and keeps the write abort's phase, a return in it only refusing the length passed),
`Spike.Test.A64AllocGHello1` (`hello1.w`'s `W0`,
`allocArena`, `allocCtr`, `allocPc`, `allocSt`, `allocAb` from the generic ones, its `allocPhOk`, `allocAbOk`),
`Spike.Test.A64Ret0CorrectP` (`ret0.w`'s `Correct` through `correctA64P'`, without `PromShared`),
`Spike.Lib.A64PhasesOfPlaceOK` (the blocks' phase checks `blkPh` from `placeOK`'s A6),
`Spike.Test.A64Ret0PhasesPlaceOK` (`ret0.w`'s and `hello1.w`'s phases and sites from A6 against the hand ones),
`Spike.Lib.Rt.A64CodeIn` (the runtime's code groups over copies of the hand blocks, light, and `rtCodeOk`),
`Spike.Lib.Rt.A64CodeInSetup` (`scc_rt_main` after a setup block, light: `rtCodeOkS`, `mainPhTabS`),
`Spike.Lib.Rt.A64RtCodeSetup` (the runtime's code checks but `scc_rt_main`'s, on either tail: `RtCodeIn0`),
`Spike.Lib.Rt.A64MainS` (`scc_rt_main` after a setup block, parametric: `mainS_segW`),
`Spike.Lib.Rt.A64MainSS` (`scc_rt_main` after a setup block at depth, both callees interfaces at depth: `mainS_segWS`,
`mainES_segWS` from `MainE`, `startS_segWS` from `_start`),
`Spike.Lib.LowerA64.TailBare` (an `Accepted0` program's output has a bare tail, checked at `bareMC`),
`Spike.Lib.A64PrintA` (`scc_rt_print` against a source that prints byte by byte),
`Spike.Lib.A64PrintEmit` (`scc_rt_print`'s write system call from the output row, assumed: `hsvc_of_emit`),
`Spike.Lib.PrintSvc` (the source at `print`'s output `write`, on any ISA: `PrintSvc`),
`Spike.Lib.A64PrintCall` (a call of `print` from any caller node: `print_callW`, `print_call_segW`),
`Spike.Lib.A64Hello1PrintLen` (`print`'s arguments at `hello1`'s call site, the clamped byte count),
`Spike.Lib.A64Hello1BodyA` (`wc_main`'s body against a byte-by-byte source, through `seg_printA_ofW`),
`Spike.Lib.A64Hello1PrintAt` (`wc_main` against `print`'s source loop, the write from the output row, assumed),
`Spike.Lib.EmitByte` (one output byte, kernel side and source side, for any ISA),
`Spike.Lib.Rt.A64RtCode` (the runtime's code checks of `startU_segW` in one pass over the program),
`Spike.Test.A64RtCode` (them on `ret0.w`, against the hand ones; a wrong frame and `hello1.w`'s `scc_rt_main` fail),
`Spike.Lib.Rt.A64RtNodes` (the runtime rows' phase checks, `RtNodesOk`, a premise A6 discharges),
`Spike.Test.A64RtNodes` (`RtNodesOk` on `ret0.w`'s runtime rows at the hand labels and phases),
`Spike.Lib.Rt.A64RtW` (the runtime's blocks and nodes inside `W` for any program, from an instance's facts and
`RtNodesOk`),
`Spike.Test.A64RtW` (them at `ret0.w`'s instance: the hand block and node lemmas, a row of its table),
`Spike.Lib.Rt.A64RtTcb` (`scc_rt_alloc_tcb`'s states inside `W` for any program, from its code and phase facts),
`Spike.Test.A64RtTcb` (`ret0.w`'s phase facts of it; the hand `tcbW` from the generic one),
`Spike.Lib.Rt.A64RtTake` (`scc_rt_stack_take`'s states inside `W` for any program, from its code, phase facts, words
and range),
`Spike.Test.A64RtTake` (`ret0.w`'s phase facts of it; the hand `takeSiteW`/`takeW` from the generic one),
`Spike.Lib.Rt.A64RtTi` (`scc_rt_thread_init`'s states inside `W` for any program, from its code, phase facts,
the TCB's words and the take's premises),
`Spike.Test.A64RtTi` (`ret0.w`'s phase facts of it; the hand `tiW` from the generic one),
`Spike.Lib.Rt.A64RtMainU` (`scc_rt_main`'s own states and the switch's inside `W` for any program, from their
code, phase facts and the limit word),
`Spike.Test.A64RtMainU` (`ret0.w`'s phase facts of them; the hand `MainUW`/`SwUW` from the generic ones),
`Spike.Lib.Rt.A64RtMainS` (`scc_rt_main` after a setup block, its own states inside `SFacts` for any program:
`MainPhS`, `mainPhS_of_tab`, `mainPhS_of_placeOKAt`, `mainSW_ofFalse`, `mainSW_sfacts`),
`Spike.Lib.Rt.A64RtWR` (option (b): the blocks and nodes inside `SFacts` with the placement per state:
`CFactsC`, `sfacts_doneR`, `sfacts_svcR`, `blkW_sfactsR`, `blkW_postOR`, `nodeW_svc_postOR`, `mainSW_sfactsR`,
`MainSW.ofPl`),
`Spike.Lib.Rt.A64RtPhOfPlaceOK` (`RtNodesOk` from the placement check, dead targets off each row's phase),
`Spike.Test.A64RtPhOfPlaceOK` (`ret0.w`'s runtime rows' phase checks from `ret0_placeOK`),
`Spike.Lib.Rt.A64RtPhTab` (the runtime's remaining phase facts as a decided table),
`Spike.Lib.Rt.A64RtPhOfTab` (a checked table's facts in the hand proofs' forms at the loader's labels),
`Spike.Test.A64RtPhTab` (`ret0`'s program passes the table; wrong facts fail; the facts read back),
`Spike.Lib.Rt.A64RtPhRec` (the per-function phase structures at a placed output's record from the table),
`Spike.Test.A64RtPhRec` (the structures at `ret0`'s placed record),
`Spike.Lib.Rt.A64EntryOfPlaceOK` (`_start`'s block inside the run's facts at a placed output's record),
`Spike.Test.A64EntryOfPlaceOK` (it at `ret0`'s placed output),
`Spike.Lib.Rt.A64RtStartU` (`scc_rt_start`'s states inside `W` at a placed output's record),
`Spike.Test.A64RtStartU` (`scc_rt_start`'s obligations at `ret0`'s placed record; a wrong row fails);
`Spike.Bridge.X64`,
`Spike.Bridge.X64Loop`,
`Spike.Lib.X64`, `Spike.Lib.X64Loop`, `Spike.Lib.X64Block`, `Spike.Lib.X64Sub` (the saturating `-`),
`Spike.Lib.X64Hello`,
`Spike.Lib.X64Cfg`, `Spike.Lib.X64Flags`, `Spike.Lib.X64Nodes`, `Spike.Lib.X64Switch`,
`Spike.Lib.X64Dead`, `Spike.Lib.X64Call`, `Spike.Lib.X64Print`, `Spike.Lib.X64PrintL`, `Spike.Lib.X64Abort`,
`Spike.Lib.X64PrintA` (`scc_rt_print` against a source that prints byte by byte),
`Spike.Lib.X64Hello1PrintLen` (`print`'s arguments at `hello1`'s call site, the clamped byte count),
`Spike.Lib.X64Hello1BodyA` (`wc_main`'s body against a byte-by-byte source, through `seg_printA_ofW`),
`Spike.Lib.X64PrintEmit` (`scc_rt_print`'s write syscall from the output row, `hsys_of_emit`),
`Spike.Lib.X64PrintCall` (a call of `print` from any caller node on x64: `print_callW`, `print_call_segW`),
`Spike.Lib.X64Hello1PrintAt` (`wc_main` against `print`'s source byte loop, `hello1_wcA_print_segW`),
`Spike.Lib.X64CodeSegs` (the prologue, the tail and the runtime's entry from checks on a program),
`Spike.Lib.X64Ret0Segs` (them and `wc_main`'s body for `ret0.w`),
`Spike.Lib.X64Ret0AllocTcb` (`ret0.w`'s TCB allocator block by block),
`Spike.Lib.X64Ret0StackTake` (its stack allocator),
`Spike.Lib.X64Ret0ThreadInit` (its thread setup),
`Spike.Lib.SegCommon` (ISA-generic `Seg` helpers shared by the instance glue),
`Spike.Lib.X64RtNodes` (a runtime store, `arch_prctl` and own-word accesses as nodes, `%rbp` after a call),
`Spike.Lib.X64Ret0` (`ret0.w`'s instance glue: whole functions of the main path),
`Spike.Lib.X64Ret0Mem` (its layout-decided memory-side premises of `start_seg`),
`Spike.Lib.X64AllocNodes` (an exchange's accesses, the heap counter's add and an allocation's `ret` as nodes),
`Spike.Lib.X64CtrRow` (x86-64 twin of `Spike.Lib.A64CtrRow`: the counter add node's consumer `CtrRow`),
`Spike.Lib.X64Alloc` (the allocator `scc_rt_alloc` as one segment),
`Spike.Lib.X64Typed`, `Spike.Lib.X64Ext`, `Spike.Lib.X64Consumer`, `Spike.Lib.X64Correct` (`Correct`
for a one-thread program on the x86-64 `canonical 1` from node obligations),
`Spike.Lib.X64PromShared`, `Spike.Lib.X64CorrectP` (the same with `PromShared` discharged),
`Spike.Lib.X64CorrectNW` (and `WriteNoProm` from `NoWrite`), `Spike.Lib.X64TailNoFul` (the same from a closed tail),
`Spike.Lib.X64AbortW` (the overflow abort path inside `W`: the `.ovf` block, the dispatcher at code 1, the stub),
`Spike.Lib.X64AbortWS` (the `.ovf` block at frames, the source held back at depth 0: `seg_localWS_lag`;
`StubW.mapF`),
`Spike.Test.X64AbortWS`,
`Spike.Lib.X64KeepTP` (`fsBase` kept across a segment at no `arch_prctl`; every instruction keeps it),
`Spike.Lib.X64NewBuf` (a buffer allocation's argument block and call of `scc_rt_alloc`, any program and caller frame),
`Spike.Lib.X64LaneStore` (a lane store `asLanes`/`xchg b[i]` against its lowered code, one segment),
`Spike.Lib.X64AbortHeapW` (the heap abort path inside `W`: the dispatcher at code 2, the stub, from a jump),
`Spike.Lib.X64KeepTPW` (node, prologue and `scc_rt_alloc` obligations at no `syscall`; `SegW.keepTPN`),
`Spike.Lib.Rt.X64MainS` (`scc_rt_main` after a setup block, parametric: the marshalling block, two interfaces),
`Spike.Lib.Rt.X64MainSS` (`mainS_segWS`, from `MainE` `mainES_segWS`, from `_start` `startS_segWS`: at depth),
`Spike.Lib.Rt.X64ExitF` (`main`'s exit from pending frames: `MainExitF`, `MainExitFA`, `xExitTail_segWSF`),
`Spike.Lib.X64CallSF` (`call_nd_FWKSF`: a machine call whose callee returns at any frames; its ghost frame
condition named: `MainGFr`, `MainGFr.ret`, `call_nd_FWKSFG`),
`Spike.Lib.Rt.X64MainSSF` (`mainS_segWSF`, `mainES_segWSF`, `startS_segWSF`: `main` returning at pending frames),
`Spike.Lib.Rt.X64MainSSB` (the twin of `Rt.A64MainSSB`: `SetupCallWSB`, `SetupGF`, `mainSC_segWSB`,
`mainS_segWSFB`, `mainES_segWSFB`, `startS_segWSFB`; `MainCallWSFB`, `MainCallWSF.toB`, `MainCallWSFB.toF`,
`MainGF`, `mainS_segWSFBM`),
`Spike.Test.X64MainSHello1` (`hello1.w`'s cells pass `mainSIn`),
`Spike.Lib.X64SetupW` (a setup block from its call to its return, any program: `setup_callW`, `SetupCallW`),
`Spike.Lib.SetupRet` (the setup block's post `SetupPostS`: the source at `ret a`, its words at result places),
`Spike.Lib.Rt.A64SetupRet`, `Spike.Lib.Rt.X64SetupRet` (the result register readers `rdA64`, `rdX64`),
`Spike.Test.A64SetupRetHello1` (`rdPostS` is `SetupPostS`), `Spike.Test.X64SetupRetHello1`,
`Spike.Lib.X64Hello1RodataSetupG` (`wc_rodata`'s setup call on x64 through `setup_callW`, region depth 240),
`Spike.Test.X64MainSHello1G`, `Spike.Test.A64MainSHello1G` (`scc_rt_main` on `hello1.w` by `mainS_segW` with the
setup interface from the G proofs; regions 320 / 336 below `main`'s entry),
`Spike.Lib.X64StubFacts` (`SFacts` at the stub's states), `Spike.Test.X64StubFactsSat`,
`Spike.Lib.X64StubW` (the overflow abort path's `Local.StubW` inside `SFacts … Dt` from `InstOk`, `abortIn` and
`abortPhOk`), `Spike.Test.X64StubW` (`abortPhOk` and the site hypotheses at `ret0.x`; failing tables),
`Spike.Lib.X64AbortPlace`, `Spike.Test.X64AbortPlaceSat`,
`Spike.Lib.X64SegInst` (the consumer's obligations from one `SegW` segment, a block's phases by pc),
`Spike.Lib.X64Ret0I` (`ret0.w`'s labels, phases, owned words and marks; its states inside `SFacts`),
`Spike.Test.X64Ret0Phase` (the take's phase and the owned words against the run, step by step),
`Spike.Lib.X64Hello1Mem` (`hello1.w`'s loaded thread, runtime words and their layout-decided facts),
`Spike.Lib.X64Hello1I` (`hello1.w`'s labels, phases, owned words and marks; its states inside `SFacts`),
`Spike.Test.X64Hello1Phase` (its take's phase and owned words against the run, step by step),
`Spike.Test.X64Ret0Offs` (`ret0.w`'s and `hello1.w`'s block offsets, generated by `Scc.Cert.Blocks.offsX64`),
`Spike.Test.X64Ret0PlaceOK`, `Spike.Test.X64Hello1PlaceOK` (`ret0.w`'s, `hello1.w`'s code checks from one
`Scc.Cert.PlaceOK.X64.placeOK` each),
`Spike.Test.X64Ret0CorrectP` (`ret0.w`'s `Correct` through `correctX64P'`, without `PromShared`),
`Spike.Test.X64Ret0Words` (`ret0.w`'s runtime words and their facts from its placement check, against the
hand ones),
`Spike.Lib.Rt.X64Layout` (the x86-64 runtime's layout as a record: words, frame and memory side),
`Spike.Lib.Rt.X64LayoutRet0` (`ret0.w`'s record from the hand facts, and the record's facts against them),
`Spike.Lib.Rt.X64TcbOfPlaceOK` (the main thread's TCB at a `placeOK` output: `mainE_tcb_ofPlaceOK`,
`scc_rt_pinned + 8`, and its thread pointer `mainE_tp_ofPlaceOK`),
`Spike.Lib.Rt.X64LayoutOfPlaceOK` (the runtime's layout of an output passing `placeOK`; `ret0.w`'s against
the hand one),
`Spike.Lib.Rt.X64Main` (`scc_rt_main` from its code check, the user function an interface),
`Spike.Lib.Rt.X64MainRet0` (`ret0.w`'s `main_segW` from it),
`Spike.Lib.Rt.X64Segs` (the runtime's segments from their code checks, `scc_rt_main` parametric),
`Spike.Lib.Rt.X64SegsRet0` (`ret0.w`'s runtime segments and `start_segW` from them),
`Spike.Lib.Rt.X64StartArith` (`scc_rt_start`'s switch region at any depth, from the layout record),
`Spike.Lib.Rt.X64Entry` (`_start` from its code check, `entry_segW'`; at a runtime layout, `entry_segW_take`),
`Spike.Test.X64Entry` (the hand `entry_segW` from it on `ret0.w`),
`Spike.Lib.Rt.X64EntryW` (`_start`'s obligations `EntryW` from an instance's facts, `entryW_of_instOk`),
`Spike.Lib.Rt.X64EntryOfPlaceOK` (`EntryW` and `_start`'s segment at a placed output, from A6 and A11),
`Spike.Test.X64EntryOfPlaceOK` (them at `ret0.x`'s record),
`Spike.Lib.Rt.X64RtPhRec` (`SwPh`, `MainPh`, `TiPh` at a placed output, from A6 and A11),
`Spike.Test.X64RtPhRec` (them at `ret0.x`'s record),
`Spike.Lib.Rt.X64RtCode` (the runtime's code checks of `startU_segW` and `entry_segW'` in one pass over the cells),
`Spike.Test.X64RtCode` (them on `ret0.w`, against the hand ones; a wrong frame and `hello1.w`'s `scc_rt_main` fail;
`hello1.w`'s setup tail passes `rtCodeOkS`),
`Spike.Lib.Rt.X64CodeInSetup` (A11's setup tail: `scc_rt_main`'s code with a setup call, `rtCodeOkS`, `setupOk`),
`Spike.Lib.Rt.X64RtCodeSetup` (`RtCodeIn0`, the runtime's code without `scc_rt_thread_init`, from either tail),
`Spike.Lib.X64PhasesOfPlaceOK` (the blocks' phase checks `blkPh` from `placeOK`'s A6),
`Spike.Test.X64Ret0PhasesPlaceOK` (`ret0.w`'s and `hello1.w`'s phases and sites from A6 against the hand ones),
`Spike.Lib.Rt.X64RtNodes` (the runtime rows' phase checks on x86-64, `RtNodesOk`, a premise A6 discharges),
`Spike.Test.X64RtNodes` (`RtNodesOk` on `ret0.x`'s runtime rows at the hand labels and phases),
`Spike.Lib.Rt.X64RtW` (the runtime's blocks and nodes inside `W` on x86-64 for any program, from an instance's
facts and `RtNodesOk`),
`Spike.Test.X64RtW` (them at `ret0.x`'s instance: the hand block and node lemmas, a row of its table),
`Spike.Lib.X64PhRec` (the phase record on x86-64: `InstOk` from the runtime's layout and A6),
`Spike.Test.X64PhRec` (it at `ret0.x`'s layout: the hand phases, sites, owned words and marks),
`Spike.Lib.Rt.X64RtTcb` (`scc_rt_alloc_tcb`'s states inside `W` on x86-64 for any program, `tcbW_gen`),
`Spike.Test.X64RtTcb` (it at `ret0.x`'s instance: its phase facts, the hand `tcbW`),
`Spike.Lib.Rt.X64RtTake` (`scc_rt_stack_take`'s states inside `W` on x86-64 for any program, `takeW_gen`),
`Spike.Test.X64RtTake` (it at `ret0.x`'s instance: its phase facts, the hand `takeSiteW` and `takeW`),
`Spike.Lib.Rt.X64RtTi` (`scc_rt_thread_init`'s states inside `W` on x86-64 for any program, `tiW_gen`),
`Spike.Test.X64RtTi` (it at `ret0.x`'s instance: its phase facts, the hand `tiW`),
`Spike.Lib.Rt.X64RtMainU` (`scc_rt_main`'s own states and the switch's inside `W` on x86-64 for any program,
`mainUW_gen`, `swUW_gen`),
`Spike.Test.X64RtMainU` (them at `ret0.x`'s instance: their phase facts, the hand `MainUW`/`SwUW`),
`Spike.Lib.Rt.X64RtStartU` (`scc_rt_start`'s states inside `SFacts … Dt` at a placed output, `startAllUW_gen`),
`Spike.Test.X64RtStartU` (it at `ret0.x`'s placed record in `_start`'s callee region; a wrong phase row fails),
`Spike.Lib.Rt.X64SegsAt` (the runtime's `scc_rt_thread_init`/`scc_rt_start` segments with the return point at any
label, `startU_segWAt`; the `.x7` originals as corollaries),
`Spike.Test.X64SegsAt` (the hand `thread_init_segW` from it on `ret0.w`; `hello1.w`'s at `.x8`),
`Spike.Lib.Rt.X64RtPhTab`, `Spike.Lib.Rt.X64RtPhOfTab` (a checked fact in the hand proofs' form),
`Spike.Test.X64RtPhTab` (the runtime's phase facts as a decided table,
`Scc.Cert.Rt.RtPhX64`'s `rtPhOk`, on `ret0.x`),
`Spike.Lib.X64PhPinsOfPlaceOK`, `Spike.Test.X64PhPinsOfPlaceOK` (the atomic accesses' phases from `placeOK`:
`hphT_ofPlaceOK`, `hphL_ofPlaceOK`, `hphN_ofPlaceOK`, and the other ends of the owned accesses),
`Spike.Test.X64Ret0Negative` (`ret0.w` with `40` made `41`: its `exit_group(43)` obligation is false),
`Spike.Lib.LowerEnv` (the lowering's environment facts, ISA-neutral, for both ISAs' body segments),
`Spike.Lib.LowerEnvImm` (the lowering's immediates as a table keyed by the remaining term, `immsOf`, ISA-neutral),
`Spike.Lib.LowerEnvImm1Of` (an `Accepted1` program's lowering has its immediates in `imms1Of`: `immIn_imms1Of`),
`Spike.Lib.LowerEnvImmAgree` (on an `Accepted0` program every entry of `imms1Of [d]` is `immsOf d`'s:
`imms1Of_sub_immsOf`),
`Spike.Lib.ImmsMono` (`Components`, `Sim` and `Correct` are monotone in `Layout.imms`, for a target whose loader and
marks do not read it), `Spike.Lib.ImmsMonoA64` (`CorrectE` on AArch64: `a64_correctE_imms_mono`),
`Spike.Lib.ImmsMonoX64` (`CorrectE` on x86-64: `x64_correctE_imms_mono`),
`Spike.Test.ImmsAgree` (an AArch64 `CorrectE` at `imms1Of [d]` gives it at `immsOf d` for `Accepted0`; axioms),
`Spike.Lib.LowerAddChk1` (a checked `+` in a call-free `Accepted1` body's walk is an instruction of the lowered
function's blocks: `lower1_add_insts`),
`Spike.Lib.LowerEnvImmC1Of` (the walk with calls, `lowerEnvsC`, and its immediates in `imms1Of`: `immIn_imms1OfC`),
`Spike.Lib.LowerCallOrder`, `Spike.Test.LowerCallOrder` (an `Accepted1` program calls only earlier code blocks:
`body1_callee_walkC`, `decl1_of_decls1`, `find_earlier`, `callee_earlier`; one-word returns `walkC_retOne`;
specifications by the call order
`CallIn`, `specs_of_callOrder`; a walk call's callee and arguments `body1_call_walkC`),
`Spike.Lib.LowerCallMem`, `Spike.Test.LowerCallMem` (a call or an addition at a point of the walk is emitted:
`lowerC_callMem`, `lowerC_addMem`),
`Spike.Lib.LowerProgC1Core` (the whole-program lowering of an `Accepted1` program from `lowerC`, ISA-free:
`lowerIR_accepted1`, `mem_progOf_funcs1`, `find_index`), `Spike.Lib.LowerProgC1` (with AArch64's `lowerAll`:
`lowerAll_accepted1_a64`),
`Spike.Lib.SlotOrder` (a function's register slots are its parameters then its definitions: `slots_eq`),
`Spike.Lib.SlotOrderC1` (the slot order of an `Accepted1` code block's function `func1`: `slots_func1`),
`Spike.Lib.SlotOrderA64` (AArch64 `funcRegs` is first occurrences by `StackMap`, and for `func1` the parameters then
the definitions: `funcRegs_func1`, `fnCtx_slots_func1`),
`Spike.Lib.SlotOrderX64` (x86-64 `instRegs`/`termRegs` by `StackMap`, and `frameOf`'s slots for `func1`:
`frameRegs_func1`, `frameOf_slots_func1`),
`Spike.Lib.LowerShapeC1` (the shape of an `Accepted1` code block's lowering: inversion, `InstC`/`TermC`, call
count, labels and `BlocksWF`: `func1_shape`, `func1_calls`, `blocksWF_func1`),
`Spike.Lib.LowerShapeC2`, `Spike.Test.LowerShapeC2Test` (the lowering of an `Accepted2` code block in closed
form, without the depth counter: `lowerC2`, `lowerExpr_lowerC2`, `lowerDeclMarks_lowerC2`, one inversion per
constructor),
`Spike.Lib.LowerShapeC2Shape` (the shape of `lowerC2`'s blocks: `InstC2`, `TermC2`, `BlockC2`, `ResC2`,
`lowerC2_resC2`),
`Spike.Lib.LowerShapeC2Walk` (the facts an induction over `lowerC2` reads at each construct: the lowering's steps
from a counter, the walk `lowerEnvs2` at each continuation (`walk2_tail_*`), `lowerC2_fv`, `lowerC2_term_ne`,
and `Fresh` past each construct),
`Spike.Lib.LowerShapeC2Some` (the closed form exists on every compiled block of an `Accepted2` program the lowering
accepts: `lowerC2_isSome`, `accepted2_lowerC2`, `accepted2_lowerDeclMarks`),
`Spike.Lib.LowerProgC2Core`, `Spike.Lib.LowerProgC2`, `Spike.Test.LowerProgC2Test` (the whole-program lowering of an
`Accepted2` program from `lowerC2`, ISA-free, and AArch64's `lowerAll`: `checkedOf_accepted2`, `spawned_accepted2`,
`lowerIR_accepted2`, `lowerAll_accepted2_a64`, `mem_progOf_funcs2`; on `hello1L.w` and `call1.w`),
`Spike.Lib.LowerSetupRet` (an `Accepted2` program's compiled `rodata` block returns the setup result:
`rodata_retTy_of_accepted2`, `rodata_retTy_compiled2`),
`Spike.Lib.LowerShapeX64` (every parameter, instruction and terminator register has an x86-64 `frameOf` slot:
`slotOff_param`, `slotOff_inst`, `slotOff_term`),
`Spike.Lib.LowerCallC1` (the call sites of an `Accepted1` code block's lowering with the depth counter: each
block the abort block, call-free, or a call block `callPost g w n ++ rest`, with the bracket before it:
`func1_callBlk`, `func1_bracket`),
`Spike.Lib.LowerA64.BlocksC1` (the AArch64 code of an `Accepted1` block with calls: `callArgs` of up to eight
register arguments (`callArgs_eq`, `getArgs_eq`, the allocator's `callArgs_three`), one-word `setResults`,
every other `InstC`/`TermC` instructions only, a call block `call{n+5}` split at its `bl` and `.spK`:
`inst_call1_inv`, `instsItems_allIns`, `callBlk_code`, `callSite_run`), `Spike.Test.LowerA64BlocksC1`
(them at work, with stack-map labels on in `progOf`'s functions; axioms),
`Spike.Lib.LowerA64.BlocksC1Code` (the AArch64 code predicate of an `Accepted1` block with calls: `CodeC`,
one arm per instruction numbered as `instsItems`, a one-word user call split at its `bl` and `.spK` (`BlC`);
`BlocksCodeC`; its `Cd` instance `CdC` and `codeC_of_seg`, `CodeC` from a block's code after its label, its
runs passing `runPhB`; `blocksCodeC`/`entryCodeC` from `blocksOk`/`blocksPh`, `fnCodeC` per function and
`fnCodeC_ofPlaceOK`/`fnCodeC_of_fnPh1` per code block from `PlaceOK`), `Spike.Test.LowerA64BlocksC1Code` (its
arms unfolded; `codeC_of_seg` applied; the deep block excluded),
`Spike.Lib.LowerCallee1` (the callees of an `Accepted1` code block's lowering, ISA-free: `decl1_take`,
`mem_earlier_index`, every `call` of the stack abort or of a code block before the caller, `lowerC_callOk`,
`user_ne_abort`), `Spike.Lib.LowerA64.CalleeRow` (a call site's rows of the stack need table from `PlaceOK`:
`needOk1_row`, `mem_callees_func1`, `needOk1_of_fnPh1`, `calleeRow_of_fnPh1`: the callee at a smaller index
with its frame, `fd + ng ≤ nd`), `Spike.Test.LowerCallee1` (the calls of a two-block program; `Names.user`
not injective; `calleeRow_of_fnPh1` at `fnPh1_ofPlaceOK`'s witnesses),
`Spike.Lib.LowerA64.UserInj` (distinct code block symbols from `PlaceOK`: `labNumL_local`, `local_inj`,
`eq_of_labelGap0`, `stackCheck_of_fnPh1`, `user_inj_of_placeOK`; `calleeRow_name_of_fnPh1`, the callee by name),
`Spike.Lib.LowerA64.CalleeRoom`, `Spike.Test.LowerA64CalleeRoom` (the twin of `LowerX64.CalleeRoom`: `NeedRoomA`,
`frame16_of_fnPh1`, `ownRoom_of_placeOK` (`lo ≤ -(fd + s)`), `calleeRoom_of_placeOK` (an 8-aligned depth `D`
below the caller's frame, `lo ≤ -fd - D`, the callee's room at `-D`), `mainRoom_of_row` (at `-needDA n`, slack `48`)),
`Spike.Lib.LowerA64.LimRoom`, `Spike.Test.LowerA64LimRoom` (the twin of `LowerX64.LimRoom`: `LimRoomA`,
`ownLim_of_placeOK` (`v + fd ≤ sp`), `calleeLim_of_placeOK` (the callee's at `sp - fd`), `mainLim_of_rows`,
`mainRow_of_placeOKAt`),
`Spike.Lib.A64AbortWS`, `Spike.Test.A64AbortWS` (the twin of `X64AbortWS`: the `.abort_overflow` block at frames,
the source held back at depth 0, `seg_localWS_lag`; `lb_take_slot`; the abort path moved between worlds,
`blkW_mapF`, `nodeW_mapF`, `StubW.mapF`), `Spike.Lib.LowerA64.AbortCallS`, `Spike.Test.LowerA64AbortCallS` (the
twin of `LowerX64.AbortCallS`: a callee's overflow abort at depth after the lag inside `SFactsS`, `hab_ofS`;
`stub_svc_noK`),
`Spike.Lib.LowerA64.StartSegSG`, `Spike.Test.LowerA64StartSegSG` (the twin of `LowerX64.StartSegSG`: `_start`'s
segment inside `SFactsS` at the `Good1` pairs, `a64_start_segWSG`; the `*_wmono` lemmas, `segWS_wmono`),
`Spike.Lib.LowerA64.UserLag`, `Spike.Test.LowerA64UserLag` (the twin of `LowerX64.UserLag`: `scc_rt_main`'s user
function at depth inside `SFactsS`, held back at its ghost, `userCallWS_of_exitCL`; `SFactsS.dt_mono`),
`Spike.Lib.LowerA64.FnC`, `Spike.Lib.LowerA64.ProgC`, `Spike.Test.LowerA64ProgC` (the twins of `LowerX64.FnC`/`ProgC`
with the call premise abstract: the prologue with its parameter spill at a node with the thread pointer
`prologue_body_segTP`, `ParamSpill`, `paramSpill_of_spills`; `fnC_segB`; `FnCode` without a depth limit, `BodySpecC`,
`BodyAt`, `FnSpecC`, `fnSpecC_of_body`, `bodySpecC_of_bracket`, `fnSpecC_allI`; `InWalkC`, `InWalkD`, `fresh_env1`),
`Spike.Lib.LowerA64.ProgCB`, `Spike.Test.LowerA64ProgCB` (every function's segment from the calls' and the callees'
premises, the call premise abstract: `CalleeSegs`, `CallPre`, `CalleePre`, `CalleePre.seg`, `at_sp0`, `calleeN_tp`,
`fnSpecC_all_ofPre`),
`Spike.Lib.LowerA64.CtxC`, `Spike.Test.LowerA64CtxC` (the contexts of the functions, the twin of `LowerX64.CtxC`
without the depth and self words: `CtxB`, `CtxB.call` at any callee room `D`, `framesPlaced_calleeF`,
`envSmall_calleeF`, `CtxB.callF`, `rsOf_param`, `ArgV.envNum`, `nj_callee`, `CxOkC`, `AbC`, `CxOkC.hab`;
`Spike.Lib.A64FramesPlacedI`, the twin of `X64FramesPlacedI`: the frames
placed in slots or immediates, `FramesPlacedInI`, `SlotPlacedI`, `slotPlacedI_of_srep`),
`Spike.Lib.LowerA64.MainC`, `Spike.Test.LowerA64MainC` (the twin of `LowerX64.MainC`'s `abC_lag`: the aborts `AbC`
held back at the consumer's start never end, from `OvfFactsS`, the code facts' fields the aborts read;
`hasAddChk_func1`; `CodeFactsS`, each function's code facts at its context, `CodeFactsS.ovfFacts`,
`LowerNoneS` (the code facts with no frames limit), `lowerNoneS_ofPlaceOK`; `main`'s context at `scc_rt_main`'s
call `mainCtxB`, `argTy_main`,
`mainPre_of` (`main`'s `CalleePre`), `uPostS_ret`, `g16_ofPlaceOK`, `spillsOk_of_paramSpill`),
`Spike.Lib.LowerA64.CallC`, `Spike.Test.LowerA64CallC` (the twin of `LowerX64.CallC`: the plain call without the
depth counter `CallC` from the callees' segments and the call's blocks inside `W`, `callC_of`; its pieces `argC_seg`,
`blC_seg`, `calleeC_seg` (`call_ndSF`, nodes `csN`, `retCN`, `exN`), `resC_seg`; the call premise `callPreC_of`),
`Spike.Lib.LowerA64.PreC`, `Spike.Test.LowerA64PreC` (the twin of `LowerX64.PreC`: the premises at the contexts from
the placement check with no frames limit, a code block's `CallPre` `callPre_of` at the callee room `-R.lo - frame`,
a callee's `CalleePre` `calleePre_of`, every code block's `FnSpecC` `fnSpecC_all_ofPlaceOK`; `argTy_callee`,
`limBv_of_le`),
`Spike.Lib.LowerA64.CallBlkW`, `Spike.Test.LowerA64CallBlkW` (the twin of `LowerX64.CallBlkW`: a call's blocks
inside the body's fragment at depth, a covered `ret`-free block of the code `blkW_bodySC`, the call's `bl`
`blkW_bl`, the callee's entry `nodeW_calleeEntry`, for a program callee from its code facts
`nodeW_calleeEntry_ofCode`; the coverage `okBlk_argLoad`, `okBlk_resStore`, `okBlk_chkHead_at`),
`Spike.Lib.LowerA64.BodyWSC`, `Spike.Test.LowerA64BodyWSC` (the twin of `LowerX64.BodyWSC`: the construct blocks
inside a block of `CdC` at `Cd1`, inside `BodyWS0` at depth, `blockAt_sub`, `cd1_of_subCdC`, `hWbS_of`, `hWsS_of`),
`Spike.Lib.LowerA64.FnCodeOf`, `Spike.Test.LowerA64FnCodeOf` (the twin of `LowerX64`'s `fnCode_ofPlaceOKR`: each
function's code `FnCode` at its placement, with the prologue `ProPh` at `stack_check` and the parameters
`params1R`, `fnCode_ofPlaceOKR`, `fnCode_ofPlaceOKX`, `fnCode_ofPlaceOK`),
`Spike.Lib.LowerA64.ProWS`, `Spike.Test.LowerA64ProWS` (the twin of `LowerX64.ProWS`: a code block's prologue
inside the body's fragment at depth from its code facts, `proW_bodyS`, `spillsOk_of_spills`, `mem_mapM_some`; with
saved registers inside `SFacts`, `proW_sfactsP` in `LowerA64.UserW`),
`Spike.Lib.LowerA64.CorrectS`, `Spike.Test.LowerA64CorrectS` (the consumer at any call depth from `_start`'s
segment inside `SFactsS`: `a64_lower_correctES`, `_rtF`, `_wn`; `msOfS_nil`),
`Spike.Lib.LowerA64.StartCorrectS`, `Spike.Test.LowerA64StartCorrectS` (the consumer from the user function's
`UserCallWS` inside `SFactsS`: `a64_lower_correctES_of_user`; `ovfDt_noWrite1`, `hroomU_ofPlaceOK'` (frame
`≤ 12240`), `tail_bare_of_accepted1`),
`Spike.Lib.LowerA64.MainRoomU`, `Spike.Test.LowerA64MainRoomU` (`main`'s frame at most `12240` from the rows at
`CfgNeedOkA`'s budget `≤ 12288`: `mainFrameU_of_placeOKAt`, `mainThread0_frameA`),
`Spike.Lib.LowerA64.CorrectC`, `Spike.Test.LowerA64CorrectC` (the compiler theorem for an `Accepted1` program
without the frame bound `4095`, at `CfgNeedOkA`: `a64_scc_correctE_text_closedAtC`, `a64_scc_correctE_closedAtC`,
`a64_lower_correctEC`; `main`'s interface at depth `UserMainS`, `userMainSW_of`, `userMainSW_ofPlaceOK`;
`mainFunc_of_accepted1`,
`lowerAll?_ok_of_placeOKC`),
`Spike.Lib.LowerA64.Closed2StmtA`, `Spike.Test.A64Hello1Closed2` (the statement of the compiler theorem for an
`Accepted2` program at any layout, `Closed2StmtA`, not yet proved; at `hello1o`: `hello1_out_eqA`, `hello1o`'s
output the certificate's, `hello1_of_closed2A`),
`Spike.Lib.Src.RunOk2` (an `Accepted2` program's pairs stay free of acquire/release/spawn and of a buffer
allocation the zero check rejects, along `FrameRun`/`FrameRunM`: `ZBad`, `FrOk2`, `progNoS_zbad_of_accepted2`,
`RunOk2`, `runOk2_of`),
`Spike.Lib.Src.SrcSafe2P` (every start of an `Accepted2` program keeps `CfgB` and is free of `AcqOp`:
`cfgB_mainStart`, `mainStart_noAcq`, `progInit_cfgB`; so `srcSafeS_srcP1oX`/`srcSafeS_srcP1oA` in
`SrcSafe2X`/`SrcSafe2A`),
`Spike.Lib.LowerA64.Closed2OfA` (`Closed2StmtA` from its open premises: `Closed2RestA` → `Closed2StmtA`
(`a64_scc_correctE_text_closedAt2_of`, via `correct2_of`); the start `start2`/`th02` at `me` = `meW2`, the first
TCB; the open premises `Obl2A`, `Rest2A`; the source's safety by `srcSafeS_srcP1oA`; the rest discharged at any
layout passing `placeOKAt`),
`Spike.Lib.LowerA64.Closed2AtA`, `Spike.Test.A64Hello1ClosedAt2` (`Closed2StmtA` from the start's and the landings'
segments: `H0InA`, `H1InA`, `In2A`, `Closed2InA` → `Closed2StmtA` (`a64_scc_correctE_text_closedAt2`, per instance
`a64_scc_correctE_text_closedAt2_at`); the nodes' abort `ab2`, `hpr2`; at `hello1o`: `hello1_of_closedAt2A`),
`Spike.Test.A64Hello1ClosedAt2B` (`hello1_of_closedAt2A` with `H0InA` from `h0InA_setup_assembledB`, the holes
named: `OpenBA`, `in2A_ofB`, `hello1_htyA`, `hello1_of_closedAt2BA`),
`Spike.Test.A64Hello1HS` (`hello1`'s setup call `hS` from the open premises named: `SetupOpenA`, `hS_ofOpenA`,
`OpenSA`, `HSBA`, `hSBA_ofOpenSA`, `hello1_huA`, `hello1_hSA`),
`Spike.Test.A64Hello1SetupAb` (`SetupOpenA.hab` at `hello1o`: the setup block `rodata` and `main` are
addition-free (`addFreeT`), so no state is at their overflow labels: `abortN2_none_addFree`,
`abOf2_seg_addFree`, `hello1_rodata_addFree`, `hello1_main_addFree`, `hello1_setupHabA`; the x64 twin in
`Spike.Test.X64Hello1HS`),
`Spike.Test.A64Hello1HsOf` (`SetupOpenA.hs` from `fnSpecC2_ofCxLBMe`: `setupHs_ofCxLB`, the base context
`SetupCxLB`, `setupHs_ofCxLB0`; at `hello1o`: `hello1_allocInA`, `hello1_rodata_elem2`),
`Spike.Lib.LowerA64.FramesPlacedSetup` (the setup frame `[fr]` placed at any state, its `me` word at the
immediate `imms2Me_setupK`: `framesPlaced_setup`),
`Spike.Test.A64Hello1CxLBOf` (`SetupOpenA.hcx` at `SetupCxLB` from the setup call's premises:
`setupCxLB_ofPre`; at any `T` and `Ab'`, the new buffer's `At` given to `Ab'` (`hAb`): `setupCxLB_ofPreT`),
`Spike.Test.A64Hello1SetupOpenOf` (`SetupOpenA` at `SetupCxLB` with `hs`, `hcx`, `hTg`, `hab` closed:
`setupOpenA_ofPre`; the remaining premises `SetupPreA` (`hwn`, `hAW`, `habA`), `OpenPA`; at `hello1o`:
`openSA_of_openPA`, `hello1_hSA_ofPre`),
`Spike.Test.A64Hello1CxOkH` (`hello1`'s landing contexts free of the frame invariant: the setup frame's `CxOkH`,
bottom keys `BotH`, landings `ElH := ElA … CxOkH BotH`),
`Spike.Test.A64Hello1SetupOpenOfF` (the same at `A64Hello1ClosedBVBF`'s frame condition `WordsNone ∧ swFSL`,
`hwn` from the setup call's premises: `SetupOpenFA`, `hS_ofOpenFA`, `OpenSFA`, `hSBVFA_ofOpenSFA`, `SetupPreFA`
(`hAW`, `habA`), `setupOpenFA_ofPre`, `OpenPFA`; at `hello1o`: `openSFA_of_openPFA`, `hello1_hSFA_ofPre`),
`Spike.Test.A64Hello1CxLBH` (`SetupCxLB` at a `CxOkH` context and any family: `cxLB_ofCxOkH`),
`Spike.Test.A64Hello1SetupOpenOfH` (`A64Hello1SetupOpenOfF` at the landings' contexts `CxOkH`: `AllocWH`,
`SetupPreHA`, `setupOpenFA_ofPreH`, `OpenPHA`; at `hello1o`: `openSFA_of_openPHA`, `hello1_hSFA_ofPreH`),
`Spike.Test.A64Hello1BotRes` (the setup frame's bottom keys' exits `ExitStk` at any segment world and labels,
the region facts from `Bounds2A`, the frame pop `hPS_framed`: `exitStk_ofSetupBotBA`, `exitStk_ofBotHA`,
`BotHRA`, `exitStk_ofBotHRA`, `h0_ofMainS0LA`, `exitStk_ofBotHRL`),
`Spike.Test.A64Hello1ResL` (`ResumeCx2T`'s placement-independent fields at `CxOkH`: the block `CxBlk2` and the
abort's `none`: `cxBlk2_ofCxOkHA`, `habN_ofCxOkHA`; plan b1's walk after the allocation: `TrNb`, `TrNb.tail`,
`tailOf_trans`, `TrNb.intro`, `TrNb.tailAt2`, `nbOnceL`, `hello1_rodata_trNoNb(T)`, `hello1_rodata_trNoCall`),
`Spike.Lib.LowerA64.ResumeCxLBP` (a call-free compiled block's `ResumeCx2` at `fnCode2OfPMe`: `resumeCx2_ofCxLBMe`),
`Spike.Test.A64Hello1HBot` (`hello1`'s `H1LandAW.hbot` at the bottom keys `BotHRA`, the aborts and `main`'s
call and the `rodata` return type closed, the keys' exits open: `hello1_hbotA`),
`Spike.Lib.LowerA64.PlacedRetJS` / `Spike.Lib.LowerX64.PlacedRetJS` (a `ret` placed by its exit's placements
`RetJS`: `RetJS.placed`),
`Spike.Test.A64Hello1HWBot` (`hello1_hbotA`'s keys' exits: the pop to `mainS0`, `W2` there, back by `w2_ofPopped`:
`w2_ofSetupBotA`, `hello1_hWBotA`; `hello1_hbotA'` closed),
`Spike.Lib.LowerA64.FnSpecLaneBuf2` (a block's `FnSpecC2` with no call at its walk's points from its contexts'
lane stores and buffers: `tailsL`, `tailOf_mem_tailsL`, `isCallLet`, `noCall_of_tailsL`, `printCallC_of_noCall`,
`fnSpecC2_ofLaneBuf`), `Spike.Test.A64Hello1NoCall` (`hello1o`'s `rodata` has no call: `hello1_rodata_noCall`,
`hello1_rodata_noCallT`),
`Spike.Lib.LowerA64.CxLB` (a context's facts for lane stores and buffers inside `W2`, a call-free block's
`FnSpecC2` from them: `CxLB`, `CxLB.hloF`, `CxLB.hloA`, `fnSpecC2_ofCxLB`),
`Spike.Lib.LowerA64.ResumeCxLB` (a context's `ResumeCx2` inside `W2` from `CxLB`, the adapter for
`H1OpenA.hres`: `resumeCx2_ofCxLB`, `resumeCx2_ofCxLB_noCall`),
`Spike.Lib.LowerX64.ResumeCxLB` (x86-64, imported by `Spike.X64`: the twin, `CxLB` at `rbR R`, the entry
region's facts given: `resumeCx2_ofCxLB`, `resumeCx2_ofCxLB_noCall`),
`Spike.Lib.LowerX64.FnSpecLaneBuf2` / `Spike.Lib.LowerX64.CxLB` (x86-64, imported by `Spike.X64`: the same
twins, the blocks run at `rbR R`: `tailsL`, `noCall_of_tailsL`, `printCallC_of_noCall`, `fnSpecC2_ofLaneBuf`, `CxLB`,
`CxLB.hloF`, `CxLB.hloA`, `fnSpecC2_ofCxLB`),
`Spike.Lib.LowerX64.CxLBP` (x86-64, imported by `Spike.X64`: a call-free compiled block's `FnSpecC2` inside `W2`
at `imms2Me` from the placement check and `CxLB` at `rbR R`: `fnSpecC2_ofCxLBMe`),
`Spike.Lib.Src.ImmsMeTail` (the theorem's immediates `imms2Me` are `imms2Of p` at a compiled block's points:
`body2_setupK`, `body2_setupTerm`, `tailAt2_ne_setup`, `immIn_congr`, `imms2Me_tailAt2`),
`Spike.Lib.LowerA64.FnCode2Me` / `Spike.Lib.LowerX64.FnCode2Me` (a compiled block's code facts at agreeing
immediates, the placement check's at `imms2Me`: `FnCode2.withI`, `proOK_withI`, `fnCode2OfPMe`,
`fnCode2OfPMe_spec`, `fnCode2OfPMe_spec2`),
`Spike.Lib.LowerA64.CxLBP` (a call-free compiled block's `FnSpecC2` inside `W2` at `imms2Me` from the placement
check and `CxLB`: `fnSpecC2_ofCxLBMe`),
`Spike.Test.Hello1MainFacts` (`hello1o`'s `main` at compiled block `1`, its points decided, ISA-independent:
`hello1_main_compiled2`, `hello1_main_find`, `hello1_main_tails`, `hello1_main_hlitP`, `hello1_main_noCallee`,
`hello1_main_noXchg`, `hello1_main_noNewBuf`),
`Spike.Test.A64Hello1ClosedBVB` (`hello1_of_closedAt2A` with `H0InA` from `h0InA_setup_assembledBVB`, `hS` from
`hello1_hSA`, the remaining holes listed: `HUBVA`, `OpenBVBA`, `in2A_ofBVB`, `hello1_of_closedBVBA`),
`Spike.Test.A64Hello1Final` (`hello1`'s top-level statement: `hello1_finalA`, `CorrectE` at the certificate's
text from the holes `Hello1HolesA` and the parse `hpa`, `#guard`ed beside it; the parse-free form `hello1_finalPA`
at `parsedTarget`; `correct2_parsed_at`, `in2A_hello1`),
`Spike.Test.A64Hello1Reduce` (`hello1`'s AArch64 holes reduced to the setup call's: `main`'s `MainOpenUA` closed
at the branch targets' check, `Hello1HolesA` from `OpenSA` (or `OpenPA`) and the landings' `H1OpenA` at `ElH`:
`hello1_mainOpenUA`, `hello1_holesA_of`, `hello1_holesA_ofP`),
`Spike.Test.A64Hello1HUL` (`main`'s call `hU` at any current placement `L0`, `ls` and labels `L0`: `MainPreUAL`,
`calleePre2R_mainAL`, `mainCallWSF_ofVacHMVAL`, `cxBlk2_mainAL`; the x64 twin in `Spike.Test.X64Hello1HUL`),
`Spike.Test.A64Hello1HU` (`HUBVA` at `hello1o` from `mainCallWSF_ofPlaceOKHMV`, the vacuous constructs, `main`'s
overflow stub, parameter count, frame and callee entry closed, left: blocks, aborts, `print`'s segments:
`posOff_proL_mainA`, `MainPreUA`, `calleePre2R_mainA`, `mainCallWSF_ofVacHMVA`, `hello1_htyA_eq`, `MainOpenUA`,
`hello1_hUBVA`),
`Spike.Test.A64Hello1PrintL` (`MainPreUAL`'s `print` segments at a current placement `L0`, `ls`, the placed labels
inside the heap `hrg` open: `hello1_printCallCAL`, `hello1_printCallCHAL`; the x64 twin in
`Spike.Test.X64Hello1PrintL`),
`Spike.Test.A64Hello1Print` (`MainPreUA`'s `print` segments at `hello1o` from `printCallC_instAI`, the world at
`imms2Me`, the code at `imms2Of`: `hello1_okPcA`, `hello1_imms_leA`, `hello1_imms_retA`, `hello1_printCallCA`,
`hello1_printCallCHA`),
`Spike.Test.A64Hello1MainL` (`main`'s callee entry at any current placement `L0`, `ls`, the placed labels inside the
heap `hrg` open: `MainBlkAL`, `hello1_mainPreUAL`, `hello1_mainBlkAL`, `hello1_mainPreUATL`; the x64 twin in
`Spike.Test.X64Hello1MainL`),
`Spike.Test.A64Hello1HUFL` (`main`'s call `hU` at any current placement at the frame `WordsNone ∧ swFSL`, a
setup bottom key's `h0` premise: `mainCallWSF_ofVacHMVAFL`, `hello1_hUAFL` at every reachable placement, closed),
`Spike.Test.A64Hello1Main` (`MainPreUA` at `hello1o` at a choice of the bounds from `print`'s segments, the
aborts' fragment closed (no addition; `printAb_segP`), `main`'s blocks from the branch targets' check
`MainTgA`: `hello1_mainPreUA`, `hello1_mainBlkA`, `hello1_mainPreUAT`),
`Spike.Test.A64Hello1TgOk` (`hello1`'s branch targets checked by kernel decision, `MainTgA` and
`SetupOpenA.hTg`'s statement discharged: `hello1_tgOkBA`, `hello1_mainTgA`, `hello1_setupTgA`, `hello1_mainBlkAC`),
`Spike.Test.A64Hello1HUF` (`main`'s call `hU` at the start's frame condition `WordsNone`, closed at `hello1o`:
`HUBVFA`, `mainCallWSF_ofVacHMVAF`, `hello1_hUBVFA`),
`Spike.Test.A64Hello1ClosedBVBF` (`hello1` from the assembled start segment at `WordsNone ∧ rtF` (`H0InAW`,
`Closed2AtWA`), the holes named: `HSBVFA`, `OpenBVBFA`, `in2AW_ofBVBF`, `hello1_of_closedBVBFA`, and with `main`'s
call closed, `hello1_of_closedBVBFAU`),
`Spike.Test.A64Hello1H1Of` (`H1OpenA`'s facts about `hello1o`'s source: `hello1_hTnA`, every allocation's element
type `elem2` at the compiled blocks in range; the landing contexts' aborts `AbH`, `hAb_AbH`; `h1OpenA_hello1`,
`H1OpenA` from `H1RestA`),
`Spike.Test.A64Hello1HabA` (`hello1`'s setup frame's buffer allocations' heap aborts never end, `SetupPreA.habA`
from `heapAb_seg`: `hello1_habA`, and from the bounds `hello1_habAB`; open: the heap stub's `write` tail),
`Spike.Test.A64Hello1HolesW` (the setup call's open premise, the setup frame's allocator instance alone,
`habA` by `hello1_habAB`: `OpenAHA`, `openPHA_of_openAHA`),
`Spike.Test.A64Hello1HAWNone` (downstream-only; `OpenAHA` from `allocW2At_of` at the landings' contexts,
every premise but the per-allocation `AllocPtW` closed: `OpenAPtA`, `cxLB_hAW_noneA`, `hello1_hAW_noneA`),
`Spike.Test.A64Hello1HAbQ` (`hello1`'s landing contexts' aborts never end, `H1RestA.hAbQ` at `CxOkH`: the heap
abort exits at the start world by `heapAb_segX` (`hello1_habAX`), `cxOkH_hAbQA`, `hello1_hAbQA`; open: the heap
stub's `write` tail),
`Spike.Test.A64Hello1HAW` (`H1OpenA.hAW` at the setup frame's contexts `CxOkH`: the region below the
allocator's frame and `AllocStoreAt` by `allocStore_w2`, `J`-free `hAW_CxOkH`, the field's shape at any start
frame condition `hAW_H1OpenA`, `hello1_hAWA`),
`Spike.Test.A64Hello1Bounds` (`hello1`'s concrete bounds fit its runtime calls: the rows `hello1_rowsA` by kernel
decision, every `Bounds2A` choice giving `allocW2_w2Full`'s region premises at `wc_rodata` and print's at `wc_main`,
`hello1_bounds2A`, `hello1_bounds2A_exists`),
`Spike.Lib.LowerA64.H0InSetupA` (`H0InA` from the setup-block start: `h0InA_of_setupFN`, `h0_ofPlaceOK_setupFN`
at `Closed2AtA`'s instance, its `W2`-side calls for every frame invariant holding at the starts),
`Spike.Lib.LowerA64.SetupOfPlaceOK`, `Spike.Test.A64Hello1SetupIn` (`scc_rt_main` after a setup block from
`PlaceOK`: A11 unpacked to `sw < 8` with `rtCodeOkS` and `mainPhTabS` at `setupMC sw`, `setupIn_of_placeOKAt`;
`hello1.w`'s facts at `setupMC 4` through it),
`Spike.Lib.LowerA64.HproSetupPA` / `Spike.Lib.LowerA64.HSAssembledA` (the twins of `LowerX64.HproSetupP` /
`LowerX64.HSAssembled`: `placedS_setupCall`, `hpro_setup_ofPlaceOKP`, `setupCallWS_ofPlaceOK`, `hS_assembledA`),
`Spike.Lib.LowerA64.SetupCallB2` (the setup call's producers at a known frame condition, `SetupCallWSB`:
`setupCallWSB_framed`, `setupCallWSB_ofFnSpec`, `setupCallWSB_ofPlaceOK`),
`Spike.Lib.LowerA64.SetupBot` / `Spike.Lib.LowerX64.SetupBot` (the setup function's bottom frame: `SetupBot`,
the bottom key at the setup frame under `CallGF`; `setupBot_seg`, `setupBot_segK`: its exits back to `mainS0`;
`setupBot_ofGF`),
`Spike.Lib.LowerA64.SetupBotM` / `Spike.Lib.LowerX64.SetupBotM` (`setupBot_seg` at a key memory side free of
the segment's: `setupBot_segM`, `setupBot_segKM`; `setupBot_exitStkM`, `H1OpenA.hbot`'s / `H1OpenXW.hbot`'s
shape at a `SetupBot` key),
`Spike.Lib.LowerA64.PinnedTcbA` (the first TCB is `Λ.pinned.lo + 8`, the twin of `LowerX64.PinnedTcb`:
`rtA_pinned_of_placeOKAtA`, `meW2_val_of_placeOKAtA`, `valRep_meW2_of_placeOKAtA`),
`Spike.Lib.LowerA64.Start2C0A` (its twin for `h0InA_setup_assembled`: `hp0_start2A`, `hf0_start2A`,
`hov_start2A`, `hC0_start2A`, `hpl0_start2A`, `hcall_start2A`, `hme_start2A` via `x0_start2A`),
`Spike.Lib.LowerA64.SetupSwA12A` (A11's setup words are the lowering's, from A12's code of `scc_rt_main`: the
gap from `.sp0` to `.sp1`, `sw_eq_setupWords2A`; the setup block's result has `sw` value words,
`valWords_of_rtCodeOkSA`),
`Spike.Test.A64Hello1NeedOk1`, `Spike.Test.X64Hello1NeedOk1` (`hello1.w`'s stack need rows on scc's output:
`needOk1` and A12's `fnOk1` decided per stack-checked function; the row-less callees `scc_rt_alloc` and
`scc_rt_print` pass as runtime routines within the headroom (`rtOk`), an unknown one or a short need fails),
`Spike.Lib.Src.LblRoomOf` (`LblRoom`, the lane store's no-wrap premise, from `below32` and the memory relation:
`lblRoom_of_range`, `lblRoom_of_memRel`),
`Spike.Lib.ArenaBound` (the heap arena, `.data` and a placed label's bytes below `2 ^ 64` from A1's `below32`, ISA-free:
`heap_hov`, `data_hov`, `lbl_hov`, `memRel_hov`), `Spike.Lib.LowerA64.ArenaOfPlaceOK` (them from `PlaceOK`:
`heap_end_lt_of_placeOKAt`, `heap_hov_of_placeOKAt`, `arena_end_lt_of_placeOKAt`, `memRel_hov_of_placeOKAt`),
`Spike.Lib.DmemPriv` (private memory never holds a byte of the heap or the static image, ISA-free: the invariant
`PrivInv` along every step and run, `PrivKeys.hpriv`, `WordsNone`), `Spike.Lib.A64DmemPriv` (`PrivInv` on the
canonical AArch64 machine: `privInv_load`, `privInv_step`, `privInv_run`), `Spike.Lib.A64DmemPrivPlace`
(`WordsNone` at the load of any placed output: `wordsNone_load_ofPlaceOKAt`, `wordsNone_run_ofPlaceOKAt`,
`wordsNone_stackMem`), `Spike.Lib.A64WordsNone` (`WordsNone` as a segment's frame: `wordsNone_and_fstable`; the
allocator's `hmem`, `hbuf` from it), `Spike.Lib.RegionCells` (a region's cells as a range: `cellsR_entry`,
`cellsR_callee`), `Spike.Lib.Rt.A64SegsF`, `Spike.Lib.Rt.A64RtStartUF` (`scc_rt_start` from the switch on with an
extra frame `Fw`: `SwUWF`, `StartAllUWF`, `startUF_segW`, `startAllUWF_gen`), `Spike.Lib.Rt.A64SwWordsNone` (the
switched stack's frame loads no heap or image word: `wordsNone_swFSL_fstable`, `wordsNone_takeMem`),
`Spike.Lib.LowerA64.StartUF` (the switch and the user `main` at the extra frame: `swUWF_gen_dt`,
`userCallW1_swF`), `Spike.Lib.LowerA64.StartSeg1WN` (the start segment along `WordsNone ∧ rtF`:
`a64_start_segW1_wn`), `Spike.Lib.LowerA64.Correct1WN`, `Spike.Test.A64Correct1WN` (the compiler theorem proved
along `WordsNone ∧ rtF`: `a64_scc_correctE_closedAt1_wn`, of `a64_scc_correctE_closedAt1`'s type by `rfl`),
`Spike.Lib.Proto.D2Imms` (a prototype of an immediate table keyed by control point: a per-point variant
choice `imms1V` and `EnvImmPt`, the existential form `EnvImmEx`, and a two-point table no term-keyed table fits),
`Spike.Lib.LowerX64.Checks`, `.Construct`, `.Node`, `.Body`, `.Prologue`, `.ProIn`, `.BodyIn`, `.Fn` (a lowered
parameterless function as one segment on x86-64, symbolic in the frame, from its code checks; `Checks` the closed
checks and `fnCodeOk`, A9), `Spike.Lib.LowerX64.Construct1`, `.Node1`, `.Body1` (`Accepted1`'s saturating `-`,
`if a = b` and `jmp` blocks and segments on x86-64; a call-free lowered body as one segment, `body1_seg`),
`Spike.Lib.LowerX64.CallCode` (the code of a call's depth bracket on x86-64: `getTp`, the depth word's load and
store, the bump, `br .ugt`, the call, `ud2`),
`Spike.Lib.LowerX64.OvfCode` (the local overflow block's code from A9),
`Spike.Lib.LowerX64.Main` (the user `main` of an `Accepted0` program as one segment,
from its `PlaceOK`), `Spike.Test.LowerX64Construct`, `Spike.Test.LowerX64Ret0Oracle` (them on `ret0.w`, against the
hand ones), `Spike.Test.LowerX64FnCode` (`fnCodeOk` on `ret0.w`), `Spike.Test.LowerX64MainSeg`
(`main_seg_of_placeOK` on `ret0.w`), `Spike.Lib.LowerX64.BodyPh`, `Spike.Test.LowerX64BodyPh` (a lowered
body's blocks in their phase, `bodyPhOk`, on `ret0.w`), `Spike.Lib.LowerX64.BodyW`, `Spike.Test.LowerX64BodyW` (a
lowered body's blocks inside `SFacts` at the entry: `fn0_seg`'s `hWb`/`hWs`, on `ret0.w`),
`Spike.Lib.LowerX64.UserW`, `Spike.Test.LowerX64UserW` (the user `main`'s prologue inside `SFacts`: `fn0_seg`'s
`hWp`, `ProPh`, on `ret0.w`), `Spike.Lib.LowerX64.UserCall` (the user `main` as `scc_rt_main`'s user function:
`UserCallW`, `UPost`; tested in `Spike.Test.LowerX64UserW`), `Spike.Test.LowerX64UserCall` (`ret0.w`'s `main` as
`swUW_gen`'s user function through `userCallW_of_fn`, the overflow abort a premise),
`Spike.Lib.LowerX64.AbortCall`, `Spike.Test.LowerX64AbortCall` (the function's `.ovf` block held back at the start
inside `SFacts`, `hab_of`, and `userCallW_main`, the user `main`'s `UserCallW` with the abort discharged, on
`ret0.w`), `Spike.Lib.LowerX64.AbortCallS`, `Spike.Test.LowerX64AbortCallS` (a callee's `.ovf` block at
frames held back at depth 0 inside `SFactsS`, `hab_ofS`; the abort path moved between worlds, `StubW.mapF`),
`Spike.Lib.LowerX64.UserLag`, `Spike.Test.LowerX64UserLag` (`scc_rt_main`'s user function at depth inside `SFactsS`,
held back at its ghost: `userCallWS_of_exitCL`; `SFactsS.dt_mono`, `SegWS.mono_W`),
`Spike.Lib.LowerX64.StartSegSG`, `Spike.Test.LowerX64StartSegSG` (`_start`'s segment inside `SFactsS` at
the `Good1` pairs: `x64_start_segWSG`; `st0W_wmono`, `x0W_wmono`, `mainUW_wmono`),
`Spike.Lib.LowerX64.CorrectS`, `Spike.Test.LowerX64CorrectS` (the consumer at any call depth from `_start`'s
segment inside `SFactsS`: `x64_lower_correctES`, at `rtF` / `WordsNone ∧ rtF`: `_rtF`, `_wn`; `msOfS_nil`),
`Spike.Lib.LowerX64.StartCorrectS`, `Spike.Test.LowerX64StartCorrectS` (the consumer from the user function's
`UserCallWS` inside `SFactsS`: `x64_lower_correctES_of_user`; `ovfDt_noWrite1`, `hroomU_ofPlaceOK'`),
`Spike.Lib.LowerX64.MainRoomU`, `Spike.Test.LowerX64MainRoomU` (`main`'s frame at most `12224` from the rows at
`CfgNeedOk`'s budget `≤ 12288`: `mainFrameU_of_placeOKAt`, `mainFrameU_of_rows`, `mainThread0_frame`),
`Spike.Lib.LowerX64.CorrectC`, `Spike.Test.LowerX64CorrectC` (the compiler theorem for an `Accepted1`
program without `MainFrame1Ok`, at `CfgNeedOk`: `x64_scc_correctE_text_closedAtC`, `x64_scc_correctE_closedAtC`,
`x64_lower_correctEC`;
`mainFunc_of_accepted1`, `lowerAll?_ok_of_placeOKC`),
`Spike.Lib.LowerX64.Closed2Stmt`, `Spike.Test.X64Hello1Closed2` (the statement of the compiler theorem for an
`Accepted2` program at any layout, `Closed2Stmt`, not yet proved; at `hello1o`: `hello1_out_eq`, `hello1o`'s
output the certificate's, `hello1_of_closed2`),
`Spike.Lib.LowerX64.Closed2Of` (`Closed2Stmt` from its open premises: `Closed2Rest` → `Closed2Stmt`
(`x64_scc_correctE_text_closedAt2_of`, via `correct2_of`); the start `start2`/`th02` at `me` = `meW2`, the first
TCB; the open premises `Obl2X`, `Rest2X`; the source's safety by `srcSafeS_srcP1oX`; the rest discharged at any
layout passing `placeOKAt`),
`Spike.Lib.LowerX64.Closed2At`, `Spike.Test.X64Hello1ClosedAt2` (`Closed2Stmt` from the start's and the landings'
segments: `H0In`, `H1In`, `In2X`, `Closed2In` → `Closed2Stmt` (`x64_scc_correctE_text_closedAt2`, per instance
`x64_scc_correctE_text_closedAt2_at`); the nodes' abort `ab2`, `hpr2`; at `hello1o`: `hello1_of_closedAt2`),
`Spike.Lib.LowerX64.Closed2AtW` (the same at the start's frame condition `WordsNone ∧ rtF`: `rest2X_ofW`,
`H0InW`, `H1InW`, `In2XW`, `Closed2InW` → `Closed2Stmt` (`x64_scc_correctE_text_closedAt2W`)),
`Spike.Lib.LowerX64.H1InLandW` (`H1InW` from the landings and at none: `H1OpenXW`, `h1InW_ofLand`,
`in2XW_ofLand`, `h1InW_none`, `in2XW_ofH0None`),
`Spike.Lib.LowerA64.Closed2AtWA` (its AArch64 twin: `entry_atECW`, `hst2_ofW`, `rest2A_ofW`, `H0InAW`, `H1InAW`,
`In2AW`, `Closed2InAW` → `Closed2StmtA` (`a64_scc_correctE_text_closedAt2W`)),
`Spike.Test.X64Hello1ClosedAt2B` (`hello1_of_closedAt2` with `H0In` from `h0In_setup_assembledB`, the holes named:
`OpenB`, `in2X_ofB`, `hello1_hty`, `hello1_of_closedAt2B`),
`Spike.Test.X64Hello1ClosedBVB` (`hello1_of_closedAt2` with `H0In` from `h0In_setup_assembledBVB`, the remaining
holes listed: `HSBV`, `HUBV`, `OpenBVB`, `in2X_ofBVB`, `hello1_of_closedBVB`),
`Spike.Test.X64Hello1ClosedBVBF` (the same at `H0InW`, `WordsNone ∧ rtF`: `HSBVF`, `HUBVF`, `OpenBVBF`,
`in2XW_ofBVBF`, `hello1_of_closedBVBF`),
`Spike.Lib.LowerX64.HeapAbX` (a buffer allocation's heap abort exit never ends under `placeOKAt`, at a call
node `NbJcOf`: `jfull_heapAbortObl_le`, `stubHN_w2_ofPlaceOKw`, `stubHN_nbAb`, `heapAb_seg`),
`Spike.Lib.LowerX64.HeapAbXS` (the same at a node of another world, its memory side and labels apart:
`stubHN_nbAbX`, `heapAb_segX`),
`Spike.Lib.LowerX64.StubCoreX` (the heap abort path inside `W2` for one call, at a `Jfull` control and a slot file
placing the call's control, `AllocPtW.hstub`'s shape: `stubHN_nbCore`),
`Spike.Lib.LowerX64.H1GX` (`H1OpenXW`'s aborts gathered over the contexts: `GX`, `gx_hAb`),
`Spike.Test.X64Hello1HAbQ` (`H1OpenXW.hAbQ` at `GX (CxOkH h hp)`, open: `hDtH`: `abortN2_none_addFreeX`,
`hello1_habAX`, `cxOkH_hAbQ`, `hello1_hAbQ`),
`Spike.Lib.LowerX64.H1RestXW` (`H1OpenXW`'s `hAW`, `hres`, `hbot` at `GX`: `H1RestXW`, `H1RestXW.toOpen`),
`Spike.Lib.LowerX64.ResumeCx2T` (x86-64, imported by `Spike.X64`; b1: the landing's context on the walk
past the landed allocation, `T ∧ Tr`, the records' contexts at a call: `ResumeCx2T`, `bodyAtPt2WT`, `resume_stkT`,
`landStk_segT`, `resumeCx2T_ofCxLB`, `resumeCx2T_ofCxLB_noCall`),
`Spike.Lib.LowerX64.H1InLandWT` (x86-64, imported by `Spike.X64`; `H1OpenXW`, `H1RestXW` with `hres` split as
`landStk_segT` takes it: `H1OpenXWT`, `h1InW_ofLandT`, `in2XW_ofLandT`, `H1RestXWT`, `H1RestXWT.toOpen`),
`Spike.Test.X64Hello1FinalT` (downstream-only; `hello1`'s x86-64 statement from `H1RestXWT` and `OpenAWF`:
`hello1_h1OpenXWT`, `hello1_finalW_ofT`),
`Spike.Test.X64Hello1FinalO` (`hello1_final`'s conclusion and `hpa` at `outLit` from `H1RestXWT` at
`TrNb (TailAt2 P1 j)` and `OpenAWF`, `out_eq`: `hello1_final'`),
`Spike.Test.A64Hello1FinalO` (`hello1_finalA`'s conclusion and `hpa` at `outLit` from `H1LandAWT` at a walk
restriction `Tr` and `OpenAHA`, `out_eq`: `hello1_finalA'`),
`Spike.Test.X64Hello1FinalO` (`hello1_final`'s conclusion and `hpa` at `outLit` from `H1RestXW` and `OpenAWF`,
`out_eq`: `hello1_final'`),
`Spike.Test.A64Hello1FinalO` (`hello1_finalA`'s conclusion and `hpa` at `outLit` from `H1LandAWT` at `TrNb`
(the walk after `rodata`'s allocation) and `OpenAHA`, `out_eq`: `hello1_finalA'`),
`Spike.Test.A64Hello1FinalT` (`hello1_finalWA_of` with `H1LandAWT` for `H1LandAW`: `hello1_finalAW_ofT`),
`Spike.Lib.LowerA64.ResumeCx2T` (plan b1: the resumption at the walk's points in `Tr`, without call blocks:
`ResumeCx2T`, `bodyAtPt2WT`; the records' `ResumeCx2` asked of contexts with a plain call: `resume_stkT`; the
landing's segment: `landStk_segT`; from `CxLB` at `T ∧ Tr`: `resumeCx2T_ofCxLB`, `resumeCx2T_ofCxLB_noCall`),
`Spike.Lib.LowerA64.H1LandAWT` (`H1LandAW` with `hres` split as `landStk_segT` takes it: `H1LandAWT` (`hAW`, `hTr`,
`hresL`, `hresS`, `hbot`), `h1InAW_ofLandT`),
`Spike.Lib.LowerA64.NbNone` (no new buffer under `Tr = TrNb`: the allocation's `AllocW2At` at `fun _ => none`:
`allocW2At_noNb`; the new buffer's `At` absurd: `nbAb_noNb`),
`Spike.Test.A64Hello1ResI` (a landing context's `CxLB` at the extended placement at a walk with no allocation:
`cxLB_updT`, `cxLBT_ofCxOkH`; at `hello1o`, `rodata`'s walk at `TrNb`: `hello1_cxLBT`),
`Spike.Test.A64Hello1H1T` (`H1LandAWT` at `hello1o`'s landings at `TrNb`: `hresL` at `CxOkH` by
`resumeCx2T_ofCxOkH`; the record from the bottom keys' exits `hW`: `hello1_landAWT`; `hello1_finalA'` through it:
`hello1_finalTA`; closed at `hello1_hWBotA`: `hello1_landAWTW`, `hello1_finalTWA`),
`Spike.Test.X64Hello1HabA` (`SetupOpen.habA` from `heapAb_seg`, open: `hDtH`, `hD`: `hello1_habA`),
`Spike.Test.X64Hello1HabAF` (`SetupPreF.habA` at `PREF` from `hello1_habA`, `hD` from the bounds: `hello1_habAF`),
`Spike.Test.X64Hello1HolesW` (the setup call's open premise, the allocator's `W2` instance at the setup frame:
`OpenAWF`, `openPF_of_openAWF`),
`Spike.Test.X64Hello1HAWNone` (downstream-only; `OpenAWF` from `allocW2At_of` at the setup frame, every
premise but the per-allocation `AllocPtW` closed: `OpenAPt`, `cxLB_hAW_none`, `hello1_hAW_none`),
`Spike.Test.X64Hello1Final` (the x86-64 twin of `Spike.Test.A64Hello1Final`: `hello1_final`, `hello1_finalP`,
`Hello1Holes`, `correct2_parsed_at`, `in2X_hello1`),
`Spike.Test.X64Hello1Reduce` (`Hello1Holes` from the setup call's `OpenP` alone: `main`'s side closed,
`hello1_mainTg` by `hTg_of_tgOkB`, `hello1_mainOpenU`, `hello1_holes_of`),
`Spike.Test.X64Hello1HUF` (`HUBVF` at `hello1o` closed: `MainCallWSF.mono_F` (a stronger frame condition, the
limit word unloaded), `hello1_hUBVF`),
`Spike.Test.X64Hello1CxOkH` (the setup frame's contexts and bottoms free of the frame invariant, for the landings
`ElX`, in the AArch64 twin's shape: `CxOkH`, `BotH`),
`Spike.Test.X64Hello1CxLBOfH` (`SetupCxLB` at any family from `CxOkH` and `SetupPreF.hAW`: `nbX_abort_fam`,
`cxLB_ofCxOkH`),
`Spike.Test.X64Hello1HUL` (downstream-only; `main`'s call `hU` at any current placement `L0`, `ls` and labels
`L0`: `MainPreUL`, `calleePre2R_mainL`, `mainCallWSF_ofVacHMVL`, `cxBlk2_mainL`),
`Spike.Test.X64Hello1BotH` (downstream-only; `H1OpenXW.hbot`'s per-key exits at a setup bottom key at its
`Bounds2`, any family, world and labels: `exitStk_ofSetupBotB`, `exitStk_ofBotH`),
`Spike.Test.X64Hello1H1Of` (`H1OpenX.hTn` at `hello1o`, every block in range: `hello1_hTn`),
`Spike.Test.X64Hello1FinalW` (`hello1`'s x86-64 landings on the `WordsNone` chain: `ElH`),
`Spike.Test.X64Hello1Bounds` (the x86-64 twin of `Spike.Test.A64Hello1Bounds`, in the frame record's region:
`hello1_rows`, `hello1_bounds2`, `hello1_bounds2_exists`),
`Spike.Test.X64Hello1HU` (`HUBV` at `hello1o` from `mainCallWSF_ofPlaceOKHMV`, the vacuous constructs and the
callee entry closed, left: blocks, aborts, `print`'s segments: `posOff_proL_main`, `MainPreU`, `calleePre2R_main`,
`mainCallWSF_ofVacHMV`, `hello1_hty_eq`, `MainOpenU`, `hello1_hUBV`),
`Spike.Test.X64Hello1Print` (`MainPreU`'s `PrintCallC`/`PrintCallCH` conjuncts at `hello1o` from
`printCallC_instAI`/`printCallCH_instAI`: `hello1_okPc`, `hello1_imms_le`, `hello1_imms_ret`,
`hello1_printCallC`, `hello1_printCallCH`; left the callee region's room, alignment and stack facts, `hG0F`,
`hDtP`, `hAb`),
`Spike.Test.X64Hello1PrintL` (`MainPreUL`'s `PrintCallC`/`PrintCallCH` conjuncts at `hello1o` at a current
placement `L0`, `ls` (`W2AtL`, `MSAtL`), left also the labels inside the heap (`hrg`): `hello1_printCallCL`,
`hello1_printCallCHL`),
`Spike.Test.X64Hello1Main` (`MainPreU` at `hello1o` at the first stack's top from the print segments and the
callee region's facts from `Bounds2` and the aborts' fragment (no overflow state, `print`'s aborts by
`printAb_segP`); left: `main`'s blocks: `MainBlk`, `hello1_mainPreU`),
`Spike.Test.X64Hello1H0L` (downstream-only; the setup bottom keys' `h0` at a current placement `L0`, `ls` from
`mainS0_segL` and `MainPreUL`, the keys pinned to the setup function: `BotHR`, `exitStk_ofBotHR`, `h0L_ofPreUL`),
`Spike.Test.X64Hello1HBot` (downstream-only; `hello1`'s `H1RestXW.hbot` at the bottom keys `BotHR`, the keys'
exits `hW` open: `hello1_hbot`),
`Spike.Test.X64Hello1HWBot` (downstream-only; `hello1_hbot`'s `hW`: the setup frame's pop to `mainS0`, `h0`'s
invariant there, back by `w2_ofPopped`: `hello1_hWBot`, `hello1_hbotW`, `hello1_restX(T)_ofHbotW`),
`Spike.Test.X64Hello1AllocMs` (downstream-only; `rodata`'s allocation at the record: the units' operand
`hello1_rodata_hu`, the header `hello1_rodata_hdr` (`mOf = 0`), `CallMsOK` by `callMsOK_arOf`: `hello1_hms`),
`Spike.Test.X64Hello1HAW` (downstream-only; `hello1`'s `H1RestXW.hAW` at the contexts `CxOkH`, the region's
bound and `AllocStoreAt` from `allocStore_w2`: `hAW_CxOkHX`, `hAW_H1RestXW`, `hello1_hAW`),
`Spike.Test.X64Hello1AllocPt` (downstream-only; `hello1`'s per-allocation `AllocPtW` premises at `rodata`'s
`eB`: `hello1_rodata_nbTail`, `hello1_rodata_packLeaf`, `hello1_rodata_count2`, `hello1_hnr`, `hello1_hacc`;
`OpenAPt` at `hello1o`, `ElH`: `hello1_allocPt`),
`Spike.Test.X64Hello1MainL` (`MainPreUL` at `hello1o` at a current placement `L0`, `ls` from the print
segments `hello1_printCallCL`/`CHL` at the labels' range `hrg`: `MainBlkL`, `hello1_mainPreUL`,
`hello1_mainBlkL`, `hello1_mainPreUTL`; left: `MainTg`, the write tails),
`Spike.Test.X64Hello1HS` (x86-64 `hello1`'s setup call `hS` (`HSBV`) from the open premises named: `CxBlk2`,
`AbOf2`, `abOf2_seg_addFree`, `SetupOpen`, `hS_ofOpen`, `OpenS`, `hSBV_ofOpenS`, `hello1_hu`,
`hello1_rodata_addFree`, `hello1_hS`; the aborts' segment closed at an addition-free setup block),
`Spike.Test.X64Hello1NoCall` (x86-64, imported by `Spike.X64`: `hello1o`'s `rodata` has no call:
`hello1_rodata_noCall`, `hello1_rodata_noCallT`),
`Spike.Test.X64Hello1ResT` (x86-64, imported by `Spike.X64`: plan b1's `Tr` after an allocation, `TrNb`, closed
under the walk; at `hello1o`'s `rodata` no allocation and no call there: `hello1_rodata_trNoNb`,
`hello1_rodata_trNoCall`),
`Spike.Test.X64Hello1HsOf` (`SetupOpen.hs` from `fnSpecC2_ofCxLBMe`, `CxLB` in the rebased region:
`setupHs_ofCxLB`, the base context `SetupCxLB`, `setupHs_ofCxLB0`; at `hello1o`: `hello1_allocIn`,
`hello1_rodata_elem2`),
`Spike.Test.X64Hello1CxLBOf` (`SetupCxLB` at the setup frame from the setup call's premises:
`setupCxLB_ofPre`, at any walk `setupCxLB_ofPreT`; left `hwn`, `hAW`, `hAb`),
`Spike.Test.X64Hello1SetupOpenOf` (`SetupOpen` at `SetupCxLB` with `hs`, `hcx`, `hTg` closed: `setupOpen_ofPre`;
the remaining premises `SetupPre` (`hwn`, `hAW`, `habA`), `OpenP`; at `hello1o`: `openS_of_openP`, `hello1_hS_ofPre`),
`Spike.Test.X64Hello1SetupOpenOfF` (downstream-only; `X64Hello1ClosedBVBF`'s `HSBVF` at the frame condition
`(WordsNone ∧ swFSL) ∧ CallerCells`, no `hwn`: `SetupOpenF` (aborts at a family `Ja`), `hS_ofOpenF`, `OpenSF`,
`hSBVF_ofOpenSF`, `SetupPreF`
(`hAW`, `habA`), `setupOpenF_ofPre`, `OpenPF`; at `hello1o`: `openSF_of_openPF`, `hello1_hSF_ofPre`),
`Spike.Test.X64Hello1SetupOpenOfH` (downstream-only; `X64Hello1SetupOpenOfF` at the landings' contexts
`CxOkH`: `AllocWH`, `SetupPreH`, `setupOpenF_ofPreH`, `OpenPH`; at `hello1o`: `openSF_of_openPH`,
`hello1_hSF_ofPreH`),
`Spike.Test.X64Hello1Res` (downstream-only; the landings' contexts' `CxLB` moved to a landing's extended
placement at any walks: `cxLB_updT`),
`Spike.Test.X64Hello1AllocStub` (downstream-only; `AllocPtW.hstub` from the call node's `NbJcOf` at `msOfAX` of any
family and abort, by `stubHN_nbCore`: `hstub_ofNbJc`),
`Spike.Test.A64Hello1AllocStub` (downstream-only; the AArch64 twin: `AllocPtW.hstub` from the call node's `NbJcOf`
at `msOfAX` of any family and abort, by `stubHN_nbCore`: `hstub_ofNbJc`),
`Spike.Test.X64Hello1AllocHS` (downstream-only; `AllocPtW.hstub` at `OpenAWF`'s instance at `rodata`'s
allocation, by `hstub_ofNbJc`: `hello1_rodata_hstub`),
`Spike.Test.A64Hello1AllocStubH` (downstream-only; `AllocPtW.hstub` at `OpenAPtA`'s instance at the write tail
`fun _ => True`, by `hstub_ofNbJc` at the call node `nbJcOf_nbJ1` in `CxOkH`'s setup callee region:
`hello1_hstubA`),
`Spike.Test.X64Hello1FinalC` (downstream-only; `hello1_final'`'s conclusion and `hpa` from the per-allocation
premises `OpenAPt` alone, `hello1_finalTW` at `hello1_hAW_none`: `hello1_finalC_of`; closed at `hello1_allocPt`:
`hello1_finalC`),
`Spike.Test.A64Hello1FinalCA` (downstream-only; the AArch64 twin: `hello1_finalA'`'s conclusion and `hpa` from
the per-allocation premises `OpenAPtA` alone, `hello1_finalTWA` at `hello1_hAW_noneA`: `hello1_finalCA_of`;
closed at `hello1_openAPtA`: `hello1_finalCA`),
`Spike.Test.A64Hello1HA` (downstream-only; `OpenAPtA` at `hello1o`, the landings and the write tail from the
per-allocation fields: `hello1_openAPtA`; `OpenAHA` there, `hello1_finalAW_ofT`'s `HA`: `hello1_openAHA`),
`Spike.Test.X64Hello1ResI` (downstream-only; a landings' context's `CxLB` at an extended placement at a walk
with no allocation, no allocation premise: `cxLBT_ofCxOkH`; at `hello1o`'s `rodata` walk at `TrNb`: `hello1_cxLBT`;
`H1RestXWT.hresL` at `CxOkH`: `resumeCx2T_ofCxOkH`; `hello1_final'`'s `HR` from the bottom exits `hW`:
`hello1_restXT`, `hello1_finalT`),
`Spike.Lib.LowerX64.H0InSetup` (`H0In` from the setup-block start: `h0In_of_setupFN`, `h0_ofPlaceOK_setupFN`
at `Closed2At`'s instance, its `W2`-side calls for every frame invariant holding at the starts),
`Spike.Lib.LowerX64.StartU`, `Spike.Test.LowerX64StartU` (the switch and `scc_rt_main` with the user
`main` inside `SFacts … Dt`: `uPost_exit`, `swUW_gen_dt`, `userCallW_sw`, the closed depth `swL`/`swL_ok`, on
`ret0`), `Spike.Lib.LowerX64.AbortOfPlaceOK`, `Spike.Test.LowerX64AbortOfPlaceOK` (`userCallW_main`'s
abort code, `write` call, phase check, abort site and the exit call's site premises from `placeOK`, `sites7`;
on `ret0`, negatives), `Spike.Lib.LowerX64.StartSeg`,
`Spike.Test.LowerX64StartSeg` (the run from `scc_rt_start` as one segment inside `SFacts … Dt` at the layout of an
output passing `placeOK`, `x64_start_segW`, stated as the callee continuation of `_start`'s call; `ec_facts`, the
region premises of `scc_rt_start`'s segments at any admissible entry state; on `ret0`),
`Spike.Lib.LowerX64.OvfDt`, `Spike.Test.LowerX64OvfDt` (the overflow stub's write tail `OvfDt`, closed under
certification: `ovfDt_of_at` discharges `hwr`, `tailNoFul_ovf`; on `ret0`),
`Spike.Lib.LowerX64.PhCheck` (A9's phase part, `fnPhOk`),
`Spike.Lib.LowerX64.PhOfPlaceOK` (`ProPh` and `bodyPhOk` from `PlaceOK`: `userPh_of_placeOK`),
`Spike.Test.LowerX64PhCheck` (`fnPhAll` on `ret0.w`, negatives), `Spike.Lib.LowerX64.MainCode` (the user
`main`'s lowered function and code from `PlaceOK`: `mainCode_ofPlaceOK`), `Spike.Lib.LowerX64.MainPh`,
`Spike.Test.LowerX64MainPh` (the user `main`'s code and phase facts from `PlaceOK`: `mainPh_ofPlaceOK`, P5),
`Spike.Lib.LowerX64.TailBare` (an `Accepted0` program's x86-64 output has a bare tail:
`tail_bare_of_accepted0`),
`Spike.Lib.LowerX64.TailBare1` (a one-block `Accepted1` program's x86-64 output has a bare tail:
`tail_bare_of_accepted1main`),
`Spike.Lib.X64StartOfPlaceOK`,
`Spike.Test.X64StartOfPlaceOK` (the start segment's runtime premises from `placeOK`, B5–B7's x86-64 twin),
`Spike.Lib.LowerX64.Correct` (the
x86-64 compiler theorem with its open work as hypotheses: `x64_lower_correct`; the loaded thread at `_start`'s
node: `entry_atX`; at a certificate's facts: `x64_scc_correct`; at every admissible entry state:
`x64_lower_correctE`, `x64_scc_correctE`, `x64_scc_correctE_text` (`Scc.Sem.X64.CorrectE`), `entry_atXE`;
`startAllUW_gen`'s `hrS`: `rS0_eq_lab`; closed, `hgen` discharged by `startAllUW_gen` and `ec_facts`
(`hgen_ofPlaceOK`): `x64_scc_correctE_closed`, `x64_scc_correctE_text_closed`),
`Spike.Test.LowerX64Correct`, `Spike.Test.X64SccCorrect` (it at `ret0`'s certificate, also at the witness entry
state; the closed theorem there too)), `Spike.Lib.LowerX64.MainCode1` (the user `main`'s lowered function and
code for an `Accepted1` program from `PlaceOK`), `Spike.Lib.LowerX64.Blocks1` (a lowered `Accepted1` block's code
and kind at the code predicate `Cd1`: `blocksCode1`, `entryCode1`), `Spike.Lib.LowerX64.BodyW1` (the body's
blocks inside `SFacts` at `Cd1`: `blkW_body1`), `Spike.Lib.LowerX64.UserCall1` (the user `main` of an `Accepted1`
program as `scc_rt_main`'s user function: `userCallW1_main`, `userCallW1_sw`), `Spike.Lib.LowerX64.StartSeg1`
(the run from `scc_rt_start` as one segment: `x64_start_segW1`), `Spike.Lib.LowerX64.Correct1`,
`Spike.Test.LowerX64Correct1` (the x86-64 compiler theorem for a main-only call-free `Accepted1` program, closed,
with `main`'s frame bound `MainFrame1Ok` as a hypothesis: `x64_scc_correctE_closedAt1`,
`x64_scc_correctE_text_closedAt1`; the `Accepted0` one as its corollary: `x64_scc_correctE_text_closedAt_of1`),
`Spike.Lib.LowerX64.EmitOut` (the x86-64 emitter only appends to its output: `Pre`, `emitInst_pre`,
`instsCode_split`, a call's code `emitInst_call_inv`), `Spike.Lib.LowerX64.CallSite1`,
`Spike.Test.LowerX64CallSite1` (each function's and each call site's placement facts of an `Accepted1` program
from `PlaceOK`: `lowerAll_accepted1_x64`, `fnPh1_ofPlaceOK`, `callSite1`, `call_blockAt`),
`Spike.Lib.LowerX64.LowerProgC2X`, `Spike.Test.LowerProgC2XTest` (`lowerAll`'s IR on an `Accepted2` program:
`lowerAll_accepted2_x64`),
`Spike.Lib.LowerX64.StartSegN`,
`Spike.Test.LowerX64StartSegN` (the start segment with the user function's depth `D` a parameter, the switch
region `swLD D`: `x64_start_segW1D`, `x64_start_segW1_ofD`; the depth from `main`'s stack need, `needD`,
`MainNeedOk`), `Spike.Lib.LowerX64.SetupOfPlaceOK`, `Spike.Test.X64Hello1SetupIn` (the setup block's facts from
`PlaceOK`, `sw < 6`; `hello1.w` at `setupMC 4`), `Spike.Lib.LowerX64.ArenaOfPlaceOK` (the heap arena below `2 ^ 64`
from `PlaceOK`), `Spike.Lib.X64DmemPriv`, `Spike.Lib.X64DmemPrivPlace`, `Spike.Lib.X64WordsNone`,
`Spike.Lib.Rt.X64SegsF`, `Spike.Lib.Rt.X64RtStartUF`, `Spike.Lib.Rt.X64SwWordsNone`, `Spike.Lib.LowerX64.StartUF`,
`Spike.Lib.LowerX64.StartSeg1WN`, `Spike.Lib.LowerX64.Correct1WN`, `Spike.Test.X64Correct1WN` (the twins of the
AArch64 `WordsNone` modules: `x64_start_segW1_wn`, `x64_scc_correctE_closedAt1_wn`),
`Spike.Lib.RtHeadroomX64`, `Spike.Lib.RtHeadroomA64`, `Spike.Test.RtHeadroomX64`,
`Spike.Test.RtHeadroomA64` (a runtime routine a stack-checked function calls or tail calls stays at least
`stackLimit - Tcb.headroom`, from `needOk1`'s `rtOk`: `rt_call_fits`, `rt_tail_fits`), `Spike.Lib.RtDepthX64`,
`Spike.Lib.RtDepthA64`, `Spike.Test.RtDepthX64`, `Spike.Test.RtDepthA64` (each `rtDepth` entry covers the regions of
the runtime routines' segment lemmas along the chain: `abort_chain`, `print_chain`, `alloc_chain`, `abort_fits`,
`print_fits`, `alloc_fits`),
`Spike.Lib.LowerX64.MainNeed`, `Spike.Test.LowerX64MainNeed` (`MainNeedOk` from the placement
check for an `Accepted1` program, given the configuration's `CfgNeedOk`: `mainNeedOk_of_placeOKAt`; the
AArch64 twin `Spike.Lib.LowerA64.MainNeed`, `Spike.Test.LowerA64MainNeed`: `main`'s callee room `D = needDA n`
for `a64_start_segWS`, `mainRoom_of_placeOKAt`; `Spike.Lib.RtMainMem`: `scc_rt_main` among the runtime's
functions, `mainThread0_mem`)
cannot
be imported together (the two ISAs' syntax modules declare the same top-level names); the library's globs build
all of them.

Allocation, lane stores and `hello1.w`'s setup block: `Spike.Lib.AllocSrc` (the source `newBuf`
step lifted to the one-thread invariant), `Spike.Lib.LaneStoreSrc` (a lane-word store into a buffer
element, source side), `Spike.Lib.AllocRow` (the allocator's arena contract `ArenaOK` and the
allocation row `row_alloc`), `Spike.Lib.Hello1RodataSrc` (`rodata`'s body as a one-frame source run),
`Spike.Lib.A64RunPc` (distinct label-relative positions in runs sit at distinct pcs at any layout: `InRun`,
`pc_run`, `pc_ne_of_inRun`), `Spike.Lib.X64RunPc` (its x64 byte-offset twin: `InRunB`, `pc_runB`, `pc_ne_of_inRunB`),
`Spike.Lib.LowerX64.AllocRa` (x64 `BlC2`, `blC2_hra`, `blC2_notAb` by return-label shape `retSfx`), `Spike.Lib.A64Hello1RodataS` (`wc_rodata`'s
segments with the source advanced by local runs), `Spike.Lib.A64Hello1RodataPostS` (the same
from the allocator's return), `Spike.Lib.A64KeepTP` (`TPIDR_EL0` kept across an `MSR`-free
segment), `Spike.Lib.A64Hello1RodataTP` (`wc_rodata`'s and the allocator's nodes at cells other than `MSR`),
`Spike.Lib.A64AbortHeapW` (the heap abort path, `scc_rt_abort(2)`),
`Spike.Lib.A64Hello1RodataSetup` (`wc_rodata` from its call to its return, thread pointer kept),
`Spike.Lib.A64Hello1RodataXa` (`wc_rodata`'s allocation continuation, from the landing to the return),
`Spike.Lib.X64Hello1RodataS`, `Spike.Lib.X64Hello1RodataPostS`, `Spike.Lib.X64Hello1RodataTP` (nodes at cells
other than `syscall`, `NoSetFs` for `NoMsr`), `Spike.Lib.X64Hello1RodataSetup`, `Spike.Lib.X64Hello1RodataXa`
(their x86-64 twins),
`Spike.Lib.Hello1RodataMem` (`rodata`'s buffer words as the latest source messages),
`Spike.Lib.AllocInv` (the counter, fresh labels and an allocation's phases, for an alloc-capable consumer),
`Spike.Lib.A64LaneStore` (a lane store `asLanes`/`xchg b[i]` against its lowered code, one segment).
`Spike.Lib.A64Hello1LaneStoreReg` (`wc_rodata`'s first lane store as an instance of that rule).
`Spike.Lib.A64NewBuf` (a buffer allocation's argument block and call of `scc_rt_alloc`, any program and caller frame).
`Spike.Lib.HeapAbort` (the heap abort's source facts and its justification, ISA-free).
`Spike.Lib.A64HeapAbort` (the allocator's way to the heap abort gives those facts).
`Spike.Lib.A64SetupW` (a setup block from its call to its return, any program: the walk over its blocks).
`Spike.Lib.A64Hello1RodataSetupG` (`wc_rodata`'s setup call re-derived through that composition).
`Spike.Lib.A64AllocS` (`newBuf_callW`, `newBuf_blkW`, `lane_storeW` at any call depth, over `SegWS`).
`Spike.Lib.A64AbortHeapS` (the heap abort path at any call depth, over `SegWS`; `SegWS.liftS_noret`),
`Spike.Lib.X64AbortHeapS` (the same on x64, over `Spike.Lib.X64AbortHeapW`, the heap abort path inside `W`),
`Spike.Lib.X64AllocS` (the same on x64: `newBuf_callWS`, `newBuf_blkWS`, `lane_storeWS`),
`Spike.Lib.ByteOut` (`print`'s byte step `MemSide.bo` on any ISA; `byteOut_emit`, both sides of a byte),
`Spike.Lib.A64PrintByteOut`, `Spike.Lib.X64PrintByteOut` (`print_call_segWB`: `print_call_segW`
under `ms.bo = ByteOut`; `hbuf_vacuous`: no `FStable` frame says eight bytes are absent),
`Spike.Lib.SegWOfNot` (`SegW.of_not`: a segment from an empty precondition, any ISA),
`Spike.Lib.A64PrintEmpty` (`print_call_emptyW`: a call of `print` with count 0, its system call unreachable),
`Spike.Lib.A64PrintTP` (`print_call_segWB_tp`, `print_call_segW_tp`, `print_call_emptyW_tp`: the thread pointer
kept across a call of `print`; `PrintAW.noMsr`; the primed `print_call_segW_tp'`, `print_call_emptyW_tp'`, over
`print_callW'`, `print_call_segW'`, `print_call_emptyW'`: `print`'s blocks asked only under frame conditions that
know the call, `PrintCall.pFJ`), `Spike.Test.A64PrintTP` (their axiom guards),
`Spike.Lib.X64PrintEmpty`, `Spike.Lib.X64PrintTP` (the x64 twins: `print_call_emptyW`; `PrintAW.noSetFs`,
`print_sys_noSetFs`, `print_call_segWB_tp`, `print_call_segW_tp`, `print_call_emptyW_tp`; the primed
`print_call_segW_tp'`, `print_call_emptyW_tp'`, over `print_callW'`, `print_call_segW'`, `print_call_emptyW'` in
`Spike.Lib.X64PrintCall`, at `PrintCall.pFJ`),
`Spike.Lib.LowerX64.PrintCallC2Code` (`printInsts` at `InstsC2` as `pblk`'s code: `print_code`),
`Spike.Lib.LowerX64.PrintCallC2` (an output call of an `Accepted2` body: `printCallC_of` from `PrintW`/`PrintWE`;
`print_blocks_toC`, `stC_slots`, `NJB.printUnit`, `printSys_src`; `printCallC_of'` from `PrintW'`/`PrintWE'`,
`print`'s states under `PrintCall.pFJ`, with `PrintSlots`, `PrintBlkW'`, `.primed`, `PBlk.pFJ_nC`;
`printCallC_ofA` with `PrintSlotsA`, `PrintLen` at every state of the argument block),
`Spike.Lib.LowerX64.PrintStepK` (the slots along `print`'s argument block: `StepK`, `preD_take`, `postD_take`),
`Spike.Lib.LowerX64.HeldC` (the source held at a callee's `ret` one frame above `fs`: `HeldC`, `HeldCtl`,
`HeldC.lagF`; `CallC2H`, `PrintCallCH`: `CallC2`, `PrintCallC` ending at `HeldC` of `ContC`),
`Spike.Lib.LowerX64.PrintCallC2H` (`printCallCH_of` from `printCallC_of`'s premises, `printCallCH_of'` from
`printCallC_of'`'s, `printCallCH_ofR` with `print`'s end states at `ret ()`, `printCallCH_ofRA` over
`printCallC_ofA`'s premises; the hold node `printNRH`),
`Spike.Lib.X64CallSAH` (`call_ndSFH`: `call_ndSF` with the callee's return not taken, landing at `fr :: fs`),
`Spike.Lib.LowerX64.CallC2H` (`callC2H_of` from `callC2_of`'s premises and `hWH`, `W` at the held pairs of the
result's store's node; `heldND`, `calleeP_seg2H`, `retP_seg2H`, `retP_segS2H`),
`Spike.Lib.PrivByteVacuous` (a byte inside eight absent ones changes no 8-byte load),
`Spike.Lib.DmemPriv` (private memory maps only the initial stack and the pool along every run, `PrivInv`;
so a placed label's byte is never private: `PrivKeys.hpriv`, the consumer's `hpriv`),
`Spike.Lib.A64DmemPriv`, `Spike.Lib.X64DmemPriv` (`PrivInv` at load and along the canonical machine's runs),
`Spike.Test.A64DmemPrivHello1`, `Spike.Test.X64DmemPrivHello1` (`privInv_load` at hello1's load, both premises
discharged; no reachable thread maps a heap or image byte: `hello1_not_mem`, nor loads a word of them:
`hello1_wordsNone`),
`Spike.Lib.Rt.A64SwWordsNone`, `Spike.Lib.Rt.X64SwWordsNone` (after the stack switch: the new region's cells in
the taken range, `cellsR_swR_sub`; `WordsNone ∧ swFSL` is `FStable`, `wordsNone_swFSL_fstable`),
`Spike.Lib.A64WordsNone`, `Spike.Lib.X64WordsNone` (`WordsNone` as a frame: `FStable` off the heap and image,
`hmem_of_wordsNone`, `hbuf_of_wordsNone`),
`Spike.Lib.A64Hello1SetupPriv`, `Spike.Lib.X64Hello1SetupPriv` (the G setup's `hmem`, `hbuf` from a frame that
loads no heap or image word, `WordsNone`, kept by frame steps off them: `hello1_rodata_setupGW_priv`),
`Spike.Test.A64MainSHello1GPriv`, `Spike.Test.X64MainSHello1GPriv` (`hello1_mainS_segGW_priv`: MainS's `hmem`,
`hbuf` from `WordsNone`),
`Spike.Test.A64FrameHello1`, `Spike.Test.X64FrameHello1` (a reachable hello1 thread's `At … F₀` is
`At … (WordsNone hello1Λ ∧ F₀)`, `FStable` for a region in the stack, `hwn` its first conjunct; at `entryR`
and in `rS0 L`: `hello1_frame_entry`, `hello1_frame_rS0`),
`Spike.Lib.RegionCells` (a region's cells as a range: `cellsR`, in the entry stack, a callee's in its caller's),
`Spike.Test.A64MainSHello1Sw`, `Spike.Test.X64MainSHello1Sw` (`hello1_mainS_segGW_sw`: MainS in the switched
stack under `WordsNone ∧ swFSL`, `hF` and `hwn` discharged from the switch's premises),
`Spike.Lib.Rt.A64SegsF`, `Spike.Lib.Rt.X64SegsF` (`SwUWF`, `StartAllUWF`: the start after the switch under an
extra memory frame `Fw ∧ swFSL`; `startSwitchUF_segW`, `startUF_segW`; at `Fw := True` the originals,
`swUWF_true_iff`, `startAllUWF_true_iff`, `startSwitchU_segW'`),
`Spike.Lib.Rt.A64RtStartUF`, `Spike.Lib.Rt.X64RtStartUF` (`startAllUWF_gen`: `startAllUW_gen` at `StartAllUWF`),
`Spike.Lib.LowerA64.StartUF`, `Spike.Lib.LowerX64.StartUF` (`swUWF_gen_dt`, `userCallW1_swF`, `userCallW_swF`:
the switch and the user `main` under `Fw ∧ swFSL`),
`Spike.Lib.LowerA64.StartSeg1WN` (`a64_start_segW1_wn`: the call-free `Accepted1` start segment with
`WordsNone` in every frame, before and after the switch),
`Spike.Lib.A64DmemPrivPlace`, `Spike.Lib.X64DmemPrivPlace` (`WordsNone` of every thread at the load of a placed
output and along every run: `wordsNone_run_ofPlaceOKAt`, `wordsNone_run_of_wide`),
`Spike.Lib.LowerA64.Correct1WN` (`a64_scc_correctE_closedAt1_wn`: the `Accepted1` compiler theorem's statement,
proved with `WordsNone ∧ rtF` in every segment's frame; `a64_lower_correctE1_wn`, `hgen1WN_ofPlaceOK`),
`Spike.Test.A64Correct1WN` (its type is `a64_scc_correctE_closedAt1`'s),
`Spike.Lib.ByteOutPriv` (`byteOut_emit` with `hpriv` from `PrivKeys` and the byte in the heap or image),
`Spike.Lib.ByteOutLd` (`byteOut_emit_ld`: `hpriv` from `PrivKeys`, `hnum` from `SrcNumSP … PrintLd`),
`Spike.Lib.A64ConsumerAE` (the consumer through `print`'s `write`: `EmitA`, `EmitJ`, `EmitSA`, `RSAE`),
`Spike.Lib.A64ConsumerAEStep` (a step from `RSAE`: `pre_emitA`, `emit_stepAE`, `wr1Zero_step`, `r_stepAE`),
`Spike.Lib.A64ConsumerAEStart` (`Correct` through `print`'s `write`: `stepSimAE`, `correctKOnAE`, `correctKAEmitE'`),
`Spike.Lib.A64ConsumerAEComp`, `Spike.Lib.X64ConsumerAEComp` (`CompAE` with the extern's model frame exempt:
`components_oneSE`, `r_componentsAE`; the x86-64 twin imported by `Spike.X64`),
`Spike.Lib.A64PlacedSE`, `Spike.Lib.X64PlacedSE` (the placement field of `NodesA`, `SFactsA` and `W2`: every
frame placed or the current frame in the output extern's model: `PlacedSE`, `PlacedSE.of_placedS`, `.of_ext`,
`.frames`, `PostSA`, `post_progressSA`, `components_oneSE`, `components_oneSX`; the x86-64 twin imported by
`Spike.X64`),
`Spike.Lib.LowerA64.PrintPlacedSE`, `Spike.Lib.LowerX64.PrintPlacedSE` (`print`'s states at `PlacedSE`, the
source at the extern's model terms and the suspended frames placed under the frame condition: `printBody_ext`,
`PlacedSE.of_printTop`, `printC_top`, `BlkW.ofJF`, `PrintAW.ofJF`, `blkW_placedSE`, `printAW_placedSE`,
`printSvc_placedSE`; `blkW_placedSE'`, `BlkW.framesOfF`: the frames placed only at the block's states; with
`W2PartE`, `BlkW.w2E`, `NodeW.w2E` in `Spike.Lib.LowerA64.W2Blk` and its twin; the x86-64 twin imported by
`Spike.X64`),
`Spike.Lib.LowerA64.PrintWEW2` (a call of `print` of an empty slice inside `W2`: `PrintCallOk`, the call
builder's obligation at a call state; `printBlkWE_w2`, `printWE_w2`, `printCallC_of`'s `hPWE`; `frOk2_printTop0`,
`printW_w2`, its `hPW` at a nonempty slice; `printBlkWE_w2'`, the frames placed only at the block's states),
`Spike.Lib.LowerX64.PrintWEW2` (its x86-64 twin: `PrintCallOk`, `printArgW_placedSE`, `printArgWE_w2`,
`printWE_w2`, `frOk2_printTop0`, `printW_w2`; `printArgW_placedSE'`, `PrintArgW.framesOfF`, `printArgWE_w2'`;
with `blkW_w2BPE` in `Spike.Lib.LowerX64.W2Body`; imported by `Spike.X64`),
`Spike.Lib.LowerA64.PrintWBW2` (`printW_w2` under `print`'s byte step and the write abort's justification:
`printW_w2B`, `hms` from the buffer's placement `hpw`, `LblRange` and the layout below `2 ^ 32`; the x86-64 twin
`Spike.Lib.LowerX64.PrintWBW2` imported by `Spike.X64`),
`Spike.Lib.LowerA64.PrintFramesJ` (the frames inside a call of `print` placed under frame conditions that
know the call: `framesPlaced_printFJ`; `printCallC_of'`'s `hPW`, `hPWE` inside `W2`: `printW_hPWJ`,
`printWE_hPWEJ`; `printW_hPWJ_AB` at the rows' memory side `msOfAB`; with `PrintCallOkR`, `printWE_w2'`,
`printW_w2'` in `Spike.Lib.LowerA64.PrintWEW2` and
`printW_w2B'`, `printW_hPW'` in `Spike.Lib.LowerA64.PrintWBW2`; the x86-64 twins in
`Spike.Lib.LowerX64.PrintFramesJ`, `Spike.Lib.LowerX64.PrintWEW2`, `Spike.Lib.LowerX64.PrintWBW2`, imported by
`Spike.X64`),
`Spike.Lib.LowerA64.PrintCallInst` (an output call assembled inside `W2` at `msOfAB`: `printCallC_inst`,
`printCallCH_inst`, `printCallC_of'` / `printCallCH_of'` with `hWL`, `hPW`, `hPWE` discharged, the walk's facts
premises; the x86-64 twin `Spike.Lib.LowerX64.PrintCallInst` imported by `Spike.X64`, over `printCallCH_ofR` in
`Spike.Lib.LowerX64.PrintCallC2H`),
`Spike.Lib.LowerA64.PrintCallInstJ` (the print-call lemmas with the frames placed knowing the argument block,
`hfpJ`, no `FStable` of the caller's condition in `printWE_w2J`, `printW_w2J`, `printW_w2BJ`; `printW_hPWJ_ABJ`,
`printWE_hPWEJ_J`; `printCallC_instJ`, `printCallCH_instJ`: `hPer` split into `hNoS`, `hfpJ`, `hcall`/`hcallE`,
`hDtP`),
`Spike.Lib.LowerA64.PrintStepK` (the steps of the print-argument block and `bl` keep the caller's frame word and
the slots off the frame: `StepK`, `stepK_of`, `arun_take_stepK`, `FreshW`, `printArgs_take`),
`Spike.Lib.LowerA64.PrintCallInstA` (the print-call lemmas with `hfpJ`, `hcall`, `hcallE` discharged from the
code, over `printCallC_ofA` / `printCallCH_ofA` and `PrintSlotsA` / `PrintLen` in `Spike.Lib.LowerA64.PrintCallC2`:
`framesPlaced_ofSlotRep`, `printArgW_framesJ`, `printCallOkR_of`, `printW_hPWA`, `printWE_hPWEA`,
`printCallC_instA`, `printCallCH_instA` with the per-call return-address premises `hraP`, `hraAb`;
`hraP_of_blC2`, `hraAb_of_blC2`),
`Spike.Lib.LowerA64.PrintCallInstAI` (the same at a table `i` below the layout's, agreeing at the calls'
continuations: `immIn_mono_i`, `slotRepAt_mono_i`, `letAt_mono_i`, `printCallC_instAI`, `printCallCH_instAI`),
`Spike.Lib.LowerX64.PrintCallInstJ` (x86-64, imported by `Spike.X64`: `printCallC_instJ`, `printCallCH_instJ`,
the per-call premises split into `hNoS`, the frames along the argument block `hfpJ`, the residual
`PrintCallOkR` `hcall`/`hcallE` and the write tail `hDtP`; `printWE_w2J`, `printW_w2J`, `printW_w2BJ`,
`printW_hPWJ_ABJ`, `printWE_hPWEJ_J`),
`Spike.Lib.LowerX64.PrintCallInstA` (x86-64, imported by `Spike.X64`: `printCallC_instA`, `printCallCH_instA`
over `printCallC_ofA`/`printCallCH_ofRA`, the frames along the argument block (`printArgW_framesJ`,
`framesPlaced_ofSlotRep`) and `PrintCallOkR` (`printCallOkR_of`) derived; left `hNoS`, `hraP`, `hraAb`
(`hraAb_of_blC2`) and `hDtP`),
`Spike.Lib.LowerX64.PrintCallInstAI` (x86-64, imported by `Spike.X64`: `printCallC_instAI`, `printCallCH_instAI`,
`printCallC_instA`'s at a lowering table `i` apart from the world's: `i`'s entries the world's (`hiL`,
`letAt_imms`, `bodyN2_imms`), the two agreeing at each `print` continuation (`hie`), the return address's facts
from the calls at `BlC2` (`hraP_of_blC2`, `printRa_notAb`)),
`Spike.Lib.PrintTopExt` (`PrintTop` at the extern's model terms or `ret ()`: `printTop_ext`, the `hTop` of
`r_componentsAE`),
`Spike.Lib.A64ConsumerAEPrint`, `Spike.Lib.X64ConsumerAEPrint` (`Correct` through `print`'s `write` at
`Top := PrintTop`: `compAE_printTop`, `correctKOnAEP`, `hE` by `emitA_of_nodes` and `hcompE` by `r_componentsAE`;
`hps`, `hpsE`, `hsvc`, `hsvcE` by `Spike.Lib.A64WriteDead` / `Spike.Lib.X64WriteDead`;
the x86-64 twin imported by `Spike.X64`),
`Spike.Lib.PrintSvcRun` (the source's runs from `print`'s output `write`, on any ISA: `PrintTop`,
`frameRun_printSvc`, `byteOut_printTop`), `Spike.Lib.A64EmitOfNodes` (the emit rows from the node obligations and
`PrintSvc`: `emitA_of_nodes`),
`Spike.Lib.WriteDead`, `Spike.Lib.A64WriteDead`, `Spike.Lib.X64WriteDead` (with `write` a certification dead
end: `certStep_write_none`; `correctKOnAE`'s `hsvc`, `hsvcE`, `hpsE`, `hps`: `writeNoPromA_b`, `writeNoPromAE_b`,
`promSharedAE_b`, `promSharedA_b`; the x86-64 twin imported by `Spike.X64`),
`Spike.Lib.A64ConsumerAW`, `Spike.Lib.X64ConsumerAW` (the arena consumers' `Correct` with the certification
premises at a `write` discharged by `Spike.Lib.A64WriteDead`/`X64WriteDead`: `correctKA_w`, `correctKOnA_w`,
`correctKA'_w`, `correctKOnA'_w`, `correctKA_of'_w`, `correctKAE'_w`, `correctKOnAE_w`, `correctKAEmitE'_w`;
the x86-64 twin imported by `Spike.X64`),
`Spike.Test.A64ByteOutPrivHello1`, `Spike.Test.X64ByteOutPrivHello1` (`byteOut_emit_priv` at hello1's buffer
bytes, `hpriv` discharged from the run's `PrivInv`),
`Spike.Lib.A64Hello1RdQ`, `Spike.Lib.X64Hello1RdQ` (`rdQ_ok`: the setups' `hQ` from the memory side's fields alone),
`Spike.Test.A64MsOfHello1Gap`, `Spike.Test.X64MsOfHello1Gap` (`msOf` carries no arena: `units`, `cells`, `heap`,
`ctr` at the defaults, so `hu` and `hQ` wait on more than `heap`),
`Spike.Test.A64PrintByteOutHello1`, `Spike.Test.X64PrintByteOutHello1` (`print_call_segWB` at hello1's
print call: `hpw`, `hov` from the setup's post and the allocator's premises),
`Spike.Lib.FreshSrc` (the source's next allocation label is fresh, from the memory relation and `FreshInv`).
`Spike.Lib.HeapObl` (the consumers' heap obligations, ISA-free: `HeapAbortObl`, `HeapCtr`, `AllocInvAt`),
`Spike.Lib.A64HeapObl` (the AArch64 allocator discharges them), `Spike.Lib.X64HeapObl` (the same on x64,
with `Jfull.heapReady`), `Spike.Lib.X64NewBufHeap` (x64's buffer allocation's heap abort exit discharges them),
`Spike.Lib.HeapPresCore` (`AllocInvAt` at the source's heap use along an allocation's steps, `land_step`; a
lane store and every other source step keep `heapUse`), `Spike.Lib.HeapPres` (with `SrcCalls`: `print`'s
`outCfg` keeps `heapUse`).
`Spike.Lib.LowerA64.PrintArgs` (`callBlock`'s `print` argument block from any caller's frame: `printArgs_run`,
`printArgsImm_run`, `inst_print_call`), `Spike.Test.LowerA64PrintArgs` (at `hello1`'s frame: the code is `wcE`),
`Spike.Lib.LowerX64.PrintArgs` (x64: `printArgs_runs`, `printArgsImm_runs` around the multiply's flag node,
`emitInst_print_items`), `Spike.Test.LowerX64PrintArgs` (at `hello1`'s frame: the code is `wcE1`, `wcMul`, `wcE2`),
`Spike.Lib.LowerA64.PrintCall` (the block, `bl scc_rt_print` and `print`'s run from any caller node:
`print_block_segW`), `Spike.Lib.LowerX64.PrintCall` (x64: the block around the multiply, `call scc_rt_print`
and `print`'s run: `print_blocks_segW`, `print_block_segW`).
`Spike.Lib.A64AbortWriteW` (the write abort path `scc_rt_abort(4)` inside `W`: `seg_disp4W`, `StubWW`,
`seg_abort4W`, `seg_jabort4W`; x64: `Spike.Lib.X64AbortWriteW`), `Spike.Lib.A64RtAbortSeg` (`print`'s and the
allocator's calls with their abort paths, one segment each: `print_call_abort_segW`, `newBuf_call_abortW`, the
region premises in `RtDepthA64`'s fits form `PrintFits`, `AllocFits`), `Spike.Test.A64RtAbortSeg` (the premises
instantiate; `hello1`'s rodata bound), x64: `Spike.Lib.X64RtAbortSeg`, `Spike.Test.X64RtAbortSeg`.
`Spike.Lib.A64AbortStubCode` (`StubHW`/`StubWW` from `abortIn`, given the nodes' states inside `W`:
`stubHW_of_code`, `stubWW_of_code`; x64: `Spike.Lib.X64AbortStubCode`),
`Spike.Lib.HeapLand` (an allocation-capable consumer's heap pieces: `AllocInvAt.prom_keep`, the landing's
`AllocLand`, `alloc_rowS`: an `Out.alloc` row's source allocation at the source's heap use),
`Spike.Lib.Arena` (the allocator's arena, ISA-neutral: `Arena`, `Arena.OK`, `Arena.ofWords_ok`),
`Spike.Lib.A64ConsumerA` (the one-thread consumer with buffer allocation, its definitions and frame runs:
`Arena`, `msOfA`, `NodesA`, `PreJA`, `RSA`),
`Spike.Lib.CtrRows` (`ExtRows.out_localP` with the counter's add giving its write: `CtrW`, `ctrRmw_row`,
`out_localW`, `out_memW`),
`Spike.Lib.A64ConsumerAMem` (`AllocInvAt` along an instruction's outcome: `allocInvAt_out` for a word the arena
allows, `allocInvAt_ctr` for the counter's add),
`Spike.Lib.A64ConsumerASys` (`A64ConsumerS`'s system-call, transfer-site and spawn facts over `NodesA`;
`PromSharedA`),
`Spike.Lib.A64ConsumerAInstr` (an instruction step from `PreJA` lands in `RSA`: `instr_stepA`, the counter's
add stuttering into its hold, the allocation's last instruction allocating at the fresh label),
`Spike.Lib.A64ConsumerAStep` (every step from `RSA` is matched: `pre_stepA`, `r_stepA`),
`Spike.Lib.A64ConsumerACore` (the certification core with the arena: `PreCoreJA`, `core_stepA`, `promSharedA`),
`Spike.Lib.A64ConsumerACorrect` (`Correct` for the allocation-capable consumer: `pre_loadA`, `stepSimA`,
`pre_progressA`, `r_abortA`, `correctKOnA`, `correctKA`),
`Spike.Lib.A64ConsumerAStart` (that `Correct` at any source start with `StartOk`, e.g. before a setup block:
`StartOk`, `pre_loadA'`, `stepSimA'`, `correctKOnA'`, `correctKA'`, `correctKA_of'`),
`Spike.Lib.A64ConsumerAWr`, `Spike.Lib.X64ConsumerAWr` (`NodesA`'s `ctrRow` and `arena` at a pair from the
instruction's address, for producers: `WrOkA`, `WrOkA.ctrRow`, `WrOkA.arena_of`, the header store `wrOkA_header`),
`Spike.Lib.ZeroTy` (`NodesA.zero` from a check per type: `ZeroOkTy`, `zero_of_zeroOkTy`, `zeroOkTy_lanes`),
`Spike.Lib.A64SegInstA`, `Spike.Lib.X64SegInstA` (the allocation-capable consumer's obligations from two
segment levels, before and after one allocation: `SegInvS`, `I2`, `SFactsA` with the abort phase `Ab`,
`inst_of_segWA2`), `Spike.Lib.AllocReach` (the placements reachable by allocations, ISA-neutral: `upd`,
`updN`, `Reach`, the multi-level fragment `IN`, `Reach.placed`, `Reach.mono`), `Spike.Lib.A64SegInstN`,
`Spike.Lib.AllocReachRoom` (`Reach.lblRoom`: `LblRoom` at every reachable placement from the arena in the heap
and `below32`; `lblRoom_none`),
`Spike.Lib.AllocLandOf` (`allocLand_of_ea`: an allocator's landing base and words land in the arena under
`Arena.OK`, ISA-neutral),
`Spike.Lib.X64SegInstN` (the obligations from a segment at every reachable placement, any `ab`:
`inst_of_segWAN`), `Spike.Lib.A64SFactsA` (`SFactsA` from the state's facts and the pair's: `SFactsSt`,
`SFacts.toSt`, `AbSt`, `abortOkA_of_ne`, `SFactsA.ofSt`, `SFactsA.ofSFacts`), `Spike.Lib.X64SFactsA` (its x86-64
twin, name for name),
`Spike.Lib.LowerA64.PrintW2` (`printSvc_w2`: `print`'s `write` call inside `W2` at `print`'s frames, from
`printSvcStP`, `printSvcAb`, `printSvc_src`, `printSvc_abort`; `frOk2_printC`; `printW2`: `print`'s blocks
inside `W2` from `printSt`, `printAb`, `printNoWr`, `printPc`),
`Spike.Lib.LowerA64.PrintArgW2` (`printBlkW_w2`, `printBlkW_w2C`: a call of `print`'s argument block and its
`bl` inside `W2`, `PrintBlkW`'s first conjunct, from the block's code and `print_ph`, its phase check from the
code predicates' chunks; `blkW_w2BPc`: `blkW_w2BP` at a block's code `CdOf` in place of its `blockAt`;
`printBlkW_ab`: its `hab` at `CdCL`, `BlC2L`; `frOk2_ret`, `printJ_hJ`: its `hJ`),
`Spike.Lib.LowerA64.PrintCallW2` (`printWL_w2`: `printCallC_of`'s `hWL`, an output call's `let` inside
`W2` as the argument block's first state; `Spike.Lib.LowerX64.PrintCallW2` its twin),
`Spike.Lib.LowerA64.PrintCallOkF` (`print`'s call-state facts from the program: `pR_facts`, `pF_stable`,
`pF_off`, `x1_lt`, `print_phDone`, `printRa_ph`, `printRa_notAb`, `printCall_ra`; `Ret0.callerCells_stable`;
`Spike.Lib.LowerX64.PrintCallOkF` its twin),
`Spike.Lib.LowerA64.PrintAbW2` (`printAbSeg2`: `printCallC_of`'s abort landing `printNA` a segment with frames,
through the write abort path's obligations without code `StubWN`; `stubWN_w2`: those inside
`W2 … (WriteAb.Ab lab)`; `Spike.Lib.LowerX64.PrintAbW2` its twin),
`Spike.Lib.LowerA64.SFactsA2` (the facts at an `Accepted2` program's pair: `W2`, `sfactsA_of_W2` through
`SFactsA.ofSt` with the cell and zero obligations from `RunOk2`, `w2_of`), `Spike.Lib.LowerX64.SFactsA2` (its
x86-64 twin, imported by `Spike.X64`), `Spike.Lib.LowerA64.W2Blk` (a block's and a node's states inside `W2`
from their parts: `SFacts` at the source start's control, `W2Part` (the abort phase, the frames placed, the write
obligation), the node's controls `FrOk2`: `BlkW.w2`, `NodeW.w2`, `noAbort_of_sfacts_c0`), `Spike.Lib.LowerX64.W2Blk`
(its x86-64 twin), `Spike.Lib.LowerA64.RtW2` (the runtime's own states inside `W2`, off the arena's heap and
counter: `WrOff`, `wrOkA_of_wrOff`, `w2Part_of_wrOff`, `BlkW.w2_rt`, `NodeW.w2_rt`),
`Spike.Lib.LowerA64.RtStartX` (the runtime's start states as `RtX`: the abort phase, the frames placed, off the
arena, at the source start's control: `RtX`, `rtX_w2`, `blkW_rtX`, `htgt_posOff`,
`nodeW_rtX_si`, `nodeW_rtX_st`, `nodeW_rtX_ldop`, `nodeW_rtX_svc`, `blkW_abSt_tg`, `htgt_offR`, `blkW_rtXG`,
`nodeW_rtX_ldr`, `nodeW_rtX_swp`, `nodeW_rtX_stlr`, `site_rtX`, `nodeW_rtX_reg`),
`Spike.Lib.LowerA64.RtStartXOf` (`scc_rt_start`'s nodes inside `RtX` at a placed output: `startW_rtX`,
`startCall_rtX`, `tcbW_rtX`, `pairW_rtX`, `takeW_rtX`, `tiW_rtX`,
`swEW_rtX`, `startEW_rtX`),
`Spike.Lib.LowerA64.StartEW2` (`scc_rt_start` to `bl scc_rt_main` inside `W2` at a placed output: `swEW_gen`,
`TcbW.imp` … `StartEW.imp`, `startEW_sfacts`, `startEW_w2`; at `arOf`: `rtWords_offArena`,
`mainPosOff_of_placeOKAt`, `startEW_w2A`),
`Spike.Lib.LowerA64.Start2W2` (the consumer's `h0` at a placed output: `rtX_w2G`, `startEW_w2G`,
`msOfAX_K_abi`, `h0_of_startS`; its premises at a placed output: `mainSIn_of_placeOKAt`, `rows_ofPlaceOK`,
`limOk_ofPlaceOK`, `hun_ofPlaceOK`; at an entry state: `W2At`, `MSAt`, `h0_ofPlaceOK`),
`Spike.Lib.LowerA64.RtMainX` (`scc_rt_main` after a setup block inside `W2`: `RtM`, `RtX.toM`, `blkW_rtM`,
`nodeW_rtM_ldr`, `nodeW_rtM_exit`, `marshal_facts`, `setupMC_Z`, `setupMC_k`, `setupMC_blks`, `mainSW_rtM`;
`MainCtl`, `BlkW.ofCtl`, `NodeW.ofCtl`, `MainSW.ofCtl`, `MainSW.imp`, `rtM_w2`; at a placed output:
`mainSW_ofPlaceOK`, `h0_ofPlaceOK`'s `hW`; `rtM_sfacts_setupEntry`, `hWC_ofPlaceOK`; `h0_ofPlaceOK_setup`),
`Spike.Lib.LowerA64.SetupProOf` (the setup function's prologue facts from `PlaceOK`: `setupPro_ofPlaceOK`),
`Spike.Lib.SetupRodata` (`rodata` a compiled block: `rodata_compiled2`, `rodata_compiled2_ofSetupOf`),
`Spike.Lib.MainCompiled2` (`main` a compiled block: `main_compiled2`, `main_compiled2_ofAccepted2`),
`Spike.Lib.LowerA64.SetupCodeOf` / `Spike.Lib.LowerX64.SetupCodeOf` (the assembled `H0In`'s code facts from the
placement check: `mainPro_ofPlaceOK` / `mainHead_ofPlaceOK`, `setupCode_ofPlaceOK`),
`Spike.Lib.LowerA64.PostSOf` / `Spike.Lib.LowerX64.PostSOf` (the setup call's post's controls' facts:
`th02_term_setup`, `postS_setupTerm`),
`Spike.Lib.LowerA64.H0InAssembledCA` / `Spike.Lib.LowerX64.H0InAssembledC` (the assembled `H0In` with those
discharged: `h0InA_setup_assembledC`, `h0In_setup_assembledC`),
`Spike.Lib.LowerA64.H0InSetupBA` / `Spike.Lib.LowerA64.H0InAssembledCBA` (the assembled `H0In` at the setup
call's known frame condition `SetupGF`: `h0InA_of_setupFNB`, `h0InA_of_setupFNPB`, `h0InA_setup_assembledFB`,
`h0InA_setup_assembledCB`; `Spike.Lib.LowerA64.HSAssembledBA`: its `hS` from the placement check with the
bottom key `SetupBot` known, `hS_assembledBA`),
`Spike.Lib.LowerX64.RtMainXV` (`h0` with `main`'s post at the held pair placed by its value: `MainCtlV`,
`xExitW_placedV`, `hWx_ofPlaceOKV`, `h0_ofPlaceOK_setupFV`), `Spike.Lib.LowerX64.H0InAssembledV` (the `H0In`
chain at the post `UPostRF ∧ MainCtlV`, without `hPost`: `h0In_setup_assembledV`, `h0In_setup_assembledCV`),
`Spike.Lib.LowerA64.RtMainXVA` / `Spike.Lib.LowerA64.H0InAssembledVA` (their AArch64 twins, `x0` kept by the
exit tail: `exitTail_take_X0`, `exitW_placedV`, `h0_ofPlaceOK_setupFV`, `h0InA_setup_assembledV`,
`h0InA_setup_assembledCV`),
`Spike.Lib.LowerX64.RtMainXVL` (the exit tail inside `W2AtL` at any current placement, the post placed by its
value: `hWx_ofPlaceOKVL`),
`Spike.Lib.LowerA64.RtMainXVLA` (its AArch64 twin: `hWx_ofPlaceOKVL`),
`Spike.Lib.LowerX64.MainS0L` (`scc_rt_main`'s segment from the marshalling block inside `W2AtL` at any current
placement at the switch frame with `WordsNone`, a setup bottom key's `h0`: `mainS0_segL`),
`Spike.Lib.LowerX64.W2Pop` (`W2` before a frame pop from `W2` at the popped pair, the popped control neither at
an allocation nor at an overflow: `w2_ofPopped`),
`Spike.Lib.LowerX64.SetupBotPop` (a setup bottom key's exit: its one frame is the setup call's, popped to
`mainS0`: `setupBot_popM`),
`Spike.Lib.LowerX64.PlacedRetFr` (a `ret`'s pair with its caller's frame placed from the popped control's
placement and the result registers: `placedS_retFr`; `FrOk2` there: `frOk2_retFr`),
`Spike.Lib.LowerA64.W2Pop` / `Spike.Lib.LowerA64.SetupBotPop` (their AArch64 twins: `w2_ofPopped`,
`setupBot_popM`),
`Spike.Lib.LowerA64.MainS0L` (`scc_rt_main` from the marshalling block at a current placement, the frame
with `WordsNone`; a setup bottom key's `h0`: `mainS0_segL`),
`Spike.Lib.LowerX64.H0InSetupB` / `Spike.Lib.LowerX64.H0InAssembledCB` (the assembled `H0In` at the setup
call's known frame condition `SetupGF`: `h0In_of_setupFNB`, `h0In_of_setupFNPB`, `h0In_setup_assembledFB`,
`h0In_setup_assembledCB`; `Spike.Lib.LowerX64.HSAssembledB`: its `hS` from the placement check with the
bottom key `SetupBot` known, `hS_assembledB`),
`Spike.Lib.LowerX64.RtMainXVB` / `Spike.Lib.LowerX64.H0InSetupVB` / `Spike.Lib.LowerX64.H0InAssembledCVB` and
`Spike.Lib.LowerA64.RtMainXVBA` / `Spike.Lib.LowerA64.H0InSetupVBA` / `Spike.Lib.LowerA64.H0InAssembledCVBA` (the
assembled `H0In` at the setup call's known frame condition `SetupGF`, `main`'s post `UPostRF ∧ MainCtlV`
without `hPost`: `h0_ofPlaceOK_setupFVB`, `h0In_setup_assembledCVB`, `h0InA_setup_assembledCVB`),
`Spike.Lib.LowerX64.H0InAssembledBVB` / `Spike.Lib.LowerA64.H0InAssembledBVBA` (with the start and stack facts
discharged as in `H0InAssembledS`/`H0InAssembledB`, over `h0In(A)_setup_assembledCVB`: `h0In_setup_assembledSVB`,
`h0In_setup_assembledBVB`, `h0InA_setup_assembledSVB`, `h0InA_setup_assembledBVB`),
`Spike.Lib.LowerA64.RtMainXNBF` / `Spike.Lib.LowerA64.RtMainXVBF` (the same `h0` with an extra frame `Fw` after
the switch, through `startSF_segWSFB`: `at_mono`, `startEWF_of`, `h0_ofPlaceOK_setupFNBF`,
`h0_ofPlaceOK_setupFVBF`),
`Spike.Lib.LowerA64.H0InSetupVBAF` / `Spike.Lib.LowerA64.H0InAssembledCVBAF` /
`Spike.Lib.LowerA64.H0InAssembledBVBAF` (the assembled `H0InAW` over it at `Fw := WordsNone`, the start at
`WordsNone ∧ rtF`, `hS` / `hU` at `WordsNone ∧ swFSL`:
`h0InA_of_setupFVBF`, `h0InA_of_setupFNPVBF`, `h0InA_setup_assembledFVBF`, `h0InA_setup_assembledCVBF`,
`h0InA_setup_assembledSVBF`, `h0InA_setup_assembledBVBF`),
`Spike.Lib.LowerA64.H0InAssembledSA` / `Spike.Lib.LowerX64.H0InAssembledS` (the assembled `H0In` with the start
control's facts also discharged by `Start2C0A` / `Start2C0`: `h0InA_setup_assembledS`, `h0In_setup_assembledS`),
`Spike.Lib.LowerA64.H0InAssembledBA` / `Spike.Lib.LowerX64.H0InAssembledB` (with the stack bounds also
discharged by `stackBounds2A` / `stackBounds2`, `hS` / `hU` for every choice of them: `Bounds2A`, `Bounds2`,
`h0InA_setup_assembledB`, `h0In_setup_assembledB`),
`Spike.Lib.LowerA64.H1InNoneA` / `Spike.Lib.LowerX64.H1InNone` (the landings' segments at no landings:
`h1InA_none`, `in2A_ofH0None`, `h1In_none`, `in2X_ofH0None`),
`Spike.Lib.LowerA64.RtMainXRL` / `Spike.Lib.LowerX64.RtMainXRL` (`scc_rt_main`'s states inside `W2` at any current
placement: `W2AtL`,
`MSAtL`, `w2AtL_none`, `msAtL_none`, `mainSW_ofPlaceOKRL`, `hWx_ofPlaceOKRL`),
`Spike.Lib.SlotRepAt` (a control's words at their placements in a slot file, the node
invariant's fact of a lagging control: `LocBaseRegAt`, `SlotRepAt`, `SlotRepAt.of_nodeJ`, `SlotRepAt.of_nodeJE`,
`ImmIn.retype`, `LocBaseRegAt.retype`), `Spike.Lib.SlotRepNone` (a control placed at no label when its term's
free variables' words are not locatives: `SEnv.onFv`, `lookupS_onFv`, `WordsRep.none_of_noLoc`,
`SlotRepAt.none_of_noLoc`, `SlotRepAt.none_of_newBuf`), `Spike.Lib.A64PlacedSlot`
(`Placed`/`SlotPlacedI` from `SlotRepAt`, locatives included: `wpOf`, `envmPf`, `placedPf_of_slotRep`,
`placed_of_slotRep`, `slotPlacedI_of_slotRep`, `SlotPlacedI.of_eq`, `placedS_of_slotPlacedI`) and its x86-64 twin
`Spike.Lib.X64PlacedSlot`, `Spike.Lib.LowerA64.PlacedBlk` (a block's and a node's states placed from the node
invariant's `SlotRepAt` in the abstract slot file, no slot written before a block's last instruction: `noSlotWr`,
`arun_slot_noSlotWr`, `noSlotWr_take`, `placedS_of_abs`, `blkW_placedS`, `nodeW_placedS`; at a pending store,
`placedS_of_abs_upd`, `blkW_placedS_upd`) and its x86-64 twin
`Spike.Lib.LowerX64.PlacedBlk`, `Spike.Lib.LowerA64.W2Body` (a covered block of an `Accepted2` body inside `W2`,
assembled from its state's facts, its placement, no write and the abort phase: `blkW_w2B`, `blkW_w2C`, and at a
call's `bl`/`callq`, `blkW_w2Call`; at a checked `+`'s pending store, `blkW_w2Pend`; with the placement a
premise, `blkW_w2BP`, `blkW_w2CP`; at a callee's entry, `nodeW_w2CalleeEntry`; the producers' `hJp` at the body's
nodes, `slotRepAt_bodyN2`, `slotRepAt_pendN2`) and its x86-64 twin
`Spike.Lib.LowerX64.W2Body` (also `blkW_noWr'`;
no system call at a block's non-final instruction, `blkW_noSys` and its twin `blkW_noSys'`),
`Spike.Lib.LowerA64.NoSlotWr` (no slot written before a
block's last instruction, `blkW_placedS`'s premise, for an `Accepted2` body's blocks: `noSlotWr_of_ne`,
`noSlotWr_getOp`, `noSlotWr_leave`, `noSlotWr_kind1`, `noSlotWr_kind2`, `noSlotWr_single`) and its x86-64 twin
`Spike.Lib.LowerX64.NoSlotWr` (on directives: `noSlotWrD`, `noSlotWrD_kindD2`),
`Spike.Lib.LowerA64.HN2` (the consumer's node obligations of an `Accepted2` program's run at `IN` from a
segment at every reachable placement inside `W2`: `nodes2_of_segW2`, and with a closed write tail
`nodes2_of_segW2_closed`; the output `write`'s source at `print`'s loop top `Svc1S`, `svc1S_of_segInW2`, and the
emit rows `emitA_of_svc1S`) and its x86-64 twin `Spike.Lib.LowerX64.HN2`,
`Spike.Lib.LowerA64.Levels2` (the levels at every reachable placement as the greatest family `gfpN` of
segments over any family containing the starts: `segInvN_of_levels`, `nodes2_of_levels`; from the start's and
the allocations' landings' segments, `StartsN`, `xa_of_landN`, `nodes2_of_starts`) and its x86-64 twin
`Spike.Lib.LowerX64.Levels2`,
`Spike.Lib.Src.LblRange` (a placed label's words below its size unmapped in private memory: `LblRange`,
`lblRange_of_memRel`, `heapWord_none`),
`Spike.Lib.Src.LblBelow32` (a placed label's base below `2 ^ 32` from `LblRange` and PlaceOK's `below32`:
`lbl_lt32`),
`Spike.Lib.LblArena` (every placed label inside the allocator's arena, ISA-neutral: `LblArena`,
`LblArena.none`, `LblArena.alloc`, `LblArena.reach`, `LblArena.word`, `LblArena.lblRange`, `LblArena.heap`),
`Spike.Lib.LblRangeReach` (`LblRange` at every reachable placement and a fresh allocation past one:
`lblRange_reach`, `lblRange_upd`),
`Spike.Lib.LowerA64.HeapW` (a lane store's element word a heap word: `HeapW`, `mapped_K0_of_heap`,
`not_own_of_heap`, `heapW_of`) and its x86-64 twin `Spike.Lib.LowerX64.HeapWOf`,
`Spike.Lib.LowerA64.LaneW2` (a lane store's nodes inside `W2` for `CdC`, the element's word a `HeapW`:
`laneW_w2`, at a code predicate inside `CdC`: `laneW_w2E`; heap-word load/store node facts, covered-block
facts at a block's code; the x86-64 twin `Spike.Lib.LowerX64.LaneW2`),
`Spike.Lib.LowerA64.LaneCW2` (`LaneC` at `CdC` from `laneC_of` and `laneW_w2`, the lane's walk facts and
`HeapW` as premises: `laneC_w2`; at `CdCL`, the pcs off the write abort's from the labels but the one after the
lane's store, the controls' facts from `FrOk2` at the ghost: `laneC_w2'`; the x86-64 twin
`Spike.Lib.LowerX64.LaneCW2`),
`Spike.Test.A64Hello1CorrectA`, `Spike.Test.X64Hello1CorrectA` (`hello1.w` correct through `correctKA` from
its remaining obligations, listed by owner: `hello1_correctKA`, `init_of_loadParsed`; `hello1_correctKL` with the
load facts discharged), `Spike.Test.A64Hello1Load`, `Spike.Test.X64Hello1Load` (`hello1.w`'s load facts: `hload`,
`himg`, `hss`, `hfr0`, `htk0`, `hown0` at the producer's `Inst.own`, `hG0`, `hGpl` at `FixG Fix hello1M0`,
`hμ` at the take site's label),
`Spike.Test.A64Hello1StartA` (`hello1.w` correct at any source start with `StartOk`: `hello1_correctKA'`,
`hello1_correctKL'` with `hμ` discharged, `hello1_correctKLS` at the start before the setup block),
`Spike.Test.X64Hello1StartA` (its x86-64 twin, with `labT_siteL`, `hello1_hμ` for the take site),
`Spike.Lib.A64Hello1SetupPre` (`scc_rt_main`'s part before `rodata` at the setup block's call depth:
`hello1_main_pre_segWS`; the setup block's call into `rodata` as a frame run: `setupCall`, `setupCall_run`),
`Spike.Lib.A64Hello1SetupPost` (`scc_rt_main` from the allocator's return, `rodata`'s return popping its frame:
`hello1_main_sp0_segW`, `retJ`, `MainPostSW`, `hello1_main_post_segWS`),
`Spike.Lib.Rt.A64StartE` (the runtime's start up to `scc_rt_main`'s entry on either tail, `scc_rt_main` the
program's: `SwEW`, `StartEW`, `MainE`, `startSwitchE_segW`, `startE_segW`, `startE_segWS`),
`Spike.Lib.Rt.A64StartEF` (the same with an extra frame `Fw` after the switch: `SwEWF`, `StartEWF`, `MainEF`,
`startSwitchEF_segW`, `startEF_segW`, `startEF_segWS`), `Spike.Lib.Rt.A64MainSSBF` (the setup block's call at
its ghost frame condition under it: `mainESF_segWSFB`, `startSF_segWSFB`),
`Spike.Test.A64Hello1StartE` (its code checks on `hello1.w`: `hello1_rtCodeOkS`, `hello1_rtCodeIn0`),
`Spike.Lib.Rt.X64StartE`, `Spike.Test.X64Hello1StartE` (their x86-64 twins, from `_start`: `entryE_segW`,
`StartE1W`, `MainE` in `call scc_rt_main`'s callee region, `scc_rt_thread_init` at `xr`: `hello1_rtCodeInTi`),
`Spike.Lib.Rt.X64StartEF` (`X64StartE` with an extra frame `Fw` after the switch, so a frame fact on the
memory before it reaches `scc_rt_main`: `SwEWF`, `MainEF`, `mainEF_ok`, `startEF_segW`, `startEF_segWS`),
`Spike.Lib.Rt.X64MainSSBF` (`mainES_segWSFB`, `startS_segWSFB` over them: `mainESF_segWSFB`, `startSF_segWSFB`),
`Spike.Lib.Rt.X64WMonoF` (the obligations at a stronger frame condition: `NodeW.monoF`, `BlkW.monoF`,
`MainSW.monoF`, `StartEW.toF`), `Spike.Lib.LowerX64.RtMainXVBF` / `Spike.Lib.LowerX64.H0InSetupVBF` (the setup
call's `hS` and `hU` at `(Fw ∧ swFSL) ∧ CallerCells`: `h0_ofPlaceOK_setupFVBF`; at `Fw := WordsNone`, `H0InW`:
`h0In_of_setupFVBF`, `h0In_of_setupFNPVBF`), `Spike.Lib.LowerX64.H0InAssembledCVBF` /
`Spike.Lib.LowerX64.H0InAssembledBVBF` (the assembled `H0InW`: `h0In_setup_assembledCVBF`, `h0In_setup_assembledBVBF`),
`Spike.Lib.A64Hello1SetupGlue` (`scc_rt_main` at the setup block's call from its entry to `print`'s abort
or the heap abort, cuts A and B's premises: `SetupPreP`, `SetupPostP`, `rdJ'`, `setupL`,
`hello1_setup_main_segWS`, `hello1_setup_segWS`), `Spike.Test.A64Hello1SetupChain` (from `_start` on
`hello1.w`: `setupC`, `setupTerm_eq`, `hello1_setup_chainWS`),
`Spike.Lib.X64Hello1SetupPre`, `Spike.Lib.X64Hello1SetupPost`, `Spike.Lib.X64Hello1SetupGlue`,
`Spike.Lib.X64Hello1SetupTail`, `Spike.Lib.X64Hello1Levels`, `Spike.Test.X64Hello1SetupChain` (their x86-64
twins: `.x2`/`.x13` for `.sp0` (`MainX2W`, `hello1_main_x2_segW`, `rX_x13_none`), `%rbp` at the returns
(`hbp`, `hbpr`, `hbpw`), `scc_rt_main` after the start in `mainR v L` under `mainF` (`mainE_ok`), the
dispatcher's `32` below an abort node (`setupL := 80 + 208 + 32`, the start's depth `setupL + 8`),
`Abort.Disp.seg_jabort2W_up` by `at_leave`),
`Spike.Test.X64Hello1LevelsA` (x86-64: `hello1_correctKLS`'s `inv0`, `inv1` from the two levels' closed
segments: `segInvS_mono_xa`, `xa_of_land`, `exists_inv1`, `exists_inv0`, `exists_invs`,
`hello1_correctKLS_levels`),
`Spike.Test.X64Hello1LevelsB` (x86-64: `h0W`, `h1W` from the levels' segments, the level after's start `P1A`
at `wc_rodata`'s `.x13`: `landJ_xa`, `hxa_pre`, `h0W_of`, `h1W_of`, `hello1_correctKLS_levelsB`),
`Spike.Lib.X64Hello1SFactsN`, `Spike.Test.X64Hello1SFactsN` (x86-64: `SFactsA` at a node state with frames from
the node's `SFacts`, for the levels' `hW0`/`hW1`: `RunOk`, `NoArenaWr`, `Placed.mono`, `FramesPlaced.mono`,
`static_le_upd`, `sfactsA_of`, `sfactsA_wr`, `sfactsA_node`; with `Spike.Lib.X64PlacedS` and `Spike.Lib.Frames1`
as on `h7c-alloc`),
`Spike.Test.X64Hello1RtW` (x86-64 twin of `Spike.Test.A64Hello1RtW`: `hello1_instOk`, `hello1Rows`, `hello1Ra`,
`hello1Dead`, `hello1TabX`, `labT_eq_labX`, `hello1_rtNodesOk`),
`Spike.Test.X64Hello1Gfp` (x86-64 twin of `Spike.Test.A64Hello1Gfp`: `GfpS`, `closeS_mono`, `le_gfpS`,
`segInvS_gfpS`, `gfpS_of_segWS`),
`Spike.Test.X64Hello1W0` (x86-64 twin of `Spike.Test.A64Hello1W0`: `AbortW`, `ArenaWr0`, `W0` with the counter's
add in a context `Ctx`, `hW0`),
`Spike.Test.X64Hello1W1` (x86-64 hello1 after the allocation: `WrIn`, `wrOkA_of_wrIn`, `wrIn_of_noArenaWr`,
`AbortW1`, `W1`, `hW1`),
`Spike.Test.X64Hello1W0N` (x86-64 twin of `Spike.Test.A64Hello1W0N`: `W0` from `Wr` `w0_of_wr`, `wr_of_noArenaWr`;
the state's facts at any control `dumN`, `BlkW.st`, `NodeW.st`, `w0_of_st`),
`Spike.Test.X64Hello1AllocW` (x86-64 twin of `Spike.Test.A64Hello1AllocW`: `allocSt`, `BlkW.nodeW`,
`nodeW_si_postA`, `nodeW_st_postA`, the counter's `lock xadd` `nodeW_xadd_postA`),
`Spike.Test.X64Hello1AllocAb` (x86-64 twin of `Spike.Test.A64Hello1AllocAb`: `allocAb`, `allocAb_ret`, `blkW_ab`,
`blkW_abG`, `nodeW_ab_si`, `nodeW_ab_fi`, `nodeW_ab_st`, `nodeW_ab_xadd`, `abTabX`, `labY`, `labT_eq_labY`),
`Spike.Test.X64Hello1Ctr` (x86-64 twin of `Spike.Test.A64Hello1Ctr`: the counter add's context `CtxA`, its row
`hctrA`, the call swapped to one with its premises `qswap`, the allocator's frame `FaA`, `allocA_closedWS`),
`Spike.Lib.X64AbSt` (x86-64 twin of `Spike.Lib.A64AbSt`: `AbSt.ofLeaves`, `blkW_abSt`, `blkAb`, `blkAb_sound`),
`Spike.Lib.X64PlacedIn` (every frame placed in kept stack slots, the write abort stub's footprint: `PlacesIn`,
`PlacedSIn`, `.toPlacedS`, `.of_eq`, `KeptA`, `PlacedSIn.of_cKept`),
`Spike.Lib.X64Hello1WImp` (x86-64 twin of `Spike.Test.A64Hello1W0N`'s two-obligation lemmas: `NodeW.imp`,
`BlkW.imp`, `XProW.imp`, `XExitW.imp`, `Alloc.AllocW.imp`, `Print.PrintW.imp`, `RdPreW.imp`, `RdPostW.imp`,
`WcBody1W.imp`, `Wc1W.imp`, `MainPreW.imp`, `MainX2W.imp`, `MainPostW.imp`, `MainPostSW.imp`),
`Spike.Test.X64Hello1WImp`,
`Spike.Test.X64Hello1W1N` (x86-64 `W1` from `Wr` `w1_of_wr`, at a label the static placement does not place;
from the state's facts `w1_of_st`),
`Spike.Test.X64Hello1StartW` (x86-64 hello1 `StartEW` at `Wr`/`Kr`: `scc_rt_thread_init` returning to `.x8`,
`hello1_tiPhAt`, `hello1_takePhX8`, `st0W`, `x0WAt`, `swEW`, `startEW`, `startEW_c0`),
`Spike.Test.X64Hello1MainPreW` (x86-64 twin of `Spike.Test.A64Hello1MainPreW`: `scc_rt_main`'s prologue and
call of `wc_rodata` at `Wr`, `SFactsSt` and `AbSt`: `mainProWr`, `mainProSt`, `mainCallWr`, `mainCallSt`,
`nodeW_ab_fsld`, `mainProAb`, `mainCallAb`),
`Spike.Lib.Rt.X64WcRa` (x86-64 twin of `Spike.Lib.Rt.A64WcRa`: a return-address slot's value at offset 0
`WcRa`),
`Spike.Test.X64Hello1AllocArena` (x86-64 twin of `Spike.Test.A64Hello1AllocArena`: `allocArena`, `hdr_addr`,
`w0_of_stA`, `arenaWr0_of_noWr`, `blkW_noWr`, `nodeW_noWr_si`, `nodeW_noWr_fi`, `nodeW_wr_st`, `nodeW_wr_xadd`),
`Spike.Test.X64Hello1AllocCtr` (x86-64 twin of `Spike.Test.A64Hello1AllocCtr`: `ctr_lt_heap`, `allocCtr`,
`blkW_pc`, `nodeW_pc`, `abortW_of_pcOff`, `allocPc`, `allocAbortW`),
`Spike.Test.X64Hello1PlacedS` (x86-64 twin of `Spike.Test.A64Hello1PlacedS`: `wpRep_slot`, `framesPlaced_setup`,
`eB_eq`, `eB_fv`, `placed_rdN`, `ctl_of_N`, `allocW_of_ctl`, `allocPlaced`),
`Spike.Lib.Hello1Runs` (ISA-neutral: the controls `hello1.w`'s frame runs reach, its terms' suffixes `hello1Terms`,
`Good1H`, `good1H_run`, no load or store, only `LanesU8` buffers `Good1H.newBuf_ty`; with x86-64's `runOk_hello1`,
`runOk_of_term` in `Spike.Lib.X64Hello1SFactsN`),
`Spike.Lib.Hello1oRuns` (ISA-neutral: the controls frame runs of `hello1o`, `print` linked, reach: the suffixes
`Suffix`, `sufs`, `hello1oTerms`, the check `goodB`/`ProgOk`, `hello1o_ok`, `Good1Ho`, `good1Ho_run`,
`Good1Ho.not_load`, `Good1Ho.not_store`, `Good1Ho.newBuf_ty`; with `runOk_ho`, `runOk_hello1o` in
`Spike.Lib.X64Hello1SFactsN` and `Spike.Lib.A64Hello1SFactsN`), `Spike.Test.Hello1oRuns`,
`Spike.Lib.A64AbortWriteW` (the write abort path inside `W`: `seg_writeW`, `Disp.DN.nd4`, `Disp.seg_disp4W`,
`Disp.StubWW`, `Disp.seg_abort4W`, `Disp.seg_jabort4W`),
`Spike.Lib.A64AbortStubCode` (`StubHW`/`StubWW` from `abortIn`, given the nodes' states inside `W`:
`stubHW_of_code`, `stubWW_of_code`),
`Spike.Lib.A64Hello1SetupTail` (`scc_rt_main` at the setup block's source with its abort tails, no exit:
`at_leaveE`, `Abort.Disp.seg_jabort2W_up`, `MAbStub`, `HAbStub`, `hello1_mAb_segWS`, `hello1_heapAb_segWS`,
`hello1_setup_main_closedWS`, `hello1_setup_closedWS`, `hello1_main_post_closedWS`),
`Spike.Lib.A64Hello1Levels` (that segment cut at `rodata`'s allocation into a level before and a level
after: `rX_sp0_none`, `hello1_setup_pre_main_closedWS`, `hello1_setup_pre_closedWS`, `hello1_post_closedWS`,
`landJ`, `rd_land`, `land_post`),
`Spike.Test.A64Hello1LevelsA` (`hello1_correctKLS`'s `inv0`, `inv1` from the two levels' closed segments:
`segInvS_mono_xa`, `xa_of_land`, `exists_inv1`, `exists_inv0`, `exists_invs`, `hello1_correctKLS_levels`),
`Spike.Lib.A64Hello1SFactsN` (`SFactsA` at `hello1.w`'s node states from the node lemmas' `SFacts`: the
placement grown, `RunOk`, `NoArenaWr`, `sfactsA_of`, `sfactsA_wr`, `sfactsA_node`), `Spike.Test.A64Hello1SFactsN`
(the levels' `W0`, `W1` forms at a node: `node_w0`, `node_w1`),
`Spike.Test.A64Hello1LevelsB` (`hello1_correctKLS_levels`'s `h0W`, `h1W` from the levels' segments, the level
after's start the allocator's landing: `okA`, `landJ_xa`, `allocLand_of_land`, `P1A`, `PreP`, `hxa_pre`, `h0W_of`,
`h1W_of`, `hello1_correctKLS_levelsB`),
`Spike.Test.A64Hello1RtW` (the generic block and node lemmas at `hello1.w`'s instance: `hello1_instOk`, its rows'
phase checks `hello1_rtNodesOk` at `hello1Rows`, `hello1Ra`, `hello1Dead`, the extended labels `labX`),
`Spike.Lib.Hello1Runs` (ISA-neutral: the controls `hello1.w`'s frame runs reach, its terms' suffixes `hello1Terms`,
`Good1H`, `good1H_run`, no load or store, only `LanesU8` buffers `Good1H.newBuf_ty`; with `runOk_hello1`,
`runOk_of_term` in `Spike.Lib.A64Hello1SFactsN`),
`Spike.Test.A64Hello1W0` (`hello1.w`'s states before the allocation, cut A's fragment `W0` and its `SFactsA`
`hW0`, at the write abort's phase `WriteAb.Ab`, the counter's add in a context `Ctx`; the abort sites
`AbortW`, the arena's writes `ArenaWr0`),
`Spike.Test.A64Hello1Gfp` (the greatest closed invariant inside a fragment `GfpS`: `segInvS_gfpS`, `le_gfpS`,
`gfpS_of_segWS`, `closeS_mono`),
`Spike.Test.A64Hello1Ctr` (`hello1.w`'s counter add before the allocation: `fstable_aR`,
`FrameRun.eq_of_newBuf`, the allocator's frame `FaA` and no exit from it `allocA_closedWS`),
`Spike.Test.A64Hello1W0N` (`W0` from `Wr` `w0_of_wr`; two node obligations into one: `NodeW.imp` …
`MainPreW.imp`),
`Spike.Test.A64Hello1AllocW` (`scc_rt_alloc`'s states carry the state's facts at any control `allocSt`; a node
after the take in a region off the stack range: `nodeW_si_postA`, `nodeW_st_postA`, `nodeW_ldop_postA`),
`Spike.Test.A64Hello1AllocAb` (`scc_rt_alloc`'s states keep the write abort's phase `allocAb`; a block or node
off the write abort's pcs: `blkW_ab`, `blkW_abG`, `nodeW_ab_si`, `nodeW_ab_st`, `nodeW_ab_ldop`; the labels
`labY`, `labT_eq_labY`),
`Spike.Test.A64Hello1AllocArena` (`scc_rt_alloc`'s states allow `W0`'s arena writes `allocArena`; nodes'
writes: `blkW_noWr`, `nodeW_noWr_si`, `nodeW_wr_st`, `nodeW_wr_ldop`, `hdr_addr`; `W0` with the arena
component given `w0_of_stA`, `arenaWr0_of_noWr`),
`Spike.Test.A64Hello1PlacedS` (`scc_rt_alloc`'s states place the setup frame under `rodata`'s
allocation `allocPlaced`: `wpRep_slot`, `framesPlaced_setup`, `placed_rdN`, `ctl_of_N`, `allocW_of_ctl`),
`Spike.Test.A64Hello1AllocCtr` (`scc_rt_alloc`'s states write the counter only at its add `allocCtr`;
`ctr_lt_heap`; off the marks' sites `allocPc`, `allocAbortW`, `blkW_pc`, `nodeW_pc`, `abortW_of_pcOff`),
`Spike.Test.A64Hello1AllocW0` (every node of `scc_rt_alloc` inside `W0` under `rodata`'s frame
`allocW0`, from the components; `q0_of_rdCtx`, the source's runs `allocRun`; in the context `CtxA`
`ctxA_of_at`, `allocW0A`),
`Spike.Lib.A64AbSt` (the abort phase kept at a node's states: `AbSt.ofLeaves`, `blkW_abSt`, the targets'
check off the write abort's pcs `blkAb`, `blkAb_sound`),
`Spike.Lib.A64AbortPhH` (the heap abort path's phase check `abortPhHeapOk`, the twin of `abortPhOk`),
`Spike.Lib.A64StubHA` (the heap abort path's `StubHW` inside `SFactsA` at a failing allocation's control:
`stubHW_sfactsA`, from `InstOk`, `abortPhHeapOk` and `HeapAbortObl` at the exit call), `Spike.Test.A64StubHA`,
`Spike.Lib.X64AbortPhH`, `Spike.Lib.X64StubHA`, `Spike.Test.X64StubHA` (their x86-64 twins),
`Spike.Lib.A64WriteAb`, `Spike.Lib.X64WriteAb` (the write abort path's phase `Ab` for `SFactsA`: `print`'s
refused `write` to `scc_rt_abort_write`, by pc and refusal data; `pc_of_ab`, `not_ab_of_pc`),
`Spike.Lib.A64AbortPhW` (the write abort path's phase check `abortPhWriteOk`), `Spike.Lib.A64StubWA` (the
write abort path's `StubWW` inside `SFactsA` with the phase `WriteAb.Ab` at the jump's control `RefCtl`:
`stubWW_sfactsA`, from `InstOk` and `abortPhWriteOk`), `Spike.Test.A64StubWA`, `Spike.Lib.X64AbortPhW`,
`Spike.Lib.X64StubWA`, `Spike.Test.X64StubWA` (their x86-64 twins),
`Spike.Lib.A64PrintAb`, `Spike.Lib.A64PrintCallAb` (`print` with the refusal's data, a `Refusal` of the bytes
left: `seg_printAb_ofW`, `print_call_segAbW`, `print_call_abort_segAbW`), `Spike.Test.A64PrintAb`,
`Spike.Lib.X64PrintAb`, `Spike.Lib.X64PrintCallAb` (their x86-64 twins),
`Spike.Lib.MemSideBW` (a memory side with the output's byte step and abort justification set, `MemSide.withBW`;
rows and segments carry over: `Out.withBW`, `OutS.withBW`, `SegW.withBW`, `SegWS.withBW`),
`Spike.Lib.MemSideA` (rows away from a buffer allocation carry over to a memory side with the arena,
`NoNewBuf`, `Out.toA`, `OutS.toA`, `SegWS.toA`), `Spike.Lib.X64OutSA` (at `msOfS` to `msOfAX … ab`: the
shared fields, `outS_toAX`, `segWS_toAX`), `Spike.Lib.A64OutSA` (its AArch64 twin),
`Spike.Lib.A64ConsumerAB` (`msOfAB`: `msOfA` with `bo := ByteOut p lbl` and `we := WeAb abi Ab`, the write
abort phase; `Out.msOfAB`, `OutS.msOfAB`, `SegWS.msOfAB`, `refused_ab_of_emit`, `byteOut_emit_msOfAB`),
`Spike.Test.A64ConsumerAB`, `Spike.Lib.X64ConsumerAB` (its x86-64 twin),
`Spike.Lib.A64Hello1BodyAb` (`wc_main`'s body and `wc_main` through `print_callAbW`, `print`'s obligations
at `PrintAb`'s nodes: `hello1_wc_bodyAb_segW`, `hello1_wcAb_segW`), `Spike.Test.A64Hello1BodyAb`,
`Spike.Lib.X64Hello1BodyAb` (its x86-64 twin),
`Spike.Lib.ArenaInit` (the arena and the counter at load: the check `arenaInitOk`, `initVal_arena`,
`initVal_ctr`, `correctKA`'s `hz0` and `hc0`), `Spike.Test.A64ArenaHello1` (those premises on `hello1.w`'s
AArch64 layout: `ar_ok`, `sub`, `al`, `stat`, `z0`, `c0`),
`Spike.Lib.X64ConsumerS` (the one-thread consumer at any call depth on x86-64, as on branch `x64cs`),
`Spike.Lib.X64ConsumerA`, `Spike.Lib.X64ConsumerAMem`, `Spike.Lib.X64ConsumerASys`, `Spike.Lib.X64ConsumerAInstr`,
`Spike.Lib.X64ConsumerAStep`, `Spike.Lib.X64ConsumerACore`, `Spike.Lib.X64ConsumerACorrect` (the allocation-capable
consumer's x86-64 twin, name for name: `correctKOnA`, `correctKA`), `Spike.Test.X64ArenaHello1` (its arena
premises on `hello1.w`'s x86-64 layout),
`Spike.Lib.Rt.X64ArenaOfPlaceOK`, `Spike.Test.X64ArenaOfPlaceOK` (those premises at any layout passing `placeOKAt`:
the arena `arOf`, `arOf_ok`, `arOf_sub`, `arOf_al`, `arOf_z0`, `arOf_c0` given the counter's zero item `CtrZ`;
against `hello1.w`'s hand arena),
`Spike.Lib.Rt.X64CtrZOfEmitted`, `Spike.Test.X64CtrZOfEmitted` (`CtrZ` of every successful lowering's output
and of every output passing `placeOKAt`, at any sizes and label offsets: `ctrZ_ofEmitted`, `ctrZ_ofPlaceOK`),
`Spike.Lib.X64AllocPh`, `Spike.Test.X64AllocPhHello1` (`scc_rt_alloc`'s phase check `allocPhOk` at any sites,
phases and labels, for A7; `allocPhOk_congr`; `hello1.x` passes it),
`Spike.Lib.X64AllocAbOk`, `Spike.Test.X64AllocAbOkHello1` (`scc_rt_alloc`'s targets off the write abort's pcs,
`allocAbOk` at any labels, for A7; `allocAbOk_congr`; `hello1.x` passes it),
`Spike.Lib.X64AllocPhPlace` (`allocPhOk`, `allocAbOk` at the record of an output passing `placeOKAt`, from A7's
`tailOffC`: `tailPhOk_ofPlaceOK`, `allocPhOk_ofPlaceOK`, `allocAbOk_ofPlaceOK`),
`Spike.Lib.X64AllocG`, `Spike.Lib.X64AllocGSt` (`scc_rt_alloc`'s write steps at any layout passing `allocIn` and
`allocPhOk`: `allocArena`, `allocCtr`, `allocPc`, `allocAbortW`, `allocSt`),
`Spike.Lib.X64AllocGAb` (its states keep the write abort's phase at any layout also passing `allocAbOk`:
`allocAb`), `Spike.Test.X64AllocGHello1` (those at `hello1.x`'s instance give its hand statements),
`Spike.Lib.X64PrintPh`, `Spike.Test.X64PrintPhHello1` (`scc_rt_print`'s phase check `printPhOk` at any sites,
phases and labels; `printLabs`, `printPhOk_congr`; `hello1.x` passes it),
`Spike.Lib.X64PrintG` (`printPc`, `printNoWr`, `printSt`: `scc_rt_print`'s block states at any instance
passing `printIn`, `printPhOk`; the twin of `Spike.Lib.A64PrintG`),
`Spike.Lib.X64W0G`, `Spike.Test.X64W0GHello1` (the states before and after the allocation, `W0`/`W1` and
their `SFactsA`, at any layout, marks, owned words, take phase, write abort phase and arena; `hello1.x`'s by
`rfl`),
`Spike.Lib.X64ConsumerAStart`, `Spike.Test.X64ConsumerAStart` (that `Correct` at any source start with `StartOk`,
the twin of `Spike.Lib.A64ConsumerAStart`: `pre_loadA'`, `stepSimA'`, `correctKOnA'`, `correctKA'`, `correctKA_of'`),
`Spike.Lib.X64ConsumerAE`, `Spike.Lib.X64ConsumerAEStep`, `Spike.Lib.X64ConsumerAEStart` (the consumer through
`print`'s `write`, the twins of `Spike.Lib.A64ConsumerAE*`: `EmitA`, `EmitSA`, `RSAE`; `pre_emitA`, `emit_stepAE`,
`r_stepAE`; `stepSimAE`, `correctKOnAE`, `correctKAEmitE'`),
`Spike.Lib.X64EmitOfNodes` (the emit rows from the node obligations, the twin of `Spike.Lib.A64EmitOfNodes`:
`emitA_of_nodes`),
`Spike.Lib.X64KeepTP`, `Spike.Test.X64KeepTP` (the `%fs` base kept across a segment asking for no
`arch_prctl(ARCH_SET_FS)`, the twin of `Spike.Lib.A64KeepTP`: `NoSetFsAt`, `exec_tp`, `out_tp`, `SegW.keepTP`).
`Spike.Lib.TailDt` (closed tails of certification steps, ISA-free: `ClosedC`, `StepsTo`, `ClosedC.rel`, a
tail proved back to front), `Spike.Lib.Rt.A64StubDt` (an abort stub's write tail `StubDt`, for every stub,
closed under certification: `stubDt_closed`, `stubDt_of_at`), `Spike.Lib.Rt.A64BlkDt` (certification steps
inside covered code, off the transfer sites: `stepC_exec`, `blk_stepC`, `blk_stepC_mid`, `blk_stepC_last`,
`si_stepC`, `svc_stepC`, `Abs.svcRet`, `exit_stepC`); their x86-64 twins `Spike.Lib.Rt.X64StubDt` (`StubDt`,
`stubDt_closed`, `stubDt_of_at`, for every stub and argument block) and `Spike.Lib.Rt.X64BlkDt` (`stepC_exec`,
`stepC_tree`, `blk_stepC`, `blk_stepC_mid`, `blk_stepC_last`, `si_stepC`, `fi_stepC`, `syscall_stepC`,
`Abs.syscallRet`, `exit_stepC`); `Spike.Lib.Rt.X64TailDt` (a write tail's pieces on x86-64: `BlkSt`,
`blkSt_steps`, `blkSt_entry`, `SysSt`, `sysSt_steps`, `ExitSt`, `exitSt_closed`, `abs_enter`, `abs_leave`);
`Spike.Lib.Rt.X64PrintDt` (`scc_rt_print`'s write tail inside its frame on x86-64: `PrintIn`,
`printIn_steps`, `printIn_of_at`); `Spike.Lib.Rt.X64WcRa` (x86-64 twin of `Spike.Lib.Rt.A64WcRa`: a
return-address slot's value at offset 0 `WcRa`, a saved frame pointer's at `-8` `WcFp`);
`Spike.Lib.Rt.X64Hello1RetDt` (`hello1.w`'s x86-64 write tail after `print` returns: `cell_kept`,
`callerCells_stable`, `abs_leave_cells`, `Abs.add_rbp`, `Abs.drop_regs`, `CP`, `cp_stable`, `RetDt`,
`retDt_of_ret`, `retDt_closed`); `Spike.Lib.Rt.X64Hello1AbDt` (on `print`'s abort: `SiSt`, `siSt_steps`,
`stubDt_of_abs`, `AbIn`, `abIn_steps`, `abs_cells`, `aR`, `abIn_of_fail`); `Spike.Lib.Rt.X64Hello1PrintDt`
(`hello1.w`'s x86-64 write tail from `print`'s `write`: `PrintDt`, `printDt_closed`, `printDt_of_at`,
`printDt_closed_hello1`); `Spike.Lib.Rt.X64Hello1NoSite` (that tail off the transfer sites: `offSite`,
`blkOff`, `printOff`, `printDt_noSite`, `printDt_noSite_hello1`, `printDt_closed_μ0`; the x86-64 modules are built by the `Spike.*` glob, not imported here, their
syntax clashing with AArch64's),
`Spike.Lib.Rt.A64WcRa` (a return-address
slot's value: `WcRa`), `Spike.Lib.Rt.A64TailDt` (tail pieces over covered code, for any
executable and layout: `Pt`, `BlkSt`, `BlkEnd`, `blkSt_steps`, `svc_steps`, `exit_closed`, `pt_enter`,
`pt_leave`), `Spike.Lib.Rt.A64PrintDt` (`scc_rt_print`'s write tail inside its frame, for any executable:
`PrintIn`, `printIn_steps`, `printIn_of_at`), `Spike.Lib.A64TailPh` and `Spike.Test.A64TailPh` (the write
tail's phase check, `tailOffC`, A7-style, on `hello1.w`, with `Spike.Lib.A64AllocPh`'s `allocPhOk`),
`Spike.Lib.Rt.A64PrintNoSite` (no thread site inside the write tail: `printIn_noSite`,
`printIn_noSite_ofPlaceOK`), `Spike.Lib.Rt.A64AbDt` (the abort path from `scc_rt_abort`'s entry to a stub's
`write` call, for any executable and layout: `AbIn`, `abIn_steps`, `abIn_of_fail`),
`Spike.Lib.Rt.A64AbNoSite` (the abort path and the write/heap stubs' tails off the transfer sites:
`abIn_noSite_write`, `stubDt_noSite`, `stubDt_noSite_write_ofPlaceOK`, `abIn_noSite_write_ofPlaceOK`),
`Spike.Lib.Rt.A64FailDt` (the abort path's write tail closed: `AbDt`, `abDt_closed`, `abDt_noSite_write`),
`Spike.Lib.LowerA64.AbortPathW2` (`AbortPathS` from every pair's `W2`: `abortPathS_of_W2`),
`Spike.Lib.LowerA64.AbStart` (the loaded thread off the write abort, `hab0_ofPlaceOKE`),
`Spike.Lib.LowerA64.UserAb` (user blocks' states keep the write abort's phase: `PosOff`,
`not_ab_abortEntry`, `blkW_abSt_pos`),
`Spike.Lib.LowerA64.UserAbC` (the same from the code predicate off the write abort's labels: `CdCL`,
`blkW_abSt_subCdL`, `blkW_abSt_fallL`),
`Spike.Lib.LowerA64.FnCodeL` (an `Accepted2` function's code off the write abort's labels:
`fnCodeC2L_ofPlaceOK` at `CdCL`, `codeC2L_of_seg`, `blockLabel_not_abLabs`, `rtFuncs_length`),
`Spike.Lib.LowerA64.FnCodeLB` (the same with each call's `bl` at a position off the write abort:
`BlC2L`, `fnCodeC2LB_ofPlaceOK`; the x64 twin in `Spike/X64.lean`),
`Spike.Lib.LowerA64.CdCLE` (a piece of code followed by a position off the write abort unless it ends
with a `b` or a `ret`: `CdCLE`, `endJ`, `posOff_end_subCdLE`, `posOff_end_lane`),
`Spike.Lib.LowerA64.FnCodeLE` (an `Accepted2` function's code at `CdCLE`: `codeC2_cdCLE`,
`fnCodeC2LE_ofPlaceOK`),
`Spike.Lib.LowerA64.LevelMono2` (the nodes, `CalleeF2` and the frames' placement at a larger level:
`bodyN2_mono`, `pendN2_mono`, `abortN2_mono`, `csN2_mono`, `retCN2_mono`, `exN2_mono`, `CalleeF2.mono`,
`PlacedS.mono_lbl`, `FramesPlaced.mono_lbl`, `FramesPlacedInI.mono_lbl`; the x64 twin in `Spike/X64.lean`),
`Spike.Lib.LowerA64.StkMono2` (the suspended frames' records and the arena's memory side at a larger level:
`StkFrOk.mono_lbl`, `StkOk.mono_lbl`, `CxOkS.mono_lbl`, `Placed.mono_lbl`, `msOfAX_pl_mono_lbl`, `msOfAX_own_lbl`,
`msOfAX_rt_anti_lbl`; the x64 twin in `Spike/X64.lean`),
`Spike.Lib.LowerA64.Resume2` (a suspended caller resumed after its callee's segment, its state pinned at
the call site by `CallerAt2`: `retCN2_of_exit`, `callC2_resume`),
`Spike.Lib.LowerA64.ResumeStk2` (the running frame's segment resumed through its suspended frames' records
to the frame above the bottom ones: `StkFr.botKey`, `StkOk.bot_drop`, `ExitStk`, `ResumeCx2`, `resume_stk`; the x64
twin `Spike.Lib.LowerX64.ResumeStk2`, its exits at the key's rebased region `rbR k.R`),
`Spike.Lib.LowerA64.H1Of2` (the landings' segments at the placement extended by the landing's label, generic in
the world and the memory side: `nWords_of_elem2`, `BodyPtW.newBufP`, `segWS_of_points`, `landStk_seg`; the x64
twin `Spike.Lib.LowerX64.H1Of2`, `AllocW2At` and the allocator's region in the body's rebased region `rbR R`),
`Spike.Lib.LowerA64.H1InLandA` (`Closed2AtA`'s `H1InA` from the landings `LandStk` at the record, `landStk_seg`
at `W2R`/`MSR`: `LandStk.fam`, `ElA`, the open facts `H1OpenA`, `h1InA_ofLand`, `in2A_ofLand`; the x64 twin
`Spike.Lib.LowerX64.H1InLand`: `Closed2At`'s `H1In`, `ElX`, `H1OpenX`, `h1In_ofLand`, `in2X_ofLand`),
`Spike.Lib.LowerA64.AbortW2` (the abort exits inside `W2`: `ovf_hKR_take`, `ovf_hW_w2`, `stubON_w2`,
`stubHN_w2`, `w2_of_sfacts`, `w2_of_sfactsA`; the x64 twin in `Spike.Lib.LowerX64.AbortW2`),
`Spike.Lib.LowerA64.StubAbW2` (the abort paths' nodes keep the write abort's phase: `stubOAb`, `stubHAb`,
`ovf_hW_w2_fi`; the x64 twin in `Spike.Lib.LowerX64.StubAbW2`),
`Spike.Lib.LowerA64.AbortW2Ab` (the abort exits inside `W2` at the write abort's phase: `stubON_w2Ab`,
`stubHN_w2Ab`, and at the record of an output passing `placeOK`, `stubON_w2_ofPlaceOK`, `stubHN_w2_ofPlaceOK`;
the x64 twin in `Spike.Lib.LowerX64.AbortW2Ab`),
`Spike.Lib.LowerA64.MainAbA` (a user function's aborts never end, at the record of an output passing
`placeOK`: the write exit call's site premises `hrelW_ofPlaceOK` … `hmsW_ofPlaceOK`, `stubWN_w2_ofPlaceOK`,
`stubON_w2_ofPlaceOKw`, `stubHN_w2_ofPlaceOKw`, `ovfAb_seg`, `printAb_seg`, `MainAb`, `mainAb_seg`,
`abortN2_slotRepAt(_me)`; the x64 twin in `Spike.Lib.LowerX64.MainAbX`),
`Spike.Lib.LowerA64.HeapAbA` (a buffer allocation's heap abort exit never ends, at the record: `stubHN_nbAb`,
`heapAb_seg` at a call node `NbJcOf`),
`Spike.Lib.LowerA64.H1InLandWA` (`H1InLandA` at the start's frame condition `WordsNone ∧ rtF`: `H1OpenAW`,
`h1InAW_ofLand`, `in2AW_ofLand`; the x64 twin in `Spike.Lib.LowerX64.H1InLandW`),
`Spike.Lib.LowerA64.H1RestAW` (`H1RestA` at `WordsNone ∧ rtF`: `H1LandAW` (`hAW`, `hres`, `hbot`), `H1RestAW`
(and `hAbQ`), `H1RestAW.toOpen`),
`Spike.Lib.LowerA64.HeapAbSwA` (the same at a node of another world, its memory side and labels apart:
`stubHN_nbCoreX`, `stubHN_nbAbX`, `heapAb_segX`; the x64 twin in `Spike.Lib.LowerX64.HeapAbXS`),
`Spike.Lib.LowerA64.PrintAbP` (an abort of `print` landing with the caller's slots, `printNAS`, never ends,
the source control's facts discharged: `printAb_segP`; the x64 twin in `Spike.Lib.LowerX64.PrintAbP`),
`Spike.Lib.LowerA64.UserTgt` (the user code's direct branch targets decided: `tgtOkB`, `dTgt`, `tgOkQB`,
`tgOkB`, `posOff_of_tgtOkB`, `tgtOkB_of_tgOkQB`, `noBl_of_last`, `last_ret_noBl`, `noBl_kind2`, `hTg_of_tgOkQB`,
`hTg_of_tgOkB`: `cxBlk2_ofW2`'s `hTg` from the check),
`Spike.Lib.LowerA64.H1RestA` (`H1OpenA` at the contexts' aborts gathered, `GA`: its rest `H1RestA` (`hAW`,
`hres`, `hbot`, `hAbQ`), `H1RestA.toOpen` with the element types `hTn`, `hAb` by construction),
`Spike.Lib.Src.*` (the per-construct proof that an `Accepted2` program's source run keeps numbers in the
cells the output extern's loop loads, and its source safety, with no hook or WeakCore's output hook: the
lowering walk `LowerEnvImm2Of` … `NJLC`, the buffers `HeapMem`, `HeapLit`, `HeapBuf`, `SliceL`, `NJLB`,
the exchange cells `SrcB`, `NoAcq`, `SrcSafe2`, the numbers `SrcNumE`, `SrcNum`, `SrcNum2`:
`srcNumS_of_accepted2`, `srcNumS_hello1` at `Spike.Test.Hello1MainSrc.hello1o`, `printLd_loadC`, and
`SrcRdNum`: `srcRd_isNum`, the consumers' read side at `rd := IsNum`; `SrcNumStart`: the same from either
start of `progInit` (`invN_progInit`, `invN_reachP`, `srcNumS_of_accepted2P`, `srcRd_isNumP`);
`Spike.Lib.Src.NumQLower`:
`numQ_of_lowerIR`, `setupValWords_of_lowerIR`, their premises from a successful `lowerIR`, from `placeOKAt` in
`Spike.Lib.LowerA64.NumQOfPlaceOKA` and `Spike.Lib.LowerX64.NumQOfPlaceOK` (`numQ_of_placeOK`,
`setupValWords_of_placeOK`); the
consumers' `SrcNumS` and `SrcSafeS`: `Spike.Lib.Src.SrcNumWA`, `Spike.Lib.Src.SrcSafe2A`, and their x86-64
twins `Spike.Lib.Src.SrcNumWX`, `Spike.Lib.Src.SrcSafe2X`, imported by `Spike.X64`), `Spike.Lib.Src.Hello1Out`
(`stdout`; `hello1o_noExit`, `hello1o_noExit_hook`: no exit in `hello1o`'s hook trace under `UsesWc`),
`Spike.Lib.Src.Accepted2Out` (the same for any `Accepted2` program from `progInit`: `noExitOp_of_accepted2`,
`noExit_hook_of_accepted2`, `hookOK_srcP1o`; `progInit_of_setupOf_some`, `progInit_of_setupOf_none`),
`Spike.Lib.Src.SetupFrame`, `Spike.Lib.A64SetupPlaced` and its x86-64 twin `Spike.Lib.X64SetupPlaced` (imported
by `Spike.X64`) (the setup call's frame placed at any layout: `setupCont_fv`, `framesPlaced_me`,
`framesPlaced_setupCont`, `allocW_of_ctl`, `allocPlacedS`), `Spike.Lib.Src.ImmsMe` (the `Accepted2`
theorems' immediate table `imms2Me`: `imms2Of p` and the first TCB for `me` at the setup start; `imms2Me_setup`,
`imms2Me_of_ne`, `imms2Me_of_none`),
`Spike.Test.SrcNumA64`, `Spike.Test.SrcNumX64`.
-/
import Spike.Bridge.Progress
import Spike.Bridge.LoopCorrect
import Spike.Lib.Thread
import Spike.Lib.Region
import Spike.Lib.Mem
import Spike.Lib.Form
import Spike.Lib.FormE
import Spike.Bridge.CertC
import Spike.Lib.SrcMem
import Spike.Lib.Consumer1
import Spike.Lib.Typed
import Spike.Lib.Place
import Spike.Lib.RtRmw
import Spike.Lib.SegLag
import Spike.Lib.SegS
import Spike.Lib.FrameRunM
import Spike.Test.SegS
import Spike.Lib.SrcMemN
import Spike.Lib.SrcFrames
import Spike.Lib.HookOK
import Spike.Lib.AllocSrc
import Spike.Lib.AllocRow
import Spike.Lib.AllocInv
import Spike.Lib.FreshSrc
import Spike.Lib.HeapAbort
import Spike.Lib.A64ConsumerS
import Spike.Lib.A64RunPc
import Spike.Lib.A64PlacedS
import Spike.Lib.A64SegInstS
import Spike.Lib.A64CallS
import Spike.Lib.A64CallSA
import Spike.Lib.Rt.A64SegsS
import Spike.Lib.SegLagS
import Spike.Lib.SegLagSF
import Spike.Lib.SegLagSC
import Spike.Lib.SegGood1
import Spike.Lib.Frames1
import Spike.Lib.A64SFactsS1
import Spike.Lib.LowerA64.StartSegS
import Spike.Lib.LowerA64.UPostS
import Spike.Lib.LowerA64.MovImm
import Spike.Lib.LowerA64.Checks
import Spike.Lib.LowerA64.Construct
import Spike.Lib.LowerA64.Construct1
import Spike.Lib.LowerA64.Node
import Spike.Lib.LowerA64.Node1
import Spike.Lib.LowerA64.Body1
import Spike.Lib.LowerA64.Body
import Spike.Lib.LowerA64.Prologue
import Spike.Lib.LowerA64.ProIn
import Spike.Lib.LowerA64.BodyIn
import Spike.Lib.LowerA64.Fn
import Spike.Lib.LowerA64.Main
import Spike.Lib.LowerA64.MainCode
import Spike.Lib.LowerA64.BodyW
import Spike.Lib.Quiet0
import Spike.Lib.Quiet1
import Spike.Lib.LowerA64.UserW
import Spike.Lib.LowerA64.UserCall
import Spike.Lib.LowerA64.AbortCall
import Spike.Lib.LowerA64.StartU
import Spike.Lib.LowerA64.AbortOfPlaceOK
import Spike.Lib.LowerA64.StartSeg
import Spike.Lib.LowerA64.OvfCode
import Spike.Lib.LowerA64.OvfDt
import Spike.Lib.LowerA64.PhCheck
import Spike.Lib.LowerA64.PhOfPlaceOK
import Spike.Lib.LowerA64.MainPh
import Spike.Lib.SrcP1
import Spike.Lib.Accepted0Src
import Spike.Lib.A64Accepted0Safe
import Spike.Lib.Accepted1Src
import Spike.Lib.A64Accepted1Safe
import Spike.Lib.Accepted1NoMem
import Spike.Lib.DepthFactsS
import Spike.Lib.Rt.A64EntryOfPlaceOK
import Spike.Lib.LowerA64.Correct
import Spike.Lib.LowerNode
import Spike.Lib.LowerNode1
import Spike.Lib.LowerEnvImm1
import Spike.Lib.LowerEnvImm
import Spike.Lib.LowerEnvImm1Of
import Spike.Lib.LowerEnvImmAgree
import Spike.Lib.ImmsMono
import Spike.Lib.ImmsMonoA64
import Spike.Lib.LowerAddChk1
import Spike.Lib.LowerEnvImmC1Of
import Spike.Lib.LowerCallOrder
import Spike.Lib.LowerProgC1
import Spike.Lib.SlotOrder
import Spike.Lib.SlotOrderC1
import Spike.Lib.SlotOrderA64
import Spike.Lib.LowerShapeC1
import Spike.Lib.LowerShapeC2
import Spike.Lib.LowerShapeC2Walk
import Spike.Lib.LowerShapeC2Shape
import Spike.Lib.LowerShapeC2Some
import Spike.Lib.LowerProgC2Core
import Spike.Lib.LowerSetupRet
import Spike.Lib.LowerProgC2
import Spike.Test.LowerProgC2Test
import Spike.Test.LowerShapeC2Test
import Spike.Lib.LowerCallC1
import Spike.Lib.Proto.D2Imms
import Spike.Lib.A64Hello1BodyA
import Spike.Lib.A64Hello1PrintLen
import Spike.Lib.A64PrintA
import Spike.Lib.A64PrintEmit
import Spike.Lib.PrintSvc
import Spike.Lib.A64PrintCall
import Spike.Lib.SegWOfNot
import Spike.Lib.A64PrintEmpty
import Spike.Lib.A64PrintTP
import Spike.Test.A64PrintTP
import Spike.Lib.A64Hello1PrintAt
import Spike.Lib.EmitByte
import Spike.Lib.LowerA64.TailBare
import Spike.Lib.LowerA64.TailBare1
import Spike.Lib.LowerA64.MainCode1
import Spike.Lib.LowerA64.Blocks1
import Spike.Lib.LowerA64.CallSite1
import Spike.Lib.LowerA64.SetupOfPlaceOK
import Spike.Lib.ArenaBound
import Spike.Lib.LowerA64.ArenaOfPlaceOK
import Spike.Lib.LowerA64.BlocksC1
import Spike.Lib.LowerA64.BlocksC1Code
import Spike.Lib.LowerCallee1
import Spike.Lib.LowerA64.CalleeRow
import Spike.Lib.LowerA64.UserInj
import Spike.Lib.DmemPriv
import Spike.Lib.A64DmemPriv
import Spike.Lib.A64DmemPrivPlace
import Spike.Lib.A64WordsNone
import Spike.Lib.RegionCells
import Spike.Lib.Rt.A64SegsF
import Spike.Lib.Rt.A64RtStartUF
import Spike.Lib.Rt.A64SwWordsNone
import Spike.Lib.LowerA64.StartUF
import Spike.Lib.LowerA64.StartSeg1WN
import Spike.Lib.LowerA64.BodyW1
import Spike.Lib.LowerA64.BodyWS1
import Spike.Lib.LowerA64.NodeTp
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.LowerA64.CallSite
import Spike.Lib.LowerA64.Fn1
import Spike.Lib.LowerA64.UserCall1
import Spike.Lib.LowerA64.StartSeg1
import Spike.Lib.LowerA64.StartSeg1WN
import Spike.Lib.Rt.A64SegsF
import Spike.Lib.Rt.A64RtStartUF
import Spike.Lib.LowerA64.StartUF
import Spike.Lib.A64DmemPrivPlace
import Spike.Lib.LowerA64.Correct1WN
import Spike.Test.A64Correct1WN
import Spike.Lib.LowerA64.Correct1
import Spike.Lib.LowerA64.Correct1WN
import Spike.Lib.RtHeadroomA64
import Spike.Lib.RtDepthA64
import Spike.Lib.RtMainMem
import Spike.Lib.LowerA64.MainNeed
import Spike.Lib.Rt.A64CodeInSetup
import Spike.Lib.Rt.A64RtCodeSetup
import Spike.Lib.Rt.A64MainS
import Spike.Lib.Rt.A64MainSS
import Spike.Lib.AllocSrc
import Spike.Lib.LaneStoreSrc
import Spike.Lib.AllocRow
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.A64Hello1RodataS
import Spike.Lib.A64Hello1RodataPostS
import Spike.Lib.A64KeepTP
import Spike.Lib.A64Hello1RodataTP
import Spike.Lib.A64AbortHeapW
import Spike.Lib.A64Hello1RodataSetup
import Spike.Lib.A64Hello1RodataXa
import Spike.Lib.Hello1RodataMem
import Spike.Lib.AllocInv
import Spike.Lib.A64LaneStore
import Spike.Lib.A64Hello1LaneStoreReg
import Spike.Lib.A64NewBuf
import Spike.Lib.HeapAbort
import Spike.Lib.A64HeapAbort
import Spike.Lib.A64SetupW
import Spike.Lib.A64Hello1RodataSetupG
import Spike.Lib.A64AllocS
import Spike.Lib.A64AbortHeapS
import Spike.Lib.FreshSrc
import Spike.Lib.HeapObl
import Spike.Lib.A64HeapObl
import Spike.Lib.LowerA64.PrintArgs
import Spike.Test.LowerA64PrintArgs
import Spike.Lib.LowerA64.PrintCall
import Spike.Lib.A64AbortWriteW
import Spike.Lib.A64RtAbortSeg
import Spike.Lib.A64AbortStubCode
import Spike.Test.A64RtAbortSeg
import Spike.Lib.HeapPresCore
import Spike.Lib.HeapLand
import Spike.Lib.Arena
import Spike.Lib.A64ConsumerA
import Spike.Lib.A64CtrRow
import Spike.Lib.CtrRows
import Spike.Lib.A64ConsumerAMem
import Spike.Lib.A64ConsumerASys
import Spike.Lib.A64ConsumerAInstr
import Spike.Lib.A64ConsumerAStep
import Spike.Lib.A64ConsumerACore
import Spike.Lib.A64ConsumerACorrect
import Spike.Lib.A64ConsumerAStart
import Spike.Lib.ArenaInit
import Spike.Test.A64ArenaHello1
import Spike.Lib.A64ConsumerAWr
import Spike.Lib.ZeroTy
import Spike.Lib.A64SegInstA
import Spike.Lib.AllocReach
import Spike.Lib.AllocLandOf
import Spike.Lib.A64SegInstN
import Spike.Lib.AllocReachRoom
import Spike.Lib.A64SFactsA
import Spike.Test.A64Hello1Load
import Spike.Test.A64Hello1CorrectA
import Spike.Test.A64Hello1StartA
import Spike.Lib.A64Hello1SetupPre
import Spike.Lib.A64Hello1SetupPost
import Spike.Lib.Rt.A64StartE
import Spike.Test.A64Hello1StartE
import Spike.Lib.A64Hello1SetupGlue
import Spike.Test.A64Hello1SetupChain
import Spike.Lib.A64AbortWriteW
import Spike.Lib.A64AbortStubCode
import Spike.Lib.A64Hello1SetupTail
import Spike.Lib.A64Hello1Levels
import Spike.Test.A64Hello1LevelsA
import Spike.Lib.A64Hello1SFactsN
import Spike.Test.A64Hello1SFactsN
import Spike.Test.A64Hello1LevelsB
import Spike.Test.A64Hello1RtW
import Spike.Lib.Hello1Runs
import Spike.Test.A64Hello1W0
import Spike.Test.A64Hello1Gfp
import Spike.Test.A64Hello1Ctr
import Spike.Test.A64Hello1W0N
import Spike.Test.A64Hello1AllocW
import Spike.Test.A64Hello1AllocAb
import Spike.Test.A64Hello1AllocArena
import Spike.Test.A64Hello1PlacedS
import Spike.Test.A64Hello1AllocCtr
import Spike.Test.A64Hello1AllocW0
import Spike.Lib.A64AbSt
import Spike.Lib.A64AbortPhH
import Spike.Lib.A64StubHA
import Spike.Test.A64StubHA
import Spike.Lib.A64WriteAb
import Spike.Lib.A64AbortPhW
import Spike.Lib.A64StubWA
import Spike.Test.A64StubWA
import Spike.Lib.A64PrintAb
import Spike.Lib.A64PrintCallAb
import Spike.Test.A64PrintAb
import Spike.Lib.MemSideBW
import Spike.Lib.MemSideA
import Spike.Lib.A64OutSA
import Spike.Lib.A64ConsumerAB
import Spike.Test.A64ConsumerAB
import Spike.Lib.ByteOutLd
import Spike.Lib.A64ConsumerAE
import Spike.Lib.A64ConsumerAEStep
import Spike.Lib.A64ConsumerAEStart
import Spike.Lib.A64ConsumerAEComp
import Spike.Lib.PrintSvcRun
import Spike.Lib.A64EmitOfNodes
import Spike.Lib.PrintTopExt
import Spike.Lib.A64PlacedSE
import Spike.Lib.LowerA64.PrintPlacedSE
import Spike.Lib.LowerA64.PrintWEW2
import Spike.Lib.LowerA64.PrintWBW2
import Spike.Lib.WriteDead
import Spike.Lib.A64WriteDead
import Spike.Lib.A64ConsumerAEPrint
import Spike.Lib.A64ConsumerAW
import Spike.Lib.Hello1Runs
import Spike.Lib.A64Hello1BodyAb
import Spike.Test.A64Hello1BodyAb
import Spike.Lib.Src.AbortImm2
import Spike.Lib.Src.LitPt2
import Spike.Lib.Src.Accepted2Out
import Spike.Lib.Src.SetupFrame
import Spike.Lib.A64SetupPlaced
import Spike.Lib.Src.ExternUnit
import Spike.Lib.Src.GroupAlg
import Spike.Lib.Src.GroupShape
import Spike.Lib.Src.HeapBuf
import Spike.Lib.Src.Hello1Out
import Spike.Lib.Src.HeapLit
import Spike.Lib.Src.HeapMem
import Spike.Lib.Src.ImmIn
import Spike.Lib.Src.ImmIn2
import Spike.Lib.Src.ImmsMe
import Spike.Lib.Src.LowerEnvImm2Of
import Spike.Lib.Src.LowerMarks2
import Spike.Lib.Src.LowerMarksImm2
import Spike.Lib.Src.NJ2
import Spike.Lib.Src.NJ2Srun
import Spike.Lib.Src.NJ3
import Spike.Lib.Src.NJL
import Spike.Lib.Src.NJLB
import Spike.Lib.Src.NJBXchg2
import Spike.Lib.Src.XchgB
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.XchgSiteB
import Spike.Lib.Src.PrintCallSrc
import Spike.Lib.Src.PrintSite
import Spike.Lib.Src.NJLB2
import Spike.Lib.Src.EnvBGhost
import Spike.Lib.Src.NJBNewBuf
import Spike.Lib.Src.NodeJEMono
import Spike.Lib.Src.LevelMono2
import Spike.Lib.Src.NJLBEnv2
import Spike.Lib.Src.NJLBS
import Spike.Lib.Src.NJLC
import Spike.Lib.Src.NJLS
import Spike.Lib.Src.NJLW
import Spike.Lib.Src.NoAcq
import Spike.Lib.Src.RunOk2
import Spike.Lib.Src.SliceL
import Spike.Lib.Src.SrcB
import Spike.Lib.Src.SrcNum
import Spike.Lib.Src.SrcNum2
import Spike.Lib.Src.SrcRdNum
import Spike.Lib.Src.SrcNumStart
import Spike.Lib.Src.NumQLower
import Spike.Lib.Src.LblRoomOf
import Spike.Test.SetupNoLoc
import Spike.Test.MainRetOk
import Spike.Lib.Src.SrcNumE
import Spike.Lib.Src.SrcNumWA
import Spike.Lib.Src.SrcSafe2
import Spike.Lib.Src.SrcSafe2A
import Spike.Lib.Src.SstepLet
import Spike.Lib.Src.Walk21
import Spike.Lib.Src.XchgLeaf
import Spike.Test.SrcNumA64
import Spike.Lib.TailDt
import Spike.Lib.Rt.A64StubDt
import Spike.Lib.Rt.A64BlkDt
import Spike.Lib.Rt.A64WcRa
import Spike.Lib.Rt.A64TailDt
import Spike.Lib.Rt.A64PrintDt
import Spike.Lib.A64TailPh
import Spike.Test.A64TailPh
import Spike.Lib.Rt.A64PrintNoSite
import Spike.Lib.Rt.A64AbDt
import Spike.Lib.Rt.A64AbNoSite
import Spike.Lib.Hello1oRuns
import Spike.Test.Hello1oRuns
import Spike.Lib.Rt.A64ArenaOfPlaceOK
import Spike.Test.A64ArenaOfPlaceOK
import Spike.Lib.Rt.CtrZSecs
import Spike.Lib.Rt.A64CtrZOfEmitted
import Spike.Test.A64CtrZOfEmitted
import Spike.Lib.A64W0G
import Spike.Lib.A64AllocPh
import Spike.Lib.A64AllocG
import Spike.Lib.A64AllocGSt
import Spike.Lib.A64AllocAbOk
import Spike.Lib.A64AllocGAb
import Spike.Lib.A64PrintG
import Spike.Lib.A64PrintGAb
import Spike.Lib.A64PrintGSvc
import Spike.Test.A64AllocGHello1
import Spike.Lib.LowerA64.BlocksC2Code
import Spike.Lib.LowerA64.Node2
import Spike.Lib.LowerA64.Body2
import Spike.Lib.LowerA64.Node2Edges
import Spike.Lib.LowerA64.RetS
import Spike.Lib.LowerA64.Body2SegX
import Spike.Lib.LowerA64.RetSL
import Spike.Lib.LowerA64.Body2Seg
import Spike.Test.LowerA64Body2
import Spike.Lib.LowerA64.Entry2
import Spike.Lib.A64XchgSeg
import Spike.Lib.LowerA64.XchgOff
import Spike.Lib.LowerA64.LaneSeg
import Spike.Lib.LowerA64.LaneC2
import Spike.Lib.LowerA64.NewBufC2
import Spike.Lib.LowerA64.PrintCallC2
import Spike.Lib.LowerA64.Body2SegOf
import Spike.Lib.LowerA64.Body2Arms
import Spike.Lib.LowerA64.BlocksC2Seg
import Spike.Lib.LowerA64.Closed2OfA
import Spike.Lib.LowerA64.Closed2AtA
import Spike.Lib.LowerA64.Closed2AtWA
import Spike.Lib.LowerA64.H0InSetupA
import Spike.Lib.LowerA64.SetupTailOfA
import Spike.Lib.LowerA64.StkOfA
import Spike.Lib.LowerA64.H0InAssembledA
import Spike.Lib.MainCompiled2
import Spike.Lib.LowerA64.SetupCodeOf
import Spike.Lib.LowerA64.PostSOf
import Spike.Lib.LowerA64.H0InAssembledCA
import Spike.Lib.LowerA64.RtMainXVA
import Spike.Lib.LowerA64.RtMainXVLA
import Spike.Lib.LowerA64.H0InAssembledVA
import Spike.Lib.LowerA64.H1InNoneA
import Spike.Lib.LowerA64.RtMainXRL
import Spike.Lib.LowerA64.MainCallOf
import Spike.Lib.LowerA64.MainHeldA
import Spike.Lib.LowerA64.HeldPostA
import Spike.Lib.LowerA64.HeldPostAV
import Spike.Lib.LowerA64.VacC2
import Spike.Lib.LowerA64.AllocW2W2
import Spike.Lib.LowerA64.AllocFnW2
import Spike.Lib.A64AllocTail
import Spike.Lib.LowerA64.AllocTailW2
import Spike.Lib.LowerA64.AllocHeldW2
import Spike.Lib.LowerA64.AllocFieldW2
import Spike.Lib.LowerA64.AllocW2Full
import Spike.Lib.LowerA64.AllocW2AtOf
import Spike.Lib.LowerA64.ArCallMs
import Spike.Lib.LowerA64.StackBounds2A
import Spike.Lib.LowerA64.SetupSwA12A
import Spike.Lib.LowerA64.PinnedTcbA
import Spike.Lib.LowerA64.HproSetupPA
import Spike.Lib.LowerA64.SetupCallB2
import Spike.Lib.LowerA64.SetupBot
import Spike.Lib.LowerA64.SetupBotM
import Spike.Lib.LowerA64.HSAssembledA
import Spike.Lib.LowerA64.Start2C0A
import Spike.Lib.LowerA64.H0InAssembledSA
import Spike.Lib.LowerA64.H0InAssembledBA
import Spike.Lib.LowerA64.NumQOfPlaceOKA
import Spike.Lib.LowerA64.SFactsA2
import Spike.Lib.LowerA64.W2Blk
import Spike.Lib.LowerA64.RtW2
import Spike.Lib.LowerA64.RtStartX
import Spike.Lib.LowerA64.RtStartXOf
import Spike.Lib.LowerA64.StartEW2
import Spike.Lib.SlotRepAt
import Spike.Lib.SlotRepNone
import Spike.Lib.A64PlacedSlot
import Spike.Lib.LowerA64.PlacedBlk
import Spike.Lib.LowerA64.W2Body
import Spike.Lib.LowerA64.PrintW2
import Spike.Lib.LowerA64.PrintArgW2
import Spike.Lib.LowerA64.PrintCallW2
import Spike.Lib.LowerA64.PrintAbW2
import Spike.Lib.LowerA64.HN2
import Spike.Lib.LowerA64.Levels2
import Spike.Lib.LowerA64.NoSlotWr
import Spike.Lib.Src.RetB
import Spike.Lib.LowerA64.RetNB
import Spike.Lib.LowerA64.CallC2
import Spike.Lib.LowerA64.CtxC2
import Spike.Lib.LowerA64.PrintFramesJ
import Spike.Lib.LowerA64.AllocRa
import Spike.Lib.LowerA64.PrintCallOkF
import Spike.Lib.LowerA64.FnCode2Of
import Spike.Lib.LowerA64.ProgC2
import Spike.Lib.Src.CallOrder2
import Spike.Lib.Src.AddFree
import Spike.Lib.Src.HeldLit2
import Spike.Lib.LowerA64.HordC2
import Spike.Lib.Src.ParamsNodup
import Spike.Lib.LowerA64.ProEdge2Of
import Spike.Lib.Src.Entry2
import Spike.Lib.Src.Entry2U
import Spike.Lib.LowerA64.ProEdge2Callee
import Spike.Lib.LowerA64.LimOk0
import Spike.Lib.Src.Walk2Facts
import Spike.Lib.Src.ContNR
import Spike.Lib.LowerA64.FnCode2Build
import Spike.Lib.LowerA64.BodyPt2
import Spike.Lib.Src.Stk2
import Spike.Lib.LowerA64.Stk2
import Spike.Lib.LowerA64.LimLvl2
import Spike.Lib.LowerA64.LandStk2
import Spike.Lib.LowerA64.MainExit2
import Spike.Lib.LowerA64.MainCall2
import Spike.Lib.LowerA64.AbortSeg2
import Spike.Lib.LowerA64.UserInj2
import Spike.Lib.Src.GroupOpds
import Spike.Lib.Rt.A64FailDt
import Spike.Lib.LowerA64.AbortPathW2
import Spike.Lib.LowerA64.AbStart
import Spike.Lib.LowerA64.Start2Facts
import Spike.Lib.LowerA64.Rest2OfA
import Spike.Lib.LowerA64.HeldTail
import Spike.Lib.LowerA64.HeldTailExit
import Spike.Lib.LowerA64.RetSFacts2
import Spike.Lib.LowerA64.Kind2SFacts
import Spike.Lib.LowerA64.CxBlk2Of
import Spike.Lib.LowerA64.HeldTailRet
import Spike.Lib.LowerA64.UserAbR
import Spike.Lib.LowerA64.MainRetPos
import Spike.Lib.LowerA64.Body2SegHF
import Spike.Lib.LowerA64.HeldTailSlot
import Spike.Lib.LowerA64.RetHeldW
import Spike.Lib.LowerA64.RetHeldAb
import Spike.Lib.LowerA64.HeldRes
import Spike.Lib.LowerA64.MainTailA
import Spike.Lib.LowerA64.MainTailP
import Spike.Lib.Src.LblRange
import Spike.Lib.Src.LblBelow32
import Spike.Lib.LblArena
import Spike.Lib.LblRangeReach
import Spike.Lib.LowerA64.HeapW
import Spike.Lib.LowerA64.LaneW2
import Spike.Lib.LowerA64.LaneCW2
import Spike.Lib.LowerA64.UserAb
import Spike.Lib.Src.Walk2Of
import Spike.Lib.LowerA64.Walk2Of
import Spike.Test.Walk2Of
import Spike.Lib.LowerA64.UserAbC
import Spike.Lib.LowerA64.FnCodeL
import Spike.Lib.LowerA64.FnCodeLB
import Spike.Lib.LowerA64.CdCLE
import Spike.Lib.LowerA64.FnCodeLE
import Spike.Lib.LowerA64.LevelMono2
import Spike.Lib.LowerA64.StkMono2
import Spike.Lib.LowerA64.Resume2
import Spike.Lib.LowerA64.ResumeStk2
import Spike.Lib.LowerA64.H1Of2
import Spike.Lib.LowerA64.H1InLandA
import Spike.Lib.LowerA64.AbortW2
import Spike.Lib.Rt.A64ExitF
import Spike.Lib.LowerA64.Start2W2
import Spike.Lib.Rt.A64RtMainS
import Spike.Lib.LowerA64.RtMainX
import Spike.Lib.A64CallSF
import Spike.Lib.Rt.A64MainSSF
import Spike.Lib.Rt.A64MainSSB
import Spike.Lib.Rt.A64MainS0
import Spike.Lib.Rt.A64StartEF
import Spike.Lib.Rt.A64MainSSBF
import Spike.Lib.LowerA64.MainExitF
import Spike.Lib.LowerA64.MainBot
import Spike.Lib.LowerA64.SetupHCall
import Spike.Lib.LowerA64.SetupCall2
import Spike.Lib.LowerA64.SetupCallC2
import Spike.Lib.LowerA64.PlacedSPostC
import Spike.Lib.LowerA64.HPlSOfSPostC
import Spike.Lib.LowerA64.RtMainXF
import Spike.Lib.LowerA64.SetupProOf
import Spike.Lib.SetupRodata
import Spike.Lib.LowerA64.StubAbW2
import Spike.Lib.LowerA64.AbortW2Ab
import Spike.Lib.LowerA64.MainAbA
import Spike.Lib.LowerA64.HeapAbA
import Spike.Lib.LowerA64.HeapAbSwA
import Spike.Lib.LowerA64.H1InLandWA
import Spike.Lib.LowerA64.H1RestAW
import Spike.Lib.LowerA64.PrintAbP
import Spike.Lib.LowerA64.UserTgt
import Spike.Lib.LowerA64.H1RestA
import Spike.Lib.Rt.A64RtWR
import Spike.Lib.LowerA64.RtMainXR
import Spike.Lib.LowerA64.RtMainXRB
import Spike.Lib.LowerA64.RtMainXNB
import Spike.Lib.LowerA64.H0InSetupBA
import Spike.Lib.LowerA64.H0InAssembledCBA
import Spike.Lib.LowerA64.RtMainXVBA
import Spike.Lib.LowerA64.H0InSetupVBA
import Spike.Lib.LowerA64.H0InAssembledCVBA
import Spike.Lib.LowerA64.H0InAssembledBVBA
import Spike.Lib.LowerA64.RtMainXNBF
import Spike.Lib.LowerA64.RtMainXVBF
import Spike.Lib.LowerA64.H0InSetupVBAF
import Spike.Lib.LowerA64.H0InAssembledCVBAF
import Spike.Lib.LowerA64.H0InAssembledBVBAF
import Spike.Lib.LowerA64.HSAssembledBA
import Spike.Test.A64Hello1HS
import Spike.Test.A64Hello1HsOf
import Spike.Lib.LowerA64.FramesPlacedSetup
import Spike.Test.A64Hello1CxLBOf
import Spike.Test.A64Hello1CxOkH
import Spike.Test.A64Hello1CxLBH
import Spike.Test.A64Hello1SetupOpenOfH
import Spike.Lib.LowerA64.ResumeCxLBP
import Spike.Lib.LowerA64.MainS0L
import Spike.Test.A64Hello1BotRes
import Spike.Test.A64Hello1HBot
import Spike.Test.A64Hello1ResL
import Spike.Test.A64Hello1SetupAb
import Spike.Lib.LowerA64.FnSpecLaneBuf2
import Spike.Lib.LowerA64.CxLB
import Spike.Lib.Src.ImmsMeTail
import Spike.Lib.LowerA64.FnCode2Me
import Spike.Lib.LowerA64.CxLBP
import Spike.Lib.LowerA64.ResumeCxLB
import Spike.Test.A64Hello1NoCall
import Spike.Test.Hello1MainFacts
import Spike.Test.A64Hello1ClosedBVB
import Spike.Test.A64Hello1Final
import Spike.Test.A64Hello1HU
import Spike.Test.A64Hello1HUL
import Spike.Test.A64Hello1Print
import Spike.Test.A64Hello1PrintL
import Spike.Test.A64Hello1Main
import Spike.Test.A64Hello1MainL
import Spike.Test.A64Hello1HUFL
import Spike.Test.A64Hello1TgOk
import Spike.Test.A64Hello1HUF
import Spike.Test.A64Hello1ClosedBVBF
import Spike.Test.A64Hello1H1Of
import Spike.Test.A64Hello1HabA
import Spike.Test.A64Hello1HAbQ
import Spike.Test.A64Hello1HolesW
import Spike.Lib.LowerA64.ResumeCx2T
import Spike.Lib.LowerA64.H1LandAWT
import Spike.Lib.LowerA64.NbNone
import Spike.Test.A64Hello1ResI
import Spike.Test.A64Hello1H1T
import Spike.Test.A64Hello1FinalT
import Spike.Test.A64Hello1FinalO
import Spike.Test.A64Hello1HAW
import Spike.Test.A64Hello1SetupOpenOf
import Spike.Test.A64Hello1SetupOpenOfF
import Spike.Test.A64Hello1Reduce
import Spike.Test.A64Hello1Bounds
import Spike.Lib.LowerA64.ProEdge2UN0
import Spike.Lib.Src.SliceGhost
import Spike.Lib.Src.Entry2M
import Spike.Lib.LowerA64.ProEdge2UNM
import Spike.Lib.LowerA64.RtMainXN
import Spike.Lib.LowerA64.CalleeRgn2
import Spike.Lib.LowerA64.RaMain2
import Spike.Lib.LowerA64.ProW2
import Spike.Lib.LowerA64.HproOf
import Spike.Lib.LowerA64.LandHu
import Spike.Lib.Rt.A64MarshalTake
import Spike.Lib.SetupWords2
import Spike.Lib.LowerA64.SetupSw
import Spike.Lib.LowerA64.HeldC
import Spike.Lib.LowerA64.LagC2
import Spike.Lib.LowerA64.PrintCallC2H
import Spike.Lib.LowerA64.PrintCallInst
import Spike.Lib.LowerA64.PrintCallInstJ
import Spike.Lib.LowerA64.PrintStepK
import Spike.Lib.LowerA64.PrintCallInstA
import Spike.Lib.LowerA64.PrintCallInstAI
import Spike.Lib.A64CallSAH
import Spike.Lib.LowerA64.CallC2H
import Spike.Lib.LowerA64.W2Pop
import Spike.Lib.LowerA64.SetupBotPop
import Spike.Lib.LowerA64.PlacedRetJS
import Spike.Test.A64Hello1HWBot
import Spike.Test.A64Hello1AllocPt
import Spike.Test.A64Hello1AllocPtH

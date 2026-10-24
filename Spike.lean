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
`Spike.Lib.LowerA64.BodyW` (a lowered body's blocks inside `SFacts`: `fn0_seg`'s `hWb`/`hWs`, `bodyPhOk`),
`Spike.Test.LowerA64BodyW`, `Spike.Lib.Quiet0` (an `Accepted0` start's controls are `Quiet`: `hQ`),
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
`Spike.Test.Hello1LinkedA64` (`hello1.w`, uncertified, at its `ld.lld` executable: placement only, A1–A9 and
`codeFills` hold and A11 fails there, so `placeOKAt` is false; A2 refuses a `.rodata` label named like a code label
below the code, `noClash`),
`Spike.Test.A64SccNegative`, `Spike.Test.X64SccNegative` (release checks at `ret0`'s certificate: the theorem's
layout loads the listing and its run exits 42; the listing with `40` made `41` parses to the corrupted program, which
fails A9, so `placeOK` is false; `Spike/Gen/drift.sh` checks the generated files against scc's output),
`Spike.Test.A64CorrectE`, `Spike.Test.X64CorrectE` (`Scc.Sem.Entry.Ok`, the release statement's entry condition
(`Scc/Sem/CorrectE.lean`), decided at `ret0`'s layout: the witness stack and `Entry.linux` pass, misaligned,
small, high and overlapping stacks fail),
`Spike.Lib.A64Place`,
`Spike.Lib.A64AllocNodes`,
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
`Spike.Test.A64Ret0PlaceOK` (`ret0.w`'s and `hello1.w`'s code checks from one `Scc.Cert.PlaceOK.A64.placeOK`),
`Spike.Lib.Rt.A64LayoutOfPlaceOK` (the runtime's layout of an output passing `placeOKAt` at a layout `Λ`,
from `Scc.Cert.PlaceOK.A64.atTables` at the tables' layout; `ret0.w`'s against
the hand one),
`Spike.Test.A64Ret0CorrectP` (`ret0.w`'s `Correct` through `correctA64P'`, without `PromShared`),
`Spike.Lib.A64PhasesOfPlaceOK` (the blocks' phase checks `blkPh` from `placeOK`'s A6),
`Spike.Test.A64Ret0PhasesPlaceOK` (`ret0.w`'s and `hello1.w`'s phases and sites from A6 against the hand ones),
`Spike.Lib.Rt.A64CodeIn` (the runtime's code groups over copies of the hand blocks, light, and `rtCodeOk`),
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
`Spike.Lib.X64Alloc` (the allocator `scc_rt_alloc` as one segment),
`Spike.Lib.X64Typed`, `Spike.Lib.X64Ext`, `Spike.Lib.X64Consumer`, `Spike.Lib.X64Correct` (`Correct`
for a one-thread program on the x86-64 `canonical 1` from node obligations),
`Spike.Lib.X64PromShared`, `Spike.Lib.X64CorrectP` (the same with `PromShared` discharged),
`Spike.Lib.X64CorrectNW` (and `WriteNoProm` from `NoWrite`), `Spike.Lib.X64TailNoFul` (the same from a closed tail),
`Spike.Lib.X64AbortW` (the overflow abort path inside `W`: the `.ovf` block, the dispatcher at code 1, the stub),
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
`Spike.Test.X64RtCode` (them on `ret0.w`, against the hand ones; a wrong frame and `hello1.w`'s `scc_rt_main` fail),
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
`Spike.Lib.Rt.X64RtPhTab`, `Spike.Lib.Rt.X64RtPhOfTab` (a checked fact in the hand proofs' form),
`Spike.Test.X64RtPhTab` (the runtime's phase facts as a decided table,
`Scc.Cert.Rt.RtPhX64`'s `rtPhOk`, on `ret0.x`),
`Spike.Lib.X64PhPinsOfPlaceOK`, `Spike.Test.X64PhPinsOfPlaceOK` (the atomic accesses' phases from `placeOK`:
`hphT_ofPlaceOK`, `hphL_ofPlaceOK`, `hphN_ofPlaceOK`, and the other ends of the owned accesses),
`Spike.Test.X64Ret0Negative` (`ret0.w` with `40` made `41`: its `exit_group(43)` obligation is false),
`Spike.Lib.LowerEnv` (the lowering's environment facts, ISA-neutral, for both ISAs' body segments),
`Spike.Lib.LowerEnvImm` (the lowering's immediates as a table keyed by the remaining term, `immsOf`, ISA-neutral),
`Spike.Lib.LowerX64.Checks`, `.Construct`, `.Node`, `.Body`, `.Prologue`, `.ProIn`, `.BodyIn`, `.Fn` (a lowered
parameterless function as one segment on x86-64, symbolic in the frame, from its code checks; `Checks` the closed
checks and `fnCodeOk`, A9), `Spike.Lib.LowerX64.OvfCode` (the local overflow block's code from A9),
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
`ret0.w`), `Spike.Lib.LowerX64.StartU`, `Spike.Test.LowerX64StartU` (the switch and `scc_rt_main` with the user
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
`Spike.Lib.X64StartOfPlaceOK`,
`Spike.Test.X64StartOfPlaceOK` (the start segment's runtime premises from `placeOK`, B5–B7's x86-64 twin),
`Spike.Lib.LowerX64.Correct` (the
x86-64 compiler theorem with its open work as hypotheses: `x64_lower_correct`; the loaded thread at `_start`'s
node: `entry_atX`; at a certificate's facts: `x64_scc_correct`; at every admissible entry state:
`x64_lower_correctE`, `x64_scc_correctE`, `x64_scc_correctE_text` (`Scc.Sem.X64.CorrectE`), `entry_atXE`;
`startAllUW_gen`'s `hrS`: `rS0_eq_lab`; closed, `hgen` discharged by `startAllUW_gen` and `ec_facts`
(`hgen_ofPlaceOK`): `x64_scc_correctE_closed`, `x64_scc_correctE_text_closed`),
`Spike.Test.LowerX64Correct`, `Spike.Test.X64SccCorrect` (it at `ret0`'s certificate, also at the witness entry
state; the closed theorem there too)) cannot
be imported together (the two ISAs' syntax modules declare the same top-level names); the library's globs build
all of them.
-/
import Spike.Bridge.Progress
import Spike.Bridge.LoopCorrect
import Spike.Lib.Thread
import Spike.Lib.Region
import Spike.Lib.Mem
import Spike.Lib.Form
import Spike.Bridge.CertC
import Spike.Lib.SrcMem
import Spike.Lib.Consumer1
import Spike.Lib.Typed
import Spike.Lib.Place
import Spike.Lib.RtRmw
import Spike.Lib.SegLag
import Spike.Lib.LowerA64.MovImm
import Spike.Lib.LowerA64.Checks
import Spike.Lib.LowerA64.Construct
import Spike.Lib.LowerA64.Node
import Spike.Lib.LowerA64.Body
import Spike.Lib.LowerA64.Prologue
import Spike.Lib.LowerA64.ProIn
import Spike.Lib.LowerA64.BodyIn
import Spike.Lib.LowerA64.Fn
import Spike.Lib.LowerA64.Main
import Spike.Lib.LowerA64.MainCode
import Spike.Lib.LowerA64.BodyW
import Spike.Lib.Quiet0
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
import Spike.Lib.Rt.A64EntryOfPlaceOK
import Spike.Lib.LowerA64.Correct
import Spike.Lib.LowerNode
import Spike.Lib.LowerEnvImm

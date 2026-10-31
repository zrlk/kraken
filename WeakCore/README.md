# WeakCore

A lowering target for SCC ('Share and Enjoy'); also a generally useful low-level language with weak memory for reasoning about programs. Assumes x64-TSO or AArch64 with FEAT_LSE2.

## What is here

- `WeakMem.lean`: the litmus-level memory model for both architectures. `check-herd.sh` checks it against herd7's verdicts on the suites in `litmus/`, using the models in `cats/`.
- `Promises.lean`: the promise machine that runs core-language programs over that memory model.
- `CoreLang.lean`, `CoreTerm.lean`, `CoreTyping.lean`: the core language, its terms, and its type checker (`checkProg`, with `CoreTyping.checkProg_sound`).
- `Term*.lean`, `Spawn*.lean` and the rest: the soundness proof. `WeakCore.lean` imports all 476 library modules.
- `extras/`: standalone tools, demos and probes, kept as unbuilt text (see `extras/README`).

Build: `LEAN_NUM_THREADS=4 lake build WeakCore` (about 19 minutes; up to about 7.6 GB in one process). Every `#print axioms` in the build (4,995 constants that use any axiom) uses only `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`.

## Current state of the proof

**Proved (token soundness).** Along every machine run (`TermMain.machine_tokens_mainF`), from a well-formed start; along every run that also spawns threads dynamically (`SpawnArmZ.machine_tokens_main_spawn`), from a `StartOKX` start; and along every run that also takes extern steps (`ExtArmZ.machine_tokens_main_em0`), from a well-formed start:
- every thread stays typed against one global environment; and
- each exclusive key (region tokens, region words, ownership handles) is held at most once, net of what outstanding promises owe. In particular, no region token is held by two threads once no outstanding promise owes it.

**New in this update: `park`/`unpark`, devices, liveness and progress.**
- *`park` and `unpark`* are trusted externs. Each thread has a permit (`TTh.permit`, initially none). `unpark t` sets `t`'s permit, joining in the caller's release view (`TermRun.relView`: what a release store with no dependencies would publish); a `park` that finds a permit consumes it and acquires its view (`TermRun.parkVs`). So `unpark` synchronises with the `park` that consumes it, transitively, as in Rust's `Thread::unpark`. A parked thread without a permit has no move of its own; it may return spuriously, as a move of the environment (`SpuriousWake`), which fairness never forces. The token theorems above cover runs with these steps: an extern step (`TermExtStep.Ext`) now ends in the configuration after the wake-up (`TermRun.wake`).
- *Devices.* Device handle types (`Reg`, `Blk`, `Bus`, `Irq`) and device externs: `mmioRead`, `mmioWrite` and `regAt` for the CPU, and, inside `device def` functions only, `devRecv`, `devWrite`, `devChoice`, `devIrq` and `devOut`. Register accesses and the device's DMA outputs are events of the trace (`TermRun.obsTrace` keeps the observable ones); a register read returns the device's last write (`CoreTerm.ExtName.Admits`). A device function models hardware: it is checked like any other function but is not compiled, and no CPU code can call, spawn or take it as a value. The trust assumption is that the device behaves as some run of its model body. The `acq`/`rel` mode of a register access orders nothing in the model; it is an obligation on the lowering. Function types carry their declaration kind. `restricted` declarations (interrupt handlers with fuel and stack budgets) parse but are refused by the checker for now.
- *Liveness*, stated over the machine with extern calls and spawns as moves (`TermLiveMachE.lean`):
  - for programs whose protocols are all robust and well formed or well-formed epoch counters: on every run from main's start no thread is ever about to access a protocol word in a held state, so no thread retries forever an access to a word held by a crashed thread (`TermLiveL3.robust_touchedFree_thm`, `no_induced_livelock_robust2_thm`; from a scenario start, `no_induced_livelock_robust2_scenario`);
  - certificates: if `TermLiveCert.check` accepts a certificate for a scenario, then on every run from its start that takes no promise step, where that start is coherent (`CfgCoh`; a scenario start is, `cfgCoh_scenario`): there is no fair livelock (`no_livelock_of_check`; `no_livelock_of_check_fair` for certificates without spawns); every configuration the run reaches is one of the certificate's, so every final state it reaches, with its outcome, is one of the certificate's (`reach_of_check`, `outcome_of_check`); and, if no thread crashes and every configuration without a move is final, every fair run reaches a final state (`terminates_of_check`);
  - forced wait: once a thread that holds a word has crashed, and no promise is outstanding from then on, the word never changes again, so a thread that keeps accessing it keeps finding the same held value (`TermLiveC.forced_wait_held_thm`), with critical-section forms (`forced_wait_in_critical_section` and its call form) and seqlock and mutex instances. The critical-section forms cover straight-line paths to the release store only, and no ticket-lock instance is claimed. It is not yet shown that the premises can hold for a real lock (no concrete mutex or seqlock setting is constructed), so these statements may be vacuous.
- *Progress.* On every run with spawns and extern steps from a well-formed start, every thread that is not finished either has a move of its own or is stuck for a listed reason: promises outstanding and not certifiable, at a spawn with the thread capacity reached, or parked with no permit (`TermProgress.progress_main`; the reasons really block, `TermProgress.stuck_sharp`).
- *A first end-to-end program.* `EM0.lean` prints "Hello, world" from a spawned thread, through a small prelude (`EM0Prelude.lean`); the soundness theorems are instantiated for it (`TermScopeEM0`). That its output is a prefix of "Hello, world\n" followed by exit code 0 is checked by bounded search only, not proved.
- *A surface language.* UnElab (`U*.lean`) adds nested operations and other sugar and elaborates to the core language; the UnElab machine and the core machine on the elaborated program have the same runs, up to the translation of configurations (`UElabSim.T2_fwd`, `T2_bwd`). The `sce` command (`Sce*.lean`; the driver is in `extras/`) checks and elaborates UnElab sources and reports liveness verdicts.
- *x86 and Arm with extern and spawn steps.* Every x86-TSO run of machine, extern and spawn steps is an Arm run with the same trace (`TermArchS.tso_stepsE_subset_arm_full`, `tso_traces_subset_arm_full`).

**Extern steps and the trace (previous update).** A configuration now carries a trace of observable events (`TermRun.Event`: an output byte, or an exit code). A program reaches the outside world through trusted externs (`CoreTerm.ExtName`); the first three were:
- `emit : U8 → Unit` appends the byte to the trace;
- `exitEv` appends the exit code, the value modulo 256 (`TermRun.exitCode`);
- `current` returns the running thread's `ThreadId`, a reference to a per-thread box. A spawned thread's box is allocated when it is spawned; the initial thread's box is allocated at its first `current` or its first `spawn`, whichever comes first.

An extern step (`TermExtStep.Ext`) reads no memory and issues no fence; memory and promises are unchanged, and so are views, except that a `park` that consumes a permit acquires its view. `emit` is an `ExtNeedsNoProm` call: it is taken only with no outstanding promise of the thread, and a certification run (`TermRun.Solo`) never takes it (`TermRun.extSteps` stops at an `emit`), so no promise spans an output byte; this removes the executions in which a store that follows an `emit` in the thread's program is promised, and read by another thread, before that `emit` runs (`TermRun.LBE`). `current` may be taken with outstanding promises once the thread has a box, and a certification run may then take it; only a thread with no box yet (the initial thread before its first `spawn` or `current`) must have no outstanding promises, because that `current` allocates. Certification produces no output: `TermRun.Certified` only asks that some solo run exists, and that run's end configuration, with any events it appended, is discarded; the observable trace grows only by real extern steps. `exitEv` still requires the calling thread to have no outstanding promises; other threads are not constrained at exit. The four `ExtArmZ` theorems (`machine_tokens_main_em0`, `token_unique_net_em0`, `token_unique_final_em0`, `reachable_typed_em0`) have the same conclusions as the `_spawn` theorems, over runs that mix machine steps, spawns and extern steps. They do not yet say anything about the trace itself; a statement relating the trace to the program's output is not yet proved.

**What the theorems assume.**
- The type checker accepts the program (`checkProg`).
- The program is in the supported fragment (`ProgScopeOKW`), and so is the start state (`RunScope`).
- The start state is well formed: `InitOK` for the machine-run and extern-step theorems (`initOK_of` derives it from the simpler `InitShape`); `StartOKX` for the spawn theorem (the system invariant, no outstanding promises, view invariants).
- The machine runs with `storeDepRts = true`.
- The liveness theorems at main's start assume the same obligations and start shape (`TermLiveL3.Setting`); the certificate theorems assume a coherent start (`CfgCoh`), take a set `V` of device values and assume `ScriptedRun V` (every `devChoice` result lies in `V`; a program without `devChoice` meets it trivially).
- The certificate-window conditions `CertWinCN` and `CertWinPN` (and their spawn/extern forms) are no longer assumed: they are discharged inside the proof (inside `ObligationsFX.toObligationsCX`).

**Not covered yet.**
- *Pair-store promises in the term-level machine.* The term-level machine (`TermRun`), over which the theorems are stated, does not yet let a thread promise a 16-byte pair store (`stp`, or a successful `casp`) ahead of its earlier loads. The litmus-level promise machine (`Promises.lean`) and the herd7 model both allow this load-buffering behaviour (for example `LB+casp`, `litmus/aarch64-pair/`). So the theorems do not yet cover executions that depend on it. This is deferred.
- A thread with outstanding promises cannot make its first `current` call, call `devChoice`, `emit`, or exit; executions that need this (for example a store after an `emit` promised before that `emit` runs, `TermRun.LBE`) are not covered.
- Access to region payloads; live region binders.
- Region modes; ticket locks; index-∀ annotations; key-carrying wrappers; `validate`; `intoRgn`.
- `storeDepRts = false` (open).
- Bounds on epoch and share keys.
- Liveness beyond the results above: programs whose protocols have held states (mutex, ticket, seqlock), beyond the forced wait; certificates for runs with promise steps. `TermLive.lean`'s bounded search decides liveness per program within its bounds.
- Interrupt handlers (`restricted` functions): refused until their fuel and stack checks exist. Device handles enter a program only as start arguments; `regAt` splits a block handle into register handles.

**Memory model: pair-store promises and barriers in the reference machine.** Pair (16-byte) stores can be promised in the litmus-level promise machine (`Promises.lean`): a plain pair store, like a `casp`, may be promised ahead of earlier accesses and is fulfilled by a pair write, both words at once. A single-word write never discharges a word of a pair promise (`Promises.keepsPairProms`). So `LB` with `stp` writers is allowed there, as herd7 allows it. The reference (non-promising) machine in `WeakMem.lean` lets a barrier issue ahead of a pending plain access it does not order, so a `DMB LD` between two writes orders neither; it still over-forbids an RMW followed by `DMB LD` and a write (`WeakMem.refGap`), which the promise machine gets right. Tests are in `litmus/aarch64-wide/`. This is in the litmus-level machine only; see "Not covered yet" for the term-level machine.

**Memory model: forwarding, `CAS` dependencies and x86 locked RMWs.** Three rules of the machine, each checked against herd7 with tests in `litmus/`:
- *Store forwarding.* A read of the thread's own plain write is forwarded: it takes the write's forwarding view (what the store's address and data depended on, `WeakMem.VState.fwd`) rather than its timestamp. This permits `SB+rfi-pos`, `SB+rfi-dmb.ld` and `SB+dmb.st-rfi-ldar+dmb.sy`, which herd7 allows; the `data-rfi` tests are the controls.
- *Successful non-acquire `CAS`.* It returns the value read with no dependency, as herd7's `aarch64_cas_ok` says, so a later access addressed through the result is not ordered after the read (`MP+dmb.sy+cas-addrRs`, `MP+dmb.sy+casl-addrRs`). `CASA`, `CASAL` and a plain `LDR` are the controls.
- *x86 locked read-modify-write.* It is a full barrier on both sides, failed `LOCK CMPXCHG` included: the fence is applied before the read as well as after the write (`SB+cmpxchg-fails`).

**Memory model: deferred.**
- Promises made by pair writes and `casp` in the core-language machine (`TermRun`); the litmus-level promise machine has them (see above).
- Zero-initialising the `Zeroable` fields of a `new` object.
- Forwarding into the register's dependency view: when a thread reads back its own write, the forwarding view is applied to the thread's views, but the destination register still depends on the write itself, so a later access addressed through that register is ordered after the write (the cause of the first stricter case below).
- The `plain` vs `once` (compiler-visible) access distinction is not modelled.

**Memory model: known differences from stock herd7.** Only the `litmus/aarch64` suite is checked against herd7's bundled model unchanged. The others use the models in `cats/`, which are the bundled ones with axioms added: `x86tso-mixed-rmw.cat` orders locked read-modify-writes (both bundled x86 models allow a non-atomic outcome of two `XCHG`s, `SWPAtomic`), `aarch64-pair.cat` treats `CASP` as one atomic access rather than two independent single-word RMWs, and `aarch64-lse2.cat` also makes the two words of any pair access (`LDP`/`STP` included) single-copy atomic, as `FEAT_LSE2` guarantees. On those tests our model is stricter than stock herd7 and agrees with the repaired model; `WeakMem.lean` names each test and the axiom it justifies.

Beyond the repaired models, the machine itself differs from herd7 in a few known places.
- *Stricter than herd7* (outcomes herd7 allows that our machine forbids):
  - A thread writes a location with a non-acquire-release RMW (`CAS`, `CASA`, `CASL`), reads its own write back, and uses the value as an address (`SB+cas-rfi-ldr-addrs` and its variants). herd7 allows the relaxed outcome; our machine forbids it. Not in `litmus/`; run against herd7 and our machine separately.
  - `LB+casp` in the core-language machine (`TermRun`), which does not make pair-write promises yet. The litmus-level machine allows it, as herd7 does (`litmus/aarch64-pair/`).
- *Weaker than herd7* (outcomes herd7 forbids that our machine allows). These are sound, because every hardware behaviour is still one of ours; they cost precision, not correctness:
  - `SB+casal-po`: a `CASAL` acts as a full barrier for later plain loads in herd7, not in our machine.
  - `SB+stlr-ldar`: a release store followed by an acquire load.
  - `MP+dmb.sy+addr-ldar-init`, `MP+dmb.sy+addr-ldar-ownW` and `MP+dmb.sy+addr-swpa-ownW`: the dependency bound of an acquire.
  Not in `litmus/`; run against herd7 and our machine separately.

The exact statements are the `theorem`s named above. `extras/check-promises.sh` checks their axioms and `extras/tools/premises/` records their premise texts.

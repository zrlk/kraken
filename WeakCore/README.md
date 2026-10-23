# WeakCore

A lowering target for SCC ('Share and Enjoy'); also a generally useful low-level language with weak memory for reasoning about programs. Assumes x64-TSO or AArch64 with FEAT_LSE2.

## What is here

- `WeakMem.lean`: the litmus-level memory model for both architectures. `check-herd.sh` checks it against herd7's verdicts on the suites in `litmus/`, using the models in `cats/`.
- `Promises.lean`: the promise machine that runs core-language programs over that memory model.
- `CoreLang.lean`, `CoreTerm.lean`, `CoreTyping.lean`: the core language, its terms, and its type checker (`checkProg`, with `CoreTyping.checkProg_sound`).
- `Term*.lean`, `Spawn*.lean` and the rest: the soundness proof. `WeakCore.lean` imports all 432 library modules.
- `extras/`: standalone tools, demos and probes, kept as unbuilt text (see `extras/README`).

Build: `LEAN_NUM_THREADS=4 lake build WeakCore` (about 17 minutes; up to about 7.4 GB in one process). Every `#print axioms` in the build (4,745 distinct constants that use any axiom) uses only `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry`.

## Current state of the proof

**Proved (token soundness).** Along every machine run (`TermMain.machine_tokens_mainF`), from a well-formed start; along every run that also spawns threads dynamically (`SpawnArmZ.machine_tokens_main_spawn`), from a `StartOKX` start; and along every run that also takes extern steps (`ExtArmZ.machine_tokens_main_em0`), from a well-formed start:
- every thread stays typed against one global environment; and
- each exclusive key (region tokens, region words, ownership handles) is held at most once, net of what outstanding promises owe. In particular, no region token is held by two threads once no outstanding promise owes it.

**New in this update: extern steps and the trace.** A configuration now carries a trace of observable events (`TermRun.Event`: an output byte, or an exit code). A program reaches the outside world through three trusted externs (`CoreTerm.ExtName`):
- `emit : U8 → Unit` appends the byte to the trace;
- `exitEv` appends the exit code, the value modulo 256 (`TermRun.exitCode`);
- `current` returns the running thread's `ThreadId`, a reference to a per-thread box allocated on first use.

An extern step (`TermExtStep.Ext`) reads no memory and issues no fence; memory, views and promises are unchanged. `emit` may be taken while the thread has outstanding promises, provided the thread is still certified afterwards, and a certification run (`TermRun.Solo`) may itself take `emit` steps. `current` and `exitEv` still require the calling thread to have no outstanding promises; other threads are not constrained at exit. The four `ExtArmZ` theorems (`machine_tokens_main_em0`, `token_unique_net_em0`, `token_unique_final_em0`, `reachable_typed_em0`) have the same conclusions as the `_spawn` theorems, over runs that mix machine steps, spawns and extern steps. They do not yet say anything about the trace itself; a statement relating the trace to the program's output is still to come.

**What the theorems assume.**
- The type checker accepts the program (`checkProg`).
- The program is in the supported fragment (`ProgScopeOKW`), and so is the start state (`RunScope`).
- The start state is well formed: `InitOK` for the machine-run and extern-step theorems (`initOK_of` derives it from the simpler `InitShape`); `StartOKX` for the spawn theorem (the system invariant, no outstanding promises, view invariants).
- The machine runs with `storeDepRts = true`.
- Two certificate-window conditions, `CertWinCN` and `CertWinPN` (and their spawn/extern forms), are **assumed, not proved**. Bounded search has found no counterexample. All three theorems assume them. Since certification runs may now take `emit` steps, these conditions range over more runs than before.

**Not covered yet.**
- *Pair-store promises in the term-level machine.* The term-level machine (`TermRun`), over which the theorems are stated, does not yet let a thread promise a 16-byte pair store (`stp`, or a successful `casp`) ahead of its earlier loads. The litmus-level promise machine (`Promises.lean`) and the herd7 model both allow this load-buffering behaviour (for example `LB+casp`, `litmus/aarch64-pair/`). So the theorems do not yet cover executions that depend on it. Work to add pair promises to the term-level machine is under way.
- A thread with outstanding promises cannot call `current` or exit; executions that need this are not covered.
- Access to region payloads; live region binders. This is the next stage (planned).
- Region modes; ticket locks; index-∀ annotations; key-carrying wrappers; `validate`; `intoRgn`.
- `storeDepRts = false` (open).
- Bounds on epoch and share keys.
- Liveness. `TermLive.lean` decides it per program, separately from these theorems.
- MMIO and interrupts, which the language does not have yet.

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

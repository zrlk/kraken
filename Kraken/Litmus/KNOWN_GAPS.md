# Known gaps between Kraken's weak-memory model and herd7

Status (herd7 master `7.58+1`, rev `9574394`). Numbers are
from `litmus_tests.py` over the frozen and generated corpora.

| Corpus | Agree | Mismatch | Unsupported |
|---|---|---|---|
| `corpus/aarch64` (catalogue) | 52 | 0 | 0 |
| `corpus/x86_64` (catalogue) | 28 | 0 | 0 |
| `corpus/x86` (catalogue, 32-bit dialect) | 21 | 0 | 0 |
| `generated/aarch64` (diycross7) | 304 | 0 | 0 |
| `generated/x86_64` (diycross7) | 39 | 0 | 0 |
| `corpus/x86_64-instructions` | 9 | 0 | 6 |
| `corpus/aarch64-instructions` (L058 with `--slow`) | 207 | 7 | 95 |
| `corpus/x86_64-vector` (hand-argued oracles) | 2 | 0 | 0 |
| `corpus/x86_64-nt` (sweep `NT` + hand-written, `movnti`; 59 SDM oracles) | 107 | 0 | 0 |
| `corpus/aarch64-views` (diycross7 + hand-written, view rules, pair stores) | 77 | 0 | 0 |
| `corpus/aarch64-noret` (diycross7 + gen_zr.py + hand-written, `NoRet` atomics) | 465 | 0 | 0 |
| `corpus/aarch64-pairs` (diycross7 `Pa` + hand-written, `LDXP`/`STXP`/`CASP`) | 71 | 2 | 3 |
| `corpus/aarch64-pairs/lse2` (`--lse2`, hand-argued oracles) | 3 | 0 | 0 |

The two instruction suites are mostly single-thread ISA checks; their gaps
are in Kraken's sequential front-end, not in the memory model. L058 (two
threads, `STP`/`LDP`) takes minutes and is listed in
`corpus/aarch64-instructions/slow.txt`: `litmus_tests.py` skips it unless
`--slow` is given.

## Model decisions taken to match herd (documented in code)

- **Pick dependencies** (`CSEL` family): only the selected source is a data
  dependency of the result; the condition is a pick dependency, which orders
  later writes but not later reads. Registers carry a read-ordering and a
  write-ordering view (`Thread.rview`/`wview`). `aarch64hwreqs.cat` `pob`.
- **CAS**: the comparand orders the write without being its data
  (`condRegs`); on success the comparand register's new dependency is
  *either* its old one plus a pick dependency on the memory read *or* the
  memory read (herd's `aarch64_cas_ok` is `altT` of the two); both are
  explored. On failure it is the memory read.
- **Acquire-release atomics**: after a successful `*AL` RMW every later
  access is ordered after its write (`[range([R & A]; amo; [W & L])]; po`).
- **No-result atomics** (herd's `NoRet`, `AArch64Sem.ml`): an atomic whose
  destination is `XZR`/`WZR` — every `ST<op>`, `LD<op>` and `SWP` with
  `Rt = ZR`, `CAS` with comparand `Rs = ZR`, any `A`/`L` suffix — has a read
  that `DMB LD`/`DSB LD` do not order (`[(Exp & R) \ NoRet]` in
  `aarch64hwreqs.cat` `bob`/`DSB-ob`) and that is never an acquire (so no
  `*AL` ordering after the write either); `DMB SY`, `DSB SY` and later
  release stores still order it, and the write keeps its release. The RMW
  event carries `noRet`; the read raises `vrOldNR`, which `fence .sy` and the
  release pre-view fold and `fence .ld` does not (`readSuccs`).
  `corpus/aarch64-noret/`. A failing `CAS WZR` writes nothing, which is why
  the read needs its own view; its read value is not observable in a final
  state (it only decides that nothing is written), so the hand-written
  failing-`CAS` tests there agree with herd but none of them tells `vrOldNR`
  apart from giving such a read no view at all.
- **Per-access data dependencies** (`STP`): each write of a pair store
  depends only on its own data register (`InstrDeps.dataRegsPer`, consumed
  per store by `runTree` through `InstrViews.forStore`), as in herd's
  `AArch64Sem.ml`, and a written-back base does not depend on the data at
  all (herd's `stp_wback`; a post-indexed `STR`'s base does, in herd as in
  Kraken). L058, `corpus/aarch64-views/LB+datapair*`, `MP+dmb.st+stp-wb`
  and its `STR` control `MP+dmb.st+wb`. No x86 instruction needs
  this: TSO orders every store anyway, and `cmpxchg16b`/vector stores are
  one event or pieces of one register.
- **Store-exclusive data** (`STXR`, `STLXR` in every width, `STXP`,
  `STLXP`): the data registers are no dependency of the write, as herd reads
  them with `read_reg_ord` (`AArch64Sem.ml` `stxr`/`stxp`, since herdtools7
  `add229fa`, 2025-02). `Kraken.Promising.AArch64.deps` drops them;
  `Operation.deps` still lists them, for the coverage test.
  `corpus/aarch64-pairs/hand/LB+fdata-*` (false dependencies; plain
  `STR`/`STP` controls keep theirs). A *true* data dependency is still
  ordered: see OPEN below.
- **`CAS`/`CASP` failure with write-back**: herd's `do_cas_with` explores a
  failing CAS both with and without an explicit write of the value read
  (`altT`). Kraken has only the no-write branch. The write-back writes the
  value it read, atomically after its source, so a reader of it can read the
  source instead; no observable difference was found:
  `hand/CAS-fail-wb-{co,mp,dep,coWW}`, `hand/CASL-fail-wb-rel`,
  `hand/CASP-fail-wb-co` all match herd.
- **x86 failed `lock cmpxchg` without write-back**: the SDM
  (vol. 2A, CMPXCHG) says the destination "receives a write cycle without
  regard to the result of the comparison" (the old value is written back on
  failure). Kraken writes nothing on failure: under `Arch.tso` a failed locked
  RMW is `fence .sy; acquire read; fence .sy` (`X64/Semantics.lean`
  `.cmpxchg`, `Promising/Thread.lean` `runTree` `.rmw`, the `none` branch).
  herd 7.58 agrees (a single atomic read event). In the x86-TSO abstract
  machine a locked same-value write-back leaves memory, store buffers and the
  lock unchanged; an extra same-value write can forbid individual executions
  but never an outcome (a reader can read it instead of its source). Checked:
  9 litmus shapes x 8 variants, Kraken = herd = Kraken with an emulated
  write-back (`lock addl $0`); the x64 `.kl` files `treiber2`, `treiber_pp`,
  `treiber_pp_late`, `treiber_aba_untagged`, `msqueue2` give identical
  verdicts and final sets at fuel 64 and 300 (`spinlock_cmpxchg2/3` time out
  with the emulated write-back, as `xchg` does: `X64/README.md`). We keep this model. Proofs rely on it ("a failing
  `cmpxchg` writes nothing": `LiveTsoRmw.lean`, `SpinX64CmpxInv.InvX`).
  Side notes: a failed `cmpxchg` on a read-only page faults on hardware
  (Kraken does not distinguish read and write permission); 32-bit register
  destinations match hardware (destination untouched, `rax` zero-extended);
  herd's `x86tso-mixed` allows a locked RMW whose write is co-before the
  write it read from (CoRR+casf with `lock addl $0`), which Kraken forbids
  (hardware also forbids it).
- **`CASP`** (all kinds, W and X): herd combines the halves with `>>|`, so
  they are not single-copy atomic and the two reads (and the two writes) are
  unordered. Kraken emits two `rmw` events (`caspTree`), choosing success or
  failure first and exploring both orders of the halves, since the Promising
  thread orders an instruction's events and an acquire or release half
  orders what follows it. Every kind has an order-sensitive pair of tests
  (`hand/MP+dmb.sy+casp*-rd01/10`, `hand/MP+casp*+dmb.sy-wr01/10`). The union
  over orders is argued, not proven, to be complete with respect to herd.
  **Hardware is stronger than herd here** (`corpus/lowering/aarch64/lse2/open/`): Arm ARM DDI 0487G.a §B2.2.1 makes
  the reads and writes of `CASP` single-copy atomic at the size of the pair,
  unconditionally (the sentence is in the base list of single-copy-atomic
  accesses, not under the Armv8.4 FEAT_LSE2 changes). Kraken (like herd)
  shows torn reads for `CASPAL` on a `uint64_t[2]` cell (4 states vs 2 on
  hardware): weaker, never stricter. On a declared 16-byte location
  (`__int128`) `CASP` is unsupported under `isa` (two 8-byte halves of a
  16-byte location are mixed-size).
  **One-event `CASP` under `isaLSE2`** (a Kraken modelling choice, not an
  architectural FEAT_LSE2 requirement): an `X`-register `CASP` whose address
  is 16-aligned and is a declared 16-byte location (`caspIsOneLoc`) is one
  16-byte `rmw` (`toEvCASP`, `Kraken/Promising/AArch64.lean`; `exec_casp16`,
  `instrSemInf_casp16`). It writes `new2:new1` iff both halves match and
  writes nothing otherwise, like a failed single-word `CAS`. It is gated on
  `isaLSE2` so that `isa` stays herd-faithful; `W`-register `CASP` and `CASP`
  on two 8-byte locations are unchanged. With it, `CASP` and FEAT_LSE2
  `LDP`/`STP` share a 16-byte cell: `lowering/aarch64/lse2/MP+caspal-i128+ldp`
  and `CoWW+stp+caspal-i128` match their hardware oracles under `--lse2`.
  Statements that gained a hypothesis with this change: `exec_casp`
  (`caspIsOneLoc … = false`), `execLSE2_of_cellAt` and `execLSE2_of_codeAt`
  (`d.isCaspX = false`; the `CASP` forms are `execLSE2_of_cellAt_casp` and
  `execLSE2_of_codeAt_casp`); `Directive.LSE2Free` now also excludes an
  `X`-register `CASP`, so the `hfree` of the `_lse2` headlines rules it out.
  The FEAT_LSE2 environment logic does not cover a `CASP` on a 16-byte
  location yet: its `CASP` rule needs both 8-byte halves to be locations of
  the layout, so `env_link_halt_lse2` (unchanged) says nothing about such a
  program; it is unsupported there, not unsound (`toEvCASP_allSeq`).
- **Store exclusive** succeeds only when paired with a load exclusive to the
  same location (herd default; the paper's `atomic` allows a different one,
  herd's `-variant CU`).
- **`DSB ST`** orders earlier stores before all later accesses
  (`FenceKind.stAll`); `DMB ST` only before later stores.
- **TSO profile**: every load `acqPc`, every store `rel`, locked RMW
  `acqRel` plus `fence .sy` on both sides.

## Model decisions that are weaker than herd (x86)

- **`movnti` is a weak non-temporal store** (`StoreKind.nt`, kept by
  `Arch.tso`), following the Intel SDM (vol. 3A §8.2.2, §11.3.1): it is
  reordered with other stores to different locations, in both directions.
  It stays ordered after earlier loads and with same-location stores, and
  `sfence`, `mfence` and locked instructions order it (`Views.vwOldNT`,
  folded in by `fence .st/.sy/.stAll`). herd treats it as an ordinary TSO
  store, so 59 tests of `corpus/x86_64-nt` are allowed by Kraken and
  forbidden by herd. They carry hand-argued `.sdm` oracles from an
  independent SDM model (`corpus/x86_64-nt/README.md`).
- **`lfence`/`sfence` order nothing against a later read.** `sfence` emits
  `fence .st`: it orders earlier stores, ordinary or non-temporal, before
  later stores. `lfence` is a no-op (loads are already ordered under TSO).
  Neither waits for the store buffer to drain before a later load, as the
  SDM says. herd's `x86tso-mixed.cat` orders `W; po; [F]; po; R` for any
  fence, so the sweep's 34 such tests are weaker than herd
  (`corpus/sweep/README.md`). This was a design decision.
- **Logic restriction, not a model gap.** The release-prefix theorems
  ((S2)/(S1′), `Kraken/Promising/ReleasePrefix.lean`) assume
  `Thread.NoNTStores`: no non-temporal store at or after the release
  promise; for (S1′) also `Thread.NextNoNT`. Both hold under ARMv8
  (`Thread.noNTStores_armv8`), so the restriction excludes only x86
  programs that use `movnti`. It is temporary, pending a follow-up
; `ReleasePrefixTestsX64.movntiFlag` shows that
  the unrestricted (S1′) is false.
  *Lifted for the release-prefix lemmas:* `Kraken/Promising/ReleasePrefixNT.lean`
  proves (S2′) and (S1′) for every program, `movnti` included, with the
  advancing run allowed to append the thread's own non-temporal messages
  (`Config.advanceableNT_of_path`, `Config.VirtualOfNT`, `VirtualRel.nt`);
  `advanceCheckNT` finds no violation on `movntiFlag`. Theorem 1′ still
  carries the `Config.NTFree` scope. *Scope of Theorem 1′:* the missing piece is
  not only the pending-NT erasure clause. The proof of Theorem 1′ runs one
  monotone virtual micro-run over a single virtual memory, which cannot host
  pending non-temporal stores: a virtual NT append at `|M|+1` lands at a
  different position than the real store (final values differ); a floating
  NT write of one thread to `x` makes another thread's `lock` RMW on `x` fail
  `Memory.atomic` in the virtual world; and `Config.VirtualOfNT` admits one
  advanced thread with pending NT stores, while two x86 threads can each be
  advanced. Lifting the scope needs per-thread private memory extensions,
  retiming micro-steps and a re-proof of the main cases (estimate 2–2.5k
  lines, high risk). No program in the tree needs it: every x64 user of
  Theorem 1′ discharges `NTFree` from its spec via
  `Config.ntFree_of_noNTInv`, and `movnti` appears only in the x86_64-nt
  litmus corpus and tests. Kept as scope; revisit only for a target program
  with `movnti` under a promised release.

## Vector accesses and widths

Vector loads and stores reach the memory model:
an aligned 16-byte `movaps`/`movapd`/`movdqa`/VEX.128 move is one 16-byte
access, `lock cmpxchg16b` one 16-byte RMW, any other vector access a
sequence of 8-byte pieces in address order. Litmus and `.kl` tests declare
widths through C types (`int8_t` … `int64_t`, `uint*`, `int128_t` /
`__int128` / `uint128_t`), take values up to 128 bits, observe `xmm`
registers, and model arrays element by element
(`Kraken/Litmus/Layout.lean`). Herd has no vector instructions, so the
vector tests (`corpus/x86_64-vector`, the `.kl` files in
`Kraken/Examples/LockFree/X64/`) carry hand-argued verdicts. Still missing:

- **EVEX** forms (`vmovdqa32/64` and the other AVX-512 moves): Kraken's x64
  front end has no EVEX encoding yet; their 16-byte atomicity guarantee
  (masking off) waits for it.
- **Line-crossing vector pieces**: an 8-byte piece of a non-atomic vector
  access that crosses a 64-byte cache line is not guaranteed atomic by the
  SDM and is reported unsupported ("vector piece crosses a cache line").

## Pair accesses

`LDXP`/`LDAXP`/`STXP`/`STLXP` on a location declared with the width of both
halves (an `__int128` for an `X` pair, a 64-bit location for a `W` pair) is
one access of that location, as herd's single-copy-atomic pair (`>>||`)
amounts to. Otherwise (two array elements, or untyped) it is two accesses,
the first carrying the exclusive (the second load is plain; the second store
is plain and happens only when the first succeeded). That is **weaker** than
herd, which keeps the two halves single-copy atomic and both exclusive:

| Test | herd | Kraken |
|---|---|---|
| `corpus/aarch64-pairs/MP+dmb.sy+ldxp-arr` | Never | Sometimes (torn read) |
| `corpus/aarch64-pairs/STXP-arr-2thr` | Never | Sometimes |
| `corpus/aarch64-instructions/L032` | Never | Never, with extra states |

A pair on a declared 16-byte location mixed with 8-byte accesses of a half,
and, under `isa`, `CASP` on a declared 16-byte location (two 8-byte `rmw`s),
are reported as unsupported mixed-size accesses (`hand/MIX-i128-*`,
`hand/CASP-i128`). Under `isaLSE2` such a `CASP` is one 16-byte `rmw` (see
"`CASP`" above).

The environment logic (`EnvWP`) covers `CASP` with both halves shared as the
machine performs it: two per-half `rmw`s in either order (`SharedEnv.CaspEnv`,
`casp_shared`; `Kraken/Promising/EnvWP.md`, "Pair effects"). `LDXP`/`STXP`
with both halves shared are deferred with LL/SC (`AllEnv` is `False` on
them). FEAT_LSE2 16-byte `LDP`/`STP` is covered for `isaLSE2`:
`AllEnvLSE2` reads an aligned pair at a 16-byte location of `D` as one 16-byte
access (`ldp_lse2_shared`, `stp_lse2_shared`), linked by `env_link_halt_lse2`
for threads whose `decls` are the layout's locations (`declsOf L`, a choice
made for the link; `isa`, `isaLSE2` and the litmus runs are unchanged). On a
mixed-size access to a 16-byte location neither side claims anything. Pairs
with a half in `dmem` are covered.

FEAT_LSE2's single-copy-atomic aligned 16-byte `LDP`/`STP` is a Kraken-only
ISA variant (`isaLSE2`, `-lse2`, `--lse2`), off by default, stronger than
herd's model, which has no FEAT_LSE2; it is checked against hand-argued
oracles in `corpus/aarch64-pairs/lse2/` and no regression corpus uses it.

## Gaps of `Reachable` (theorems), not of the explorer

These do not affect the litmus comparison (the explorer handles them), but
they bound what a theorem about `Reachable`/`Config.final` says.

- **Mixed-size / overlapping accesses in `succs`**. Model
  *laxer than hardware*: unsound with respect to the SDM and the Arm ARM in
  that region. `Memory.read?`/`initVal`/`finalVal` compare whole `Loc`s
  (`Promising/Basic.lean:118-157`), and with `decls = {}` (strict mode)
  `Decls.resolve` makes every undeclared access its own footprint
  (`Promising/Basic.lean:200`, `resolve_empty` at `:227`). So two unequal but
  overlapping footprints (`⟨c, 4⟩` and `⟨c + 2, 4⟩`, or `⟨c, 4⟩` and
  `⟨c, 8⟩`) are independent locations in `succs` (`Promising/Machine.lean:337`,
  through `succsL`, `:253`) and hence in `Reachable` (`:348`), which no
  hardware does. The only overlap check, `overlapFault`
  (`Promising/Machine.lean:309`), is applied by the explorer's `succsR`
  (`:324`, which drops the successor and reports a `mixed-size access`
  fault), not by `succs`. The litmus front ends reject such tests
  (`checkMixed`, `Litmus/AArch64.lean:218`, `Litmus/X64.lean:275`), as herd
  does without `-variant mixed`, so the comparison is unaffected. The lock
  theorems carry a disjointness hypothesis
  (`hdisj : Decls.overlaps l 4 c 4 = false` in `swp_counter_public`,
  `Promising/SLR/SwpPublic.lean`, and `x64_counter_public`,
  `Promising/SLR/X64SpinPublic.lean`) to stay where the model matches the
  hardware. Dropping or faulting overlapping successors in `succs` would
  make theorems vacuous on such programs; the real fix is a byte-level
  (mixed-size) memory.
- **Faults and wild jumps are invisible to theorems**.
  `succsL` drops `.error` outcomes into its fault list
  (`Promising/Machine.lean:261`), so a faulting run has no successor: it
  never becomes final and is never constrained. `Thread.halted` is
  `exec = none` (`Promising/Thread.lean:132`), and `exec` is `none` at
  `endPc` *or* at a pc with no directive (`Promising/AArch64.lean:134`,
  `Promising/X64.lean:236`), so `Config.final` (`Promising/Machine.lean:33`)
  counts a jump out of the text as termination. Hence "every final
  configuration satisfies `P`" says nothing about faulting runs and covers
  wild halts. The per-instruction rules treat a `.fault` leaf as `True`
  (`EvTree.EraseWPR`, `Promising/SLR/ReachRules.lean:412`; `EvTree.All`,
  `Promising/PromiseSafe.lean:337`). The observable predicates are in
  `Promising/Faults.lean` (`Config.FaultStep`, `Config.FaultFree`,
  `Thread.cleanHalted`, `Config.cleanFinal`, `Config.WildFree`), with
  explorer checks for the two N = 2 lock instances. A theorem-level fix needs
  those predicates, `.fault ⇒ False` in the per-instruction rules, and a
  conclusion at *every* reachable configuration (not only final ones),
  which depends on how certification is carried through the invariant.
- **General `PromisePure` (option (A)) is open.** Theorem 1′
  (`theorem1IIPure`) needs `PromisePure`: on every path to a final
  configuration, a promise not fulfilled by a release write
  (`RelFulfilled`) writes a value pure for its location's release
  predicate. What is proved is option (C) and its generalisations
  (`Promising/SLR/PromisePureGeneral.lean`):
  - `promisePure_of_relWrites`: impure values are written only by writes of
    effective kind `.rel`, at every reachable thread state;
  - `promisePure_of_relWritesT` / `promisePure_of_relWritesReach`: the same
    with a thread-local invariant (`Jinv tid t`, on the whole thread);
  - `promisePure_of_fulfilCell`: the same condition, asked only while the
    promising thread holds its promise.

  (A) would instead derive purity from the rules. A rule's ghost would mark
  only release writes' messages as release (`RelPure`, `ThreadRuleRXK`,
  `Promising/SLR/RelPure*.lean`, proved for the four lock and MP rules).
  The reduction is proved: (A) follows from `RelPure` plus a replay lemma
  `ReplayConcl` (`promisePure_of_replay`). The replay re-runs thread `j`
  from its promise step `J` to the fulfilling step `f` on hybrid
  configurations, i.e. the source with the promise deleted
  (`Sim.SimInvP`, `Promising/SLR/Sim/Partial.lean`, proved per thread).

  The obstacle is erasure of those hybrids. Each environment step of
  `(J, f]` must keep the hybrid erased. In the source that is Theorem 1′'s
  own induction step, so obtaining it here is circular. Moreover, a hybrid in
  which another thread has read the deleted message, or one causally after
  it, is not a machine run. Even the static transfer of erasure from source
  to hybrid needs a new stability hypothesis on every release and acquire
  predicate: it must survive deleting a message and flooring views
  (`Pred.DelStable`; `Pred.mono` only covers memory prefixes). Closing it
  needs a different proof architecture for Theorem 1′, e.g. a promise-free
  certification erasure.

  **Uncovered:** a program whose rule's ghost marks a *plain* store's message
  as release and stores an impure value there. Its plain store fails
  `RelWrites`, so no theorem above applies with that predicate. The fallback
  `promisePure_of_pureNonRel` still gives Theorem 1′ with predicates that are
  pure at the locations the program writes non-release: weaker, never none.

  **Route around it: thread-owned write sets.**
  `treiber2_arm.kl`'s pop writes `top` with a plain `CAS`, so `top`'s release
  predicate must be pure (`RmwOkCAdj`, `PromisePure'`) and carries nothing
  (`ghost₀A`, `EnvG/Treiber2ArmGhost.lean`). The facts that `treiber2`'s
  final layer reads off `top`'s slots are instead kept by their writers:
  each thread holds half of `top` with its own write set of `top` and its
  node's link and data word whole. At the final erasure the two halves
  make all of `top`, so every message of `top` is one of the two threads'
  own writes (`OwnWrites.msg_mem_pair`, `EnvG/Treiber2ArmOwn.lean`,
  ISA-neutral). The push `casl` reads with only own messages of `top`
  before the push, by the RMW's atomicity (`atomic_between`), not by
  `AdjAt.lastAt`, which needs an impure predicate. This route applies to
  other programs whose shared word is written non-release by every thread
  and whose history is determined by the threads' own writes.
  - Two model facts the proof uses, both from the existing semantics:
    `rmw_success_fwd_rel` (a successful armv8 release RMW, the push `casl`,
    leaves its forwarding item at or below `vRel`) and `load_acq_vrNew` (an
    armv8 acquire load whose forwarding item is at or below `vrNew` or
    `vRel` reads at or below its new `vrNew`: the acquire pre-view takes
    `vRel`), hence `FwdOKX` in place of `Treiber2.FwdOK`. An acquire load
    may take the forwarding view of the thread's own exclusive write
    (herd's `aarch64.cat` orders only the exclusive pair's read before a
    later acquire read of the same location, `aob = [Exp & M]; rmw; lrs;
    [A | Q]`; `MP+dmb+addr-{CAS,XCL}-rfi-*` and `SB+CAS-rfi-*` in
    `corpus/aarch64-views/`), so the pop `cas` (plain) leaves an item
    bounded by neither; no acquire load of `top` follows it (`ComDA` in
    `DnBA`/`DnDA`).
- **Fence-based release (`dmb ish; str`) cannot publish an impure value.**
  - **Hardware side: sound.** Messages carry no view in Kraken. A release
    store differs from a plain one only in two ways:
    - its pre-view also takes `relPre = vrOld ⊔ vrOldNR ⊔ vwOld`
      (`writeSuccs`, `Promising/Thread.lean`);
    - it raises `vRel`, which only later acquire loads read (RCsc
      `stlr; ldar`), so it plays no part in message passing.

    `dmb ish` (`fence .sy`) puts `vwNew` above `relPre`, and every store's
    pre-view takes `vwNew ⊔ vCAP`. So after the fence, with no access in
    between, a plain store is release-bounded exactly as `stlr` is
    (`Views.FenceRel`, `writeSuccs_fenceRel_relPre`,
    `EvTree.RelFulfilsF.relPre_lt`, `Promising/FenceRelease.lean`).
    `relPre_lt` is the only property of the fulfilling write that Theorem
    1′'s machine side ((S2), (S1′)) uses. `dmb ishst` / `dsb st` order only
    earlier writes (`fenceStep_st_fenceRel` needs the reads already covered),
    which matches herd: LB+dmb.st is allowed.
  - **Proof side at the original guard `G₀`: not covered.** `RelFulfilled` (hence `PromisePure`) and
    `NPSafe`'s prepay conjunct are keyed to `Thread.RelFulfilsLive`, whose
    write case needs `A.storeKind k = .rel`. A fence-release fulfilment is
    never prepaid, so its promise reaches case (d2), which needs the value
    pure.
  - **Counterexample to the statement.** Take the armv8 writer
    `str 42,[data]; dmb ish; str 1,[flag]` with `rel flag 1` owning `data`
    (impure).
    - Path: the writer runs `str data` (timestamp 1), then promises
      `flag := 1` at timestamp 2 before the `dmb`. Certification: `dmb`,
      then `str flag` fulfils 2 > `vwNew` = 1. The path then runs to a final
      configuration.
    - The promise is fulfilled by a plain store, so it is not `RelFulfilled`,
      and its value is impure. So `PromisePure` is false for this program,
      and no cell condition can give it.
  - **Fix, `PromisePure'` side: done**. The
    chain is generic in the prepay guard (`NPSafeP G K`, `PromisePure' G`,
    `Theorem1IIPure'`; `SLR/Theorem1FinalP.lean`), with the fence-aware
    guards `GF` and `GHyb rel` (`SLR/NPSafePFence.lean`).
    `SLR/PromisePureF.lean` adds the producer:
    - `EvTree.RelWritesF A Q F`: writes that are neither release nor
      fence-released satisfy `Q` (the flag `F` is the context's `FenceRel`;
      `fence .sy` sets it, any access clears it, `dmb ishst` never sets it);
      `RelWrites.relWritesF` transfers every existing cell proof.
    - `promisePure_of_relWritesF` (`PromisePure' GF`) and
      `promisePureHyb_of_relWritesF` (`PromisePure' (GHyb rel)`), from a
      thread invariant `Jinv` and the cell condition at flag
      `t.views.FenceRel` (`finishInstr_fenceRel`,
      `stepOne_fenceRel_of_fence_sy` supply the flag after `dmb ish`).
    - `theorem1IIPure_of_relWritesF` (Theorem 1′ through
      `theorem1IIPure_Hyb_S`, per thread `NPSafeP (GHyb g.rel)
      (K2Scope AllocIds)`) and `theorem1IIPure_of_relWritesF_GF`;
      `relWritesF_hyps_of_relWrites`: the release-write form's hypotheses
      (with `RelPure` rules) imply the new form's.
    - The writer above at the cell level (`SLR/PromisePureFTests.lean`):
      its flag store fails `RelWrites` and satisfies `RelWritesF`.
  - **Fix, `NPSafeP` side: done for MP**. `MpFence.mp_fence`
    (`SLR/MpFence.lean`) is the MP property (`MpPublic.mp_public`'s
    statement) for the writer `mov w2,#1; mov w3,#1; str w2,[x1]; dmb ish;
    str w3,[x0]` (`FenceW.fwriterMp`; data value `1` so that the existing MP
    reader proof is reused) and the existing MP reader, under `Arch.armv8`,
    with the impure flag predicate. Concrete instance and explorer check:
    `SLR/MpFenceConcrete.lean`.
    - The writer's rule `FenceW.fwRuleG` (`SLR/FenceWRule.lean`) is a
      `ThreadRuleRXG (GHyb rel)` (for every `rel` pure at the data word):
      its `prepay` is the old `stlr` prepay, at the fence-released flag
      store (`relFulfilsF_posF`). The `G₀` disjunct never holds (no release
      store); a fence-aware fulfilment by the data store is excluded by
      purity of its message. `NPSafeP` by `NPSafeP.of_ruleRXG`
      (`fw_npSafeP_hyb(_S)`).
    - The erasure rules are store-kind agnostic (`eraseWPR_store_rel`,
      `Erase.fresh_of_impure`); the timestamp bound `vwOld < tw` of the
      release split comes from `FenceRel` (`writeSuccs_fresh_vwOld_F`,
      `writeSuccs_relF_relPre`), so the invariant carries `FenceRel` at the
      flag store (set by the `dmb ish` cell, kept by the environment and by
      prepayments).
    - The cell condition's thread invariant (`MpFence.FReach`, with
      `FenceRel` at the flag store) holds at every reachable configuration by
      `threadInv_reachable` (the thread-level `configInv_reachable`).
      Assembly: `final_of_relWritesF` (the `GHyb` `final_of_relWrites`).
  - **Recipe for another `dmb ish; str` publisher:** (1) phase invariant
    with `Views.FenceRel` at each fence-released impure store; (2) a
    `ThreadRuleRXG (GHyb rel)` whose `prepay` handles each store that can
    fulfil fence-aware (`Thread.RelFulfilsLiveF`): the impure ones as for
    `stlr`, the pure ones by the impure conjunct of `GHyb`; (3) the cell
    condition `RelWritesF` under a thread-level invariant
    (`threadInv_reachable`); (4) `theorem1IIPure_of_relWritesF` /
    `final_of_relWritesF`.
  - **EnvG/vcgen route: prototype** (`SLR/EnvG/FenceEnv*.lean`).
    `EnvG` already models fence release with no frozen change: `fence .sy`
    sets the state's `fencedR`/`fencedW` bits, `StoreOk` allows a planned
    release at `effRel` (`.rel` *or* both bits set), and `NodeRel` carries
    `FencedInv`. The prototype adds two pieces. (1) The rule side:
    `ThreadRuleRXG.ofSafelyEnvGHyb` / `npSafeP_hyb_of_safelyEnvG_S` give
    `NPSafeP (GHyb g.rel)` from the usual `ofSafelyEnvG` data plus an
    `InvG … (QA64 …)` start condition; `InvG.prepayHyb` handles the
    fence-aware fulfilment. (2) Purity: a separate per-thread environment
    `SharedEnv.relPureF`, proved with vcgen and assembled by
    `final_of_relPureFSafely`. `relPureF` is needed because EnvG's bits are
    more permissive than `RelWritesF`'s syntactic flag. `FenceEnvMp.mp_fence_envG`
    has `MpFence.mp_fence`'s statement (checked by `rfl`).
  - **Still open:** a generic producer (a `ThreadRuleRX`-to-`GHyb` transfer
    for rules whose impure non-release stores are all fence-released);
    on the EnvG route, release RMWs are not fence-aware, and each thread
    needs a second vcgen proof (`relPureF`); `dmb ishst` publishers (need the
    reads covered, `fenceStep_st_fenceRel`).
  - **Workaround elsewhere:** use `stlr` for the publishing store, or a
    predicate pure at `flag`.
- **Write after load-acquire: covered by the take rule (option (S)); the
  ticket lock is proved** (ticket lock, MCS/CLH locks, SPSC ring buffer,
  ownership hand-off): a thread that acquires a location's permission by a
  *load*-acquire and then *writes* that location.
  - **Why it was not covered under the existing `NPSafe`.** The store rules need the write permission in the thread's own
    resource, `0 < (r.wr l).q` (`EvTree.eraseWPR_store`,
    `EvTree.eraseWPR_rmw`, `Promising/SLR/ReachRules.lean:610, 636`). Loads
    keep `(r, g)` (`eraseWPR_load`), and a load cannot move the acquired
    slot into `r` under the existing erasure and `NPSafe`: keeping the id
    `ι` violates `Erase.slotsDom` (a replacement slot must satisfy
    `slotsPred` at the unit resource); swapping `ι` for a fresh `ι'` adds
    slots at old messages, which `NPSafe`'s K2 conjunct (`ReachFrame`,
    quantified over every `ρ`) forbids; dropping `ι` removes its other
    slots and breaks `Erase.writes` or K1.
  - **Read side works.** An acquire load followed by plain loads of the
    owned data (MP's reader) is covered via `slot_of_seen` and
    `read_max_slot` (`Promising/SLR/StoreHelpers.lean`).
  - **Options, for a design decision** (each is a new `Erase'`/`NPSafe'` plus
    a re-proof of Theorem 1′, or an edit of existing definitions):
    - (T) a ghost field `taken` of slots moved into a thread, exempt from
      `slotsDom`;
    - (S) keep the swap and restrict K2 to acquire ids allocated before the
      step (`ι < g₁.acqTab.length`).
  - **Now covered, option (S)**:
    a load may *take* the acquired slot. K2 is scoped to acquire ids
    allocated before the instruction (`K2Scope … AllocIds`), and Theorem 1′
    is proved for that frame (`theorem1IIPure_G₀_S`, `theorem1IIPure_F_S`,
    `theorem1IIPure_Hyb_S`, `SLR/Theorem1FinalP.lean`).
    - Old-style rules: `ThreadRuleRXGS`, `NPSafeP.of_ruleRXGS`
      (`SLR/TakeRuleThread.lean`).
    - EnvG: the environment `EnvGT` lets non-forwarded acquire loads take
      their exposed slot. Links: `ThreadRuleRXGS.ofSafelyEnvGT`
      (`EnvG/TakeA64Link.lean`), and `ofSafelyEnvGTR` with release-kind RMWs
      (`EnvG/TakeRA64Link.lean`). Assembly: `final_of_relPureSafelyS`.
    - Example: `TakeMp.takeMp_envG`, MP whose reader spins on `ldar`, then
      stores to and reloads the data (`EnvG/TakeMpPublic.lean`).
    - Limits: AArch64 only (since the x64 take route also x64: `ofSafelyEnvGTX`,
      `EnvG/TakeX64Link.lean`, used by `SpscX.x64_spsc_envG`); only
      non-forwarded acquire loads take; no take at a fence node; the take and
      the use of what is taken are in different instructions.
    - **Skipped releases**. On `EnvGT` a load takes only the
      slots of the message it reads (`takeAll`), so a reader that skips a
      release (reads `tail = 2` without ever reading `tail = 1`, which herd
      allows) strands the skipped message's slot: it is renamed to the fresh
      id and no later load can take it (A64 `spsc_queue.kl`). **Covered on `EnvGTU`** (`EnvG/TakeU*.lean`):
      the cumulative take `takeUpTo l tr` takes the slots of `(l, ts)` for
      every `ts ≤ tr`. Sound with the existing lemmas only (`Erase.take` has no
      timestamp condition; `Erase.rStepS_take` needs `ts ≤ wfloor`, and
      `ts ≤ tr ≤ wfloor`). `EnvGT`'s take is the no-skip special case
      (`takeUpTo_eq_takeAll`). Smoke: `TakeUSkip` (a reader that reads
      `f = 2` collects `Dt` from the `f = 1` slot, through a
      memory-dependent predicate). The old `EnvGT` links are unchanged.
      **Now proved: A64 `spsc_queue.kl`** (`SpscA.a64_spsc_envG`, `EnvG/A64SpscPublic.lean`), both threads on
      `EnvGTU`, all layouts. Per-thread image (each thread runs its own part
      of the code block; `codeMatches`: the block is
      `spscProdA ++ spscNop ++ spscConsA`). **Resolved**:
      `SpscA.a64_spsc_envG_whole` (`EnvG/A64SpscWholePublic.lean`) runs both
      threads in the whole block from their start labels, through the masked
      guarded-exit link `EnvG/A64MaskLink.lean`; concrete instance with
      `codeMatchesW`/`runnerMatchesW`. `a64_spsc_envG` is kept.
  - **Now proved: the ticket lock**. Who gets ticket `v` is
    decided by the RMW chain on `next`, whose relaxed messages must stay pure
    (`PromisePure'`), so they cannot carry token slots; the dispenser
    extension (`Dispenser.TX`, `EnvGTD`, `theorem1IIPureX_G₀_S`
    the ticket lock proof/the ticket lock proof/the ticket lock proof) hands each ticket's token out at the RMW.
    - `TicketLock.ticket_counter_envG` (`EnvG/TicketLockPublic.lean`):
      `counter = N` at every final configuration of `ticketlock2.kl`'s
      worker (`ldadda` hand-out, `ldar` spin, plain increment, `stlr`
      release), for all layouts, `N` threads with `N + 1 < 2 ^ 32`, disjoint
      4-byte words initially `0`. No fault: `tkRule_noFault`.
    - Route: one `vcgen` proof on `EnvGTD` (`tkWorker_envGTD`), purity and
      the single-RMW dispenser shape by a second `vcgen` proof in the
      phase-tracking purity env `dispPure` (`EnvG/TicketLockPure.lean`),
      `theorem1IIPureX_G₀_S_singleRmw`, then `ticket_final`
      (`EnvG/TicketLockGhost.lean`).
    - **Now proved: the `ldaddal` variant** (additive, no model
      change: `next` stays pure, so the release RMW never
      forwards what it claims). `TicketLock.ticket_al_counter_envG`
      (`EnvG/TicketAlPublic.lean`): the statement of `ticket_counter_envG`
      for `ticketlock_al2.kl`/`ticketlock_al3.kl`'s worker `tkWorkerAl`
      (`LDADDAL` hand-out); concrete instances with `codeMatches` and
      `runnerMatches` (whole image) in `EnvG/ConcreteTicketAl.lean`. Route:
      the ticket env with a release-kind ticket RMW `EnvGTDR`
      (`EnvG/TicketREnv.lean`: `RmwOkTD` without `¬ effRelRmw`, with
      `∀ v, pl.rel D.x v = false`), its link (`TicketRLink.lean`: the
      in-flight ticket RMW `NodeRel.rmwTDRRel`), rule link with the
      release-RMW prepay (`TicketRRuleLink.lean`: `XFresh` from the
      fulfilling RMW's atomicity) and AArch64 link with `Phase1TreeR`
      (`TicketRA64Link.lean`); the ghost, VC and final layers of
      `TicketLock` are reused unchanged.
    - **Closed:** the x64 ticket lock with the unlocked
      `incl (owner)` release (`X64/ticketlock2.kl`):
      `TicketX2.ticket2_counter_envG_verbatim` / `_runner` /
      `Concrete.ticket2_counter_envG_runner_concrete2`
      (`EnvG/X64Ticket2{VCGen,Public,Runner}.lean`), not through the SLR
      link (no x64 link combines the `LR` shapes with `EnvGTDR`) but by a
      per-thread invariant on the timestamps of the thread's accesses at
      every reachable configuration (`EnvG/TicketX2{Run,Env,Reach,Final}.lean`).
    - MCS/CLH locks have no example yet. (SPSC ring buffers: proved since,
      `SpscA.a64_spsc_envG` above and the x64 `SpscX.x64_spsc_envG`,
      `EnvG/X64SpscPublic.lean`; index: `Examples/LockFree/THEOREMS.md`.)
- **Whole-thread environment `EnvG`, phase 1: releases must be stores**
  (`Promising/SLR/EnvG/`, `ThreadRuleRX.ofEnvG` / `ofSafelyEnvG`).
  - **Release RMWs: covered by the `R` link, with two limits** (
    the release-RMW extension). `ThreadRuleRX.ofEnvG` / `ofSafelyEnvG` still ask `¬ effRelRmw`
    (`Phase1Shape`). The additive `ThreadRuleRX.ofEnvGR` (`EnvG/RuleLink.lean`)
    / `ofSafelyEnvGR` (`EnvG/A64LinkR.lean`) take `Phase1ShapeR` /
    `Phase1TreeR` (decided per program by `dirs_phase1R`). Their *shape*
    check accepts `swpal`, `ldaddl` and the other total `ld<op>l` on
    AArch64, but the per-step obligations restrict what can be proved:
    see limit 2 for release-only RMWs and for plans that give
    something away (limits 2 and 3 are lifted on the claim-conditional
    `EnvGC`/`EnvGTC` the claim-conditional extension). An RMW
    fulfils a pending promise and claims at fulfilment (`NodeRel.rmwRelS`,
    `EnvG/LinkR.lean`); the RMW write is prepaid like a store
    (`prepayGenericRmw'`, `EnvG/PrepayRmw.lean`). The original statement `PrepayGenericRmw` (`EnvG/Prepay.lean`) is unprovable as stated (it
    claims at promise time) and stays unproved. The limits:
    1. **An in-flight release RMW must never fail** (`∀ x, op x ≠ none`). A
       failing CAS leaves its prepaid promise outstanding, so `casal` and
       x64 `cmpxchg` releases are excluded (`RmwRelSmoke.lean`: `dirs_phase1R`
       rejects `casal`).
    2. **Planned-release RMWs claim nothing given away. Lifted on
       `EnvGC`/`EnvGTC`** (the `swpl` relay; see "Lifted" below). On
       the old `EnvG`/`EnvGT` links the limit stands as follows
       (`RelRmwGiveOk isa pl rel₀`, a hypothesis of `ofSafelyEnvGR`): the
       update slots an RMW claims carry nothing at the locations the
       release gives away. It holds trivially when the plan gives nothing
       away (`RelRmwGiveOk.of_gives_nil`); otherwise it is a program
       obligation.
       - **Correction: with gives ≠ [] it is not provable as
         stated.** `RelRmwGiveOk` quantifies over *every* `Erase` ghost
         with the program's `rel`, every location `l` and every read time
         `tr`. Nothing ties `tr` to the message the RMW actually reads, and
         `Ghost.Le` lets `upd` grow. So an erasure ghost may hold a
         release-mode message at `l` (even the initial one, once it is put
         in release mode) whose unclaimed update slot has predicate `True`
         and carries the given-away location. Its claimed-slot product then
         meets `Res.only (pl.gives l new)` non-trivially. "It reads `l`'s
         initial message, which has no update slots, so `RelRmwGiveOk`
         holds" (the ticket take route's remark on the `swpl` relay and the CLH lock) is
         therefore wrong. Every use so far is `of_gives_nil`.
       - **Release-only RMWs** (armv8 `.rel`: `swpl`, `ldaddl` and the
         other `ld<op>l`) are also blocked on the `RmwOk` side. `Arch.rmwKind`
         remaps only `.plain`, so their read half is not acquire, `ClaimOk`
         fails, and `RmwOk` then needs `claimedSlots g l tr = []` at every
         anchor ghost (`AnchorOk`). That has the same counterexample as
         above. `swpal`/`ldaddal` fix `ClaimOk` but still need the give
         obligation over `σ.r ⋅ C`.
       - Consequence (history: true on `EnvG`/`EnvGT`, before the claim-conditional extension):
         `dirs_phase1R` accepting `swpl`/`ldaddl` (`RmwRelSmoke.lean`,
         `TakeRSmoke.takeRelRmw`) checks shape only. On the old links no
         release-only RMW, and no release RMW whose plan gives something
         away, has an end-to-end proof; the proved `mp_relay3.kl` releases
         with `stlr` (`EnvG/RelayPublic.lean`).
       - Proposed fix (option (b), a change to the existing design): give
         `RelRmwGiveOk`/`RmwOk` ghost-knowledge side conditions. State
         them at the read message (`ReadAt` of `(l, tr)` and the env
         invariant `Q`), not at arbitrary erasure ghosts, so a program can
         show that the slots it actually claims carry nothing given away
         (e.g. "f2 holds only messages whose slots carry no `Dt`").
         **Superseded by the claim-conditional extension; not needed** (no change to existing code).
       - **Lifted on `EnvGC`/`EnvGTC`** (`EnvG/RmwGhost*.lean`;
         links `ThreadRuleRX.ofSafelyEnvGRC`, `ThreadRuleRXGS.ofSafelyEnvGTRC`).
         Both causes are choices in how the old environment is written, not
         limits of the model. The new environments claim only when
         `ClaimOk` holds. A non-claiming RMW is erased as a store, so
         release-only RMWs need no claim condition. They also give from the
         thread's own resource `σ.r` and keep the claimed slots, so
         `LinkHypsRC`/`LinkHypsTRC` have no `RelRmwGiveOk` field. Ghost-only
         bookkeeping: no execution is excluded. `EnvG` refines into `EnvGC`
         (`envG_ok_toC`, `envGC_step_toG`). End to end:
         `mp_relay3_swpl_envG` (`EnvG/RelaySwplPublic.lean`, for
         `mp_relay3_swpl.kl`). The relay takes `Dt` at its `ldar` and gives
         it away with `swpl` (release-only, gives `[Dt]`). A lock released by
         an RMW: `swpl_counter_envG` (`EnvG/SwplLockPublic.lean`,
         `spinlock_swpl2.kl`), whose `swpl wzr` gives the counter share and a
         split share of the lock. Still impossible
         on every environment: a release RMW forwarding what it *claims* in
         the same instruction (the `ldaddal` ticket chain).
    3. **Release RMWs give whole locations only. Lifted on
       `EnvGC`/`EnvGTC`** (`RmwOkC` has no `Plan.Whole`,
       because the plan gives from `σ.r` and the claimed slots are kept
       apart, `Plan.afterC_op_give`). On the old `EnvG`/`EnvGT` links: a release
       RMW's plan entry has no split (`Plan.Whole`, a conjunct of `RmwOk`).
       The in-flight link (`Plan.after_op_claim`) and the RMW prepay
       (`Plan.give_op_of_unit`) need the homomorphism laws of
       `Res.only`/`Res.drop`, which a general `(cl, r)` split lacks. Lifting
       it would need an optional split law (`give (r ⋅ C) = give r ⋅ …` for
       claimed slots `C`).
    - There is no x64 instance yet. x64 RMWs are release-kind with
      `noRet = false`; `xchg` / `lock xadd` are total, and `cmpxchg` hits
      limit 1. (Since then: the x64 `xchg` spinlock goes through the `R` link,
      `ThreadRuleRX.ofSafelyEnvGRX`, `X64SpinPublicG.x64_spin_counter_envG`;
      the `xchg` relay `RelayX.mp_relay3_xchg_envG` through the
      claim-conditional `ofSafelyEnvGTRCX`; `lock cmpxchg` through the `F`
      route below; `EnvG/X64_KNOWN_GAPS.md`, "An x64 lock".)
  - **Failing in-flight release RMWs: the `F` route** (the x64 `cmpxchg` lock proof; unconditional). This addresses limit 1 of the entry above. The `F`
    link (`EnvG/RmwFailRule.lean`, `RmwFailRuleLink.lean`; AArch64
    `ThreadRuleRXF.ofSafelyEnvGF`, `dirs_phase1F` accepts `casal`; x64
    `ThreadRuleRXF.ofSafelyEnvGFX`, `dirs_phase1FX` accepts `lock cmpxchg`)
    needs no totality and gives `NPSafeF`: `NPSafe` whose step conjunct also
    assumes `StepFul`, which is all Theorem 1′'s annotated run uses.
    - **Closed:** Theorem 1′ for `NPSafeF` is `Theorem1FChain`
      (`theorem1IIPure_of_F` is proved from it), now proved as
      `theorem1FChain` (`EnvG/RmwFailChain.lean`): the Theorem 1′ chain is
      generic in a step guard (`StepGuard`, `NPSafePS`, `theorem1IIPureS'`),
      discharged from `StepFulP` at its two `stepAt` sites.
    - Example: `CmpxPublic.x64_cmpx_counter_envG'`, the x64 `lock cmpxchg`
      spinlock `counter = N`, unconditional (`x64_cmpx_counter_envG`, kept,
      takes `Theorem1FChain` as an explicit hypothesis). The x64 `xchg` spinlock
      (`X64SpinPublicG.x64_spin_counter_envG`) is unconditional, through the
      `R` link.
    - **Treiber with ≥ 2 pushers — proved** (`treiber2_nodes.kl`, `treiber2.kl`; the
      1 push ∥ 1 pop `treiber_pp_envG` is proved on the F × C link): release
      RMWs cannot forward claims (the ticket take route (c)); no own-message adjacency at
      RMWs (F1/F2): the release obligation of `RmwOkC` has no `atomic` and no
      own-message exclusion between the read and the fresh write, so a
      history predicate on `top` cannot be established on `EnvGC`. **The
      adjacency is supplied by the additive sibling link `EnvGCAdj`** (`EnvG/AdjSpike*.lean`: `AdjAt`, `ThreadRuleRXF.ofSafelyEnvGFCAdj`;
      EnvGC judgments transfer via `qa64C_toCAdj`). **Closed (
      the Treiber node proof): proved on `EnvGCAdj`** — `Treiber2.treiber2_nodes_envG`
      (`treiber2_nodes.kl`) and `Treiber2.treiber2_envG` (`treiber2.kl`, with
      the data word), both with concrete instances (`EnvG/Treiber2*.lean`,
      `EnvG/ConcreteTreiber2*.lean`). Forwarding stays impossible; the proof
      freezes each node (link and data word) at its push and reconstructs the
      history of `top` at the final erasure (`Treiber2Hist`,
      `Treiber2Final`), with one acquire id of `top` per thread.
    - **Michael–Scott queue, 1 enqueue ∥ 1 dequeue — proved**:
      `MsQueue.msqueue1_envG` (`msqueue1.kl`, `1:X10=1`, on `EnvGCAdj`, all
      layouts, concrete instance `ConcreteMsQueue.msqueue1_envG_concrete`;
      `EnvG/MsQueue*.lean`). Start hypotheses: `head = tail = d` and both
      links `0` initially (`InitV`), and both threads start with an empty
      private memory (`dmem` maps no 8- or 4-byte word). Only the addresses'
      `Loc`s are distinguished (the mixed-size gap). The dequeuer's
      zero-step back edge (`cbz x5, deq1a`) needs a ranked CFG rule
      (`cfgEnv_partial_rank`, `EnvG/MsQueueCfg.lean`), since
      `cfgEnv_partial`'s `EdgeSafe` forbids it.
    - **Michael–Scott queue, 2 enqueues ∥ 2 dequeues — proved (
      the MS queue proof)**: `MsQueue.msqueue2_envG` (`msqueue2.kl`,
      `1:X10=1 ∧ 1:X11=2`, on `EnvGCAdj`, all layouts, concrete instance
      `ConcreteMsQueue2.msqueue2_envG_concrete`; `EnvG/MsQueue2*.lean`).
      Start hypotheses as for msqueue1 (`InitV2`: `head = tail = d`, the
      three links `0`; empty private memories), plus `n1 ≠ 0`, `n2 ≠ 0`
      and pairwise distinct `Loc`s (`QLocs2`).
    - **Michael–Scott queue, 2 enqueues ∥ 2 competing dequeuers — proved**: `MsQueue.msqueue3_envG` (`msqueue3.kl`,
      `(1:X10=1 ∧ 2:X10=2) ∨ (1:X10=2 ∧ 2:X10=1)`, on `EnvGCAdj`, all
      layouts, concrete instance `ConcreteMsQueue3.msqueue3_envG_concrete`;
      `EnvG/MsQueue3*.lean`). Start hypotheses as for msqueue2 (`InitV2`,
      `QLocs2`, empty private memories for all three threads). The x64
      queue: proved since (on `EnvGCAdjX`):
      `MsQueueX.x64_msqueue2_envG_verbatim` and
      `MsQueue3X.x64_msqueue3_envG_verbatim` (`X64/msqueue{2,3}.kl` verbatim),
      with `_runner` companions (`EnvG/X64_KNOWN_GAPS.md`, the x64 MS queue proof).
  - **Release splits: the whole-location limitation is resolved
    for store releases.** Plans used to give away fixed whole locations, never a
    share of the released location, and the same whatever `cl` was, so a lock
    release could not pay SLR's `Bad` disjunct (unclean releasers, forwarded `Bad`). A plan entry may now carry a
    `Plan.Split` (`give keep : Prop → Res → Res`, exact, keeping a positive
    share), with the generic share library in `EnvG/Split.lean`. The split's
    knowledge is fixed at the prepay (`Inflight` records `P` with `cl → P`;
    `StoreFacts`/`RmwFacts` expose `∃ P, (σ.cl → P) ∧ σ'.r = after … P σ.r`),
    so **an unclean thread gets some split, not a chosen one**: after an
    unclean release it knows only a positive share of the lock, not `1/N`.
    `Plan.Valid` is unchanged and decidable. Splits on RMW releases: limit 3
    above.
  - **Claim fix:** a successful RMW exposes that the message it
    read is unclaimed at the anchor ghost (`RmwOut`/`RmwFacts`,
    `ErAt.not_claimed_rmw`), so an RMW-claim acquire can use its claimed
    slots (the former `StepRmwU` is now `stepRmwU`, `EnvG/CasStepRmwU.lean`).
  - **Stated hypotheses** (per program, not proved generically):
    `Phase1Tree A e` (every tree of the code is a deterministic single
    access with no release RMW: `DetAccess` and the `SingleAccessS` shape),
    `e.rmwLive` (decided), `pl.Valid` (decided, e.g.
    `sampleLockPlan_valid`).
  - **No-fault track** (`EnvG/RuleNoFault.lean`, `EnvG/A64NoFault.lean`,
    `EnvG/Answers.lean`, `EnvG/A64Answers.lean`). `NoFaultRule` for the
    rule is proved from fault-free code alone, with or without promises:
    `noFaultRule_ofSafelyEnvG_struct` (AArch64, from `DirsNoFault e`,
    `dirs_no_fault`) and `noFaultRule_ofEnvG_struct` (ISA-neutral, from
    fault-free trees at every invariant state). A run faults only at a
    `.fault` leaf, so no env answer is needed.
    - `DirsNoFault e` asks the tree of every directive to be fault-free from
      every machine state: it rejects `unimplemented` instructions,
      SP-relative addressing (`unaligned_sp` from an arbitrary SP), and any
      `undefined` register or flags value (`toEv` makes it a fault leaf;
      `Effects.AllEnv` is `∀ v` there, so `Safely` does not exclude it).
    - The older env route (`noFaultRule_ofEnvG` / `noFaultRule_ofSafelyEnvG`)
      also takes `EnvGAnswersAt` (an env write outcome for every actual
      write). It holds for a thread without outstanding promises
      (`envGAnswers_of_promFree`), but is believed **false** for a thread
      with a pure own non-pending promise `ts` at `l` whose next store
      writes another value to `l`: every actual write overtakes `ts`, and
      `EnvG` offers no overtaking outcome (sketch, not formalised). Those two theorems may be vacuous there; use the
      `_struct` forms.
  - The existing `InflightWritesDead` (`EnvG/Link.lean`) is unprovable as
    stated. It is superseded by the tree-indexed side conditions
    (`SingleAccessS`, `StartS`, `treeJ_envG_eraseWPRDS_start`,
    `EnvG/LinkS.lean`).

## Reachability theorems for the `Sometimes` LockFree examples

Each `# expect: Sometimes` example in `Examples/LockFree/{X64,AArch64}`
should have a Lean theorem `∃ c, Reachable A fuel c0 c ∧ c.final ∧ …`
showing the violating (forall) or satisfying (exists) final state. Here
`c0` is the runner's initial configuration (decls and initial memory
included; the link is a `#guard_msgs #eval` comparison with the runner's
config, not a kernel proof). The witness is the explorer's trace
(`Litmus/reach_trace.py`), replayed by `reachRun` and checked with
`decide +kernel` (`Promising/ReachCore.lean`, `reach_witness_prop`). The
`.kl` header line `# Proved reachable:` names the theorem.

- **Proved (8):** x64 `dekker_broken`, `mp_incl_early`, `publish_movups`,
  `spsc_queue_early`, `treiber_aba_untagged`, `treiber_pp_late`; AArch64
  `spinlock_relaxed_acq2`, `ticketlock_relaxed2`
  (`Promising/Reach{X64,A64}*.lean`). These need no promise and hold for
  every `fuel`.
- **Proved with promises (7 theorems):** AArch64 `treiber_pp_relaxed`,
  `spinlock_relaxed2`, `spsc_queue_relaxed2`, `msqueue_relaxed1`,
  `msqueue_relaxed2`, `spsc_queue_relaxed3`, `treiber2_relaxed`
  (`Promising/ReachA64<Camel>.lean`, theorem
  `Kraken.Promising.Reach.<Camel>.<name>_reachable`). Every witness contains
  a promise step, and with `-promises 0` each of these files is `Always`. A
  promise successor, and any later instruction step of a thread holding a
  promise, is in `succs` only if `certify` succeeds. `certify` keeps a
  `Std.HashSet` of visited states and a `Std.HashMap` cache, which the kernel
  cannot evaluate (`hash` reduces through the opaque `mixHash` and
  `System.Platform.numBits`). `Promising/ReachCertCore.lean` defines
  `reachGoL`, the same search with a list as visited set and no cache, and
  proves `certify = reachCert` (`reachCert_eq`, `reach_certify_exact`, via a
  cache invariant that holds for the empty cache the runner starts from).
  The checker `reachPRun` replays instruction and promise steps
  (`ReachPStep`), evaluating `reachCert` where `succs` needs a certification;
  `reach_witness_promise` turns a `decide +kernel` run into the theorem.
  Long witnesses are split into segments at generated intermediate
  configurations (`Promising/ReachCheckpoint.lean`, `reach_segment`;
  `ReachA64Checkpoint.lean`) so that each kernel check stays under 4 GB.
  These theorems are stated for `fuel = 300`, the runner's `-fuel` (`run.sh`,
  `TheoremsAArch64`): certification explores up to `fuel` steps and its
  visited set ignores the remaining fuel, so `succs` is not monotone in
  `fuel` and the theorem is not claimed for other values. The witnesses for
  `msqueue_relaxed2` and `treiber2_relaxed` come from an explorer run with
  `-promises 1` (the unbounded run exceeds 600 s); each step is still a
  `succs` step of the unbounded relation, so the theorem is unaffected.

## Declarations in the AArch64 whole-image theorems

The `.kl` runner gives every configuration the declarations
`Decls.ofInit initMem cells (unsizedDefault := !sized)`. Before the AArch64 declarations proofs the
AArch64 whole-image theorems (`EnvG/A64Whole*.lean`) started from
`decls = {}`, so they were not about the runner's configuration.

- **Typed headers.** 21 AArch64 headers (README, "Typed headers and
  runner-exact theorems") type their shared symbols, which makes the runner's
  declarations strict sized (`Decls.StrictSized`, `EnvG/A64DeclsCommon.lean`).
  Explorer verdicts and configuration counts are unchanged. Cells reached
  only by offset (`n+8`, spsc `buf+8`) stay undeclared, and an undeclared
  access resolves as it does at `decls = {}`.
- **Bridge** (`EnvG/A64DeclsBridge.lean`). `exec_reresolve`: for strict sized
  `ds`, `isa.exec` at `decls = ds` is the `decls = {}` tree re-resolved
  against `ds` (`EvTree.reresolve`). A mixed-size access becomes a fault.
  - Side condition: `Executable.noPairs e` (no `LDXP`/`STXP`), decided.
    A pair effect is one `2w`-byte access when the pair is a declared
    location (`pairIsOneLoc`) and two `w`-byte accesses at `decls = {}`, so
    it does not re-resolve node by node. `LDP`/`STP` are two plain accesses
    and `CASP` resolves each half, so neither needs the condition. No LockFree
    example uses `LDXP`/`STXP`; a program that does is not covered.
- **D forms** (`EnvG/A64DeclsLink.lean`). `QA64MD` (`QA64M` at
  `st.noDecls` with `st.decls = ds`) and D variants of the link families TU,
  T, plain, FC, FCAdj and TRC. Also `RelPureSpec.HoldsD` with
  `final_of_relPureSafely{,F,S}D`.
- **Runner-exact companions** (`EnvG/A64Whole*Runner.lean`, glue in
  `EnvG/A64DeclsRunner.lean`):
  - Theorems: `treiber_pp_envG_runner`, `treiber2_envG_runner`,
    `msqueue{1,2,3}_envG_runner`, `mp_relay3_envG_runner`,
    `mp_relay3_swpl_envG_runner`, each with a `_concrete` instance.
  - The statement takes `ds` with `ds.StrictSized` and the thread start
    predicates at `decls = ds` (`WithDeclsD`).
  - Each concrete instance starts from `Config.init` of the runner's threads
    (decls included) and the runner's initial memory. A `runnerIsD`
    `#guard_msgs #eval` compares that configuration with the runner's
    (decls and memory), which is not a kernel proof. The `runnerMatches*`
    checks of the `decls = {}` theorems compare code only.
  - the AArch64 runner-exact proofs added the rest (`EnvG/A64*Runner.lean`):
    `treiber2_nodes_envG_runner`, `a64_spsc_envG_runner`,
    `cas_counter_envG_runner`, `swpl_counter_envG_runner`,
    `ticket_counter_envG_runner` and `ticket_al_counter_envG_runner`. Each
    has a `_concrete` instance, or `_concrete2`/`_concrete3` for the
    two- and three-thread `.kl` files. The counters keep their
    any-`N`-thread form, with `WithDeclsD ds (StartState …)` for every
    thread.
  - the `treiber2_arm` proof added `treiber2_arm_envG_runner` with `_concrete`
    (`EnvG/A64Treiber2ArmRunner.lean`); its header is typed as
    `treiber2.kl`'s, with the same declarations and initial memory.
  - the AArch64 runner-exact proofs also added D forms of three more link families in
    `EnvG/A64DeclsLinkMore.lean`: RC (`EnvGC`, used by swpl), TD (`EnvGTD`)
    and TDR (`EnvGTDR`, both used by the ticket locks).
  - For the ticket locks, `DispSpec.HoldsD`/`dispSpec_stepD` are added
    (`EnvG/DispenserPureA64.lean`) and `ticket_counter_ofD`
    is `ticket_counter_of` at `HoldsD` (`EnvG/A64TicketRunner.lean`). Both,
    and the x64 `ticket_counter_ofX`, are instances of the generic
    `TicketLock.ticket_counter_core` (`EnvG/TicketCounterCore.lean`); their statements are unchanged.
  - New concrete: `ConcreteTicketD` for the `ldadda` worker of
    `ticketlock{2,3}.kl`. No concrete instance existed before; the existing
    files only had `runnerWhole`.
  - the SWP runner proofs closed **`spinlock_swp{2,3}`**. Its existing proof
    (`SwpFinal.swp_counter_armv8`, `SwpPublic.swp_counter_public`) is on
    the older pre-EnvG cell route, whose cell lemmas go through
    `exec_eq_of_codeAt`'s `decls = {}`, and has no `QA64*` invariant to
    build a D form from. The SWP runner proofs added a new EnvG proof of the same worker,
    `SwpEnvG.swp_counter_envG` (`EnvG/SwpEnvG*.lean`), with the existing
    public statement verbatim (`swp_counter_envG_type_eq`). It runs on the
    swpl lock's `EnvGC`, with the swpl table and VCs; the only new VC is
    the `stlr` release, `vc_stlr`. From it come
    `swp_counter_envG_runner` with `_concrete2`/`_concrete3`
    (`EnvG/A64SwpRunner.lean`). The existing cell-route theorems are
    unchanged.
  - Also not covered here: the x64 files, which have their own runner-exact
    companions (`EnvG/X64_KNOWN_GAPS.md`); and mp / mp_fence.
    mp and mp_fence have no AArch64 `.kl` and therefore no runner.
- **No-fault is not covered.** The `_noFault` rules stay at `decls = {}`.
  Declarations restrict faults, and a fault is a `W` law, so a separate
  argument is needed (as on x64).
  - the AArch64 no-fault-at-declarations proofs added it for the fixed-layout programs
    (`EnvG/A64NoFaultD*.lean`): `cas`, `swpl`, `ticket`, `ticket_al`
    (`*_counter_envG_runner_noFault`; the SWP runner proofs added `swp` in
    `EnvG/A64SwpNoFault.lean`, with the program-level
    `swp_counter_envG_runner_faultFree`), `mp_relay3(_swpl)` (one theorem per
    role) and `spsc` (producer and consumer), each with a `_concrete`
    instance. The theorems are about new rules (`…_declsA`, built by the
    `…MAD` link wrappers), with the same `B` as the existing `…_decls` rules,
    whose invariant adds `AddrSafeA S` (a `Safely` run of the thread's text
    in `SharedEnv.invTop S`, which accepts only accesses to a word of `S`).
    The existing rules are unchanged: their invariant (`QA64MD`) has no layout,
    so their no-fault at `decls = ds` does not follow from it.
  - The no-fault needs `ds.AgreesOnA S`: each word of `S` resolves under
    `ds` as under `{}`. An undeclared word agrees (spsc `buf+8`).
  - Was open (closed by the AArch64 fault-freedom proofs, next item): the pointer programs (`treiber*`, `msqueue*`), which need a
    value-set invariant, and a program-level `FaultFree` at
    `decls = ds` (a `decls = ds` form of the `ThreadSpec.Holds` route).
  - the AArch64 fault-freedom proofs proved program-level `Config.FaultFree` at `decls = ds` (any
    architecture, promises included, the existing `Config.FaultFree`
    unchanged) for all 7 fixed-layout families and the pointer programs
    `treiber_pp`, `treiber2`, `treiber2_nodes`, `msqueue{1,2,3}`
    (`*_runner_faultFree`, each with a `_concrete` instance at the runner's
    declarations and initial memory). Route: `a64_faultFree_of_valSpecs`
    (`EnvG/MemValsA64.lean`): one value specification (`ValSpecA`, a
    `QA64MD` run in `SharedEnv.inv S G`) per thread, `G` of the value-invariant fault-freedom proofs form
    `L l → V v`, `ds.AgreesOnA S` and `MemVals L V` of the initial memory.
    Fixed layouts use `G = ⊤` and the AArch64 no-fault-at-declarations proofs' address runs
    (`EnvG/A64FaultFreeFixed.lean`); the pointer programs have value runs
    (`EnvG/MemValsA64{TreiberPP,Treiber2,Treiber2Nodes,MsQueue,MsQueue23}.lean`).
    - The neutral the value-invariant fault-freedom proofs core is reused through `ValXA`
      (`EnvG/MemValsA64Core.lean`), a weakening of `ValX` that also accepts a
      store with `b = false` when it is exclusive: `inv S G` admits a failed
      store-exclusive at any value. A non-exclusive store never reports
      `b = false` (`runTree`'s `fail` list is empty for `xcl = false`).
      The `ValXA` lemmas are now the generic forms, in the neutral
      `EnvG/MemValsGen.lean`, and the value-invariant fault-freedom proofs' `ValX` lemmas are their
      instances (`ValX.toValXA`).
    - msqueue: as on x64, the null node's link (`0 + 8`, 8 bytes) is in the
      layout: a value invariant cannot exclude `head = 0`/`tail = 0`, so the
      proof covers that load. It is undeclared and overlaps no declaration of
      the runner.
    - Phase-1 limit as everywhere: single-access trees.
  - the runner-exact fault-freedom proofs added `treiber2_arm` (the Arm-minimal Treiber stack; push `ldr`/
    `casl`, pop `ldar`/`cas`): `Treiber2Arm.treiber2_arm_envG_runner_faultFree`
    with `_concrete` (`EnvG/MemValsA64Treiber2Arm.lean`). The value invariant
    is treiber2's (reused): `top` and both links hold `0`, `n0` or `n1`.
    Access kinds do not matter to the value environment.
  - the runner-exact fault-freedom proofs also added `*_runner_safe_faultFree` (with `_concrete` or
    `_concreteN`) for every AArch64 family that has both a runner-exact
    safety theorem and a `*_runner_faultFree`: the existing runner conclusion
    (for every final configuration reachable under `Arch.armv8`) ∧
    `Config.FaultFree`, at the union of the two theorems' hypotheses
    (`EnvG/RunnerSafeFFA64.lean`; x64 twins in `EnvG/RunnerSafeFFX64.lean`).
    These are pairs of the existing theorems, with no new reasoning.
- **SwpConcrete.** `SwpConcrete.lean`'s `runnerDecls` check, which compared
  `decls = {}` with the runner's declarations of the untyped
  `spinlock_swp2.kl`, now evaluates to `false` (the header is typed). The new
  `runnerDeclsSized` check compares against the sized declarations and
  evaluates to `true`.
- **Lake does not track `include_str`.** After editing a `.kl`, delete the
  oleans of the modules that `include_str` it (the `*Concrete.lean`,
  `A64LiveTests`, `A64WholeCounters`, `SwpConcrete`, `TheoremsAArch64`).
  Otherwise the `#guard_msgs` comparisons run against the stale text.

## Liveness (LIVEPF)

Ticket-lock liveness (Stage 3, `Promising/LiveTicket.lean`):

- **Proved, promise-free fragment, valid layouts:**
  `Live.TicketPF.ticket_live_pf [ValidLayout (layout tkWorker)] : TicketLivePF fuel`
  (`Promising/LiveTicketPF.lean`), for any number `N` of workers
  (`N + 1 < 2^32`), under `WeakFair ∧ MemFair ∧ PromiseFree`; concrete
  `ticket_live_pf_concrete` at the `fakeSize` layout. The invariant is
  `Live.TicketInv.InvW` (`Promising/LiveTicketInv.lean`).
- **The `ValidLayout` hypothesis is needed.** On an invalid layout a single
  thread can spin forever: a `B.NE` cell of size `2^64 - 8` makes its
  fall-through address wrap back to the `LDAR`, so the thread never reaches
  the critical section whatever `owner` holds. `TicketLivePF` quantifies over all layouts, so it is
  proved here only under the hypothesis (option (a)).
- **Hardware basis for `MemFair`:** Arm ARM (DDI 0487) B2.7.1 "Normal memory": "A write to a memory location with the Normal attribute completes in finite time" (verbatim in issues C.a and G.a; C.a adds that it "is globally observed for the shareability domain … in finite time", a sentence removed in later issues with the axiomatic memory model). (Verified
  against both PDFs. An earlier version of this entry attached an unverified
  "Arm ARM B2" citation to the invalid-layout sentence by mistake.) x86: no SDM sentence guarantees eventual visibility (checked: Intel SDM Vol. 3A, order no. 253668-090US, Feb 2026); `MemFair` is a modelling assumption (store buffers drain in finite time, as in x86-TSO). Qualitative support, same revision: §14.10 "Store Buffer" (§11.10 in older revisions): processors "temporarily store each write (store) to memory in a store buffer" and "the existence of the store buffer is transparent to software, even in systems that use multiple processors"; it lists only the events that always drain the buffer (exceptions/interrupts, serializing and I/O instructions, LOCK, BINIT, SFENCE, MFENCE), not a finite-time bound. §11.2.3.5: a store is "temporarily held in a processor's store buffer".
- **Weak fairness alone is not enough:** `Live.TicketCexG.ticketLiveWF_false`
  (`Promising/LiveTicketCexG.lean`, generic lasso `lasso_not_live`) and
  `Live.TicketCex.ticket_not_live_weakFair`.
- **Open:** `TicketLive` (promises allowed). `WeakFair → WeakFairInstr` with
  promises needs `DropBounded` (`Promising/LiveWfInstr.lean`,
  `weakFairInstr_of_weakFair`); the promise-free proof uses
  `weakFairInstr_of_promiseFree` instead. With promises, the waiter's view
  argument (memory fairness, then the next `LDAR` reads the last write) also
  needs the promise-certification invariant, not done.
- **Promise-emptying lemma and semantic ticket-lock liveness.**
  - `DropBounded` for `tkWorker` (bound 1): `Live.TicketDrop.weakFairInstr_ticket`
    (`Promising/LiveTicketDrop.lean`).
  - **Proved, fuel 0:** `Live.TicketZero.ticket_live_zero [ValidLayout] :
    Ticket.TicketLive 0` (`Promising/LiveTicketZero.lean`): at fuel 0
    `certify` finds no write, so every trace is promise-free.
  - **Proved, semantic certification:** `Live.TicketSem.ticket_live_sem
    [ValidLayout] (fuel) : TicketLiveSem fuel` and `ticket_live_sem_concrete`
    (`Promising/LiveTicketSem.lean`, invariant `Live.TicketInvP.InvP`). This
    is a new statement beside `TicketLive`: it uses the machine of
    `Promising/LiveSem.lean`, where a step of a thread with promises requires
    `CertOkN` (certifiable within `fuel` instructions), under `WeakFairSem ∧
    MemFair`. The reason: `certify.go`'s visited set ignores the remaining fuel,
    so `certify` is incomplete. The existing `TicketLive fuel` is a statement
    about that search and may be false.
  - **Still open: `TicketLive fuel` for `fuel ≥ 1`.** Evidence, not proof: an
    exhaustive BFS over the unreduced `succs` found no witness of
    non-liveness. Runs: `TkStart`, n = 2 at fuel 2–12; n = 3 at fuel 7–12 with
    restricted promises; n = 3 at fuel 9 with all threads promising the
    counter (118k configurations). No waiter was ever stuck. The only
    disabled threads hold no ticket. They carry a counter promise that
    assumed a ticket they then lost to another thread, and they block nobody.
    Probable reason: `certify.go` tries the newest read first (its `foldl`
    prepends, and `readSuccs` lists timestamps in ascending order). So the
    holder's latest-`owner` read is searched before any looping path, and the
    fuel-blind pruning never removes the only certification.
- **Runner declarations:** the promise-free ticket-lock theorems
  are also proved for the `.kl` runner's workers (`decls = ds`); see
  "Liveness: runner declarations (LIVERUN)".
- **The `ldaddal` ticket lock
  (`ticketlock_al2/3.kl`, worker `tkWorkerAl`) has the same table.** Explicit
  statements in `Promising/LiveTicketAlThm.lean` (namespace `Live.TicketAl`,
  statement defs `TkStartAl`/`TkWaitingAl`/`TkDoneAl`/`TicketAlLive*` in
  `Promising/LiveTicketAl.lean`):
  - executable machine (`succs`/`TraceS`), `WeakFair ∧ MemFair ∧
    PromiseFree`: `ticket_al_live_pf [ValidLayout (layout tkWorkerAl)]`,
    `ticket_al_live_pf_concrete` (at `ConcreteTicketAl.tkAlLayout`);
  - semantic machine (`CertOkN`/`TraceSem`), `WeakFairSem ∧ MemFair`:
    `ticket_al_live_sem [ValidLayout]` for every fuel, `ticket_al_live_sem_concrete`;
  - weak fairness alone refuted (executable machine): `ticketAlLiveWF_false`
    (the lasso schedule of `LiveTicketCex` replayed on `tkWorkerAl`, kernel
    checks re-run);
  - runner forms: `ticket_al_live_{pf,sem}_runner{,_concrete,N}` (start
    structure `TkStartAlD ds`: `Decls.AgreesAt`, no `Sized`, no `prom = []`).
  - **Still open:** `TicketAlLive fuel` for `fuel ≥ 1` (executable machine,
    promises allowed), exactly as `TicketLive`.
  - **How (source-level instantiation, nothing assumed).** `tkWorkerAl`
    differs from `tkWorker` in one cell (`LDADDA` → `LDADDAL`), and every step
    lemma the `ldadda` chain applies to the ticket RMW is generic in the RMW
    kind (`spec_rmw`, `spec_rmw_p`, `replay_rmw`, `en_rmw`, `spec_rmw_len`).
    The command `#ticket_al_clone` (`Promising/LiveTicketAlClone.lean`) reads
    an existing `LiveTicket*.lean` / `LiveRunner*A64Ticket.lean` source, applies
    a fixed list of whole-word substitutions (`ticketAlSubst`: `tkWorker` →
    `tkWorkerAl`, `StartState` → `StartStateAl`, `.rmw .acq` → `.rmw .acqRel`,
    namespaces `TicketX` → `TicketAlX`, statement and theorem names) and
    elaborates the result in the clone module (`LiveTicketAl{Trees,Inv,Drop,
    Solo,InvP,PF,Sem,CexG}.lean`, `LiveRunner{,Sem}A64TicketAl.lean`). Every
    cloned declaration is elaborated and kernel-checked again, as if written
    out; it is an instantiation of the proof text, not an assumption, and no
    existing file changed. Each clone module imports its original, so lake
    rebuilds it when the original changes. The release half of `LDADDAL` only
    raises the RMW's write bound and views, which none of these lemmas
    inspects.
- **Fairness witnesses: the fairness hypotheses are
  satisfiable.** Each liveness theorem quantifies over fair traces from a
  start configuration, so it would be vacuous if there were none.
  `Live.Witness.fair_exists` and `fairSem_exists`
  (`Promising/LiveSemWitness.lean`, ISA-neutral) build a round-robin trace.
  At each step it steps the next thread that has not halted, with an outcome
  that reads the newest message and leaves no promise; once every thread has
  halted it repeats the (final) configuration. That trace is a `TraceS` at every fuel with `WeakFair`, `WeakFairInstr`,
  `PromiseFree` and `MemFair`, and a `TraceSem` with `WeakFairSem`,
  `WeakFairInstrSem` and `MemFair`. These are the existing definitions,
  unchanged. They need `Progressive`: at every configuration reachable by
  such steps, every thread that has not halted has such an outcome.
  `progressive_of_inv` reduces `Progressive` to the existing lock invariant,
  plus one shape lemma per pc (`goodT_done/choose/store/load/ldst/rmw`).
  Forwarded reads also need a new instruction invariant, `FwdLeCoh` (a
  forwarding entry is at most the coherence view). For these locks
  `Progressive` excludes no behaviour: with no promise, the last write is
  always readable. Instances (`Promising/LiveSemWitnessA64.lean`, under
  `ValidLayout`, at the `TkStart`/`CasStart`/`SwpStartG` start
  configurations):
  - `Live.WitnessA64.tk_fair_exists` / `tk_fairSem_exists`;
  - `cas_fair_exists` / `cas_fairSem_exists`;
  - `swp_fair_exists` / `swp_fairSem_exists` (any `SwpCode P`);
  - `swpWorker_*` and `swplWorker_*` (SWP, SWPL).

  **Done:**
  - the x64 instances (`Promising/LiveSemWitnessX64.lean`, executable
    machine `Arch.tso`; a forwarded load is newest by `FwdLeCoh`, so
    `Progressive` excludes nothing here either):
    `Live.WitnessX64.cmpx_fair_exists` / `cmpx_fairSem_exists`
    (`CmpxStart`), `xchg_*` (`XchgStart`), `tkX_*` (`TkStartX`, store
    release) and `tk2X_*` (`Tk2StartX`, `incl` release, a load-store by
    `goodT_ldst`);
  - the `ldaddal` ticket lock (`Promising/LiveSemWitnessTicketAl.lean`):
    `Live.WitnessTicketAl.tkAl_fair_exists` / `tkAl_fairSem_exists`
    (`TkStartAl`, at the cloned `TicketAl` invariant);
  - the runner-declaration starts (`decls = ds`), as `Progressive`:
    `Live.Witness.progressive_of_mapC` (`Promising/LiveSemWitnessRunner.lean`,
    ISA-neutral) transfers `Progressive` back along `State.noDecls`
    (`RunnerSim.ExecSim`), giving `*_progressive_runner` at `CmpxStartD`,
    `XchgStartD`, `TkStartXD`, `Tk2StartXD` (`LiveSemWitnessX64.lean`),
    `TkStartD`, `CasStartD`, `SwpStartGD` (`LiveSemWitnessA64Runner.lean`)
    and `TicketAl.TkStartAlD` (`LiveSemWitnessTicketAl.lean`). The fair
    traces are then `fair_exists (*_progressive_runner hs) (startPF_init _ _)`
    (resp. `fairSem_exists`); the 16 `*_fair_exists_runner` statements are
    not written out.

## Liveness: spinlocks (LIVESPIN)

Spinlock liveness (Stage 3, `Promising/LiveSpin.lean`). The property for a
test-and-set/CAS lock is **deadlock-freedom** (`Live.Spin.ProgressFrom`): if
some thread waits, some thread that is not yet done is later done.
Starvation-freedom of such a lock is false in general (with re-acquiring
clients a fair scheduler can let one thread lose every race), so it is not
stated.

- **Proved, AArch64 CAS spinlock (`spinlock_cas2/3.kl`), promise-free
  fragment, valid layouts:** `Live.SpinCasPF.spin_cas_live_pf
  [ValidLayout (layout casTtasWorker)] : CasSpinLivePF fuel`
  (`Promising/LiveSpinCasPF.lean`), any number of workers, under
  `WeakFair ∧ MemFair ∧ PromiseFree`; concrete `spin_cas_live_pf_concrete`.
  The invariant (`Live.SpinCasInv.InvC`) is only "a non-zero lock has a
  holder": a writing `CASA` makes its thread a holder, and the holder's
  `STLR` writes `0`. No mutual exclusion or atomicity is used.
- **Per-thread, one-shot workers:** `spin_cas_live_oneShot_pf :
  CasSpinLiveOneShotPF fuel` (every waiting thread is eventually done). This
  holds because each worker takes the lock once and halts (the set of
  finished threads grows only finitely often); it is a property of these
  programs, not starvation-freedom of the lock.
- **Proved, AArch64 SWP spinlocks, promise-free fragment,
  valid layouts:** `Live.SpinSwpFam.spin_swp_live_pf
  [ValidLayout (layout swpWorker)] : SwpSpinLivePF fuel` (`spinlock_swp2/3`,
  `SWPA` lock, `STLR` unlock) and `spin_swpl_live_pf
  [ValidLayout (layout swplWorker)] : SwplSpinLivePF fuel`
  (`spinlock_swpl2/3`, `SWPA` lock, `SWPL` unlock), with the one-shot
  corollaries `spin_swp(l)_live_oneShot_pf` and concrete instances
  (`Promising/LiveSpinSwpFam.lean`). Both from one generic proof
  (`Live.SpinSwpPF.swp_live_pf_gen`, any program with `SwpCode P`). A
  failing `SWPA` writes, so the invariant (`Live.SpinSwpInv.InvS`) adds
  "a thread's own lock writes are at or below its coherence view of the
  lock"; with RMW atomicity every swap reads the last write
  (`Live.SpinSwpStep.spec_swp`). The start states are those of the safety
  theorems (`SwpPublic.StartState`, `SwplLock.StartState`).
- **Open:** `CasSpinLive`, `SwpSpinLive`, `SwplSpinLive` (promises allowed;
  same obstacles as `TicketLive`, see "Liveness (LIVEPF)"); x64
  (`spinlock2/3`, `spinlock_cmpxchg2/3`).
- **Runner declarations:** the promise-free CAS/SWP/SWPL theorems
  are also proved for the `.kl` runner's workers (`decls = ds`); see
  "Liveness: runner declarations (LIVERUN)".
- **Semantic CAS spinlock liveness proof.**
  - **Proved, CAS spinlock with promises, semantic certification:**
    `Live.SpinSemCas.spin_cas_live_sem [ValidLayout (layout casTtasWorker)]
    (fuel) : Live.SpinSem.CasSpinLiveSem fuel`, concrete
    `spin_cas_live_sem_concrete` (at `SpinCasPF.casLayout`), and the one-shot
    corollary `spin_cas_live_oneShot_sem : CasSpinLiveOneShotSem fuel` (with
    concrete instance), in `Promising/LiveSpinSemCas.lean`. The statements
    (`Promising/LiveSpinSem.lean`, deadlock-freedom `ProgressFromSem`) have the
    start configurations, `CasWaiting` and `CasDone` of `CasSpinLive`, over the
    machine of `Promising/LiveSem.lean` (a step of a thread with promises needs
    `CertOkN`) under `WeakFairSem ∧ MemFair`, as `TicketLiveSem`.
  - The invariant (`Live.SpinSemInv.InvS`) classifies a certifiable worker's
    promises (`Live.SpinSemSolo.Good`): an *acquire* promise (lock, non-zero)
    belongs to a thread in its try/spin loop; a counter promise to a thread up
    to its `STR`; a *release* promise (lock, `0`) to a thread up to its `STLR`,
    above its `vwOld`, and, in the loop, together with an acquire promise.
    Every promise is above the thread's coherence view. A thread out of the
    loop, or with an acquire promise, certifies without fresh writes and is
    always instruction-enabled. A non-zero lock's last write is still promised
    by its writer, or the writer holds the lock with the write in its
    coherence view. A thread in the loop with only a counter promise may be
    unable to certify; the proof never needs it to step (a thread that steps
    infinitely often takes infinitely many instruction steps, by the drop
    bound, and it spins and acquires).
  - **Still open: `CasSpinLive fuel`** (over `succs`): the `certify` search is
    incomplete (fuel-blind visited set), as for `TicketLive`.
  - **Still open: `SwpSpinLive`, `SwplSpinLive`** (over `succs`): the
    `certify` search is incomplete, as for `CasSpinLive`. Their semantic
    versions are now proved (see below).
- **Semantic SWP spinlock liveness proof.**
  - **Proved, SWP spinlocks with promises, semantic certification:**
    `Live.SpinSemSwpLive.spin_swp_live_sem [ValidLayout (layout swpWorker)]
    (fuel) : Live.SpinSemSwp.SwpSpinLiveSem fuel` (`spinlock_swp2/3`, `SWPA`
    lock, `STLR` unlock) and `spin_swpl_live_sem [ValidLayout (layout
    swplWorker)] (fuel) : SwplSpinLiveSem fuel` (`spinlock_swpl2/3`, `SWPA`
    lock, `SWPL` unlock), the one-shot corollaries
    `spin_swp(l)_live_oneShot_sem`, and concrete instances
    `spin_swp(l)_live_sem_concrete`, `spin_swp(l)_live_oneShot_sem_concrete`
    (at `SpinSwpFam.swpLiveLayout`/`swplLiveLayout`, no hypothesis left), in
    `Promising/LiveSpinSemSwpLive.lean`. The statements
    (`Promising/LiveSpinSemSwp.lean`) are those of `SwpSpinLive`/
    `SwplSpinLive` (start configurations, `SwpWaitingG`, `SwpDoneG`) over the
    `LiveSem` machine under `WeakFairSem ∧ MemFair`.
  - One generic proof (`swp_live_sem_gen`, `swp_live_oneShot_sem_gen`) for any
    program with `SwpCode P` and `RelR P`: the release is a *release* write
    (`STLR`, or a release RMW such as `SWPL`). `SwpCode.rel` also admits a
    plain RMW, whose release promise could be certified before the counter
    store (no `vwOld` bound), so the release-promise class fails. `RelR` is
    discharged for both programs (`relR_swp`, `relR_swpl`).
  - A failing `SWPA` writes, so the CAS invariant ("the last lock write is
    owned") is false. The invariant (`Live.SpinSemSwpInv.InvS`) says instead:
    above the last zero of the lock, the *first* lock message is a promise of
    its writer, pinned to that zero (`SpinSemSwpSolo.AcqAt`: the writer did
    not write the zero, and no lock write lies between), or its writer holds
    the lock with the message in its coherence view. By atomicity, the swap
    that fulfils a pinned promise reads the zero, so it acquires
    (`read_zero_gap`). Also: each thread's own writes of `0` to the lock are
    its promises, or the thread is past its release. Liveness: no holder and
    no pinned promise stays forever (as for CAS), so from then on every lock
    message is at or below a zero (`no_above`). New lock messages are then
    zeros, and a spinner that catches up with the last zero reads `0` at its
    `LDR` and at its `SWPA`.
  - Generic lemmas worth hoisting: `SpinSemSwpSolo.ZeroAt/ZNot/Gap/TopZ` and
    their `mono`/`back`, `read_zero`, `read_zero_gap`, `run_swp_p`,
    `spec_swp_p`, `spec_load_w`; `SpinSemSwpLive.exists_least`/
    `exists_greatest`. Also `threadNPn_prefix`/`NACert` (copies of
    `SpinSemSolo`'s). `LiveSpinSemSwpLive` uses `SpinSemCas`'s trace lemmas
    at `casLayout`, because they carry an unused layout instance of
    `casTtasWorker`.
  - **x64 (not done):** `LiveSem` and the trace lemmas of `LiveSpinSemCas`
    (`inf_pigeon`, `instr_inf`, `adv`) are ISA-generic. The RMW lemmas of
    `LiveSpinSemShape` (`spec_rmwo_p`, `replay_rmwo`, `SpinStep.en_rmwo`)
    assume `A.rmwFence = false`; x64's locked `CMPXCHG`/`XCHG` have
    `rmwFence`, so they need fenced variants, plus x64 copies of the
    solo-run (`Good`, `NACert`) and invariant layers for the `.kl` workers.

## Liveness: spinlocks, x64 (LIVESPINX)

The x64 counterpart of "Liveness: spinlocks (LIVESPIN)", same property
(deadlock-freedom, `Live.SpinX64Step.ProgressFromN`, an ISA-neutral copy of
`Live.Spin.ProgressFrom`) and the same proof shape, under `Arch.tso`.

- **Proved, x64 `lock cmpxchg` spinlock (`spinlock_cmpxchg2/3.kl`),
  promise-free fragment, valid layouts:** `Live.SpinX64CmpxPF.spin_cmpx_live_pf
  [ValidLayout (layout cmpxImageV)] : CmpxSpinLivePF fuel`
  (`Promising/LiveSpinX64CmpxPF.lean`), for the verbatim worker in its image
  (absolute `(lock)`/`(counter)`, `decls = {}`, the start of
  `CmpxAbs.x64_cmpx_counter_envG_verbatim`), any number of workers, under
  `WeakFair ∧ MemFair ∧ PromiseFree`. At the `.kl` runner's layout:
  `spin_cmpx_live_pf_concrete`, and `spin_cmpx_live_pf_runnerN` from `N`
  copies of the runner's prepared worker and initial memory. Per-thread
  liveness of these one-shot workers: `spin_cmpx_live_oneShot_pf` (not
  starvation-freedom of the lock). Invariant `Live.SpinX64CmpxInv.InvX`: "a
  non-zero lock has a holder" (a failing `cmpxchg` writes nothing).
- **TSO RMW steps:** `Promising/LiveTsoRmw.lean` (generic, lock-agnostic):
  the `rmwFence = true` versions of the RMW step lemmas (the fences change
  views only), with the read logged, coherence views monotone, and
  `rmw_reads_last` (an atomic RMW reads the last write when the thread's own
  messages to the location are within its coherence view).
- **`MemFair` is still needed on TSO**: the RMW's fences do not raise the
  coherence view of the lock, which is what bounds a waiter's read. On x86
  `MemFair` is a modelling assumption (finite store-buffer drain, x86-TSO;
  see the `MemFair` docstring in `Promising/LiveTrace.lean`).
- **Not covered:** the runner's declarations (`decls = ds`; the trees go
  through `X64.exec_eq_of_codeAt`, which needs `decls = {}`), as for the
  safety theorems' whole-image form. Now covered, for both x64 spinlocks, by
  "Liveness: runner declarations (LIVERUN)".
- **Proved, x64 `xchg` spinlock (`spinlock2/3.kl`),
  promise-free fragment, valid layouts:** `Live.SpinX64XchgPF.spin_xchg_live_pf
  [ValidLayout (layout spinImageV)] : XchgSpinLivePF fuel`
  (`Promising/LiveSpinX64XchgPF.lean`), for the verbatim test-and-test-and-set
  worker in its image (the start of `SpinAbs.x64_spin_counter_envG_verbatim`),
  any number of workers, under `WeakFair ∧ MemFair ∧ PromiseFree`; waiting =
  positions 1–7 (plain-load spin, `xchgl`, its test), done = past the
  `movl $0,(lock)` release. At the runner's layout:
  `spin_xchg_live_pf_concrete`, `spin_xchg_live_pf_runnerN`; one-shot
  per-thread `spin_xchg_live_oneShot_pf(_concrete)` (not starvation-freedom).
  A failing `xchg` writes `1`, so the invariant
  `Live.SpinX64XchgInv.InvX` adds the swap-lock liveness proof's `OwnLe` ("a thread's own lock
  messages are at or below its coherence view of the lock"): every `xchgl`
  then reads the last write (`TsoRmw.spec_rmwo_tso`'s `rmw_reads_last`
  clause), and "a non-zero lock has a holder" is kept (a swap reading
  non-zero leaves the existing holder in place). The plain-load spin needs
  `MemFair`, as the `cmpxchg` waiter's read does.
- **Open:** `CmpxSpinLive`/`XchgSpinLive` (promises allowed).
- **Semantic x64 `lock cmpxchg` spinlock liveness proof, `lock cmpxchg` spinlock with
  promises, proved, semantic certification:**
  `Live.SpinX64SemCmpx.spin_cmpx_live_sem [ValidLayout (layout cmpxImageV)]
  (fuel) : SpinX64Sem.CmpxSpinLiveSem fuel`, the one-shot corollary
  `spin_cmpx_live_oneShot_sem`, and `spin_cmpx_live_sem_concrete`/
  `spin_cmpx_live_oneShot_sem_concrete` at the runner's layout `cmpxLayoutV`
  (no hypothesis left), in `Promising/LiveSpinX64SemCmpx.lean`. The statements
  (`Promising/LiveSpinX64Sem.lean`) are those of `CmpxSpinLive`/
  `CmpxSpinLiveOneShot` (start configurations `CmpxStart`, `CmpxWaiting`,
  `CmpxDone`) over the machine of `Promising/LiveSem.lean` (a step of a thread
  with promises needs `CertOkN`) under `WeakFairSem Arch.tso ∧ MemFair
  Arch.tso` (`FairX`), for every fuel, any number of workers. `MemFair` on
  x86 is a modelling assumption, as above.
  - **TSO shortcut (proved, generic):** on TSO a thread with outstanding
    promises certifies without fresh writes
    (`SpinX64SemShape.nacertG_of_tsoW`, for any program whose steps satisfy
    the per-step property `TsoW` under a step invariant): every store is a
    release, so a fresh write raises `vwOld` past `|M|`, hence past every
    outstanding promise, and every fulfilment needs `vwOld < ts`. So every
    worker not at its end is always instruction-enabled, weak fairness
    applies to the waiting thread directly, and the AArch64 proof's
    pigeonhole over stepping threads, `instr_inf`, and the classes of
    possibly uncertifiable threads are not needed.
  - Pieces: `SpinX64SemShape.spec_rmwo_p_tso`/`replay_rmwo_tso` (fencing
    conditional RMW with promises; the fulfilment keeps `vwOld < ts`),
    `TsoW`/`nacertG_of_tsoW`; solo runs `SpinX64SemCmpxSolo` (`SInv`, `Good`,
    `step_solo`/`Eff`, `NACert.replay`, `instrEnabledSem_of`); invariant
    `SpinX64SemCmpxInv.InvS` ("a non-zero lock's last write is still promised
    by its writer, or the writer holds the lock with the write in its
    coherence view", every promise above the coherence view, `NACertG`);
    `SpinX64SemCmpx.spec_rmwo_p_log` (a fencing RMW logs its read with any
    promise set, for `reads_inf` of a thread holding an acquire promise).
  - **** `LiveSpinX64SemShape.lean` (whole file: `spec_rmwo_p_tso`,
    `spec_choose_vw`, `replay_rmwo_tso`, `TsoW`, `nacert_of_tsoW`,
    `nacertG_of_tsoW`); `SpinX64SemCmpx.writeSuccs_log`/`spec_rmwo_p_log`;
    `SpinX64SemCmpxSolo.replay_choose`.
  - **Still open: the existing `CmpxSpinLive fuel`/`XchgSpinLive fuel`**,
    stated over `succs`, whose certification search `certify` is incomplete,
    exactly as for `CasSpinLive`/`TicketLive`. **Not done (follow-up
    the semantic x64 `xchg` liveness proof):** `xchg` with promises; its statements
    `SpinX64Sem.XchgSpinLiveSem`/`XchgSpinLiveOneShotSem` are stated, not
    proved.
- **Semantic x64 `xchg` spinlock liveness proof, x64 `xchg` spinlock with promises, semantic
  machine (proved):** `Live.SpinX64SemXchgLive.spin_xchg_live_sem
  [ValidLayout (layout spinImageV)] (fuel) : SpinX64Sem.XchgSpinLiveSem fuel`
  and the one-shot `spin_xchg_live_oneShot_sem : XchgSpinLiveOneShotSem fuel`
  (`Promising/LiveSpinX64SemXchgLive.lean`), with `_concrete` (at
  `spinLayoutV`, no hypothesis) and `spin_xchg_live_sem_runnerN`. Over
  `TraceSem Arch.tso` under `WeakFairSem ∧ MemFair`, promises allowed. The
  port of the semantic swap-lock liveness proof's SWP proof: solo layer
  `LiveSpinX64SemXchgSolo.lean` (`SInv`, `Good`, `Eff`, `step_solo`; every
  certifiable worker certifies without fresh writes by the TSO shortcut
  `SpinX64SemShape.nacertG_of_tsoW`), invariant
  `LiveSpinX64SemXchgInv.lean` (`InvS`: above the top zero of the lock, the
  first lock message is a pinned promise of its writer or held; plus
  own-zero bookkeeping; a failing `xchgl` writes, so `InvX` does not carry
  over). `MemFair` on x86 stays a modelling assumption. The existing
  `XchgSpinLive` over `succs` stays **open** (incomplete `certify`). This
  closes the "Not done (follow-up the semantic x64 `xchg` liveness proof)" item of the bullet above.

## Liveness: ticket lock, x64 (LIVEX64A)

The x64 counterpart of "Liveness (LIVEPF)" for `X64/ticketlock3.kl`
(`lock xaddl` take, plain-load spin on `owner`, release with the plain store
`movl %ecx,(owner)`), same property (every waiting thread is eventually
done, starvation-freedom), under `Arch.tso`. Statements in
`Promising/LiveX64Ticket.lean` (`Live.TicketX64.TicketX64Live/PF/WF`).

- **Proved, promise-free fragment, valid layouts:**
  `Live.TicketX64PF.ticket3_x64_live_pf [ValidLayout (layout tk3ImageV)] :
  TicketX64LivePF fuel` (`Promising/LiveX64TicketPF.lean`), for the verbatim
  worker in its image (absolute `(next)`/`(owner)`/`(counter)`, `decls = {}`,
  the start states of `TicketX.ticket3_counter_envG_verbatim`), any number
  `N` of workers (`N + 1 < 2^32`), under `WeakFair ∧ MemFair ∧ PromiseFree`;
  concrete `ticket3_x64_live_pf_concrete` at the `.kl` runner's layout
  (`tk3LayoutV`). The invariant is `Live.TicketX64Inv.InvW`
  (`Promising/LiveX64TicketInv.lean`), the AArch64 `InvW` with the TSO
  `lock xadd` step; event trees in `Promising/LiveX64TicketTrees.lean`.
- **Weak fairness alone is not enough:**
  `Live.TicketX64Cex.ticketX64LiveWF_false : ¬ TicketX64LiveWF fuel` at the
  runner's layout (`Promising/LiveX64TicketCex.lean`), a kernel-checked
  lasso: with two workers, the second reads the initial `owner` forever
  while the first's release stays unread.
- **`MemFair` is still needed on TSO** (the lasso above); on x86 it is a
  modelling assumption (finite store-buffer drain, x86-TSO; see "Liveness
  (LIVEPF)" and the `MemFair` docstring in `Promising/LiveTrace.lean`).
- **Not covered:** the runner's declarations (`decls = ds`), as for
  "Liveness: spinlocks, x64 (LIVESPINX)". Now covered by "Liveness:
  runner declarations (LIVERUN)".
- **Open:** `TicketX64Live` (promises allowed; same obstacles as
  `TicketLive`).
- **Semantic x64 ticket-lock liveness proof, proved, semantic certification:**
  `Live.X64SemTicket.ticket3_x64_live_sem [ValidLayout (layout tk3ImageV)]
  (fuel) : X64Sem.TicketX64LiveSem fuel` and `ticket3_x64_live_sem_concrete`
  at `tk3LayoutV` (`Promising/LiveX64SemTicket.lean`; statement in
  `Promising/LiveX64Sem.lean`). The x64 counterpart of
  `TicketSem.ticket_live_sem` ("Liveness (LIVEPF)"): the
  same start configurations (`TkStartX`) and `TkWaitingX`/`TkDoneX`, on the
  machine of `Promising/LiveSem.lean` (a step of a thread with promises
  requires `CertOkN`), under `WeakFairSem ∧ MemFair`, for every fuel, any
  number of workers, promises allowed. Pieces: fencing RMW with promises
  (`X64SemShape.spec_rmw_p_tso`/`replay_rmw_tso`, `lock xaddl` raises `vwOld`
  past every promise), promise-agnostic step lemmas `X64SemStep.q1`–`q12`
  and `DropBounded Arch.tso 1` (`dropBounded_of_sinv`), solo runs with
  promises (`X64SemSolo.Good`/`NACert`/`nacert_replay`/`instrEnabledSem_of`),
  invariant `X64SemInv.InvP` (`inv_step`, `trace_invP`); adapted copies of
  the AArch64 `LiveTicketSolo`/`LiveTicketInvP`/`LiveTicketSem`.
  **Still open: the existing `TicketX64Live fuel`**, stated over `succs`, whose
  certification search `certify` is incomplete (`certify.go`'s visited set
  ignores the remaining fuel), exactly as for `TicketLive`.
  **Not covered:** `ticketlock2.kl` with promises (its `incl (owner)` release
  writes the value it reads plus one, so a certified `owner` promise needs
  the holder's read of `owner` to be its ticket; follow-up job).
  **** the `_tso` RMW shape lemmas of `LiveX64SemShape.lean`; the
  ISA-generic trace lemmas `step_prefix`/`prefix_le`/`get_le`/
  `same_or_instr`/`adv` and `getCoh_eq` in `LiveX64SemTicket.lean` (copies of
  `LiveTicketSem`'s).
- **`ticketlock2.kl`, proved, promise-free fragment, valid
  layouts:** `Live.Ticket2X64PF.ticket2_x64_live_pf [ValidLayout (layout
  tk2ImageV)] : Ticket2X64LivePF fuel` (`Promising/LiveX64Ticket2PF.lean`;
  statements `Live.Ticket2X64.Ticket2X64Live/PF/WF` in
  `Promising/LiveX64Ticket2.lean`, the same shape at `tk2ImageV` and the start
  states of `TicketX2.ticket2_counter_envG_verbatim`), concrete
  `ticket2_x64_live_pf_concrete` at `tk2LayoutV`. The release `incl (owner)`
  is a plain load and a plain store, not an RMW, so it writes the value it
  reads plus one; the invariant `Live.Ticket2X64Inv.InvW`
  (`Promising/LiveX64Ticket2Inv.lean`) adds "the only `owner` message with
  value `m` is the last write" and, per thread, "no forwarding entry of
  `owner` before the release" and "coherence view of `owner` at its last
  write once `m` was read" (positions 7–10), so the holder's `incl` reads
  `m`. Step lemmas for the load-then-store shape and forwarding in
  `Promising/LiveX64Ticket2Step.lean`. **Weak fairness alone is not enough:** `Live.Ticket2X64Cex.ticket2X64LiveWF_false : ¬
  Ticket2X64LiveWF fuel` at `tk2LayoutV` (`Promising/LiveX64Ticket2Cex.lean`,
  the `Lasso.Spec` lasso: the second worker reads the initial `owner` forever).
  **Open:** `Ticket2X64Live` (promises); the runner's declarations are covered by "Liveness: runner declarations (LIVERUN)". `Live.Ticket2X64Inv.getCoh_eq` (another copy of
  `LiveTicketPF.getCoh_eq`); the trees/invariant/PF files are adapted copies
  of the ticketlock3 ones.
- **Semantic x64 `ticket2` liveness proof, `ticketlock2.kl` with promises,
  proved, semantic certification:** `Live.X64Sem2Ticket.ticket2_x64_live_sem
  [ValidLayout (layout tk2ImageV)] (fuel) : X64Sem2.Ticket2X64LiveSem fuel`
  and `ticket2_x64_live_sem_concrete` at `tk2LayoutV`
  (`Promising/LiveX64Sem2Ticket.lean`; statement in
  `Promising/LiveX64Sem2.lean`, shaped like `X64Sem.TicketX64LiveSem` with the
  start configurations `Tk2StartX` and `Tk2WaitingX`/`Tk2DoneX`), on the
  machine of `Promising/LiveSem.lean` under `WeakFairSem ∧ MemFair`, for every
  fuel, any number of workers, promises allowed. This closes the "Not
  covered: `ticketlock2.kl` with promises" item of the semantic x64 ticket-lock liveness proof update
  above. Pieces: the load-then-store shape with promises
  (`X64Sem2Shape.spec_ldst_p`/`replay_ldst`: the store of `incl` appends, or
  fulfils a promise above every view, as on TSO every store is a release
  store); step lemmas `X64Sem2Step.q1`–`q11` (forwarding tracked by `FwdK`,
  the release `q10` writes `incv v` for the value `v` it reads); solo runs
  with promises (`X64Sem2Solo.Good`: a thread's `owner` promises sit at
  positions ≤ 10 and carry the value its covered read of `owner` plus one,
  `OVal`; `NACert`/`nacert_replay`/`instrEnabledSem_of`); invariant
  `X64Sem2Inv.InvP`, whose new field `omono` (`owner` values strictly increase
  with the timestamp, `omono_step`) together with the holder's own `owner`
  promise lying above its read (`InvP.oval_eq`) replaces the unique-writer
  argument of the `lock xaddl` release: the holder of `k` reads `k` and
  promises/writes `k + 1`. **Still open: the existing `Ticket2X64Live fuel`**,
  stated over `succs`, whose certification search `certify` is incomplete,
  exactly as for `TicketX64Live`/`TicketLive`. ****
  `X64Sem2Shape.spec_ldst_p`/`replay_ldst`/`le_of_writeIn` (generic
  load-then-store with promises), `X64Sem2Inv.omono_step` and the `OVal`
  pattern; the trace lemmas, `mem_erase_of_ne'`, `xv_toNat`,
  `threadNPn_prefix` copied into `LiveX64Sem2Solo/Ticket.lean` from the
  ticketlock3 files (those carry the section instance `ValidLayout (layout
  tk3ImageV)`, so they cannot be used at the ticketlock2 layout).
- **Duplicated, to be moved to a shared module:**
  `Live.TicketX64Inv.pigeon` (copy of the AArch64 one),
  `Live.TicketX64PF.getCoh_eq` (copy of `LiveTicketPF.getCoh_eq`),
  `Live.TicketX64Cex.promiseBy_prom` and the lasso
  `LassoChecksX`/`lassoX_*`/`lassoX_not_live` (copies of the generic
  `LiveTicketCexG` lasso at x64 and `Arch.tso`).

## Liveness: runner declarations (LIVERUN)

The promise-free liveness theorems above are stated for workers with no
declarations (`decls = {}`); the `.kl` runner's workers carry the typed
header's declarations `ds`. The theorems below lift the x64 ones and the AArch64 ones to `ds`.

- **Generic transfer** (`Promising/LiveRunnerSim.lean`, ISA-neutral):
  `Live.RunnerSim.ExecSim f G` (a thread-state map `f` under which `exec`,
  `deps`, `showInstr` commute and leaves are preserved, on states satisfying
  `G`) gives `stepOne`/`runTree` commutation, and along traces from a
  promise-free configuration `mapTrace` keeps `WeakFair`, `MemFair` and
  `PromiseFree`; hence `liveFrom_transfer` / `progressFrom_transfer`: a
  liveness (`LiveFrom`) or deadlock-freedom (`ProgressFrom`) statement about
  the mapped start configuration gives the same about the original one, for
  any predicates invariant under the map. Promise-free fragment only: the
  invariant `GoodC` includes "no promises", which is what lets the trees be
  compared exactly.
- **x64 bridge** (`Promising/LiveRunnerX64.lean`): `RunnerX64.execSimD`,
  `ExecSim State.noDecls (GD ds e)` from `X64VecDecls.exec_declsAgree` under
  the static `CellsDeclsAgree ds e` (every cell's accesses agree with `ds`);
  `cellsDeclsAgree_layoutL` reduces it to the image's directives. The
  safety theorems reach `ds` differently (`underDecls`/`reresolve`, a
  mixed-size access becomes a fault, which the safety trees accept);
  liveness needs exact trees, so here the declarations must agree with
  every access.
- **Proved, x64, promise-free fragment** (`WeakFair ∧ MemFair ∧
  PromiseFree`), for every `ds` that resolves each word of the image at 4
  bytes to itself (`Decls.AgreesAt`; weaker than the safety side's
  `ds.Sized`: nothing is assumed about other declarations), on a valid
  layout; then at the runner's layout and declarations (`_runner_concrete`)
  and for `N` copies of the runner's prepared worker with its initial memory
  (`_runnerN`, no hypothesis left except, for the ticket locks, the existing
  theorem's own `N + 1 < 2^32`):
  - `ticketlock3.kl`: `Live.RunnerX64Ticket.ticket3_x64_live_pf_runner`,
    `_runner_concrete`, `_runnerN` (`Promising/LiveRunnerX64Ticket.lean`);
  - `ticketlock2.kl`: `Live.RunnerX64Ticket2.ticket2_x64_live_pf_runner`,
    `_runner_concrete`, `_runnerN` (`Promising/LiveRunnerX64Ticket2.lean`);
  - `spinlock_cmpxchg2/3.kl`: `Live.RunnerX64Spin.spin_cmpx_live_pf_runner`,
    `_runner_concrete`, `_runnerN`; `spinlock2/3.kl`:
    `Live.RunnerX64Spin.spin_xchg_live_pf_runner`, `_runner_concrete`,
    `_runnerN` (`Promising/LiveRunnerX64Spin.lean`).
  - one-shot per-thread forms, same start structures
    (`CmpxStartD ds`, `XchgStartD ds`) and simulation, by
    `liveFrom_transfer`: `Live.RunnerX64One.spin_cmpx_live_oneShot_pf_runner`
    and `spin_xchg_live_oneShot_pf_runner`, each with `_runner_concrete`,
    `_runnerN` (`Promising/LiveRunnerX64One.lean`; not starvation-freedom
    of the lock).
- **AArch64 bridge** (`Promising/LiveRunnerA64.lean`): A64
  addresses are register values, so no static per-image fact holds; the set
  of states is dynamic: `A64Whole.WithDeclsD ds S` (declarations `ds`, and
  without them a per-lock invariant `S`). `RunnerA64.StepOK ds e S` asks
  that every `S`-state runs `e` with no declarations and that its tree is
  `TreeOK ds S` (every access at a location `ds` resolves to itself, every
  leaf in `S`); then `RunnerA64.execSimA (hnp : e.noPairs = true) : ExecSim
  State.noDecls (WithDeclsD ds S)`, from `A64DeclsBridge.exec_reresolve`
  (whose no-pair-merge condition is the static no-`LDXP`/`STXP` check) and
  `reresolve_of_treeOK`. In the instances `S` is the existing liveness proof's
  `Static` (program, end address, address registers, private memory) with
  the pc on one of the worker's positions, and `StepOK` is read off the
  existing per-cell trees (`stepOK_tk`, `stepOK_cas`, `stepOK_swp` — the last
  generic in `SpinSwpTrees.SwpCode P`). `LiveRunnerSim` is unchanged.
- **Proved, AArch64, promise-free fragment** (`WeakFair ∧ MemFair ∧
  PromiseFree`, `Arch.armv8`), on a valid layout, for every `ds` that
  resolves the lock words at 4 bytes to themselves (`Decls.AgreesAt`, as on
  x64 and as the A64 no-fault side's `*_agreesA`), with the start states of
  the safety side's runner theorems (`WithDeclsD ds (StartState …)`); the
  safety side's `ds.StrictSized` is not needed. Then at the runner's layout
  (`_runner_concrete`) and for `N` copies of the runner's prepared worker
  (declarations included) with its initial memory (`_runnerN`, no hypothesis
  left except, for the ticket lock, the existing theorem's own
  `N + 1 < 2^32`):
  - `ticketlock2/3.kl` (`ldadda`): `Live.RunnerA64Ticket.ticket_live_pf_runner`,
    `_runner_concrete`, `_runnerN` (`Promising/LiveRunnerA64Ticket.lean`);
  - `spinlock_cas2/3.kl`: `Live.RunnerA64Cas.spin_cas_live_pf_runner`
    (deadlock-freedom) and `spin_cas_live_oneShot_pf_runner` (one-shot
    per-thread), each with `_runner_concrete`, `_runnerN`
    (`Promising/LiveRunnerA64Cas.lean`);
  - `spinlock_swp2/3.kl`, `spinlock_swpl2/3.kl`:
    `Live.RunnerA64Swp.spin_swp_live_pf_runner`, `spin_swpl_live_pf_runner`
    and the `_oneShot_` forms, each with `_runner_concrete`, `_runnerN`
    (`Promising/LiveRunnerA64Swp.lean`; generic
    `swp_live_pf_runner_gen` / `swp_live_oneShot_pf_runner_gen`).
- **With promises** (`Promising/LiveRunnerSemSim.lean`):
  the same transfer on the machine with semantic certification
  (`LiveSem.lean`: `TraceSem`, `InstrSem`, `PromSem`, `CertOkN`),
  reusing `ExecSim` and both bridges (`execSimD`, `execSimA`) unchanged.
  The invariant `RunnerSemSim.GoodS G` is `GoodC` without "no promises".
  Promise steps do not read the thread's state, so they map trivially.
  `ExecSim` is a property of states (leaves stay in `G` whatever the
  memory), so certification runs map both ways:
  `threadNPn_mapT`, `threadNPn_of_mapT`, `certOkN_mapT_iff`. Hence
  `stepSem_mapC`, `enabledSem_of_mapC`, `mapTraceSem` (keeping
  `WeakFairSem` and `MemFair`), **`liveFromSem_transfer`** and
  **`progressFromSem_transfer`** under `Fair = WeakFairSem ∧ MemFair` (the
  fairness of the existing with-promises theorems; on x86 `MemFair` is a
  modelling assumption, see `LiveTrace.lean`).
- **Proved, with promises (semantic certification), at the runner's
  declarations**, with the same start structures and hypotheses as the
  promise-free runner forms above (`ds.AgreesAt` at the lock words; no
  `Sized`, nothing about promises), each with `_runner_concrete` and
  `_runnerN` (no hypothesis left except the ticket locks' own
  `N + 1 < 2^32`):
  - `ticketlock2/3.kl` (A64 `ldadda`):
    `Live.RunnerSemA64Ticket.ticket_live_sem_runner`
    (`Promising/LiveRunnerSemA64Ticket.lean`);
  - `spinlock_cas2/3.kl`: `Live.RunnerSemA64Cas.spin_cas_live_sem_runner`
    (deadlock-freedom) and `spin_cas_live_oneShot_sem_runner` (one-shot
    per-thread) (`Promising/LiveRunnerSemA64Cas.lean`);
  - `ticketlock3.kl` (x64): `Live.RunnerSemX64Ticket.ticket3_x64_live_sem_runner`
    (`Promising/LiveRunnerSemX64Ticket.lean`);
  - `spinlock_swp2/3.kl`, `spinlock_swpl2/3.kl`:
    `Live.RunnerSemA64Swp.spin_swp_live_sem_runner`,
    `spin_swpl_live_sem_runner` and the `_oneShot_` forms
    (`Promising/LiveRunnerSemA64Swp.lean`; generic
    `swp_live_sem_runner_gen` / `swp_live_oneShot_sem_runner_gen`);
  - `ticketlock2.kl` (x64): `Live.RunnerSemX64Ticket2.ticket2_x64_live_sem_runner`
    (`Promising/LiveRunnerSemX64Ticket2.lean`);
  - `spinlock_cmpxchg2/3.kl`:
    `Live.RunnerSemX64Cmpx.spin_cmpx_live_sem_runner` (deadlock-freedom)
    and `spin_cmpx_live_oneShot_sem_runner` (one-shot per-thread), start
    structure `CmpxStartD ds`, bridge `execSimD`
    (`Promising/LiveRunnerSemX64Cmpx.lean`; x86 `MemFair` a modelling
    assumption);
  - `spinlock2/3.kl` (x64 `xchg` the x64 runner liveness theorems with promises):
    `Live.RunnerSemX64Xchg.spin_xchg_live_sem_runner` (deadlock-freedom)
    and `spin_xchg_live_oneShot_sem_runner` (one-shot per-thread), start
    structure `XchgStartD ds`, bridge `execSimD`
    (`Promising/LiveRunnerSemX64Xchg.lean`; x86 `MemFair` a modelling
    assumption; its `_runnerN` shares its short name with the existing
    `Live.SpinX64SemXchgLive.spin_xchg_live_sem_runnerN` at `decls = {}`).
  - `ticketlock_al2/3.kl` (A64 `ldaddal`):
    `Live.TicketAl.ticket_al_live_pf_runner` (executable machine,
    promise-free) and `ticket_al_live_sem_runner` (semantic machine), with
    `_runner_concrete` and `_runnerN`, start structure `TkStartAlD ds`,
    bridge `execSimA` (`Promising/LiveTicketAlThm.lean`; proofs by
    `#ticket_al_clone` of `LiveRunner{,Sem}A64Ticket.lean`).

## Termination

**Statement.** `Live.Term.TermBoundSem A fuel c0` (`Promising/LiveTerm.lean`):
one index `K` such that every semantic trace (`TraceSem`, which stutters only
at final configurations) from `c0` is final at `K`. **No fairness hypothesis**
(any schedule, instruction and promise steps alike); `TermBoundSem.termFromSem`
gives `TermFromSem` under any fairness predicate. For a fixed finite client this
is wait-freedom.

**Proof principle (generic).** `termBoundSem_of_threadRank`: an invariant, plus a
per-thread rank that does not depend on the promise set, is stable under memory
extension, and is lowered by every instruction step of its thread. The measure is
Σ_threads ((B+1)·rank + (fuel·B − |prom|)): a promise step uses up headroom.
**Outstanding promises are bounded by certification only**
(`prom_le_of_certOkN`, `DropBounded` with `B = 1`: at most one promise
fulfilled per instruction), not by the program text. The retry rank is
`Memory.cntBelow` / `Memory.curBelow`, the count and value of the writes to the
location at or below the thread's coherence view. `window_rank`: a read
(load or failed CAS) of a value other than the current one strictly raises the
count. `step_cnt`: any other step raises the count, or keeps both count and value.

**Instances** (`Promising/LiveTermTreiber2Thm.lean`):

| program | theorems |
|---|---|
| `treiber2.kl` | `Live.TermTreiber2.treiber2_term_sem`, `_concrete`, `_gen` |
| `treiber2_arm.kl` | `Live.TermTreiber2Arm.treiber2_arm_term_sem`, `_concrete`, `_all` |
| `treiber2_relaxed.kl` | `Live.TermTreiber2Relaxed.treiber2_relaxed_term_sem`, `_all` |
| `treiber2_nodes.kl` | `Live.TermTreiber2Nodes.treiber2_nodes_term_sem`, `_concrete`, `_all` (`Promising/LiveTermTreiber2Nodes.lean`) |

The arm and relaxed proofs are `#tk_clone` re-elaborations of the treiber2
proofs. The cells differ only in the kinds of the load of `top` and of the CASes,
which the cell statements quantify over.

`treiber2_nodes.kl` (`treiber2NImage`) has no `STR W9` and no `LDR W11`, so its
cells sit at non-uniformly shifted positions and do not clone textually.
`Promising/LiveTermTreiber2P.lean` restates the argument position-parametrically,
with the same rank table (`TermTreiber2.rk`, `sOf`, `fl`). Its hypothesis
`Cells W σ data` gives one exec fact per cell at position `σ i` of a program `W`,
plus distinct addresses. The data cells are present only if `data`. From it,
`term_sem_genP`. `LiveTermTreiber2Nodes.lean` proves
`cellsN : Cells treiber2NImage sigN false` and instantiates it. The treiber2 proofs are re-derived from the parametric form too
(`TermTreiber2.cells : Cells treiber2DWorker id true`, from the
`LiveTermTreiber2Trees` lemmas; the arm and relaxed clones likewise), with
their statements unchanged; the rank table is in `LiveTermTreiber2Rank.lean`.

- The two-thread forms take the hypotheses of `treiber2_envG_whole` /
  `treiber2_arm_envG_whole` without reachability and finality (`hn`, `hn0`,
  `hn1`, `hT0` unused). The `_gen`/`_all` forms take any number of threads.
- **`t ≠ n + 8`** (each worker's node link word is not `top`) is the only
  non-start hypothesis. It makes the worker's `STR X2,[X1,#8]` a write to a
  location other than `top`. Every real start satisfies it: `top` and the nodes
  are distinct declared words. The safety theorems assume it too (`ht0`, `ht1`),
  so the drop-in forms need nothing extra. The concrete instances discharge it
  by `decide`.
- **`K` depends on `fuel` and on the number of threads, and on nothing
  else:** rank bound `N = threads · (2 + fuel)` on the writes to `top` (at most
  two successful CASes per thread plus its outstanding promises to `top`), and
  promise headroom `fuel` per thread.
- **Fixed-fuel caveat.** The result is about `TraceSem` at one fuel,
  for every fuel. A run whose promises need ever longer certifications is not a
  `TraceSem` at any single fuel and is not covered. For these finite clients a
  certification-length bound would close this; not done.
- **Remaining.** The runner-declarations forms are not covered (unsized
  `decls`, as in `treiber2_relaxed.kl`'s runner configuration): `Static`
  assumes `decls = {}`.
  `treiber2_nodes.kl` is done (above).

## Liveness: repeated acquisition (LOOP)

**Programs.** `ticketlock_loop2.kl` (N = 2) and `ticketlock_loop3.kl`
(N = 3): the `ticketlock2.kl` worker (`ldadda` ticket, `ldar` spin, counter
increment, `stlr` release) run for `k = 2` rounds. The round counter is `X7`
(rounds left), tested by `CBZ` at the loop head, so `k = 0` runs no round.
Bounded check (`run.sh`): `ticketlock_loop2.kl` Always (452 547 configurations,
30 s). `ticketlock_loop3.kl` is marked `# slow`, like 6 other files: it timed
out at 600 s (over 5.6 GB after 6 min). It has no verdict.
There is no whole-image safety theorem for either file.

**Statements** (`Promising/LiveTicketLoop.lean`, `tkLoopWorker`, start
configurations `TkLoopStart k N x o c`: N workers, `X7 = k`, `N·k + 1 < 2^32`).
All are on the semantic machine (`TraceSem`, `CertOkN`), for every fuel. A
worker's round is `k - X7`.

- `TicketLoopStarveSem`: per-round starvation-freedom. A worker spinning in
  round `r` (`TkLoopWaiting k r`) eventually acquires in round `r`
  (`TkLoopDone k r`: past its spin loop in round `r`, or in a later round).
- `TicketLoopFinishSem`: every worker eventually completes all `k` rounds
  (`TkLoopFinished`: at the end of the text).
- `TicketLoopTermSem`: every trace reaches a final configuration.
- `TicketLoopLiveSem` = Starve ∧ Finish.

Each is stated under `WeakFairSem ∧ MemFair`. **All four are proved**, with
promises, on a valid layout, for every fuel and every N with `N·k + 1 < 2^32`
(`Promising/LiveTicketLoopSem.lean`):

- `Live.TicketLoopSem.ticket_loop_starve_sem`;
- `Live.TicketLoopSem.ticket_loop_finish_sem`;
- `Live.TicketLoopSem.ticket_loop_term_sem`;
- `Live.TicketLoopSem.ticket_loop_live_sem`;
- `Live.TicketLoopSem.ticket_loop_live_sem_concrete`, at the layout
  `TicketLoopPF.tkLoopLayout`.

The proof is summarised under "Proof of the full statements" below. Safety
(mutual exclusion of the whole image) is still not proved for these files.

**Proved: the promise-free fragment** (`Promising/LiveTicketLoopPF.lean`).
The same statements on semantic traces with no promise step (`PromiseFreeSem`:
no `PromSem` step), on a valid layout, for every fuel and every N with
`N·k + 1 < 2^32`:

- `Live.TicketLoopPF.ticket_loop_starve_pf`;
- `Live.TicketLoopPF.ticket_loop_finish_pf`;
- `Live.TicketLoopPF.ticket_loop_live_pf`;
- `Live.TicketLoopPF.ticket_loop_live_pf_concrete`, at the layout
  `tkLoopLayout`.

The invariant (`LiveTicketLoopInv.InvL`) adds three things to the one-shot
`InvW`:

- a thread holds a ticket only from its `LDADDA` to its `STLR`, and the held
  tickets are exactly `[m, xc)`;
- `xc` is the sum over threads of the tickets taken, so `xc ≤ N·k` and the
  ticket never wraps;
- `OwnLe` on `next`: a thread's own earlier `next` writes are at or below its
  coherence view, so its `LDADDA` reads the last write in every round
  (`SpinSwpStep.spec_swp`).

Starvation-freedom per round follows the `LiveTicketPF` holder argument on the
loop positions. Finishing is a well-founded induction on the rank
`20·X7 + rk pc`: a worker that never finishes is always instruction-enabled,
its rank drops at every step outside the spin loop, and per-round
starvation-freedom gets it out of the spin loop with a smaller rank.

Fair traces exist, so neither hypothesis is vacuous:

- `Live.TicketLoopWitness.tk_loop_fairSem_exists`: `LoopFair`;
- `Live.TicketLoopWitness.tk_loop_fairSemPF_exists`: `LoopFairPF`. The
  round-robin trace takes no promise step.

**Why the one-shot proof (`LiveTicketSem`) does not carry over to `k ≥ 2`.**
These are hand-derived findings, not formalised.

- **F1: `NACert` fails for waiting threads.** The one-shot proof shows that a
  waiting thread, and the holder, are always instruction-enabled. It does so
  by certifying them without fresh writes (`NACert`), which replays against
  any larger memory (`nacertG_replay`). With rounds, a waiting thread's only
  certification may need fresh writes. Example: it holds a counter promise of
  the *next* round, and its solo run must first take a fresh next-round
  ticket (a fresh `LDADDA`).
- **F2: a thread can be disabled forever.** Take N = 2, k = 2, fuel ≥ about 30.
  1. T takes ticket 0 (owner is 0) and spins.
  2. T promises, in turn, P1: counter := 1, Po: owner := 1 and P2:
     counter := 2. P2 is its round-1 counter write. Each promise is
     certifiable when it is made.
  3. P2's only certification takes ticket 1 by a fresh `LDADDA` in round 1
     and reads Po.
  4. U now takes ticket 1 with a fresh `LDADDA`.
  5. From then on, every certification of T would have to take ticket ≥ 2 in
     round 1 and read owner = 2 below P2's timestamp. None exists.
  6. So T has no certifiable instruction step and no useful promise step,
     forever. U reads Po and finishes. The configuration is non-final with
     nothing enabled.

  This is how the promising machine is expected to behave, not a modelling
  bug. Such runs are finite and so are not `TraceSem`s, and the statements
  above survive. But `NoStuck` fails for looping clients (and, on AArch64, for
  one-shot lock clients too: see "Stuck configurations" in the section on the
  executable checker vs the semantic machine). A waiting thread need
  not be enabled, so the one-shot `henT` is false. The proof must argue that
  "someone must step" (a `TraceSem` stutters only at final configurations)
  instead of relying on the waiting thread's fairness.
- **F3: the holder of the final `owner` value certifies without fresh
  writes.** This is the key fact for the full proof. **Proved**:
  `Live.TicketLoopHolder.holder_nacert` (`Promising/LiveTicketLoopHolder.lean`):

  ```lean
  /-- `H` holds ticket `M`: taken (positions 6–13, low word of `X3` is `M`), or
  reserved (an outstanding promise of value `M + 1` to `next`). -/
  def HoldsLoop (x : BitVec 64) (u : Thread isa) (mem : Memory) (M : Nat) : Prop :=
    (TicketLoopInv.Ticketed u ∧ TicketLoopInv.tk u = M) ∨
    (¬ TicketLoopInv.Ticketed u ∧
      ∃ ts ∈ u.prom, ∃ w, mem.get? ts = some w ∧ w.loc = L4 x ∧ w.val.toNat = M + 1)

  theorem holder_nacert [Executable.ValidLayout (layout tkLoopWorker)] {fuel k N : Nat}
      {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
      (hs : TkLoopStart k N x o c states initMem) (tr : TraceSem Arch.armv8 fuel isa)
      (h0 : tr.cfg 0 = Config.init states initMem) (i : Nat) {H M : Nat} {u : Thread isa}
      (hu : (tr.cfg i).threads[H]? = some u)
      (hM : ((tr.cfg i).mem.finalVal (L4 o)).toNat = M)
      (hh : HoldsLoop x u (tr.cfg i).mem M)
      (hno : ∀ ts w, (tr.cfg i).mem.get? ts = some w → w.loc = L4 o → w.val.toNat ≠ M + 1)
      (hc : CertOkN Arch.armv8 H u (tr.cfg i).mem fuel) (hM32 : M + 1 < 2 ^ 32) :
      u.prom = [] ∨ NACertG Arch.armv8 fuel H u (tr.cfg i).mem
  ```

  `hM` is unused (named `_hM` in the source). `hM32` says the `owner` counter
  does not wrap around at `2^32 - 1`. The trace invariant with promises
  discharges it (`M ≤ xc ≤ N·k` and `N·k + 1 < 2^32`), so
  `Live.TicketLoopInvP.holder_nacert'` is the same statement without `hM32`.
  `Live.TicketLoopInvP.holder_nacertV` is the form the final proof uses: the
  holder in the sense of the invariant (`HoldsV`: a taken ticket, or a
  reserved one through an outstanding `next` promise).

  It rests on three facts about the model, checked in `Promising/Thread.lean`:

  1. a release write's pre-view takes `vwOld`, so fresh writes kill `owner`
     promises;
  2. an acquire read's pre-view takes `vRel`, so after a *fresh* `STLR` the
     next `LDADDA` cannot read below an outstanding `next` promise, and every
     `next` promise is dead;
  3. an acquire read raises `vwNew`, and a write needs a timestamp above
     `vwNew` and `vCAP`, so a later write must lie above the message read.

  Since no `owner` message of value `M + 1` exists, H's round-M release is
  fresh. Everything outstanding after it is dead (2), so a certification of H,
  cut at the first empty promise set, has no fresh write.

**Proof of the full statements.**

1. **Invariant with promises** (`Promising/LiveTicketLoopCert.lean`,
   `Promising/LiveTicketLoopInvP.lean`). A per-thread invariant `TI` holds for
   any promise set. The certification analysis then gives three facts about a
   worker that empties its promise set alone:
   - a `next` promise is fulfilled by an atomic read of the last `next`
     message below it;
   - an `owner` promise is fulfilled with no fresh write before it;
   - there are at most as many `next` promises as `LDADDA`s left.

   With these, `TicketLoopInvP.LInv` holds at every index of a semantic trace
   (`trace_linv`):
   - the `next` and `owner` values form chains;
   - every `next` message of value `v + 1` has a holder of `v` unless
     `owner = v + 1` exists;
   - `xc` is the sum of taken and reserved tickets, so `xc ≤ N·k`;
   - no thread has a dead promise.

   The `owner` value `M` never decreases (`trace_o`).
2. **Someone must step** (`Promising/LiveTicketLoopSem.lean`,
   `final_reached`). If a fair trace never reaches a final configuration:
   - Some thread steps infinitely often. By the rank `20·X7 + rk pc` it ends
     up spinning forever with a ticket `K` (`spin_eventually`).
   - `K ≤ M` contradicts memory fairness (`spin_le_false`). For `K < M`, its
     own `owner` message of value `K + 1` becomes a dead promise. For `K = M`,
     it reads `M` and leaves the loop.
   - So `K > M`, and the `next` message of value `M + 1` has a holder `H` of
     `M`.
   - If `H` steps infinitely often, it spins with no promise
     (`spin_stuck`), so its ticket is `M`: contradiction.
   - Otherwise, F3 (`holder_nacertV`) and `nacert_replay_loop` keep `H`
     instruction-enabled forever, and weak fairness makes it step:
     contradiction.

   F1 and F2 are avoided: no waiting thread needs to be enabled, only the
   holder of the final `owner` value.
3. **The statements.** At a final configuration every worker is at its end
   with `X7 = 0`. That gives Finish. It also gives Starve: a worker that
   waited in round `r` has `X7 ≠ 0` then, so it acquired in round `r`.
   Termination is `final_reached` itself.

Size: about 2.4k lines (Cert 959, InvP 722, Sem 725), plus the F3 facts (`LiveTicketLoopFacts.lean`, `LiveTicketLoopHolder.lean`, 722).

`#tk_clone` does not apply: it substitutes one cell, and the program here
differs in 14 cells.

## OPEN: stricter than herd (parked with LL/SC)

A store exclusive that writes the value of an earlier load (a true data
dependency, `LDR X0,[x]; LDXR; STXR W8,X0,[f]`) allows load buffering in
current herd: since herdtools7 `add229fa` (2025-02-13, "Rework input
ports"), `stxr`/`stxp` read their data with `read_reg_ord`, so there is no
`data` edge (`aarch64deps.cat` l. 69). herd before that commit, the
Promising-ARM era model, says Never, as Kraken does. Kraken cannot produce
the outcome: no thread can certify the needed promise in an append-only
memory without value speculation. Tests, the herd history (built and run at
`add229fa^` and `add229fa`), and the minimal Promising change that would
allow it: `corpus/aarch64-pairs/open/README.md`. Outside the regression
run.

## OPEN: unlocked `cmpxchg` stricter than the SDM text

A failed *unlocked* `cmpxchg` with a memory destination is, by the SDM text,
a read followed by a separate, non-atomic write-back of the old value, so a
concurrent store between them could be lost. Kraken (`rmwPlain`: a plain load,
a store only on success) and herd model it as a read with no write, so the
lost update is forbidden: Kraken is stricter than the SDM text, equal to herd.
A hardware probe (AMD EPYC 7B13, Zen 3) saw 0 lost updates in 20M rounds. No
`.kl` file or proof uses unlocked `cmpxchg` on shared memory. Also, on the
failure path Kraken checks only read access (relevant only if read-only
memory is ever modelled). Parked with the other herd-comparison items.

## Unsupported (by design, reported as such)

- Mixed-size accesses: a location is a footprint (address, width). In a
  test that types a location, an access at another width than its
  declaration, or two overlapping footprints at an address no symbol names,
  is reported unsupported, as herd does without `-variant mixed` ("Illegal
  mixed-size test"); e.g. M001 (`Variant=mixed`). Untyped tests keep herd's
  width-agnostic default (legacy mode).
- Pointer initialisers (`int *p = &x`), code addresses in registers
  (`0:X3=P1:L0`), instruction values (`instr:"..."`), memory tags,
  page-table entries and faults.
- Loops: the certification budget (`-fuel`, default 64 instructions per
  thread) bounds them; herd's own `Loop Ok`/`Loop No` pseudo-state is not
  reproduced. `litmus_tests.py` drops it from herd's states and compares the
  real states and the verdict word (rows marked `(herd Loop)`, counted in the
  summary; `corpus/README.md`), so A184 and the sweep's 80 `*-amo` tests
  agree; a real-state difference is still reported
  (`selftest/check_loop.py`).
- Nondeterministic register values (`undefined` of a bitvector or of the
  whole flags) are reported as a fault; `undefined Bool` is explored.
- x86: `rip`/segment registers, `endbr64`, `nopl`, `shl 2,%eax` (immediate
  without `$`).

## Mismatches in `corpus/aarch64-instructions` (7)

| Test | Cause |
|---|---|
| L029 | herd prunes the loop's unrolling (`States 0`, `Loop Ok`, verdict `Never`): with the pseudo-state dropped herd has no real state; ours (`0:X1=10`, `Always`) is the actual one |
| A257, A258 | code addresses (`label:"P0:L0"`) |
| A265 | `forall 0:X1=0xffffffff` on a 64-bit `EON` result: herd types the literal as 32-bit `int` |
| L051 | instruction values (`instr:"ADD W0,W0,#1"`) |
| L086 | instruction fetch (`Stable=`, reading code) |
| L032 | `LDXP`/`STXP` on two array elements: two accesses, weaker than herd's single-copy-atomic pair (see Pair accesses) |

Only L032 is a memory-model disagreement, and it is weaker than herd.

## Audit scope: demo files

The 9 `native_decide` uses in `Kraken/AArch64/Examples/WeakMemory.lean` (6) and
`Kraken/X64/Examples/WeakMemory.lean` (3) are outside the axiom audit. The audit
(`isasplit.py`) skips `/Examples/` files outside `Kraken/Examples/LockFree/` on
purpose: those example collections declare clashing names and cannot be imported
together. These are demonstration files; no LockFree theorem depends on them.

## The executable checker vs the semantic machine (the promise projection)

Two machines. The **semantic machine** (`StepSem`, `CertOkN`, the paper's
promise rule; `ReachableSem`, `TraceSem`) is the reference semantics. The
**executable machine** (`succs`/`certify`, `Reachable`, `TraceS`, `explore`)
is a checker. It is a sound but **incomplete** under-approximation at a fixed
fuel, witnessed concretely in `Promising/LiveBridgeTests.lean`:

- `succs` is not monotone in fuel (Cex1: a promise is offered at fuel 4, not at
  5–6, again at 7);
- `certify` rejects states that certify within the fuel, because its DFS
  visited set ignores the remaining fuel (Cex1);
- DFS pruning loses recorded writes, on AArch64 only (Cex3);
- the difference is outcome-observable at fixed fuel (Cex4, an LB-shaped
  program: forbidden by `explore` at fuels 11–16, allowed from 17).

Consequences:

- **Verdicts.** "Forbidden"/"Always"/`Never` verdicts computed with `explore`
  at a fixed fuel may be too strict. Positive results (reachable outcomes, bug
  witnesses) are unaffected (proved, next item). **Checked on the real corpus:**
  at the fuels in use (litmus 64, LockFree 300), existing `explore` and a complete
  prototype (BFS `certify` plus the paper's promise rule) agree on the
  verdict, the final-state set and the explored-configuration count for all
  1,181 tests that both complete (1,231 `.litmus` files over every suite and all
  53 LockFree `.kl`; 100 unsupported by both; 3 `# slow` files completed by
  neither: A64 `msqueue3`, `msqueue_relaxed2`, `treiber2_relaxed`). So no
  current verdict, and no herd mismatch, is caused by the checker gap. Below the
  fuels in use the gap is reachable from real programs: the prototype reaches
  more intermediate configurations in A64 `spinlock2`, `spinlock_relaxed2`,
  `spinlock_relaxed_acq2` (fuels 6–14) and x64 `msqueue2` (fuels 30–34, 42–44),
  never with a different verdict or final set.
  The comparison tool is `Kraken/Litmus/CheckerCompare.lean` with the
  non-default executables `checkercompare_{aarch64,x64}`, whose output has the
  main litmus drivers' format so that a script can compare the two.
  `CheckerCompare.lean` is a **measurement tool, not a reference semantics**: its
  prototype checker is unverified and nothing should be proved about it; the
  reference is the semantic machine (`StepSem`).
- **Positive results transfer (proved).** The executable machine
  is sound for the semantic one at the same fuel: `Live.Bridge.stepSemOfSuccs`
  (every `succs` successor of a bounded configuration is a `StepSem` step) and
  `Live.Bridge.reachableSem_of_reachable'` (`Reachable A fuel c c'` from a
  bounded `c` gives `ReachableSem A fuel c c'`), in
  `Promising/StepSemOfSuccs.lean`, under `[I.LawfulState]` only. Binder-free
  forms for AArch64 (`Arch.armv8`) and x64 (`Arch.tso`):
  `reachableSem_of_reachable_{a64,x64}` and, from `Config.init`,
  `reachableSem_of_reachable_init_{a64,x64}` (`StepSemOfSuccs{A64,X64}.lean`).
  So every reach theorem and every witness found by `explore` is a reachability
  fact of the semantic machine; likewise every executable trace is a semantic
  trace (`traceToSem`). Ingredients: `certifySoundN'`/`certify_soundN2`
  (`certify` sound at the fuel, `CertifySoundN2.lean`) and `Proj.promReplay`
  (SLR's Lemma 1, replay direction, no hypothesis, `PromReplay.lean`).
  `LawfulState` cannot be dropped: `succs` shares one hash-map cache across
  threads, and with an unlawful state `BEq` it offers a promise the semantic
  machine forbids at that fuel (`Promising/LiveBridgeTestsLawful.lean`). Negative
  results ("Forbidden", `Never`) still do not transfer: that direction needs a
  complete `certify`, which today's is not.
- **Safety theorems.** The Stage 2 theorems over `Reachable` are statements
  about the checker. Lifting them to `ReachableSem` is open.
  Its first step is done: `Proj.promProjection` (SLR's Lemma 1, projection
  direction, no hypothesis) gives `Live.Bridge.ReachableK.of_reachableSem'`,
  so every `ReachableSem` run, at every fuel, is a run of the fuel-free
  `ReachableK`, which also contains `Reachable` (`ReachableK.of_reachable`).
- **The chain over `ReachableK`.** The Stage 2 safety chain is
  also proved over `ReachableK` (`Kraken/Promising/ReachableK.lean`). Naming:
  the `ReachableK` form of a declaration `foo` is `fooK`, in the same
  namespace; the citable, fuel-free forms of the hubs are `foo_reachK`
  (`SLR/ChainK/Payoff*.lean`, e.g. `final_of_relPureSafely_reachK`,
  `theorem1IIPure'_reachK`), and `ticket_counter_envG_sem`
  (`SLR/ChainK/TicketA64Demo.lean`) states the AArch64 ticket lock over
  `ReachableSem` at every fuel. Mechanism: the leaf lemmas are generalised in
  place to `SuccKind` steps, a few lemmas used through dot notation get
  hand-written twins (`Live.Bridge.ReachableK.x`, `Config.LiveK.x`), and the
  rest is produced by `#chaink_clone` (`Kraken/Promising/ChainK/Clone.lean`),
  a source-level instantiation: it re-reads the listed source file, renames
  `Reachable`, `succs`, `Config.Live`, … and every cloned declaration
  `foo ↦ fooK` (each rename is logged), and elaborates the result again, so
  every `fooK` is kernel-checked from scratch. The `fooK` statements carry a
  phantom `fuel` (`ReachableKF A fuel` is an `abbrev` for `ReachableK A`);
  cite only the `_reachK`/`_sem` forms. Not covered: the bridges from the
  existing `Reachable`-based statements (`Theorem1IIPure.theorem1II`, the
  F/S-chain `…FD`/`…SD` links), which are skipped by the clone.
- **The `_sem` twins of the published theorems.** The
  safety and fault-freedom theorems of `Examples/LockFree/THEOREMS.md` that
  mention `Reachable` or `Config.FaultFree` have twins named `…_sem…`. Each
  twin has the same statement with `Reachable A fuel c₀ c` replaced by
  `ReachableSem A fuel c₀ c` (the same fuel binder, now the certification
  fuel), and `Config.FaultFree` replaced by `Config.FaultFreeSem`
  (`SLR/ChainK/FaultFree.lean`). That makes 267 twins, including
  `ticket_counter_envG_sem`. They are listed with their statements in
  `Examples/LockFree/SEM_TWINS.md` and cited as "also" in THEOREMS.md.
  - **How they are proved.** `#sem_twin` (`SLR/ChainK/SemTwin.lean`)
    proves each twin from the K clone `fooK` of the original (opt-in
    `#chaink_clone'` in `SLR/ChainK/TwinsClone*.lean`). The transport uses
    `ReachableK.of_reachableSem'` from `Config.init_bnd` and
    `Config.FaultFreeSem.of_K`.
  - **Checking.** `Examples/LockFree/tools/sem_twins.py` re-checks every
    statement, independently of `#sem_twin`.
  - **Not covered.** `X64.EnvG.VecPublish.x64_publish_movdqa_verbatim` and
    its `_faultFree` form are stated for a general start configuration (only
    `c₀.mem.msgs = #[]`). Without `c₀.Bnd` (thread views within the
    memory), `ReachableK.of_reachableSem'` does not apply, so they have no
    twin. The `_concrete` instances do have twins.
  - **Also not covered.** The reachability, liveness and verdict theorems
    have no twins, and neither do `InvEnv.swp_reachable` and
    `swp_counter_envG_type_eq`.
- **The fuel-free semantic machine `…SemInf`: the lowering target (
  P2).** `Promising/LiveSemInf.lean` restates the semantic machine rule for
  rule with unbounded certification: `InstrSemInf`/`PromSemInf`/`StepSemInf`
  are `InstrSem`/`PromSem`/`StepSem` with `CertOk A tid t mem` (some
  promise-free solo run `ThreadNP` empties the promise set) in place of
  `CertOkN A tid t mem fuel`. With them come `ReachableSemInf`,
  `TraceSemInf`, `EnabledSemInf`, `WeakFairSemInf`, the `…FromSemInf`
  liveness predicates, and `Config.FaultFreeSemInf`. **This is the machine a
  lowering (WeakCore's backward simulation) should target: no statement
  about it mentions fuel.** How it relates to the other machines (all proved,
  no hypothesis except where noted):
  - one step: `stepSemInf_iff_stepSemU : StepSemInf A tid c c' ↔ ∃ fuel,
    StepSem A fuel tid c c'`, likewise `instrSemInf_iff_instrSemU` and
    `promSemInf_iff`; from `certOk_iff_exists_certOkN` and
    `threadNP_iff_exists_threadNPn`;
  - runs: `reachableSemInf_iff : ReachableSemInf A c c' ↔ ∃ fuel,
    ReachableSem A fuel c c'`, and `forall_reachableSemInf_iff` (a safety
    property at every fuel is a safety property on the Inf machine);
  - executable side: `ReachableK.of_reachableSemInf` (from a `Config.Bnd`
    start, the Inf machine is inside `ReachableK`/`SuccKind`);
  - traces: `TraceSemInf.toU`/`TraceSemU.toInf` keep the configurations, and
    `weakFairSemInf_iff`, `liveFromSemInf_iff`, `progressFromSemInf_iff`,
    `termFromSemInf_iff`, `termBoundSemInf_iff` identify the Inf predicates
    with the `…SemU` ones of `LiveCertBounded.lean`, for every fairness;
  - fault freedom: `Config.FaultFreeSemInf.iff_forall` (`SLR/ChainK/InfTwin.lean`).
  - **Twins.** `#inf_twin` (`SLR/ChainK/InfTwin.lean`) gives every `_sem`
    twin of `SEM_TWINS.md` (267) a fuel-free twin `…_semInf…`. It drops the
    `∀ fuel` binder and maps `ReachableSem A fuel` ↦ `ReachableSemInf A` and
    `Config.FaultFreeSem A fuel` ↦ `Config.FaultFreeSemInf A`.
    `#semU_inf_twin` (`Promising/LiveCertBoundedInf.lean`) restates the 16
    AArch64 CertBounded headlines (`spin_cas_live*_semInf*`, the `treiber2*`
    `TermBoundSemInf` family), and `LiveCertBoundedInfCmpx.lean` the 4 x64
    ones (`spin_cmpx_live*_semInf*`) with no extra hypothesis. Listing:
    `Examples/LockFree/INF_TWINS.md`, re-checked by
    `Examples/LockFree/tools/inf_twins.py`.
  - **Does not transfer.** `∀ fuel, TermBoundSem A fuel c₀` does not give
    `TermBoundSemInf A c₀`. The bound may grow with the fuel, and a trace
    whose steps need ever longer certifications is a trace at no fixed fuel.
    `termTransferInf` needs `CertBoundedFrom` (likewise `liveTransferInf`,
    `progressTransferInf`, `termFromTransferInf`). The fixed-fuel liveness
    theorems (`LiveFromSem A fuel …`) are about traces at one fuel and do not
    transfer without `CertBoundedFrom` either. Statements with fuel in
    another position (e.g. `StuckSem A fuel`, `DeadPromiseIn A fuel`) are
    rejected by `#inf_twin`.
- **Stuck configurations.** On AArch64 the semantic
  machine reaches configurations that are not final and in which no thread
  can step, also for the existing one-shot lock clients (not only for the
  looping ticket lock, LOOP's F2). Example (`spinlock_cas2` shape): before its
  acquiring `CASA`, T promises its plain `counter := 1` store (certifiable:
  the plain `STR` is not ordered after the acquire RMW's write). U then
  acquires, increments, releases and halts. T can no longer fulfil the
  promise: its CAS cannot read the initial lock value (no longer atomic) and
  reading U's release is an acquire read that lifts its view above the
  promise. Evaluated on toy versions of `spinlock_cas2` and `ticketlock2`: no
  certification at any length (whole solo state space); the executable
  machine shows 12 stuck configurations per shape on ARMv8, none on TSO. The
  existing `LiveSpinSemSolo.lean` docstring already notes that such a thread
  "may be unable to certify". Such a run ends with a promise that is never
  fulfilled: a dead speculation that yields no outcome and matches no hardware
  execution. It is finite, so not a `TraceSem`, and the liveness theorems are
  silent on it, correctly (infinite runs in which the other threads go on are
  traces and are covered). It forbids no outcome. Consequence: a plain
  "no stuck configuration" statement is false on AArch64 at every fuel
  from 5. **Proved (`Promising/LiveNoStuck{,Tso,X64,A64}.lean`):**
  every stuck configuration has a dead promise (`Live.NoStuck.stuckHasDeadPromise`,
  any ISA, given `OkStepsPF`; once dead, a promise stays dead along every run,
  `deadProm_reachableSem`); on TSO no stuck configuration is reachable
  (`tsoNoStuck`, given `TsoCertInv`: no `movnti`, at most one memory write per
  instruction path). Instances with no open hypothesis: the x64 locks
  (`spin_{cmpx,xchg}_noStuck_sem`, `ticket{2,3}_x64_noStuck_sem`, with
  `_concrete` forms) and, on AArch64, the dead-promise form for the CAS lock
  (`spin_cas_stuckHasDeadPromise`, `_concrete`). With no stuck configuration,
  the x64 liveness theorems hold for every maximal run, not only for infinite
  traces (`*_live{,_oneShot}_sem_max`, via `MaxRunSem`, `liveFromSemMax_of`).
  **`OkStepsPF` discharged:** `Live.NoStuck.stuckHasDeadPromise_of_faultFreeSem`
  (`Promising/LiveOkSteps.lean`) derives the dead-promise form from
  `Config.FaultFreeSem` and `Config.Bnd` for any ISA with `ISA.ExecTotal`
  (instances for `AArch64.isa`, `isaLSE2`, `X64.isa`: a bounded promise-free
  thread can always read the last write and promise-now a write; `CASP`'s
  `choose 0` dead branches are handled in `caspTree_total`). Hypothesis-free
  forms for the nine locks at the runner layouts, any `N`, `Arch`, `fuel`:
  `*_stuckHasDeadPromise_concreteN` (`LiveOkSteps{A64,X64}Locks.lean`); any
  other program with a `*_faultFree_sem*` twin gets it by the same one-liner.
  Open: there is no AArch64 no-stuck statement (it is false); `NoStuckFrom`
  still needs `ConsistentSem` along runs (x64 has it via `tsoNoStuck`).
- **Liveness.** `TraceSem` fixes one fuel per trace, so fair traces whose
  certification lengths grow without bound are not covered. No current
  example is known to need such traces (not proved).
  **Closed for the `treiber2` family:** `Live.CertBounded`
  (`LiveCertBounded.lean`) defines the fuel-free machine (`TraceSemU`,
  `WeakFairSemU`, `LiveFromSemU`, `TermBoundSemU`, ...) and proves that a
  certification bound (`CertBoundedFrom c0 F`) turns every `∀ fuel` liveness,
  progress or termination theorem into a fuel-free one (`liveTransfer(G)`,
  `progressTransfer(G)`, `termTransfer`). For `treiber2`, `_arm`, `_relaxed`,
  `_nodes` the bound is proved, `F = 82 + 40·n` for `n` threads (no fuel, no
  layout): `treiber2_term_semU(_concrete)` and siblings
  (`LiveCertBoundedTreiber2{,P}.lean`).
  **Closed for the AArch64 CAS spinlock:** `LiveCertCut.lean`
  proves view monotonicity of the executable thread rules (`Thread.Dom`,
  `stepOne_dom`, `CertOkN.of_dom`) and an iteration cut (`ThreadNPn.cut`,
  `CertOkN.bound_of_cuts`); register views and the exclusive bank are not
  monotone, so the loop-head domination is established per program.
  `LiveCertBoundedSpinCas.lean` proves `cas_certBounded : CertBoundedFrom
  Arch.armv8 c0 13` (program-only bound) and `spin_cas_live{,_oneShot}_semU`
  with `_concrete` forms. **SWP/SWPL and x64 `xchg` cannot be closed this
  way:** a failing swap writes, so a waiting thread can chain promises, each
  certified by a failing swap fulfilling the previous one; a chain of `k`
  promises is reachable at fuel about `4k` and needs `k` instructions to
  certify, so no fixed `F` bounds certification. A fuel-free liveness
  statement for these locks needs a different formulation (not planned).
  **Closed for the x64 `lock cmpxchg` spinlock:**
  `LiveCertBoundedSpinCmpx.lean` proves `cmpx_certBounded : CertBoundedFrom
  Arch.tso c0 18` (program-only bound; the `LiveCertCut` lemmas are used
  unchanged, the locked RMW is decomposed locally as fence; read; fence) and
  `spin_cmpx_live{,_oneShot}_semU` with `_concrete` forms, under
  `WeakFairSemU ∧ MemFair` (`MemFair` is a modelling assumption on x86). The
  Inf-machine twins `spin_cmpx_live{,_oneShot}_semInf{,_concrete}` are in
  `LiveCertBoundedInfCmpx.lean` (INF_TWINS.md, "Headlines (X64)").
  **Closed for the ticket locks:** the loop is read-only (the
  ticket RMW never fails), so two loads of `owner` in a promise-carrying
  stretch cut the run (load and compare replayed from the earlier load state;
  `LiveCertCutRegS.lean` for the two changing register-view slots).
  `ticket_certBounded : CertBoundedFrom Arch.armv8 c0 11` (AArch64
  `ticketlock`, `LiveCertBoundedTicket.lean`) and `ticket3_x64_certBounded :
  CertBoundedFrom Arch.tso c0 11` (x64 `ticket3`,
  `LiveCertBoundedTicketX64.lean`), program-only bounds;
  `ticket_live_semU`/`ticket3_x64_live_semU` with `_concrete` forms, and
  their Inf-machine twins `…_live_semInf(_concrete)`
  (`LiveCertBoundedInfTicket{,X64}.lean`).
  **Closed for the repeated-acquire ticket lock:** a
  certifying solo run may go through every round left (a promise of a later
  round's write is fulfilled only there), but outside the read-only spin
  loop every instruction moves forward and the `SUB` lowers `X7 ≤ k`. Two
  `LDAR`s in one spin visit cut the run (the `LDAR` and the `CMP` after it
  are replayed, as for the single-acquire lock). The bound is linear in the
  round count `k`, a program constant (`X7` at the start):
  `ticket_loop_certBounded : CertBoundedFrom Arch.armv8 c0 (12 * k + 2)`
  (`LiveCertBoundedTicketLoop.lean`); `ticket_loop_live_semU` (starvation
  freedom per round and completion of all rounds, `_concrete`) and
  `ticket_loop_term_semU` (`TermFromSemU`, via `termFromTransfer`;
  `_concrete`), and their Inf-machine twins `ticket_loop_{starve,finish,
  live,term}_semInf` (`LiveCertBoundedInfTicketLoop.lean`).
  **x64 `ticket2`:**
  the same cut (the release `incl (owner)` is after the loop);
  `ticket2_x64_certBounded : CertBoundedFrom Arch.tso c0 10`
  (`LiveCertBoundedTicket2X64.lean`, program-only bound, image-independent
  x64 helpers in `LiveCertCutX64.lean`), `ticket2_x64_live_semU` with
  `_concrete`, and the Inf twins `ticket2_x64_live_semInf(_concrete)`
  (`LiveCertBoundedInfTicket2X64.lean`).
  Nothing is left open on this route.
- **x64 `treiber2` termination is conditional on `NoEmptyRead`.**
  `Live.TermX64Treiber2.x64_treiber2_termBoundSem_of_noEmptyRead` (any number
  of threads, `decls = {}`) and the runner-layout instance
  `…Concrete.x64_treiber2_termBoundSem_concrete_of_noEmptyRead` prove
  `TermBoundSem Arch.tso fuel` under the explicit hypothesis `NoEmptyRead`: at
  every `ReachableSem` configuration, a thread after its pop load of `top` has
  `%rax ≠ 0`. Unlike AArch64 (`cbz` exit), x64 `treiber2.kl` loops on an empty
  stack (`testq; je pop`), and no rank pays for that loop. The hypothesis is
  **not proved**. Explorer evidence only (fuel 300, final states): with the
  empty branch made observable the program is Always, and a no-push control
  shows the branch can fire. Discharge plan (~2.9k lines): ghost history and
  thread invariant, closure under every instruction and promise step, the
  certification configuration built from the post-read configuration (an
  earlier argument from the pre-read configuration is wrong: certification
  can fulfil the reader's own promised pop), and a stack-count invariant on
  the `top` chain; it uses the no-stuck proofs' TSO consistency (`LiveNoStuckTso.lean`). The runner's declared configuration (`decls ≠ {}`) is not covered.
- **treiber_pp liveness: AArch64 and x64.**
  `LiveTreiberPpA64.lean` proves `treiber_pp_live_sem` / `treiber_pp_live_runner`
  (with hypothesis-free `_concrete` forms): under `WeakFairSem ∧ MemFair`, on
  every `TraceSem Arch.armv8 fuel` trace (promises included) from the
  whole-image start, both pusher and popper reach their end addresses.
  `LiveTreiberPpX64.lean` / `LiveTreiberPpX64Runner.lean` prove the same for
  the x64 `.kl` code verbatim on `TraceSem Arch.tso fuel`:
  `x64_treiber_pp_live_sem` (the start of `x64_treiber_pp_envG_verbatim`, no
  declarations) and `x64_treiber_pp_live_runner` (the runner's declarations;
  `OkStepsPF` from `x64_treiber_pp_envG_runner_faultFree_sem`), each with a
  hypothesis-free `_concrete`. Both are proved directly by staged freezing
  (the ISA-neutral `TreiberPp.skeleton`, `LiveTreiberPpSkel.lean`, unchanged
  for x64), not by transfer from the SC machine (the popper's loads are
  value-dependent). Stated for `n ≠ 0` (a null node makes the popper spin
  forever; x64: `symT "n1" ≠ 0`) and `t ≠ n + 8`.
  **Fuel-free form on AArch64:** `LiveCertBoundedTreiberPpA64.lean`
  proves `treiber_pp_certBounded` / `treiber_pp_certBounded_runner :
  CertBoundedFrom Arch.armv8 c0 51` (program-only bound: a rank `21 + 10·3`
  over the at most `3` writes to `top` seen by a solo run, the headroom
  `S + promAt top ≤ 1` proved along `ReachableSem` at every fuel, promise
  steps included, and the read-only empty spin `LDAR; CBZ` cut by
  domination) and, by `liveTransfer`, `treiber_pp_live_semU` /
  `treiber_pp_live_runner_semU` with hypothesis-free `_concrete` forms under
  `WeakFairSemU ∧ MemFair`; Inf twins `…_semInf…` in
  `LiveCertBoundedInfTreiberPpA64.lean` (INF_TWINS.md, "Headlines (AArch64)").
  Open: the x64 fuel-free form (no certification bound for
  `x64_treiber_pp` yet). The bound is expected to be program-only with the
  same shape (rank over the writes to `top`, headroom invariant, spin cut);
  estimate 550–700 lines. The extra difficulty is the empty spin
  `movq; testq; je`: `testq` sets `AF` nondeterministically (`.choose`), so
  the loop head after `je` is not unique and the cut needs one witness per
  `AF` value (as in the bounded-certification proofs' `LiveCertBoundedSpinCmpx.lean`); the plain
  `movq` load is `.acqPc` on `Arch.tso` (read view raised to the post-view),
  which the domination argument needs (the x64 trees emit `.load .plain`,
  `LiveTreiberPpX64Trees.lean`; nothing proved on it yet).

## Lowering pilot with a stack frame: conditional

- `Lower.Pilot2.pilot2_promising_of_envGValsBridge` is conditional on two named
  obligations, `EnvGValsBridge (treiber2GA t n0 n1)` and `Pilot2ValsReach`. The
  Promising chain (`EnvGCAdj`/Theorem 1′) gives a reader no value facts, so a
  load through a pointer read from `top` cannot be routed away from a
  non-empty `dmem` stack (`Lower/DStack.lean`). The generic fix (route c2) replaces both by a per-thread value
  specification; productisation in progress.
- **Closed:** `Lower.Pilot2.pilot2_promising`
  (`Lower/Pilot2ValsWhole.lean`) proves the same conclusion without either
  obligation, via `envGValsBridge_ofSpecs` (`Promising/SLR/EnvG/ValsA64.lean`),
  adding only start facts (the link words of `n0`, `n1` are initially 0). The
  conditional theorem is kept unchanged.

## x64 lowering pilot with a stack: whole-program theorem open

- `Lower/PilotX64*.lean` proves the per-thread pieces (`main_specX`, `hthr_pX`,
  `pilotX_final`) but no whole-program `pilotX_promising`. The x64 value bridge (`envGValsBridgeX_ofSpecs`) takes the *unrestricted*
  purity specs `RelPureSpecQX.Holds` (judgments in
  `(relPureQ Arch.tso ⊥).within S`), and these are **false** for this program:
  pop's link load is at an arbitrary answer `y` of the `top` load, and
  `within S` then requires `(y,8) ∈ S`. Closing it needs a guarded purity
  copy (`NoNTInvV`, `promisePure_tsoV`, `final_of_relPureSafelyQX_tsoFV'`) plus a `HoldsV` pass and assembly for the pilot. AArch64 is unaffected
  (`RelPureSpec` has no layout; `pilot2_promising` is unconditional).
- **Closed:** `Lower.PilotX.pilotX_promising` (`Lower/PilotX64Whole.lean`)
  proves the whole program on `Reachable Arch.tso fuel` from start facts only
  (`StartPX` for each thread, `top = 0`, the initial memory in `GV P`). The
  route: the text's judgments in the guarded environment
  `counted (relInvX (SL P) (GV P))`, its `HoldsV` at the starts, and
  `Vals.envGValsBridgeX_ofPure` (`Lower/KitX64ValsPure.lean`), which takes
  `HoldsV` in place of `Holds`; its ISA-neutral part is
  `Promising/SLR/PromisePureVals.lean`. The conditional
  `pilotX_promising_of_bridge_pure` is kept unchanged. The semantic-machine
  forms `pilotX_promising_sem`/`_semInf` (`Lower/PilotsX64Sem.lean`) go
  through `Vals.envGValsBridgeX_ofPure_sem`/`_semInf`
  (`Lower/KitX64ValsPureSem.lean`, `ReachableK` clones of the bridge and of
  `final_of_chainVP`); the concrete instance `Concrete.pilotX_concrete`
  (`Lower/PilotX64Concrete.lean`) is at the explorer's configuration of
  `Lower/PilotX64Prog.lean`, with no hypothesis beyond reachability.

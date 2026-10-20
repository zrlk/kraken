# The environment-aware wp (design note)

Design shape (ii). Lean: `Kraken/EnvWP.lean` (x64 interface,
`AllEnv`, step relation, wp, lifting theorem), `Kraken/Promising/EnvWPX64.lean`
(statements about the Promising machine as `Prop`s), example
`Kraken/X64/Examples/EnvWP.lean`.

## 1. Shape

A thread's `dmem` holds its private memory only. Every access outside `dmem`
is an *access to the environment*. The thread may issue it only if the
environment permits it (the **guarantee**, together with the access
discipline). The run continues from every outcome the environment allows (the
**rely**). Shape (i), *merged*, is the instance `SharedEnv.lastWrite L`, the
last write per location.

| Design point | Choice | Why |
|---|---|---|
| Where the import goes | `Kraken/EnvWP.lean` imports `Kraken.MachineWP` and nothing from `Kraken.Promising`. `Kraken/Promising/EnvWPX64.lean` imports both. | The interface is about the ISA's `Effects`. Only the link statements mention the Promising memory, so a change of `Val` or `Loc` touches one definition (`envRel`). The file sits next to `Step.lean`/`MachineWP.lean`, so the AArch64 copy is `Kraken/AArch64/EnvWP.lean`. |
| Values | `BitVec 128` payload plus a byte count (1, 2, 4, 8, 16) | The memory model's "width with a 128-bit payload". Independent of `Promising.Val`. |
| Interference | Not a separate step. It is folded into the outcomes `step` allows, and environment state changes only at the thread's own accesses. | This is why lifting costs nothing (§6). Matches the promise-free machine, where another thread's write changes only what a later read may return. |
| `dmem` | The environment never changes it. | `Device.lean`'s handlers can hand `dmem` back, which would let shared bytes move into `dmem`. Data ownership (for `pf_complete_drf`) is expressed in environment state instead (§5). |

## 2. The interface

```lean
inductive SharedAccess
  | load  (k : LoadKind)  (xcl : Bool) (addr) (bytes)                 -- Ret: BitVec 128
  | store (k : StoreKind) (xcl : Bool) (addr) (bytes) (v : BitVec 128) -- Ret: Bool (success)
  | rmw   (k : RmwKind) (addr) (bytes) (op : BitVec 128 → Option (BitVec 128)) -- Ret: old value
  | fence (k : FenceKind)                                               -- Ret: Unit
structure SharedEnv where
  State : Type
  ok    : SharedAccess → State → Prop                      -- guarantee + access discipline
  step  : (a : SharedAccess) → State → a.Ret → State → Prop -- rely
```

`AllEnv env g post` at an access `a` is `env.ok a g ∧ ∀ r g', env.step a g r g' → continue at g'`.

| `Effects` constructor | `All` | `AllEnv` |
|---|---|---|
| `done`, `undefined`, `require_*` (also `_avx`) | as usual | the same (`post` also sees the environment state) |
| `unimplemented`, `gp_unaligned` | `False` | `False` |
| `nonmem_load dmem a w` | `False` | `load .plain false a w.bytes`; the value at width `w` |
| `nonmem_store dmem a v` | `False` | `store .plain false a w.bytes v`; success ignored |
| `sync_load k xcl` / `sync_store k xcl` | `False` | `load k xcl` / `store k xcl`; the store passes its success `Bool` to the tree (AArch64 `STXR`) |
| `rmw k dmem a w op` | `False` | `rmw k a w.bytes (rmwOp128 w op)`; old value at width `w` |
| `fence k` | skip | `fence k`: permitted, and steps the state (views move at a barrier) |
| `nonmem_load_avx true` / `nonmem_store_avx true` (aligned 16-byte moves) | `False` | one access of `w.bytes` = 16 bytes (atomic) |
| `nonmem_load_avx false` / `nonmem_store_avx false` | `False` | `w.bytes / 8` plain 8-byte pieces in address order (`LoadPieces`/`StorePieces`). The pieces are reassembled little-endian (`ofPieces`/`toPieces`). A tear between pieces is observable. |
| `rmw16 k` (`lock cmpxchg16b`) | `False` | one `rmw k a 16 op` (atomic) |

Kinds are recorded in the access. An environment that tracks views gives them
meaning; `lastWrite` ignores them. On x86 the TSO profile does the ordering, so
x64 issues `.plain` loads and stores, `.acqRel` RMWs (`lock`, `xchg`) and
`fence .sy/.ld/.st`. The access discipline (exactly a location at its width,
each vector piece exactly an 8-byte location, line-crossing pieces
unsupported) is `ok`'s job. `AllEnv` has no layout of its own. A partial overlap
with a shared location cannot be mapped (the shared bytes are not in `dmem`),
so it reaches the environment as an access that `ok` refuses.

The step relation and wp mirror `Kraken.Step` and the `MachineWP` core over
`MachineState × env.State`: `Executable.stepAtEnv`, `instrStepEnv`, `wpEnv`
(`wpEnv_mono`, `wpEnv_cons`), `MachineWP.TripleEnv`, `Executable.ProcSpecEnv`.

## 3. Relation to the Promising machine's views

A thread of the promise-free machine has views (`coh l`, `vrOld`, `vrOldNR`, `vwOld`,
`vrNew`, `vwNew`, `vRel`, register views), and the shared memory is a message
list. A read of `l` returns any message to `l` with timestamp ≥ `coh l` and
the read's pre-view; a write appends a message.

| Promising | Environment |
|---|---|
| shared memory (messages) | not in the state. Other threads' messages show up as `step` outcomes. |
| thread views | part of `State` in an n-thread instance (or an abstraction: "has seen the release of `x`") |
| read: any message with ts ≥ view | `step (.load ..)`: the values of those messages that the global invariant allows |
| promise-free write: new message, views raised | `ok (.store ..)` (may this thread write `v`?) and `step` (raise views, update ghost state) |
| RMW (atomic, exclusive pair) | one `rmw` access, or `load xcl` and `store xcl` with a success `Bool` |
| fence: views raised | `step (.fence k)` |
| one thread (`merged_link`) | `lastWrite L`: `State` = the value of each location; a load returns it, a store or RMW replaces it |

`envRel L g mem` relates `lastWrite`'s state to a Promising memory
(`g a` = `finalVal` at the location's width). `MergeRel L d g D` is `MemRel`
with `g` in place of the memory.

## 4. What a thread's proof hands to the §5.2 logic

A thread `t` proves `ProcSpecEnv (E t) entry Pre Post` (or a `TripleEnv`) for
a rely/guarantee environment `E t`. The §5.2 logic discharges two things once,
for all `t` (and for symmetric threads, by one lemma quantified over `t ≠ t'`):

1. **Rely is sound**: in every reachable promise-free configuration satisfying
   the global invariant, every value the machine lets `t` read is allowed by
   `(E t).step`, and the views move as `step` says.
2. **Guarantee implies the others' rely**: every access `(E t).ok` permits
   preserves the global invariant, and with it every `t' ≠ t`'s rely.

The per-thread judgment says nothing about other threads, so it is a theorem
about the thread's code alone. The `MachineWP` rules do the register and
private-memory part of every instruction (conservativity, §5.2 last bullet),
and the shared-location rules do the accesses.

**Spinlock sketch** (lock word `L`, data `X` written only in the critical
section, invariant `Inv` on `X` when the lock is free):

| | |
|---|---|
| `State` | `held : Bool`, `x : Option Val` (the value of `X` this thread may rely on), views abstracted as "saw the last release of `L`" |
| `ok (load/rmw L)` | always (anyone may test and try the lock) |
| `step (rmw .acqRel L (fun _ => some 1))` (`xchg`) | `old = 0 ∧ held' ∧ x' = some v` for some `v` with `Inv v` (acquire: the previous holder's release is seen), **or** `old = 1 ∧` state unchanged |
| `step (load L)` | any `0`/`1`, state unchanged (test before test-and-set) |
| `ok (store X v)` | `held` (guarantee: only the holder writes data) |
| `step (store X v)` | `x' = some v` |
| `step (load X)` | `held → r = x` (**no interference**: owned). With `¬held` the thread may not read `X` at all (`ok` is `False`). |
| `ok (store L 0)` (on x86 a plain store, which TSO makes a release; `STLR` on AArch64) | `held ∧ x = some v ∧ Inv v` (guarantee: release with the invariant re-established) |
| `step (store L 0)` | `held' = false`, `x' = none` |

Mutual exclusion is then rely-soundness of this environment for every thread,
which is §5.3's invariant.

## 5. Fit with `pf_complete_drf`

`pf_complete_drf` needs (a) ordered writes to sync locations and (b)
`DataRaceFreePF`: data accesses see the last write in every promise-free run.
Ownership is environment state: "data location `l` is owned by this thread now"
is a `State` predicate under which `step (load l)` returns exactly the
thread's own last write and `ok` permits writes to `l`. Without ownership,
`ok` refuses every data access. So:

- a thread proof in such an environment never touches an unowned data location
  (`ok` is `False` there);
- rely-soundness for owned locations is exactly "no other thread writes `l`
  meanwhile", the DRF obligation (b);
- sync locations are those `ok` lets every thread access; the ordered-write
  condition (a) is a syntactic property of their kinds (`.rel` stores,
  `.acqRel` RMWs) that the access records.

So the per-thread judgments plus interference freedom give `DataRaceFreePF`
as a corollary instead of a separate proof. On x64 every program is
write-ordered (`pf_complete_ordered` suffices); the ownership discipline is
still how the proofs are structured.

## 6. The lifting theorem: proved, free

| Level | Theorem |
|---|---|
| one tree | `Effects.allEnv_of_all (hI : env.FenceInv I) : e.All post → ∀ g, I g → e.AllEnv env g (fun s g' => post s ∧ I g')` |
| one instruction | `Executable.instrStepEnv_of_instrStep` |
| runs | `Executable.eventually_instrStepEnv_of_instrStep : Eventually e.instrStep P st → ∀ g, I g → Eventually (e.instrStepEnv env) (fun x => P x.1 ∧ I x.2) (st, g)` |
| wp | `Executable.wpEnv_of_wp` |
| triples | `MachineWP.wpEnv_of_triple : ⦃P⦄ q ⦃Q; E⦄ → TripleEnv env (P ∧ I) q (Q ∧ I) (E ∧ I)` |
| procedures | `Executable.ProcSpec.env` |

`All` is `False` wherever `AllEnv` consults the environment, with one
exception: fences. `All` skips a fence, while `AllEnv` asks the environment.
So the lift carries any invariant `I` of the environment state that fences
permit and preserve (`FenceInv`). With `FencesSkip` (fences are permitted and
change nothing; true of `none`, `lastWrite` and any environment without
views) `I` can be `(· = g)`: the state is literally unchanged across lifted
code. With views, `I` is "views ≥ some floor", which a fence preserves. No
monotonicity issue arises, because environment state moves only at the thread's
own accesses (§1). Sanity check: `Effects.allEnv_none_iff`, where `AllEnv` in
the empty environment is `All`.

## 7. AArch64: proved

AArch64's `Effects` has the same access constructors (`nonmem_load/store`,
`sync_load/store` with `xcl`, `rmw`, `fence`), no vector cases, and
`unaligned_sp` (which stays `False`). The port:

| Piece | Names | Where |
|---|---|---|
| ISA-free core, shared by both ISAs | `SharedAccess`, `SharedEnv`, `LoadPieces`/`StorePieces`, `piecesNat`/`ofPieces`/`toPieces`, `FenceInv`/`FencesSkip`, `SharedEnv.none`, `Layout`, `upd`, `lastWrite`, `rmwOpBits` | `Kraken/SharedEnv.lean` |
| ISA-free merge | `envRel`, `MergeRel`, `gmem`, `gmem_finalVal`, `mergeRel_iff`, `sharedBytes_gmem`, `exists_merge`, `memRel_iff_mergeRel_of_envRel` | `Kraken/Promising/EnvMerge.lean` |
| `AllEnv` (no AVX cases; `STXR`'s success comes from `step`, the `∀ ok` pattern of the store-exclusive rules), `stepAtEnv`, `instrStepEnv`, `wpEnv`, `TripleEnv`, `ProcSpecEnv`, `wpEnv_of_triple` | same names as x64 | `Kraken/AArch64/EnvWP.lean` |
| Environment rules | `ldr/str/ldrb/ldrh/strb/strh/ldp/stp/ldar/stlr/stxr/cas/swp/ldop/dmb/dsb/isb_shared`, pairs: `casp_shared`, `casp_lastWrite`, `dmb/dsb/isb_skip`; unscaled and literal: `ldur/stur/ldurb/ldurh/sturb/sturh/ldr_lit_shared`, `ldr_pool_env` | `Kraken/AArch64/EnvWPRules.lean` |
| `MemRelIffMergeRel`, `LastWriteToMerged`, `EnvLinkHalt` | `memRel_iff_mergeRel`, `lastWrite_to_merged`, `env_link_halt` (and `instrStepEnv_step1W`) | `Kraken/Promising/EnvWPAArch64.lean` (`Program.instrStepEnv_of_tripleEnv` in `SeqLinkAArch64Prog.lean`) |
| CAS example | `cas_correctEnv`, `cas_layout_wf`, `cas_promising` (no `hpres`/`hacc`/`h0`) | `Kraken/AArch64/Examples/AtomicsLink.lean` |

The statements `MemRelIffMergeRel` etc. live in the Promising link file, as
for x64 (they mention `Memory`). `LDP`/`STP` have a rule only for both slots
shared. The `LDR`/`STR` rules take any `AddrExpr`, so pre- and post-indexed
and register-offset forms are covered. The unscaled forms are covered too
(`LDUR`/`STUR` and the byte/halfword `LDURB`/`LDURH`/`STURB`/`STURH`) and the
literal loads: `LDR Rt, label` reads the label's address through `dmem` like
any load, and nothing keeps that address out of `L`, so it has a shared rule
(`ldr_lit_shared`); `LDR Rt, =expr` reads no memory in Kraken's semantics (the
pool constant is the value), so it is never a shared access and its rule
(`ldr_pool_env`) holds in every environment. So are the sign-extending
loads: `MachineWP` mapped rules (`ldrsb_spec` … `ldpsw_spec`,
`Kraken/AArch64/WP/RulesSignExt.lean`), shared rules (`ldrsb_shared` …
`ldpsw_shared`, `ldrsw_lit_shared`, `ldrsw_pool_env`) and combined rules
(`ldrsb_env_spec` … `ldrsw_pool_env_spec`; examples in
`AArch64/Examples/WPSignExt.lean`). `CASP` is covered (`casp_shared`,
`casp_lastWrite`; "Pair effects" below). So are FEAT_LSE2 16-byte
`LDP`/`STP` (`ldp_lse2_shared`, `stp_lse2_shared`, linked to `isaLSE2` by
`env_link_halt_lse2`; same subsection). Not covered: `LDXP/STXP` with both
halves shared (same subsection).

Open: `SharedAccess.rmw` has no `noRet` field (AArch64's `rmw` effect does);
a view-tracking environment (Stage 2) will need it, since an `LDADD` to `XZR`
orders differently from one that returns.

## 8. The link statements: proved

| Statement | Proof | Where |
|---|---|---|
| `MachineWP.MovStoreSharedRule`, `MachineWP.XchgSharedRule` and siblings | `mov_load_shared`, `mov32_load_shared`, `mov_store_shared`, `mov32_store_shared`, `xchg_shared`, `lock_cmpxchg_shared`, `lock_xadd_shared`, `lock_bin_imm_shared`, `lock_bin_reg_shared`, `mfence/lfence/sfence_shared`, `movdqa/movapd_load/store_shared` (one atomic 16-byte access), `movdqu/movups_load/store_shared` (two 8-byte pieces), `lock_cmpxchg16b_shared`; for parity with the `MachineWP` mapped rules: `lock_un_shared`, `mov8_load_shared`, `mov8_store_imm/reg_shared`, `movsxd_load_sib_shared`, `cmp32_mem_imm_shared`, `movaps_load/store_shared`; the VEX moves of every `AvxWidth` (`vmovdqa/vmovapd/vmovdqu_load/store_shared`, by `SharedEnv.AvxLoad`/`AvxStore`), the SIB `movaps`/`vmovaps`/`vmovups` and the packed arithmetic with a memory source (`mulps`, `xorps`, `vmulps`, `vfmadd231ps`); the shapes still without a rule are tabled in the file's header | `Kraken/EnvWPRules.lean` (the statements stay in `Kraken/EnvWP.lean`) |
| `MemRelIffMergeRel`: `MemRel L d mem D ↔ MergeRel L d g D` under `envRel L g mem` | `memRel_iff_mergeRel` | `Kraken/Promising/EnvWPX64.lean` |
| `LastWriteToMerged`: shape (ii) in `lastWrite L` ⇒ shape (i) (`step1W L`) on the merge | `lastWrite_to_merged` | same |
| `EnvLinkHalt`: an environment judgment from `(s, pc)` and `g ~ mem` holds, with some `g' ~ c.mem`, at the end of every halting promise-free run | `env_link_halt` (by `LastWriteToMerged` and `merged_link_halt`) | same |

The hypothesis that remains is `ValidLayout` (for `instrStep` to `step1`);
There is no `NoAvx` hypothesis, as for `merged_link`. There is no `hpres`/`hacc`/`h0`:
`AllEnv` in `lastWrite L` refuses every access that is not exactly a location
of `L`, which is the access discipline of `step1W`.

How `LastWriteToMerged` goes: `gmem L g` is a message-free Promising memory
with initial values `g` on `L`, so `MergeRel L d g D` is
`MemRel L d (gmem L g) D` (`mergeRel_iff`) and `MergedMem`'s lemmas serve the
environment state. Per primitive, `load_esim` … `rmw16Plain_esim` are the
converse of `SeqLinkX64`'s `*_sim` (split tree under `AllEnv`, merged tree
under `AllW`, distinct continuations). `esim_search` lifts them to
`operation_esim`/`avxOperation_esim`/`directive_esim` as `sim_search` does,
and `instrStepEnv_step1W` is one instruction. `env_link_halt` builds the
merge of the start state (`exists_merge`). At the end it recovers the split
state's `dmem` by extensionality and `envRel` from the two `loadBytes`
equations on the footprint.

The CAS example uses all of it: `casIncr_correctEnv` and `casIncr_promising` in
`Kraken/X64/Examples/AtomicsLink.lean`.

**Deviation: the rules are not `@[spec]`.** `@[spec]` refuses a `TripleEnv`
("neither a Hoare triple …"): `vcgen` only knows the `Std.WP.WP` instance of
`Program`, whose predicate is `MachineData → Prop`. So the rules are plain
theorems. A proof chains them by hand: `Executable.wpEnv_cons` cuts off one
instruction, `MachineWP.wpEnv_of_triple` (with
`(lastWrite_fencesSkip L).fenceInv_eq g`) lifts a `vcgen` triple of the
memory-free parts, and the shared rule handles each shared access
(`casIncr_correctEnv` is the pattern). The next section restates them over
`EnvProgram`, where `@[spec]` accepts them.

### `vcgen` over `wpEnv`

Built: `Kraken/EnvVCGen.lean` (x64), `Kraken/AArch64/EnvVCGen.lean`.

- *Program type and `WP` instance.* `structure EnvProgram (env) where prog :
  Program` with the scoped instance `MachineWP.instWPEnv` (`Pred :=
  MachineData → env.State → Prop`, `wp := cenv.wpEnv env prog`). Its triple
  is `TripleEnv`: `TripleEnv.of_triple` turns a `TripleEnv` goal into a
  `vcgen` goal on `⟨p⟩ : EnvProgram env`, and `TripleEnv.triple` turns a
  `TripleEnv` rule into a `@[spec]` one (weakening the precondition).
- *One generic rule, no copies.* `env_lift_spec` (`@[spec low]`, needs
  `[env.Skips]`, a class wrapping `FencesSkip`, with instances for `none` and
  `lastWrite L`) steps the first directive `d` of `⟨d :: p⟩` by the `Program`
  wp of `[d]` and passes `g` through to the wp of `⟨p⟩`. So every
  `MachineWP` rule serves the environment wp unchanged: `vcgen` meets
  `[d]` inside the precondition and uses the existing `Program` specs.
  `env_nil_spec` ends the program. The spec lookup is keyed only on the
  program expression, so the `EnvProgram` rules and the `Program` rules never
  compete.
- *Rule priority.* The atomic and read-modify-write shapes (x64 `xchg`,
  `lock cmpxchg`/`xadd`/`<op>`, `lock cmpxchg16b`; AArch64 `LDAR` and kin,
  `STLR`, `STXR`, `CAS`, `SWP`, `LD<op>`) are `@[spec]` (`*_shared_spec`):
  above the generic rule, so they go to the environment. On a location in
  `dmem` erase the rule for that call (`vcgen [-lock_xadd_shared_spec]`).
  Fences are `@[spec 50]`, below the generic rule, which steps them as no-ops
  wherever `Skips` holds. Vector, narrow and paired accesses (`movdqa` …,
  `LDRB`/`LDRH`/`STRB`/`STRH`/`LDP`/`STP`) are not registered: pass them to
  the `vcgen` call that needs them.
- *Combined rules for plain moves.* x64 `movq`/`movl` loads and stores and
  AArch64 `LDR`/`STR` (`*_env_spec`, `@[spec]`) decide by `dmem`: if the
  address is mapped the access is a `dmem` access, otherwise an environment
  access. The precondition is one disjunction in front of one continuation,
  so `vcgen` does not branch (a `⊓` of two implications would make it
  continue twice) and the same rule serves a private slot and a shared
  location. These rules need no `Skips`.
- *Use.* `apply TripleEnv.of_triple; unfold prog; vcgen`, then discharge the
  VCs (`simp_all [SharedEnv.lastWrite, and_assoc, …]`). The `unfold` is
  required: `vcgen [prog]` does not unfold under `EnvProgram.mk`.
- *Examples.* `casIncr_correctEnv'` and `cas_correctEnv'` re-prove the CAS
  example's statements by `vcgen`; `fetchAddStash_correctEnv`
  (`X64/Examples/EnvVCGen.lean`) and `incStash_correctEnv`
  (`AArch64/Examples/EnvVCGen.lean`) mix a shared atomic, ALU, a private slot
  and plain loads of both kinds in one `vcgen` call.

Open:

- Environments with views need `FenceInv` per invariant, not `FencesSkip`;
  `env_lift_spec` does not apply to them (Stage 2).
- ~~No environment version of `cfg`/loops~~: done below ("Control flow over `wpEnv`").
- x64 parity: `lock inc/dec/neg/not` is `@[spec]` (`lock_un_shared_spec`);
  the byte moves, `movslq (%b,%i,s)`, `cmpl $i, d(%b)` and `movaps` have
  unregistered `*_shared_spec` rules (example `incFlag_correctEnv`).
- x64 parity: the VEX moves, the SIB `movaps`/`vmovaps`/`vmovups` and
  the packed arithmetic with a memory source have unregistered
  `*_shared_spec` rules (example `vexShared_correctEnv`). `vcgen` does not
  enter the continuations of `LoadPieces`/`StorePieces`/`AvxLoad`/`AvxStore`:
  the proof reduces them (`AvxLoad_true`, `AvxStore_false`, …), splits the
  pieces with `refine` and calls `vcgen` again behind them. ~~Done by hand~~:
  `vcgen_env [rules]` (`Kraken/EnvVCGen.lean`) does it, one
  introduction rule per access or piece (`SharedEnv.StorePieces.intro_cons`,
  `LoadPieces.intro_succ`, `AvxLoad.intro_pieces_W256`, …; the counts are
  literals per width, `w.bytes / 8` does not unify with `n + 1`) and `vcgen`
  again on the tail only; `vcgen` itself is unchanged. Examples:
  `vexShared_correctEnv` re-proved, `vexPieces_correctEnv` (four piece loads,
  a `W256` `vmovdqa` store in pieces).
- Combined rules exist only for 64/32-bit `mov` (x64) and `LDR`/`STR`,
  `LDUR`/`STUR` and the literal `LDR`s (AArch64: `ldur_env_spec`,
  `stur_env_spec`, `ldr_lit_env_spec`, `ldr_pool_env_spec`, example
  `sturLdur_correctEnv`); x64 also has `push`/`pop` of a register, `ret` and
  `jmp *d(%b)` (`push_reg_env_spec`, `pop_reg_env_spec`, `ret_env_spec`,
  `jmp_mem_base_disp_env_spec`, `@[spec]`; `ret` and the jump end in the exit
  `E`), `call_env_spec` (not `@[spec]`, as `call_spec`; there is also the
  procedure-spec form `call_proc_env_spec`/`_at` over `ProcSpecEnv`, with
  `ProcSpecEnv.of_tripleEnv`, example `fetchIncCall_correctEnv`,
  `X64/Examples/EnvProcCall.lean`; the continuation form `call_proc_specK*`
  still has none), and the AArch64
  sign-extending loads (`ldrsb_env_spec` …). Examples: `stackShared_correctEnv`,
  `jmpShared_correctEnv`, `sext_correctEnv`. Other plain accesses to shared
  locations need their unregistered rule.
- A locked operation on a private (`dmem`) location in an `EnvProgram` needs
  `vcgen [-rule]`.

### Control flow over `wpEnv`

Built: `Kraken/Safely.lean`, `Kraken/SharedEnvCounted.lean`,
`Kraken/EnvCfg.lean` (x64), `Kraken/AArch64/EnvCfg.lean`,
`Kraken/Promising/SeqLinkSafe.lean`, `Kraken/Promising/EnvLinkSafe{X64,AArch64}.lean`;
examples `X64/Examples/EnvCasLoop.lean`, `AArch64/Examples/EnvLLSCLoop.lean`.

- *Total rule.* `MachineWP.cfgEnv` is `cfg` with the table and the variant
  reading `(s, g)`, one `EnvProgram` triple per block (so `vcgen` proves the
  blocks), a back edge decreasing the variant (`Program.EdgeLtEnv`), built on
  `Program.linkEnv`. The conclusion is a `TripleEnv`, so
  `Program.instrStepEnv_of_tripleEnv` and `env_link_halt` apply unchanged.
  `cfg_cases_env [p]` splits the block obligation per block (it stops before
  the snapshot binders, `∀ n` or `∀ s₀ g₀`).
- *Partial rule.* `MachineWP.cfgEnv_partial` has no variant and concludes a
  `PartialTripleEnv`: `Safely` (`Kraken/Safely.lean`, ISA-free: an invariant
  that holds now and, outside the postcondition, admits a step and is kept by
  every successor) in place of `Eventually`.
- *Zero-step guard.* A block triple may hold by taking an exit in zero steps,
  so without a variant two blocks jumping to each other prove anything
  (`Program.unguardedLinkEnvPartial_false`, the recorded counterexample). A
  jump exit of the partial rule therefore goes forward in the text or leaves
  the block's entry state (`Program.EdgeSafe`). Where the state may come back
  unchanged (a failed `STXR` in `lastWrite`), `SharedEnv.counted env` adds a
  ghost count of shared accesses; `MachineWP.PartialTripleEnv.uncount`
  projects it away (`∃ n` in pre- and postconditions).
- *At the machine and the Promising machine.*
  `Program.instrStepEnv_of_partialTripleEnv` reads a partial triple as
  `Safely` from the start address. `env_link_halt_safe` (both ISAs; generic
  part `SeqReach.sim_safe`/`reachablePF_sim_safe`) is `env_link_halt` with
  `Safely` for `Eventually` and `hstuck` (no environment step at `endPc`,
  given by `not_instrStepEnv_of_end`) for `hstop`. What a theorem proved by
  `cfgEnv_partial` says about the Promising machine, precisely: for every
  promise-free one-thread run from a message-free memory whose thread has
  reached `endPc`, the final thread state and some environment state related
  to the final memory satisfy the postcondition. Runs that never reach
  `endPc` (a loop that keeps retrying) are not constrained at all.
- *Examples.* x64: `casLoop` (`movq`; `leaq`; `lock cmpxchgq`; `jne retry`)
  by `cfgEnv` in `lastWrite` (the compare after loading an unchanged location
  succeeds, variant `0`), carried by `env_link_halt` (`casLoop_promising`).
  AArch64: `llscInc` (`ldxr`; `add`; `stxr`; `cbnz retry`) is not totally
  correct even in `lastWrite`, so it is proved by `cfgEnv_partial` in
  `counted (lastWrite L)` (`llscInc_correctCounted`, the back edge is the only
  VC needing the counter), projected, and carried by `env_link_halt_safe`
  (`llscInc_promising`). Neither needs `hpres`/`hacc`/`h0`.

Open:

- Termination of an LL/SC loop needs an environment in which a
  store-exclusive eventually succeeds (Stage 3's progress hypothesis);
  `lastWrite` gives partial correctness only.
- The rules are one-thread (`lastWrite`); environments with views (Stage 2)
  reuse `cfgEnv`/`cfgEnv_partial` unchanged, but not the link.

### LSE loops (AArch64)

Built: `AArch64/Examples/EnvLSELoops.lean`. No new rules: `cfgEnv`,
`cfgEnv_partial`, the `@[spec]` LSE rules (`cas_shared_spec`,
`swp_shared_spec`, `ldop_shared_spec`) and the existing links suffice.

- *Total.* `casInc` (`ldr`; `add`; `mov`; `casal`; `cmp`; `b.ne retry`) by
  `cfgEnv` in `lastWrite [(a, 8)]`, with a real variant: `1` at `retry` while
  `x1` is stale, `0` otherwise. A failed `casal` returns the slot's value in
  `x1`, and in `lastWrite` nothing changes the slot in between, so the next
  attempt succeeds (the loop head admits any `x1`; contrast x64's `casLoop`,
  whose head reloads and so needs variant `0` only). The loop-free `ldaddal`
  fetch-and-increment and `swpal` test-and-set are one `vcgen` call each. The
  `swpa` spinlock acquire (`spinlock_swp2.kl`) is total only from a free
  lock: in `lastWrite` no other thread releases a held lock.
- *Partial.* The same acquire with no hypothesis on the lock, by
  `cfgEnv_partial` in `counted (lastWrite L)`: the back edges (spin on `ldr`,
  retry `swpa`) may return to the entry state, but each passes a shared
  access, which moves the counter.
- *At the machine and the Promising machine.* Total theorems give
  `Eventually` at the machine (`casInc_terminates`, `swpAcquire_terminates`)
  and, by `env_link_halt`, the postcondition for every promise-free
  one-thread run that reaches `endPc` (`*_promising`); the partial one goes
  through `uncount` and `env_link_halt_safe` (`swpAcquire_promising_partial`).
  Neither link states termination on the Promising machine;
  `env_link_terminates` does (`casInc_terminates_promising`,
  `swpAcquire_terminates_promising`; see "Termination on the Promising
  machine" below).
- *Layout.* `step1W_stop_of_end`/`not_instrStepEnv_of_end` require the last
  cell to be an instruction (a trailing label fails their `hd` default), so a
  loop whose exit is a forward jump past its last block is laid out with the
  exit as the fall-through (`swpAcquire` enters with `b try`). The
  trailing-label variants `step1W_stop_of_end_labels`,
  `not_instrStep_of_end_labels`, `not_instrStepEnv_of_end_labels` (both ISAs;
  the last instruction is cell `p.length - 1 - k`, followed by `k` labels) lift this:
  `swpAcquireNat` is the acquire in its natural layout (`cbz w2, done` …
  `done:`), with total correctness, Promising termination and the halting-run
  theorem.
- *LL/SC* is deferred in the Stage 2/3 logic (scope
  box); `llscInc` stays as the partial example.

### Pair effects (AArch64)

Built: `SharedEnv.CaspEnv`, the `rmw_pair` case of `AllEnv`
(`AArch64/EnvWP.lean`), its link case in `rmwPairK_esim`
(`Promising/EnvWPAArch64.lean`), the rules `casp_shared`/`casp_lastWrite`
(`AArch64/EnvWPRules.lean`), the specs `casp_shared_spec` (`@[spec]`) and
`casp_lastWrite_spec` (`@[spec high]`, picked by `vcgen` in `lastWrite`;
`AArch64/EnvVCGen.lean`), and the examples in `AArch64/Examples/EnvCASP.lean`.

- *`CASP` is two accesses, not one.* The Promising machine performs a `CASP`
  with both halves shared as `caspTree` (`Promising/AArch64.lean`): two 8-byte
  (or 4-byte) `rmw`s, one per half, in either order, with the success bit
  chosen up front and checked against the values read; herd likewise
  sequences the halves (`>>|`), it does not make the pair single-copy atomic.
  So `CaspEnv` asks, for every `succ` and both orders, for two `.rmw` accesses
  (each half's op writes its new value only when `succ` and that half
  matches), and the continuation only when the two values read agree with
  `succ`. An atomic 16-byte reading would be stricter than the machine.
  `All`/`AllW` stay `False` on pairs (no change to the `dmem`-only logic); a
  pair with a half in `dmem` keeps its single-access cases.
- *`lastWrite`.* Different locations, so the order does not matter:
  `lastWrite_caspEnv_iff` reduces `CaspEnv` to both halves in `L` and the
  continuation at `caspLW g …` (both writes on a match of both halves, else
  `g`). `caspLW` is a definition over `(lastWrite L).State`, not an `if` over
  functions: `vcgen` silently fails to apply a spec whose environment-state
  argument only type checks after unfolding `(lastWrite L).State`.
  `caspLW_apply` reads it pointwise for `simp`.
- *Examples.* `vpBump` (loop-free `ldp`; `caspal`) and `vpUpdate` (the
  versioned-pointer retry loop, total by `cfgEnv` with variant `1` at `retry`
  while `x2:x3` is stale) on `lastWrite [(a, 8), (a + 8, 8)]`, each carried to
  the Promising machine by `env_link_halt` (`vpBump_promising`,
  `vpUpdate_promising`; `vpUpdate_terminates` at the machine).
- *Deferred: `LDXP`/`STXP`* with both halves shared (`sync_load_pair`/
  `sync_store_pair` stay `False` in `AllEnv`), with LL/SC.
- *FEAT_LSE2 16-byte `LDP`/`STP`.* `Executable.step` (ISA `isa`) never
  emits a non-exclusive pair effect; only `isaLSE2.lse2Effects` does, and
  `toEv` makes it one 16-byte access exactly on a declared 16-byte location
  (`pairIsOneLoc`), two plain accesses otherwise. The reading is shared:
  `Directive.interpLSE2?` (`AArch64/LSE2.lean`) is the FEAT_LSE2 reading of
  a cell (an aligned 64-bit `LDP`/`STP`), used by `lse2Effects` (refactored to
  it, litmus results unchanged) and by the environment logic.
  Built: `AArch64/EnvLSE2.lean` (`Effects.AllEnvLSE2 D env`, `AllEnv` with
  the `sync_load_pair`/`sync_store_pair` cases for `xcl = false` relative to a
  list `D` of 16-byte locations: one 16-byte `.plain` access if
  `(addr, 2 * w.bytes) ∈ D`, the two accesses otherwise; the
  `instrStepEnvLSE2`/`wpEnvLSE2`/`TripleEnvLSE2` chain over
  `Directive.interpLSE2`; the embedding `TripleEnvLSE2.of_tripleEnv` of every
  `TripleEnv`; the rules `ldp_lse2_shared`/`stp_lse2_shared` and their
  `vcgen` specs, with `env_lse2_lift_spec` lifting every `EnvProgram` spec
  under `SharedEnv.LSE2Disc D env`), `AArch64/EnvLSE2Sound.lean`
  (`Directive.interpLSE2_sound`), `Promising/EnvLSE2AArch64.lean` (the link:
  `allEnvLSE2_seq`, `seqSim_lse2`, `env_link_halt_lse2`) and the example
  `AArch64/Examples/EnvLSE2.lean` (`publish16_correctEnv`,
  `publish16_promising`).
  - *The link is direct.* Both sides run the same `MachineState`; the thread
    is related to the judgment's state by `RelLSE2` (same state, decls
    `declsOf L`) and the environment state to the memory by `envRel` alone,
    with no merged state and no `hsplit`: a byte in `dmem` is read from `dmem`
    on both sides. `MemRel`/`MergeRel` need nothing for 16-byte locations.
  - *`decls = declsOf L` is a choice made for the link only.* `isaLSE2`,
    `isa` and the litmus runs are unchanged (each reads the `decls` its thread
    has); `env_link_halt_lse2` speaks about the runs whose thread declares
    exactly the layout `L` (every location at its width), with `D = L`.
  - *Mixed-size access: neither side claims anything.* `lastWrite L` permits
    an access only at a location's exact address and width (and
    `LSE2Disc` asks an environment to refuse the 8-byte low half of a
    16-byte location of `D`); the machine with `declsOf L` resolves such an
    access to a mixed-size fault (`Decls.resolve`), whose runs `AllSeq` does
    not constrain.
  - *`LSE2Disc`.* The lifting of the `AllEnv` rules (`env_lse2_lift_spec`)
    needs the environment to refuse an 8-byte plain access at a 16-byte
    location of `D` and to accept every plain store; `lastWrite_lse2Disc`
    (and `lastWrite_lse2Disc_of_wf` for a well-formed layout) discharges it
    for `lastWrite`.
  - *`vcgen`.* `ldp_lse2_shared_spec`/`stp_lse2_shared_spec` are `@[spec]`;
    on a pair whose bytes are in `dmem` erase them
    (`vcgen [-MachineWP.ldp_lse2_shared_spec]`).
  - *Not covered:* `LDXP`/`STXP` (`xcl = true`, `AllEnvLSE2` stays `False`),
    termination for `isaLSE2`, and x64 (no FEAT_LSE2 analogue).

### Termination on the Promising machine

Built: `Kraken/Promising/SeqLinkTerm.lean` (ISA-free),
`Kraken/Promising/EnvLinkTerm{X64,AArch64}.lean`; examples
`casLoop_terminates` (x64), `casInc_terminates_promising`,
`swpAcquire_terminates_promising`, `swpAcquireNat_terminates_promising`
(AArch64).

- *Two statements.* `StepPF A fuel c R`: every promise-free successor of `c`
  satisfies `R` (no successor asked for). `Eventually (StepPF A fuel) Q c` is
  **no divergence**: no infinite promise-free run from `c` avoids `Q`; a run
  may stop early (a faulting thread has no successor). `StepPF'` also asks for
  a promise-free successor; `Eventually (StepPF' A fuel) Q c` is
  **termination**: every maximal promise-free run is finite and ends in `Q`.
  `fuel` plays no role (a promise-free instruction step certifies nothing);
  both hold for every `fuel`. `eventually_stepPF_bounded` gives a uniform
  bound on the run length (`BoundedPF`, König: `succs` is finite).
- *No divergence, free.* `env_link_no_div` (each ISA): `env_link_halt`'s
  premises without `hstop` give `Eventually (StepPF A fuel)` of `EndIn` (the
  thread at `endPc`, the final state and an environment state related to the
  final memory satisfying the postcondition) from the start configuration.
- *Termination.* `env_link_terminates` adds two premises: `hstuck` (no
  environment step at `endPc`: `not_instrStepEnv_of_end` or its `_labels`
  variant) and `DirsNoFault e` (no directive's effect tree, translated by the
  adapter, contains a `fault` leaf or an empty `choose`), and concludes
  `Eventually (StepPF' A fuel)`. Inside, `EvTree.SeqOk` (a sequential run of
  the tree that the machine takes too: a plain store succeeds, an exclusive
  store fails, a `choose` takes some branch) is what turns a step of the
  environment judgment into a promise-free machine step (`runTree_seqOk`,
  `succs_seqOk`); `EvTree.NoFault.seqOk` discharges it from `DirsNoFault`.
- *Discharging `DirsNoFault`.* The tactic `dirs_no_fault p` (each ISA) proves
  `DirsNoFault (layout p)` for a program defined by name: one `simp` per
  directive through the semantics and `toEv`, splitting on whether each
  access is mapped. The examples' final theorems carry neither `SeqOk` nor
  `DirsNoFault`.

Open:

- **Adapter faults vs. single-threaded `undefined`.** The adapters
  (`Kraken/Promising/X64.lean`, `AArch64.lean`) translate an `undefined` value
  of a register, vector or flags type into `.fault` (a Boolean `undefined`
  becomes `choose 2`), and a vector piece that crosses a cache line into
  `.fault` too, while `Effects.All`/`AllEnv` (and so every triple, `cfgEnv`
  and the environment links) let an `undefined` value be arbitrary and
  constrain no piece's line. Examples: x64 `shrd` with a masked count at
  least the width (`if count >= w.bits then undefined setstatus`, flags),
  `bswap` at 16 bits (`| _ => undefined (fun v => …)`, a register). AArch64's
  semantics uses `undefined` only at `Bool` today (the spurious `STXR`
  failure), which the adapter turns into `choose 2`; its register/flags
  branches would fault in the same way if a rule used them. Such an
  instruction can be totally correct by `cfgEnv` and still fault on the
  Promising machine. **The single-threaded semantics is authoritative** for
  what an instruction does; the adapter's `fault` is a conservative stand-in
  (it only removes runs, so `env_link_halt`, `env_link_halt_safe` and
  `env_link_no_div` stay sound), and termination is where the gap shows:
  `DirsNoFault` cannot be discharged for such a program, so
  `env_link_terminates` does not apply to it. Closing the gap means
  translating a register/flags `undefined` into a `choose` over a finite
  witness set or an unconstrained value (needs `EvTree.choose` over the type,
  not `Fin n`), and deciding the line-crossing policy at the
  single-threaded level; adapters unchanged by termination.
- Termination is one-thread and in `lastWrite`, like the rest of the link;
  LL/SC loops still need Stage 3's progress hypothesis.
- `dirs_no_fault` unfolds the whole semantics per directive; on large
  programs it may need the per-instruction lemma `dirsNoFault_layout` with
  hand-written `DirNoFault` facts.

## Invariant environment

The sections above prove one thread against an environment that fixes the shared
locations' values (`lastWrite`). The invariant environment extends this to *several*
threads: each thread is proved alone, by `vcgen`/`cfgEnv`/`TripleEnv` as
before, against

```lean
SharedEnv.inv (S : Layout) (G : Loc → Val → Prop)   -- Kraken/SharedEnvInv.lean
```

`S` lists the shared locations (address, width in bytes), `G` is a value
invariant per location. An access must be exactly a location of `S`; a read
returns *any* value satisfying `G`; a store's value must satisfy `G`; an
`rmw`'s `op` must map every `G`-old value to a `G`-new value (a failed
compare writes nothing); a store succeeds unless exclusive; fences are
permitted and do nothing (`FencesSkip`, so the fence rules apply). The
existing `@[spec]` shared rules are generic in the environment, so `vcgen`
works unchanged; the `inv_ok_*`/`inv_step_*` simp lemmas turn its side
conditions into `(a, n) ∈ S` and `G` facts.

**The link (ISA-free core `Kraken/Promising/InvLink.lean`).**
`EvTree.AllInv G Q` says a semantics tree's reads may return anything in `G`,
its writes satisfy `G`, and its leaves satisfy `Q`; `stepOne_allInv` turns that
into "every outcome of `stepOne` from a `MemInv G` memory has a `MemInv G`
memory and a `Q` state". `StepPreserves A G J` (each instruction keeps the
per-thread invariant `J` and `MemInv G`) gives `configInv_reachable` (both at
every `Reachable` configuration: promise steps, certification and
interleavings included, since promised messages are checked by the
`WritesPreserve`/`write_invariant` argument) and
`writesPreserve_of_stepPreserves` (the premise of `write_invariant`).
`MemInv.of_init`/`MemInv.of_init_on` discharge the initial memory
(`msgs = #[]` and `G` at the initial values).

**Per ISA (`Promising/InvLink{AArch64,X64}.lean`).** One `*_isim` lemma per
semantic primitive gives `exec_allInv_of_instrStepEnv`: an `instrStepEnv`
step in `inv S G` makes the machine's tree `AllInv G`. A thread is described
by `ThreadSpec S G` (code with `ValidLayout`, `endPc`, `post` only at
`endPc`, an invariant `inv` closed under `instrStepEnv` or ending in `post`);
`ThreadSpec.ofSafely` builds one from a `Safely` judgment and
`ThreadSpec.ofTripleEnv`/`ofTripleEnv_holds` from a `TripleEnv` with no
exceptional exit, started at the text's start. `ThreadSpec.Holds sp st`:
the thread runs `sp.e`, ends at `sp.endPc`, has no declarations, and its
machine state satisfies `sp.inv`.

- **Link A** (`inv_reachable`, `inv_writesPreserve`): given `MemInv G` at
  `c0` and `(sp tid).Holds` for every thread of `c0` (each thread its own
  program, any number of threads), every configuration `Reachable` from
  `c0` on the full Promising machine has `MemInv G`: every initial value and
  every message, fulfilled or promised, satisfies `G`; hence every value any
  thread can read of a location satisfies `G`.
- **Link B** (`inv_reachable`, second conjunct; `inv_reachable_post`): in
  every reachable configuration every thread still satisfies its
  `ThreadSpec`, i.e. its machine state satisfies the invariant of its
  single-thread proof (for `ofSafely`, `Safely … post`); a thread at its
  `endPc` satisfies `post` given `hstuck` (no `instrStepEnv` step at
  `endPc`, e.g. `not_instrStepEnv_of_end_labels`). That is all Link B
  covers: a *safety* statement about states the machine reaches. It does not
  say the thread reaches `endPc`, nor that it does not fault (see below).

**x64 side conditions.** Two premises appear only on x64.
`Le16 S` (every location ≤ 16 bytes; decidable, `by decide`) is the first
argument of `threadSpec_stepPreserves`/`inv_reachable`/`inv_writesPreserve`/
`inv_reachable_post`: the x64 machine tags atomic accesses with a 16-byte
line check. `Split S st.st.1.dmem` (no byte of a shared location mapped in
the private memory) is the 4th conjunct of x64 `Holds` and an extra last
argument of `ofTripleEnv_holds`: x64 vector/piecewise accesses read mapped
private bytes first, so the shared/private split must be fixed for the run
to be the one the env proof described; it is preserved by every step
(`Split.storeInt`, `piece_none`, `loadInt_none`) and discharged by
`Split.empty` or `Split.of_get` (finitely many lookups).

**Examples** (`{AArch64,X64}/Examples/InvEnv.lean`), each on the full
machine with any number of threads:
(a) ring index: a `cas(al)`/`lock cmpxchg` advance of an index kept `< 8`
(`G`: index `< 8`), `ring_reachable`, `ring_reachable_post`;
(b) racy plain accesses: a flag kept in `{0, 1}` by threads toggling it with
a plain load/xor/store and threads storing `1` (`flag_reachable`);
(c) negative control: storing `2` makes the `vcgen` obligation false
(`flagG_two`), checked by `fail_if_success`;
plus, AArch64, the whole worker of
`Examples/LockFree/AArch64/spinlock_swp2.kl` (`swpWorker`): `cfgEnv_partial`
in `SharedEnv.counted (inv …)`, `swp_reachable`: lock and counter stay in
`G`, and a finished worker has `w2 = 0`.

**What the invariant environment does not prove.**
- Ownership and mutual exclusion: `inv` only constrains values, so the
  spinlock example cannot conclude that the counter ends at `2` or that the
  critical sections exclude each other; reads are constrained by `G`, not by
  coherence or views. That is Stage 2 (rely/guarantee with views or
  ownership).
- No-fault: the adapter's `fault` (for register/flags `undefined`, see
  "Termination", and line-crossing accesses) is permitted by `AllInv`
  (a faulted thread has no further steps), so Link B says nothing about
  whether a thread faults; only that if it runs, it is in its invariant.
- Progress/termination: Link B is safety; the termination results are
  one-thread in `lastWrite` and are not lifted to `inv`.

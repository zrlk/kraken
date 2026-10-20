# OPEN: stricter than herd (parked with LL/SC)

These tests are outside the regression run: `litmus_tests.py` does not
descend into subdirectories, and `gen.sh` does not copy them. Each has a
`.litmus.herd` oracle from herd7 `7.58+1` (rev `9574394`) with
`-variant mixed`. On all five, herd says **Sometimes** and Kraken says
**Never**.

| Test | Shape |
|---|---|
| `LB+data-stxr` | P0: `LDR X0,[x]; LDXR X6,[f]; STXR W8,X0,[f]`; P1: `LDR X2,[f]; DMB SY; STR #1,[x]`; `exists 0:X0=1 /\ 1:X2=1` |
| `LB+data-stxr-ok` | the same, with the `STXR` succeeding (`0:X8=0`) |
| `LB+data-stxp-arr` | `STXP X0,X0` on two array elements |
| `LB+data-stxp-i128` | `STXP X0,X0` on one `__int128` |
| `LB+data-stxpw-i64` | `STXP W0,W0` on one `uint64_t` |

In each test the store-exclusive writes the value of an earlier load, so the
data dependency is real.

## (a) Cause in herd

`herd/AArch64Sem.ml` at rev `9574394` reads a store-exclusive's data
register with `read_reg_ord_sz` (input port `Port.No`), not
`read_reg_data_sz` (`Port.Data`):

```ocaml
let stxr sz t rr rs rd ii =
  do_stxr
    (read_reg_ord_sz sz rs ii)                       (* l. 2205 *)
    (fun an ac ea resa v  -> write_mem_atomic sz an aexp ac ea v resa ii)
    sz t rr rd ii

let stxp sz t rr rs1 rs2 rd ii =
  ...
      (read_reg_ord_sz sz rs1 ii >>> fun v ->        (* l. 2215 *)
       write_mem_atomic sz an aexp ac ea v resa ii)
      >>||
        (add_size ea sz >>= fun a ->
         read_reg_ord_sz sz rs2 ii >>> fun v -> ...  (* l. 2219 *)
```

`aarch64deps.cat` l. 69 defines
`data = [Exp & R]; dtrm & po; [Rreg]; iico_data & ii_data; [Exp & W]`.
`ii_data` only relates register reads on a `Port.Data` input. So there is no
`data` edge from the load to the store-exclusive's write, and nothing else
puts the write in `ob` after the load: `dob`, `bob` and `aob` in
`aarch64.cat`, with no barrier and no release. The LB cycle is therefore not
forbidden.

## (b) History: a herd change from 2025

The change is herdtools7 commit `add229fa` (Luc Maranget, 2025-02-13,
"[herd] Rework input ports"). It replaced the boolean "data port" of
register reads with `Port.Addr`/`Port.Data`/`Port.No`. In `stxr` it turned
`read_reg_data sz rs ii` into `read_reg_ord_sz sz rs ii`. `stxp`, added in
`361487d0` (2022-05-03) with `read_reg_data`, was changed the same way. The
commit message says it adds tests for "the presence of data ports in AMO's
and in CAS", but none for store exclusives.

I built herd at `add229fa^` (`9a73ae47`) and at `add229fa` (scratch builds, `dune build`)
and ran them on the same tests:

| Test | herd `add229fa^` | herd `add229fa` | herd `7.58+1` (`9574394`) | Kraken |
|---|---|---|---|---|
| `LB+data-stxr` | Never | Sometimes | Sometimes | Never |
| `LB+data-stxr-ok` | Never | Sometimes | Sometimes | Never |
| `LB+data-stxp-arr` | Never | Sometimes | Sometimes | Never |
| `hand/LB+fdata-stxr` (false dependency) | Never | Sometimes | Sometimes | Sometimes |
| `hand/LB+data-stlxr` (release) | Never | Never | Never | Never |
| `hand/LB+data-cas` | Never | Never | Never | Never |
| `hand/LB+fdata-str` | Never | Never | Never | Never |

I also ran herd `add229fa^` over the regression corpora and compared its
verdicts with the cached current-herd oracles:

- `corpus/aarch64` (52 tests), `aarch64-noret` (465) and
  `generated/aarch64` (304): no difference.
- `aarch64-views` (77): one difference, `MP+dmb.st+wb` (old Sometimes,
  current Never). It concerns a post-indexed `STR`'s write-back and is
  unrelated to store exclusives; Kraken follows current herd there.
- `aarch64-pairs` (76): only the three `LB+fdata-stx*` tests differ (old
  Never, current Sometimes). `STXP-arr-2thr` gives no verdict in the old
  herd.

So the port rework changes no other verdict in the corpora that Kraken
checks.

Before February 2025, herd had a data dependency into store exclusives,
like every other store. That model is the one Pulte et al.'s Promising-ARM
equivalence (PLDI'19) is stated against, and Kraken agreed with it on all of
these tests until `e511175` dropped the dependency to match current herd.
The current herd behaviour looks like a side effect of the port rework
rather than a deliberate architectural change; we have not confirmed this
with the herd maintainers. The latest herdtools7 master (`4101bc61`,
2026-10-15) still reads with `read_reg_ord_sz`.

## (c) What Promising would need to allow it

Kraken's memory is append-only: a write's timestamp is its position. A
thread may promise a write only if running it alone certifies the write,
with the same value, and with a constraining view `≤ |M|`.

- P0 cannot promise `f := 1` first: alone, it reads `x = 0` and writes 0.
- So P1 must promise `x := 1` first. It can, since alone it reads
  `f = init`, and after `DMB SY` its view is 0. The promise gets timestamp `t`.
- P0 then reads `x = 1` at `t`. Its `STXR` (no dependency view since
  `e511175`) appends `f := 1` at a timestamp `t' > t`.
- P1 reads `f` at `t'`, so `DMB SY` raises its view to `t'`. Fulfilling the
  `x` promise at `t < t'` then fails.

Allowing the outcome needs one of:

1. **Writes at a timestamp before existing messages.** The original
   Promising semantics (Kang et al.) uses dense timestamps and inserts a
   write anywhere above its views and the location's coherence. P0's
   `f := 1` could then go below `t`. Promising-ARM drops insertion because,
   by its equivalence proof, any such write could have been promised
   earlier. That argument needs the write's value to be certifiable, which
   the missing `data` edge breaks. Restoring insertion changes `Memory`,
   `Thread.fulfil`, certification (`certify`/`certifiedPromises`) and every
   proof that indexes messages by position (`PromiseSafe`, `Conservative`,
   `PFComplete*`, the `SeqLink*`/`EnvWP*` links).
2. **Certifying against a speculated value.** Certify P0's promise
   `f := 1` assuming its `LDR x` returns 1, without requiring that value to
   be in memory. This is value speculation (out-of-thin-air in general). It
   would have to be limited to values that flow only into store-exclusive
   data, or LB+data with a plain `STR` (herd: Never; also
   `aarch64-views/LB+datapair*`) becomes allowed.

Option 1 is the minimal semantic change. LB+data with a plain `STR` keeps
its `data` edge and so its dependency view, which still forbids it. But
insertion also lets non-dependent writes go below earlier messages, so the
corpora would need rerunning; I expect no catalogue change, by Promising-ARM's
completeness argument. Both options are machine changes and are out of scope
here.

# Block-data generators

`genblocks_a64.py` and `genblocks_x64.py` read scc's assembly listing of a
program and write one `block_spec` line per block of covered instructions,
with its function's stack region and the block's static offsets at entry.
`Spike/Lib/A64Hello.lean` and `Spike/Lib/X64Hello.lean` hold their output
for `Scc/Test/hello.w` at an earlier revision, pasted below each file's header.

The block lemmas (`Spike/Lib/A64Flow.lean`, `Spike/Lib/X64Block.lean`) and
the composition (`Spike/Lib/A64Cfg.lean`, `Spike/Lib/X64Cfg.lean`) do not
depend on scc's layout. After a layout change, rerun the generators on the
new listing and replace the data.

Static offsets: at a label they are the meet of all incoming edges
(fall-through and branches), computed to a fixpoint. A whole-function proof
(`Spike/Lib/A64Print.lean`) relies on this, because a node's offsets have to
hold on every edge into it.

Coverage statistics go to `OUT.lean.json`. `covered` counts the instructions
in blocks. `nodes` counts the instructions outside blocks that a
single-instruction node lemma covers at known offsets: `flag_nd`
(`Spike/Lib/X64Flags.lean`), `si_nd` (`Spike/Lib/A64Nodes.lean`,
`Spike/Lib/X64Nodes.lean`), and the system-call nodes `svc_nd` and
`syscall_nd` (same files, through `Out.sys`). A system call is counted by
the number the straight-line code before it sets: `sys` (no kernel event:
`rt_sigaction`, `exit_group`, `futex`, `exit`), `sys, control only`
(`write`, `clone`: the node matches the thread's control, not the kernel
step's events) or `sys, number after a label` (the abort exits, where the
number is set before the label and must come from the node's invariant).
x64's `arch_prctl` is not counted (`syscall_nd` excludes it). x64's thread-pointer loads
`movq %fs:k, %r` are counted as `thread pointer` (`fsld_nd`,
`Spike/Lib/X64Nodes.lean`, through `Out.rtLoad`). x64's `ud2` (after a call
that does not return, or after `exit_group`) is counted as `dead`
(`dead_nd`, `Spike/Lib/X64Dead.lean`: a node whose invariant no run
satisfies).

Stack switches (a register operation writing `sp`/`%rsp` from a register
of unknown offset, and x64's `andq $k, %rsp`) are nodes of their own
(`sw_nd`, `swand_nd`: `Spike/Lib/A64Switch.lean`, `Spike/Lib/X64Switch.lean`),
counted as `switch` in `nodes`. After a switch the offsets restart in a new
region based at the new stack pointer (offset 0, no register offsets), with
its own `[lo, hi)`: the static offsets carry an epoch, the number of
switches on the way, and edges of different epochs meet to unknown.

Python 3, standard library only.

## Rows outside the blocks

`genrows_a64.py` completes `scc --code`'s block tables for a per-node
instance (`correctA64`): every `.text` instruction no block covers becomes a
row (`Spike/Lib/Rows.lean`) with its function, place, kind (`label`,
`system`, `site`, `switch`, `svc`, `load`, `store`, `rmw`) and runtime flag,
emitted both as data and as one-instruction blocks checked by `blocksIn`
(so every row has `CodeAt`), with the source nodes from `scc --blocks`'
placement data. It fails on an instruction shape it does not classify, and
checks that blocks and rows cover the program once.

The H0 milestone's data (`Spike/Gen/ret0.w`): `Spike/Lib/A64Ret0Code.lean`
(`scc --code`, verbatim), `Spike/Lib/A64Ret0Place.lean` (`scc --blocks`'
placement data, its namespace renamed `SccPlace.ret0`) and
`Spike/Lib/A64Ret0Rows.lean` (`genrows_a64.py`), all written by

    Spike/Gen/regen_a64.sh ret0 A64Ret0

After a runtime, lowering or layout change, rerun it. The staleness check

    Spike/Gen/regen_a64.sh ret0 A64Ret0 --check

regenerates under `.lake/spike-gen/` and fails if a committed file differs;
run it before committing anything that changes scc's output.

On x64, `genrows_x64.py` does the same from `scc --code`'s block tables and
its instruction sizes (`<name>Asm.sizes`), with the kinds `flags` (`flag_nd`)
and `dead` (`ud2`, `dead_nd`) besides; `scc` writes no x64 placement data,
so there are no source nodes. The H0 x64 data, `Spike/Lib/X64Ret0Code.lean`
and `Spike/Lib/X64Ret0Rows.lean`, from the same `ret0.w`:

    Spike/Gen/regen_x64.sh ret0 X64Ret0            # regenerate
    Spike/Gen/regen_x64.sh ret0 X64Ret0 --check    # staleness check

Both scripts write the certificate `Spike/Test/Cert/MODCert.lean` too. A
program that does not satisfy PlaceOK (ask `Scc/Test/placediag.sh`) is
regenerated with `CERT_FAILS=N`, so that scc writes the negative certificate
(`--cert-fails N`). On both ISAs `hello1.w`'s placement holds (A11 checks
its setup tail), so its certificates are the positive ones; `hello1.w` is
outside `Accepted0`, so they make no correctness claim:

    Spike/Gen/regen_a64.sh hello1 A64Hello1
    Spike/Gen/regen_x64.sh hello1 X64Hello1

`Spike/Gen/drift.sh` runs all eight staleness checks (`ret0`, `hello1` and
`call1` on both ISAs, `frame0` on x86-64 and `chain5` on AArch64) and exits
0 when every generated file matches scc's output, 1 otherwise.

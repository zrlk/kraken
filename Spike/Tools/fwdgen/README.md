# fwdgen: regenerating the closed hello run's chunks

The checked-in `HelloRootL0XClosed*` modules were generated at a fixed x64 hello layout; regenerate
them when that layout changes.

`Spike/Test/HelloRootL0XClosedC1.lean` … `C8.lean` are generated. Lake does not run anything in this
directory; the `.lean.txt` files are kept as text so that lake does not build them.

The generator only picks the lemma for each step and its witnesses (addresses, values, list names). Every
step is checked by Lean (`decide`/`rfl` on the concrete state), so a wrong witness makes the build fail
instead of yielding a false theorem.

## Pipeline (work directory `$FWDGEN_DIR`, default `/tmp/fwdgen`)

```
cp Spike/Tools/fwdgen/sim.lean.txt $FWDGEN_DIR/sim.lean
cp Spike/Tools/fwdgen/tab.lean.txt $FWDGEN_DIR/tab.lean
LEAN_NUM_THREADS=1 lake env lean $FWDGEN_DIR/sim.lean > $FWDGEN_DIR/sim.out   # reference run, 300 steps
LEAN_NUM_THREADS=1 lake env lean $FWDGEN_DIR/tab.lean > $FWDGEN_DIR/tab2.out  # cell addresses and labels
python3 Spike/Tools/fwdgen/mkinsns.py $FWDGEN_DIR/sim.out > $FWDGEN_DIR/insns.txt
python3 Spike/Tools/fwdgen/genfwd.py           # writes $FWDGEN_DIR/gen.json
for k in 1 2 3 4 5 6 7 8; do python3 Spike/Tools/fwdgen/emit.py $k; done   # writes Spike/Test/…C$k.lean
```

`sim.lean` runs thread 0 alone from the loaded state at `Λe`. At each choice it takes leaf 0, a load reads
the last write, and a system call returns 0 (`arch_prctl` also sets `%fs`). The take copies the taken range.

## What is derived and what is fixed

- Derived from the run and the tables:
  - the last step (the first `lock xadd` on `scc_rt_heap_use`, the counter add);
  - the take's step and range;
  - the steps of the two system calls;
  - every pc, cell index, register file, flag set, stack slot and shared write;
  - the chunk boundaries (36 steps each).
- Fixed, and must be edited by hand if the layout changes:
  - in `HelloRootL0XClosedBase.lean`: the register files at the kernel steps (`Rsig`, `Rsig'`, `Rfs`, `Rfs'`,
    `Rtk`), the cells 18/32/504, the take range `rTk`, the take/release site pcs 4200314/4200354 (`take_at`,
    `rel_at`), and the bound 72022848 in `sg_take`;
  - in `HelloRootL0XClosedStep.lean`: the site pcs in the `hs` side conditions;
  - in `tab.lean.txt`: the label list (the labels this path uses) and the address window of the cell dump;
  - in `genfwd.py`: the entry stack bounds (`Entry.linux`).
  The generator asserts that the special steps' register files match the Base names. The Lean build checks
  everything else.

## The closing module

`Spike/Test/HelloRootL0XClosed.lean` is hand-written, not generated. On regeneration, update its run-specific
numerals from the new reference run: `s283` (the last chunk's end state: registers, flags, private memory, pc),
the counter-add cell index and pc in `exec283`, the counter word (`4225760`, also in `exec283`, `wrAt283` and
`ctrLoc_eq`), the return-address slot (`%rbp + 8 = 72039096`) and its value (`.Lwc_rodata.x0 = 4203222`) in
`ra283`, the `%rbp` value in `reach283`'s level-1 refutation, `.Lwc_main.x0`'s address in `lab__Lwc_main_x0` (the
label's name can change with the layout too), and the final memory and kernel state names (`M233`, `X1`) and the
chunk list in `run283`.

/-
**Part 5: the history layer of the two-thread
Treiber stack**, pure. Since every name
of this file is an alias (`hoist_alias`, same statements) of the Treiber node proof's
`EnvG/Treiber2Hist.lean`, whose import is now ISA-neutral (nothing: the layer
depends neither on the ISA nor on the node layout).

At the final clean erasure the messages of `top` are exactly the initial one
(`0`), the two pushes `A.p`, `B.p` and the pops `A.q`, `B.q` of the threads
that popped. `hist_ok` (the **law**): both threads popped, and they popped
the two distinct nodes. On x64 the `cbz` branch of the AArch64 program is a
spin (`je pop`), so `SideOK.cbz` is never used with a true hypothesis there;
the law is kept as it is.

Contents (aliases): `Side`, `T`, `PopOK`, `SideOK`, `HistOK` (+ `swap`),
`hist_core`, `hist_ok`, `hist_time`, and the structures' generated
constants.
-/
import Kraken.Promising.SLR.EnvG.X64Treiber2Ghost
import Kraken.Promising.SLR.EnvG.Treiber2Hist
import Kraken.Promising.SLR.EnvG.Alias

-- The history layer of `EnvG/Treiber2Hist.lean` under the `Treiber2X` names
-- (the x64 MS queue proof item 1; the structures become reducible aliases).
hoist_alias [
  Kraken.Promising.SLR.EnvG.Treiber2.Side ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side,
  Kraken.Promising.SLR.EnvG.Treiber2.Side._sizeOf_inst ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side._sizeOf_inst,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.n ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.n,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.anz ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.anz,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.bnz ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.bnz,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.p ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.p,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.popped ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.popped,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.q ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.q,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.mk ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.mk,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.casesOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.casesOn,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.nne ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.nne,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.pne ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.pne,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.qa ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.qa,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.qb ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.qb,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.qne ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.qne,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.rec ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.rec,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.recOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.recOn,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.sa ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.sa,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.sb ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.sb,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.swap ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.swap,
  Kraken.Promising.SLR.EnvG.Treiber2.HistOK.val0 ↦ Kraken.Promising.X64.EnvG.Treiber2X.HistOK.val0,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.tr ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.tr,
  Kraken.Promising.SLR.EnvG.Treiber2.T ↦ Kraken.Promising.X64.EnvG.Treiber2X.T,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.adj ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.adj,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.tr0 ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.tr0,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.v ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.v,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.x4 ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.x4,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.y ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.y,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.mk ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.mk,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.casesOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.casesOn,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.le0 ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.le0,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.le1 ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.le1,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.lt ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.lt,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.nodeA ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.nodeA,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.nodeB ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.nodeB,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.nz ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.nz,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.p_lt_q ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.p_lt_q,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.rec ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.rec,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.recOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.recOn,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.swap ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.swap,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.t0 ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.t0,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.t1 ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.t1,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.v0 ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.v0,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.v1 ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.v1,
  Kraken.Promising.SLR.EnvG.Treiber2.PopOK.vq ↦ Kraken.Promising.X64.EnvG.Treiber2X.PopOK.vq,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.mk ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.mk,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.casesOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.casesOn,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.ctorIdx ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.ctorIdx,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.mk.inj ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.mk.inj,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.mk.injEq ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.mk.injEq,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.mk.noConfusion ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.mk.noConfusion,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.mk.sizeOf_spec ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.mk.sizeOf_spec,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.noConfusionType ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.noConfusionType,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.noConfusion ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.noConfusion,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.rec ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.rec,
  Kraken.Promising.SLR.EnvG.Treiber2.Side.recOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.Side.recOn,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.mk ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.mk,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.casesOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.casesOn,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.cbz ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.cbz,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.pop ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.pop,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.ppos ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.ppos,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.push ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.push,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.pval ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.pval,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.rec ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.rec,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.recOn ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.recOn,
  Kraken.Promising.SLR.EnvG.Treiber2.SideOK.swap ↦ Kraken.Promising.X64.EnvG.Treiber2X.SideOK.swap,
  Kraken.Promising.SLR.EnvG.Treiber2.T.swap ↦ Kraken.Promising.X64.EnvG.Treiber2X.T.swap,
  Kraken.Promising.SLR.EnvG.Treiber2.hist_core ↦ Kraken.Promising.X64.EnvG.Treiber2X.hist_core,
  Kraken.Promising.SLR.EnvG.Treiber2.hist_ok ↦ Kraken.Promising.X64.EnvG.Treiber2X.hist_ok,
  Kraken.Promising.SLR.EnvG.Treiber2.hist_time ↦ Kraken.Promising.X64.EnvG.Treiber2X.hist_time]

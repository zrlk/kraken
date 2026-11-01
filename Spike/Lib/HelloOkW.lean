/-
**hello.w's ghost records' facts** (check-in 0): wake's
`okW` and the buffer's placement `BufPl` (`HelloInst`) at the record's
placement, with the buffer's label `lB` and base `b0` as parameters (no
`Gh` field).

- `okH Λ lbl' cSf lB b0 g`: `okW Λ lbl' cSf g ∧ BufPl g.lbl g.lsize g.cS lB b0`.
- `okH_okW`, `okH_buf`: the projections; `okH_sub`: a record satisfying
  `okH` as one satisfying `okW` (wake's lemmas at `w : {g // okW …}` apply).
- `b0_eq`: `b0` is the worker side's placement of `lB` (`lbl' lB = some b0`,
  from `okW_lbl` and `BufPl`): `b0` is not free, it is fixed by `lbl'`.
- `okH_frzS`, `okH_ne_cS`, `okH_frz`: `HelloInst.frzS_buf` / `buf_ne_cS` /
  `frz_buf` at the record's location data `wakeLocs`-shaped `W` (any `W`
  whose placement and flag are the record's).
- **The buffer's label**: `lBH := freshLabel 0 2 0 1` (`= 2`). rodata runs
  on thread 0 of `setupStartT 2` (`lbase = 0`, stripe `n = 2`, one
  allocation made, the `ThreadId` box: `nalloc = 1`), and its `newBuf` is
  the thread's first allocation after the box, at `freshLabel g.lbase g.n
  g.i s.nalloc` (`TermRun`'s `newBuf` row). `setupStartT_lbase`,
  `setupStartT_n`, `setupStartT_nalloc`, `setupStartT_tid` pin the start's
  fields; `lBH_eq`: `lBH = 2`; `lBH_ne_tid`: it is not main's `ThreadId`
  label `mainTidLbl 2`. That rodata's allocation is the first one after the
  start (the run from `setupStartT 2` to `rdCN`) is the source run's fact
  and is not proved here.
-/
import Spike.Lib.WakeOkW
import Spike.Lib.A64HelloInst

namespace Spike.Lib.HelloOkW

open Kraken.Promising Scc.Sem
open Spike.Lib Spike.Lib.WakeInst Spike.Lib.WakeOkW Spike.Lib.WakeP
open Spike.Lib.HelloInst (BufPl helloP frzS_buf buf_ne_cS frz_buf)

/-- **hello.w's ghost records' facts**: wake's (`okW`), and rodata's buffer
placed at the spawn (`BufPl`: label `lB` at `b0`, two words, off `c`). -/
def okH (Λ : Scc.Sem.Layout) (lbl' : WeakMem.AllocLabel → Option Nat) (cSf : WeakMem.Address)
    (lB : WeakMem.AllocLabel) (b0 : Nat) (g : Gh) : Prop :=
  okW Λ lbl' cSf g ∧ BufPl g.lbl g.lsize g.cS lB b0

section Proj

variable {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
  {lB : WeakMem.AllocLabel} {b0 : Nat} (w : {g : Gh // okH Λ lbl' cSf lB b0 g})

theorem okH_okW : okW Λ lbl' cSf w.1 := w.2.1
theorem okH_buf : BufPl w.1.lbl w.1.lsize w.1.cS lB b0 := w.2.2

/-- **The record as wake's** (`okW`'s lemmas apply). -/
def okH_sub : {g : Gh // okW Λ lbl' cSf g} := ⟨w.1, w.2.1⟩

@[simp] theorem okH_sub_val : (okH_sub w).1 = w.1 := rfl

include w in
/-- **`b0` is the worker side's placement of the buffer's label**: `okW`
fixes the record's placement to `lbl'` (`okW_lbl`), `BufPl` places `lB` at
`b0`. -/
theorem b0_eq : lbl' lB = some b0 := by
  rw [← okW_lbl (okH_sub w)]; exact (okH_buf w).1

include w in
/-- The buffer's label is not the flag's (`cSf`, `okW_cS`). -/
theorem lB_ne_cSf : lB ≠ cSf.label := by
  rw [← okW_cS (okH_sub w)]; exact (okH_buf w).2.2

/-- The buffer holds at least two words at the worker side's sizes. -/
theorem two_le_lsize : 2 ≤ w.1.lsize lB := (okH_buf w).2.1

end Proj

/-! ## The buffer's words are frozen at the record's location data -/

section Frz

variable {I : ISA} {K : Kernel.Abi I} {μ : Marks} {W : WakeLocs}
  {Λ : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
  {lB : WeakMem.AllocLabel} {b0 : Nat} (w : {g : Gh // okH Λ lbl' cSf lB b0 g})
  (hl : W.lbl = w.1.lbl) (hs : W.lsize = w.1.lsize) (hc : W.cS = w.1.cS)

include hl hs hc in
/-- `BufPl` at location data whose placement and flag are the record's. -/
theorem bufPl_W : BufPl W.lbl W.lsize W.cS lB b0 := by
  rw [hl, hs, hc]; exact okH_buf w

include hl hs hc in
/-- **The buffer's source words are frozen** (`frzS_buf`). -/
theorem okH_frzS {i : Nat} (hi : i < 2) : (helloP K μ W).frzS ⟨lB, i⟩ :=
  frzS_buf (bufPl_W w hl hs hc) hi

include hl hs hc in
/-- **The buffer's words are not `c`** (`buf_ne_cS`). -/
theorem okH_ne_cS (i : Nat) : (⟨lB, i⟩ : WeakMem.Address) ≠ W.cS :=
  buf_ne_cS (bufPl_W w hl hs hc) i

include hl hs hc in
/-- **The buffer's target words are frozen** (`frz_buf`), `cT`'s shape from
`okW_cT` at `W.cT = w.1.cT`. -/
theorem okH_frz {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hT : W.cT = w.1.cT) (h : MemRelP Λ W.lbl W.lsize ts tm sm tp tq sp) (hwf : Λ.WF)
    {i : Nat} (hi : i < 2) : (helloP K μ W).frz (wordLoc (b0 + 8 * i)) := by
  refine frz_buf h hwf (bufPl_W w hl hs hc) ?_ hi
  rw [hT, hl, hs, hc]; exact okW_cT (okH_sub w)

end Frz

/-! ## The buffer's label at the instance -/

/-- **rodata's buffer label**: thread 0's allocation `1` (the first after
the `ThreadId` box) in stripe `2`, base `0`. -/
def lBH : WeakMem.AllocLabel := TermRun.freshLabel 0 2 0 1

theorem lBH_eq : lBH = 2 := rfl

/-- `setupStartT 2` allocates no label before the run. -/
theorem setupStartT_lbase : (SrcSem.setupStartT 2).lbase = 0 := rfl

/-- `setupStartT 2`'s stripe is `2`. -/
theorem setupStartT_n : (SrcSem.setupStartT 2).n = 2 := rfl

/-- `setupStartT 2`'s one thread has made one allocation (the box). -/
theorem setupStartT_nalloc : ∃ th, (SrcSem.setupStartT 2).ths = #[th] ∧ th.nalloc = 1 :=
  ⟨_, rfl, rfl⟩

/-- **The next allocation of `setupStartT 2`'s thread is `lBH`**: the
`newBuf` row's label `freshLabel g.lbase g.n g.i s.nalloc` at `gOf … 0` and
the start thread's `nalloc`. -/
theorem setupStartT_fresh (p : CoreTerm.Prog) (k : Promises.Knobs) (arch : WeakMem.Arch) :
    ∃ th, (SrcSem.setupStartT 2).ths = #[th] ∧
      let g := TermRun.gOf p k arch (SrcSem.setupStartT 2) 0
      TermRun.freshLabel g.lbase g.n g.i th.nalloc = lBH :=
  ⟨_, rfl, rfl⟩

/-- `lBH` is not main's `ThreadId` label. -/
theorem lBH_ne_tid : lBH ≠ SrcSem.mainTidLbl 2 := by decide

end Spike.Lib.HelloOkW

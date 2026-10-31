/-
**The box's landing as `h1` reads it** (wake.w, x86-64): the statement of
the landing `Box l b n` that `X64WakeH1Inv.h1Stmt_of` takes, the pairs
`h0`'s segment (`wc_main` from its entry to the box's store,
`X64WakeJ0.wake_wc_entry_segJm`) hands to `h1`'s at the fresh label `l`,
the cell `b` and the size `n`.

- `Box L ms0 F0 l b n s c`: some region `R`, frame condition `F` (inside
  `F0`), entry invariant `J0` and thread pointer `t` (main's TCB, `tcb0`)
  with `s, c` at `bX ms0 lab J0 l b` (past the box's store), the region's
  facts (`wc_main`'s frame on a pool stack, `BandTi`'s body), `n = 1`, the
  source at the rest of main (`c = publish o; p = pair c me; spawnTerm`)
  with `o` bound to `l`'s locative and `me` to main's `ThreadId`, main's
  stack owned and the child's stack unmapped (`KeepUn.U`, kept by every
  step until its take; `Pz` follows by `pz_of_unowned`).
- `box_at`, `box_n`, `box_env`: the landing's projections.
- `box_rsp`: the `%rsp` conjunct at `h0`'s landing (`wJ0 (wNC lab Jm) σC`
  on `(wR R0 D).fp (-8)`), from `wF`'s `Abs` of `σC`.

x86-64 twin of `Spike/Lib/A64WakeBox.lean` (same names, namespace
`Spike.Lib.X64.Flow.WakeWc`). This module is statement only, as the
original: the proof that `h0`'s segment lands in `Box` is open.

**Where this differs from AArch64** (forced by the x86-64 frame shape,
`X64WakeFrame`):
- `R` is the landing's region, `wc_main`'s region at the call
  re-based at the saved `%rbp` (`(WakeM.wR R0 D).fp (-8)`,
  `X64WakeWcSp0.bXR_rebase`), where `X64WakeWcHat.wake_wc_mid_hatW` runs:
  `R.lo ≤ -320` (A64 `-336`) and `16 ≤ R.hi` (A64 `0 ≤`: the return
  address and the saved `%rbp` sit above the base);
- no `hfit`/`hupF` conjuncts: on x86-64 the region already reaches the
  caller's two words (`X64WakeWcMain`'s doc, `fp8_ok`), A64's `upAS` has
  no counterpart;
- the band (`X64WakeWcSp4W.BandTi`) is `R.addr k` for `-80 ≤ k ≤ -72`
  (A64 `-128 ≤ k ≤ -80`);
- `J0`'s `ThreadId` word is in `%rdi` (A64 `x0`);
- the region is `64` below the top of stack 0 (`R.base + 64 = stacksA +
  16384`: `scc_rt_main`'s region at `top - 8`, `wc_main`'s `48` lower, the
  landing's `8` lower again; A64 `48`), and below the child's stack is
  `R.hi ≤ 64` (A64 `48`);
- `%rsp` at `wc_main`'s entry (`J0`) is `R.base + 8` (no A64 counterpart:
  it pins `scc_rt_main`'s saved `%rbp` for `MainPieces.hfp`, through
  `CloneP` and `ClonePost`);
- the thread pointer is `fsBase` (`X64.KeepTP.TP`).
-/
import Spike.Lib.X64WakeWcSp0
import Spike.Lib.X64WakeMain
import Spike.Lib.X64KeepUn
import Spike.Lib.X64OwnedPz
import Spike.Lib.X64WakeLoadT
import Spike.Lib.X64WakeBoxDefs
import Spike.Lib.X64WakeSrcDefs
import Spike.Lib.Rt.X64RtTi2
import Spike.Lib.Rt.X64RtPreChild
import Spike.Lib.Rt.X64Layout

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64WakeBoxDefs (boxTerm)

/-- **The box's landing** at the fresh label `l`, the cell `b` and the size
`n` (`h1Stmt_of`'s `Box`), in `L`'s executable, `h0`'s memory side `ms0` and
the start's frame condition `F0`: for some region `R`, frame condition `F`,
`wc_main` entry invariant `J0` and thread pointer `t`,
- the region: `R.OK`, `base` 16-aligned, `F` stable, `R.lo ≤ -320`
  (`wake_wc_mid_hatW`'s `hlo`), `16 ≤ R.hi` (its `hhi`);
- `wc_main`'s frame on a pool stack (`WcSp4W.BandTi L R`'s body): `R.addr k`
  for `-80 ≤ k ≤ -72` in `(pool.lo, pool.lo + pool.size]`;
- `F` inside `F0` (the start's facts kept: the limit word unmapped, the
  heap and counter off);
- the call's shape: `J0` is `WakeM.wJ0` of `scc_rt_main`'s call node `wNC`
  over some `J` and `σC`, `%rdi` at `J0` is main's `ThreadId` word
  (`WakeLoadT.tcb0`), and the region is `64` below the top of stack 0
  (`stacksA + 16384`), and `%rsp` at `J0` is `8` above the base (`R` is
  `wc_main`'s region at the call re-based at the saved `%rbp`: the call's
  `%rsp` holds the return address, the push of `%rbp` is `8` below);
- the pair at `bX ms0 lab J0 l b` (past the box's store) with the thread
  pointer `t`, main's TCB (`WakeLoadT.tcb0`: `pinA + 8`);
- one object (`n = 1`);
- the source past the `new`: the term `boxTerm`, no hold, `o` bound to
  `l`'s owned locative at `.ptr .own .int`, `me` to main's `ThreadId`
  locative;
- main's stack owned (`Ti2.r0Of`), the child's stack unmapped (`KeepUn.U`
  at `PreChild.r1Of`);
- `F` kept by the child stack's take (`hFt`) and reading memory only
  (`hFd`), the region below the child's stack (`R.hi ≤ 64`), main's stack
  mapped off the region under `F` (`StackOff` at `Ti2.r0Of`), and the
  region's bounds word-aligned (`R.lo % 8 = 0`, `R.hi % 8 = 0`).

**Provisional**, as the AArch64 original: the ownership conjunct; `PlacedSE`
at `L0T` is not included. -/
def Box (L : RuntimeLayout) (ms0 : MemSide isa) (F0 : MachineData → Prop)
    (l : WeakMem.AllocLabel) (b n : Nat) (s : State) (c : Ctl) : Prop :=
  ∃ (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64),
    (R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -320 ∧ 16 ≤ R.hi) ∧
    (∀ k, -80 ≤ k → k ≤ -72 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
      (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) ∧
    (∀ m, F m → F0 m) ∧
    ((∃ (J : AS → Ctl → Prop) (σC : AS),
        J0 = WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) ∧
      (∀ σe c, J0 σe c → σe.regs.rdi.toNat = Spike.Lib.X64WakeLoadT.tcb0 L.Λ) ∧
      R.base.toNat + 64 = L.stacksA.toNat + 16384 ∧
      ∀ σe c, J0 σe c → σe.regs.get64 .rsp = R.base + 8#64) ∧
    (At L.exe L.endPc R F (bX ms0 (_root_.Executable.labels L.exe).label J0 l b) s c ∧
      Spike.Lib.X64.KeepTP.TP t s ∧ t.toNat = L.pinA.toNat + 8) ∧
    n = 1 ∧
    (c.term = boxTerm ∧ c.hold = none ∧
      TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])) ∧
    (Spike.Lib.X64Consumer.Owned L.Λ (Spike.Lib.X64.Rt.Ti2.r0Of (_root_.Executable.labels L.exe).label) s ∧
      Spike.Lib.X64.KeepUn.U (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) s) ∧
    ((∀ m pm, F m → F (Ret0.takeMem pm (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) m)) ∧
      (∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') ∧ R.hi ≤ 64 ∧
      (∀ m, F m → Ret0.StackOff (Spike.Lib.X64.Rt.Ti2.r0Of (_root_.Executable.labels L.exe).label) R m) ∧
      R.lo % 8 = 0 ∧ R.hi % 8 = 0)

variable {L : RuntimeLayout} {ms0 : MemSide isa} {F0 : MachineData → Prop}
  {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl}

/-- The landing is past the box's store with main's thread pointer. -/
theorem box_at (h : Box L ms0 F0 l b n s c) :
    ∃ (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64),
      At L.exe L.endPc R F (bX ms0 (_root_.Executable.labels L.exe).label J0 l b) s c ∧
        Spike.Lib.X64.KeepTP.TP t s :=
  let ⟨R, F, J0, t, _, _, _, _, ⟨ha, htp, _⟩, _⟩ := h
  ⟨R, F, J0, t, ha, htp⟩

/-- The landing's object is one cell's (`n = 1`). -/
theorem box_n (h : Box L ms0 F0 l b n s c) : n = 1 :=
  let ⟨_, _, _, _, _, _, _, _, _, hn, _⟩ := h
  hn

/-- The landing binds `o` to `l`'s locative. -/
theorem box_env (h : Box L ms0 F0 l b n s c) :
    TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :=
  let ⟨_, _, _, _, _, _, _, _, _, _, ⟨_, _, ho, _⟩, _⟩ := h
  ho

/-- **`Box`'s `%rsp` conjunct at `h0`'s landing** (its discharge where `Box`
is produced, the twin of A64 `WakeHxa.box_landing`): at `wc_main`'s entry
`wJ0 (wNC lab Jm) σC` with `σC` the caller's state on `R0` at `wNC`'s
offsets (`WakeM.wF`'s `Abs`), every entry state's `%rsp` is `8` above the
landing region `(wR R0 D).fp (-8)`'s base. -/
theorem box_rsp {lab : Label → Int64} {Jm : AS → Ctl → Prop} {σC : AS} {R0 : Region} {D : Int}
    {m0 : MachineData} (hA : Abs R0 ⟨-48, []⟩ m0 σC) :
    ∀ σe c, WakeM.wJ0 (WakeM.wNC lab Jm).J σC σe c →
      σe.regs.get64 .rsp = ((WakeM.wR R0 D).fp (-8)).base + 8#64 := by
  rintro σe c ⟨rfl, -⟩
  show σC.regs.get64 .rsp = _
  rw [hA.so .rsp (-48) (by simp [SO.get])]
  simp only [Region.fp, Region.callee, Region.addr, BitVec.add_assoc]
  rw [show BitVec.ofInt 64 (-8) + 8#64 = 0#64 by decide, BitVec.add_zero]

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.box_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.box_env

/-- info: 'Spike.Lib.X64.Flow.WakeWc.box_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.box_at

/-- info: 'Spike.Lib.X64.Flow.WakeWc.box_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.box_n

/-- info: 'Spike.Lib.X64.Flow.WakeWc.box_rsp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.box_rsp

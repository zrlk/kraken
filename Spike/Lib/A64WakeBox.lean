/-
**The box's landing as `h1` reads it** (wake.w, AArch64): the
statement of `A64WakeWcInv.H1Stmt`'s `Box l b n`, the pairs `h0`'s segment
(`wc_main` from its entry to the box's store, `wake_wc_entry_segJm`) hands to
`h1`'s at the fresh label `l`, the cell `b` and the size `n`.

- `Box L ms0 F0 l b n s c`: some region `R`, frame condition `F` (inside
  `F0`), entry invariant `J0` and thread pointer `t` (main's TCB, `tcb0`)
  with `s, c` at `bX ms0 lab J0 l b` (past the box's store), the region's
  facts (`wc_main`'s frame on a pool stack, `BandTi`'s body), `n = 1`, the
  source at the rest of main (`c = publish o; p = pair c me; spawnTerm`)
  with `o` bound to `l`'s locative and `me` to main's `ThreadId`, main's
  stack owned and the child's stack unmapped (`KeepUn.U`, kept by every
  step until its take; `Pz` follows by `pz_of_unowned`).
- `box_at`, `box_n`, `box_env`: the landing's projections.

This module is statement only: the proof that `h0`'s segment lands in `Box`
is the open obligation (`Box`'s conjuncts are consumed in `h1Stmt_of`'s
`hB`).
-/
import Spike.Lib.A64WakeWcInv
import Spike.Lib.A64OwnedPz
import Spike.Lib.A64KeepUn
import Spike.Lib.WakeLoadT

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.WakeT1 (mainTidLbl)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.WakePreA (spawnTerm)

/-- **The box's landing** at the fresh label `l`, the cell `b` and the size
`n` (`H1Stmt`'s `Box`), in `L`'s executable, `h0`'s memory side `ms0` and
the start's frame condition `F0`: for some region `R`, frame condition `F`,
`wc_main` entry invariant `J0` and thread pointer `t`,
- the region: `R.OK`, `base` 16-aligned, `F` stable, `R.lo ≤ -336`
  (`wake_wc_mid_hatW`'s `hlo`; the heap abort's stub, needs `-288`,
  `wake_wc_entry_segW` `-240`), `0 ≤ R.hi`, two words of room above the
  base (`hfit`, `WakeMainS.wR_hfit` at `WakeM.wR`) and the caller's two
  frame words loadable under `F` (`hupF`, `wR_hup` at `WakeM.wF`);
- `wc_main`'s frame on a pool stack (`WcSp4W.BandTi L R`'s body): `sp` at
  the call (`R.addr (-80)`) and past the callee's `sub` (`R.addr (-128)`)
  in `(pool.lo, pool.lo + pool.size]`;
- `F` inside `F0` (the start's facts kept: the limit word unmapped, the
  heap and counter off);
- the call's shape (for `CloneInv`/`ClonePost`): `J0` is
  `WakeM.wJ0` of `scc_rt_main`'s call node `wNC` over some `J` and `σC`,
  `x0` at `J0` is main's `ThreadId` word (`WakeLoadT.tcb0`), and the region
  is `48` below the top of stack 0 (`stacksA + 16384`);
- the pair at `bX ms0 lab J0 l b` (past the box's store, the cell at
  `[sp, #8]`) with the thread pointer `t`, main's TCB (`WakeLoadT.tcb0`:
  `pinA + 8`);
- one object (`n = 1`, `NewSt`'s `mxa l A 1`);
- the source past the `new`: the term `boxTerm`, no hold, `o` bound to
  `l`'s owned locative at `.ptr .own .int` (the `new` of `z : int`), `me` to main's `ThreadId` locative;
- main's stack owned (`Ti2.r0Of`), the child's stack unmapped
  (`KeepUn.U` at `PreChild.r1Of`: state-level, kept by every step and by
  the segments up to the take, `KeepUn.SegW.keepUn`; its `Pz`, word-level,
  is what the take site's callers need to refute it owned);
- `F` kept by the child stack's take (`hFt`: `scc_rt_thread_init`'s, inside
  the box's segment) and reading memory only (`hFd`: a `clone` refusal
  writes `x0`), and the region below the child's stack (`R.hi ≤ 48`: its top
  is stack 0's, `r1Of`'s base), for the take's frame facts (`hKR`);
- main's stack mapped off the region under `F` (`StackOff` at `Ti2.r0Of`:
  every aligned word of stack 0 outside `R` loadable), the thread-init
  segment's `hF0` (`StackM` at `r0Of` is not kept by `FStable`, whose
  `DFrame` frees the inside of `R`, itself inside stack 0);
- the region's bounds word-aligned (`R.lo % 8 = 0`, `R.hi % 8 = 0`: no
  word straddles its edges; at `h0`'s `WakeM.wR (swR v (-384) 0) 336`
  they are `-336` and `0`).

**Provisional**: the ownership conjunct (pending the take's ownership kept
through `wc_main`'s nodes); `PlacedSE` at `L0T` is not included (it is
rebuilt from the TCB and the env conjuncts). -/
def Box (L : RuntimeLayout) (ms0 : MemSide isaLSE2) (F0 : MachineData → Prop)
    (l : WeakMem.AllocLabel) (b n : Nat) (s : State) (c : Ctl) : Prop :=
  ∃ (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64),
    (R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -336 ∧ 0 ≤ R.hi ∧
      (R.base.toNat : Int) + 16 ≤ 2 ^ 64 ∧
      ∀ m, F m → ∀ k : Int, k % 8 = 0 → 0 ≤ k → k < 16 → (Mem.loadInt m.dmem (R.addr k) 8).isSome) ∧
    (∀ k, -128 ≤ k → k ≤ -80 → L.Λ.stackPool.lo < (R.addr k).toNat ∧
      (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) ∧
    (∀ m, F m → F0 m) ∧
    ((∃ (J : AS → Ctl → Prop) (σC : AS),
        J0 = WakeM.wJ0 (WakeM.wNC (_root_.Executable.labels L.exe).label J).J σC) ∧
      (∀ σe c, J0 σe c → σe.regs.X0.toNat = Spike.Lib.WakeLoadT.tcb0 L.Λ) ∧
      R.base.toNat + 48 = L.stacksA.toNat + 16384) ∧
    (At L.exe L.endPc R F (bX ms0 (_root_.Executable.labels L.exe).label J0 l b) s c ∧
      Spike.Lib.A64.KeepTP.TP t s ∧ t.toNat = L.pinA.toNat + 8) ∧
    n = 1 ∧
    (c.term = boxTerm ∧ c.hold = none ∧
      TermRun.evalAt c.env (.var "o") = some (.ptr .own .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      TermRun.evalAt c.env (.var "me") = some (.tid, [TermRun.cst (.loc ⟨mainTidLbl 2, 0⟩ 0)])) ∧
    (Spike.Lib.A64Consumer.Owned L.Λ (Spike.Lib.A64.Rt.Ti2.r0Of (_root_.Executable.labels L.exe).label) s ∧
      Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) s) ∧
    ((∀ m pm, F m → F (Ret0.takeMem pm (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) m)) ∧
      (∀ m m' : MachineData, m'.dmem = m.dmem → F m → F m') ∧ R.hi ≤ 48 ∧
      (∀ m, F m → Ret0.StackOff (Spike.Lib.A64.Rt.Ti2.r0Of (_root_.Executable.labels L.exe).label) R m) ∧
      R.lo % 8 = 0 ∧ R.hi % 8 = 0)

variable {L : RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
  {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl}

/-- The landing is past the box's store with main's thread pointer. -/
theorem box_at (h : Box L ms0 F0 l b n s c) :
    ∃ (R : Region) (F : MachineData → Prop) (J0 : AS → Ctl → Prop) (t : UInt64),
      At L.exe L.endPc R F (bX ms0 (_root_.Executable.labels L.exe).label J0 l b) s c ∧
        Spike.Lib.A64.KeepTP.TP t s :=
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

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.box_env' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.box_env

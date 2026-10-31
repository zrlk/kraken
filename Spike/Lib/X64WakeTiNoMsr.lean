/-
**`scc_rt_thread_init`'s and `scc_rt_stack_take`'s obligations at cells
other than a `syscall`** (x86-64; twin of `Spike/Lib/A64WakeTiNoMsr.lean`):
every node obligation of the two runtime functions inside `W` is one inside
`fun s c => W s c ∧ NoSetFsAt s` in any valid layout of cells with their
code checks (`threadInitIn`, `stackTakeIn`), the form the thread pointer's
keep (`SegW.keepTPA`, `X64WakeWcHat`) reads off the fragment. None of their
blocks is a `syscall`. As on AArch64 no `K` clause is added: the take's
site is moved by its outside move, so only its code is read there.

- `blkA`, `nodeA`: `BlkW.noSetFs`, `NodeW.noSetFs` at a `blockAtB` check,
  without the `K` clause;
- `takeW_nm`: `scc_rt_stack_take`'s obligations (the site from its `nop`);
- `tiW_nm`: `scc_rt_thread_init`'s, the nested take by `takeW_nm`.

**Unlike AArch64**: the thread pointer is `fsBase`, changed only by
`arch_prctl`, so `NoMsrAt` / `dNoMsr` are `NoSetFsAt` / `dNoSys` (cells
other than `syscall`, `X64KeepTP`); the code checks are `blockAtB` /
`labelGapB` on cells (A64's `blockAt prog l k`), so a node's pc is
`label l + ofNat k` in bytes; x86-64's `TakeW` has no `adrp` pairs (its
single-instruction nodes are plain `NodeW`s), `TakeW` / `TiW` take no `P`,
and `TiW` has the extra block `.c7` (the call).
-/
import Spike.Lib.X64Ret0
import Spike.Lib.X64KeepTPW
import Spike.Lib.Rt.X64RtStartU

namespace Spike.Lib.X64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region)
open Spike.Lib.X64 (ND BlkW NodeW At cNoSys noSetFsAt_of_code)
open Spike.Lib.X64.KeepTP (NoSetFsAt)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Ret0 (TakeG TakeW TK TiG TiW TI tiCall storeBlks_eq)
open Spike.Lib.X64.Flow.Ret0.StackTake (stackTakeIn)
open Spike.Lib.X64.Flow.Ret0.ThreadInit (threadInitIn storeOff callBlk)
open Spike.Lib.X64.Flow.Ret0.AllocTcb (siAt)
open Spike.Lib.X64.Rt.StartU (blkW_wmono nodeW_wmono)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F M : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
  {kp : Nat} {cells : List (Directive × Nat)}

/-- **A block node at a checked block with no `syscall`** is inside
`W ∧ NoSetFsAt`. -/
theorem blkA (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {n : ND} {b : List (Directive × Nat)} {l : Label} {k : Nat} (h : BlkW W K exe endPc R F n b)
    (hb : blockAtB cells l k b = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hds : cNoSys b = true) : BlkW (fun s c => W s c ∧ NoSetFsAt s) K exe endPc R F n b :=
  blkW_wmono (fun _ _ h => ⟨h.1, h.2.1⟩) (h.noSetFs (code_field hp hend hb e) hds)

/-- **A node at a checked block with no `syscall`** is inside
`W ∧ NoSetFsAt`. -/
theorem nodeA (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    {n : ND} {b : List (Directive × Nat)} {l : Label} {k : Nat} (h : NodeW W K exe endPc R F n)
    (hb : blockAtB cells l k b = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hne : 0 < b.length) (hds : cNoSys b = true) : NodeW (fun s c => W s c ∧ NoSetFsAt s) K exe endPc R F n :=
  nodeW_wmono (fun _ _ h => ⟨h.1, h.2.1⟩) (h.noSetFs (code_field hp hend hb e) hne hds)

set_option hygiene false in
/-- A block node at its `blockAtB` check `H`. -/
local macro "tb " H:term:max : tactic =>
  `(tactic| exact blkA hp hend hi $H (by first | rfl | exact ofNat_zero' _) (by decide))

set_option hygiene false in
/-- A single-instruction node at its `blockAtB` check `H`. -/
local macro "tn " H:term:max : tactic =>
  `(tactic| exact nodeA hp hend hi $H (by first | rfl | exact ofNat_zero' _) (by decide) (by decide))

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_stack_take` is inside `W ∧ NoSetFsAt`**: its blocks and nodes
by `blkA`/`nodeA`, the site at its `nop`. -/
theorem takeW_nm (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : stackTakeIn cells = true) {q : TakeG} (h : ∀ i, TakeW W K exe endPc R F M q i) :
    ∀ i, TakeW (fun s c => W s c ∧ NoSetFsAt s) K exe endPc R F M q i := by
  simp only [stackTakeIn, siAt, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨-, t0, t1, t2, t3, d0, t4, d26, t5, d52, t6, t7, swp, t8, t9, ldn, t10, b0, t11, unl, b31, t12, nxt,
    t13, t14, ok0, t15, t16, -, tn, t17⟩ := hin
  intro i
  have hi := h i
  cases i <;> dsimp only [TakeW] at hi ⊢
  case e => tb t0
  case entry => tb t1
  case cls => tb t2
  case j1 => tb t3
  case d0 => tn d0
  case d7 => tb t4
  case d26 => tn d26
  case d33 => tb t5
  case d52 => tn d52
  case d59 => tb t6
  case sp0 => tb t7
  case swp => tn swp
  case sp14 => tb t8
  case lk0 => tb t9
  case ldn => tn ldn
  case lk7 => tb t10
  case b0 => tn b0
  case b7 => tb t11
  case unl => tn unl
  case b31 => tn b31
  case b38 => tb t12
  case nxt => tn nxt
  case b61 => tb t13
  case b108 => tb t14
  case ok0 => tn ok0
  case ok7 => tb t15
  case tk => tb t16
  case site =>
    intro s c hA
    obtain ⟨he, hn, -, hpc, -⟩ := id hA
    exact ⟨hi s c hA, noSetFsAt_of_code (code_field hp hend tn (ofNat_zero' _) s he hn) (by decide) (j := 0)
      (by decide) rfl rfl (by rw [hpc]; simp [Spike.Lib.X64.cellOff]; rfl)⟩
  case ret => tb t17

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_thread_init` is inside `W ∧ NoSetFsAt`**: its blocks and
stores by `blkA`/`nodeA`, the nested take by `takeW_nm`. -/
theorem tiW_nm (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : threadInitIn cells = true) (hst : stackTakeIn cells = true) {q : TiG}
    (h : ∀ i, TiW W K exe endPc R F M q i) : ∀ i, TiW (fun s c => W s c ∧ NoSetFsAt s) K exe endPc R F M q i := by
  simp only [threadInitIn, storeOff, storeBlks_eq,
    List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    and_assoc] at hin
  obtain ⟨-, t0, t1, tc, -, t2, t3, t4, t5, t6, t7, t8, s0, s1, s2, s3, s4, s5⟩ := hin
  rw [show callBlk = tiCall from rfl] at tc
  intro i
  have hi := h i
  cases i <;> dsimp only [TiW] at hi ⊢
  case e => tb t0
  case entry => tb t1
  case c7 => tb tc
  case call => exact fun g hg => takeW_nm hp hend hst (hi g hg)
  case x7 => tb t2
  case st0 => tn s0
  case f1 => tb t3
  case st1 => tn s1
  case f2 => tb t4
  case st2 => tn s2
  case f3 => tb t5
  case st3 => tn s3
  case f4 => tb t6
  case st4 => tn s4
  case f5 => tb t7
  case st5 => tn s5
  case ret => tb t8

end Spike.Lib.X64.WakePh.Ti2

/-- info: 'Spike.Lib.X64.WakePh.Ti2.blkA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.blkA

/-- info: 'Spike.Lib.X64.WakePh.Ti2.nodeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.nodeA

/-- info: 'Spike.Lib.X64.WakePh.Ti2.takeW_nm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.takeW_nm

/-- info: 'Spike.Lib.X64.WakePh.Ti2.tiW_nm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.tiW_nm

/-
**`scc_rt_thread_init`'s and `scc_rt_stack_take`'s obligations at cells
other than an `MSR`** (AArch64): every node obligation of the two runtime
functions inside `W` is one inside `fun s c => W s c ∧ NoMsrAt s` in any
valid layout of a program with their code checks (`threadInitIn`,
`stackTakeIn`), the form `HMidP.ti`'s segment asks (`SegW.keepTP` reads
`NoMsrAt` off the fragment). None of their blocks is an `MSR`. Unlike
`NoMsrW` no `K` clause is added: the take's site is moved by its outside
move, so only its code is read there.

- `blkA`, `nodeA`: `blk_nm`, `node_nm` without the `K` clause;
- `takeW_nm`: `scc_rt_stack_take`'s obligations (the site from its `nop`);
- `tiW_nm`: `scc_rt_thread_init`'s, the nested take by `takeW_nm`.
-/
import Spike.Lib.A64WakeWcNoMsr
import Spike.Lib.Rt.A64RtStartU

namespace Spike.Lib.A64.WakePh.Ti2

open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.KeepTP (NoMsrAt dNoMsr)
open Spike.Lib.A64.Flow.Ret0 (TakeG TakeW TK TiG TiW TI)
open Spike.Lib.A64.Flow.WakeWc (blk_nm node_nm)
open Spike.Lib.A64.Rt.StartU (blkW_wmono nodeW_wmono)
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Spike.Lib.A64.Flow.Ret0 (ofNat4_succ')

/-- A node's pc at its label and cell. -/
local macro "pcE" : tactic =>
  `(tactic| first | rfl | exact ofNat4_zero _ | exact (ofNat4_succ' _ _).symm | (rw [ofNat4_zero]; rfl))

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F M P : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
  {kp : Nat} {prog : List Directive}

/-- **A block node at a checked block with no `MSR`** is inside `W ∧ NoMsrAt`. -/
theorem blkA (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {n : ND} {b : List Directive} {l : Label} {k : Nat} (h : BlkW W K exe endPc R F n b)
    (hb : blockAt prog l k b = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hds : b.all dNoMsr = true) : BlkW (fun s c => W s c ∧ NoMsrAt s) K exe endPc R F n b :=
  blkW_wmono (fun _ _ h => ⟨h.1, h.2.1⟩) (blk_nm hp hend h hb e hds)

/-- **A node at a checked one-instruction block with no `MSR`** is inside
`W ∧ NoMsrAt`. -/
theorem nodeA (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    {n : ND} {d : Directive} {l : Label} {k : Nat} (h : NodeW W K exe endPc R F n)
    (hb : blockAt prog l k [d] = true) (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hds : [d].all dNoMsr = true) : NodeW (fun s c => W s c ∧ NoMsrAt s) K exe endPc R F n :=
  nodeW_wmono (fun _ _ h => ⟨h.1, h.2.1⟩) (node_nm hp hend h hb e hds)

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_stack_take` is inside `W ∧ NoMsrAt`**: its blocks and nodes by
`blkA`/`nodeA`, the label pairs' second instructions one cell on, the site
at its `nop`. -/
theorem takeW_nm (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : Ret0.StackTake.stackTakeIn prog = true) {q : TakeG} (h : ∀ i, TakeW W K exe endPc R F M q i P) :
    ∀ i, TakeW (fun s c => W s c ∧ NoMsrAt s) K exe endPc R F M q i P := by
  simp only [Ret0.StackTake.stackTakeIn, Ret0.StackTake.labIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨-, t0, t1, t2, t3, d0a, d0b, t4, d7a, d7b, t5, d14a, d14b, t6, t7, t8, t9, t10, t11, t12, b0a, b0b,
    t13, t14, b6a, b6b, t15, t16, t17, t18, ok0a, ok0b, t19, t20, -, tn, t21⟩ := hin
  intro i
  have hi := h i
  cases i <;> dsimp only [TakeW] at hi ⊢
  case e => exact blkA hp hend hi t0 (ofNat4_zero _) (by decide)
  case entry => exact blkA hp hend hi t1 (ofNat4_zero _) (by decide)
  case cls => exact blkA hp hend hi t2 (ofNat4_zero _) (by decide)
  case j1 => exact blkA hp hend hi t3 rfl (by decide)
  case d0 => exact ⟨nodeA hp hend hi.1 d0a (by pcE) (by decide),
    nodeA hp hend hi.2 d0b (by pcE) (by decide)⟩
  case d2 => exact blkA hp hend hi t4 rfl (by decide)
  case d7 => exact ⟨nodeA hp hend hi.1 d7a rfl (by decide), nodeA hp hend hi.2 d7b (by pcE) (by decide)⟩
  case d9 => exact blkA hp hend hi t5 rfl (by decide)
  case d14 => exact ⟨nodeA hp hend hi.1 d14a rfl (by decide),
    nodeA hp hend hi.2 d14b (by pcE) (by decide)⟩
  case d16 => exact blkA hp hend hi t6 rfl (by decide)
  case sp0 => exact blkA hp hend hi t7 (ofNat4_zero _) (by decide)
  case swp => exact nodeA hp hend hi t8 rfl (by decide)
  case sp3 => exact blkA hp hend hi t9 rfl (by decide)
  case lk0 => exact blkA hp hend hi t10 (ofNat4_zero _) (by decide)
  case ldn => exact nodeA hp hend hi t11 rfl (by decide)
  case lk2 => exact blkA hp hend hi t12 rfl (by decide)
  case b0 => exact ⟨nodeA hp hend hi.1 b0a (by pcE) (by decide),
    nodeA hp hend hi.2 b0b (by pcE) (by decide)⟩
  case b2 => exact blkA hp hend hi t13 rfl (by decide)
  case unl => exact nodeA hp hend hi t14 rfl (by decide)
  case b6 => exact ⟨nodeA hp hend hi.1 b6a rfl (by decide), nodeA hp hend hi.2 b6b (by pcE) (by decide)⟩
  case b8 => exact blkA hp hend hi t15 rfl (by decide)
  case nxt => exact nodeA hp hend hi t16 rfl (by decide)
  case b12 => exact blkA hp hend hi t17 rfl (by decide)
  case b21 => exact blkA hp hend hi t18 rfl (by decide)
  case ok0 => exact ⟨nodeA hp hend hi.1 ok0a (by pcE) (by decide),
    nodeA hp hend hi.2 ok0b (by pcE) (by decide)⟩
  case ok2 => exact blkA hp hend hi t19 rfl (by decide)
  case tk => exact blkA hp hend hi t20 (ofNat4_zero _) (by decide)
  case site =>
    intro s c hA
    obtain ⟨he, hn, -, hpc, -⟩ := id hA
    exact ⟨hi s c hA, noMsrAt_of_code (code_of hp hend tn (ofNat4_zero _) s he hn) (by decide) (j := 0)
      (by decide) rfl rfl (by rw [ofNat4_zero]; exact hpc)⟩
  case ret => exact blkA hp hend hi t21 rfl (by decide)

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_thread_init` is inside `W ∧ NoMsrAt`**: its blocks and stores
by `blkA`/`nodeA`, the nested take by `takeW_nm`. -/
theorem tiW_nm (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hin : Ret0.ThreadInit.threadInitIn prog = true) (hst : Ret0.StackTake.stackTakeIn prog = true) {q : TiG}
    (h : ∀ i, TiW W K exe endPc R F M q i P) : ∀ i, TiW (fun s c => W s c ∧ NoMsrAt s) K exe endPc R F M q i P := by
  simp only [Ret0.ThreadInit.threadInitIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨-, t0, t1, t2, s0, t3, s1, t4, s2, t5, s3, t6, s4, t7, s5, t8⟩ := hin
  intro i
  have hi := h i
  cases i <;> dsimp only [TiW] at hi ⊢
  case e => exact blkA hp hend hi t0 (ofNat4_zero _) (by decide)
  case entry => exact blkA hp hend hi t1 (ofNat4_zero _) (by decide)
  case call => exact fun g hg => takeW_nm hp hend hst (hi g hg)
  case sp => exact blkA hp hend hi t2 (ofNat4_zero _) (by decide)
  case st0 => exact nodeA hp hend hi s0 rfl (by decide)
  case f1 => exact blkA hp hend hi t3 rfl (by decide)
  case st1 => exact nodeA hp hend hi s1 rfl (by decide)
  case f2 => exact blkA hp hend hi t4 rfl (by decide)
  case st2 => exact nodeA hp hend hi s2 rfl (by decide)
  case f3 => exact blkA hp hend hi t5 rfl (by decide)
  case st3 => exact nodeA hp hend hi s3 rfl (by decide)
  case f4 => exact blkA hp hend hi t6 rfl (by decide)
  case st4 => exact nodeA hp hend hi s4 rfl (by decide)
  case f5 => exact blkA hp hend hi t7 rfl (by decide)
  case st5 => exact nodeA hp hend hi s5 rfl (by decide)
  case ret => exact blkA hp hend hi t8 rfl (by decide)

end Spike.Lib.A64.WakePh.Ti2

/-- info: 'Spike.Lib.A64.WakePh.Ti2.blkA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.blkA

/-- info: 'Spike.Lib.A64.WakePh.Ti2.nodeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.nodeA

/-- info: 'Spike.Lib.A64.WakePh.Ti2.takeW_nm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.takeW_nm

/-- info: 'Spike.Lib.A64.WakePh.Ti2.tiW_nm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.tiW_nm

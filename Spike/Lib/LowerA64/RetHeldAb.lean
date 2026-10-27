/-
**`main`'s `ret b` block keeps the write abort's phase at the held frames**
(AArch64): `retHeld_hW`'s `hab` (`Spike/Lib/LowerA64/RetHeldW.lean`) from
`blkW_abSt_subCdLR` (`Spike/Lib/LowerA64/UserAbR.lean`): the block
`directives (ls ++ cx.leave ++ [ret])` a part of the code off the write
abort's labels at the return address `ra` of its frame (`FrJ`), its only
`ret` the last instruction, reached at `ra` (the epilogue's `x30`, the
frame's saved return address), every other instruction a fall-through
(the result's loads, `ldr`, `movz`/`movk`; the epilogue's `ldr`s and `add`),
and `ra` a position off the write abort (`hpos`, e.g. `posOff_mainRetS`).

- `fallBlk_movzD`, `fallBlk_movkD`, `fallBlk_movImm`, `fallBlk_getOp`, `fallBlk_retLoads`: the result's loads
  are fall-throughs;
- `retBlk_fallR`: every instruction of the return block a fall-through or a
  `ret`; `retBlk_last`: its last instruction a `ret`;
- `retBlk_pc_heldRN`: the return block's run at the held node lands at the
  frame's `ra`;
- `retHeld_hab`: the return block keeps the write abort's phase at the held
  node of its `bodyN2`, `retHeld_hW`'s `hab`.
-/
import Spike.Lib.LowerA64.RetHeldW
import Spike.Lib.LowerA64.UserAbR

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (Marks)
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.WriteAb (Ab)

/-! ## The return block's instructions -/

/-- `movz` is a fall-through. -/
theorem fallBlk_movzD (d : XReg) (q : Nat × Nat) : fallBlk [movzD d q] = true := by
  unfold movzD fallBlk A64.Flow.classify; rfl

/-- `movk` is a fall-through. -/
theorem fallBlk_movkD (d : XReg) (q : Nat × Nat) : fallBlk [movkD d q] = true := by
  unfold movkD fallBlk A64.Flow.classify; rfl

/-- A `movz`/`movk` is a fall-through. -/
theorem fallBlk_movImm (t : XReg) (v : Int) : fallBlk (directives (movImm t v)) = true := by
  rw [directives_movImm]
  generalize nzHw _ 0 = hs
  cases hs with
  | nil => exact fallBlk_movzD t (0, 0)
  | cons q rest =>
    show fallBlk (movzD t q :: rest.map (movkD t)) = true
    simp only [fallBlk, List.all_cons, List.all_map, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by simpa [fallBlk] using fallBlk_movzD t q, fun x _ => ?_⟩
    simpa [fallBlk] using fallBlk_movkD t x

/-- An operand's load is a fall-through. -/
theorem fallBlk_getOp {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {t : XReg} {a : Scc.IR.Operand}
    {l : List Item} (ha : cx.getOp t a = .ok l) : fallBlk (directives l) = true := by
  rcases getOp_cases hf h1 ha with ⟨r, off, -, -, hl⟩ | ⟨v, -, rfl⟩
  · rw [hl]
    simp [fallBlk, RW.dir, AI.toDir, A64.Flow.classify, RegOnly, fallI]
  · exact fallBlk_movImm t _

/-- The result's loads are fall-throughs. -/
theorem fallBlk_retLoads {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) :
    ∀ (ps : List (Scc.IR.Operand × XReg)) {ls : List Item}, retLoads cx ps = .ok ls →
      fallBlk (directives ls) = true
  | [], ls, h => by
    simp only [retLoads, Except.ok.injEq] at h
    subst h
    simp [directives, fallBlk]
  | (o, r) :: ps, ls, h => by
    simp only [retLoads, bind, Except.bind] at h
    cases hl : cx.getOp r o with
    | error e => rw [hl] at h; cases h
    | ok l =>
      rw [hl] at h
      cases hr : retLoads cx ps with
      | error e => rw [hr] at h; cases h
      | ok ls' =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [directives_append]
        simp only [fallBlk, List.all_append, Bool.and_eq_true]
        exact ⟨fallBlk_getOp hf h1 hl, fallBlk_retLoads hf h1 ps hr⟩

/-- **Every instruction of the return block is a fall-through or a `ret`.** -/
theorem retBlk_fallR {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {ps : List (Scc.IR.Operand × XReg)}
    {ls : List Item} (hl : retLoads cx ps = .ok ls) :
    ∀ d ∈ directives (ls ++ cx.leave ++ [ret]), ∀ a, A64.Flow.classify d = some a →
      fallI a = true ∨ ∃ r, a = .ret r := by
  rw [directives_leave hf h1]
  intro d hd a ha
  rcases List.mem_append.mp hd with hd | hd
  · have := List.all_eq_true.mp (fallBlk_retLoads hf h1 ps hl) d hd
    rw [ha] at this
    exact .inl this
  · simp only [epi, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;>
      simp [RW.dir, AI.toDir, A64.Flow.classify, RegOnly] at ha <;> subst ha <;> simp [fallI]

/-- **The return block's last instruction is a `ret`.** -/
theorem retBlk_last {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (ls : List Item) :
    ∃ hne : directives (ls ++ cx.leave ++ [ret]) ≠ [], ∃ r,
      A64.Flow.classify ((directives (ls ++ cx.leave ++ [ret])).getLast hne) = some (.ret r) := by
  have hds := directives_leave hf h1 ls
  refine ⟨by rw [hds]; simp [epi], .low (.reg .X30) .W64, ?_⟩
  simp only [hds, epi]
  rw [List.getLast_append_of_ne_nil _ (by simp)]
  simp [AI.toDir, A64.Flow.classify]

/-! ## At the held node -/

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {fs : List TermRun.Frame}

/-- **The return block's run at the held node lands at the frame's
`ra`** (`FrJ`, the epilogue's `ret x30`). -/
theorem retBlk_pc_heldRN {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    {ps : List (Scc.IR.Operand × XReg)} {ls : List Item} (hl : retLoads cx ps = .ok ls) (lab : Label → Int64)
    {i : Expr → String → Nat → Option Nat} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr}
    {s : Spike.Lib.Form.SEnv} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {tp : UInt64} :
    ∀ σ c, (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp)).J σ c →
      (arun lab (directives (ls ++ cx.leave ++ [ret]))
        ⟨(heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp)).pc,
         (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp)).o, σ⟩).pc =
        Int64.ofBitVec ra := by
  rintro σ c ⟨-, cR, -, ⟨-, hfj, -⟩, -⟩
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  show (arun lab (directives (ls ++ cx.leave ++ [ret])) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩).pc = _
  obtain ⟨R', hrun, -⟩ := arun_retLoads hf h1 lab _ hl pc σ
  rw [directives_leave hf h1, arun_append, hrun]
  obtain ⟨hpc, -⟩ := arun_epi lab
    (pc + Int64.ofNat (4 * (directives ls).length)) (-(cx.frame : Int)) { σ with regs := R' }
    (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc
  rw [hpc, hfj.2]

/-- **`main`'s `ret b` block keeps the write abort's phase at the held
frames** (`retHeld_hW`'s `hab`; `blkW_abSt_subCdLR`): the block a part of
the code off the write abort's labels at the frame's return address `ra`
(`hcd`), covered (`hok`); `ra` a position off the write abort (`hpos`, e.g.
`posOff_mainRetS` at `scc_rt_main`'s return point). -/
theorem retHeld_hab {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habt : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    {ps : List (Scc.IR.Operand × XReg)} {ls : List Item} (hl : retLoads cx ps = .ok ls)
    {i : Expr → String → Nat → Option Nat} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr}
    {s : Spike.Lib.Form.SEnv} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {tp : UInt64} {R : Region} {F : MachineData → Prop} {lo hi : Int}
    (hcd : SubCd (CdCL prog okPc ph lab (Int64.ofBitVec ra)) pc (directives (ls ++ cx.leave ++ [ret])))
    (hok : okBlk lo hi (oF cx) (directives (ls ++ cx.leave ++ [ret])) = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpos : PosOff prog lab (Int64.ofBitVec ra)) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
      (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp))
      (directives (ls ++ cx.leave ++ [ret])) := by
  refine blkW_abSt_subCdLR hI hpr habt hcd hok hR hal hlo hhi
    (hret_of_run hok (retBlk_pc_heldRN hf h1 hl lab)) (.inl (retBlk_last hf h1 ls)) ?_
  intro σ c _ k hk a ha t ht hc
  rcases retBlk_fallR hf h1 hl _ (List.getElem_mem hk) a ha with hfa | ⟨r, rfl⟩
  · rcases hc with hc | ⟨r, rfl⟩
    · cases a <;> simp only [fallI, Bool.false_eq_true] at hfa <;>
        simp only [aiTgts, List.mem_singleton] at ht <;> exact absurd ht hc
    · simp [fallI] at hfa
  · simp only [aiTgts, List.mem_singleton] at ht
    exact .inl (ht ▸ hpos)

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.retBlk_fallR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retBlk_fallR

/-- info: 'Spike.Lib.LowerA64.retHeld_hab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retHeld_hab

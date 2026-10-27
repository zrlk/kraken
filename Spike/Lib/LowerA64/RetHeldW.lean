/-
**`main`'s `ret b` block inside `W2` at the held frames** (AArch64): the
block `directives (ls ++ cx.leave ++ [ret])` (the result's loads, the
frame's exit, `ret`) at the held node of its `bodyN2`
(`Spike/Lib/LowerA64/Body2SegHF.lean`), its states inside `W2` by
`blkW_heldTail`: `HeldS` by `blkW_heldS` from the abort phase's facts (the
caller's, `blkW_abSt_subCdLR`), `Ret0` from the frame's result cell
(`blkW_ret0_slot`, the block stores nothing), no write (`blkW_noWr'`) and no
system call (`blkW_noSys'`).

- `NoStr`, `arun_slot_of_noStr`: a block of no stores keeps the cells
  before each of its instructions;
- `retBlk_noStr`, `retBlk_slot`: the return block stores nothing;
- `retSlot_heldRN`: `RetSlot` at the held node of a `bodyN2`;
- `retHeld_hW`: the return block's states inside `W2` at the held frames,
  `retHeld_seg`'s `hW`.
-/
import Spike.Lib.LowerA64.Body2SegHF
import Spike.Lib.LowerA64.HeldTailSlot
import Spike.Lib.LowerA64.LaneW2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

/-! ## Blocks of no stores -/

/-- **A directive that is no stack store.** -/
def NoStr (d : Directive) : Prop := ∀ t n, d ≠ (AI.str t n).toDir

/-- **A step of no store keeps the cells.** -/
theorem dstep_slot_of_noStr (lab : Label → Int64) (am : AM) {d : Directive} (h : NoStr d) :
    (Spike.Lib.A64.Flow.dstep lab am d).σ.slot = am.σ.slot := by
  unfold Spike.Lib.A64.Flow.dstep
  cases hc : classify d with
  | none => rfl
  | some a =>
    have hd := (classify_sound hc).1
    cases a with
    | str t n => exact absurd hd (h t n)
    | _ => rfl

/-- **A run of no stores keeps the cells.** -/
theorem arun_slot_of_noStr (lab : Label → Int64) :
    ∀ (blk : List Directive) (am : AM), (∀ d ∈ blk, NoStr d) → (arun lab blk am).σ.slot = am.σ.slot
  | [], _, _ => rfl
  | d :: blk, am, h => by
    show (arun lab blk (Spike.Lib.A64.Flow.dstep lab am d)).σ.slot = _
    rw [arun_slot_of_noStr lab blk _ fun d' hd' => h d' (List.mem_cons_of_mem _ hd'),
      dstep_slot_of_noStr lab am (h d (List.mem_cons_self ..))]

/-- **A block of no stores keeps the cells before each instruction.** -/
theorem arun_take_slot_of_noStr (lab : Label → Int64) {blk : List Directive} (h : ∀ d ∈ blk, NoStr d)
    (am : AM) (k : Nat) : (arun lab (blk.take k) am).σ.slot = am.σ.slot :=
  arun_slot_of_noStr lab _ am fun d hd => h d (List.mem_of_mem_take hd)

/-! ## The return block -/

/-- A `movz`/`movk` is no store. -/
theorem noStr_movImm (t : XReg) (v : Int) : ∀ d ∈ directives (movImm t v), NoStr d := by
  rw [directives_movImm]
  intro d hd t' n he
  generalize nzHw _ 0 = hs at hd
  cases hs with
  | nil =>
    simp only [movDs, List.mem_singleton] at hd
    subst hd; simp [movzD, AI.toDir] at he
  | cons p rest =>
    simp only [movDs, List.mem_cons, List.mem_map] at hd
    rcases hd with rfl | ⟨q, -, rfl⟩
    · simp [movzD, AI.toDir] at he
    · simp [movkD, AI.toDir] at he

/-- An operand's load is no store. -/
theorem noStr_getOp {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {t : XReg} {a : Scc.IR.Operand}
    {l : List Item} (ha : cx.getOp t a = .ok l) : ∀ d ∈ directives l, NoStr d := by
  rcases getOp_cases hf h1 ha with ⟨r, off, -, -, hl⟩ | ⟨v, -, rfl⟩
  · rw [hl]
    intro d hd t' n he
    simp only [List.mem_singleton] at hd
    subst hd; simp [RW.dir, AI.toDir] at he
  · exact noStr_movImm t _

/-- The result's loads are no stores. -/
theorem noStr_retLoads {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) :
    ∀ (ps : List (Scc.IR.Operand × XReg)) {ls : List Item}, retLoads cx ps = .ok ls →
      ∀ d ∈ directives ls, NoStr d
  | [], ls, h => by
    simp only [retLoads, Except.ok.injEq] at h
    subst h
    simp [directives]
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
        intro d hd
        rcases List.mem_append.mp hd with hd | hd
        · exact noStr_getOp hf h1 hl d hd
        · exact noStr_retLoads hf h1 ps hr d hd

/-- **The return block stores nothing.** -/
theorem retBlk_noStr {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {ps : List (Scc.IR.Operand × XReg)}
    {ls : List Item} (hl : retLoads cx ps = .ok ls) : ∀ d ∈ directives (ls ++ cx.leave ++ [ret]), NoStr d := by
  rw [directives_leave hf h1]
  intro d hd
  rcases List.mem_append.mp hd with hd | hd
  · exact noStr_retLoads hf h1 ps hl d hd
  · intro t n he
    simp only [epi, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [RW.dir, AI.toDir] at he

/-- **The return block keeps the cells before each instruction.** -/
theorem retBlk_slot {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {ps : List (Scc.IR.Operand × XReg)}
    {ls : List Item} (hl : retLoads cx ps = .ok ls) (lab : Label → Int64) (am : AM) (k : Nat) :
    (arun lab ((directives (ls ++ cx.leave ++ [ret])).take k) am).σ.slot = am.σ.slot :=
  arun_take_slot_of_noStr lab (retBlk_noStr hf h1 hl) am k

/-! ## Inside `W2` -/

/-- **`RetSlot` at the held node of a `bodyN2`**: the held pair's run
lands at a control of `bodyN2`'s invariant, whose symbolic environment `s`
places the frame's result `f.x` as a register operand at a region cell
(`hx`). -/
theorem retSlot_heldRN {p : Prog} {lbl : Lbl} {lsize : WeakMem.AllocLabel → Nat}
    {i : Expr → String → Nat → Option Nat} {cx : FnCtx} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr}
    {s : Spike.Lib.Form.SEnv} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {tp : UInt64} {fs : List TermRun.Frame} {R : Region}
    (hx : ∀ f, fs = [f] → ∃ t r, Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]) ∧
      ∃ k, rsOf cx r = some k ∧ R.Off k) :
    ∀ σ c, (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp)).J σ c →
      RetSlot p lbl R σ c := by
  rintro σ c ⟨hH, cR, hr, ⟨⟨L, sm, B, c', hloc, hJ, -⟩, -⟩, -⟩
  exact retSlot_of_heldRun hH hr hloc hJ hx

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl lbl0 : Lbl}
  {lsize : Lsize} {fs : List TermRun.Frame} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop} {K : State → State → Prop}

/-- **`main`'s `ret b` block inside `W2` at the held frames**
(`retHeld_seg`'s `hW`): `blkW_heldTail` at `heldRN` of the block's
`bodyN2`, `HeldS` by `blkW_heldS` from the abort phase's facts (`hab`,
e.g. `blkW_abSt_subCdLR` at `scc_rt_main`'s return point, `posOff_mainRetS`),
`Ret0` from the frame's result cell (`retSlot_heldRN` at `hx`,
`retBlk_slot`), no write and no system call (the block covered, `hok`);
`SFacts` at the source start's control (`hS`). -/
theorem retHeld_hW (hp : ProgNoS ZBad p) {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    {ps : List (Scc.IR.Operand × XReg)} {ls : List Item} (hl : retLoads cx ps = .ok ls)
    {i : Expr → String → Nat → Option Nat} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr}
    {s : Spike.Lib.Form.SEnv} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {tp : UInt64} {lo hi : Int}
    (hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st pc (directives (ls ++ cx.leave ++ [ret])))
    (hok : okBlk lo hi (oF cx) (directives (ls ++ cx.leave ++ [ret])) = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F
      (Spike.Lib.A64.AllocG.dumN (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp)))
      (directives (ls ++ cx.leave ++ [ret])))
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F
      (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp))
      (directives (ls ++ cx.leave ++ [ret])))
    (hx : ∀ f, fs = [f] → ∃ t r, Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]) ∧
      ∃ k, rsOf cx r = some k ∧ R.Off k) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F
      (heldRN p fs ((bodyN2 p lbl lsize i cx fp ra c0 pc t s lits cs bufs).withTp tp))
      (directives (ls ++ cx.leave ++ [ret])) :=
  blkW_heldTail hp hS (fun _ _ h => h.1)
    (blkW_heldS hab (blkW_ret0_slot (retSlot_heldRN hx) fun σ k _ => retBlk_slot hf h1 hl _ _ k)
      (blkW_noWr' hcode hok hR hal hlo hhi) (blkW_noSys' hcode hok))

end Spike.Lib.LowerA64

/-- info: 'Spike.Lib.LowerA64.retBlk_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retBlk_slot

/-- info: 'Spike.Lib.LowerA64.retHeld_hW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.retHeld_hW

/-
**Per-construct segments** (AArch64), symbolic in the frame, the IR
registers' slots, the pc and the source.

The node invariant at a point of a lowered `Accepted0` body is `NJ`: the
source runs locally to a control at the point's term whose environment the
lowering's environment (`ofEnv`) represents, operands valued in the frame's
slots (`rsOf`), and the frame's saved `x29`/`x30` are the ghosts `fp`/`ra`
(`FrJ`).

- `NJ.atom`: `let x = a` emits nothing; the node invariant moves past it.
- `add_seg`: the checked `+`'s block (operand loads, `adds`, `b.cs`) lands
  at the pending-store node (`pendN`: the source has added, `x`'s slot
  valued by `x9`) or, on carry, at the overflow abort label with the source
  at the `+` about to overflow (`AbJ`: `OvfReady`, every bound word a number,
  the environment placed in the frame's cells, the free variables placed,
  its immediates the table `i`'s at the source's term, `ImmIn`).
- `store_seg`: the store `str x9, [sp, #off]` lands at the next node.
- `ret_seg`: `ret a` (the operand's load into `x0`, the frame's exit) lands
  at the saved return address with `x0` representing `a`'s word (`RetJ`).
-/
import Spike.Lib.LowerA64.Construct
import Spike.Lib.LowerNode
import Spike.Lib.LowerEnvImm
import Spike.Lib.A64Nodes
import Spike.Lib.A64Prologue
import Spike.Lib.Src
import Spike.Lib.Typed

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

/-! ## The frame's nodes (AArch64) -/

variable {p : Prog}

/-- **The saved frame pointer and return address** in their cells. -/
def FrJ (fp ra : BitVec 64) (sl : Int → BitVec 64) : Prop := sl (-16) = fp ∧ sl (-8) = ra

/-- The static offsets in a frame: `sp` at its base. -/
def oF (cx : FnCtx) : SO := ⟨-(cx.frame : Int), []⟩

/-- **A node of the body** at `pc`, term `t`, symbolic environment `s`;
the source control reached locally from the ghost `c0` (the function's
entry). -/
def bodyN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (c0 : Ctl)
    (pc : Int64) (t : Expr) (s : SEnv) : ND :=
  ⟨pc, oF cx, fun σ c => NJ p lbl (rsOf cx) t s σ.slot c ∧ FrJ fp ra σ.slot ∧ LocalRun p c0 c⟩

/-- **The pending store** of a checked `+`: the source has added, `x`'s
cell `k` valued by `x9`. -/
def pendN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx) (fp ra : BitVec 64) (c0 : Ctl)
    (pc : Int64) (t : Expr) (s : SEnv) (k : Int) : ND :=
  ⟨pc, oF cx, fun σ c => NJ p lbl (rsOf cx) t s (upd σ.slot k σ.regs.X9.toBitVec) c ∧ FrJ fp ra σ.slot ∧
    LocalRun p c0 c⟩

/-- **The source at the overflow abort label** (the handover to the abort
path): `AbSrc` in some symbolic environment whose immediates are the table
`i`'s at the source's term (`ImmIn`), the term satisfying `T` (in practice:
a point of the body's walk, `InWalk`), operands in the frame's cells, and
the saved pair. -/
def AbJ (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (lbl : WeakMem.AllocLabel → Option Nat) (cx : FnCtx)
    (fp ra : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  (∃ s, AbSrc lbl (rsOf cx) s σ.slot c ∧ ImmIn i s c.term ∧ T c.term) ∧ FrJ fp ra σ.slot

/-- **The overflow abort label**, the source at the `+` that carries. -/
def abortN (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (cx : FnCtx) (lab : Label → Int64) (fp ra : BitVec 64) (c0 : Ctl) : ND :=
  ⟨lab (cx.local "abort_overflow"), oF cx, fun σ c => AbJ i T lbl cx fp ra σ c ∧ LocalRun p c0 c⟩

/-- Different IR registers have different cells. -/
theorem rsOf_inj {cx : FnCtx} {r d : Scc.IR.Reg} {k : Int} (hr : rsOf cx r = some k) (hd : rsOf cx d = some k) :
    r = d := by
  unfold rsOf at hr hd
  cases h1 : cx.slotOff r with
  | error _ => simp [h1] at hr
  | ok o1 =>
    cases h2 : cx.slotOff d with
    | error _ => simp [h2] at hd
    | ok o2 =>
      simp only [h1, h2, Option.some.injEq] at hr hd
      exact slotOff_inj h1 (by rw [h2]; congr 1; omega)

theorem so_le_refl (o : SO) (h : o.regs = []) : SO.le o o = true := by
  obtain ⟨sp, regs⟩ := o
  cases h
  simp [SO.le]

/-- **The return's exit**: at the saved return address, the frame popped;
the source at `ret a` with `a`'s one word a number represented by `x0`,
`x29`/`x30` restored to the ghosts `fp`/`ra`. -/
def RetJ (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  ∃ a t w, c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, [w]) ∧ (∃ n, w.val = .num n) ∧
    ValRep lbl w.val σ.regs.X0.toBitVec.toNat ∧ σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra

/-- **The return's exit node.** -/
def retN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) : ND :=
  ⟨Int64.ofBitVec ra, ⟨0, []⟩, fun σ c => RetJ lbl fp ra σ c ∧ LocalRun p c0 c⟩

/-- **`ret` of one operand** is its load into `x0` and the epilogue. -/
theorem directives_leave {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (l : List Item) :
    directives (l ++ cx.leave ++ [ret]) = directives l ++ epi (Int64.ofInt cx.frame) := by
  have hs : cx.frame ≤ 32768 := by omega
  rw [leave_eq hf hs, addImm_small _ (by omega) (by omega)]
  simp [directives_append, directives, epi, RW.dir, AI.toDir, i64, ins, ret, rz, spW64, ofInt_sub_lit]

theorem frame_ge16 {cx : FnCtx} (hf : FrameOk cx) : 16 ≤ cx.frame := by
  have := le_align16 (8 * cx.slots.length + 16)
  unfold FrameOk at hf; omega

/-! ## A block's edge -/

/-- **A block's edge** at node `n` (`seg_ndW`'s obligations on the block's
closed form): the block is not empty and covered from the node's offsets
for cells in `[lo, hi)`, and from every state of the node's invariant its
abstract run (labels `lab`) lands at an internal node of `N` or an exit of
`E`, after a local run of the source. -/
def BlkEdge (p : Prog) (lab : Label → Int64) (lo hi : Int) (n : ND) (blk : List Directive) {ι κ : Sort _}
    (N : ι → ND) (E : κ → ND) : Prop :=
  blk ≠ [] ∧ okBlk lo hi n.o blk = true ∧
    ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧ Lands N E (arun lab blk ⟨n.pc, n.o, σ⟩) c'

/-- **A block's edge is one segment** (`seg_ndW`). -/
theorem BlkEdge.seg {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
    {lo hi : Int} {n : ND} {blk : List Directive} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}
    (h : BlkEdge p (_root_.Executable.labels exe).label lo hi n blk N E)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hW : BlkW W K exe endPc R F n blk) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  seg_ndW h.1 h.2.1 hF hR hal hlo hhi hcode hW h.2.2

section Segs

variable {lbl : WeakMem.AllocLabel → Option Nat} {c0 : Ctl} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isaLSE2} {K : State → State → Prop}

/-- **The checked `+`'s edge** (`add_seg`'s block, at the labels `lab`). -/
theorem add_edge {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i s (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e)) :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN p lbl cx fp ra c0 pc (.let_ x (.add a b) e) s)
      (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow")))
      (fun _ : Unit => pendN p lbl cx fp ra c0
        (pc + Int64.ofNat (4 * (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))).length))
        e ((x, .int, [.one (.reg d)]) :: s) (off - cx.frame))
      (fun _ : Unit => abortN i T p lbl cx lab fp ra c0) := by
  have hne : directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow")) ≠ [] := by
    simp [directives_append, directives_addChecked]
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx)
      (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [directives_append, directives_append, List.append_assoc, okBlk_getOp hf h1 h16 ha,
      okBlk_getOp hf h1 h16 hb]
    exact okBlk_addChecked _
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    add_block hf h1 h16 ha hb (cx.local "abort_overflow") lab pc σ
  by_cases hlt : va.toNat + vb.toNat < 2 ^ 64
  · refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0⟩⟩
    · show pc + _ = _
      rw [hpc]; simp [hlt]
    · show SO.le (oF cx) _ = true
      rw [hso]; exact so_le_refl _ rfl
    · show NJ p lbl (rsOf cx) e _ (upd _ (off - cx.frame) _) c
      rw [hsl, h9]
      refine hJ.add_ok hsa hsb hva hvb hlt (by simp [rsOf, hd]) ?_ ?_
      · intro q hq pl hpl o ho r k' hor hr' hk
        subst hk
        exact hfr q hq pl hpl o ho r hor (rsOf_inj hr' (by simp [rsOf, hd]))
      · rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hlt
    · show FrJ fp ra _
      rw [hsl]; exact hfj
  · obtain ⟨c1, hr, hab, ht⟩ := hJ.add_ovf_term hsa hsb hva hvb (by omega) htot
    refine ⟨c1, hr, .inr ⟨(), ?_, ?_, ?_, hc0.trans hr⟩⟩
    · show _ = _
      rw [hpc]; simp [hlt]; rfl
    · show SO.le (oF cx) _ = true
      rw [hso]; exact so_le_refl _ rfl
    · show AbJ i T lbl cx fp ra _ c1
      rw [AbJ, hsl]; exact ⟨⟨s, hab, ht ▸ himm, ht ▸ hT⟩, hfj⟩

/-- **The checked `+`'s block is one segment**: from the node at
`let x = a + b` (operands placed at `pa`, `pb`, loaded into `x9`, `x10`) to
the pending store after the block, or, on carry, to the overflow abort
label. `x`'s IR register `d` has a cell no other placed operand has. -/
theorem add_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : cx.getOp .X9 pa = .ok la) (hb : cx.getOp .X10 pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : cx.slotOff d = .ok off) {pc : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s pc (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))))
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i s (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e))
    (hW : BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc (.let_ x (.add a b) e) s)
      (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow")))) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc (.let_ x (.add a b) e) s))
      (Next exe endPc R F
        (fun _ : Unit => pendN p lbl cx fp ra c0
          (pc + Int64.ofNat (4 * (directives (la ++ lb ++ addChecked .X9 .X9 .X10 (cx.local "abort_overflow"))).length))
          e ((x, .int, [.one (.reg d)]) :: s) (off - cx.frame))
        (fun _ : Unit => abortN i T p lbl cx (_root_.Executable.labels exe).label fp ra c0)) :=
  (add_edge hf h1 h16 ha hb hd _ hsa hsb hfr htot himm hT).seg hF hR hal hlo hhi hcode hW

/-- **The store `str x9, [sp, #off]`'s edge** (`store_seg`'s block, at the
labels `lab`). -/
theorem store_edge {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {d : Scc.IR.Reg} {off : Int}
    (hd : cx.slotOff d = .ok off) {pc : Int64} (lab : Label → Int64) {fp ra : BitVec 64} {t : Expr} {s : SEnv} :
    BlkEdge p lab (-(cx.frame : Int)) 0 (pendN p lbl cx fp ra c0 pc t s (off - cx.frame))
      (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)])
      (fun _ : Unit => bodyN p lbl cx fp ra c0 (pc + 4) t s) (fun e : Empty => e.elim) := by
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hds : directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)] =
      [(.X9, Int64.ofInt off)].map fun q => spStr q.1 q.2 := rfl
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx)
      (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]) = true := by
    rw [hds]
    refine okBlk_spStrs (by simp [oF]; omega) fun q hq => ?_
    simp only [List.mem_singleton] at hq
    subst hq
    simp only [oF, ho, offOk, decide_eq_true_eq]
    omega
  refine ⟨by rw [hds]; simp, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0⟩⟩⟩
  all_goals simp only [hds, List.map_cons, List.map_nil, arun, List.foldl, pendN, oF] at *
  all_goals rw [dstep_spStr]
  · rfl
  · exact so_le_refl _ rfl
  · show NJ _ _ _ _ _ (upd σ.slot _ _) c
    rw [ho, show -(cx.frame : Int) + off = off - cx.frame by omega]
    exact hJ
  · obtain ⟨h16', h8'⟩ := hfj
    have hk1 : (-16 : Int) ≠ -(cx.frame : Int) + (Int64.ofInt off).toInt := by rw [ho]; omega
    have hk2 : (-8 : Int) ≠ -(cx.frame : Int) + (Int64.ofInt off).toInt := by rw [ho]; omega
    show upd σ.slot _ _ (-16) = fp ∧ upd σ.slot _ _ (-8) = ra
    simp only [upd_apply, hk1, hk2, ↓reduceIte, h16', h8', and_self]

/-- **The store `str x9, [sp, #off]` of a checked `+`'s result is one
segment**: from the pending store to the next node. -/
theorem store_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0) {d : Scc.IR.Reg}
    {off : Int}
    (hd : cx.slotOff d = .ok off) {pc : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s pc (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)]))
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {t : Expr} {s : SEnv}
    (hW : BlkW W K exe endPc R F (pendN p lbl cx fp ra c0 pc t s (off - cx.frame))
      (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 off, none⟩⟩)])) :
    SegW W K p lbl ms (At exe endPc R F (pendN p lbl cx fp ra c0 pc t s (off - cx.frame)))
      (At exe endPc R F (bodyN p lbl cx fp ra c0 (pc + 4) t s)) :=
  ((store_edge hf h1 h16 hd _).seg hF hR hal hlo hhi hcode hW).mono_post fun _ _ h =>
    h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-- **`ret a`'s edge** (`ret_seg`'s block, at the labels `lab`). -/
theorem ret_edge {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa : Scc.IR.Operand} {l : List Item} (ha : cx.getOp .X0 pa = .ok l) {pc : Int64} (lab : Label → Int64)
    {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty}
    (hsa : sevalAt s a = some (t, [.one pa])) :
    BlkEdge p lab (-(cx.frame : Int)) 0 (bodyN p lbl cx fp ra c0 pc (.ret a) s) (directives (l ++ cx.leave ++ [ret]))
      (fun _ : Unit => retN p lbl fp ra c0) (fun e : Empty => e.elim) := by
  have hge := frame_ge16 hf
  have hF64 : (Int64.ofInt cx.frame).toInt = cx.frame := toInt_ofInt_small (by omega) (by omega)
  have hds := directives_leave hf h1 l
  have hok : okBlk (-(cx.frame : Int)) 0 (oF cx) (directives (l ++ cx.leave ++ [ret])) = true := by
    show okBlk _ _ ⟨-(cx.frame : Int), []⟩ _ = true
    rw [hds, okBlk_getOp hf h1 h16 ha]
    have := okBlk_epi (F := Int64.ofInt cx.frame) (by rw [hF64]; omega) (by rw [hF64]; omega)
    rwa [hF64] at this
  refine ⟨by rw [hds]; simp [epi], hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  obtain ⟨c1, hr, hj, hnum⟩ := hJ
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  have hwn := hnum.evalAt hsa he
  obtain ⟨v, hv, hrun⟩ := arun_getOp hf h1 ha lab pc σ
  match ws, hw with
  | [w], ⟨⟨v', hv', hrep⟩, _⟩ =>
  rw [hv] at hv'
  cases hv'
  refine ⟨c1, hr, .inl ⟨(), ?_⟩⟩
  show Hit (retN p lbl fp ra c0) (arun _ (directives (l ++ cx.leave ++ [ret])) ⟨pc, ⟨-(cx.frame : Int), []⟩, σ⟩) c1
  rw [hds, arun_append, hrun]
  obtain ⟨hpc, hso, hsl, -, h29, h30, hr0⟩ := arun_epi lab
    (pc + Int64.ofNat (4 * (directives l).length)) (-(cx.frame : Int)) { σ with regs := σ.regs.setXReg .X0 v }
    (Int64.ofInt cx.frame)
  have h8 : (Int64.ofInt cx.frame - 8).toInt = cx.frame - 8 := by
    rw [Int64.toInt_sub, show (8 : Int64).toInt = 8 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  have h16' : (Int64.ofInt cx.frame - 16).toInt = cx.frame - 16 := by
    rw [Int64.toInt_sub, show (16 : Int64).toInt = 16 from rfl, bmod_sub (by omega) (by rw [hF64]; omega), hF64]
  rw [h8, show -(cx.frame : Int) + (cx.frame - 8) = -8 by omega] at hpc h30
  rw [h16', show -(cx.frame : Int) + (cx.frame - 16) = -16 by omega] at h29
  rw [hF64, show -(cx.frame : Int) + cx.frame = 0 by omega] at hso
  obtain ⟨hfp, hra⟩ := hfj
  obtain ⟨n, hn, -⟩ := hwn w (List.mem_singleton_self w)
  refine ⟨?_, ?_, ⟨a, t, w, hj.1, hj.2.1, he, ⟨n, hn⟩, ?_, ?_, ?_⟩, hc0.trans hr⟩
  · rw [hpc]; simp [retN, hra]
  · rw [hso]; rfl
  · have := hr0 .X0 (by decide) (by decide)
    simp only [Reg64s.getXReg_X0] at this
    rw [this]; simpa using hrep
  · rw [h29]; exact hfp
  · rw [h30]; exact hra

/-- **`ret a` is one segment**: from the node at `ret a` (`a` placed at
`pa`) through the load of `pa` into `x0` and the epilogue to the saved return
address. -/
theorem ret_seg {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    {pa : Scc.IR.Operand} {l : List Item} (ha : cx.getOp .X0 pa = .ok l) {pc : Int64}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc (directives (l ++ cx.leave ++ [ret])))
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int))
    (hhi : 0 ≤ R.hi) {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty}
    (hsa : sevalAt s a = some (t, [.one pa]))
    (hW : BlkW W K exe endPc R F (bodyN p lbl cx fp ra c0 pc (.ret a) s) (directives (l ++ cx.leave ++ [ret]))) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl cx fp ra c0 pc (.ret a) s))
      (At exe endPc R F (retN p lbl fp ra c0)) :=
  ((ret_edge hf h1 h16 ha _ hsa).seg hF hR hal hlo hhi hcode hW).mono_post fun _ _ h =>
    h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

end Segs

end Spike.Lib.LowerA64

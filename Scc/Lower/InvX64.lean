import Scc.Emit.X64
import Scc.Lower.SpecX64
import Scc.Lower.InvProg

/-!
# x86-64 frame slots of the emitter

The x86-64 twin of `Scc/Lower/InvA64.lean`: where the x86-64 emitter
(`Scc/Emit/X64.lean`) keeps a function's IR registers, and the code of the
constructs of an `Accepted0` body.

* `frameOf_slots`, `frameOf_size`: the frame of a function numbers its
  registers (first occurrences, `eraseDups`) from 0 and has
  `align16 (8 * n) + 8 * outWords` bytes below the frame record;
* `slotOff_find`, `slotOff_index`: a register numbered `k` is at
  `-8 * (k + 1)` from `%rbp`; `slotOff_inj`: different registers are at
  different offsets; `slotOff_bounds`: the offset is a negative multiple of
  8 and the slot lies in the register area, above the outgoing area;
* `ld_reg`, `ld_imm`, `st_eq`: loading an operand into a machine register
  and storing a machine register into an IR register are one `movq` each;
* `emitInst_addChk`: the code of `addChk d a b` (`movq` of the operands,
  `addq`, `jc` to the function's overflow abort, `movq` into `d`);
  `emitTerm_ret1`: the code of `ret [v]`;
* `lowerAll?_low_x64`, `lowerAll_accepted0_x64`: on an `Accepted0` program
  `lowerAll`'s IR is the runtime functions, then `func0 main r`
  (`Scc/Lower/InvProg.lean`).

Unlike AArch64 the code of a slot access does not depend on the frame size:
it is one `movq` with the displacement as an `int64` constant (`mem`), so no
frame bound is assumed here; whether the displacement encodes is the
printer's and the placement check's concern.

## Machine-block boundaries around `addChk`

`emitInst_addChk` emits the two operand loads, `addq %rcx, %rax`,
`jc .L<f>.ovf`, then the store of `%rax` into `d`'s slot. The conditional
jump ends a machine block; the store (its fall-through successor) begins
the next one.
-/

namespace Scc.Lower.InvX64

open Scc.Emit.X64
open Scc.IR

/-! ## The frame of a function -/

theorem frameOf_slots (areas : List (Sym × Nat)) (f : Func) :
    (frameOf areas f).slots =
      (f.params ++ f.blocks.flatMap fun b => b.insts.flatMap instRegs ++ termRegs b.term).eraseDups.zipIdx :=
  rfl

theorem frameOf_size (areas : List (Sym × Nat)) (f : Func) :
    (frameOf areas f).size =
      (8 * (frameOf areas f).slots.length + 15) / 16 * 16 + 8 * outWords areas f := by
  simp [frameOf]

/-! ## Slot offsets -/

/-- A register found among the slots, numbered `k`, is at `-8 * (k + 1)`;
the lookup does not change the emitter's state. -/
theorem slotOff_find {fr : Frame} {r r' : IR.Reg} {k : Nat}
    (h : fr.slots.find? (·.1 == r) = some (r', k)) (s : S) :
    fr.slotOff r s = .ok (-(8 * ((k : Int) + 1)), s) := by
  simp only [Frame.slotOff, h]; rfl

/-- What a successful `slotOff` says: the state is unchanged and the register
is numbered `k` among the slots. -/
theorem slotOff_index {fr : Frame} {r : IR.Reg} {s s' : S} {off : Int}
    (h : fr.slotOff r s = .ok (off, s')) :
    s' = s ∧ ∃ k, (r, k) ∈ fr.slots ∧ off = -(8 * ((k : Int) + 1)) := by
  cases hf : fr.slots.find? (·.1 == r) with
  | none =>
    simp only [Frame.slotOff, hf] at h
    cases h
  | some v =>
    obtain ⟨r', k⟩ := v
    rw [slotOff_find hf] at h
    cases h
    have hm := List.mem_of_find?_eq_some hf
    have he : (r' == r) = true := by simpa using List.find?_some hf
    simp only [beq_iff_eq] at he
    subst he
    exact ⟨rfl, k, hm, rfl⟩

theorem mem_zipIdx_get {l : List IR.Reg} {r : IR.Reg} {k : Nat} (h : (r, k) ∈ l.zipIdx) :
    ∃ hk : k < l.length, l[k] = r := by
  rw [List.mem_zipIdx_iff_getElem?] at h
  obtain ⟨hk, he⟩ := List.getElem?_eq_some_iff.mp h
  exact ⟨hk, he⟩

/-- Different registers of a function are at different offsets. -/
theorem slotOff_inj {areas : List (Sym × Nat)} {f : Func} {fr : Frame}
    (hfr : fr.slots = (frameOf areas f).slots) {r r' : IR.Reg} {s s₁ s₂ : S} {off : Int}
    (h : fr.slotOff r s = .ok (off, s₁)) (h' : fr.slotOff r' s = .ok (off, s₂)) : r = r' := by
  obtain ⟨-, k, hk, ho⟩ := slotOff_index h
  obtain ⟨-, k', hk', ho'⟩ := slotOff_index h'
  have : k = k' := by omega
  subst this
  rw [hfr, frameOf_slots] at hk hk'
  obtain ⟨_, e1⟩ := mem_zipIdx_get hk
  obtain ⟨_, e2⟩ := mem_zipIdx_get hk'
  exact e1.symm.trans e2

/-- **Slot bounds**: a negative multiple of 8, within the `8 * n` bytes of
register slots below the frame record, above the outgoing area. -/
theorem slotOff_bounds {areas : List (Sym × Nat)} {f : Func} {fr : Frame}
    (hfr : fr.slots = (frameOf areas f).slots) (hsz : fr.size = (frameOf areas f).size)
    {r : IR.Reg} {s s' : S} {off : Int} (h : fr.slotOff r s = .ok (off, s')) :
    off ≤ -8 ∧ off % 8 = 0 ∧ -off ≤ 8 * (fr.slots.length : Int) ∧
      8 * (fr.slots.length : Int) + 8 * (outWords areas f : Int) ≤ fr.size := by
  obtain ⟨-, k, hk, rfl⟩ := slotOff_index h
  have hlt : k < fr.slots.length := by
    rw [hfr, frameOf_slots] at hk ⊢
    obtain ⟨hk', -⟩ := mem_zipIdx_get hk
    rw [List.length_zipIdx]; exact hk'
  have hs := frameOf_size areas f
  rw [← hfr, ← hsz] at hs
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## Loads and stores -/

/-- Loading IR register `x` into `r` is one `movq off(%rbp), %r`. -/
theorem ld_reg {fr : Frame} {x : IR.Reg} {s : S} {off : Int} (h : fr.slotOff x s = .ok (off, s))
    (r : Reg64) :
    ld fr (.reg x) r s =
      .ok ((), { s with out := .d (i64 (.mov (xr r) (om (mem .rbp off)))) :: s.out }) := by
  simp only [ld, Frame.slot, bind, StateT.bind, h, pure, StateT.pure, Except.pure, Except.bind]
  rfl

/-- Loading an immediate is one `movq`/`movabsq`. -/
theorem ld_imm (fr : Frame) (v : UInt64) (r : Reg64) (s : S) :
    ld fr (.imm v) r s =
      .ok ((), { s with out := .d (i64 (.mov (xr r) (.imm (.int64 v.toInt64)))) :: s.out }) :=
  rfl

/-- Storing `r` into IR register `d` is one `movq %r, off(%rbp)`. -/
theorem st_eq {fr : Frame} {d : IR.Reg} {s : S} {off : Int} (h : fr.slotOff d s = .ok (off, s))
    (r : Reg64) :
    st fr r d s =
      .ok ((), { s with out := .d (i64 (.mov (xm (mem .rbp off)) (or_ r))) :: s.out }) := by
  simp only [st, Frame.slot, bind, StateT.bind, h, pure, StateT.pure, Except.pure, Except.bind]
  rfl

/-! ## The code of the constructs -/

/-- **The code of `addChk d a b`**: `a` into `%rax`, `b` into `%rcx`,
`addq %rcx, %rax`, `jc` to the function's overflow abort, `%rax` into
`d`. -/
theorem emitInst_addChk (fr : Frame) (sm : Option StackMap.Entry) (d : IR.Reg)
    (a b : IR.Operand) :
    emitInst fr sm (.addChk d a b) = (do
      ld fr a .rax; ld fr b .rcx
      ins (i64 (.add (xr .rax) (or_ .rcx)))
      ins (i64 (.jcc .c (labelOf fr.fn "ovf")))
      st fr .rax d) := rfl

/-- **The code of `ret [v]`**: `v` into `%rax`, the epilogue, `ret`. -/
theorem emitTerm_ret1 (fr : Frame) (v : IR.Operand) :
    emitTerm fr (.ret [v]) = (do ld fr v .rax; epilogue; ins (i64 .ret)) := by
  have ha : retRegs = .rax :: retRegs.tail := rfl
  simp only [emitTerm, loadArgs]
  rw [ha]
  simp [forIn, ForIn.forIn, retRegs]

/-! ## `lowerAll`'s IR -/

section
open CoreTerm Scc.Lower Scc.Lower.Inv

/-- `lowerAll?`'s IR (x86-64) is `lowerIR`'s. -/
theorem lowerAll?_low_x64 {cfg : Config} {p : Prog} {e : Scc.Lower.X64.Emitted}
    (h : Scc.Lower.X64.lowerAll? cfg p = .ok e) : lowerIR cfg p = .ok e.low := by
  unfold Scc.Lower.X64.lowerAll? at h
  cases hl : lowerIR cfg p with
  | error m => simp only [hl, bind, Except.bind] at h; cases h
  | ok l =>
    simp only [hl, bind, Except.bind, Scc.Lower.X64.emitAll] at h
    cases hi : Scc.Emit.X64.emitItemsMaps l.ir with
    | error m => simp only [hi] at h; cases h
    | ok v => simp only [hi, pure, Except.pure] at h; cases h; rfl

/-- **`lowerAll`'s IR on an `Accepted0` program** (x86-64), when the
lowering and emission succeed: the runtime functions, then `func0 main r`. -/
theorem lowerAll_accepted0_x64 (cfg : Config) {d : Decl} (hd : Accepted0 [d] = true)
    {e : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.lowerAll? cfg [d] = .ok e) :
    ∃ r rt, lower0 [(d.arg, .unit, [])] 0 d.body = some r ∧
      rtFuncs cfg.layout ⟨.unit, true⟩ 0 = .ok rt ∧
      (Scc.Lower.X64.lowerAll cfg [d]).low.ir = progOf cfg.layout rt [func0 (Names.user "main") r] := by
  obtain ⟨r, rt, hr, hrt, hir, -⟩ := lowerIR_accepted0 cfg hd (lowerAll?_low_x64 h)
  refine ⟨r, rt, hr, hrt, ?_⟩
  simp only [Scc.Lower.X64.lowerAll, h]
  exact hir

end

end Scc.Lower.InvX64

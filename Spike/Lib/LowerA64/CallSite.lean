/-
**Call-site helpers** (AArch64): the straight-block pieces a plain call's
segments (`Spike/Lib/LowerA64/CallC.lean`) run at the caller's frame.

- `seg_blk1`: a straight block's segment to one node;
- `arun_spStr1`: a slot store's run;
- `ofs_eq`, `ofs_le`, `frJ_upd`: a register's cell from the frame's base,
  below the saved pair;
- `getOp_ne_nil`: an operand's load is never empty.

The callee's interface at a call (`CallG`, `calleeN`, `ArgV`, `CalleeF`) is
in `Spike/Lib/LowerA64/CallIface.lean`.
-/
import Spike.Lib.LowerA64.BodyC
import Spike.Lib.A64CallSA
import Spike.Lib.Rt.A64Main
import Spike.Lib.LowerA64.CallIface

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.A64.Flow.Ret0 (OwnAt StOk LdOk CallerCells rAddr_x10 getRegOrZr_x9 ownLdr_ndW ownStr_ndW setXReg_TPIDR)
open Scc.Lower.Inv (regName labName)

set_option linter.unusedSimpArgs false

section Edges

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-- **A straight block's segment to one node**: `BlkEdge.seg` with one
internal node and no exit. -/
theorem seg_blk1 {ms0 : MemSide isaLSE2} {W₀ : Frag isaLSE2} {lo : Int} {n n' : ND} {blk : List Directive}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : 0 ≤ R.hi)
    (hcode : CdOf exe endPc n.pc blk) (hW : BlkW W₀ K exe endPc R F n blk)
    (hne : blk ≠ []) (hok : okBlk lo 0 n.o blk = true)
    (h : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Hit n' (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c') :
    SegW W₀ K p lbl ms0 (At exe endPc R F n) (At exe endPc R F n') :=
  (BlkEdge.seg (N := fun _ : Unit => n') (E := fun e : Empty => e.elim)
    ⟨hne, hok, fun σ c hJ => let ⟨c', hr, hh⟩ := h σ c hJ; ⟨c', hr, .inl ⟨(), hh⟩⟩⟩
    hF hR hal hlo hhi hcode hW).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

theorem four_eq : (4 : Int64) = Int64.ofNat 4 := rfl

/-- **A store `str Xr, [sp, #o]`'s run.** -/
theorem arun_spStr1 (lab : Label → Int64) (pc : Int64) (sp : Int) (σ : AS) (r : XReg) (o : Int64) :
    arun lab [spStr r o] ⟨pc, ⟨sp, []⟩, σ⟩ =
      ⟨pc + Int64.ofNat 4, ⟨sp, []⟩, { σ with slot := upd σ.slot (sp + o.toInt) (σ.regs.getXReg r).toBitVec }⟩ := by
  simp only [arun, List.foldl, dstep_spStr, four_eq]

/-- A register's cell from the frame's base. -/
theorem ofs_eq {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {r : Scc.IR.Reg} {o : Int} (ho : cx.slotOff r = .ok o) :
    -(cx.frame : Int) + (Int64.ofInt o).toInt = o - cx.frame := by
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho
  rw [toInt_ofInt_small (by omega) (by omega)]; omega

theorem ofs_le {cx : FnCtx} (hf : FrameOk cx) {r : Scc.IR.Reg} {o : Int} (ho : cx.slotOff r = .ok o) :
    o - (cx.frame : Int) ≤ -24 := by
  obtain ⟨h0, h8, hle⟩ := slotOff_bounds hf ho; omega

/-- A write below the saved pair keeps it. -/
theorem frJ_upd {fp ra : BitVec 64} {sl : Int → BitVec 64} (h : FrJ fp ra sl) {k : Int} (hk : k ≤ -24)
    (v : BitVec 64) : FrJ fp ra (upd sl k v) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩ <;> rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))] <;> assumption

/-- An operand's load is never empty. -/
theorem getOp_ne_nil {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) {t : XReg} {a : Scc.IR.Operand}
    {l : List Item} (ha : cx.getOp t a = .ok l) : directives l ≠ [] := by
  rcases getOp_cases hf h1 ha with ⟨r, off, rfl, hs, hl⟩ | ⟨v, rfl, rfl⟩
  · rw [hl]; simp
  · rw [directives_movImm]; generalize nzHw _ 0 = hs; cases hs <;> simp [movDs]

end Edges

end Spike.Lib.LowerA64
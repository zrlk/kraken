/-
**A call of `print` from any caller node** (AArch64): `callBlock`'s
`.print` case (`Scc/Lower/Term.lean`), its argument block
(`Spike/Lib/LowerA64/PrintArgs.lean`) and `bl scc_rt_print`, composed with
`print_call_segW` (`Spike/Lib/A64PrintCall.lean`) at the call site.

- `blPrintD`, `arun_bl`, `okBlk_bl`: the `bl`'s directive, its run (to `print`'s
  label, `x30` the address after it) and coverage.
- `opdNat`: an operand's value at a state's slots; `callSt`: the state at
  `print`'s entry after the block and `bl`; `callN`: the call node.
- `callSt_facts`: `x0`, `x1` (`min(n, 8·m)`), `x30` at `print`'s entry and
  the slots kept; `opdVal_kept`, `printN_of_x1`.
- `print_block_segW`: the block with its call and `print`'s run are one
  segment inside `W`, from a caller node at `pc` with the body's offsets
  (`oF c`); `print_call_segW`'s count premise is discharged from the block.
-/
import Spike.Lib.LowerA64.PrintArgs
import Spike.Lib.A64PrintCall

namespace Spike.Lib.LowerA64

open CoreLang
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.Form (opdVal)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS)
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.PrintA (PrintAW EmitW)

set_option linter.unusedSimpArgs false

/-- `bl scc_rt_print`'s directive. -/
abbrev blPrintD : List Directive := directives [call Scc.Lower.Names.print]

theorem blPrintD_eq : blPrintD = [.instr ⟨.W64, .BL (.label "scc_rt_print")⟩] := rfl

/-- **`bl scc_rt_print`'s run**: to `print`'s label, `x30` the address after it. -/
theorem arun_bl (lab : Label → Int64) (pc : Int64) (c : FnCtx) (σ : AS) :
    arun lab blPrintD ⟨pc, oF c, σ⟩ =
      ⟨lab "scc_rt_print", oF c, { σ with regs := σ.regs.setRegOrZr (.low (.reg .X30) .W64) (pc + 4).toBitVec }⟩ := by
  simp [blPrintD_eq, arun, A64.Flow.dstep, A64.Flow.classify, AI.step, AI.tgt, AI.so, oF, SO.kill, rm, int64_ofInt_toInt]
  rw [Ret0.ofInt_bmod, BitVec.ofInt_add, int64_ofInt_toInt]
  rfl

theorem okBlk_bl {lo hi sp : Int} : okBlk lo hi ⟨sp, []⟩ blPrintD = true := rfl


/-- An operand's value at a state's slots, as a number (`0` when not
placed). -/
def opdNat (c : FnCtx) (σ : AS) (o : Scc.IR.Operand) : Nat := (opdVal (rsOf c) σ.slot o).getD 0

/-- **The state at `print`'s entry**: after the argument block `L` and `bl`
from `σ0` at `pc`. -/
def callSt (lab : Label → Int64) (c : FnCtx) (pc : Int64) (L : List Item) (σ0 : AS) : AS :=
  (arun lab (directives L ++ blPrintD) ⟨pc, oF c, σ0⟩).σ

/-- **The call node** after the argument block `L` at `pc` from the
invariant `J`: `print`'s label, the body's offsets. -/
def callN (lab : Label → Int64) (c : FnCtx) (pc : Int64) (L : List Item) (J : AS → Ctl → Prop) : ND :=
  ⟨lab "scc_rt_print", oF c, fun σ c' => ∃ σ0, J σ0 c' ∧ σ = callSt lab c pc L σ0⟩

section Facts

variable {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095)

include hf h1 in
/-- **The block with its call runs to `print`'s entry**, with `x0` the
buffer's address `b + lo(o)`, `x1` the count `min(n, 8·m)` (unsigned,
wrapping), `x30` the address after the `bl`, every slot but the block's
fresh registers' kept. -/
theorem callSt_facts {i1 i2 i3 i4 : Nat} {lo s cap kk : Scc.IR.Reg} {b o m n : Scc.IR.Operand}
    {l1 l2 l3 l4 l5 : List Item}
    (c1 : c.inst i1 (.ext false .w32 lo o) = .ok l1) (c2 : c.inst i2 (.bin .add s b (.reg lo)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5)
    (hb : ∀ r, b = .reg r → r ≠ lo) (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s)
    (hn : ∀ r, n = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap) (hsc : s ≠ cap) (hsk : s ≠ kk)
    (lab : Label → Int64) (pc : Int64) (σ0 : AS) :
    ∃ vb vo vm vn : BitVec 64, opdVal (rsOf c) σ0.slot b = some vb.toNat ∧
      opdVal (rsOf c) σ0.slot o = some vo.toNat ∧ opdVal (rsOf c) σ0.slot m = some vm.toNat ∧
      opdVal (rsOf c) σ0.slot n = some vn.toNat ∧
      arun lab (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD) ⟨pc, oF c, σ0⟩ =
        ⟨lab "scc_rt_print", oF c, callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0⟩ ∧
      (callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0).regs.X0.toBitVec = vb + (vo.take 32).setWidth 64 ∧
      (callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0).regs.X1.toBitVec =
        (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64) ∧
      (callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0).regs.X30.toBitVec =
        (pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length) + 4).toBitVec ∧
      ∀ j, (∀ q, rsOf c q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk) →
        (callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0).slot j = σ0.slot j := by
  obtain ⟨vb, vo, vm, vn, hvb, hvo, hvm, hvn, rg, st, sl, hx0, hx1, e, hsl⟩ :=
    printArgs_run hf h1 c1 c2 c3 c4 c5 hb hm hn hsc hsk lab pc σ0
  have he : arun lab (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD) ⟨pc, oF c, σ0⟩ =
      ⟨lab "scc_rt_print", oF c, ⟨rg.setRegOrZr (.low (.reg .X30) .W64)
        (pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length) + 4).toBitVec, st, sl⟩⟩ := by
    rw [arun_append, e, arun_bl]
  have hs : callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0 = ⟨rg.setRegOrZr (.low (.reg .X30) .W64)
        (pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length) + 4).toBitVec, st, sl⟩ := by
    rw [callSt, he]
  refine ⟨vb, vo, vm, vn, hvb, hvo, hvm, hvn, by rw [he, ← hs], ?_, ?_, ?_, ?_⟩
  · rw [hs, ← hx0]; simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  · rw [hs, ← hx1]; simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  · rw [hs]; simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  · intro j hj; rw [hs]; exact hsl j hj

/-- An operand off the written registers reads the same at slots kept off
them. -/
theorem opdVal_kept {lo s cap kk : Scc.IR.Reg} {sl sl' : Int → BitVec 64} {a : Scc.IR.Operand}
    (ha : ∀ r, a = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap ∧ r ≠ kk)
    (hsl : ∀ j, (∀ q, rsOf c q = some j → q ≠ lo ∧ q ≠ s ∧ q ≠ cap ∧ q ≠ kk) → sl' j = sl j) :
    opdVal (rsOf c) sl' a = opdVal (rsOf c) sl a := by
  cases a with
  | imm => rfl
  | reg r =>
    simp only [opdVal]
    cases hr : rsOf c r with
    | none => rfl
    | some j =>
      simp only [Option.map_some]
      rw [hsl j fun q hq => ?_]
      have := rsOf_inj hq hr
      subst this
      exact ha q rfl

/-- **The count passed to `print`** is `printN` of the operands' values at
the call state, when `8·m` is below `2^63`. -/
theorem printN_of_x1 {vn vm : BitVec 64} (hm : 8 * vm.toNat < 2 ^ 63) :
    (if vn.toNat < (vm * 8#64).toNat then vn else vm * 8#64).toNat = printN vn.toNat vm.toNat := by
  have h8 : (vm * 8#64).toNat = vm.toNat * 8 := by
    rw [BitVec.toNat_mul]; simp only [BitVec.toNat_ofNat]; omega
  unfold printN
  split <;> omega

end Facts

section Seg

variable {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **`print`'s argument block and its call are one segment inside `W`**,
from any caller node at `pc` (the body's offsets, invariant `J`) whose code
there is `callBlock`'s `.print` case (`c1`…`c5`, then `bl scc_rt_print`):
the block (`printArgs_run`, `okBlk_printArgs`) to the call node `nC`
(`callN`), then `print_call_segW` with `print`'s count and slice length the
operands `n`, `m`'s values at the call state (`opdNat`; the count's
`printN` is discharged from the block's `min(n, 8·m)`). The caller gives
the block's states inside `W` (`hWb`), its code (`hcode`), and
`print_call_segW`'s remaining premises at `nC`. -/
theorem print_block_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    {c : FnCtx} (hf : FrameOk c) (h1 : c.frame ≤ 4095) (h16 : c.frame % 16 = 0)
    {i1 i2 i3 i4 : Nat} {lo s cap kk : Scc.IR.Reg} {b o m n : Scc.IR.Operand} {l1 l2 l3 l4 l5 : List Item}
    (c1 : c.inst i1 (.ext false .w32 lo o) = .ok l1) (c2 : c.inst i2 (.bin .add s b (.reg lo)) = .ok l2)
    (c3 : c.inst i3 (.bin .mul cap m (Scc.Lower.imm 8)) = .ok l3)
    (c4 : c.inst i4 (.select .ult kk n (.reg cap) n (.reg cap)) = .ok l4)
    (c5 : c.getArgs [.reg s, .reg kk] = .ok l5)
    (hb : ∀ r, b = .reg r → r ≠ lo) (hm : ∀ r, m = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap ∧ r ≠ kk)
    (hn : ∀ r, n = .reg r → r ≠ lo ∧ r ≠ s ∧ r ≠ cap ∧ r ≠ kk) (hsc : s ≠ cap) (hsk : s ≠ kk)
    {pc : Int64} {J : AS → Ctl → Prop} {nC : ND}
    (hnC : nC = callN (_root_.Executable.labels exe).label c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) J)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s pc (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD))
    (hWb : BlkW W K exe endPc R F ⟨pc, oF c, J⟩ (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD))
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop} {pw wn : AS → TermRun.Word}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -(c.frame : Int) + -48) (hhi : 0 ≤ R.hi)
    -- the call site
    (hP0 : ∀ σ c', nC.J σ c' → PrintC (pw σ) (wn σ) (opdNat c σ n) (opdNat c σ m) 0 c')
    (hm8 : ∀ σ c', nC.J σ c' → 8 * opdNat c σ m < 2 ^ 63)
    (hW : ∀ σC c', nC.J σC c' → PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn (opdNat c · n) (opdNat c · m) σC)
      (pcS pw wn (opdNat c · n) (opdNat c · m) σC) W K exe endPc (pR nC.o.sp R) (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c', nC.J σC c' → ∀ (F' : MachineData → Prop) s c'', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn (opdNat c · n) (opdNat c · m))
        (pcS pw wn (opdNat c · n) (opdNat c · m)) σC .svc) s c'' →
      W s c'' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c', nC.J σC c' → ∀ (F' : MachineData → Prop) s c'', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn (opdNat c · n) (opdNat c · m))
        (pcS pw wn (opdNat c · n) (opdNat c · m)) σC .svc) s c'' →
      ∀ k j, k + j < printN (opdNat c σC n) (opdNat c σC m) →
      BO s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j)
        (loadC (pw σC) (wn σC) (opdNat c σC m) (k + j))
        (fun c0 => ∃ mw b, c0 = nextC (pw σC) (wn σC) (opdNat c σC m) (k + j) mw b))
    (hwe : ∀ σC c', nC.J σC c' → ∀ (F' : MachineData → Prop) s c'', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn (opdNat c · n) (opdNat c · m))
        (pcS pw wn (opdNat c · n) (opdNat c · m)) σC .svc) s c'' →
      ∀ k c1, PrintC (pw σC) (wn σC) (opdNat c σC n) (opdNat c σC m) k c1 → WE s c1)
    -- where the return and the abort land
    (hret : ∀ σC c' σR c'', nC.J σC c' →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (opdNat c σC n) (opdNat c σC m) (printN (opdNat c σC n) (opdNat c σC m)) c'' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c'')
    (habort : ∀ σC c' σR c'' k, nC.J σC c' → σR.regs.X0 = 4 →
      PrintC (pw σC) (wn σC) (opdNat c σC n) (opdNat c σC m) k c'' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨(_root_.Executable.labels exe).label "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, σR⟩ c'') :
    SegW W K p lbl ms (At exe endPc R F ⟨pc, oF c, J⟩) (Next exe endPc R F N E) := by
  let lab := (_root_.Executable.labels exe).label
  have hfr : 16 ≤ c.frame := by
    have := hf; unfold FrameOk at this; simp only [align16] at this; omega
  have hosp : nC.o.sp = -(c.frame : Int) := by rw [hnC]; rfl
  -- the count
  have hN : ∀ σ c', nC.J σ c' → σ.regs.X1.toBitVec.toNat = printN (opdNat c σ n) (opdNat c σ m) := by
    intro σ c' hJ
    have hJ' := hJ
    rw [hnC] at hJ'
    obtain ⟨σ0, -, rfl⟩ := hJ'
    obtain ⟨vb, vo, vm, vn, -, -, hvm, hvn, -, -, hx1, -, hsl⟩ :=
      callSt_facts hf h1 c1 c2 c3 c4 c5 hb (fun r h => ⟨(hm r h).1, (hm r h).2.1⟩)
        (fun r h => ⟨(hn r h).1, (hn r h).2.1, (hn r h).2.2.1⟩) hsc hsk lab pc σ0
    have en : opdNat c (callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0) n = vn.toNat := by
      simp only [opdNat]; rw [opdVal_kept hn hsl, hvn]; rfl
    have em : opdNat c (callSt lab c pc (l1 ++ l2 ++ l3 ++ l4 ++ l5) σ0) m = vm.toNat := by
      simp only [opdNat]; rw [opdVal_kept hm hsl, hvm]; rfl
    have h8 := hm8 _ c' hJ
    rw [em] at h8
    rw [en, em, hx1, printN_of_x1 h8]
  refine SegW.seq (Q := At exe endPc R F nC) ?_
    (print_call_segW hp hend hprog hF hR hal (by rw [hosp]; omega) (by rw [hosp]; omega)
      (by rw [hosp]; omega) (by rw [hnC]; rfl) hP0 hN hm8 hW hd hE hK hcl
      (fun σC c hJ F' _ => hWs σC c hJ F') (fun σC c hJ F' _ => hlb σC c hJ F')
      (fun σC c hJ F' _ => hwe σC c hJ F') hret habort)
  -- the block
  have hok : okBlk (-(c.frame : Int)) 0 (oF c) (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD) = true := by
    simp only [oF, directives_append, List.append_assoc]
    rw [okBlk_inst_ext32 hf h1 h16 c1, okBlk_inst_bin hf h1 h16 (.inl rfl) c2,
      okBlk_inst_bin hf h1 h16 (.inr rfl) c3, okBlk_inst_select hf h1 h16 c4, okBlk_args2 hf h1 h16 c5]
    rfl
  refine (seg_ndW (N := fun _ : Unit => nC) (E := fun e : Empty => e.elim) (by simp [blPrintD_eq]) hok hF hR hal
    (by omega) hhi hcode hWb fun σ c' hJ => ⟨c', .refl c', .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  obtain ⟨-, -, -, -, -, -, -, -, he, -⟩ :=
    callSt_facts hf h1 c1 c2 c3 c4 c5 hb (fun r h => ⟨(hm r h).1, (hm r h).2.1⟩)
      (fun r h => ⟨(hn r h).1, (hn r h).2.1, (hn r h).2.2.1⟩) hsc hsk lab pc σ
  subst hnC
  refine ⟨?_, ?_, σ, hJ, ?_⟩
  · show lab "scc_rt_print" = (arun lab _ _).pc
    rw [he]
  · show SO.le (oF c) (arun lab _ _).so = true
    rw [he]; simp [SO.le, oF]
  · show (arun lab _ _).σ = _
    rfl

end Seg

end Spike.Lib.LowerA64

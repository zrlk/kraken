/-
**A function's stack-checked prologue and the `exit_group` tail** (AArch64),
for any frame size, limit offset and labels.

- **The prologue** (`Scc/Emit/A64.lean`, `emitFn`, `f.checkStack`): the
  emitter's stack check `sub x9, sp, #Z; mrs x10, tpidr_el0` (`chkHead`),
  the limit load `ldr x10, [x10, #lim]` (`ldrDir`), `subs xzr, x9, x10;
  b.lo L` (`chkBr`), then the frame's setup `add sp, x9, #0; str x29, [sp,
  #Z-16]; str x30, [sp, #Z-8]; add x29, sp, #Z-16` (`frSetup`) and the
  parameters' stores `str xi, [sp, #o]` (`frameSet`). Each block's closed
  form (`chkHead_run`, `chkBr_run`, `frameSet_run`) and coverage (`_ok`) is
  proved for a symbolic frame size; `prologue_seg` makes the four nodes one
  segment from the function's entry (`sp` at offset 0) to the body's first
  node (`sp` at `-Z`, offsets `oFr Z`), the branch to `L` not taken: for
  every limit `v` the runtime memory may hold at `[tpidr_el0, #lim]`
  (`tcbA`, through `rtld_nd`) the obligation gives `v ≤ sp - Z`.
- **The `exit_group` tail** (`scc_rt_main`'s last block): `str x0, [sp,
  #k]; ldr x0, [sp, #k]; movz x8, #94` (`exitTail`, `x0` kept, `x8 = 94`:
  `exitTail_run`) and `svc #0`; `exitTail_seg` is a segment to any exit
  (`exit_nd`: the call does not return).
-/
import Spike.Lib.A64Ret
import Spike.Lib.A64AllocNodes
import Spike.Lib.A64Dead
open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

namespace Spike.Lib.A64.Flow

set_option linter.unusedSimpArgs false

/-- The stack check's head: `sub x9, sp, #Z; mrs x10, tpidr_el0`. -/
def chkHead (F : Int64) : List Directive :=
  [.instr ⟨.W64, .SUB_e (.low (.reg .X9) .W64) (.low .SP .W64) (.imm ⟨.int64 F, .S0⟩)⟩,
   .instr ⟨.W64, .MRS (.low (.reg .X10) .W64) .TPIDR_EL0⟩]

/-- The stack check's branch: `subs xzr, x9, x10; b.lo L`. -/
def chkBr (L : Label) : List Directive :=
  [.instr ⟨.W64, .SUBS_s (.low .XZR .W64) (.low (.reg .X9) .W64) ⟨.low (.reg .X10) .W64, 0, .LSL⟩⟩,
   .instr ⟨.W64, .B_cond .CC (.label L)⟩]

/-- `str Xr, [sp, #o]`. -/
def spStr (r : XReg) (o : Int64) : Directive :=
  .instr ⟨.W64, .STR (.low (.reg r) .W64) ⟨.low .SP .W64, .imm ⟨.int64 o, none⟩⟩⟩

/-- The frame's setup: `add sp, x9, #0; str x29, [sp, #Z-16]; str x30, [sp, #Z-8];
add x29, sp, #Z-16`. -/
def frSetup (F : Int64) : List Directive :=
  [.instr ⟨.W64, .ADD_e (.low .SP .W64) (.low (.reg .X9) .W64) (.imm ⟨.int64 0, .S0⟩)⟩,
   spStr .X29 (F - 16), spStr .X30 (F - 8),
   .instr ⟨.W64, .ADD_e (.low (.reg .X29) .W64) (.low .SP .W64) (.imm ⟨.int64 (F - 16), .S0⟩)⟩]

/-- The frame's setup and the parameters' stores `str r, [sp, #o]` for `(r, o) ∈ ps`. -/
def frameSet (F : Int64) (ps : List (XReg × Int64)) : List Directive :=
  frSetup F ++ ps.map fun p => spStr p.1 p.2

/-- The registers after the check's head: `x9 = sp - Z`, `x10` the thread pointer. -/
def chkRegs (F : Int64) (r : Reg64s) : Reg64s :=
  (r.setXReg .X9 (r.SP.toBitVec - F.toBitVec)).setXReg .X10 r.TPIDR_EL0.toBitVec

/-- The static offsets during the check: `sp` at 0, `x9` the new `sp`. -/
def oChk (F : Int64) : SO := ⟨0, [(.X9, -F.toInt)]⟩
/-- The static offsets in the frame: `sp` at `-Z`, `x29` at the saved pair. -/
def oFr (F : Int64) : SO := ⟨-F.toInt, [(.X29, -16), (.X9, -F.toInt)]⟩

/-- The check's head is covered. -/
theorem chkHead_ok (lo hi : Int) (F : Int64) : okBlk lo hi ⟨0, []⟩ (chkHead F) = true := by
  simp [chkHead, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write,
    SO.kill, rm, SO.set, SO.get]

/-- **The check's head**, in closed form. -/
theorem chkHead_run (lab : Label → Int64) (pc : Int64) (σ : AS) (F : Int64) :
    arun lab (chkHead F) ⟨pc, ⟨0, []⟩, σ⟩ = ⟨pc + 4 + 4, oChk F, { σ with regs := chkRegs F σ.regs }⟩ := by
  simp [chkHead, oChk, chkRegs, arun, dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regRes,
    Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp,
    SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst]
  rfl

/-- The check's branch is covered. -/
theorem chkBr_ok (lo hi : Int) (F : Int64) (L : Label) : okBlk lo hi (oChk F) (chkBr L) = true := by
  simp [chkBr, oChk, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write,
    SO.kill, rm, SO.set, SO.get]

/-- **The check's branch**: to `L` iff `x10` is above `x9` (unsigned); the
registers and cells unchanged. -/
theorem chkBr_run (lab : Label → Int64) (pc : Int64) (σ : AS) (F : Int64) (L : Label) :
    (arun lab (chkBr L) ⟨pc, oChk F, σ⟩).pc =
      (if σ.regs.X10.toNat ≤ σ.regs.X9.toNat then pc + 4 + 4 else lab L) ∧
    (arun lab (chkBr L) ⟨pc, oChk F, σ⟩).so = oChk F ∧
    (arun lab (chkBr L) ⟨pc, oChk F, σ⟩).σ.regs = σ.regs ∧
    (arun lab (chkBr L) ⟨pc, oChk F, σ⟩).σ.slot = σ.slot := by
  simp [chkBr, oChk, arun, dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, soReg, regRes,
    Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64, ConstExpr.interp,
    SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst]
  have := σ.regs.X9.toNat_lt; have := σ.regs.X10.toNat_lt
  by_cases h : σ.regs.X10.toNat ≤ σ.regs.X9.toNat
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- A store into the frame: the cell at `sp + o` gets `Xr`. -/
theorem dstep_spStr (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) (r : XReg) (n : Int64) :
    dstep lab ⟨pc, o, σ⟩ (spStr r n) =
      ⟨pc + 4, o, { σ with slot := upd σ.slot (o.sp + n.toInt) (σ.regs.getXReg r).toBitVec }⟩ := by
  simp [spStr, dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, Reg64s.getRegOrZr_X]

/-- The cells after the stores `ps` of the registers `regs`, `sp` at offset `sp`. -/
def stSlots (sp : Int) (regs : Reg64s) : List (XReg × Int64) → (Int → BitVec 64) → Int → BitVec 64
  | [], sl => sl
  | p :: ps, sl => stSlots sp regs ps (upd sl (sp + p.2.toInt) (regs.getXReg p.1).toBitVec)

/-- The parameters' stores, in closed form. -/
theorem arun_spStrs (lab : Label → Int64) (ps : List (XReg × Int64)) (pc : Int64) (o : SO) (σ : AS) :
    arun lab (ps.map fun p => spStr p.1 p.2) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (4 * ps.length), o, { σ with slot := stSlots o.sp σ.regs ps σ.slot }⟩ := by
  induction ps generalizing pc σ with
  | nil => simp [arun, stSlots]
  | cons p ps ih =>
    simp only [List.map_cons, arun, List.foldl] at ih ⊢
    rw [dstep_spStr, ih]
    simp only [stSlots, List.length_cons, AM.mk.injEq, and_true]
    rw [Int64.add_assoc, show (4 : Int64) = Int64.ofNat 4 from rfl, ← Int64.ofNat_add]
    congr 2; omega

/-- The registers after the frame's setup: `sp` the new frame, `x29` at
its saved pair. -/
def frRegs (F : Int64) (r : Reg64s) : Reg64s :=
  ({ r with SP := r.X9 }).setXReg .X29 (r.X9.toBitVec + BitVec.ofInt 64 (F.toInt - 16))

/-- The cells after the frame's setup: the caller's `x29` and `x30` saved. -/
def frSlot (σ : AS) : Int → BitVec 64 := upd (upd σ.slot (-16) σ.regs.X29.toBitVec) (-8) σ.regs.X30.toBitVec

/-- **The frame's setup**, in closed form. -/
theorem frSetup_run (lab : Label → Int64) (pc : Int64) (σ : AS) {F : Int64} (hF : 16 ≤ F.toInt) :
    arun lab (frSetup F) ⟨pc, oChk F, σ⟩ = ⟨pc + 4 + 4 + 4 + 4, oFr F,
      { σ with regs := frRegs F σ.regs, slot := frSlot σ }⟩ := by
  simp [frSetup, oChk, oFr, frRegs, frSlot, arun, spStr, Reg64s.getRegOrZr_X, dstep, classify, RegOnly, AI.so, AI.step,
    AI.tgt, soReg, regRes, Operation.interp, MachineData.setRegOrSp, Reg64s.setRegOrSp, Reg64s.setRegOrSp64,
    ConstExpr.interp, SO.set, ExtOrImmReg.interp, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, SO.get, lk,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst,
    bmod_sub (by omega : (0 : Int) ≤ 16) hF, bmod_sub (by omega : (0 : Int) ≤ 8) (by omega : (8 : Int) ≤ F.toInt)]
  refine ⟨by omega, ?_⟩
  rw [show -F.toInt + (F.toInt - 16) = -16 by omega, show -F.toInt + (F.toInt - 8) = -8 by omega]

/-- The frame's setup is covered. -/
theorem frSetup_ok {lo hi : Int} {F : Int64} (h16 : F.toInt % 16 = 0) (hF : 16 ≤ F.toInt) (hlo : lo ≤ -16)
    (hhi : 0 ≤ hi) : okBlk lo hi (oChk F) (frSetup F) = true := by
  simp [frSetup, oChk, spStr, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write,
    SO.kill, SO.killZ, rm, SO.set, SO.get, lk, offOk, bmod_sub (by omega : (0 : Int) ≤ 16) hF,
    bmod_sub (by omega : (0 : Int) ≤ 8) (by omega : (8 : Int) ≤ F.toInt)]
  omega

/-- Stores into cells inside the region are covered. -/
theorem okBlk_spStrs {lo hi : Int} {o : SO} (h16 : o.sp % 16 = 0) {ps : List (XReg × Int64)}
    (hps : ∀ p ∈ ps, offOk lo hi (o.sp + p.2.toInt) = true) :
    okBlk lo hi o (ps.map fun p => spStr p.1 p.2) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hc : classify (spStr p.1 p.2) = some (AI.str (.low (.reg p.1) .W64) p.2) := rfl
    simp only [List.map_cons, okBlk, hc, AI.ok, AI.so, AI.isTerm, Bool.not_false, Bool.or_true,
      Bool.and_true]
    rw [hps p List.mem_cons_self, ih fun q hq => hps q (List.mem_cons_of_mem _ hq)]
    simp [h16]

/-- **The frame's setup and the parameters' stores are covered**, the stores'
cells inside the region. -/
theorem frameSet_ok {lo hi : Int} {F : Int64} (h16 : F.toInt % 16 = 0) (hF : 16 ≤ F.toInt) (hlo : lo ≤ -16)
    (hhi : 0 ≤ hi) {ps : List (XReg × Int64)} (hps : ∀ p ∈ ps, offOk lo hi (-F.toInt + p.2.toInt) = true) :
    okBlk lo hi (oChk F) (frameSet F ps) = true := by
  have h := okBlk_spStrs (lo := lo) (hi := hi) (o := oFr F) (by simp [oFr]; omega) (ps := ps) (by simpa [oFr] using hps)
  simp [frameSet, frSetup, oChk, spStr, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB, SO.write,
    SO.kill, SO.killZ, rm, SO.set, SO.get, lk, offOk, bmod_sub (by omega : (0 : Int) ≤ 16) hF,
    bmod_sub (by omega : (0 : Int) ≤ 8) (by omega : (8 : Int) ≤ F.toInt)]
  refine ⟨⟨⟨by omega, by omega, by omega⟩, by omega⟩, ⟨⟨by omega, by omega, by omega⟩, by omega⟩, ?_⟩
  rw [show -F.toInt + (F.toInt - 16) = -16 by omega]
  simpa [oFr, spStr] using h

/-- **The frame's setup and the parameters' stores**, in closed form. -/
theorem frameSet_run (lab : Label → Int64) (pc : Int64) (σ : AS) {F : Int64} (hF : 16 ≤ F.toInt)
    (ps : List (XReg × Int64)) :
    arun lab (frameSet F ps) ⟨pc, oChk F, σ⟩ = ⟨pc + 4 + 4 + 4 + 4 + Int64.ofNat (4 * ps.length), oFr F,
      { σ with regs := frRegs F σ.regs, slot := stSlots (-F.toInt) (frRegs F σ.regs) ps (frSlot σ) }⟩ := by
  have h := frSetup_run lab pc σ hF
  simp only [arun] at h
  simp only [frameSet, arun, List.foldl_append, h]
  have h2 := arun_spStrs lab ps (pc + 4 + 4 + 4 + 4) (oFr F) { σ with regs := frRegs F σ.regs, slot := frSlot σ }
  simp only [arun] at h2
  rw [h2]
  rfl

/-- The thread-control-block word the check reads, `[tpidr_el0, #lim]`. -/
def tcbA (r : Reg64s) (lim : Int64) : BitVec 64 := BitVec.ofInt 64 (r.TPIDR_EL0.toBitVec.toInt + lim.toInt)

/-- The limit load reads `tcbA`. -/
theorem rAddr_chkRegs (F lim : Int64) (r : Reg64s) : rAddr (chkRegs F r) .X10 lim = tcbA r lim := by
  simp [rAddr, chkRegs, tcbA]

/-- `oChk Z` claims no more than itself. -/
theorem SO.le_oChk (F : Int64) : SO.le (oChk F) (oChk F) = true := by simp [SO.le, oChk, lk]

/-- `oChk Z` claims nothing about `x10`. -/
theorem SO.le_oChk_kill (F : Int64) : SO.le (oChk F) ((oChk F).kill .X10) = true := by
  simp [SO.le, oChk, SO.kill, rm, lk]

/-- The `exit_group` tail's block: `str x0, [sp, #k]; ldr x0, [sp, #k]; movz x8, #94`. -/
def exitTail (k : Int64) : List Directive := [spStr .X0 k, RW.dir .X0 (.slot k), RW.dir .X8 (.imm 94)]

/-- **The tail's block**: `x8 = 94`, `x0` kept, the cell stored. -/
theorem exitTail_run (lab : Label → Int64) (pc : Int64) (o : SO) (σ : AS) (k : Int64) :
    arun lab (exitTail k) ⟨pc, o, σ⟩ = ⟨pc + 4 + 4 + 4, ⟨o.sp, rm (rm o.regs .X0) .X8⟩,
      { σ with regs := σ.regs.setXReg .X8 94#64, slot := upd σ.slot (o.sp + k.toInt) σ.regs.X0.toBitVec }⟩ := by
  simp [exitTail, spStr, RW.dir, AI.toDir, arun, Reg64s.getRegOrZr_X, dstep, classify, RegOnly, AI.so, AI.step,
    AI.tgt, soReg, regRes, Operation.interp, ConstExpr.interp, SO.set, SO.get, lk, upd_apply,
    MachineData.setRegOrZr, Reg64s.setRegOrZr, Reg64s.setRegOrZr64, zrB, SO.write, SO.kill, SO.killZ, rm, regDst]
  rw [show σ.regs.setXReg .X0 σ.regs.X0.toBitVec = σ.regs from Reg64s.setXReg_getXReg _ .X0]

/-- The tail's block is covered, the cell inside the region. -/
theorem exitTail_ok {lo hi : Int} {o : SO} {k : Int64} (hk : offOk lo hi (o.sp + k.toInt) = true)
    (h16 : o.sp % 16 = 0) : okBlk lo hi o (exitTail k) = true := by
  simp [exitTail, spStr, RW.dir, AI.toDir, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, regDst, zrB,
    SO.write, SO.kill, SO.killZ, rm, SO.set, SO.get, lk, hk, h16]

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- The prologue's node after the limit's address (`chkHead`). -/
def proN1 (pc0 Z : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc0 + 4 + 4, oChk Z, fun σ1 c => ∃ σ, J σ c ∧ σ1 = { σ with regs := chkRegs Z σ.regs }⟩

/-- The prologue's node after the limit's load. -/
def proN2 (ms : MemSide isaLSE2) (pc0 Z lim : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc0 + 4 + 4 + 4, oChk Z, fun σ2 c => ∃ σ v, J σ c ∧ ms.G ⟨tcbA σ.regs lim, 8⟩ v ∧
    σ2 = ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }⟩

/-- The prologue's node after the check's branch (not taken). -/
def proN3 (ms : MemSide isaLSE2) (pc0 Z lim : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc0 + 4 + 4 + 4 + 4 + 4, oChk Z, fun σ3 c => ∃ σ v, J σ c ∧ ms.G ⟨tcbA σ.regs lim, 8⟩ v ∧
    σ3.regs = (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs ∧ σ3.slot = σ.slot⟩

/-- **The prologue's states inside `W`**, none moved by `K`: one obligation
per node (the entry's block, the load, the branch, the frame's set-up). -/
structure ProW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isaLSE2) (pc0 Z lim : Int64) (L : Label)
    (ps : List (XReg × Int64)) (J : AS → Ctl → Prop) : Prop where
  w0 : BlkW W K exe endPc R F ⟨pc0, ⟨0, []⟩, J⟩ (chkHead Z)
  w1 : NodeW W K exe endPc R F (proN1 pc0 Z J)
  w2 : BlkW W K exe endPc R F (proN2 ms pc0 Z lim J) (chkBr L)
  w3 : BlkW W K exe endPc R F (proN3 ms pc0 Z lim J) (frameSet Z ps)

/-- Every prologue is inside the trivial predicate, with no outside moves. -/
theorem ProW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {J : AS → Ctl → Prop} :
    ProW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, BlkW.triv⟩

/-- **A stack-checked prologue is one segment** from the function's entry
(node invariant `J`, `sp` at offset 0) to the body's first node `nb`
(`sp` at `-Z`, offsets no stronger than `oFr Z`), the source stuttering.
From every state of `J`: the limit's address `tcbA` is owned by the runtime,
plain (no atomic access races the load), outside the private memory; for every
limit `v` the runtime memory may hold there, `v ≤ sp - Z` (the branch to the
grow stub is not taken), and `nb`'s invariant holds of every state with the
registers after the prologue and the cells after its stores. Its states lie in `W`, none moved by `K`
(`hW`, `ProW`). -/
theorem prologue_segW {W : Frag isaLSE2} {K : State → State → Prop} {Z lim : Int64} {L : Label}
    {ps : List (XReg × Int64)} {pc0 : Int64} {J : AS → Ctl → Prop}
    {nb : ND} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 (chkHead Z))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4) [ldrDir .X10 .X10 lim])
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4 + 4) (chkBr L))
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4 + 4 + 4 + 4) (frameSet Z ps))
    (hpc : nb.pc = pc0 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * ps.length))
    (ho : SO.le nb.o (oFr Z) = true) (hW : ProW W K exe endPc R F ms pc0 Z lim L ps J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs Z (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs →
          σ'.slot = stSlots (-Z.toInt) σ'.regs ps (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨pc0, ⟨0, []⟩, J⟩) (At exe endPc R F nb) := by
  let n1 : ND := ⟨pc0 + 4 + 4, oChk Z, fun σ1 c => ∃ σ, J σ c ∧ σ1 = { σ with regs := chkRegs Z σ.regs }⟩
  let n2 : ND := ⟨pc0 + 4 + 4 + 4, oChk Z, fun σ2 c => ∃ σ v, J σ c ∧ ms.G ⟨tcbA σ.regs lim, 8⟩ v ∧
    σ2 = ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }⟩
  let n3 : ND := ⟨pc0 + 4 + 4 + 4 + 4 + 4, oChk Z, fun σ3 c => ∃ σ v, J σ c ∧ ms.G ⟨tcbA σ.regs lim, 8⟩ v ∧
    σ3.regs = (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs ∧ σ3.slot = σ.slot⟩
  have one : ∀ {P : Frag isaLSE2} {n : ND},
      SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW W K p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.seq (Q := At exe endPc R F n1) ?_ (SegW.seq (Q := At exe endPc R F n2) ?_
    (SegW.seq (Q := At exe endPc R F n3) ?_ ?_))
  · refine one (seg_ndW (by simp [chkHead]) (chkHead_ok (-Z.toInt) 0 Z) hF hR hal hlo hhi hc0 hW.w0 fun σ c hJ =>
      ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    rw [chkHead_run]
    exact ⟨rfl, SO.le_oChk Z, σ, hJ, rfl⟩
  · refine one (rtld_ndW (N := fun _ : Unit => n2) (E := fun e : Empty => e.elim) hF hc1 hW.w1 ?_)
    rintro m σ1 c hA hFm ⟨σ, hJ, rfl⟩
    obtain ⟨hrt, hmp, hdm, hv⟩ := hedge σ c hJ
    simp only [rAddr_chkRegs]
    exact ⟨hrt, hmp, hdm m hFm, c, .refl c, fun v hG => .inl ⟨(), rfl, SO.le_oChk_kill Z, σ, v, hJ, hG, rfl⟩⟩
  · refine one (seg_ndW (by simp [chkBr]) (chkBr_ok (-Z.toInt) 0 Z L) hF hR hal hlo hhi hc2 hW.w2 ?_)
    rintro σ2 c ⟨σ, v, hJ, hG, rfl⟩
    obtain ⟨-, -, -, hv⟩ := hedge σ c hJ
    have hle := (hv v hG).1
    obtain ⟨hpc2, hso2, hr2, hs2⟩ := chkBr_run (Executable.labels exe).label (pc0 + 4 + 4 + 4)
      (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }) Z L
    refine ⟨c, .refl c, .inl ⟨(), ?_, by rw [hso2]; exact SO.le_oChk Z, σ, v, hJ, hG, hr2, hs2⟩⟩
    rw [hpc2, ite_eq_left]
    have hsp : (σ.regs.SP - Z.toUInt64).toNat = (σ.regs.SP.toBitVec - Z.toBitVec).toNat := rfl
    simp [ldStep, chkRegs]
    rw [hsp]
    simpa using hle
  · refine one (seg_ndW (by simp [frameSet, frSetup]) (frameSet_ok h16 hZ (by omega) (Int.le_refl 0) hps) hF hR
      hal hlo hhi hc3 hW.w3 ?_)
    rintro σ3 c ⟨σ, v, hJ, hG, hr3, hs3⟩
    obtain ⟨-, -, -, hv⟩ := hedge σ c hJ
    refine ⟨c, .refl c, .inl ⟨(), ?_⟩⟩
    rw [frameSet_run _ _ _ hZ]
    have hfs : frSlot σ3 = frSlot σ := by
      simp only [frSlot, hs3, hr3]
      simp [ldStep, chkRegs]
    refine ⟨hpc, ho, (hv v hG).2 _ (by simp only [hr3]) ?_⟩
    simp only [hfs]

/-- **A stack-checked prologue is one segment** from the function's entry
(node invariant `J`, `sp` at offset 0) to the body's first node `nb`
(`sp` at `-Z`, offsets no stronger than `oFr Z`), the source stuttering.
From every state of `J`: the limit's address `tcbA` is owned by the runtime,
plain (no atomic access races the load), outside the private memory; for every
limit `v` the runtime memory may hold there, `v ≤ sp - Z` (the branch to the
grow stub is not taken), and `nb`'s invariant holds of every state with the
registers after the prologue and the cells after its stores. -/
theorem prologue_seg {Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {pc0 : Int64} {J : AS → Ctl → Prop}
    {nb : ND} (h16 : Z.toInt % 16 = 0) (hZ : 16 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-Z.toInt) 0 (-Z.toInt + q.2.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 (chkHead Z))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4) [ldrDir .X10 .X10 lim])
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4 + 4) (chkBr L))
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 4 + 4 + 4 + 4 + 4) (frameSet Z ps))
    (hpc : nb.pc = pc0 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + Int64.ofNat (4 * ps.length))
    (ho : SO.le nb.o (oFr Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs lim).toNat ∧ ms.mp ⟨tcbA σ.regs lim, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs lim) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs lim, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs Z (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs Z σ.regs }).regs →
          σ'.slot = stSlots (-Z.toInt) σ'.regs ps (frSlot σ) → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨pc0, ⟨0, []⟩, J⟩) (At exe endPc R F nb) :=
  (prologue_segW h16 hZ hF hR hal hlo hhi hps hc0 hc1 hc2 hc3 hpc ho ProW.triv hedge).toSeg

/-- The `exit_group` tail's node at the `svc` (`x8 = 94`, `x0` as at the
tail's entry). -/
def exitNx (n : ND) : ND :=
  ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ c => σ.regs.X8.toNat = 94 ∧ ∃ σ0, n.J σ0 c ∧ σ.regs.X0 = σ0.regs.X0⟩

/-- **The `exit_group` tail's states inside `W`**, none moved by `K`: the
block's and the `svc`'s. -/
structure ExitW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (n : ND) (k : Int64) : Prop where
  w0 : BlkW W K exe endPc R F n (exitTail k)
  w1 : NodeW W K exe endPc R F (exitNx n)

/-- Every tail is inside the trivial predicate, with no outside moves. -/
theorem ExitW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {k : Int64} : ExitW (fun _ _ => True) (fun _ _ => False) exe endPc R F n k :=
  ⟨BlkW.triv, NodeW.triv⟩

/-- **The `exit_group` tail is a segment to any exit**: the block (`x8 = 94`)
lands at the `svc` (`exit_nd`), `x0` unchanged; `hok` matches the
`exit_group` there with the status `x0` held at the tail's entry. Its states lie in `W`,
none moved by `K` (`hW`, `ExitW`). At the `svc`, `hok` is given `x0` unchanged from the entry. -/
theorem exitTail_segW {W : Frag isaLSE2} {K : State → State → Prop} {n : ND} {k : Int64} {Q : Frag isaLSE2}
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hk : offOk lo hi (n.o.sp + k.toInt) = true) (h16 : n.o.sp % 16 = 0)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir])
    (hW : ExitW W K exe endPc R F n k)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  let nx : ND := ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ c =>
    σ.regs.X8.toNat = 94 ∧ ∃ σ0, n.J σ0 c ∧ σ.regs.X0 = σ0.regs.X0⟩
  refine SegW.seq (Q := At exe endPc R F nx) ?_ (exit_ndW hK hcs hW.w1 (fun _ _ h => h.1) ?_)
  · refine (seg_ndW (N := fun _ : Unit => nx) (E := fun e : Empty => e.elim) (by simp [exitTail])
      (exitTail_ok hk h16) hF hR hal hlo hhi hc hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    rw [exitTail_run]
    refine ⟨rfl, by simp [SO.le, nx], rfl, σ, hJ, ?_⟩
    show (σ.regs.setXReg .X8 94#64).X0 = σ.regs.X0
    rfl
  · rintro s c σ ⟨he, hn, hdc, hpc, σ', hA, hD, -⟩ ⟨-, σ0, hJ0, hx0⟩ hreg
    rw [hx0]
    exact hok s c σ0 hJ0 ⟨he, hn, hdc, hpc, σ', hA, hD, by show σ'.regs.X0 = _; rw [← hA.regs, hreg]; exact hx0⟩

/-- **The `exit_group` tail is a segment to any exit**: the block (`x8 = 94`)
lands at the `svc` (`exit_nd`), `x0` unchanged; `hok` matches the
`exit_group` there with the status `x0` held at the tail's entry. -/
theorem exitTail_seg {n : ND} {k : Int64} {Q : Frag isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hk : offOk lo hi (n.o.sp + k.toInt) = true) (h16 : n.o.sp % 16 = 0)
    (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (exitTail k))
    (hcs : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (n.pc + 4 + 4 + 4) [svcDir])
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (exitTail_segW hK hF hR hal hlo hhi hk h16 hc hcs ExitW.triv hok).toSeg

end Fn

/-! ## The parser's forms -/

/-- The prologue is what Kraken's parser makes of scc's text. -/
example : chkHead 96 ++ [ldrDir .X10 .X10 8] ++ chkBr "L" ++ frameSet 96 [(.X0, 0), (.X1, 8)] =
    parseAArch64("sub x9, sp, #96
mrs x10, tpidr_el0
ldr x10, [x10, #8]
subs xzr, x9, x10
b.lo L
add sp, x9, #0
str x29, [sp, #80]
str x30, [sp, #88]
add x29, sp, #80
str x0, [sp]
str x1, [sp, #8]") := by decide

/-- The `exit_group` tail. -/
example : exitTail 8 ++ [svcDir] = parseAArch64("str x0, [sp, #8]
ldr x0, [sp, #8]
movz x8, #94
svc #0") := by decide

end Spike.Lib.A64.Flow

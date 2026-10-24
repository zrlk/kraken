/-
**Segments of an emitted x64 program from checks on its cells**: the
stack-checked prologue, the `exit_group` tail and `scc_rt_start` up to its
first call, for any valid layout of a program that passes a check decided
once per program (`blockAtB`, `labelGapB`: `Scc/Cert/Rt/CodeX64.lean`).
The x64 twin of `Spike/Lib/A64CodeSegs.lean`.

Offsets are from `%rsp` at the function's entry (the return address at
`[0, 8)`).

- **The prologue** (`xPrologue_seg`): `pushq %rbp; movq %rsp, %rbp`
  (`xHead`), the stack check's address `leaq -Z(%rsp), %rax` (`xLea`), the
  limit `movq %fs:lim, %r11` (`fsldG_nd`: only the values the runtime's
  memory may hold need land), `cmpq %r11, %rax; jb L` (`xCmp`, not taken),
  then `subq $Z, %rsp` and the parameters' stores (`xFr`); the body's
  first node has `%rsp` at `-8 - Z` and `%rbp` at `-8` (`oF Z`).
  `prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps` checks the code
  (`fn`'s head right before the check's label `sc`, the blocks after `sc`
  and the body's label `entry` after them); `prologue_seg_of` is
  `xPrologue_seg` from `fn` to a node at `entry`.
- **The `exit_group` tail** (`xExitTail_seg`): `movq %rax, k(%rbp); movq
  k(%rbp), %rdi; movl $231, %eax` (`xExit`), then `syscall` (`exit_nd`), a
  segment to any fragment from a node whose offsets are `%rbp`'s alone.
  `exitIn cells l k z0 z1 z2` checks it right after `l`; `exitTail_seg_of`.
- **`scc_rt_start` up to its first call** (`start_seg`): the frame of 32
  (`xStart0`), the handler's address (`leaq scc_rt_sigign(%rip), %rax`,
  `si_nd`), the arguments (`xStartArgs`) and `rt_sigaction(SIGPIPE, act,
  NULL, 8)` (`syscall_nd`, which returns 0: `syscallCall_rtSigaction`), to a
  node at the call `call scc_rt_alloc_tcb` whose obligation holds of
  `startS`. `startIn cells` checks the code; `start_seg_of`.
-/
import Spike.Lib.X64Dead
import Kraken.X64.Parser
import Scc.Cert.Rt.CodeX64

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## The prologue -/

/-- `pushq %rbp; movq %rsp, %rbp`. -/
def xHead : List (Directive × Nat) :=
  [(op64 (.push (.regOrMem (.reg (.low .rbp .W64)))), 1),
   (op64 (.mov (.reg (.low .rbp .W64)) (.regOrMem (.reg (.low .rsp .W64)))), 3)]

/-- `leaq -Z(%rsp), %rax`, `z` bytes. -/
def xLea (Z : Int64) (z : Nat) : List (Directive × Nat) :=
  [(op64 (.lea (.low .rax .W64) { base := some (.reg .rsp), idx := none, disp := .int64 (-Z) }), z)]

/-- `cmpq %r11, %rax; jb L`. -/
def xCmp (L : String) (z1 z2 : Nat) : List (Directive × Nat) :=
  [(op64 (.cmp (.reg (.low .rax .W64)) (.regOrMem (.reg (.low .r11 .W64)))), z1), (op64 (.jcc .c L), z2)]

/-- `movq %r, n(%rbp)`, `z` bytes (`p = (r, n, z)`). -/
def xSt (p : Reg64 × Int64 × Nat) : Directive × Nat :=
  (op64 (.mov (.mem { base := some (.reg .rbp), idx := none, disp := .int64 p.2.1 })
    (.regOrMem (.reg (.low p.1 .W64)))),
    p.2.2)

/-- `subq $Z, %rsp`, then the parameters' stores `movq %r, n(%rbp)`. -/
def xFr (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat)) : List (Directive × Nat) :=
  (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z) :: ps.map xSt

/-- The blocks are the parser's form of the listing. -/
example : xHead ++ xLea 32 5 ++ xCmp "L" 3 2 ++ xFr 32 4 [(.rdi, -8, 4)] =
    (parse("pushq %rbp
movq %rsp, %rbp
leaq -32(%rsp), %rax
cmpq %r11, %rax
jb L
subq $32, %rsp
movq %rdi, -8(%rbp)")).zip [1, 3, 5, 3, 2, 4, 4] := by decide

/-- Runs a concrete x64 block on a symbolic abstract state (`block_spec`'s
simp set, for blocks with parameters). -/
macro "x64simp" : tactic => `(tactic| simp [arun, dstep, classify, RegOnly, AI.so, soReg, regDst, regRes,
   Operation.interp, Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg,
   Reg64s.set, ConstExpr.interp, AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, lk, rm,
   List.foldl, Reg.base, BlockSpec.AI.step_ld', BlockSpec.AI.step_st', BlockSpec.AI.step_push',
   BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jcc', BlockSpec.AI.tgt_jcc',
   BlockSpec.AI.tgt_st', BlockSpec.AI.tgt_push', BlockSpec.AI.tgt_reg', BlockSpec.AI.tgt_ld',
   upd_apply, Reg64s.get_low64])



/-- The offsets after the head: `%rsp` and `%rbp` at the saved `%rbp`. -/
abbrev oH : SO := ⟨-8, [(.rbp, -8)]⟩

/-- The registers after the head. -/
def hdRegs (r : Reg64s) : Reg64s := (r.set64 .rsp (r.rsp.toBitVec - 8#64)).set64 .rbp (r.rsp.toBitVec - 8#64)

/-- **The head**, in closed form. -/
theorem xHead_run (lab : String → Int64) (pc : Int64) (σ : AS) :
    arun lab xHead ⟨pc, ⟨0, []⟩, σ⟩ =
      ⟨pc + 1 + 3, oH, { σ with regs := hdRegs σ.regs, slot := upd σ.slot (-8) σ.regs.rbp.toBitVec }⟩ := by
  simp only [xHead]; x64simp; rfl

/-- The head is covered. -/
theorem xHead_ok {lo hi : Int} (hlo : lo ≤ -8) (hhi : 0 ≤ hi) : okBlk lo hi ⟨0, []⟩ xHead = true := by
  simp [xHead, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, SO.get, SO.set, SO.write, SO.kill, lk, rm,
    offOk]
  omega

/-- The offsets after the check's address: `%rax` at `-8 - Z`. -/
abbrev oL (Z : Int64) : SO := ⟨-8, [(.rax, -8 - Z.toInt), (.rbp, -8)]⟩

/-- Adding to a word's signed value is subtracting the negation. -/
theorem ofInt_toInt_add (x : BitVec 64) (k : Int) : BitVec.ofInt 64 (x.toInt + k) = x - BitVec.ofInt 64 (-k) := by
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_ofInt, BitVec.toInt_sub]

/-- A non-negative word's negation is its own balanced residue. -/
theorem neg_bmod {Z : Int64} (h0 : 0 ≤ Z.toInt) : (-Z.toInt).bmod 18446744073709551616 = -Z.toInt := by
  have := Z.toInt_lt
  simp only [Int.bmod]
  split <;> omega

/-- **The check's address**, in closed form. -/
theorem xLea_run (lab : String → Int64) (pc : Int64) (σ : AS) {Z : Int64} (h0 : 0 ≤ Z.toInt) (z : Nat) :
    arun lab (xLea Z z) ⟨pc, oH, σ⟩ =
      ⟨pc + Int64.ofNat z, oL Z, { σ with regs := σ.regs.set64 .rax (σ.regs.rsp.toBitVec - Z.toBitVec) }⟩ := by
  have hb : (-Z.toInt).bmod 18446744073709551616 = -Z.toInt := neg_bmod h0
  simp only [xLea]; x64simp
  refine ⟨by rw [hb]; omega, ?_⟩
  rw [hb]
  have ht : σ.regs.rsp.toBitVec.take 64 = σ.regs.rsp.toBitVec := by
    simp [BitVec.take, BitVec.extractLsb'_eq_self]
  simp only [BitVec.toAddressSize, ht, ← Int.sub_eq_add_neg]
  congr 1
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt, BitVec.toInt_sub]
  rfl

/-- The check's address is covered. -/
theorem xLea_ok {lo hi : Int} (Z : Int64) (z : Nat) : okBlk lo hi oH (xLea Z z) = true := by
  simp [xLea, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, SO.get, SO.set, SO.write, SO.kill, lk, rm]

/-- **The check's branch**: to `L` iff the limit `%r11` is above `%rax`
(unsigned); the registers and cells unchanged. -/
theorem xCmp_run (lab : String → Int64) (pc : Int64) (o : SO) (σ : AS) (L : String) (z1 z2 : Nat) :
    (arun lab (xCmp L z1 z2) ⟨pc, o, σ⟩).pc =
      (if σ.regs.r11.toNat ≤ σ.regs.rax.toNat then pc + Int64.ofNat z1 + Int64.ofNat z2 else lab L) ∧
    (arun lab (xCmp L z1 z2) ⟨pc, o, σ⟩).so = o ∧
    (arun lab (xCmp L z1 z2) ⟨pc, o, σ⟩).σ.regs = σ.regs ∧
    (arun lab (xCmp L z1 z2) ⟨pc, o, σ⟩).σ.slot = σ.slot := by
  simp only [xCmp]; x64simp
  have := σ.regs.r11.toNat_lt; have := σ.regs.rax.toNat_lt
  by_cases h : σ.regs.r11.toNat ≤ σ.regs.rax.toNat
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- The check's branch is covered. -/
theorem xCmp_ok {lo hi : Int} (o : SO) (L : String) (z1 z2 : Nat) : okBlk lo hi o (xCmp L z1 z2) = true := by
  simp [xCmp, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, SO.get, SO.set, SO.write, SO.kill, lk, rm,
    regDst]

/-- The cells after the parameters' stores `ps` of the registers `regs`
(`%rbp` at `-8`). -/
def xStSlots (regs : Reg64s) : List (Reg64 × Int64 × Nat) → (Int → BitVec 64) → Int → BitVec 64
  | [], sl => sl
  | p :: ps, sl => xStSlots regs ps (upd sl (-8 + p.2.1.toInt) (regs.get64 p.1))

/-- The stores' bytes. -/
def szSum (ps : List (Reg64 × Int64 × Nat)) : Nat := (ps.map (·.2.2)).sum

/-- A parameter's store with `%rbp` at `-8`. -/
theorem dstep_xSt (lab : String → Int64) (pc : Int64) (o : SO) (ho : o.get .rbp = some (-8)) (σ : AS)
    (p : Reg64 × Int64 × Nat) :
    dstep lab ⟨pc, o, σ⟩ (xSt p) =
      ⟨pc + Int64.ofNat p.2.2, o, { σ with slot := upd σ.slot (-8 + p.2.1.toInt) (σ.regs.get64 p.1) }⟩ := by
  simp [xSt, dstep, classify, BlockSpec.AI.step_st', BlockSpec.AI.tgt_st', AI.so, ho]

/-- **The parameters' stores**, in closed form. -/
theorem arun_xSts (lab : String → Int64) (ps : List (Reg64 × Int64 × Nat)) (pc : Int64) (o : SO)
    (ho : o.get .rbp = some (-8)) (σ : AS) :
    arun lab (ps.map xSt) ⟨pc, o, σ⟩ =
      ⟨pc + Int64.ofNat (szSum ps), o, { σ with slot := xStSlots σ.regs ps σ.slot }⟩ := by
  induction ps generalizing pc σ with
  | nil => simp [arun, xStSlots, szSum]
  | cons p ps ih =>
    simp only [List.map_cons, arun, List.foldl] at ih ⊢
    rw [dstep_xSt lab pc o ho, ih]
    simp only [xStSlots, szSum, List.map_cons, List.sum_cons, AM.mk.injEq, and_true]
    rw [Int64.add_assoc, ← Int64.ofNat_add]

/-- The offsets in the frame. -/
abbrev oF (Z : Int64) : SO := ⟨-8 - Z.toInt, [(.rax, -8 - Z.toInt), (.rbp, -8)]⟩

/-- **The frame's allocation and the parameters' stores**: `%rsp` down by
`Z`, the cells stored; the flags are the `sub`'s. -/
theorem xFr_run (lab : String → Int64) (pc : Int64) (σ : AS) (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat)) :
    (arun lab (xFr Z z ps) ⟨pc, oL Z, σ⟩).pc = pc + Int64.ofNat z + Int64.ofNat (szSum ps) ∧
    (arun lab (xFr Z z ps) ⟨pc, oL Z, σ⟩).so = oF Z ∧
    (arun lab (xFr Z z ps) ⟨pc, oL Z, σ⟩).σ.regs = σ.regs.set64 .rsp (σ.regs.rsp.toBitVec - Z.toBitVec) ∧
    (arun lab (xFr Z z ps) ⟨pc, oL Z, σ⟩).σ.slot =
      xStSlots (σ.regs.set64 .rsp (σ.regs.rsp.toBitVec - Z.toBitVec)) ps σ.slot := by
  have h1 : arun lab (xFr Z z ps) ⟨pc, oL Z, σ⟩ = arun lab (ps.map xSt)
      (dstep lab ⟨pc, oL Z, σ⟩ (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z)) := rfl
  have h2 : (dstep lab ⟨pc, oL Z, σ⟩ (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z)).so = oF Z := by
    x64simp
  have h3 : (dstep lab ⟨pc, oL Z, σ⟩ (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z)).pc =
      pc + Int64.ofNat z := by x64simp
  have h4 : (dstep lab ⟨pc, oL Z, σ⟩ (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z)).σ.regs =
      σ.regs.set64 .rsp (σ.regs.rsp.toBitVec - Z.toBitVec) := by x64simp
  have h5 : (dstep lab ⟨pc, oL Z, σ⟩ (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z)).σ.slot = σ.slot := by
    x64simp
  rw [h1]
  generalize dstep lab ⟨pc, oL Z, σ⟩ (op64 (.sub (.reg (.low .rsp .W64)) (.imm (.int64 Z))), z) = am at h2 h3 h4 h5
  obtain ⟨pc', o', σ'⟩ := am
  simp only at h2 h3 h4 h5
  subst h2 h3
  rw [arun_xSts lab ps _ _ (by simp [SO.get, lk]) σ']
  simp [h4, h5]

/-- The frame's allocation and the stores are covered, the stores' slots in
the region. -/
theorem xFr_ok {lo hi : Int} (Z : Int64) (z : Nat) (ps : List (Reg64 × Int64 × Nat))
    (hps : ∀ p ∈ ps, offOk lo hi (-8 + p.2.1.toInt) = true) : okBlk lo hi (oL Z) (xFr Z z ps) = true := by
  have hs : ∀ (o : SO), o.get .rbp = some (-8) → okBlk lo hi o (ps.map xSt) = true := by
    intro o ho
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      have hc : classify (xSt p).1 = some (AI.st .rbp p.2.1 p.1) := rfl
      simp only [List.map_cons, okBlk, hc, AI.ok, AI.so, AI.isTerm, ho, Bool.not_false, Bool.or_true,
        Bool.and_true]
      rw [hps p List.mem_cons_self, ih fun q hq => hps q (List.mem_cons_of_mem _ hq)]; rfl
  simp only [xFr, okBlk]
  simp [classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, SO.get, SO.set, SO.write, SO.kill, lk, rm]
  exact hs _ (by simp [SO.get, lk])

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A node at a thread-pointer load, the value the runtime's**: as
`fsld_nd`, but only the values the runtime memory may hold at the address
(`ms.G`) need land. Its states lie in `W`, and no outside
move `K` moves them (`hW`). -/
theorem fsldG_ndW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {d : Reg64} {k : Int64} {z : Nat} (hd : d ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hW : ∀ s c, At exe endPc R F n s c → W s c ∧ ∀ s', ¬ K s s')
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + k.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + k.toBitVec, 8⟩ false ∧
      Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + k.toBitVec) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + k.toBitVec, 8⟩ v →
        Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d (v.setWidth 64) σ⟩ c') :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegW.step hW fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (fsDir d k) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hrt, hmp, hdm, c', hr, hL⟩ := hedge _ σ c hA hD hJ
  have ha : fsAddr s z { base := none, idx := none, disp := .int64 k } = σ.regs.fsBase.toBitVec + k.toBitVec := by
    simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
  have hex := exec_movfs_load_agrees hc ha hdm (agrees_of_decls hdc _ _)
  refine .rtLoad _ _ _ c' hex hrt hmp hr fun v hG _ => ?_
  have hset : s.st.1.regs.set (Reg.low d .W64) (v.setWidth 64) = s.st.1.regs.set64 d (v.setWidth 64) := by
    cases d <;> rfl
  have hA' : Abs R (n.o.kill d) { s.st.1 with regs := s.st.1.regs.set64 d (v.setWidth 64) }
      (fsStep d (v.setWidth 64) σ) := by
    refine ⟨by simp only [fsStep, hA.regs], hA.zmms, hA.status, ?_, hA.slot⟩
    exact SORel.write (o := n.o) (d := d) (by simp [SO.write, hd]) hA.so fun r hr =>
      Reg64s.get64_set64_ne _ hr _
  have hD' : F { s.st.1 with regs := s.st.1.regs.set64 d (v.setWidth 64) } := hF _ _ hD fun _ _ _ => rfl
  have hs1 : after s z { s.st.1 with regs := s.st.1.regs.set (Reg.low d .W64) (v.setWidth 64) } =
      { s with st := ({ s.st.1 with regs := s.st.1.regs.set64 d (v.setWidth 64) }, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc, hset]
  rw [hs1]
  rcases hL v hG with ⟨j, hj⟩ | ⟨x, hx⟩
  · exact .inl ⟨j, hj.at he hn hdc hA' hD'⟩
  · exact .inr ⟨x, hx.at he hn hdc hA' hD'⟩

/-- **`fsldG_ndW` inside the trivial predicate**, with no outside moves. -/
theorem fsldG_nd {n : ND} {d : Reg64} {k : Int64} {z : Nat} (hd : d ≠ .rsp) (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(fsDir d k, z)])
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + k.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + k.toBitVec, 8⟩ false ∧
      Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + k.toBitVec) 8 = none ∧
      ∃ c', LocalRun p c c' ∧ ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + k.toBitVec, 8⟩ v →
        Lands N E ⟨n.pc + Int64.ofNat z, n.o.kill d, fsStep d (v.setWidth 64) σ⟩ c') :
    Seg p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  (fsldG_ndW (W := fun _ _ => True) (K := fun _ _ => False) (hW := fun _ _ _ => ⟨trivial, fun _ h => h⟩)
    hd hF hcode hedge).toSeg

/-- The state after the head. -/
def xS1 (σ : AS) : AS := { σ with regs := hdRegs σ.regs, slot := upd σ.slot (-8) σ.regs.rbp.toBitVec }

/-- The state after the check's address. -/
def xS2 (Z : Int64) (σ : AS) : AS :=
  { xS1 σ with regs := (xS1 σ).regs.set64 .rax ((xS1 σ).regs.rsp.toBitVec - Z.toBitVec) }

/-- The state after the limit's load. -/
def xS3 (Z : Int64) (v : BitVec 64) (σ : AS) : AS := fsStep .r11 v (xS2 Z σ)

/-- **The registers in the frame**: `%rsp` down by `8 + Z`, `%rbp` at the
saved `%rbp`, `%rax` the check's address, `%r11` the limit. -/
def xFrRegs (Z : Int64) (v : BitVec 64) (r : Reg64s) : Reg64s :=
  let r3 := ((hdRegs r).set64 .rax ((hdRegs r).rsp.toBitVec - Z.toBitVec)).set64 .r11 v
  r3.set64 .rsp (r3.rsp.toBitVec - Z.toBitVec)

/-- `oL Z` is below itself. -/
theorem oL_le (Z : Int64) : SO.le (oL Z) (oL Z) = true := by simp [SO.le, lk]

/-- The limit's register has no offset. -/
theorem oL_kill (Z : Int64) : (oL Z).kill .r11 = oL Z := by simp [SO.kill, rm]

/-- The check's address: `%rsp - 8 - Z`. -/
theorem xS2_rax (Z : Int64) (σ : AS) :
    (xS2 Z σ).regs.rax.toBitVec = σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec := by
  simp [xS2, xS1, hdRegs, Reg64s.set64]

/-- The head keeps the thread pointer. -/
theorem xS1_fsBase (σ : AS) : (xS1 σ).regs.fsBase = σ.regs.fsBase := by
  simp [xS1, hdRegs, Reg64s.set64]

/-- The x64 prologue's node after the head. -/
def xProN1 (pc0 : Int64) (J : AS → Ctl → Prop) : ND := ⟨pc0 + 1 + 3, oH, fun σ1 c => ∃ σ, J σ c ∧ σ1 = xS1 σ⟩

/-- The x64 prologue's node after the check's address. -/
def xProN2 (pc0 : Int64) (zl : Nat) (Z : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc0 + 1 + 3 + Int64.ofNat zl, oL Z, fun σ2 c => ∃ σ, J σ c ∧ σ2 = xS2 Z σ⟩

/-- The x64 prologue's node after the limit's load. -/
def xProN3 (ms : MemSide isa) (pc0 : Int64) (zl zf : Nat) (Z lim : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf, oL Z, fun σ3 c => ∃ σ v, J σ c ∧
    ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v ∧ σ3 = xS3 Z (v.setWidth 64) σ⟩

/-- The x64 prologue's node after the check's branch (not taken). -/
def xProN4 (ms : MemSide isa) (pc0 : Int64) (zl zf z1 z2 : Nat) (Z lim : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2, oL Z, fun σ4 c => ∃ σ v,
    J σ c ∧ ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v ∧ σ4.regs = (xS3 Z (v.setWidth 64) σ).regs ∧
    σ4.slot = (xS1 σ).slot⟩

/-- **The x64 prologue's states inside `W`**, none moved by `K`: one
obligation per node (the head, the check's address, the limit's load, the
check, the frame's set-up). -/
structure XProW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (ms : MemSide isa) (pc0 Z lim : Int64) (L : String)
    (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) (J : AS → Ctl → Prop) : Prop where
  w0 : BlkW W K exe endPc R F ⟨pc0, ⟨0, []⟩, J⟩ xHead
  w1 : BlkW W K exe endPc R F (xProN1 pc0 J) (xLea Z zl)
  w2 : NodeW W K exe endPc R F (xProN2 pc0 zl Z J)
  w3 : BlkW W K exe endPc R F (xProN3 ms pc0 zl zf Z lim J) (xCmp L z1 z2)
  w4 : BlkW W K exe endPc R F (xProN4 ms pc0 zl zf z1 z2 Z lim J) (xFr Z zs ps)

/-- Every x64 prologue is inside the trivial predicate, with no outside
moves. -/
theorem XProW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    {J : AS → Ctl → Prop} :
    XProW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨BlkW.triv, BlkW.triv, NodeW.triv, BlkW.triv, BlkW.triv⟩

/-- **A stack-checked x64 prologue is one segment** from the function's
entry (`%rsp` at offset 0) to the body's first node (`%rsp` at `-8 - Z`,
offsets `oF Z`), the branch to `L` not taken: for every limit `v` the
runtime memory may hold at `%fs:lim` the obligation gives `v ≤ %rsp - 8 - Z`.
Its states lie in `W`, none moved by `K` (`hW`, `XProW`). -/
theorem xPrologue_segW {W : Frag isa} {K : State → State → Prop}
    {Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    {pc0 : Int64} {J : AS → Ctl → Prop} {nb : ND} (hZ : 0 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 xHead)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 1 + 3) (xLea Z zl))
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl) [(fsDir .r11 lim, zf)])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf) (xCmp L z1 z2))
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2) (xFr Z zs ps))
    (hpc : nb.pc = pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2 +
      Int64.ofNat zs + Int64.ofNat (szSum ps))
    (ho : SO.le nb.o (oF Z) = true)
    (hW : XProW W K exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs Z (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs ps (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨pc0, ⟨0, []⟩, J⟩) (At exe endPc R F nb) := by
  let pc1 := pc0 + 1 + 3
  let n1 : ND := ⟨pc1, oH, fun σ1 c => ∃ σ, J σ c ∧ σ1 = xS1 σ⟩
  let n2 : ND := ⟨pc1 + Int64.ofNat zl, oL Z, fun σ2 c => ∃ σ, J σ c ∧ σ2 = xS2 Z σ⟩
  let n3 : ND := ⟨pc1 + Int64.ofNat zl + Int64.ofNat zf, oL Z, fun σ3 c => ∃ σ v, J σ c ∧
    ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v ∧ σ3 = xS3 Z (v.setWidth 64) σ⟩
  let n4 : ND := ⟨pc1 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2, oL Z, fun σ4 c => ∃ σ v,
    J σ c ∧ ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v ∧ σ4.regs = (xS3 Z (v.setWidth 64) σ).regs ∧
    σ4.slot = (xS1 σ).slot⟩
  have one : ∀ {P : Frag isa} {n : ND},
      SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW W K p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.seq (Q := At exe endPc R F n1) ?_ (SegW.seq (Q := At exe endPc R F n2) ?_
    (SegW.seq (Q := At exe endPc R F n3) ?_ (SegW.seq (Q := At exe endPc R F n4) ?_ ?_)))
  · refine one (seg_ndW (by simp [xHead]) (xHead_ok (lo := -8 - Z.toInt) (hi := 0) (by omega) (by omega)) hF hR
      hlo hhi hc0 hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    rw [xHead_run]
    exact ⟨rfl, show SO.le oH oH = true by decide, σ, hJ, rfl⟩
  · refine one (seg_ndW (n := n1) (by simp [xLea]) (xLea_ok Z zl) hF hR hlo hhi hc1 hW.w1 ?_)
    rintro σ1 c ⟨σ, hJ, rfl⟩
    refine ⟨c, .refl c, .inl ⟨(), ?_⟩⟩
    rw [xLea_run _ _ _ hZ]
    exact ⟨rfl, oL_le Z, σ, hJ, rfl⟩
  · refine one (fsldG_ndW (n := n2) (N := fun _ : Unit => n3) (E := fun e : Empty => e.elim) (by decide) hF hc2
      hW.w2 ?_)
    rintro m σ2 c hA hFm ⟨σ, hJ, rfl⟩
    obtain ⟨hrt, hmp, hdm, hv⟩ := hedge σ c hJ
    have hfs : (xS2 Z σ).regs.fsBase = σ.regs.fsBase := by simp [xS2, xS1, hdRegs, Reg64s.set64]
    rw [hfs]
    exact ⟨hrt, hmp, hdm m hFm, c, .refl c,
      fun v hG => .inl ⟨(), rfl, by rw [oL_kill]; exact oL_le Z, σ, v, hJ, hG, rfl⟩⟩
  · refine one (seg_ndW (n := n3) (by simp [xCmp]) (xCmp_ok _ L z1 z2) hF hR hlo hhi hc3 hW.w3 ?_)
    rintro σ3 c ⟨σ, v, hJ, hG, rfl⟩
    obtain ⟨-, -, -, hv⟩ := hedge σ c hJ
    have hle := (hv v hG).1
    obtain ⟨hpc3, hso3, hr3, hs3⟩ := xCmp_run (Executable.labels exe).label n3.pc (oL Z) (xS3 Z (v.setWidth 64) σ)
      L z1 z2
    refine ⟨c, .refl c, .inl ⟨(), ?_, by rw [hso3]; exact oL_le Z, σ, v, hJ, hG, hr3, hs3⟩⟩
    rw [hpc3, ite_eq_left]
    have e1 : (xS3 Z (v.setWidth 64) σ).regs.r11.toNat = (v.setWidth 64).toNat := by
      simp [xS3, fsStep, Reg64s.set64]
    have e2 : (xS3 Z (v.setWidth 64) σ).regs.rax.toNat = (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat := by
      rw [← xS2_rax]; rfl
    rw [e1, e2]; exact hle
  · refine one (seg_ndW (n := n4) (by simp [xFr]) (xFr_ok Z zs ps hps) hF hR hlo hhi hc4 hW.w4 ?_)
    rintro σ4 c ⟨σ, v, hJ, hG, hr4, hs4⟩
    obtain ⟨-, hv⟩ := (hedge σ c hJ).2.2.2 v hG
    obtain ⟨h1, h2, h3, h4⟩ := xFr_run (Executable.labels exe).label n4.pc σ4 Z zs ps
    refine ⟨c, .refl c, .inl ⟨(), ?_, by rw [h2]; exact ho, hv _ ?_ ?_⟩⟩
    · rw [h1, hpc]
    · rw [h3, hr4]; rfl
    · rw [h4, hs4, h3, hr4]

/-- **A stack-checked x64 prologue is one segment** from the function's
entry (`%rsp` at offset 0) to the body's first node (`%rsp` at `-8 - Z`,
offsets `oF Z`), the branch to `L` not taken: for every limit `v` the
runtime memory may hold at `%fs:lim` the obligation gives `v ≤ %rsp - 8 - Z`. -/
theorem xPrologue_seg {Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    {pc0 : Int64} {J : AS → Ctl → Prop} {nb : ND} (hZ : 0 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc0 xHead)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (pc0 + 1 + 3) (xLea Z zl))
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl) [(fsDir .r11 lim, zf)])
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf) (xCmp L z1 z2))
    (hc4 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2) (xFr Z zs ps))
    (hpc : nb.pc = pc0 + 1 + 3 + Int64.ofNat zl + Int64.ofNat zf + Int64.ofNat z1 + Int64.ofNat z2 +
      Int64.ofNat zs + Int64.ofNat (szSum ps))
    (ho : SO.le nb.o (oF Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs Z (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs ps (xS1 σ).slot → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨pc0, ⟨0, []⟩, J⟩) (At exe endPc R F nb) :=
  (xPrologue_segW hZ hF hR hlo hhi hps hc0 hc1 hc2 hc3 hc4 hpc ho XProW.triv hedge).toSeg

end Fn

/-! ## The `exit_group` tail -/

/-- `movq %rax, n(%rbp); movq n(%rbp), %rdi; movl $231, %eax`. -/
def xExit (n : Int64) (z0 z1 z2 : Nat) : List (Directive × Nat) :=
  [(op64 (.mov (.mem { base := some (.reg .rbp), idx := none, disp := .int64 n }) (.regOrMem (.reg (.low .rax .W64)))),
     z0),
   (op64 (.mov (.reg (.low .rdi .W64)) (.regOrMem (.mem { base := some (.reg .rbp), idx := none, disp := .int64 n }))),
     z1),
   (.instr (.regular .W64 .W32 (.mov (.reg (.low .rax .W32)) (.imm (.int64 231)))), z2)]

/-- `xExit` is the parser's form of the listing. -/
example : xExit (-16) 4 4 5 = (parse("movq %rax, -16(%rbp)
movq -16(%rbp), %rdi
movl $231, %eax")).zip [4, 4, 5] := by decide

/-- **The tail's block**: it falls through with `%rax = 231`, `%rdi` the
`%rax` before it. -/
theorem xExit_run (lab : String → Int64) (pc : Int64) (sp b : Int) (σ : AS) (n : Int64) (z0 z1 z2 : Nat) :
    (arun lab (xExit n z0 z1 z2) ⟨pc, ⟨sp, [(.rbp, b)]⟩, σ⟩).pc =
      pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2 ∧
    (arun lab (xExit n z0 z1 z2) ⟨pc, ⟨sp, [(.rbp, b)]⟩, σ⟩).σ.regs.rax.toNat = 231 ∧
    (arun lab (xExit n z0 z1 z2) ⟨pc, ⟨sp, [(.rbp, b)]⟩, σ⟩).σ.regs.rdi.toBitVec = σ.regs.rax.toBitVec := by
  simp only [xExit]; x64simp
  first | rfl | exact ⟨rfl, rfl⟩

/-- The tail's block is covered, its slot in the region. -/
theorem xExit_ok {lo hi sp b : Int} (n : Int64) (z0 z1 z2 : Nat) (hk : offOk lo hi (b + n.toInt) = true) :
    okBlk lo hi ⟨sp, [(.rbp, b)]⟩ (xExit n z0 z1 z2) = true := by
  simp [xExit, okBlk, classify, RegOnly, AI.ok, AI.so, AI.isTerm, soReg, SO.get, SO.set, SO.write, SO.kill, lk, rm,
    regDst, Reg.base, hk]

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- The `exit_group` tail's node at the `syscall` (`%rax = 231`, `%rdi`
the `%rax` at the tail's entry). -/
def xExitNx (n : ND) (sp b : Int) (z0 z1 z2 : Nat) : ND :=
  ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2, ⟨sp, [(.rbp, b)]⟩,
    fun σ c => σ.regs.rax.toNat = 231 ∧ ∃ σ0, n.J σ0 c ∧ σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩

/-- **The `exit_group` tail's states inside `W`**, none moved by `K`: the
block's and the `syscall`'s. -/
structure XExitW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (n : ND) (sp b : Int) (k : Int64) (z0 z1 z2 : Nat) : Prop where
  w0 : BlkW W K exe endPc R F n (xExit k z0 z1 z2)
  w1 : NodeW W K exe endPc R F (xExitNx n sp b z0 z1 z2)

/-- Every tail is inside the trivial predicate, with no outside moves. -/
theorem XExitW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {n : ND}
    {sp b : Int} {k : Int64} {z0 z1 z2 : Nat} :
    XExitW (fun _ _ => True) (fun _ _ => False) exe endPc R F n sp b k z0 z1 z2 :=
  ⟨BlkW.triv, NodeW.triv⟩

/-- **The `exit_group` tail does not return**: from a node whose offsets are
`%rbp`'s alone (at `b`), with its code, it is a segment to any fragment, given
the `exit_group` at the `syscall` with the status the `%rax` at the tail's
entry is matched (`hok`). Its states lie in `W`, none moved by `K` (`hW`, `XExitW`). -/
theorem xExitTail_segW {W : Frag isa} {K : State → State → Prop}
    {n : ND} {Q : Frag isa} {sp b : Int} {k : Int64} {z0 z1 z2 z3 : Nat}
    (hno : n.o = ⟨sp, [(.rbp, b)]⟩) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : offOk lo hi (b + k.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (xExit k z0 z1 z2))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2) [(op64 .syscall, z3)])
    (hW : XExitW W K exe endPc R F n sp b k z0 z1 z2)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2,
      ⟨sp, [(.rbp, b)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  let nx : ND := ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2, ⟨sp, [(.rbp, b)]⟩,
    fun σ c => σ.regs.rax.toNat = 231 ∧ ∃ σ0, n.J σ0 c ∧ σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩
  refine SegW.seq (Q := At exe endPc R F nx) ?_ (exit_ndW hK hc1 hW.w1 (fun σ c h => h.1) ?_)
  · refine (seg_ndW (N := fun _ : Unit => nx) (E := fun e : Empty => e.elim) (by simp [xExit])
      (hno ▸ xExit_ok k z0 z1 z2 hk) hF hR hlo hhi hc0 hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    obtain ⟨h1, h2, h3⟩ := xExit_run (Executable.labels exe).label n.pc sp b σ k z0 z1 z2
    rw [hno]
    refine ⟨h1, ?_, h2, σ, hJ, h3⟩
    simp only [xExit]; x64simp; simp [nx, SO.le, lk]
  · rintro s c σ ⟨he, hn, hdc, hpc, σ', hA, hD, -⟩ ⟨-, σ0, hJ0, hx0⟩ hreg
    have e : σ.regs.rdi.toNat = σ0.regs.rax.toNat := congrArg BitVec.toNat hx0
    rw [e]
    exact hok s c σ0 hJ0 ⟨he, hn, hdc, hpc, σ', hA, hD, by
      show σ'.regs.rdi.toBitVec = _; rw [← hA.regs, hreg]; exact hx0⟩

/-- **The `exit_group` tail does not return**: from a node whose offsets are
`%rbp`'s alone (at `b`), with its code, it is a segment to any fragment, given
the `exit_group` at the `syscall` with the status the `%rax` at the tail's
entry is matched (`hok`). -/
theorem xExitTail_seg {n : ND} {Q : Frag isa} {sp b : Int} {k : Int64} {z0 z1 z2 z3 : Nat}
    (hno : n.o = ⟨sp, [(.rbp, b)]⟩) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    {lo hi : Int} (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : offOk lo hi (b + k.toInt) = true)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc (xExit k z0 z1 z2))
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2) [(op64 .syscall, z3)])
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2,
      ⟨sp, [(.rbp, b)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (xExitTail_segW hno hK hF hR hlo hhi hk hc0 hc1 XExitW.triv hok).toSeg

end Fn

/-! ## `scc_rt_start` up to its first call -/

/-- `scc_rt_start`'s frame: the head, then `subq $32, %rsp`. -/
def xStart0 : List (Directive × Nat) := (parse("pushq %rbp
movq %rsp, %rbp
subq $32, %rsp")).zip [1, 3, 4]
/-- The `rt_sigaction` call's arguments: the handler's address (in `%rax`)
spilled and reloaded into `%rsi`. -/
def xStartArgs : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq $13, %rdi
movq -8(%rbp), %rsi
movq $0, %rdx
movq $8, %r10
movl $13, %eax")).zip [4, 7, 4, 7, 7, 5]
/-- The offsets in `scc_rt_start`'s frame. -/
abbrev oS : SO := ⟨-40, [(.rbp, -8)]⟩
block_spec xStart0 (-40) 0 ⟨0, []⟩ xStart0
block_spec xStartArgs (-40) 0 oS xStartArgs

/-- **`rt_sigaction(SIGPIPE, act, NULL, 8)` decodes.** -/
theorem syscallCall_rtSigaction {r : Reg64s} (ha : r.rax.toNat = 13) (h0 : r.rdi.toNat = 13) (h2 : r.rdx.toNat = 0)
    (h3 : r.r10.toNat = 8) : syscallCall r = some .rtSigaction := by
  simp [syscallCall, Scc.Sem.Kernel.decode, Scc.Sem.Kernel.Nrs.x64, ha, h0, h2, h3,
    Scc.Sem.Kernel.sigpipe, Scc.Sem.Kernel.sigsetSize]
  exact h3

/-- `scc_rt_start`'s entry label. -/
abbrev startE : Label := ".Lscc_rt_start.entry"
/-- The handler's label. -/
abbrev sigign : Label := "scc_rt_sigign"
/-- The handler's address. -/
abbrev siSig : SI := .leaRip .rax sigign

/-- The state after the frame's setup. -/
def startS0 (lab : Label → Int64) (σ : AS) : AS := (arun lab xStart0 ⟨lab "scc_rt_start", ⟨0, []⟩, σ⟩).σ
/-- The state after the handler's address. -/
def startS1 (lab : Label → Int64) (σ : AS) : AS := siSig.step lab (startS0 lab σ)
/-- The state at the system call. -/
def startS2 (lab : Label → Int64) (σ : AS) : AS := (arun lab xStartArgs ⟨lab startE + 7, oS, startS1 lab σ⟩).σ
/-- **The state at the first call**: `rt_sigaction` returned 0. -/
def startS (lab : Label → Int64) (σ : AS) : AS := syscallStep (lab startE + 7 + 34 + 2) 0#64 (startS2 lab σ)

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `scc_rt_start`'s node at its entry label, after the frame's setup. -/
def xStartN1 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE, oS, fun σ1 c => ∃ σ, J σ c ∧ σ1 = startS0 lab σ⟩

/-- `scc_rt_start`'s node at the arguments, after the handler's address. -/
def xStartN2 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE + 7, oS, fun σ2 c => ∃ σ, J σ c ∧ σ2 = startS1 lab σ⟩

/-- `scc_rt_start`'s node at the system call. -/
def xStartN3 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab startE + 7 + 34, oS, fun σ3 c => ∃ σ, J σ c ∧ σ3 = startS2 lab σ⟩

/-- **`scc_rt_start`'s states up to its first call inside `W`**, none moved
by `K`: one obligation per node (the frame's setup, the handler's address,
the arguments, the system call). -/
structure XStartW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (J : AS → Ctl → Prop) : Prop where
  w0 : BlkW W K exe endPc R F ⟨(Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩ xStart0
  w1 : NodeW W K exe endPc R F (xStartN1 (Executable.labels exe).label J)
  w2 : BlkW W K exe endPc R F (xStartN2 (Executable.labels exe).label J) xStartArgs
  w3 : NodeW W K exe endPc R F (xStartN3 (Executable.labels exe).label J)

/-- The entry is inside the trivial predicate, with no outside moves. -/
theorem XStartW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {J : AS → Ctl → Prop} : XStartW (fun _ _ => True) (fun _ _ => False) exe endPc R F J :=
  ⟨BlkW.triv, NodeW.triv, BlkW.triv, NodeW.triv⟩

/-- **`scc_rt_start` up to its first call is one segment**, given its code:
from the entry (`%rsp` at offset 0) to a node at the call whose obligation
holds of `startS`. Its states lie in `W`, none moved by `K`
(`hW`, `XStartW`). -/
theorem start_segW {W : Frag isa} {K : State → State → Prop}
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label "scc_rt_start") xStart0)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label startE)
      [(siSig.toDir, 7)])
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label startE + 7) xStartArgs)
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label startE + 7 + 34)
      [(op64 .syscall, 2)])
    (hgap : (Executable.labels exe).label startE = (Executable.labels exe).label "scc_rt_start" + 8)
    {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hW : XStartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) := by
  let lab := (Executable.labels exe).label
  let n1 : ND := ⟨lab startE, oS, fun σ1 c => ∃ σ, J σ c ∧ σ1 = startS0 lab σ⟩
  let n2 : ND := ⟨lab startE + 7, oS, fun σ2 c => ∃ σ, J σ c ∧ σ2 = startS1 lab σ⟩
  let n3 : ND := ⟨lab startE + 7 + 34, oS, fun σ3 c => ∃ σ, J σ c ∧ σ3 = startS2 lab σ⟩
  have one : ∀ {P : Frag isa} {n : ND},
      SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW W K p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.seq (Q := At exe endPc R F n1) ?_ (SegW.seq (Q := At exe endPc R F n2) ?_
    (SegW.seq (Q := At exe endPc R F n3) ?_ ?_))
  · refine one (seg_ndW (by simp [xStart0]) xStart0_ok hF hR hlo hhi hc0 hW.w0
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, rfl⟩⟩)
    · rw [xStart0_run]; exact hgap
    · rw [xStart0_run]; rfl
  · refine one (si_ndW (si := siSig) rfl hF hc1 hW.w1
      fun σ c ⟨σ0, hJ, hσ⟩ => ⟨c, .refl c, .inl ⟨(), rfl, rfl, σ0, hJ, by rw [hσ]; rfl⟩⟩)
  · refine one (seg_ndW (by simp [xStartArgs]) xStartArgs_ok hF hR hlo hhi hc2 hW.w2
      fun σ c ⟨σ0, hJ, hσ⟩ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ0, hJ, by rw [hσ]; rfl⟩⟩)
    · rw [xStartArgs_run]
    · rw [xStartArgs_run]; rfl
  · refine (syscall_ndW (n := n3) (N := fun _ : Unit => nC) (E := fun e : Empty => e.elim) hK hF hc3 hW.w3
      (fun σ c ⟨σ0, hJ, hσ⟩ => ⟨.rtSigaction, ?_, (fun a h => nomatch h), (fun v hv => ?_)⟩) ?hok).mono_post
      fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
    case hok =>
      rintro s c σ call - ⟨σ0, -, rfl⟩ hcall
      have h : syscallCall (startS2 lab σ0).regs = some .rtSigaction := by
        apply syscallCall_rtSigaction <;> simp [startS2, xStartArgs_run] <;> rfl
      rw [h] at hcall
      cases hcall
      exact ⟨nofun, nofun, nofun, nofun⟩
    · subst hσ
      apply syscallCall_rtSigaction <;> simp [startS2, xStartArgs_run] <;> rfl
    · simp only [Scc.Sem.Kernel.results, List.mem_singleton] at hv
      subst hv hσ
      refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_⟩⟩
      · rw [hpc]; rfl
      · exact ho
      · exact hedge σ0 c hJ

/-- **`scc_rt_start` up to its first call is one segment**, given its code:
from the entry (`%rsp` at offset 0) to a node at the call whose obligation
holds of `startS`. -/
theorem start_seg (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hc0 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label "scc_rt_start") xStart0)
    (hc1 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label startE)
      [(siSig.toDir, 7)])
    (hc2 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label startE + 7) xStartArgs)
    (hc3 : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((Executable.labels exe).label startE + 7 + 34)
      [(op64 .syscall, 2)])
    (hgap : (Executable.labels exe).label startE = (Executable.labels exe).label "scc_rt_start" + 8)
    {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) :=
  (start_segW hK hF hR hlo hhi hc0 hc1 hc2 hc3 hgap hpc ho XStartW.triv hedge).toSeg

end Fn
/-! ## Code from the checks -/

/-- No bytes on. -/
theorem ofNat_zero' (a : Int64) : a + Int64.ofNat 0 = a := by
  rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]

/-- `m + n` bytes on: `n` more after `m`. -/
theorem ofNat_add' (a : Int64) (m n : Nat) : a + Int64.ofNat (m + n) = a + Int64.ofNat m + Int64.ofNat n := by
  rw [Int64.add_assoc, Int64.ofNat_add]

/-- **A function's prologue in `cells`**: the head right after the
function's label `fn`, the check's label `sc` right after it, the blocks
after `sc` (with their sizes) and the body's label `entry` after them. -/
def prologueIn (cells : List (Directive × Nat)) (fn sc entry : Label) (Z lim : Int64) (L : Label)
    (zl zf z1 z2 zs : Nat) (ps : List (Reg64 × Int64 × Nat)) : Bool :=
  labelGapB cells fn sc 4 && blockAtB cells fn 0 xHead && blockAtB cells sc 0 (xLea Z zl) &&
  blockAtB cells sc zl [(fsDir .r11 lim, zf)] && blockAtB cells sc (zl + zf) (xCmp L z1 z2) &&
  blockAtB cells sc (zl + zf + z1 + z2) (xFr Z zs ps) &&
  labelGapB cells sc entry (zl + zf + z1 + z2 + zs + szSum ps)

/-- **The `exit_group` tail at label `l` in `cells`**: `xExit k` right after
`l`, the system call after it. -/
def exitIn (cells : List (Directive × Nat)) (l : Label) (k : Int64) (z0 z1 z2 : Nat) : Bool :=
  blockAtB cells l 0 (xExit k z0 z1 z2) && blockAtB cells l (z0 + z1 + z2) [(op64 .syscall, 2)]

/-- **`scc_rt_start` up to its first call in `cells`**: the frame's setup,
the entry label right after it, the handler's address, the arguments and
the system call. -/
def startIn (cells : List (Directive × Nat)) : Bool :=
  labelGapB cells "scc_rt_start" startE 8 && blockAtB cells "scc_rt_start" 0 xStart0 &&
  blockAtB cells startE 0 [(siSig.toDir, 7)] && blockAtB cells startE 7 xStartArgs &&
  blockAtB cells startE 41 [(op64 .syscall, 2)]

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {cells : List (Directive × Nat)} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **The prologue is one segment** in any valid layout of cells with
`prologueIn`: `xPrologue_seg` from the function's label to a node at
`entry`. Its states lie in `W`, none moved by
`K` (`hW`, `XProW` at the function's label). -/
theorem prologue_seg_ofW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (hZ : 0 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oF Z) = true)
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label fn) Z lim L zl zf z1 z2 zs ps J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs Z (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs ps (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) := by
  simp only [prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, g1⟩ := hin
  have e0 := label_labelGapB hp g0
  have e1 := label_labelGapB hp g1
  have h4 : (_root_.Executable.labels exe).label fn + 1 + 3 = (_root_.Executable.labels exe).label sc := by
    rw [e0, Int64.add_assoc]; rfl
  refine xPrologue_segW hZ hF hR hlo hhi hps (code_field hp hend b0 (ofNat_zero' _)) (code_field hp hend b1 ?_)
    (code_field hp hend b2 ?_) (code_field hp hend b3 ?_) (code_field hp hend b4 ?_) ?_ ho hW hedge
  · rw [h4, ofNat_zero']
  · rw [h4]
  · rw [h4, ofNat_add']
  · rw [h4, ofNat_add', ofNat_add', ofNat_add']
  · rw [hpc, e1, h4, ofNat_add', ofNat_add', ofNat_add', ofNat_add', ofNat_add']

/-- **The prologue is one segment** in any valid layout of cells with
`prologueIn`: `xPrologue_seg` from the function's label to a node at
`entry`. -/
theorem prologue_seg_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {fn sc entry : Label}
    {Z lim : Int64} {L : Label} {zl zf z1 z2 zs : Nat} {ps : List (Reg64 × Int64 × Nat)}
    (hin : prologueIn cells fn sc entry Z lim L zl zf z1 z2 zs ps = true)
    {J : AS → Ctl → Prop} {nb : ND} (hZ : 0 ≤ Z.toInt) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -8 - Z.toInt) (hhi : 0 ≤ R.hi)
    (hps : ∀ q ∈ ps, offOk (-8 - Z.toInt) 0 (-8 + q.2.1.toInt) = true)
    (hpc : nb.pc = (_root_.Executable.labels exe).label entry)
    (ho : SO.le nb.o (oF Z) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + lim.toBitVec).toNat ∧ ms.mp ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + lim.toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + lim.toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - Z.toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs Z (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs ps (xS1 σ).slot → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label fn, ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (prologue_seg_ofW hp hend hin hZ hF hR hlo hhi hps hpc ho XProW.triv hedge).toSeg

/-- **The `exit_group` tail does not return** in any valid layout of cells
with `exitIn`: `xExitTail_seg` from a node at its label. Its states lie in `W`, none
moved by `K` (`hW`, `XExitW`). -/
theorem exitTail_seg_ofW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {l : Label} {k : Int64}
    {z0 z1 z2 : Nat} (hin : exitIn cells l k z0 z1 z2 = true) {n : ND} {Q : Frag isa} {sp b : Int}
    (hpc : n.pc = (_root_.Executable.labels exe).label l) (hno : n.o = ⟨sp, [(.rbp, b)]⟩)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) {lo hi : Int}
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : offOk lo hi (b + k.toInt) = true)
    (hW : XExitW W K exe endPc R F n sp b k z0 z1 z2)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2,
      ⟨sp, [(.rbp, b)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  simp only [exitIn, Bool.and_eq_true] at hin
  refine xExitTail_segW hno hK hF hR hlo hhi hk (code_field hp hend hin.1 ?_) (code_field hp hend hin.2 ?_) hW hok
  · rw [hpc, ofNat_zero']
  · rw [hpc, ofNat_add', ofNat_add']

/-- **The `exit_group` tail does not return** in any valid layout of cells
with `exitIn`: `xExitTail_seg` from a node at its label. -/
theorem exitTail_seg_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) {l : Label} {k : Int64}
    {z0 z1 z2 : Nat} (hin : exitIn cells l k z0 z1 z2 = true) {n : ND} {Q : Frag isa} {sp b : Int}
    (hpc : n.pc = (_root_.Executable.labels exe).label l) (hno : n.o = ⟨sp, [(.rbp, b)]⟩)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) {lo hi : Int}
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hk : offOk lo hi (b + k.toInt) = true)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat z0 + Int64.ofNat z1 + Int64.ofNat z2,
      ⟨sp, [(.rbp, b)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (exitTail_seg_ofW hp hend hin hpc hno hK hF hR hlo hhi hk XExitW.triv hok).toSeg

/-- **`scc_rt_start` up to its first call is one segment** in any valid
layout of cells with `startIn`: `start_seg`. Its states lie in `W`, none moved by `K`
(`hW`, `XStartW`). -/
theorem start_seg_ofW {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : startIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hW : XStartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) := by
  simp only [startIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, c0, c1, c2, c3⟩ := hin
  refine start_segW hK hF hR hlo hhi (code_field hp hend c0 (ofNat_zero' _)) (code_field hp hend c1 (ofNat_zero' _))
    (code_field hp hend c2 rfl) (code_field hp hend c3 ?_) (label_labelGapB hp g0) hpc ho hW hedge
  rw [Int64.add_assoc]; rfl

/-- **`scc_rt_start` up to its first call is one segment** in any valid
layout of cells with `startIn`: `start_seg`. -/
theorem start_seg_of {kp : Nat} (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : startIn cells = true)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) :=
  (start_seg_ofW hp hend hin hK hF hR hlo hhi hpc ho XStartW.triv hedge).toSeg

end Fn

end Spike.Lib.X64.Flow

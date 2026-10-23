/-
**AArch64 rows for label addresses, unscaled accesses and system
instructions, on `isaLSE2`.**

The rows `Lower/EventsA64.lean` lacks for a whole compiled program (scc's
runtime): in the same shape (`CellAt st d sz` the only hypothesis on the
cell), generic over registers, immediates, labels, pc and layout.

- **Label addresses.** `labelAddr st L` is the address the executable's
  labels give `L` (a code label, or a data symbol placed as a label cell).
  `exec_adrp_label`: `adrp Xd, L` writes `L`'s 4 KiB page;
  `exec_add_lo12`: `add Xd, Xn, :lo12:L` adds `L`'s low 12 bits;
  `page_add_lo12`: the two add up to `L`'s address.
- **Stack-pointer arithmetic.** `exec_add_e_imm`: `add Xd|SP, Xn|SP, #n`
  with the immediate evaluated (the stack switch `add sp, Xn, #0`).
- **Unscaled accesses** (`ldur`/`stur`, a separate constructor from
  `ldr`/`str`): `exec_ldur`/`exec_stur` (address unmapped: one plain 8-byte
  event), `_agrees`, `_mapped` (no event), as for `ldr`/`str`.
- **System instructions.** `exec_nop`, `exec_mrs`, `exec_msr` (register
  moves, no event); `exec_svc`: `svc #imm` faults with
  `pendingSyscallMsg imm`; `execCert_svc`: under `execLSE2Cert results` it is
  a choice over `results (svcInfo st imm)`, each branch writing the result to
  `X0` and continuing after the `svc` (the state a kernel model's return
  gives, written as one: `X0 := UInt64.ofNat r.toNat`).
- **The cell itself.** `CellAt.directive`: the directive at the pc;
  `CellAt.dirSize`: the cells at the pc occupy `sz` bytes in all (a kernel
  model's next pc is `pc + sz`).
-/
import Kraken.Promising.Lower.EventsA64

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-! ## The cell -/

section Cell

variable {st : State} {d : Directive} {sz : Nat}

/-- **The directive at a cell's pc** is the cell's. -/
theorem CellAt.directive (h : CellAt st d sz) : st.directive = some d := by
  obtain ⟨_, _, rest, hcode⟩ := h
  unfold State.directive
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress st.exe st.st.2) =
      Kraken.Executable.codeAt st.exe st.st.2 from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- **The cells at a cell's pc occupy `sz` bytes**: the labels in front of
the directive occupy none. -/
theorem CellAt.dirSize (h : CellAt st d sz) :
    ((Kraken.Executable.directivesAtAddress st.exe st.st.2).map (·.2)).sum = sz := by
  obtain ⟨hv, _, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  rw [hat, List.map_append, List.sum_append]
  clear hat
  have h0 : (ls.map (·.2)).sum = 0 := by
    induction ls with
    | nil => rfl
    | cons c cs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [(hls c (List.mem_cons_self ..)).2, ih (fun c' hc' => hls c' (List.mem_cons_of_mem _ hc'))]
  simp [h0]

/-- **`execLSE2Cert`'s tree at a cell without a FEAT_LSE2 reading**: the
translation of `Directive.interp` by `toEvCert results`. -/
theorem execLSE2Cert_of_cellAt_free (results : SyscallInfo → List (BitVec 64)) (h : CellAt st d sz)
    (hf : d.LSE2Free) :
    execLSE2Cert results st = some ((toEvCert results st.decls (@Directive.interp (_root_.Executable.labels st.exe) d
      st.st.1 (.mk st.st.2 (st.st.2 + .ofNat sz)) (nextS st sz) jmpS)).map fun s => { st with st := s }) := by
  have hdir := h.directive
  obtain ⟨hv, hne, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  have hcell : st.cell = some (d, sz) := by
    unfold State.cell
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress st.exe st.st.2) =
        Kraken.Executable.codeAt st.exe st.st.2 from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  letI := Executable.labels st.exe
  have hl : lse2Effects st = none := by
    unfold lse2Effects
    simp only [hcell]
    exact Directive.interpLSE2?_none_of_free hf _ _ _
  have hx : st.isCaspX = false := by
    simp only [State.isCaspX, hdir]
    revert hf; unfold Directive.isCaspX; split <;> simp [Directive.LSE2Free]
  simp only [execLSE2Cert, hdir, hne, hl, hx, execCert, Option.isNone_some, Bool.or_false,
    Bool.false_eq_true, ite_false]
  congr 2
  unfold Executable.step
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

end Cell

/-- Read a register or system cell (no memory unfolding). -/
local macro "cellR" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free $hc trivial]
  simp only [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, MachineData.setRegOrZr,
    MachineData.setRegOrSp, $ts,*]
  try rfl))

/-- Read a memory cell through `execLSE2_of_cellAt_free` and unfold it. -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free $hc trivial]
  simp [Directive.interp, Instr.interp, Operation.interp, UnscaledAddrExpr.interpLoad,
    UnscaledAddrExpr.interpStore, UnscaledAddrExpr.checkSPAlignment, UnscaledAddrExpr.eval,
    MachineData.load, MachineData.store, MachineData.loadK, MachineData.storeK, RegOrSp.interpBase,
    toEv, EvTree.map, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-! ## Label addresses -/

/-- The address the executable's labels give `L`. -/
abbrev labelAddr (st : State) (L : Label) : Int64 := (_root_.Executable.labels st.exe).label L

/-- A 64-bit vector through `Int64.ofNat` of its value is itself. -/
theorem toBitVec_ofNat_toNat (v : BitVec 64) : (Int64.ofNat v.toNat).toBitVec = v := by
  simp

/-- An `Int64` read back from its integer value is its bit vector. -/
theorem ofInt_toInt_int64 (x : Int64) : BitVec.ofInt 64 x.toInt = x.toBitVec := by
  rw [Int64.toInt, BitVec.ofInt_toInt]

/-- The `:lo12:` immediate, read back as 64 bits, is the low 12 bits. -/
theorem ofInt_lo12 (v : BitVec 64) :
    BitVec.ofInt 64 (Int64.ofNat (v &&& 0xFFF#64).toNat).toInt = v &&& 0xFFF#64 := by
  rw [ofInt_toInt_int64]; simp

/-- **A page plus its low 12 bits is the address.** -/
theorem page_add_lo12 (a : BitVec 64) : (a &&& ~~~0xFFF#64) + (a &&& 0xFFF#64) = a := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · rw [← BitVec.and_or_distrib_left, BitVec.or_comm, BitVec.or_not_self, BitVec.and_allOnes]
  · ext i hi
    simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
    cases (0xFFF#64)[i] <;> simp

section Labels

variable {st : State} {sz : Nat}

/-- **`adrp Xd, L`**: no event; `Xd` is `L`'s 4 KiB page. -/
theorem exec_adrp_label {dst : RegOrZr .W64} {L : Label}
    (hc : CellAt st (.instr ⟨.W64, .ADRP dst (.label L)⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst ((labelAddr st L).toBitVec &&& ~~~0xFFF#64) })) := by
  cellR hc [ConstExpr.interp, ofInt_toInt_int64]

/-- **`add Xd, Xn, :lo12:L`**: no event; `Xd := Xn + ` `L`'s low 12 bits. -/
theorem exec_add_lo12 {dst src : RegOrSp .W64} {L : Label}
    (hc : CellAt st (.instr ⟨.W64, .ADD_e dst src (.imm ⟨.lo12 (.label L), .S0⟩)⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrSp dst (st.st.1.regs.getRegOrSp src + ((labelAddr st L).toBitVec &&& 0xFFF#64)) })) := by
  cellR hc [ExtOrImmReg.interp, ConstExpr.interp, ofInt_toInt_int64, toBitVec_ofNat_toNat]

end Labels

/-! ## Stack-pointer arithmetic -/

section SpArith

variable {st : State} {sz : Nat}

/-- **`add Xd|SP, Xn|SP, #n`** (unshifted immediate; `add sp, Xn, #0` is a
stack switch, `mov sp, Xn`): no event; `Xd := Xn + n`. -/
theorem exec_add_e_imm {dst src : RegOrSp .W64} {n : Int64}
    (hc : CellAt st (.instr ⟨.W64, .ADD_e dst src (.imm ⟨.int64 n, .S0⟩)⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrSp dst (st.st.1.regs.getRegOrSp src + n.toBitVec) })) := by
  cellR hc [ExtOrImmReg.interp, ConstExpr.interp, ofInt_toInt_int64]

end SpArith

/-! ## Unscaled accesses -/

section Unscaled

variable {st : State} {sz : Nat}

/-- **`ldur Xt, [Xn, #i]`**, address unmapped in `dmem`: one plain 8-byte
load. -/
theorem exec_ldur {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDUR dst ⟨.low (.reg n) .W64, .int64 i⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  cell hc [ha, hdm]

/-- `ldur` at an agreeing address: the load of `⟨a, 8⟩`. -/
theorem exec_ldur_agrees {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDUR dst ⟨.low (.reg n) .W64, .int64 i⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) (hag : st.decls.AgreesAt a 8) :
    isaLSE2.exec st = some (.load .plain false ⟨a, 8⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  rw [exec_ldur hc ha hdm, access_agrees hag]

/-- `ldur` at an address mapped in `dmem`: no event. -/
theorem exec_ldur_mapped {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDUR dst ⟨.low (.reg n) .W64, .int64 i⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (BitVec.ofInt 64 j) })) := by
  cell hc [ha, hdm]

/-- **`stur Xt, [Xn, #i]`**, address unmapped: one plain 8-byte store. -/
theorem exec_stur {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STUR src ⟨.low (.reg n) .W64, .int64 i⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l => .store .plain false l
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cell hc [ha, hdm]

/-- `stur` at an agreeing address: the store to `⟨a, 8⟩`. -/
theorem exec_stur_agrees {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STUR src ⟨.low (.reg n) .W64, .int64 i⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) (hag : st.decls.AgreesAt a 8) :
    isaLSE2.exec st = some (.store .plain false ⟨a, 8⟩
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_stur hc ha hdm, access_agrees hag]

/-- `stur` at a mapped address: no event (`dmem` updated). -/
theorem exec_stur_mapped {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STUR src ⟨.low (.reg n) .W64, .int64 i⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with dmem := Mem.storeInt st.st.1.dmem a 8 (st.st.1.regs.getRegOrZr src).toInt })) := by
  cell hc [ha, hdm]

end Unscaled

/-! ## System instructions -/

section Sys

variable {st : State} {sz : Nat}

/-- **`nop`**: no event, nothing changes but the pc. -/
theorem exec_nop (hc : CellAt st (.instr ⟨.W64, .NOP⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz st.st.1)) := by
  cellR hc []

/-- **`mrs Xd, tpidr_el0`**: no event; `Xd` is the thread pointer. -/
theorem exec_mrs {dst : RegOrZr .W64} (hc : CellAt st (.instr ⟨.W64, .MRS dst .TPIDR_EL0⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst st.st.1.regs.TPIDR_EL0.toBitVec })) := by
  cellR hc [Reg64s.getSysReg]

/-- **`msr tpidr_el0, Xn`**: no event; the thread pointer is `Xn`. -/
theorem exec_msr {src : RegOrZr .W64} (hc : CellAt st (.instr ⟨.W64, .MSR .TPIDR_EL0 src⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := { st.st.1.regs with TPIDR_EL0 := UInt64.ofBitVec (st.st.1.regs.getRegOrZr src) } })) := by
  cellR hc [Reg64s.setSysReg]

/-- The system call `svc #imm` asks for at `st`: the immediate, `X8` and
`X0`–`X5` (`MachineData.pendingSyscall`). -/
abbrev svcInfo (st : State) (imm : Nat) : SyscallInfo :=
  let x (r : XReg) : BitVec 64 := (st.st.1.regs.getXReg r).toBitVec
  { imm, num := x .X8, args := [x .X0, x .X1, x .X2, x .X3, x .X4, x .X5] }

/-- The state after a system call returns `r`: `X0 := r`, every other
register and the private memory unchanged, the pc after the `svc`. -/
abbrev svcRet (st : State) (sz : Nat) (r : BitVec 64) : State :=
  after st sz { st.st.1 with regs := { st.st.1.regs with X0 := UInt64.ofNat r.toNat } }

/-- **`svc #imm`** faults with the pending-system-call message: no event. -/
theorem exec_svc {imm : Nat} (hc : CellAt st (.instr ⟨.W64, .SVC imm⟩) sz) :
    isaLSE2.exec st = some (.fault (pendingSyscallMsg imm)) := by
  cellR hc [MachineData.pendingSyscall]

/-- Kraken's write of `X0` is the record update a kernel model writes. -/
theorem setXReg_X0 (regs : Reg64s) (r : BitVec 64) :
    regs.setXReg .X0 r = { regs with X0 := UInt64.ofNat r.toNat } := by
  simp only [Reg64s.setXReg, UInt64.ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- **`svc #imm` under certification** (`execLSE2Cert results`): a choice
over the results `results` allows the call, each branch continuing after the
`svc` with the result in `X0`. -/
theorem execCert_svc (results : SyscallInfo → List (BitVec 64)) {imm : Nat}
    (hc : CellAt st (.instr ⟨.W64, .SVC imm⟩) sz) :
    execLSE2Cert results st = some (.choose (results (svcInfo st imm)).length fun i =>
      .done (svcRet st sz (results (svcInfo st imm))[i])) := by
  rw [execLSE2Cert_of_cellAt_free results hc trivial]
  simp only [Directive.interp, Instr.interp, Operation.interp, MachineData.pendingSyscall, toEvCert,
    EvTree.map, setXReg_X0]

end Sys

end Kraken.Promising.Lower.A64

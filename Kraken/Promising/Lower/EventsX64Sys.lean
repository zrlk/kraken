/-
**x64 rows for label addresses, `%fs:` loads, system instructions, shifts by
`%cl` and 32-bit `xor`, on `X64.isa`.**

The rows `Lower/EventsX64.lean` and `Lower/EventsX64Flags.lean` lack for a
whole compiled program (scc's runtime), in the same shape (`CellAt st d sz`
the only hypothesis on the cell).

- **Label addresses.** `eaddr_label_rip`: the effective address of
  `L(%rip)` is `labelAddr st L`; `exec_lea_rip_label`: `leaq L(%rip), r`
  writes it.
- **`%fs:` loads** (`movq %fs:m, r`, `Operation.movfs`): the address is
  `fsAddr st sz m` (the thread pointer plus the operand's effective
  address); `exec_movfs_load` (unmapped: one plain 8-byte load), `_agrees`,
  `_mapped` (no event), as for `exec_load`.
- **System instructions.** `exec_nop` (no event); `exec_ud2` (the fault
  `ud2Msg`); `exec_syscall`: `syscall` faults with `pendingSyscallMsg`;
  `execCert_syscall`: under `execCert results` it is a choice over
  `results (syscallInfo st sz)`, each branch writing `rax`, `rcx`, `r11`
  and continuing after the `syscall` (`syscallRet`, written as a kernel
  model writes it).
- **The cell itself.** `CellAt.directive`, `CellAt.dirSize` (as on AArch64).
- **Shifts by `%cl`.** `silent_shl_cl`/`silent_shr_cl`: with the count
  `clCount st` (the low 8 bits of `rcx`, masked to 6) nonzero, a silent tree
  whose leaves have the shifted value and some flags (the flags are partly
  undefined); `exec_shl_cl_zero`/`exec_shr_cl_zero`: with count 0, nothing
  changes.
- **32-bit `xor`** (`xorl r32, r32'`): `exec_xor_rr32`, a choice of `AF`;
  the 32-bit result is zero-extended into the 64-bit register.
  `exec_xor_rr32_self`: `xorl r, r` zeroes the register.
-/
import Kraken.Promising.Lower.EventsX64Flags

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64

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

/-- **`execCert`'s tree at a cell**: the translation of the cell's
interpretation by `toEvCert results`. -/
theorem execCert_of_cellAt (results : SyscallInfo → List SyscallRet) (h : CellAt st d sz) :
    execCert results st = some ((toEvCert results st.decls (@Directive.interp (_root_.Executable.labels st.exe) d
      st.st.1 (rangeOf st sz) (fun s' => .done (s', st.st.2 + .ofNat sz))
      (fun pc s' => .done (s', pc)))).map fun s => { st with st := s }) := by
  have hdir := h.directive
  obtain ⟨hv, hne, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  simp only [execCert, hdir, Option.isNone_some, Bool.or_false, hne, Bool.false_eq_true, ↓reduceIte]
  congr 2
  unfold Executable.step
  letI := Executable.labels st.exe
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

end Cell

/-- Read the cell through `exec_of_cellAt` and unfold it (`EventsX64.lean`'s
local `cell`, repeated, with the segment-relative operands). -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  try simp only [rspOf, Reg64s.get64] at *
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    Operand.interpSeg, RegOrMem.interpSeg, AddrExpr.interpSeg, MachineData.setSeg,
    MachineData.set, MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, Width.bytesv, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-! ## Label addresses -/

section Labels

variable {st : State} {sz : Nat}

/-- **The effective address of `L(%rip)`** is the address of `L`, at any
cell. -/
theorem eaddr_label_rip (st : State) (sz : Nat) (L : Label) :
    eaddr st sz { base := some .rip, idx := none, disp := .sub (.label L) .after_current_instruction }
      = (labelAddr st L).toBitVec := by
  simp only [eaddr, AddrExpr.interp, ConstExpr.interp, BitVec.setWidth_eq]
  have h (x y : BitVec 64) : BitVec.ofInt 64 (x.toInt + 0 + y.toInt) = x + y := by
    rw [Int.add_zero, BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  refine (h _ _).trans ?_
  rw [Int64.toBitVec_sub, BitVec.add_comm, BitVec.sub_add_cancel]

/-- **`leaq L(%rip), r64`**: no event; `r` is `L`'s address. -/
theorem exec_lea_rip_label {d : Reg .W64} {L : Label}
    (hc : CellAt st (op64 (.lea d { base := some .rip, idx := none, disp := .sub (.label L) .after_current_instruction })) sz) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set d (labelAddr st L).toBitVec })) := by
  rw [exec_lea hc, eaddr_label_rip]

end Labels

/-! ## `%fs:` loads -/

section Fs

variable {st : State} {sz : Nat}

/-- The address of the `%fs:`-relative operand `m` at the cell: the thread
pointer plus `m`'s effective address. -/
abbrev fsAddr (st : State) (sz : Nat) (m : AddrExpr) : BitVec 64 :=
  st.st.1.regs.fsBase.toBitVec + eaddr st sz m

/-- **`movq %fs:m, r64`**, address unmapped in `dmem`: one plain 8-byte
load. -/
theorem exec_movfs_load {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.movfs (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : fsAddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth 64) })) := by
  simp only [fsAddr, eaddr, BitVec.setWidth_eq] at ha
  cell hc [ha, hdm]

/-- `movq %fs:m, r64` at an agreeing address: the load of `⟨a, 8⟩`. -/
theorem exec_movfs_load_agrees {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.movfs (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : fsAddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none)
    (hag : st.decls.AgreesAt a 8) :
    isa.exec st = some (.load .plain false ⟨a, 8⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth 64) })) := by
  rw [exec_movfs_load hc ha hdm, access_agrees hag]

/-- `movq %fs:m, r64` at an address mapped in `dmem`: no event. -/
theorem exec_movfs_load_mapped {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.movfs (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : fsAddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set r (BitVec.ofInt 64 j) })) := by
  simp only [fsAddr, eaddr, BitVec.setWidth_eq] at ha
  cell hc [ha, hdm]

end Fs

/-! ## System instructions -/

section Sys

variable {st : State} {sz : Nat}

/-- **`nop`** (any length): no event, nothing changes but the pc. -/
theorem exec_nop {n : Nat} (hc : CellAt st (op64 (.nop n)) sz) :
    isa.exec st = some (.done (after st sz st.st.1)) := by
  cell hc []

/-- **`ud2`** faults with `ud2Msg`: no event. -/
theorem exec_ud2 (hc : CellAt st (op64 .ud2) sz) : isa.exec st = some (.fault ud2Msg) := by
  cell hc []

/-- **`syscall`** faults with the pending-system-call message: no event. -/
theorem exec_syscall (hc : CellAt st (op64 .syscall) sz) : isa.exec st = some (.fault pendingSyscallMsg) := by
  cell hc [MachineData.pendingSyscall]

/-- The system call `syscall` asks for at the cell: `rax`, the arguments
`rdi`, `rsi`, `rdx`, `r10`, `r8`, `r9`, and the address after the
instruction (`MachineData.pendingSyscall`). -/
abbrev syscallInfo (st : State) (sz : Nat) : SyscallInfo :=
  let g := st.st.1.regs.get64
  { num := g .rax, args := [g .rdi, g .rsi, g .rdx, g .r10, g .r8, g .r9],
    nextPc := (st.st.2 + .ofNat sz).toBitVec }

/-- The state after a system call returns `r`: `rax`, `rcx`, `r11` from
`r`, every other register and the private memory unchanged, the pc after
the `syscall`. -/
abbrev syscallRet (st : State) (sz : Nat) (r : SyscallRet) : State :=
  after st sz { st.st.1 with regs := { st.st.1.regs with
    rax := UInt64.ofNat r.rax.toNat, rcx := UInt64.ofNat r.rcx.toNat, r11 := UInt64.ofNat r.r11.toNat } }

/-- **`syscall` under certification** (`execCert results`): a choice over
the results `results` allows the call, each branch continuing after the
`syscall` with `rax`, `rcx` and `r11` written. -/
theorem execCert_syscall (results : SyscallInfo → List SyscallRet) (hc : CellAt st (op64 .syscall) sz) :
    execCert results st = some (.choose (results (syscallInfo st sz)).length fun i =>
      .done (syscallRet st sz (results (syscallInfo st sz))[i])) := by
  rw [execCert_of_cellAt results hc]
  simp [Directive.interp, Instr.interp, Operation.interp, MachineData.pendingSyscall, toEvCert, EvTree.map,
    Reg64s.set64, UInt64.ofNat, BitVec.ofNat_toNat, syscallInfo, syscallRet]
  rfl

end Sys

/-! ## Shifts by `%cl` -/

section ShiftCl

variable {st : State} {sz : Nat}

/-- The count of a shift by `%cl`: the low 8 bits of `rcx`, masked to 6 (a
64-bit operand). -/
abbrev clCount (st : State) : Nat := (st.st.1.regs.rcx.toBitVec.take 8).toNat &&& 63

theorem clCount_lt (st : State) : clCount st < 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- **`shl r64, %cl`, flags arbitrary** (count `n = clCount st`, nonzero): no
event; `d := a <<< n`. -/
theorem silent_shl_cl {d : Reg .W64} (hc : CellAt st (op64 (.shl (.reg d) .cl)) sz) (hk : clCount st ≠ 0) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d (st.st.1.regs.get d <<< clCount st), status := fl }) t := by
  have hlt := clCount_lt st
  have hk' : (clCount st == 0) = false := by simpa using hk
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [clCount] at hk' hlt
  by_cases h1 : (clCount st == 1) = true <;> simp only [clCount, Bool.not_eq_true] at h1 <;>
    simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, h1,
      RegOrMem.interp, ShiftCountExpr.interpMasked, ShiftCountExpr.interp, toEv, EvTree.map, SilentTree]

/-- **`shr r64, %cl`, flags arbitrary** (count `n = clCount st`, nonzero): no
event; `d := a.ushiftRight n`. -/
theorem silent_shr_cl {d : Reg .W64} (hc : CellAt st (op64 (.shr (.reg d) .cl)) sz) (hk : clCount st ≠ 0) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d ((st.st.1.regs.get d).ushiftRight (clCount st)), status := fl }) t := by
  have hlt := clCount_lt st
  have hk' : (clCount st == 0) = false := by simpa using hk
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [clCount] at hk' hlt
  by_cases h1 : (clCount st == 1) = true <;> simp only [clCount, Bool.not_eq_true] at h1 <;>
    simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, h1,
      RegOrMem.interp, ShiftCountExpr.interpMasked, ShiftCountExpr.interp, toEv, EvTree.map, SilentTree]

/-- **`shl r64, %cl` with count 0**: no event, nothing changes. -/
theorem exec_shl_cl_zero {d : Reg .W64} (hc : CellAt st (op64 (.shl (.reg d) .cl)) sz) (hk : clCount st = 0) :
    isa.exec st = some (.done (after st sz st.st.1)) := by
  simp only [clCount] at hk
  cell hc [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, hk]

/-- **`shr r64, %cl` with count 0**: no event, nothing changes. -/
theorem exec_shr_cl_zero {d : Reg .W64} (hc : CellAt st (op64 (.shr (.reg d) .cl)) sz) (hk : clCount st = 0) :
    isa.exec st = some (.done (after st sz st.st.1)) := by
  simp only [clCount] at hk
  cell hc [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, hk]

end ShiftCl

/-! ## 32-bit `xor` -/

section Xor32

variable {st : State} {sz : Nat}

/-- A 32-bit, 64-bit-addressed instruction. -/
abbrev op32 (o : Operation .W32) : Directive := .instr (.regular .W64 .W32 o)

/-- **`xorl r32, r32'`**: no event; `d := d ^^^ s` (zero-extended into the
64-bit register), the flags of the 32-bit result, a choice of `AF`. -/
theorem exec_xor_rr32 {d s : Reg .W32} (hc : CellAt st (op32 (.xor (.reg d) (.reg s))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (after st sz { st.st.1 with
        regs := st.st.1.regs.set d (st.st.1.regs.get d ^^^ st.st.1.regs.get s),
        status := .from_result (st.st.1.regs.get d ^^^ st.st.1.regs.get s)
          { cf := false, af := i.val == 1, of := false } })) := by
  cell hc []

/-- **`xorl r32, r32`**: no event; the register is zeroed, the flags those of
0, a choice of `AF`. -/
theorem exec_xor_rr32_self {d : Reg .W32} (hc : CellAt st (op32 (.xor (.reg d) (.reg d))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (after st sz { st.st.1 with
        regs := st.st.1.regs.set d 0#32,
        status := .from_result 0#32 { cf := false, af := i.val == 1, of := false } })) := by
  rw [exec_xor_rr32 hc, BitVec.xor_self]

end Xor32

end Kraken.Promising.Lower.X64

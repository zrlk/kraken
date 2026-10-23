/-
x64 label addresses, `%fs:` loads, system instructions, shifts by `%cl` and
32-bit `xor` (`Lower/EventsX64Sys.lean`) on a `mkState` thread with a data
symbol `tab` at `0x200000`:

    leaq tab(%rip), %rax
    movq %fs:8, %rcx
    shlq %cl, %rax
    xorl %edx, %edx
    nop
    syscall
    ud2

`leaq` gives `tab`'s address (`step_lea`); the `%fs:` load reads the word at
the thread pointer plus 8 from the private memory (`step_movfs`); the shift
by `%cl` and the `xorl` are silent steps; `syscall` faults under
`isa.exec` and is a choice over the given results under `execCert`
(`step_syscall`, `step_syscall_cert`); `ud2` faults (`step_ud2`).
-/
import Kraken.X64.Parser
import Kraken.Promising.X64Sized
import Kraken.Promising.Lower.CodeSegX64Syms
import Kraken.Promising.Lower.EventsX64Sys

namespace Kraken.X64.Examples.LabelSys

open Kraken.X64.Parser
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- The program. -/
def prog : Program := parse("
  leaq tab(%rip), %rax
  movq %fs:8, %rcx
  shlq %cl, %rax
  xorl %edx, %edx
  nop
  syscall
  ud2
")

/-- The data symbol. -/
abbrev syms : List (String × BitVec 64) := [("tab", 0x200000#64)]

variable (regs : Reg64s) (dmem : DataMem)

/-- Thread 0 with the symbol. -/
abbrev st : State := mkState 0 prog regs syms dmem

/-- Thread 0's base address. -/
abbrev base : Int64 := Int64.ofNat 0x100000

/-- The code cells, one byte per instruction. -/
def cells : List (Directive × Nat) := prog.map fun d => (d, 1)

/-- The cells of the executable: the code, the padding up to the symbol, the
label. -/
def exeCells : List (Directive × Nat) := cells ++ [(.byteArray (.mk #[]), 0x200000 - 0x100007), (.label "tab", 0)]

theorem st_exe : (st regs dmem).exe = (base, exeCells) := rfl

theorem sizeCheck_exe : SizeCheck base exeCells [("tab", 0x100000)] = true := by decide

theorem validLayout_st : Kraken.Executable.ValidLayout (st regs dmem).exe := by
  rw [st_exe]; exact validLayout_of_sizeCheck sizeCheck_exe

/-- **`tab` resolves to its address**, in every state of the thread. -/
theorem tab_addr (m : MachineData) (pc : Int64) :
    labelAddr { st regs dmem with st := (m, pc) } "tab" = base + .ofNat 0x100000 := by
  rw [labelAddr]; exact label_of_sizeCheck' sizeCheck_exe (by decide)

/-- **Instruction `j` is a `CellAt`** at `base + j`, in any machine data. -/
theorem cellAt_run (m : MachineData) {j : Nat} {i : Instr} {sz : Nat} (hd : cells[j]? = some (.instr i, sz)) :
    CellAt { st regs dmem with st := (m, base + .ofNat ((cells.take j).map (·.2)).sum) } (.instr i) sz := by
  obtain ⟨ds, h1, h2⟩ := mkState_split 0 prog regs syms dmem [] {}
  have h0 : Kraken.Executable.codeAt (st regs dmem).exe base = cells ++ exeCells.drop 7 := by
    rw [st_exe, show base = (base, exeCells).1 from rfl, Kraken.Executable.codeAt_start]; rfl
  exact cellAt_segment_instr (validLayout_st regs dmem) h1 h2
    (mkState_endPc_code 0 prog regs syms dmem [] {}) h0 (by decide) hd m

/-- The state at instruction `j`, with machine data `m`. -/
abbrev at_ (m : MachineData) (j : Nat) : State := { st regs dmem with st := (m, base + .ofNat j) }

/-- `cellAt_run` at `at_`: the cells before instruction `j` are `j` bytes. -/
theorem cellAt_at (m : MachineData) {j : Nat} {i : Instr} {sz : Nat} (hd : cells[j]? = some (.instr i, sz))
    (hj : ((cells.take j).map (·.2)).sum = j) : CellAt (at_ regs dmem m j) (.instr i) sz := by
  have := cellAt_run regs dmem m hd
  rwa [hj] at this

/-- **`leaq tab(%rip), %rax`**: no event; `rax` is `tab`'s address. -/
theorem step_lea (m : MachineData) :
    isa.exec (at_ regs dmem m 0) = some (.done (after (at_ regs dmem m 0) 1
      { m with regs := m.regs.set (.low .rax .W64) 0x200000#64 })) := by
  rw [exec_lea_rip_label (cellAt_at regs dmem m (j := 0) rfl rfl), tab_addr]
  rfl

/-- **`movq %fs:8, %rcx`** with the word `w` at the thread pointer plus 8 in
the private memory: no event; `rcx := w`. -/
theorem step_movfs (m : MachineData) {w : Int} (hw : Mem.loadInt m.dmem (m.regs.fsBase.toBitVec + 8#64) 8 = some w) :
    isa.exec (at_ regs dmem m 1) = some (.done (after (at_ regs dmem m 1) 1
      { m with regs := m.regs.set (.low .rcx .W64) (BitVec.ofInt 64 w) })) :=
  exec_movfs_load_mapped (cellAt_at regs dmem m (j := 1) rfl rfl)
    (by simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp]) hw

/-- **`syscall`** faults under `isa.exec`. -/
theorem step_syscall (m : MachineData) :
    isa.exec (at_ regs dmem m 5) = some (.fault pendingSyscallMsg) :=
  exec_syscall (cellAt_at regs dmem m (j := 5) rfl rfl)

/-- **`syscall` under certification**: one branch per result, each with
`rax`, `rcx`, `r11` written and the pc after the `syscall`. -/
theorem step_syscall_cert (results : SyscallInfo → List SyscallRet) (m : MachineData) :
    execCert results (at_ regs dmem m 5) = some (.choose (results (syscallInfo (at_ regs dmem m 5) 1)).length
      fun i => .done (syscallRet (at_ regs dmem m 5) 1 (results (syscallInfo (at_ regs dmem m 5) 1))[i])) :=
  execCert_syscall results (cellAt_at regs dmem m (j := 5) rfl rfl)

/-- **`ud2`** faults. -/
theorem step_ud2 (m : MachineData) : isa.exec (at_ regs dmem m 6) = some (.fault ud2Msg) :=
  exec_ud2 (cellAt_at regs dmem m (j := 6) rfl rfl)

/-- The thread's steps (the first branch of a choice): `rax`, `rcx`, `rdx`
and the pc after each; then how it stops. -/
def trace : Nat → State → List String
  | 0, _ => []
  | n + 1, s =>
    let next (s' : State) :=
      let r := s'.st.1.regs
      s!"rax={r.rax} rcx={r.rcx} rdx={r.rdx} pc={s'.st.2}" :: trace n s'
    match isa.exec s with
    | some (.done s') => next s'
    | some (.choose (_ + 1) k) =>
      match k 0 with
      | .done s' => next s'
      | .choose (_ + 1) k' => match k' 0 with
        | .done s' => next s'
        | _ => ["deep choice"]
      | _ => ["choice"]
    | some (.fault msg) => [s!"fault: {msg}"]
    | none => ["halt"]
    | some _ => ["event"]

/-- The registers: `rdx` all ones, the thread pointer `0x300000`. -/
def regs0 : Reg64s := { rdx := 0xFFFFFFFFFFFFFFFF, fsBase := 0x300000 }

/-- The private memory: the word 3 at the thread pointer plus 8. -/
def dmem0 : DataMem := Mem.storeInt ∅ 0x300008#64 8 3

/--
info: ["rax=2097152 rcx=0 rdx=18446744073709551615 pc=1048577", "rax=2097152 rcx=3 rdx=18446744073709551615 pc=1048578",
  "rax=16777216 rcx=3 rdx=18446744073709551615 pc=1048579", "rax=16777216 rcx=3 rdx=0 pc=1048580",
  "rax=16777216 rcx=3 rdx=0 pc=1048581", "fault: pending system call: syscall"]
-/
#guard_msgs in
#eval trace 10 (st regs0 dmem0)

/-- The values of `rax`, `rcx`, `r11` at the leaves of a tree, and the pcs. -/
partial def leaves : EvTree State → List String
  | .done s => let r := s.st.1.regs; [s!"rax={r.rax} rcx={r.rcx} r11={r.r11} pc={s.st.2}"]
  | .choose n k => (List.finRange n).flatMap fun i => leaves (k i)
  | _ => ["other"]

-- Under certification with two results, the `syscall` is a choice of two
-- branches, each continuing after it with the three registers written.
/-- info: some ["rax=0 rcx=1048582 r11=2 pc=1048582", "rax=7 rcx=1048582 r11=2 pc=1048582"] -/
#guard_msgs in
#eval (execCert (fun i => [⟨0, i.nextPc, 2⟩, ⟨7, i.nextPc, 2⟩]) (at_ regs0 dmem0 {} 5)).map leaves

-- `ud2` faults.
/-- info: ["fault: ud2: undefined instruction"] -/
#guard_msgs in
#eval trace 1 (at_ regs0 dmem0 {} 6)

end Kraken.X64.Examples.LabelSys

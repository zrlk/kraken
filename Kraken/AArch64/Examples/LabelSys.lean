/-
AArch64 label addresses and system instructions (`Lower/EventsA64Sys.lean`)
on a `mkStateSyms` thread with a data symbol `tab` at `0x200008`:

    adrp x9, tab
    add x9, x9, :lo12:tab
    ldur x10, [x9, #-8]
    msr tpidr_el0, x9
    mrs x11, tpidr_el0
    nop
    svc #0

`adrp` gives `tab`'s page `0x200000`, `add :lo12:` its low bits `8`, so `x9`
is `tab`'s address (`x9_eq_tab`); the `ldur` reads the word below it from the
private memory; `msr`/`mrs` move it through the thread pointer; `svc` faults
under `isaLSE2.exec` and is a choice over the given results under
`execLSE2Cert` (`step_svc`, `step_svc_cert`).
-/
import Kraken.AArch64.Parser
import Kraken.Promising.Lower.CodeSegA64Syms
import Kraken.Promising.Lower.EventsA64Sys
import Kraken.AArch64.WP.SegmentExtract

namespace Kraken.AArch64.Examples.LabelSys

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-- The program. -/
def prog : Program := parseAArch64("
  adrp x9, tab
  add x9, x9, :lo12:tab
  ldur x10, [x9, #-8]
  msr tpidr_el0, x9
  mrs x11, tpidr_el0
  nop
  svc #0
")

/-- Its instructions. -/
def instrs : List Instr :=
  [⟨.W64, .ADRP (.low (.reg .X9) .W64) (.label "tab")⟩,
   ⟨.W64, .ADD_e (.low (.reg .X9) .W64) (.low (.reg .X9) .W64) (.imm ⟨.lo12 (.label "tab"), .S0⟩)⟩,
   ⟨.W64, .LDUR (.low (.reg .X10) .W64) ⟨.low (.reg .X9) .W64, .int64 (-8)⟩⟩,
   ⟨.W64, .MSR .TPIDR_EL0 (.low (.reg .X9) .W64)⟩,
   ⟨.W64, .MRS (.low (.reg .X11) .W64) .TPIDR_EL0⟩,
   ⟨.W64, .NOP⟩,
   ⟨.W64, .SVC 0⟩]

theorem prog_eq : prog = instrs.map Directive.instr := by decide

/-- The data symbol. -/
abbrev syms : List (String × BitVec 64) := [("tab", 0x200008#64)]

variable (regs : Reg64s) (dmem : DataMem)

/-- Thread 0 with the symbol. -/
abbrev st : State := mkStateSyms 0 prog regs syms dmem

/-- Thread 0's base address. -/
abbrev base : Int64 := Int64.ofNat 0x100000

theorem st_exe : (st regs dmem).exe
    = (base, prog.map (fun d => (d, d.fakeSize)) ++
        [(.byteArray (.mk #[]), 0x200008 - 0x10001c), (.label "tab", 0)]) := rfl

theorem validLayout_st : Kraken.Executable.ValidLayout (st regs dmem).exe := by
  rw [st_exe]; exact Kraken.Executable.validLayout_of_cellsOk _ (by decide) (by decide)

/-- **`tab` resolves to its address.** -/
theorem tab_addr : labelAddr (st regs dmem) "tab" = Int64.ofNat 0x200008 := by
  rw [labelAddr, st_exe, prog_eq, Kraken.Executable.label_addrOf _ "tab" 8 rfl (by decide)]
  decide

/-- **Instruction `j` is a `CellAt`** at `base + 4j`, in any machine data. -/
theorem cellAt_run (m : MachineData) {j : Nat} {i : Instr} (hi : instrs[j]? = some i) :
    CellAt { st regs dmem with st := (m, base + .ofNat (4 * j)) } (.instr i) 4 := by
  obtain ⟨ds, h1, h2⟩ := mkStateSyms_split 0 prog regs syms dmem [] {}
  have h0 : Kraken.Executable.codeAt (st regs dmem).exe base
      = (instrs.map Directive.instr).map (·, 4) ++ [(.byteArray (.mk #[]), 0x200008 - 0x10001c), (.label "tab", 0)] := by
    rw [show base = (st regs dmem).exe.1 from rfl, Kraken.Executable.codeAt_start, st_exe, prog_eq]; rfl
  exact cellAt_segment4_instr (validLayout_st regs dmem) h1 h2
    (mkStateSyms_endPc_code 0 prog regs syms dmem [] {}) h0 hi m

/-- `tab` resolves to its address in every state of the thread. -/
theorem tab_addr' (m : MachineData) (pc : Int64) :
    labelAddr { st regs dmem with st := (m, pc) } "tab" = Int64.ofNat 0x200008 :=
  tab_addr regs dmem

/-- The state at instruction `j`, with machine data `m`. -/
abbrev at_ (m : MachineData) (j : Nat) : State := { st regs dmem with st := (m, base + .ofNat (4 * j)) }

/-- **`adrp x9, tab`**: no event; `x9` is `tab`'s page. -/
theorem step_adrp (m : MachineData) :
    isaLSE2.exec (at_ regs dmem m 0) = some (.done (after (at_ regs dmem m 0) 4
      { m with regs := m.regs.setRegOrZr (.low (.reg .X9) .W64) 0x200000#64 })) := by
  rw [exec_adrp_label (cellAt_run regs dmem m (j := 0) rfl), tab_addr']
  rfl

/-- **`add x9, x9, :lo12:tab`**: no event; `x9` gains `tab`'s low bits. -/
theorem step_add (m : MachineData) :
    isaLSE2.exec (at_ regs dmem m 1) = some (.done (after (at_ regs dmem m 1) 4
      { m with regs := m.regs.setRegOrSp (.low (.reg .X9) .W64) (m.regs.getRegOrSp (.low (.reg .X9) .W64) + 8#64) })) := by
  rw [exec_add_lo12 (cellAt_run regs dmem m (j := 1) rfl), tab_addr']
  rfl

/-- The page and the low bits add up to `tab`'s address. -/
example : 0x200000#64 + 8#64 = 0x200008#64 := by
  rw [show (0x200000#64 : BitVec 64) = 0x200008#64 &&& ~~~0xFFF#64 by decide,
    show (8#64 : BitVec 64) = 0x200008#64 &&& 0xFFF#64 by decide, page_add_lo12]

/-- **`svc #0`** faults under `isaLSE2.exec`. -/
theorem step_svc (m : MachineData) :
    isaLSE2.exec (at_ regs dmem m 6) = some (.fault (pendingSyscallMsg 0)) :=
  exec_svc (cellAt_run regs dmem m (j := 6) rfl)

/-- **`svc #0` under certification**: one branch per result, each with the
result in `x0` and the pc after the `svc`. -/
theorem step_svc_cert (results : SyscallInfo → List (BitVec 64)) (m : MachineData) :
    execLSE2Cert results (at_ regs dmem m 6) = some (.choose (results (svcInfo (at_ regs dmem m 6) 0)).length
      fun i => .done (svcRet (at_ regs dmem m 6) 4 (results (svcInfo (at_ regs dmem m 6) 0))[i])) :=
  execCert_svc results (cellAt_run regs dmem m (j := 6) rfl)

/-- The no-event steps of the thread: `x9`, `x10`, `x11`, the thread pointer
and the pc after each; then how it stops. -/
def trace : Nat → State → List String
  | 0, _ => []
  | n + 1, s =>
    match isaLSE2.exec s with
    | some (.done s') =>
      let r := s'.st.1.regs
      s!"x9={r.X9} x10={r.X10} x11={r.X11} tp={r.TPIDR_EL0} pc={s'.st.2}" :: trace n s'
    | some (.fault msg) => [s!"fault: {msg}"]
    | none => ["halt"]
    | some _ => ["event"]

/-- The private memory: the word 42 at `0x200000`. -/
def dmem0 : DataMem := Mem.storeInt ∅ 0x200000#64 8 42

/--
info: ["x9=2097152 x10=0 x11=0 tp=0 pc=1048580", "x9=2097160 x10=0 x11=0 tp=0 pc=1048584",
  "x9=2097160 x10=42 x11=0 tp=0 pc=1048588", "x9=2097160 x10=42 x11=0 tp=2097160 pc=1048592",
  "x9=2097160 x10=42 x11=2097160 tp=2097160 pc=1048596", "x9=2097160 x10=42 x11=2097160 tp=2097160 pc=1048600",
  "fault: pending system call: svc #0"]
-/
#guard_msgs in
#eval trace 10 (st {} dmem0)

/-- The values of `x0` at the leaves of a tree, and the pcs. -/
partial def leaves : EvTree State → List String
  | .done s => [s!"x0={s.st.1.regs.X0} pc={s.st.2}"]
  | .choose n k => (List.finRange n).flatMap fun i => leaves (k i)
  | _ => ["other"]

-- Under certification with results `[0, 5]`, the `svc` is a choice of two
-- branches, each continuing after it with the result in `x0`.
/-- info: some ["x0=0 pc=1048604", "x0=5 pc=1048604"] -/
#guard_msgs in
#eval (execLSE2Cert (fun _ => [0, 5]) (at_ {} dmem0 {} 6)).map leaves

end Kraken.AArch64.Examples.LabelSys

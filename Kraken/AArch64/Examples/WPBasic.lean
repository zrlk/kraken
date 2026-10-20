/-
The first AArch64 programs proved with `vcgen` on the machine-founded wp
(`Kraken.AArch64.WP.MachineWP`): straight-line register arithmetic. Each
program is a label and three instructions; the walk applies `label_spec`,
the instruction rules and `nil_spec`, and `grind` discharges the VC with the
register API of `Kraken.AArch64.WP.Specs`. The registers the programs do not
write keep their values.

Each triple is also read at the machine (`Kraken.AArch64.WP.Bridge`): by
`Program.instrStep_of_triple` as the instruction-step judgment from the start
address to the end of the text, and by `Program.run_of_triple` as the
baseline judgment `Eventually (straightlineStep …)`.
-/
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Bridge

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP

set_option mvcgen.warning false

/-- `MOVZ`, `MOV` (register) and `ADD` (immediate). -/
def wp_basic : Program := parseAArch64("
start:
  movz x0, #5
  mov x1, x0
  add x2, x1, #3
")

/-- `SUB` (immediate), `NOP` and `MOVZ` with a shift. -/
def wp_basic2 : Program := parseAArch64("
start:
  sub x2, x2, #1
  nop
  movz x3, #1, lsl #16
")

variable [layout : _root_.Layout]

section
/-- The ambient code of the first example: `wp_basic`, laid out. -/
local instance wp_basic.env : CodeEnv := ⟨layout wp_basic⟩

theorem wp_basic_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄
      wp_basic
    ⦃ fun _ s => s.regs.X0 = 5 ∧ s.regs.X1 = 5 ∧ s.regs.X2 = 8
        ∧ s.regs.X3 = d.regs.X3 ∧ s.regs.SP = d.regs.SP ∧ s.status = d.status ⦄ := by
  vcgen [wp_basic] with finish

/-- `wp_basic_correct`, read at the machine as the instruction-step judgment. -/
theorem wp_basic_instrStep [Executable.ValidLayout (layout wp_basic)] (d : MachineData) :
    Eventually (layout wp_basic).instrStep
      (fun st => st.2 = (layout wp_basic).addrOf wp_basic.length
        ∧ st.1.regs.X0 = 5 ∧ st.1.regs.X1 = 5 ∧ st.1.regs.X2 = 8
        ∧ st.1.regs.X3 = d.regs.X3 ∧ st.1.regs.SP = d.regs.SP ∧ st.1.status = d.status)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (wp_basic_correct d) rfl

/-- `wp_basic_correct`, read at the machine as the baseline judgment. -/
theorem wp_basic_run [Executable.ValidLayout (layout wp_basic)] (d : MachineData) :
    Eventually (straightlineStep (layout wp_basic))
      (fun st => st.1.regs.X0 = 5 ∧ st.1.regs.X1 = 5 ∧ st.1.regs.X2 = 8
        ∧ st.1.regs.X3 = d.regs.X3 ∧ st.1.regs.SP = d.regs.SP ∧ st.1.status = d.status)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (wp_basic_correct d) rfl
end

section
/-- The ambient code of the second example: `wp_basic2`, laid out. -/
local instance wp_basic2.env : CodeEnv := ⟨layout wp_basic2⟩

theorem wp_basic2_correct (d : MachineData) (h : d.regs.X2.toNat = 10) :
    ⦃ fun s => s = d ⦄
      wp_basic2
    ⦃ fun _ s => s.regs.X2.toNat = 9 ∧ s.regs.X3 = 0x10000 ∧ s.regs.X0 = d.regs.X0 ⦄ := by
  vcgen [wp_basic2] with finish

/-- `wp_basic2_correct`, read at the machine as the instruction-step judgment. -/
theorem wp_basic2_instrStep [Executable.ValidLayout (layout wp_basic2)] (d : MachineData)
    (h : d.regs.X2.toNat = 10) :
    Eventually (layout wp_basic2).instrStep
      (fun st => st.2 = (layout wp_basic2).addrOf wp_basic2.length
        ∧ st.1.regs.X2.toNat = 9 ∧ st.1.regs.X3 = 0x10000 ∧ st.1.regs.X0 = d.regs.X0)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (wp_basic2_correct d h) rfl

/-- `wp_basic2_correct`, read at the machine as the baseline judgment. -/
theorem wp_basic2_run [Executable.ValidLayout (layout wp_basic2)] (d : MachineData)
    (h : d.regs.X2.toNat = 10) :
    Eventually (straightlineStep (layout wp_basic2))
      (fun st => st.1.regs.X2.toNat = 9 ∧ st.1.regs.X3 = 0x10000 ∧ st.1.regs.X0 = d.regs.X0)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (wp_basic2_correct d h) rfl
end

/-
AArch64 control flow and procedures proved with `vcgen` on the machine-founded
wp: the `vcgen` twin of `controlflow` (`p4`, parked in `Examples.lean`), a
counted loop through the control-flow rule `MachineWP.cfg`, a leaf call
through `BL`/`RET`, and the mutual recursion `even`/`odd` through
`ProcSpec.of_cfg_post` and `call_proc_spec_at`. Each triple on a laid-out
program is also read at the machine (`Program.instrStep_of_triple`, and
`Program.run_of_triple` where the exit channel is empty).
-/
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.Cfg
import Kraken.AArch64.WP.RulesCF
import Kraken.AArch64.WP.Rules

open Kraken.AArch64.Parser
open Kraken
open Std.WP
open MachineWP
open Lean.Order

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.AArch64.Examples.WPControl

/-! ## `controlflow` (`p4`): a branch not taken

`eor x0, x0, x0` clears `x0`, so `cbnz` falls through. The rule of `cbnz`
asks the exit channel at the taken side, which the triple leaves empty: the VC
is that `x0 ≠ 0` is impossible there. The literal `#42` reaches the VC as
`BitVec.ofInt 64 (Int64.toInt 42)`, which `grind`'s normalizer folds (the
`Int64` literal rules of `MachineWP`); `bv_decide` is not involved. -/

/-- The program of `p4_correct` (`Examples.lean`). -/
def controlflow : Program := parseAArch64("
start:
  mov x0, #1
  eor x0, x0, x0
  cbnz x0, start
  mov x1, #42
")

variable [layout : _root_.Layout]

section
/-- The ambient code: `controlflow`, laid out. -/
local instance controlflow.env : CodeEnv := ⟨layout controlflow⟩

theorem controlflow_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ controlflow ⦃ fun _ s => s.regs.X1 = 42 ∧ s.regs.X0 = 0 ⦄ := by
  vcgen [controlflow] with finish

/-- `controlflow_correct`, read at the machine as the instruction-step judgment. -/
theorem controlflow_instrStep [Executable.ValidLayout (layout controlflow)] (d : MachineData) :
    Eventually (layout controlflow).instrStep
      (fun st => st.2 = (layout controlflow).addrOf controlflow.length
        ∧ st.1.regs.X1 = 42 ∧ st.1.regs.X0 = 0)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (controlflow_correct d) rfl

/-- `p4_correct`'s statement, from `controlflow_correct`. -/
theorem p4_correct [Executable.ValidLayout (layout controlflow)] (d : MachineData) :
    Eventually (straightlineStep (layout controlflow)) (fun s' => s'.1.regs.X1 = 42)
      (d, Kraken.Layout.start Directive) :=
  eventually_weaken _ _ _ _ (fun _ h => h.1) (Program.run_of_triple (controlflow_correct d) rfl)
end

/-! ## A counted loop through `MachineWP.cfg`

`count` moves `x0` into `x1` one unit at a time: `cbz` leaves the loop when
`x0` is zero, `b` is the back edge. The table gives the invariant at `loop`,
`x0 + x1 = d.x0`; the variant is `x0`, which the back edge decreases. -/

def count : Program := parseAArch64("
start:
  movz x1, #0
loop:
  cbz x0, done
  sub x0, x0, #1
  add x1, x1, #1
  b loop
done:
  nop
")

/-- The spec table of `count`, for a run that started on `d`. -/
abbrev count_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "loop", s => s.regs.X0 + s.regs.X1 = d.regs.X0 ∧ s.regs.X2 = d.regs.X2
  | "done", s => s.regs.X1 = d.regs.X0 ∧ s.regs.X0 = 0 ∧ s.regs.X2 = d.regs.X2
  | _, _ => False

section
variable [Executable.ValidLayout (layout count)]

/-- The ambient code: `count`, laid out. -/
local instance count.env : CodeEnv := ⟨layout count⟩

theorem count_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄
      count
    ⦃ fun _ s => s.regs.X1 = d.regs.X0 ∧ s.regs.X0 = 0 ∧ s.regs.X2 = d.regs.X2 ⦄ := by
  apply MachineWP.cfg (count_table d) (fun _ s => s.regs.X0.toNat)
  cfg_cases [count]
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish

/-- `count_correct`, read at the machine as the instruction-step judgment. -/
theorem count_instrStep (d : MachineData) :
    Eventually (layout count).instrStep
      (fun st => st.2 = (layout count).addrOf count.length
        ∧ st.1.regs.X1 = d.regs.X0 ∧ st.1.regs.X0 = 0 ∧ st.1.regs.X2 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (count_correct d) rfl

/-- `count_correct`, read at the machine as the baseline judgment. -/
theorem count_run (d : MachineData) :
    Eventually (straightlineStep (layout count))
      (fun st => st.1.regs.X1 = d.regs.X0 ∧ st.1.regs.X0 = 0 ∧ st.1.regs.X2 = d.regs.X2)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (count_correct d) rfl
end

/-! ## A loop on the flags: `subs` and `b.ne`

`countdown` is `count` with the test at the bottom: after a `cbz` guard for
`x0 = 0`, it counts `x0` down with `subs` and loops on `b.ne`. The invariant at
`loop` is `x0 + x1 = d.x0` with `x0 ≠ 0`; the variant is `x0`.

(A version adding 2 per round, with the invariant `x1 + 2 * x0 = 2 * d.x0`,
makes `grind`'s ring solver panic on the back-edge VC, `mkImpEqExprProof`
"assertion violation: d.p matches .num 0", and the kernel then rejects the
proof with "unknown constant `_inhabitedExprDummy`".) -/

def countdown : Program := parseAArch64("
start:
  movz x1, #0
  cbz x0, done
loop:
  add x1, x1, #1
  subs x0, x0, #1
  b.ne loop
done:
  nop
")

abbrev countdown_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "loop", s => s.regs.X0 ≠ 0 ∧ s.regs.X0 + s.regs.X1 = d.regs.X0
  | "done", s => s.regs.X1 = d.regs.X0 ∧ s.regs.X0 = 0
  | _, _ => False

section
variable [Executable.ValidLayout (layout countdown)]

/-- The ambient code: `countdown`, laid out. -/
local instance countdown.env : CodeEnv := ⟨layout countdown⟩

theorem countdown_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ countdown ⦃ fun _ s => s.regs.X1 = d.regs.X0 ∧ s.regs.X0 = 0 ⦄ := by
  apply MachineWP.cfg (countdown_table d) (fun _ s => s.regs.X0.toNat)
  cfg_cases [countdown]
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish

/-- `countdown_correct`, read at the machine as the baseline judgment. -/
theorem countdown_run (d : MachineData) :
    Eventually (straightlineStep (layout countdown))
      (fun st => st.1.regs.X1 = d.regs.X0 ∧ st.1.regs.X0 = 0)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (countdown_correct d) rfl
end

/-! ## Testing a bit: `tbnz`

`parity` sets `x1` to the low bit of `x0` by branching on it. -/

def parity : Program := parseAArch64("
start:
  tbnz x0, #0, odd
  movz x1, #0
  b done
odd:
  movz x1, #1
done:
  nop
")

abbrev parity_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "odd", s => s = d ∧ d.regs.X0.toBitVec.getLsbD 0 = true
  | "done", s => s.regs.X1.toNat = d.regs.X0.toNat % 2
  | _, _ => False

section
variable [Executable.ValidLayout (layout parity)]

/-- The ambient code: `parity`, laid out. -/
local instance parity.env : CodeEnv := ⟨layout parity⟩

theorem parity_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ parity ⦃ fun _ s => s.regs.X1.toNat = d.regs.X0.toNat % 2 ⦄ := by
  apply MachineWP.cfg (parity_table d)
  cfg_cases [parity]
  · vcgen with finish
  · vcgen with finish
  · vcgen with finish

/-- `parity_correct`, read at the machine as the baseline judgment. -/
theorem parity_run (d : MachineData) :
    Eventually (straightlineStep (layout parity))
      (fun st => st.1.regs.X1.toNat = d.regs.X0.toNat % 2)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (parity_correct d) rfl
end

/-! ## A leaf call: `BL` and `RET`

`leaf` calls `inc2` twice. `BL` leaves the address behind it in `X30` and
`RET` jumps back there; `inc2` touches neither `X30` nor the stack, so it
needs no frame. The procedure is proved once, as a `ProcSpec` from its blocks
(`ProcSpec.of_cfg`), placed inside `leaf` (`PlacedIn.of_placed`), and each
call site steps through it with `call_proc_spec_at`. `leaf_correct'` does the
same with the callee's text and triple instead (`fun_spec_from_label`, x64's
`CallSwap` pattern). -/

def leaf : Program := parseAArch64("
start:
  bl inc2
  bl inc2
  b done
inc2:
  add x0, x0, #2
  ret
done:
  nop
")

/-- `inc2` on its own, as `leaf` has it. -/
def inc2_body : Program := parseAArch64("
inc2:
  add x0, x0, #2
  ret
")

section
variable [CodeEnv]

/-- The address of a label in the ambient code. -/
local macro "L" : term => `((_root_.Executable.labels cenv).label)

/-- `inc2` returns to the address in `X30` with `x0` increased by 2, and the
other registers but `x0` as they were. -/
abbrev Inc2Spec : Prop :=
  cenv.ProcSpec (L "inc2") (α := Unit)
    (fun _ ra t => t.lr = ra)
    (fun _ _ t s => s.regs.X0 = t.regs.X0 + 2 ∧ s.regs.X1 = t.regs.X1
      ∧ s.regs.X30 = t.regs.X30 ∧ s.regs.SP = t.regs.SP ∧ s.dmem = t.dmem)

omit layout in
theorem inc2_spec (hpl : Program.PlacedIn inc2_body) : Inc2Spec := by
  refine Kraken.Executable.ProcSpec.of_cfg (p := inc2_body)
    (fun _ ra t₀ l s => l = "inc2" ∧ s = t₀ ∧ t₀.lr = ra) (hblocks := ?_) (hpre := ?_)
  · intro _ ra t₀
    cfg_cases [inc2_body]
    vcgen with finish
  · intro _ ra t hra
    exact ⟨rfl, rfl, hra⟩
end

/-- The spec table of `leaf`: the caller starts on `d`, and the procedure is
entered by calls rather than by an edge of the table. -/
abbrev leaf_table (d : MachineData) : Label → MachineData → Prop
  | "start", s => s = d
  | "done", s => s.regs.X0 = d.regs.X0 + 4 ∧ s.regs.X1 = d.regs.X1
  | _, _ => False

section
variable [Executable.ValidLayout (layout leaf)]

/-- The ambient code: `leaf`, laid out. -/
local instance leaf.env : CodeEnv := ⟨layout leaf⟩

/-- Where `leaf` sits. -/
theorem leaf_placed : Program.Placed leaf "start" :=
  Program.placed_of_layout (by decide) rfl (by decide)

theorem leaf_correct (d : MachineData) :
    ⦃ fun s => s = d ⦄ leaf ⦃ fun _ s => s.regs.X0 = d.regs.X0 + 4 ∧ s.regs.X1 = d.regs.X1 ⦄ := by
  have hspec := inc2_spec (Program.PlacedIn.of_placed leaf_placed (by decide))
  have hc := MachineWP.call_proc_spec_at () "inc2" hspec
  have hpl := leaf_placed
  apply MachineWP.cfg (leaf_table d)
  cfg_cases [leaf]
  · -- two calls: each `call_proc_spec_at` asks `∀ ra, Pre ∧ ∀ s', Post → wp`, and
    -- the `refine` opens it so that the next `vcgen` steps the cells behind the call
    vcgen [hc]
    all_goals call_simp
    all_goals try refine ⟨?_, fun s' hpost => ?_⟩
    all_goals try (vcgen [hc]; all_goals call_simp)
    all_goals try refine ⟨?_, fun s' hpost => ?_⟩
    all_goals try (vcgen; all_goals call_simp)
    all_goals grind
  · vcgen with finish
  · vcgen with finish

/-- `leaf_correct`, read at the machine as the instruction-step judgment. -/
theorem leaf_instrStep (d : MachineData) :
    Eventually (layout leaf).instrStep
      (fun st => st.2 = (layout leaf).addrOf leaf.length
        ∧ st.1.regs.X0 = d.regs.X0 + 4 ∧ st.1.regs.X1 = d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.instrStep_of_triple (leaf_correct d) rfl

/-- `leaf_correct`, read at the machine as the baseline judgment. -/
theorem leaf_run (d : MachineData) :
    Eventually (straightlineStep (layout leaf))
      (fun st => st.1.regs.X0 = d.regs.X0 + 4 ∧ st.1.regs.X1 = d.regs.X1)
      (d, Kraken.Layout.start Directive) :=
  Program.run_of_triple (leaf_correct d) rfl

/-- The procedure's text, as the call rule takes it. -/
abbrev inc2_text : Program := parseAArch64("
  add x0, x0, #2
  ret
")

omit [Executable.ValidLayout (layout leaf)] in
/-- The procedure from the state its caller left: `x0` increased by 2, and a
return to the address in `X30`. -/
theorem inc2_text_spec (ra : Int64) (s : MachineData) :
    ⦃ fun t => t = s.setLr ra ∧ True ⦄
      inc2_text
    ⦃ (fun _ _ => False); fun a s' => a = ra ∧ s'.regs.X0 = s.regs.X0 + 2
        ∧ s'.regs.X1 = s.regs.X1 ⦄ := by
  vcgen simplifying_assumptions with finish

/-- `leaf_correct` through the callee's text (`fun_spec_from_label`). -/
theorem leaf_correct' (d : MachineData) :
    ⦃ fun s => s = d ⦄ leaf ⦃ fun _ s => s.regs.X0 = d.regs.X0 + 4 ∧ s.regs.X1 = d.regs.X1 ⦄ := by
  have hpl := leaf_placed
  have hcall := MachineWP.fun_spec_from_label
    (hpl.block "inc2" ⟨"inc2", inc2_text, some "done"⟩ rfl) inc2_text_spec
  apply MachineWP.cfg (leaf_table d)
  cfg_cases [leaf]
  · vcgen [hcall] with finish
  · vcgen with finish
  · vcgen with finish
end

end Kraken.AArch64.Examples.WPControl

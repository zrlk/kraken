import Kraken.AArch64.EnvCalls

/-!
# A call whose callee touches shared memory, in the environment wp

`callLdar` calls `f` with `bl`; `f` performs one shared acquire load
(`ldar x0, [x1]`) and returns. The caller then adds one to the value loaded.
The environment is `SharedEnv.lastWrite [(c, 8)]`, with `x1 = c` a shared
word outside `dmem`.

- `callee_envSpec`: the callee's `TripleEnv`, by one `vcgen` call (`LDAR` by
  `ldar_shared_spec`, `RET` by the generic rule): from `s.setLr ra` it returns
  to `ra` with `x0` the shared word's value and the environment state unchanged.
- `caller_envSpec`: the caller's `TripleEnv` (`bl f; add x2, x0, #1`), proved
  from `callee_envSpec` through `MachineWP.fun_specEnv_from_label`; the tail
  `add` by `vcgen`.
- `caller_correctEnv`: the same on the laid-out program, with the callee's
  placement from `Program.placed_of_layout`.
-/

open Std.WP
open Kraken
open MachineWP

set_option mvcgen.warning false
set_option experimental.vcgen true

namespace Kraken.AArch64.Examples.EnvCalls

open Kraken.AArch64.Parser

variable [layout : _root_.Layout]

/-- The caller, the callee `f`, and the exit. -/
def callLdar : Program := parseAArch64("
start:
  bl f
  add x2, x0, #1
  b done
f:
  ldar x0, [x1]
  ret
done:
  nop
")

/-- The callee's text, as the call rule takes it. -/
def calleeText : Program := parseAArch64("
  ldar x0, [x1]
  ret
")

/-- The caller's text up to the exit branch. -/
def callerText : Program := parseAArch64("
  bl f
  add x2, x0, #1
")

/-- The environment: last writes to the shared word at `c`. -/
abbrev envC (c : BitVec 64) : SharedEnv := SharedEnv.lastWrite [(c, 8)]

/-- What the callee needs of its caller: `x1` points at the shared word,
which is not in `dmem`. -/
abbrev CalleePre (c : BitVec 64) (s : MachineData) (_ : (envC c).State) : Prop :=
  s.regs.X1.toBitVec = c ∧ Mem.loadInt s.dmem c 8 = none

/-- What the callee gives back: `x0` is the shared word's value, `x1` and
`dmem` are kept, and the environment state is unchanged. -/
abbrev CalleePost (c : BitVec 64) (s : MachineData) (g : (envC c).State) (s' : MachineData)
    (g' : (envC c).State) : Prop :=
  s'.regs.X0.toBitVec = (g c).setWidth 64 ∧ s'.regs.X1 = s.regs.X1 ∧ s'.dmem = s.dmem ∧ g' = g

omit layout in
/-- **The callee's environment triple**: one shared `LDAR` and a return. -/
theorem callee_envSpec [CodeEnv] (c : BitVec 64) (ra : Int64) (s : MachineData) (g : (envC c).State) :
    TripleEnv (envC c) (fun t g' => t = s.setLr ra ∧ g' = g ∧ CalleePre c s g) calleeText
      (fun _ _ => False) (fun a s' g' => a = ra ∧ CalleePost c s g s' g') := by
  apply TripleEnv.of_triple
  unfold calleeText
  vcgen
  all_goals simp_all [SharedEnv.lastWrite, MachineData.setLr, Reg64s.setXReg]
  all_goals rfl

omit layout in
/-- **The caller's environment triple, from the callee's.** -/
theorem caller_envSpec [CodeEnv] (c : BitVec 64) (d : MachineData)
    (hplace : cenv.sits ((_root_.Executable.labels cenv).label "f") calleeText)
    (hx1 : d.regs.X1.toBitVec = c) (hnone : Mem.loadInt d.dmem c 8 = none) :
    TripleEnv (envC c) (fun s _ => s = d) callerText
      (fun s g => s.regs.X2.toBitVec = (g c).setWidth 64 + 1) (fun _ _ _ => False) := by
  have hcall := MachineWP.fun_specEnv_from_label (Pre := CalleePre c) (Post := CalleePost c) hplace
    (fun ra s g => callee_envSpec c ra s g)
  -- the tail behind the call
  have htail : ∀ s' g', s'.regs.X0.toBitVec = (g' c).setWidth 64 →
      cenv.wpEnv (envC c) (parseAArch64("add x2, x0, #1") : Program)
        (fun s g => s.regs.X2.toBitVec = (g c).setWidth 64 + 1) (fun _ _ _ => False) s' g' := by
    intro s' g' hx0
    refine TripleEnv.of_triple (env := envC c) (P := fun s g => s = s' ∧ g = g') ?_ s' g' ⟨rfl, rfl⟩
    vcgen
    all_goals simp_all
  unfold callerText
  refine TripleEnv.mono (fun s g (hs : s = d) => ?_) (fun _ _ h => h) (fun _ _ _ h => h) (@hcall _ _ _)
  subst hs
  refine ⟨⟨hx1, hnone⟩, fun s' g' h => ?_⟩
  obtain ⟨hx0, -, -, rfl⟩ := h
  exact htail s' _ hx0

section

variable [Executable.ValidLayout (layout callLdar)]

/-- The ambient code: `callLdar`, laid out. -/
local instance callLdar.env : CodeEnv := ⟨layout callLdar⟩

/-- Where `callLdar` sits. -/
theorem callLdar_placed : Program.Placed callLdar "start" :=
  Program.placed_of_layout (by decide) rfl (by decide)

/-- **`caller_envSpec` on the laid-out program**: the callee sits at `f`. -/
theorem caller_correctEnv (c : BitVec 64) (d : MachineData) (hx1 : d.regs.X1.toBitVec = c)
    (hnone : Mem.loadInt d.dmem c 8 = none) :
    TripleEnv (envC c) (fun s _ => s = d) callerText
      (fun s g => s.regs.X2.toBitVec = (g c).setWidth 64 + 1) (fun _ _ _ => False) :=
  caller_envSpec c d (callLdar_placed.block "f" ⟨"f", calleeText, some "done"⟩ rfl) hx1 hnone

end

end Kraken.AArch64.Examples.EnvCalls

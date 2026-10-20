/-
Part 8: **`treiber2_arm.kl` whole image**, as
`EnvG/A64WholeTreiber2.lean` for `treiber2.kl`.

`treiber2_arm.kl`'s `code` block is exactly `treiber2ArmWorker` (its
`worker:` label included: `codeMatchesA`), and both of its threads run that
block from `worker` (cell `0`) to `done` (the end of the text). So
`treiber2_arm_envG` is already a whole-image theorem; only its two layouts are
independent.

- `treiber2_arm_envG_whole`: `treiber2_arm_envG` at one layout `l` for both
  threads (the runner's situation: one executable, `l treiber2ArmWorker`).
- `treiber2_arm_envG_whole_concrete`: at the runner's layout (`wLayoutA`:
  text at `0x100000`, each directive its `fakeSize`), with `runnerMatchesWA`:
  the runner's prepared threads (`Kraken.Litmus.AArch64.prepareProgram`) are
  exactly `wWorkerA0`, `wWorkerA1` (executable, pc, end, registers, empty
  private memory; not compared: `decls`, the theorem assumes none; see
  `EnvG/A64Treiber2ArmRunner.lean` for the runner's exact configuration).
-/
import Kraken.Promising.SLR.EnvG.Treiber2ArmPublic
import Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data

namespace Kraken.Promising.SLR.EnvG.Treiber2Arm

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.Treiber2 (Treiber2DFinal)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2InitMem)

/-- **`treiber2_arm.kl`, both threads running the whole `.kl` image** (the
`code` block is `treiber2ArmWorker`): `treiber2_arm_envG` with one layout `l`
for both threads, each from `worker` to `done`, as the runner sets them up. -/
theorem treiber2_arm_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWA (layout := l) t n0 1 s0) (h1 : StartWA (layout := l) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg :=
  treiber2_arm_envG l l t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hc hf

/-! ## The runner's instance -/

/-- The `.kl` source. -/
def treiber2ArmKl : String := include_str "../../../Examples/LockFree/AArch64/treiber2_arm.kl"

/-- The `code` block of the `.kl` parses to `treiber2ArmWorker` (its `worker`
label included). -/
def codeMatchesA (src : String) : Bool :=
  match Kraken.Litmus.parseProgram src with
  | .error _ => false
  | .ok p => match Kraken.AArch64.Parser.parse ("\n".intercalate p.code) with
    | .ok prog => prog == treiber2ArmWorker
    | .error _ => false

/-- The runner's layout of the image: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def wLayoutA : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiber2ArmWorker

instance wValidA : Executable.ValidLayout (wLayoutA treiber2ArmWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- Thread `0` as the runner prepares it: `X0 = top`, `X1 = n1`, `X9 = 1`,
from `worker` to `done`. -/
def wWorkerA0 : AArch64.State where
  exe := wLayoutA treiber2ArmWorker
  endPc := 0x100000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X9 := 1 } }, 0x100000)

/-- Thread `1` as the runner prepares it: `X0 = top`, `X1 = n2`, `X9 = 2`,
the same executable. -/
def wWorkerA1 : AArch64.State where
  exe := wLayoutA treiber2ArmWorker
  endPc := 0x100000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200, X9 := 2 } }, 0x100000)

/-- The runner's threads run `wWorkerA0`'s and `wWorkerA1`'s executable, pc,
end, registers and private memory. -/
def runnerMatchesWA (src : String) : Bool :=
  let same (t : Thread isa) (s : AArch64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 wWorkerA0 && same t1 wWorkerA1
    | _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (codeMatchesA treiber2ArmKl, runnerMatchesWA treiber2ArmKl)

section
attribute [local instance] wLayoutA

theorem wWorkerA0_start : StartWA topAddr n1Addr 1 wWorkerA0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [wWorkerA0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

theorem wWorkerA1_start : StartWA topAddr n2Addr 2 wWorkerA1 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [wWorkerA1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨
(0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`** for `treiber2_arm.kl` under
`Arch.armv8`, both threads running the runner's executable (the whole `code`
block at `0x100000`): concrete instance of `treiber2_arm_envG_whole`. -/
theorem treiber2_arm_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [wWorkerA0, wWorkerA1] treiber2InitMem) c)
    (hf : c.final = true) : Treiber2DFinal n1Addr n2Addr c :=
  treiber2_arm_envG_whole wLayoutA topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wWorkerA0_start wWorkerA1_start (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber2Arm

#print axioms Kraken.Promising.SLR.EnvG.Treiber2Arm.treiber2_arm_envG_whole_concrete

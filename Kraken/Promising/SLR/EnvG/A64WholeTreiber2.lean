/-
**`treiber2.kl` whole image.** Additive:
`Treiber2.treiber2_envG` (`EnvG/Treiber2DataPublic.lean`) and its concrete
instance are unchanged.

`treiber2.kl`'s `code` block is exactly `treiber2DWorker` (its `worker:`
label included: `ConcreteTreiber2Data.codeMatches`), and both of its
threads run that block from `worker` (cell `0`) to `done` (the end of the
text). So `treiber2_envG` is already a whole-image theorem; only its two
layouts are independent, and its concrete instance puts thread `1`'s copy at
`0x200000`, which is not the runner's executable.

- `treiber2_envG_whole`: `treiber2_envG` at one layout `l` for both threads
  (the runner's situation: one executable, `l treiber2DWorker`).
- `treiber2_envG_whole_concrete`: at the runner's layout (`wLayout2D`: text
  at `0x100000`, each directive its `fakeSize`), with `runnerMatchesW`: the
  runner's prepared threads (`Kraken.Litmus.AArch64.prepareProgram`) are
  exactly `wWorker0`, `wWorker1` (executable, pc, end, registers, empty
  private memory; not compared: `decls`, the theorem assumes none).
-/
import Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data

namespace Kraken.Promising.SLR.EnvG.Treiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2Kl treiber2InitMem)

/-- **The two-thread Treiber stack `treiber2.kl`, both threads running the
whole `.kl` image** (the `code` block is `treiber2DWorker`): `treiber2_envG`
with one layout `l` for both threads, each from `worker` to `done`, as the
runner sets them up. -/
theorem treiber2_envG_whole {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (hn : n0 ≠ n1) (hn0 : n0 ≠ 0) (hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWD (layout := l) t n0 1 s0) (h1 : StartWD (layout := l) t n1 2 s1)
    (hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0)
    {cfg : Config isa} (hc : Reachable Arch.armv8 fuel (Config.init [s0, s1] initMem) cfg)
    (hf : cfg.final = true) : Treiber2DFinal n0 n1 cfg :=
  treiber2_envG l l t n0 n1 ht0 ht1 hn hn0 hn1 h0 h1 hT0 hc hf

/-! ## The runner's instance -/

/-- The runner's layout of the image: text at `0x100000`, each directive
its `fakeSize`. -/
@[reducible] def wLayout2D : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize treiber2DWorker

instance wValid2D : Executable.ValidLayout (wLayout2D treiber2DWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- Thread `0` as the runner prepares it: `X0 = top`, `X1 = n1`, `X9 = 1`,
from `worker` to `done`. -/
def wWorker0 : AArch64.State where
  exe := wLayout2D treiber2DWorker
  endPc := 0x100000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1100, X9 := 1 } }, 0x100000)

/-- Thread `1` as the runner prepares it: `X0 = top`, `X1 = n2`, `X9 = 2`,
the same executable. -/
def wWorker1 : AArch64.State where
  exe := wLayout2D treiber2DWorker
  endPc := 0x100000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200, X9 := 2 } }, 0x100000)

/-- The runner's threads run `wWorker0`'s and `wWorker1`'s executable, pc,
end, registers and private memory. -/
def runnerMatchesW (src : String) : Bool :=
  let same (t : Thread isa) (s : AArch64.State) : Bool :=
    t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
      t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem.isEmpty
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => match pr.config.threads.toList with
    | [t0, t1] => same t0 wWorker0 && same t1 wWorker1
    | _ => false

/-- info: (true, true) -/
#guard_msgs in
#eval (ConcreteTreiber2Data.codeMatches treiber2Kl, runnerMatchesW treiber2Kl)

section
attribute [local instance] wLayout2D

theorem wWorker0_start : StartWD topAddr n1Addr 1 wWorker0 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [wWorker0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

theorem wWorker1_start : StartWD topAddr n2Addr 2 wWorker1 := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩ <;>
    simp [wWorker1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`(0:X10=n1 ∧ 0:X11=1 ∧ 1:X10=n2 ∧ 1:X11=2) ∨
(0:X10=n2 ∧ 0:X11=2 ∧ 1:X10=n1 ∧ 1:X11=1)`** for `treiber2.kl` under
`Arch.armv8`, both threads running the runner's executable (the whole `code`
block at `0x100000`): concrete instance of `treiber2_envG_whole`. -/
theorem treiber2_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [wWorker0, wWorker1] treiber2InitMem) c)
    (hf : c.final = true) : Treiber2DFinal n1Addr n2Addr c :=
  treiber2_envG_whole wLayout2D topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wWorker0_start wWorker1_start (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Treiber2

#print axioms Kraken.Promising.SLR.EnvG.Treiber2.treiber2_envG_whole_concrete

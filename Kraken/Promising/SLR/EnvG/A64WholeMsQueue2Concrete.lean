/-
**A concrete instance of
`MsQueue.msqueue2_envG_whole`** — the `.kl` runner's own executable and
threads for `msqueue2.kl`.

- `codeMatchesWQ2`: the `.kl`'s `code` block parses to exactly `msq2Image`.
- `runnerMatchesWQ2`: the runner's prepared threads run exactly `msq2Image`
  laid out by `wLayoutQ2` (text at `0x100000`, each directive its
  `fakeSize`), thread `0` from `enq` (`0x100000`) to `pdone` (`0x100084`)
  with `X0 = head`, `X1 = tail`, `X12 = n1`, `X13 = n2`, thread `1` from
  `deq1` (`0x100088`) to `ddone1` (`0x100114`) with `X0 = head`,
  `X1 = tail`, the runner's whole register file and empty private memory.
- `msqueue2_envG_whole_concrete`: the theorem there, at the runner's
  placement (`head = 0x1000`, `d = 0x1100`, `tail = 0x1200`,
  `n1 = 0x1300`, `n2 = 0x1400`); every hypothesis by `decide`/`rfl`/`simp`. No
  `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue2
import Kraken.Promising.SLR.EnvG.A64WholeRunner
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The runner's layout of the image. -/
@[reducible] def wLayoutQ2 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize msq2Image

instance wValidQ2 : Executable.ValidLayout (wLayoutQ2 msq2Image) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The enqueuer as the runner prepares it. -/
def enqWQ2 : AArch64.State where
  exe := wLayoutQ2 msq2Image
  endPc := 0x100000 + 132
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200, X12 := 0x1300, X13 := 0x1400 } }, 0x100000)

/-- The dequeuer as the runner prepares it. -/
def deqWQ2 : AArch64.State where
  exe := wLayoutQ2 msq2Image
  endPc := 0x100000 + 276
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200 } }, 0x100000 + 136)

/-- The initial memory: `head = tail = d`, the links `0`. -/
def msq2InitMemW : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1200, 8⟩, 0x1100), (⟨0x1100 + 8, 8⟩, 0), (⟨0x1300 + 8, 8⟩, 0),
    (⟨0x1400 + 8, 8⟩, 0)]

/-- The `.kl` source. -/
def msqueue2KlW : String := include_str "../../../Examples/LockFree/AArch64/msqueue2.kl"

/-- The `code` block of `msqueue2.kl` parses to `msq2Image`. -/
def codeMatchesWQ2 (src : String) : Bool := A64Whole.codeIs src msq2Image

/-- info: true -/
#guard_msgs in
#eval codeMatchesWQ2 msqueue2KlW

/-- The runner's threads are `enqWQ2` and `deqWQ2`. -/
def runnerMatchesWQ2 (src : String) : Bool := A64Whole.runnerIs src [enqWQ2, deqWQ2]

/-- info: true -/
#guard_msgs in
#eval runnerMatchesWQ2 msqueue2KlW

section
attribute [local instance] wLayoutQ2

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labQ2_at {x : Label} (i : Nat) (hd : msq2Image.drop i = Program.fromLabel msq2Image x := by decide)
    (hne : Program.fromLabel msq2Image x ≠ [] := by decide) : labQ2 x = (wLayoutQ2 msq2Image).addrOf i :=
  Program.label_addrOf_drop (by decide) hd hne

set_option maxRecDepth 8192 in
theorem enqWQ2_start : StartEQ2 0x1200 0x1300 0x1400 enqWQ2 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 : Int64) = labQ2 "enq"; rw [labQ2_at 0]; decide
  · show (0x100000 + 132 : Int64) = labQ2 "pdone"; rw [labQ2_at 42]; decide
  all_goals simp [enqWQ2, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem deqWQ2_start : StartDQ2 0x1000 0x1200 deqWQ2 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 + 136 : Int64) = labQ2 "deq1"; rw [labQ2_at 44]; decide
  · show (0x100000 + 276 : Int64) = labQ2 "ddone1"; rw [labQ2_at 84]; decide
  all_goals simp [deqWQ2, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`1:X10 = 1 ∧ 1:X11 = 2`** for `msqueue2.kl` under `Arch.armv8`, both threads
running the runner's executable: concrete instance of
`msqueue2_envG_whole`. -/
theorem msqueue2_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enqWQ2, deqWQ2] msq2InitMemW) c) (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 ∧
      th1.st.st.1.regs.X11.toBitVec = 2 :=
  msqueue2_envG_whole wLayoutQ2 0x1000 0x1200 0x1100 0x1300 0x1400 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    enqWQ2_start deqWQ2_start
    (by refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue2_envG_whole_concrete

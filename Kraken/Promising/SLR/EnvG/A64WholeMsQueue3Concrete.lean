/-
**A concrete instance of
`MsQueue.msqueue3_envG_whole`** — the `.kl` runner's own executable and
threads for `msqueue3.kl`.

- `codeMatchesWQ3`: the `.kl`'s `code` block parses to exactly `msq3Image`.
- `runnerMatchesWQ3`: the runner's prepared threads run exactly `msq3Image`
  laid out by `wLayoutQ3` (text at `0x100000`, each directive its
  `fakeSize`), thread `0` from `enq` (`0x100000`) to `pdone` (`0x100084`)
  with `X0 = head`, `X1 = tail`, `X12 = n1`, `X13 = n2`, thread `1` from
  `deq1` (`0x100088`) to `ddone1` (`0x1000d0`) and thread `2` from `deq2`
  (`0x1000d4`) to `ddone2` (`0x10011c`), both with `X0 = head`,
  `X1 = tail`, the runner's whole register file and empty private memory.
- `msqueue3_envG_whole_concrete`: the theorem there, at the runner's
  placement (`head = 0x1000`, `d = 0x1100`, `tail = 0x1200`,
  `n1 = 0x1300`, `n2 = 0x1400`); every hypothesis by `decide`/`rfl`/`simp`. No
  `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue3
import Kraken.Promising.SLR.EnvG.A64WholeRunner
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The runner's layout of the image. -/
@[reducible] def wLayoutQ3 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize msq3Image

instance wValidQ3 : Executable.ValidLayout (wLayoutQ3 msq3Image) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The enqueuer as the runner prepares it. -/
def enqWQ3 : AArch64.State where
  exe := wLayoutQ3 msq3Image
  endPc := 0x100000 + 132
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200, X12 := 0x1300, X13 := 0x1400 } }, 0x100000)

/-- The first dequeuer as the runner prepares it. -/
def deqAWQ3 : AArch64.State where
  exe := wLayoutQ3 msq3Image
  endPc := 0x100000 + 208
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200 } }, 0x100000 + 136)

/-- The second dequeuer as the runner prepares it. -/
def deqBWQ3 : AArch64.State where
  exe := wLayoutQ3 msq3Image
  endPc := 0x100000 + 284
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200 } }, 0x100000 + 212)

/-- The initial memory: `head = tail = d`, the links `0`. -/
def msq3InitMemW : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1200, 8⟩, 0x1100), (⟨0x1100 + 8, 8⟩, 0), (⟨0x1300 + 8, 8⟩, 0),
    (⟨0x1400 + 8, 8⟩, 0)]

/-- The `.kl` source. -/
def msqueue3KlW : String := include_str "../../../Examples/LockFree/AArch64/msqueue3.kl"

/-- The `code` block of `msqueue3.kl` parses to `msq3Image`. -/
def codeMatchesWQ3 (src : String) : Bool := A64Whole.codeIs src msq3Image

/-- info: true -/
#guard_msgs in
#eval codeMatchesWQ3 msqueue3KlW

/-- The runner's threads are `enqWQ3`, `deqAWQ3` and `deqBWQ3`. -/
def runnerMatchesWQ3 (src : String) : Bool := A64Whole.runnerIs src [enqWQ3, deqAWQ3, deqBWQ3]

/-- info: true -/
#guard_msgs in
#eval runnerMatchesWQ3 msqueue3KlW

section
attribute [local instance] wLayoutQ3

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labQ3_at {x : Label} (i : Nat) (hd : msq3Image.drop i = Program.fromLabel msq3Image x := by decide)
    (hne : Program.fromLabel msq3Image x ≠ [] := by decide) : labQ3 x = (wLayoutQ3 msq3Image).addrOf i :=
  Program.label_addrOf_drop (by decide) hd hne

set_option maxRecDepth 8192 in
theorem enqWQ3_start : StartEQ3 0x1200 0x1300 0x1400 enqWQ3 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 : Int64) = labQ3 "enq"; rw [labQ3_at 0]; decide
  · show (0x100000 + 132 : Int64) = labQ3 "pdone"; rw [labQ3_at 42]; decide
  all_goals simp [enqWQ3, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem deqAWQ3_start : StartDQ3 "deq1" "ddone1" 0x1000 0x1200 deqAWQ3 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 + 136 : Int64) = labQ3 "deq1"; rw [labQ3_at 44]; decide
  · show (0x100000 + 208 : Int64) = labQ3 "ddone1"; rw [labQ3_at 65]; decide
  all_goals simp [deqAWQ3, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem deqBWQ3_start : StartDQ3 "deq2" "ddone2" 0x1000 0x1200 deqBWQ3 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 + 212 : Int64) = labQ3 "deq2"; rw [labQ3_at 67]; decide
  · show (0x100000 + 284 : Int64) = labQ3 "ddone2"; rw [labQ3_at 88]; decide
  all_goals simp [deqBWQ3, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`(1:X10 = 1 ∧ 2:X10 = 2) ∨ (1:X10 = 2 ∧ 2:X10 = 1)`** for
`msqueue3.kl` under `Arch.armv8`, all three threads running the runner's
executable: concrete instance of `msqueue3_envG_whole`. -/
theorem msqueue3_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enqWQ3, deqAWQ3, deqBWQ3] msq3InitMemW) c)
    (hf : c.final = true) :
    ∃ th1 th2, c.threads[1]? = some th1 ∧ c.threads[2]? = some th2 ∧
      ((th1.st.st.1.regs.X10.toBitVec = 1 ∧ th2.st.st.1.regs.X10.toBitVec = 2) ∨
        (th1.st.st.1.regs.X10.toBitVec = 2 ∧ th2.st.st.1.regs.X10.toBitVec = 1)) :=
  msqueue3_envG_whole wLayoutQ3 0x1000 0x1200 0x1100 0x1300 0x1400 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    enqWQ3_start deqAWQ3_start deqBWQ3_start
    (by refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue3_envG_whole_concrete

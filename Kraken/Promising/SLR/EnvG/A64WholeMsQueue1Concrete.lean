/-
**A concrete instance of
`MsQueue.msqueue1_envG_whole`** — the `.kl` runner's own executable and
threads for `msqueue1.kl`.

- `codeMatchesWQ1`: the `.kl`'s `code` block parses to exactly `msq1Image`.
- `runnerMatchesWQ1`: the runner's prepared threads run exactly `msq1Image`
  laid out by `wLayoutQ1` (text at `0x100000`, each directive its
  `fakeSize`), thread `0` from `enq` (`0x100000`) to `pdone` (`0x100044`)
  with `X0 = head`, `X1 = tail`, `X12 = n1`, `X13 = n2`, thread `1` from
  `deq1` (`0x100048`) to `ddone1` (`0x100090`) with `X0 = head`,
  `X1 = tail`, the runner's whole register file and empty private memory.
- `msqueue1_envG_whole_concrete`: the theorem there, at the runner's
  placement (`head = 0x1000`, `d = 0x1100`, `tail = 0x1200`,
  `n1 = 0x1300`); every hypothesis by `decide`/`rfl`/`simp`. No
  `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeMsQueue1
import Kraken.Promising.SLR.EnvG.A64WholeRunner
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.SLR.EnvG.MsQueue

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The runner's layout of the image. -/
@[reducible] def wLayoutQ1 : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize msq1Image

instance wValidQ1 : Executable.ValidLayout (wLayoutQ1 msq1Image) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The enqueuer as the runner prepares it. -/
def enqWQ1 : AArch64.State where
  exe := wLayoutQ1 msq1Image
  endPc := 0x100000 + 68
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200, X12 := 0x1300, X13 := 0x1400 } }, 0x100000)

/-- The dequeuer as the runner prepares it. -/
def deqWQ1 : AArch64.State where
  exe := wLayoutQ1 msq1Image
  endPc := 0x100000 + 144
  st := ({ regs := { X0 := 0x1000, X1 := 0x1200 } }, 0x100000 + 72)

/-- The initial memory: `head = tail = d`, the links `0`. -/
def msq1InitMemW : List (Loc × Val) :=
  [(⟨0x1000, 8⟩, 0x1100), (⟨0x1200, 8⟩, 0x1100), (⟨0x1100 + 8, 8⟩, 0), (⟨0x1300 + 8, 8⟩, 0)]

/-- The `.kl` source. -/
def msqueue1KlW : String := include_str "../../../Examples/LockFree/AArch64/msqueue1.kl"

/-- The `code` block of `msqueue1.kl` parses to `msq1Image`. -/
def codeMatchesWQ1 (src : String) : Bool := A64Whole.codeIs src msq1Image

/-- info: true -/
#guard_msgs in
#eval codeMatchesWQ1 msqueue1KlW

/-- The runner's threads are `enqWQ1` and `deqWQ1`. -/
def runnerMatchesWQ1 (src : String) : Bool := A64Whole.runnerIs src [enqWQ1, deqWQ1]

/-- info: true -/
#guard_msgs in
#eval runnerMatchesWQ1 msqueue1KlW

section
attribute [local instance] wLayoutQ1

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labQ1_at {x : Label} (i : Nat) (hd : msq1Image.drop i = Program.fromLabel msq1Image x := by decide)
    (hne : Program.fromLabel msq1Image x ≠ [] := by decide) : labQ1 x = (wLayoutQ1 msq1Image).addrOf i :=
  Program.label_addrOf_drop (by decide) hd hne

set_option maxRecDepth 8192 in
theorem enqWQ1_start : StartEQ1 0x1200 0x1300 enqWQ1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 : Int64) = labQ1 "enq"; rw [labQ1_at 0]; decide
  · show (0x100000 + 68 : Int64) = labQ1 "pdone"; rw [labQ1_at 22]; decide
  all_goals simp [enqWQ1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem deqWQ1_start : StartDQ1 0x1000 0x1200 deqWQ1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, fun a => ?_, fun a => ?_⟩
  · show (0x100000 + 72 : Int64) = labQ1 "deq1"; rw [labQ1_at 24]; decide
  · show (0x100000 + 144 : Int64) = labQ1 "ddone1"; rw [labQ1_at 45]; decide
  all_goals simp [deqWQ1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`1:X10 = 1`** for `msqueue1.kl` under `Arch.armv8`, both threads
running the runner's executable: concrete instance of
`msqueue1_envG_whole`. -/
theorem msqueue1_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [enqWQ1, deqWQ1] msq1InitMemW) c) (hf : c.final = true) :
    ∃ th1, c.threads[1]? = some th1 ∧ th1.st.st.1.regs.X10.toBitVec = 1 :=
  msqueue1_envG_whole wLayoutQ1 0x1000 0x1200 0x1100 0x1300 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) enqWQ1_start deqWQ1_start
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Config.init] <;> decide) hc hf

end Kraken.Promising.SLR.EnvG.MsQueue

#print axioms Kraken.Promising.SLR.EnvG.MsQueue.msqueue1_envG_whole_concrete

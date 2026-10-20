/-
**A concrete instance of
`Relay.mp_relay3_swpl_envG_whole`** — the `.kl` runner's own executable and
threads for `mp_relay3_swpl.kl`.

- `codeMatchesWS`: the `.kl`'s `code` block parses to exactly
  `relaySwpl3Img`.
- `runnerMatchesWS`: the runner's prepared threads run exactly
  `relaySwpl3Img` laid out by `wLayoutS` (text at `0x100000`, each directive
  its `fakeSize`), thread `0` from `writer` (`0x100000`) to `wdone`
  (`0x100014`) with `X0 = f1`, `X1 = d`, thread `1` from `relay`
  (`0x100018`) to `rdone` (`0x100034`) with `X0 = f1`, `X1 = d`, `X2 = f2`,
  thread `2` from `reader` (`0x100038`) to `ddone` (`0x100048`) with
  `X0 = f2`, `X1 = d`, the runner's whole register file and empty private
  memory.
- `mp_relay3_swpl_envG_whole_concrete`: the theorem there, at the runner's
  placement (`d = 0x1000`, `f1 = 0x1100`, `f2 = 0x1200`); every hypothesis
  by `decide`/`rfl`/`simp`. No `native_decide`.
-/
import Kraken.Promising.SLR.EnvG.A64WholeRelaySwpl
import Kraken.Promising.SLR.EnvG.A64WholeRunner
import Kraken.AArch64.WP.LayoutOfSize

namespace Kraken.Promising.SLR.EnvG.Relay

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The runner's layout of the image. -/
@[reducible] def wLayoutS : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize relaySwpl3Img

instance wValidS : Executable.ValidLayout (wLayoutS relaySwpl3Img) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The initial memory: the three words at `0`. -/
def relaySwpl3InitMem : List (Loc × Val) := [(⟨0x1000, 4⟩, 0), (⟨0x1100, 4⟩, 0), (⟨0x1200, 4⟩, 0)]

/-- The writer as the runner prepares it. -/
def writerS0 : AArch64.State where
  exe := wLayoutS relaySwpl3Img
  endPc := 0x100000 + 20
  st := ({ regs := { X0 := 0x1100, X1 := 0x1000 } }, 0x100000)

/-- The `swpl` relay as the runner prepares it. -/
def relayS1 : AArch64.State where
  exe := wLayoutS relaySwpl3Img
  endPc := 0x100000 + 52
  st := ({ regs := { X0 := 0x1100, X1 := 0x1000, X2 := 0x1200 } }, 0x100000 + 24)

/-- The reader as the runner prepares it. -/
def readerS2 : AArch64.State where
  exe := wLayoutS relaySwpl3Img
  endPc := 0x100000 + 72
  st := ({ regs := { X0 := 0x1200, X1 := 0x1000 } }, 0x100000 + 56)

/-- The `.kl` source. -/
def relaySwpl3Kl : String := include_str "../../../Examples/LockFree/AArch64/mp_relay3_swpl.kl"

/-- The `code` block of `mp_relay3_swpl.kl` parses to `relaySwpl3Img`. -/
def codeMatchesWS (src : String) : Bool := A64Whole.codeIs src relaySwpl3Img

/-- info: true -/
#guard_msgs in
#eval codeMatchesWS relaySwpl3Kl

/-- The runner's threads are `writerS0`, `relayS1` and `readerS2`. -/
def runnerMatchesWS (src : String) : Bool := A64Whole.runnerIs src [writerS0, relayS1, readerS2]

/-- info: true -/
#guard_msgs in
#eval runnerMatchesWS relaySwpl3Kl

section
attribute [local instance] wLayoutS

set_option maxRecDepth 8192 in
/-- A label's address from its position in the image. -/
theorem labS3_at {x : Label} (i : Nat) (hd : relaySwpl3Img.drop i = Program.fromLabel relaySwpl3Img x := by decide)
    (hne : Program.fromLabel relaySwpl3Img x ≠ [] := by decide) : labS3 x = (wLayoutS relaySwpl3Img).addrOf i :=
  Program.label_addrOf_drop (by decide) hd hne

set_option maxRecDepth 8192 in
theorem writerS0_start : StartWS3 0x1100 0x1000 writerS0 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · show (0x100000 : Int64) = labS3 "writer"; rw [labS3_at 0]; decide
  · show (0x100000 + 20 : Int64) = labS3 "wdone"; rw [labS3_at 6]; decide
  all_goals simp [writerS0, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem relayS1_start : StartYS3 0x1100 0x1200 0x1000 relayS1 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · show (0x100000 + 24 : Int64) = labS3 "relay"; rw [labS3_at 8]; decide
  · show (0x100000 + 52 : Int64) = labS3 "rdone"; rw [labS3_at 16]; decide
  all_goals simp [relayS1, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

set_option maxRecDepth 8192 in
theorem readerS2_start : StartDS3 0x1200 0x1000 readerS2 := by
  refine ⟨rfl, rfl, ?_, ?_, by decide, by decide, ?_, ?_⟩
  · show (0x100000 + 56 : Int64) = labS3 "reader"; rw [labS3_at 18]; decide
  · show (0x100000 + 72 : Int64) = labS3 "ddone"; rw [labS3_at 23]; decide
  all_goals simp [readerS2, Mem.loadInt, Mem.loadBytes, List.allSome, List.range_succ]

end

/-- **`2:X4 = 43 ∧ [d] = 43`** for `mp_relay3_swpl.kl` under `Arch.armv8`,
the three threads running the runner's executable: concrete instance of
`mp_relay3_swpl_envG_whole`. -/
theorem mp_relay3_swpl_envG_whole_concrete {fuel : Nat} {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [writerS0, relayS1, readerS2] relaySwpl3InitMem) c)
    (hf : c.final = true) :
    (∃ t, c.threads[2]? = some t ∧ BitVec.setWidth 32 t.st.st.1.regs.X4.toBitVec = 43) ∧
      c.mem.finalVal ⟨0x1000, 4⟩ = 43#128 :=
  mp_relay3_swpl_envG_whole wLayoutS 0x1100 0x1200 0x1000 ⟨by decide, by decide, by decide⟩ writerS0_start
    relayS1_start readerS2_start (by simp only [Config.init]; decide) (by simp only [Config.init]; decide) hc hf

end Kraken.Promising.SLR.EnvG.Relay

#print axioms Kraken.Promising.SLR.EnvG.Relay.mp_relay3_swpl_envG_whole_concrete

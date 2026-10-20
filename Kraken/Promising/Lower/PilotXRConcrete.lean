/-
**Concrete instance of `Lower.PilotXR.pilotXR_promising`.**
ISA: x64; machine: the executable Promising machine
(`Reachable Arch.tso`).

The instance is at the explorer's configuration of `Lower/PilotXRProg.lean`
(the one its `#guard_msgs` run explores): the layout `xrLayout` (text at
`0x100000`, labels 0 bytes, every instruction 1), the start states
`threadXR 0x2000` and `threadXR 0x3000` (`rbx = &top = 0x1000`, the arena of
thread `w` at its node, `r11` the end of the text, `dmem` empty) and the
initial memory `initMemXR` (`top = 0`).

- `pXR`: the parameters (`top` at `0x1000`, node `0` at `0x2000`, node `1`
  at `0x3000`) and `pXR_locs` (`TLocs`, by `decide`).
- `threadXR_start`: both start states satisfy `StartXR` (by `rfl`/`decide`,
  the label addresses through `Program.label_addrOf_drop` and `labXR_done`).
- `pilotXR_concrete`: every final configuration reachable under `Arch.tso`
  from that configuration has the two threads' `r12` the two nodes
  `0x2000`/`0x3000`, in some order. Its only hypotheses are the
  reachability `hc` and finality `hf`.
-/
import Kraken.Promising.Lower.PilotXRWhole
import Kraken.Promising.SLR.EnvG.ConcreteCommon

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.PilotXR.Concrete

open Kraken.Promising.Lower.PilotXR
open Kraken.Promising.X64.EnvG.Treiber2X

/-- The explorer's parameters: `top` at `0x1000`, node `0` at `0x2000`,
node `1` at `0x3000` (`threadXR`'s arenas). -/
def pXR : Params := ⟨0x1000, fun w => if w = 0 then 0x2000 else 0x3000⟩

/-- `top` is not a node; the nodes are distinct and non-null. -/
theorem pXR_locs : TLocs pXR :=
  ⟨by decide, by decide, by decide⟩

section
attribute [local instance] xrLayout

/-- `main` is the start of the text. -/
theorem labXR_main : labXR "main" = (0x100000 : Int64) := by
  rw [show labXR "main" = (xrLayout pilotXR).addrOf 0 from
    Program.label_addrOf_drop pilotXR_nodup (by decide) (by decide)]
  decide

/-- `done` is `endXR`, the end of the text. -/
theorem labXR_done' : labXR "done" = endXR := by
  rw [labXR_done]; decide

/-- **Both explorer start states satisfy `StartXR`.** -/
theorem threadXR_start (w : Nat) (hw : w < 2) :
    StartXR pXR w (threadXR (if w = 0 then 0x2000 else 0x3000)) := by
  refine ⟨rfl, rfl, labXR_main.symm, labXR_done'.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [labXR_done']; rfl
  · rfl
  · rcases w with _ | _ | w
    · rfl
    · rfl
    · omega
  · rcases w with _ | _ | w
    · decide
    · decide
    · omega
  · intro k; simp [threadXR]

/-- **The stackless x64 Treiber pilot at the explorer's configuration**:
every final configuration reachable under `Arch.tso` from the two
`threadXR` threads and `initMemXR` has the threads' `r12` the two nodes
(`0x2000`, `0x3000`), in some order. -/
theorem pilotXR_concrete {fuel : Nat} {cfg : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [threadXR 0x2000, threadXR 0x3000] initMemXR) cfg)
    (hf : cfg.final = true) : Treiber2FinalX 0x2000 0x3000 cfg :=
  pilotXR_promising (layout := xrLayout) (P := pXR) pXR_locs (threadXR_start 0 (by decide))
    (threadXR_start 1 (by decide)) (by simp only [Config.init_mem]; decide) hc hf

end

end Kraken.Promising.Lower.PilotXR.Concrete

#print axioms Kraken.Promising.Lower.PilotXR.Concrete.pilotXR_concrete

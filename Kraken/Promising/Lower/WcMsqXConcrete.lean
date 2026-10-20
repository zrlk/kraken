/-
**Concrete instance of `Lower.WcMsqX.wcMsqX_promising`** (non-vacuity), at
the explorer's configuration of `Lower/WcMsqXProg.lean` (layout `wxLayout
wcMsqX`, start states `thr wcMsqX 50 0 …` at `main_e` and `thr wcMsqX 50 26 …`
at `main_w`, memory `initMemW`). ISA: x64.
`pW_locs` (`QLocs`) is by `decide`; `initMemW_initV` gives `InitV` of
`Config.init`; `wcMsqX_concrete` has only the reachability `hc` (under
`Arch.tso`) and finality `hf` as hypotheses.
-/
import Kraken.Promising.Lower.WcMsqXWhole
import Kraken.Promising.SLR.EnvG.ConcreteCommon

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG Kraken.Promising.X64 Kraken.Promising.X64.EnvG

namespace Kraken.Promising.Lower.WcMsqX.Concrete

open Kraken.Promising.Lower.WcMsqX
open Kraken.Promising.X64.EnvG.MsQueueX

/-- The explorer's parameters: `head` at `0x1000`, `tail` at `0x1008`, the
sentinel at `0x2000`, the nodes at `0x2100`/`0x2200`; untracked swings. -/
def pW : Params := ⟨0x1000, 0x1008, 0x2000, 0x2100, 0x2200, false⟩

/-- `head`, `tail` and the three links are distinct; the nodes non-null. -/
theorem pW_locs : QLocs pW :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide⟩

/-- The explorer's layout of `wcMsqX`. -/
@[reducible] def wLayout : _root_.Layout := wxLayout wcMsqX

instance wValid : Executable.ValidLayout (wLayout wcMsqX) :=
  Concrete.validLayout_of_cells _ (by decide) (by decide)

/-- The enqueuer's explorer start state. -/
def threadEW : X64.State := thr wcMsqX 50 0 0x1008 0x2100 0x2200

/-- The dequeuer's explorer start state. -/
def threadWW : X64.State := thr wcMsqX 50 26 0x1000 0 0

section
attribute [local instance] wLayout
set_option maxRecDepth 20000
theorem labW_main_e : labW "main_e" = (0x100000 : Int64) := by
  rw [show labW "main_e" = (wLayout wcMsqX).addrOf 0 from
    Program.label_addrOf_drop wcMsqX_wf.nodup (by decide) (by decide)]
  decide

/-- `main_w` is `26` instructions in (cell `31`). -/
theorem labW_main_w : labW "main_w" = (0x100000 + 26 : Int64) := by
  rw [show labW "main_w" = (wLayout wcMsqX).addrOf 31 from
    Program.label_addrOf_drop wcMsqX_wf.nodup (by decide) (by decide)]
  decide

/-- `done` is the end of the text (`50` instructions). -/
theorem labW_done' : labW "done" = (0x100000 + Int64.ofNat 50 : Int64) := by
  rw [labW_done]; decide

theorem threadEW_start : StartEW pW threadEW := by
  refine ⟨rfl, rfl, labW_main_e.symm, labW_done'.symm, ?_, rfl, rfl, rfl, ?_⟩
  · rw [labW_done']; rfl
  · intro k; simp [threadEW, thr]

theorem threadWW_start : StartW pW threadWW := by
  refine ⟨rfl, rfl, labW_main_w.symm, labW_done'.symm, ?_, rfl, ?_⟩
  · rw [labW_done']; rfl
  · intro k; simp [threadWW, thr]

/-- **The explorer's initial memory initialises the queue** (`InitV`). -/
theorem initMemW_initV : InitV (Config.init (I := isa) [threadEW, threadWW] initMemW).mem pW := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [pW, Params.head, Params.tail, Params.ls, Params.l1, Params.l2, Config.init_mem] <;> decide

end

/-- **WeakCore's try-once Michael–Scott queue lowered to x64, at the
explorer's configuration**: every final configuration reachable under
`Arch.tso` has the dequeuer's results among `(0x2100, 0x2200)`,
`(0x2100, ∅)`, `(∅, 0x2100)`, `(∅, ∅)`. -/
theorem wcMsqX_concrete {fuel : Nat} {cfg : Config isa}
    (hc : Reachable Arch.tso fuel (Config.init [threadEW, threadWW] initMemW) cfg)
    (hf : cfg.final = true) : WcMsqXFinal 0x2100 0x2200 cfg :=
  wcMsqX_promising (layout := wLayout) (P := pW) pW_locs rfl threadEW_start threadWW_start initMemW_initV hc hf

end Kraken.Promising.Lower.WcMsqX.Concrete

#print axioms Kraken.Promising.Lower.WcMsqX.Concrete.wcMsqX_concrete

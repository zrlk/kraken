/-
**The successors of `scc_rt_thread_init`'s and `scc_rt_stack_take`'s
memory instructions keep `sp` and `x30`** (AArch64; as `Tcb2W.keep_rmw` /
`keep_hdr`): a swap, a load, a release store and a store of an unmapped
word step to the next pc writing neither `sp` nor `x30`; at the take site
the take writes only memory (`keep_take`).

- `keep_swp`, `keep_ldr`, `keep_stlr`, `keep_str`.
-/
import Spike.Lib.A64WakeStartTiG
import Spike.Lib.A64WakeWfW2

namespace Spike.Lib.A64.WakePh.StartTi

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (abi)
open Spike.Lib.A64ConsumerA (StSucc)

variable {μ : Scc.Sem.Marks} {s s' : State}

/-- **The lock's swap `swp<k> Xs, x11, [Xn]`** of an unmapped word keeps
`sp` and `x30`. -/
theorem keep_swp {kk : Kraken.RmwKind} {rs b : XReg}
    (hc : Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.WakeWf.swpDir kk rs .X11 b) 4)
    (hdc : s.decls = {}) (hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg b).toBitVec 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm hd; cases hd)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_swp hc hdm] at htr
    cases htr
    rw [hdc, EvTree.access_empty] at hl
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **The free count's load `ldr x9, [Xn, #i]`** of an unmapped word keeps
`sp` and `x30`. -/
theorem keep_ldr {b : XReg} {i : Int64}
    (hc : Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.ldrDir .X9 b i) 4)
    (hdc : s.decls = {}) (hdm : Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.rAddr s.st.1.regs b i) 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm hd; cases hd)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_ldr_agrees hc rfl hdm (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)] at htr
    cases htr
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **A release store `stlr Xt, [Xn]`** of an unmapped word keeps `sp` and
`x30`. -/
theorem keep_stlr {t b : XReg}
    (hc : Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.WakeWf.stlrDir t b) 4)
    (hdc : s.decls = {}) (hdm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg b).toBitVec 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm hd; cases hd)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_stlr_agrees hc hdm (Spike.Lib.A64.Flow.agrees_of_decls hdc _ _)] at htr
    cases htr
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **A store `str Xt, [Xn, #i]`** of an unmapped word keeps `sp` and
`x30`. -/
theorem keep_str {t b : XReg} {i : Int64}
    (hc : Kraken.Promising.Lower.A64.CellAt s (Spike.Lib.A64.Flow.strDir t b i) 4)
    (hdc : s.decls = {}) (hdm : Mem.loadInt s.st.1.dmem (Spike.Lib.A64.Flow.rAddr s.st.1.regs b i) 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (by intro imm hd; cases hd)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_str hc rfl hdm] at htr
    cases htr
    rw [hdc, EvTree.access_empty] at hl
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- info: 'Spike.Lib.A64.WakePh.StartTi.keep_swp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keep_swp

/-- info: 'Spike.Lib.A64.WakePh.StartTi.keep_ldr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keep_ldr

/-- info: 'Spike.Lib.A64.WakePh.StartTi.keep_stlr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keep_stlr

/-- info: 'Spike.Lib.A64.WakePh.StartTi.keep_str' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms keep_str

end Spike.Lib.A64.WakePh.StartTi

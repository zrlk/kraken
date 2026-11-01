/-
**hello.w's ghost records' facts at the record's own placement**: `okHR`,
the predicate of hello's root records `{g : Gh // okHR Λ lB g}`. It is
`HelloOkW.okH` without a family-wide placement `lbl'` or flag `cSf`: wake's
`GhOK` (as `WakeWorkerR.ghOK_of_clone` builds it, at the record's own
placement and flag) and rodata's buffer placed at the record's placement
(`BufPl`, its base some `b0`).

- `okHR Λ lB g`: `GhOK Λ g ∧ ∃ b0, BufPl g.lbl g.lsize g.cS lB b0`.
- `okHR_ghOK`, `okHR_buf`: the projections; `okHR_bufAt`: `BufPl` at any
  base the record's placement gives `lB` (the base is the placement's);
  `okHR_cT`, `okHR_Spos`: `GhOK`'s `cT` shape and nonempty source memory.
- `okHR_frzS`, `okHR_ne_cS`, `okHR_frz`: `HelloInst.frzS_buf` /
  `buf_ne_cS` / `frz_buf` at location data whose placement and flag are
  the record's.
- `okHR_recW`: the record built at the clone (`WakeOkW.recW`) satisfies
  `okHR` from `WakeOkW.okW_of_clone`'s premises at the record's own
  placement and flag and the buffer's placement.
-/
import Spike.Lib.HelloOkW

namespace Spike.Lib.HelloOkHR

open Kraken.Promising Scc.Sem
open Spike.Lib Spike.Lib.WakeInst Spike.Lib.WakeOkW Spike.Lib.WakeP
open Spike.Lib.WakeInstFields (GhOK)
open Spike.Lib.HelloInst (BufPl helloP frzS_buf buf_ne_cS frz_buf)

/-- **hello.w's ghost records' facts**: wake's `GhOK`, and rodata's buffer
`lB` placed at the record's placement (`BufPl`: two words, off `c`). -/
def okHR (Λ : Scc.Sem.Layout) (lB : WeakMem.AllocLabel) (g : Gh) : Prop :=
  GhOK Λ g ∧ ∃ b0, BufPl g.lbl g.lsize g.cS lB b0

section Proj

variable {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} (w : {g : Gh // okHR Λ lB g})

theorem okHR_ghOK : GhOK Λ w.1 := w.2.1
theorem okHR_buf : ∃ b0, BufPl w.1.lbl w.1.lsize w.1.cS lB b0 := w.2.2

/-- `BufPl` at the base the record's placement gives the buffer. -/
theorem okHR_bufAt {b0 : Nat} (hb : w.1.lbl lB = some b0) : BufPl w.1.lbl w.1.lsize w.1.cS lB b0 := by
  obtain ⟨b, h1, h2, h3⟩ := okHR_buf w
  rw [hb] at h1; cases h1
  exact ⟨hb, h2, h3⟩

/-- `WakeCompatI.hC_I`'s `cT` (as `WakeOkW.okW_cT`). -/
theorem okHR_cT : ∃ a, w.1.cT = wordLoc a ∧ wordAddr w.1.lbl w.1.cS = some a ∧
    w.1.cS.offset < w.1.lsize w.1.cS.label := by
  obtain ⟨b, hl, ho, hT⟩ := w.2.1.2.2.2.1
  exact ⟨_, hT, by simp [wordAddr, hl], ho⟩

/-- The source memory is nonempty at the spawn. -/
theorem okHR_Spos : 0 < w.1.S := w.2.1.2.2.1

end Proj

/-! ## The buffer's words are frozen at the record's location data -/

section Frz

variable {I : ISA} {K : Kernel.Abi I} {μ : Marks} {W : WakeLocs}
  {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} {b0 : Nat} (w : {g : Gh // okHR Λ lB g})
  (hb : w.1.lbl lB = some b0) (hl : W.lbl = w.1.lbl) (hs : W.lsize = w.1.lsize) (hc : W.cS = w.1.cS)

include hb hl hs hc in
/-- `BufPl` at location data whose placement and flag are the record's. -/
theorem bufPlR_W : BufPl W.lbl W.lsize W.cS lB b0 := by
  rw [hl, hs, hc]; exact okHR_bufAt w hb

include hb hl hs hc in
/-- **The buffer's source words are frozen** (`frzS_buf`). -/
theorem okHR_frzS {i : Nat} (hi : i < 2) : (helloP K μ W).frzS ⟨lB, i⟩ :=
  frzS_buf (bufPlR_W w hb hl hs hc) hi

include hb hl hs hc in
/-- **The buffer's words are not `c`** (`buf_ne_cS`). -/
theorem okHR_ne_cS (i : Nat) : (⟨lB, i⟩ : WeakMem.Address) ≠ W.cS :=
  buf_ne_cS (bufPlR_W w hb hl hs hc) i

include hb hl hs hc in
/-- **The buffer's target words are frozen** (`frz_buf`), `cT`'s shape from
`okHR_cT` at `W.cT = w.1.cT`. -/
theorem okHR_frz {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hT : W.cT = w.1.cT) (h : MemRelP Λ W.lbl W.lsize ts tm sm tp tq sp) (hwf : Λ.WF)
    {i : Nat} (hi : i < 2) : (helloP K μ W).frz (wordLoc (b0 + 8 * i)) := by
  refine frz_buf h hwf (bufPlR_W w hb hl hs hc) ?_ hi
  rw [hT, hl, hs, hc]; exact okHR_cT w

end Frz

/-! ## The record built at the clone -/

/-- **The record built at the clone satisfies `okHR`**:
`WakeOkW.okW_of_clone` at the record's own placement and flag (as
`WakeWorkerR.ghOK_of_clone`), and the buffer's placement. -/
theorem okHR_recW {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} {b0 : Nat} {T S : Nat}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {l : WeakMem.AllocLabel}
    {pT : Loc} {cw : TermRun.Word} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (hm : MemRelP Λ lbl lsize ts tm sm tp tq sp) (hwf : Λ.WF)
    {cA : Nat} (hv : ValRep lbl (.loc ⟨l, 0⟩ 0) cA) (hcw : cw.val = .loc ⟨l, 0⟩ 0)
    (hin : 0 < lsize l) (hS : 0 < S) (hB : BufPl lbl lsize ⟨l, 0⟩ lB b0) :
    okHR Λ lB (recW T S lbl lsize l pT cw) :=
  ⟨(okW_of_clone hm hwf hv hcw hin hS rfl rfl).1, b0, hB⟩

end Spike.Lib.HelloOkHR

/-- info: 'Spike.Lib.HelloOkHR.okHR_bufAt' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.HelloOkHR.okHR_bufAt

/-- info: 'Spike.Lib.HelloOkHR.okHR_frz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloOkHR.okHR_frz

/-- info: 'Spike.Lib.HelloOkHR.okHR_recW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloOkHR.okHR_recW

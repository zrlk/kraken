/-
**hello.w's ghost records' facts at the record's own placement** (x86-64; the twin of
`Spike/Lib/HelloOkHR.lean`, its live part): `okHR`, the predicate of hello's root records
`{g : Gh // okHR Λ lB T W g}`: wake's `GhOK` (at the record's own placement and flag), rodata's buffer placed at
the record's placement (`BufPl`, its base some `b0`), and the self words `T`, `W` off the record's labels and flag
(`X64WakeInst.SelfOK`, wake's `GhOKR` conjunct).

- `okHR Λ lB T W g`: `GhOK Λ g ∧ (∃ b0, BufPl g.lbl g.lsize g.cS lB b0) ∧ SelfOK T W g`.
- `okHR_buf`, `okHR_self`: the projections; `okHR_bufAt`: `BufPl` at any base the record's placement gives `lB`;
  `okHR_cT`, `okHR_Spos`: `GhOK`'s `cT` shape and nonempty source memory.
- `bufPlR_W`, `okHR_frz`: `BufPl` and `X64HelloInst.frz_buf` at location data whose placement and flag are the
  record's.
- `okHR_recW`: the record built at the clone (`X64WakeOkW.recW`) satisfies `okHR` from
  `X64WakeOkW.okW_of_clone`'s premises at the record's own placement and flag, the buffer's placement and the
  record's `SelfOK` (`X64HelloSelfOK.selfOK_placedH` at the instance).

**Where this differs from AArch64**: the statements and proofs are A64's over x86-64's `X64WakeInst.Gh`,
`X64WakeInstFields.GhOK` and `X64WakeOkW` (same shapes), with `BufPl`, `helloP`, `frz_buf` from
`X64HelloInstFrz`; the `SelfOK` conjunct has no AArch64 counterpart (x86-64's memory sides own the TCB words
`%fs:0` reads, so the records keep them off their labels and flag). A64's `okHR_ghOK`, `okHR_frzS` and `okHR_ne_cS` are not used by the hello proof and are not
restated.
-/
import Spike.Lib.X64WakeOkW
import Spike.Lib.X64HelloInstFrz

namespace Spike.Lib.X64HelloOkHR

open Kraken.Promising Scc.Sem
open Spike.Lib Spike.Lib.X64WakeInst Spike.Lib.X64WakeOkW Spike.Lib.WakeP
open Spike.Lib.X64WakeInstFields (GhOK)
open Spike.Lib.X64HelloInst (BufPl helloP frz_buf)

/-- **hello.w's ghost records' facts**: wake's `GhOK`, rodata's buffer
`lB` placed at the record's placement (`BufPl`: two words, off `c`), and
`SelfOK T W` (the TCB words off the labels, `c`'s word not main's). `T` and
`W` are explicit because `okHR` sees only the layout `Λ`, not the runtime
layout's `pinA` they are offsets of. -/
def okHR (Λ : Scc.Sem.Layout) (lB : WeakMem.AllocLabel) (T W : BitVec 64) (g : Gh) : Prop :=
  GhOK Λ g ∧ (∃ b0, BufPl g.lbl g.lsize g.cS lB b0) ∧ SelfOK T W g

section Proj

variable {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} {T W : BitVec 64} (w : {g : Gh // okHR Λ lB T W g})

theorem okHR_buf : ∃ b0, BufPl w.1.lbl w.1.lsize w.1.cS lB b0 := w.2.2.1

/-- The record's self words (`X64HelloMs.helloLocs_okG`'s `hself` at the instance). -/
theorem okHR_self : SelfOK T W w.1 := w.2.2.2

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
  {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} {T1 W1 : BitVec 64} {b0 : Nat}
  (w : {g : Gh // okHR Λ lB T1 W1 g})
  (hb : w.1.lbl lB = some b0) (hl : W.lbl = w.1.lbl) (hs : W.lsize = w.1.lsize) (hc : W.cS = w.1.cS)

include hb hl hs hc in
/-- `BufPl` at location data whose placement and flag are the record's. -/
theorem bufPlR_W : BufPl W.lbl W.lsize W.cS lB b0 := by
  rw [hl, hs, hc]; exact okHR_bufAt w hb

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
    (hin : 0 < lsize l) (hS : 0 < S) (hB : BufPl lbl lsize ⟨l, 0⟩ lB b0) {T1 W1 : BitVec 64}
    (hself : SelfOK T1 W1 (recW T S lbl lsize l pT cw)) :
    okHR Λ lB T1 W1 (recW T S lbl lsize l pT cw) :=
  ⟨(okW_of_clone hm hwf hv hcw hin hS rfl rfl).1, ⟨b0, hB⟩, hself⟩

end Spike.Lib.X64HelloOkHR

/-- info: 'Spike.Lib.X64HelloOkHR.okHR_buf' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_buf

/-- info: 'Spike.Lib.X64HelloOkHR.okHR_self' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_self

/-- info: 'Spike.Lib.X64HelloOkHR.okHR_cT' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_cT

/-- info: 'Spike.Lib.X64HelloOkHR.okHR_Spos' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_Spos

/-- info: 'Spike.Lib.X64HelloOkHR.bufPlR_W' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.bufPlR_W


/-- info: 'Spike.Lib.X64HelloOkHR.okHR_bufAt' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_bufAt

/-- info: 'Spike.Lib.X64HelloOkHR.okHR_frz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_frz

/-- info: 'Spike.Lib.X64HelloOkHR.okHR_recW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOkHR.okHR_recW

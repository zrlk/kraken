/-
**main's owned words after the spawn** (x86-64): the facts main's rows need now that `WCompat0.own0` reads the
relation's owned words `Q.own w 0 s []` (constant, `ownConst0`; never a
runtime write's target, `ownMp0`; in main's cover set, `ownCov0`) in place of
none, so that main may own its TCB word (`X64WakeOwnX.wakeOwnX`).

- `tlatestP_erase_out`, `ownVal_erase_out`, `ownOk_erase_out`: a fulfilment of
  a promise to another location keeps the owned words reading as their values.
- `ownOk_promise'`: a promise keeps them (`Scc.Sem.ownVal_promise`, no cover).
- `stepOneWith_cohL`: one step under any certification semantics keeps the
  restricted cover (`Inv2Core.stepOne_cohL`'s form of `stepOneWith_cohP`).
- `Parts.own0_const`, `Parts.ownOk0`, `Parts.own0`, `Parts.ownDisj0`,
  `Parts.ownCov0`, `Parts.ownMp0`: thread 0's own facts of `Parts`' core at
  any new state of main.
-/
import Spike.Lib.X64WakeW1Keep
import Spike.Lib.X64WakeM0Compat
import Spike.Lib.Inv2CohL
import Scc.Sem.CertStep

namespace Spike.Lib.X64WakeM0

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.Inv2Core Spike.Lib.X64WakeW1

/-! ## The owned words under a fulfilment and a promise -/

/-- **The latest write not promised of a word survives a fulfilment** of a
promise to another location. -/
theorem tlatestP_erase_out {tm : Memory} {prom : List Time} {a k : Nat} (h : TLatestP tm prom a k) {q : Nat}
    {wq : Msg} (hg : tm.get? q = some wq) (hw : wq.loc ≠ wordLoc a) : TLatestP tm (prom.erase q) a k := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun k'' w' hlt hg' hl => ?_⟩
  · rcases h1 with h0 | ⟨w', hg', hl, hp⟩
    · exact .inl h0
    · exact .inr ⟨w', hg', hl, fun hm => hp (List.mem_of_mem_erase hm)⟩
  · have hne : k'' ≠ q := by
      rintro rfl; rw [hg] at hg'; cases hg'; exact hw hl
    exact (List.mem_erase_of_ne hne).mpr (h2 k'' w' hlt hg' hl)

/-- **A word's value survives a fulfilment** of a promise to another
location. -/
theorem ownVal_erase_out {tm : Memory} {prom : List Time} {a : Nat} {v : Val} (h : OwnVal tm prom a v) {q : Nat}
    {wq : Msg} (hg : tm.get? q = some wq) (hw : wq.loc ≠ wordLoc a) : OwnVal tm (prom.erase q) a v :=
  let ⟨k, hl, hr⟩ := h
  ⟨k, tlatestP_erase_out hl hg hw, hr⟩

/-- **The owned words keep their values under a fulfilment** of a promise to
none of them. -/
theorem ownOk_erase_out {own : List (Loc × Val)} {tm : Memory} {prom : List Time} (h : ExtRows.OwnOk own tm prom)
    {q : Nat} {wq : Msg} (hg : tm.get? q = some wq) (hw : ∀ L v, (L, v) ∈ own → wq.loc ≠ L) :
    ExtRows.OwnOk own tm (prom.erase q) := by
  intro L v hm
  obtain ⟨hb, hv⟩ := h L v hm
  refine ⟨hb, ownVal_erase_out hv hg ?_⟩
  rw [← ExtRows.loc_wordLoc hb]
  exact hw L v hm

/-- **A promise keeps the owned words reading as their values**
(`Scc.Sem.ownVal_promise`; no cover needed). -/
theorem ownOk_promise' {own : List (Loc × Val)} {mem : Memory} {prom : List Time} (h : ExtRows.OwnOk own mem prom)
    (w : Msg) : ExtRows.OwnOk own (mem.append w).1 (prom ++ [(mem.append w).2]) :=
  fun L v hm => let ⟨hb, hv⟩ := h L v hm; ⟨hb, ownVal_promise hv w⟩

/-- **One step under any certification semantics keeps the restricted
cover.** -/
theorem stepOneWith_cohL {I : ISA} (A : Arch) {cs : CertSem I} {t : Thread I} {tid : Nat} {mem : Memory}
    {L : Loc → Prop} {outs : List (Except String (Kraken.Promising.Outcome I))} {o : Kraken.Promising.Outcome I}
    (hstep : cs.step A t tid mem = some outs) (ho : .ok o ∈ outs) (hc : CohCoversL t.views t.prom mem L) :
    CohCoversL o.thread.views o.thread.prom o.mem L := by
  obtain ⟨tree, st, c', -, hr, hth, hm⟩ := stepOneWith_runOut A hstep ho
  have hc' := runTree_cohL A tid _ L tree _ st c' hr hc
  obtain ⟨e1, e2⟩ := finishInstr_relKey hth
  have e3 : o.thread.views.coh = c'.views.coh := by have := congrArg Views.coh e2; exact this
  intro k w hk hl hp
  rw [e1] at hp
  rw [hm] at hk
  have := hc' k w hk hl hp
  unfold Views.getCoh at this ⊢
  rw [e3]; exact this

/-! ## Thread 0's own facts of `Parts` -/

variable {Q : WakeRel} {D : WSide Q.ι} {M : MSide Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **main's owned words do not depend on its state** (`ownConst0`, main's
source stack empty by `PT0`). -/
theorem _root_.Spike.Lib.X64WakeW1.Parts.own0_const (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    Q.own w 0 st s0.stack = Q.own w 0 t0.st s0.stack := by
  have hpt0 := h.pt0
  rw [hPT0] at hpt0
  rw [hpt0.2.1]; exact hC0.ownConst0 w _ _

/-- **main's owned words read as their values** at any new state of main, at
the same memory and promises. -/
theorem _root_.Spike.Lib.X64WakeW1.Parts.ownOk0 (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    ExtRows.OwnOk (Q.own w 0 st s0.stack) t.1.mem t0.prom := by
  rw [h.own0_const hC0 hPT0 st]; exact h.core.own0

/-- **main's owned words read as their values**, at main's empty source
stack (`PT0`). -/
theorem _root_.Spike.Lib.X64WakeW1.Parts.own0 (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    ExtRows.OwnOk (Q.own w 0 t0.st []) t.1.mem t0.prom := by
  have hpt0 := h.pt0
  rw [hPT0] at hpt0
  have := h.core.own0
  simp only [ite_true] at this
  rw [hpt0.2.1] at this
  exact this

/-- **main's owned words are not the worker's**, at any new state of main. -/
theorem _root_.Spike.Lib.X64WakeW1.Parts.ownDisj0 (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    ∀ L v v', (L, v) ∈ Q.own w 0 st s0.stack → (L, v') ∈ Q.own w 1 t1.st s1.stack → False := by
  rw [h.own0_const hC0 hPT0 st]; exact h.core.own_disj

/-- **main's owned words are in its cover set** (`ownCov0`). -/
theorem _root_.Spike.Lib.X64WakeW1.Parts.ownCov0 (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) :
    ∀ L v, (L, v) ∈ Q.own w 0 st s0.stack → (Q.P w).cov 0 L := by
  have hpt0 := h.pt0
  rw [hPT0] at hpt0
  rw [hpt0.2.1]; exact hC0.ownCov0 w st

/-- **A runtime write of main is to none of its owned words** (`ownMp0`). -/
theorem _root_.Spike.Lib.X64WakeW1.Parts.ownMp0 (hC0 : WCompat0 Q M μ Λ) (hPT0 : Q.PT0 = PT0 M)
    (h : Parts Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (st : isa.State) {l : Loc} (hmp : (M.ms w).mp l true) :
    ∀ L v, (L, v) ∈ Q.own w 0 st s0.stack → l ≠ L := by
  have hpt0 := h.pt0
  rw [hPT0] at hpt0
  rw [hpt0.2.1]
  rintro L v hm rfl
  exact hC0.ownMp0 w st _ v hm hmp

end Spike.Lib.X64WakeM0

/-- info: 'Spike.Lib.X64WakeM0.ownOk_erase_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeM0.ownOk_erase_out

/-- info: 'Spike.Lib.X64WakeM0.ownOk_promise'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeM0.ownOk_promise'

/-- info: 'Spike.Lib.X64WakeM0.stepOneWith_cohL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeM0.stepOneWith_cohL

/-- info: 'Spike.Lib.X64WakeW1.Parts.ownMp0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeW1.Parts.ownMp0

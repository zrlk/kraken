/-
**hello.w: the buffer's and the box's labels at main's `spawn`** (x86-64; the twin of
`Spike/Lib/HelloNewBuf.lean`, its live part). Along source runs (`VBufR`), with main the only thread at
`spawnTermH`, the slice's buffer label is main's first allocation after its `ThreadId` box (`lBH`) and the box
`c`'s label its second (`lbX`); so the two differ (`lBH_ne_box`).

- `rodata_newBuf_label`: the two labels at the `spawn`.
- `lBH_ne_box`: `lBH ≠ lbX`.
- `clonePreH_labels`: the same at the clone (`ClonePreH`'s source side, `ClonePreH.src`).

**Where this differs from AArch64**: `ClonePreH` is `X64HelloPreA`'s, which has no label prefix `pfx`, and its
slice and box words are in `%r12, %rbx, %r13, %r14` and `%r15` (A64: `x9 .. x13`). A64's non-vacuity part
(`stepN`, `runN_run`, `stepN_some`, `sSp`, `sSp_shape`, `sSp_reach`, `hna_ge`, `reach_spawn`) is not used by the
hello proof and has no twin.
-/
import Spike.Lib.X64HelloVBuf
import Spike.Lib.X64HelloOkW

namespace Spike.Lib.X64HelloNewBuf

open CoreLang CoreTerm TermRun
open Scc.Sem Scc.Sem.SrcSem
open Spike.Lib.X64HelloMainPreSrc
open Spike.Lib.X64HelloPreTerm
open Spike.Lib.X64HelloSplit (slTy)
open Spike.Lib.X64HelloVBuf (VBufR)
open Spike.Lib.X64HelloOkW (lBH)

/-! ## The labels at the `spawn` -/

/-- **Rodata's buffer label at main's `spawn`**: along source runs
(`VBufR`), with main the only thread at `spawnTermH` (`SpawnSrcH l ws`),
the slice's buffer label `lb` is main's first allocation after its
`ThreadId` box (`lBH`) and `c`'s label `l` its second (`lbX`). -/
theorem rodata_newBuf_label {s : Cfg} {th0 : TTh} {l : WeakMem.AllocLabel} {ws : List Word}
    {lb : WeakMem.AllocLabel} {hd : Option (Nat × Word)} (hv : VBufR s) (hs : s.ths = #[th0])
    (hS : SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩) (hh : ws.head? = some (cst (.loc ⟨lb, 0⟩ 0))) :
    lb = lBH ∧ l = lbX := by
  obtain ⟨th, k, wo0, wo1, h0, -, -, hat, -⟩ := hv (by rw [hs]; rfl)
  rw [hs] at h0
  obtain rfl : th0 = th := by simpa using h0
  obtain rfl := X64HelloVBuf.hat_spawnTerm hat hS.1
  have hsl := hS.2.2.2.2.1
  have hcc := hS.2.2.1
  change evalAt th0.env (.var "sl") = some (slTy, ws) at hsl
  change evalAt th0.env (.var "c") = some (.ptr .pub .int, [cst (.loc ⟨l, 0⟩ 0)]) at hcc
  rw [hat.2.2.1] at hsl hcc
  simp [hc, envP0, envC, envO, c0H, envS, evalAt, lookupE] at hsl
  simp [hc, envP0, envC, envO, evalAt, lookupE, cst, Promises.TVal.mk0] at hcc
  subst hsl
  simp [cst, Promises.TVal.mk0] at hh
  exact ⟨hh.symm, hcc.symm⟩

/-- The buffer's label is not the box's (`BufPl`'s `lB ≠ cS.label` at the
`spawn`'s `c`). -/
theorem lBH_ne_box : lBH ≠ lbX := by decide

/-- **At the clone** (`ClonePreH`'s source side, `ClonePreH.src`): under
`VBufR`, the slice's buffer label `lb` (`SlRep`'s, placed at `%r12`) is `lBH`
and `c`'s label `l` (placed at `%r15`) is `lbX`; so `lb ≠ l`. -/
theorem clonePreH_labels {Λ : Scc.Sem.Layout} {r0 r1 : Range}
    {X : Kraken.Promising.X64.State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : Cfg} (hv : VBufR s) (h : X64HelloPreA.ClonePreH Λ r0 r1 X lbl t s) :
    ∃ (th0 : TTh) (hd : Option (Nat × Word)) (l lb : WeakMem.AllocLabel) (ws : List Word),
      s.ths = #[th0] ∧ SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧ ws.head? = some (cst (.loc ⟨lb, 0⟩ 0)) ∧
      lb = lBH ∧ l = lbX ∧ lb ≠ l := by
  obtain ⟨_, th0, hd, l, ws, _, hs, hS, _, hR, _, _⟩ := h.src
  obtain ⟨lb, rfl, -⟩ := hR
  obtain ⟨h1, h2⟩ := rodata_newBuf_label hv hs hS rfl
  exact ⟨th0, hd, l, lb, _, hs, hS, rfl, h1, h2, by rw [h1, h2]; exact lBH_ne_box⟩

end Spike.Lib.X64HelloNewBuf

/-- info: 'Spike.Lib.X64HelloNewBuf.rodata_newBuf_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloNewBuf.rodata_newBuf_label

/-- info: 'Spike.Lib.X64HelloNewBuf.lBH_ne_box' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64HelloNewBuf.lBH_ne_box

/-- info: 'Spike.Lib.X64HelloNewBuf.clonePreH_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloNewBuf.clonePreH_labels

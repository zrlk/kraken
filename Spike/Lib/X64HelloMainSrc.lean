/-
**hello.w on x86-64: main's source path after its `spawn`** (the twin of `Spike/Lib/HelloMainSrc.lean`; at
`helloSrc`, of `X64WakeMainSrc`, `X64WakeMainSrcW` and `X64WakeMainSrcR.src_pieces`): past `spawnTermH`'s
`spawn`, main is at `tail waitLoop [] c []` (`X64WakeM0.mTail`) with `c` bound to the flag's locative; hello's
`waitLoop` is wake's, so the tail call enters `X64WakeMainSrc.waitBody` (the flag's atomic load).

- `main_src_runH`: the tail call, to `X64WakeMainSrc.waitC w`.
- `main_src_wakeH`: every source premise of `main_closed_wakeW`, at
  `helloSrc` (the statement of `X64WakeMainSrcW.main_src_wake`).
- `src_piecesH`: `MainPieces`' source fields at the spawned configuration
  `spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws`, stated on plain
  `lbl`/`lsize`/`cS`; the `PreR` form is left to the instance.

## Differences from the AArch64 version

- Over `X64HelloSrc.helloSrc`, `X64HelloSplit.pktTy`, `X64WakeM0`, `X64WakeMainSrc`, `X64WakeMainSrcW`,
  `X64SpawnViewLtSteps`.
- `waitLoop_find` is a private lemma here (only `main_src_runH` uses it); A64's `spawnTermH_eq`,
  `main_src_loadH` and `main_src_load_spawnH` are dead and not twinned.
-/
import Spike.Lib.X64HelloMainPreSrc
import Spike.Lib.X64WakeMainSrcW
import Spike.Lib.X64SpawnViewLtSteps

namespace Spike.Lib.X64HelloMainSrc

open CoreLang CoreTerm
open Scc.Sem (ValRep LocRep)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloSplit (pktTy)
open Spike.Lib.X64WakeM0 (mTail wlBody wlIf wlPark)
open Spike.Lib.WakeMLive (wlRet)

/-- hello's `waitLoop` has wake's body. -/
private theorem waitLoop_find :
    helloSrc.find? (·.name == "waitLoop") = some
      { name := "waitLoop", tparams := [], idx := [], arg := "c", argTy := .ptr .pub .int, retTy := .int,
        body := X64WakeMainSrc.waitBody } := rfl

/-- **The tail call into `waitLoop`**, concretely: to `waitC w`. -/
theorem main_src_runH {cP : Spike.Lib.Ctl} {ty : Ty} {w : TermRun.Word}
    (ht : cP.term = .tail "waitLoop" [] (.var "c") [])
    (hc : TermRun.evalAt cP.env (.var "c") = some (ty, [w])) :
    Spike.Lib.LocalRun helloSrc cP (X64WakeMainSrc.waitC w) := by
  refine .single ⟨rfl, ?_⟩
  intro g mem pairs th hg ht' he hσ _
  simp [TermRun.tstep, ht', ht, TermRun.enter, hg, he, hc, hσ, TermRun.ol, waitLoop_find, X64WakeMainSrc.waitC]
  rfl

/-- **main's source premises of `main_closed_wakeW`, at `helloSrc`** (the
statement of `WakeMainSrcW.main_src_wake`). -/
theorem main_src_wakeH {lbl : WeakMem.AllocLabel → Option Nat} {A : BitVec 64} {cP : Spike.Lib.Ctl}
    {ty : Ty} {w : TermRun.Word} (ht : cP.term = mTail)
    (hc : TermRun.lookupE cP.env "c" = some (ty, [w])) (hval : ValRep lbl w.val A.toNat)
    (htag : ∃ sa, w.val = .loc sa 0) :
    ∃ c0 : Spike.Lib.Ctl,
      Spike.Lib.LocalRun helloSrc cP c0 ∧ c0.term = .let_ "d" (.load true (.var "c")) wlIf ∧
      TermRun.evalAt c0.env (.var "c") = some (.ptr .pub .int, [w]) ∧ ValRep lbl w.val A.toNat ∧
      (∃ sa, w.val = .loc sa 0) ∧
      c0.term = wlBody ∧ (cP.term ≠ wlBody ∧ cP.term ≠ wlIf) ∧
      cP.term ≠ wlRet ∧ (∀ y ∈ Scc.Sem.exprFv cP.term, y = "c") ∧
      TermRun.lookupE c0.env "c" = some (.ptr .pub .int, [w]) ∧
      c0.term ≠ wlRet ∧ (∀ y ∈ Scc.Sem.exprFv c0.term, y = "c") ∧
      wlIf ≠ wlRet ∧ (∀ y ∈ Scc.Sem.exprFv wlIf, y = "d" ∨ y = "c") ∧ ("d" : String) ≠ "c" := by
  have hrun := main_src_runH (cP := cP) (ty := ty) (w := w) ht hc
  have hl : TermRun.lookupE (X64WakeMainSrc.waitC w).env "c" = some (.ptr .pub .int, [w]) := by
    simp [X64WakeMainSrc.waitC, TermRun.lookupE]
  have hne := X64WakeMainSrcW.mTail_ne
  refine ⟨_, hrun, rfl, hl, hval, htag, rfl, ⟨ht ▸ hne.1, ht ▸ hne.2.1⟩, ht ▸ hne.2.2, ?_, hl,
    ?_, ?_, ?_, ?_, by decide⟩
  · rw [ht]; simp [mTail, Scc.Sem.exprFv, Scc.Sem.atVars]
  · simp [X64WakeMainSrc.waitC, X64WakeMainSrc.waitBody, wlRet]
  · simp [X64WakeMainSrc.waitC, X64WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]
  · simp [wlIf, wlRet]
  · simp [wlIf, wlPark, wlRet, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]

/-- **The source fields at hello's spawn** (the twin of
`WakeMainSrcR.src_pieces`; `hs'`, `hc`, `hA`, `hlsz`, `hcS` named premises). -/
theorem src_piecesH {s s' : TermRun.Cfg} {th0 s0 s1 : TermRun.TTh} {ws : List TermRun.Word}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {cS : WeakMem.Address}
    {l : WeakMem.AllocLabel} {cA : BitVec 64}
    (hs' : s' = TermSpawnStep.spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws)
    (hths : s.ths = #[th0]) (hths' : s'.ths = #[s0, s1])
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hA : lbl l = some cA.toNat) (hlsz : 0 < lsize l) (hcS : cS = ⟨l, 0⟩) :
    (Spike.Lib.Ctl.of s0).term = mTail ∧
      TermRun.lookupE (Spike.Lib.Ctl.of s0).env "c" = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc cS 0 ∧
      ValRep lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat ∧
      LocRep lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val cA.toNat 0 ∧
      ∃ sa, (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc sa 0 ∧ sa.offset < lsize sa.label := by
  have hs0 : s0 = TermSpawnStep.spawnPar s 0 th0 "t" mTail := by
    subst hs'
    have h := congrArg (·[0]?) hths'
    simp [TermSpawnStep.spawnCfg, TermSpawnStep.spawnT, hths] at h
    exact h.symm
  subst hs0
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := X64SpawnViewLtSteps.src_fields (i := 0) (lsize := lsize) hc hA hlsz
  exact ⟨h1, h2, by rw [hcS]; exact h3, h4, h5, h6⟩

end Spike.Lib.X64HelloMainSrc

/-- info: 'Spike.Lib.X64HelloMainSrc.main_src_wakeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainSrc.main_src_wakeH

/-- info: 'Spike.Lib.X64HelloMainSrc.src_piecesH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainSrc.src_piecesH

/-
**hello.w: main's source path after its `spawn`** (the twin, at
`helloSrc`, of `WakeMainSrc`, `WakeMainSrcW` and `WakeMainSrcR.src_pieces`):
past `spawnTermH`'s `spawn`, main is at `tail waitLoop [] c []`
(`WakeM0.mTail`) with `c` bound to the flag's locative; hello's `waitLoop`
is wake's, so the tail call enters `WakeMainSrc.waitBody` (the flag's
atomic load).

- `waitLoop_find`: hello's `waitLoop` has wake's body.
- `main_src_runH`: the tail call, to `WakeMainSrc.waitC w`.
- `main_src_loadH`, `main_src_load_spawnH`: the load's control from a
  control at `mTail`, and at the spawn's parent
  (`TermSpawnStep.spawnPar`, `x := t`).
- `main_src_wakeH`: every source premise of `main_closed_wakeW`, at
  `helloSrc` (the statement of `WakeMainSrcW.main_src_wake`).
- `src_piecesH`: `MainPieces`' source fields at the spawned configuration
  `spawnCfg s 0 th0 "t" mTail "worker" [] pktTy ws`, stated on plain
  `lbl`/`lsize`/`cS`; the `PreR` form is left to the instance.
-/
import Spike.Lib.HelloMainPreSrc
import Spike.Lib.WakeMainSrcW
import Spike.Lib.SpawnViewLtSteps

namespace Spike.Lib.HelloMainSrc

open CoreLang CoreTerm
open Scc.Sem (ValRep LocRep)
open Spike.Lib.HelloSrc (helloSrc)
open Spike.Lib.HelloMainPreSrc (pktTy spawnTermH)
open Spike.Lib.WakeM0 (mTail wlBody wlIf wlPark)
open Spike.Lib.WakeMLive (wlRet)

/-- `spawnTermH`'s continuation is `mTail`. -/
theorem spawnTermH_eq : spawnTermH = .let_ "t" (.spawn "worker" (.var "p") pktTy []) mTail := rfl

/-- hello's `waitLoop` has wake's body. -/
theorem waitLoop_find :
    helloSrc.find? (·.name == "waitLoop") = some
      { name := "waitLoop", tparams := [], idx := [], arg := "c", argTy := .ptr .pub .int, retTy := .int,
        body := WakeMainSrc.waitBody } := rfl

/-- **The tail call into `waitLoop`**, concretely: to `waitC w`. -/
theorem main_src_runH {cP : Spike.Lib.Ctl} {ty : Ty} {w : TermRun.Word}
    (ht : cP.term = .tail "waitLoop" [] (.var "c") [])
    (hc : TermRun.evalAt cP.env (.var "c") = some (ty, [w])) :
    Spike.Lib.LocalRun helloSrc cP (WakeMainSrc.waitC w) := by
  refine .single ⟨rfl, ?_⟩
  intro g mem pairs th hg ht' he hσ _
  simp [TermRun.tstep, ht', ht, TermRun.enter, hg, he, hc, hσ, TermRun.ol, waitLoop_find, WakeMainSrc.waitC]
  rfl

/-- **main's source from its tail call to the flag load** (the twin of
`WakeMainSrc.main_src_load`). -/
theorem main_src_loadH {lbl : WeakMem.AllocLabel → Option Nat} {A : BitVec 64} {cP : Spike.Lib.Ctl}
    {ty : Ty} {w : TermRun.Word} (ht : cP.term = .tail "waitLoop" [] (.var "c") [])
    (hc : TermRun.evalAt cP.env (.var "c") = some (ty, [w])) (hval : ValRep lbl w.val A.toNat)
    (htag : ∃ sa, w.val = .loc sa 0) :
    ∃ (c0 : Spike.Lib.Ctl) (x : String) (a : CoreTerm.At) (e : Expr) (ty' : Ty) (w' : TermRun.Word),
      Spike.Lib.LocalRun helloSrc cP c0 ∧ c0.term = .let_ x (.load true a) e ∧
      TermRun.evalAt c0.env a = some (ty', [w']) ∧ ValRep lbl w'.val A.toNat ∧ ∃ sa, w'.val = .loc sa 0 :=
  ⟨_, "d", .var "c", _, .ptr .pub .int, w, main_src_runH ht hc, WakeMainSrc.waitC_term w, WakeMainSrc.waitC_ev w,
    hval, htag⟩

/-- **At the spawn's parent** (the twin of `WakeMainSrc.main_src_load_spawn`):
main past `spawnTermH`'s `spawn`, with `c` bound before the spawn to the
locative of a label `l` placed at `A`. -/
theorem main_src_load_spawnH {lbl : WeakMem.AllocLabel → Option Nat} {A : BitVec 64} {c : TermRun.Cfg}
    {i : Nat} {th0 : TermRun.TTh} {l : WeakMem.AllocLabel}
    (hc : TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]))
    (hval : ValRep lbl (.loc ⟨l, 0⟩ 0) A.toNat) :
    ∃ (c0 : Spike.Lib.Ctl) (x : String) (a : CoreTerm.At) (e : Expr) (ty : Ty) (w : TermRun.Word),
      Spike.Lib.LocalRun helloSrc (Spike.Lib.Ctl.of (TermSpawnStep.spawnPar c i th0 "t" mTail)) c0 ∧
      c0.term = .let_ x (.load true a) e ∧ TermRun.evalAt c0.env a = some (ty, [w]) ∧
      ValRep lbl w.val A.toNat ∧ ∃ sa, w.val = .loc sa 0 := by
  refine main_src_loadH (ty := .ptr .pub .int) (w := TermRun.cst (.loc ⟨l, 0⟩ 0)) rfl ?_ hval ⟨⟨l, 0⟩, rfl⟩
  have : TermRun.evalAt (Spike.Lib.Ctl.of (TermSpawnStep.spawnPar c i th0 "t" mTail)).env (.var "c") =
      TermRun.evalAt th0.env (.var "c") := by
    simp [Spike.Lib.Ctl.of, TermSpawnStep.spawnPar, TermRun.evalAt, TermRun.lookupE]
  rw [this, hc]

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
  have hl : TermRun.lookupE (WakeMainSrc.waitC w).env "c" = some (.ptr .pub .int, [w]) := by
    simp [WakeMainSrc.waitC, TermRun.lookupE]
  have hne := WakeMainSrcW.mTail_ne
  refine ⟨_, hrun, rfl, hl, hval, htag, rfl, ⟨ht ▸ hne.1, ht ▸ hne.2.1⟩, ht ▸ hne.2.2, ?_, hl,
    ?_, ?_, ?_, ?_, by decide⟩
  · rw [ht]; simp [mTail, Scc.Sem.exprFv, Scc.Sem.atVars]
  · simp [WakeMainSrc.waitC, WakeMainSrc.waitBody, wlRet]
  · simp [WakeMainSrc.waitC, WakeMainSrc.waitBody, Scc.Sem.exprFv, Scc.Sem.atVars, Scc.Sem.opVars, Scc.Sem.opAts]
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
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := SpawnViewLtSteps.src_fields (i := 0) (lsize := lsize) hc hA hlsz
  exact ⟨h1, h2, by rw [hcS]; exact h3, h4, h5, h6⟩

/-- info: 'Spike.Lib.HelloMainSrc.main_src_load_spawnH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_src_load_spawnH

/-- info: 'Spike.Lib.HelloMainSrc.main_src_wakeH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms main_src_wakeH

/-- info: 'Spike.Lib.HelloMainSrc.src_piecesH' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms src_piecesH

end Spike.Lib.HelloMainSrc

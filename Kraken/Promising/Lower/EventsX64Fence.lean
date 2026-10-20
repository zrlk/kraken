/-
**`fence .ld` on `Arch.tso` is a stutter.**

WeakCore's `fence ld` lowers to **nothing** on x64. Two facts matter for that
row.

1. **The x64 `exec` does produce `.fence .ld`**: `lfence`
   (`X64/Semantics.lean`, `.lfence => .fence .ld`). So Kraken's x64 model has
   a load fence, and the question "is it a no-op on TSO" is a question about
   Kraken's own machine, answered here.
2. **The lowering emits no instruction**, so for the lowering itself Kraken
   never sees the fence: the WeakCore side must take its `fence ld` step as a
   source stutter matched by zero target steps. That is a WeakCore-side
   obligation (the WK-tso `fence ld` step must leave the simulation relation
   intact); nothing on the Kraken side is needed for it. What this file adds
   is the Kraken-side evidence that the erasure is exact: on `Arch.tso` the
   load fence is *literally* the identity on a thread's views in every
   reachable configuration, so emitting `lfence` and emitting nothing have
   the same outcomes, step for step.

## Results (ISA-neutral, `Arch.tso`)

- `fenceStep_ld_of_ldFold`: under `LdFold` (`vrOld ≤ vrNew ∧ vrOld ≤ vwNew`)
  `fenceStep c .ld` only appends the fence to the log (any `Arch`).
- `LdFold` is an invariant of the fuel-free machine on `Arch.tso`: every TSO
  load is an acquire (`plainLoad = .acqPc`), so a read raises `vrOld` and,
  with it, `vrNew` and `vwNew` (a `noRet` read leaves `vrOld` alone); stores
  touch none of the three; fences and `rmwPost` only raise `vrNew`/`vwNew`.
  `runTree_ldFold`, `cfgLdFold_init`, `reachableSemInf_ldFold`.
- `instrSemInf_fence_ld_stutter`: from a thread with `LdFold`, a
  `.fence .ld` step is exactly the no-event step (the right-hand side of
  `instrSemInf_done_iff`), with no side condition left (contrast
  `Tso.instrSemInf_fence_st_stutter`, which needs `vwOld ⊔ vwOldNT ≤ vwNew`).
- `X64.instrSemInf_lfence_stutter`: the same at an `lfence` cell of
  `X64.isa`.

On `Arch.armv8` `LdFold` fails after a relaxed load (`vrOld` rises,
`vrNew` does not), and `dmb ishld` is not a stutter there, as expected.
-/
import Kraken.Promising.Lower.TsoCollapse
import Kraken.Promising.Lower.EventsX64Inf

namespace Kraken.Promising.Lower.Tso

open Kraken.Promising

/-- **The load-fence fold**: `vrOld` is already below `vrNew` and `vwNew`,
so `fence .ld` has nothing to add. -/
def LdFold (vs : Views) : Prop := vs.vrOld ≤ vs.vrNew ∧ vs.vrOld ≤ vs.vwNew

/-- Under `LdFold`, `fence .ld` only logs itself (any `Arch`). -/
theorem fenceStep_ld_of_ldFold {c : Ctx} (h : LdFold c.views) :
    fenceStep c .ld = { c with log := c.log ++ [.fence .ld] } := by
  have e1 : max c.views.vrNew c.views.vrOld = c.views.vrNew := by simp only [LdFold, View] at *; omega
  have e2 : max c.views.vwNew c.views.vrOld = c.views.vwNew := by simp only [LdFold, View] at *; omega
  simp only [fenceStep, e1, e2]

section Inv

variable (tid : Nat) (iv : InstrViews)

/-- A TSO read keeps `LdFold`: every TSO load kind is an acquire. -/
theorem readSuccs_ldFold {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {x : Time × Val × Ctx}
    (hx : x ∈ readSuccs Arch.tso iv c k xcl l noRet) (hc : LdFold c.views) : LdFold x.2.2.views := by
  have hacq : (Arch.tso.loadKind k).isAcquire = true := by cases k <;> rfl
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · rw [Option.ite_none_left_eq_some] at ht
    obtain ⟨-, ht⟩ := ht
    obtain rfl := Option.some.inj ht
    simp only [hacq, ite_true, Views.setCoh]
    unfold LdFold at *
    cases noRet <;> simp only [Bool.false_eq_true, ite_true, ite_false, View] at * <;> omega

/-- A write keeps `LdFold` (any `Arch`, any kind): it touches none of the
three views. -/
theorem writeSuccs_ldFold {xr : View} {A : Arch} {c c' : Ctx} {iv' : InstrViews} {k : StoreKind} {xcl : Bool} {l : Loc}
    {v : Val} {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv' c k xcl l v tr extra xr)
    (hc : LdFold c.views) : LdFold c'.views := by
  rcases (mem_writeSuccs_iff A tid iv').mp h with ⟨t, -, -, -, rfl⟩ | ⟨-, rfl⟩ <;>
    exact hc

/-- **A run of any tree on `Arch.tso` keeps `LdFold`.** -/
theorem runTree_ldFold {σ : Type} (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx)
    (h : .ok (s, c') ∈ runTree Arch.tso tid iv c tree) (hc : LdFold c.views) : LdFold c'.views := by
  refine runTree_preserves Arch.tso tid iv (fun c c' => LdFold c.views → LdFold c'.views) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ ?_ ?_ ?_ tree c s c' h hc
  · intro c k xcl l noRet x hx h
    exact readSuccs_ldFold iv hx h
  · intro c iv' k xcl l v tr extra xr c' hc' h
    exact writeSuccs_ldFold tid hc' h
  · intro c k h
    unfold LdFold at *
    cases k <;> simp only [fenceStep, View] at * <;> omega
  · intro c l h; exact h
  · intro c k noRet l h
    unfold rmwPost; split
    · unfold LdFold at *; simp only [View] at *; omega
    · exact h

end Inv

section Machine

open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

variable {I : ISA}

/-- Every thread of the configuration satisfies `LdFold`. -/
def CfgLdFold (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → LdFold t.views

theorem cfgLdFold_init (states : List I.State) (initMem : List (Loc × Val)) :
    CfgLdFold (Config.init states initMem : Config I) := by
  intro i t h
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  exact ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem CfgLdFold.withThread {c : Config I} (hc : CfgLdFold c) {tid : Nat} {t th : Thread I}
    (ht : c.threads[tid]? = some t) {mem : Memory} (hth : LdFold th.views) :
    CfgLdFold (c.withThread tid th mem) := by
  intro i t' h
  rw [Config.withThread_get? c th mem (lt_size_of_get? ht)] at h
  split at h
  · obtain rfl := Option.some.inj h; exact hth
  · exact hc i t' h

/-- An instruction step on `Arch.tso` keeps `CfgLdFold`. -/
theorem instrSemInf_ldFold {tid : Nat} {c c' : Config I} (hc : CfgLdFold c)
    (h : InstrSemInf Arch.tso tid c c') : CfgLdFold c' := by
  obtain ⟨t, outs, o, ht, hs, ho, -, rfl⟩ := h
  refine hc.withThread ht ?_
  cases hex : I.exec t.st with
  | none => simp [stepOne, hex] at hs
  | some tree =>
    obtain ⟨st, c1, hr, hth, -⟩ := (stepOne_ok_iff Arch.tso tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩
    have h1 := runTree_ldFold tid _ tree _ st c1 hr (hc tid t ht)
    rcases CertCut.finishInstr_views hth with e | e <;> rw [e] <;> exact h1

/-- A promise step keeps `CfgLdFold` (views unchanged). -/
theorem promSemInf_ldFold {A : Arch} {tid : Nat} {c c' : Config I} (hc : CfgLdFold c)
    (h : PromSemInf A tid c c') : CfgLdFold c' := by
  obtain ⟨t, w, ht, -, -, rfl⟩ := h
  exact hc.withThread ht (hc tid t ht)

/-- **`LdFold` is an invariant of the fuel-free machine on `Arch.tso`.** -/
theorem reachableSemInf_ldFold {c c' : Config I} (h : ReachableSemInf Arch.tso c c') (hc : CfgLdFold c) :
    CfgLdFold c' := by
  induction h with
  | refl => exact hc
  | step tid hs _ ih =>
    rcases hs with hs | hs
    · exact ih (instrSemInf_ldFold hc hs)
    · exact ih (promSemInf_ldFold hc hs)

variable (A : Arch) (tid : Nat) {c c' : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
include ht

/-- **`fence .ld` is a stutter** from a thread with `LdFold` (on
`Arch.tso`, every reachable thread: `reachableSemInf_ldFold`): the step is
exactly the no-event step (`instrSemInf_done_iff`'s right-hand side). -/
theorem instrSemInf_fence_ld_stutter {s : I.State} (hex : I.exec t.st = some (.fence .ld fun _ => .done s))
    (hf : LdFold t.views) :
    InstrSemInf A tid c c' ↔ ∃ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
        (ctx0 tid t c.mem) ∧ CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  rw [instrSemInf_fence_iff A tid ht hex, fenceStep_ld_of_ldFold (c := ctx0 tid t c.mem) hf]
  rfl

end Machine

end Kraken.Promising.Lower.Tso

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- Read the cell through `exec_of_cellAt` and unfold it (`EventsX64.lean`'s
local `cell`, repeated: local macros do not cross files). -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  try simp only [rspOf, Reg64s.get64] at *
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, Width.bytesv, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-- **`lfence`**: one `.ld` fence. -/
theorem exec_lfence {st : State} {sz : Nat} (hc : CellAt st (op64 .lfence) sz) :
    isa.exec st = some (.fence .ld fun _ => .done (after st sz st.st.1)) := by
  cell hc []

variable (A : Arch) (tid : Nat) {c c' : Config isa} {t : Thread isa}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`lfence` is a source stutter** from a thread with `LdFold` (on
`Arch.tso`: every thread of every reachable configuration,
`Tso.reachableSemInf_ldFold`). -/
theorem instrSemInf_lfence_stutter (hc : CellAt (stOf t) (op64 .lfence) sz) (hf : Tso.LdFold t.views)
    (h : InstrSemInf A tid c c') : Stutter A tid c c' t (after (stOf t) sz (stOf t).st.1) := by
  obtain ⟨th, hth, hcert, rfl⟩ := (Tso.instrSemInf_fence_ld_stutter A tid ht (exec_lfence hc) hf).mp h
  exact ⟨th, rfl, finishInstr_st hth, (finishInstr_relKey hth).1, CertCut.finishInstr_views hth, hcert⟩

end Kraken.Promising.Lower.X64

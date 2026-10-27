/-
**A function's `ret` placed by its exit's placements** (AArch64): at the
return exit `RetJS` (`Spike/Lib/LowerA64/RetS.lean`) at an abstract state
`σ`, the control at `ret a` is placed (`Placed`) in every target state whose
registers are `σ`'s: the returned words are at their placements `pls` of
operands valued by the argument registers, so each operand's place is its
register, and `a` is the only variable the term reads.

- `RetJS.placed`: `Placed` at the `ret` from `RetJS` at the state's registers.
-/
import Spike.Lib.LowerA64.PlacedSPostC
import Spike.Lib.A64AbortPlace

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (WordPlace WordPlaceRep Place placeVal)
open Scc.Sem.A64 (machine kernel)
open Spike.Lib.A64Consumer
open Spike.Lib.Form (WordPl WordRep WordsRep)
open Spike.Lib.LowerNode (group_opds)

open Classical in
/-- **A `ret` placed by its exit's placements**: at `RetJS` at `σ`, the
control is placed in every state `s` whose registers are `σ`'s (`hr`, e.g.
`Abs.regs`): the returned atom's words at their placements, each operand
in its argument register. -/
theorem RetJS.placed {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {σ : Spike.Lib.A64.Flow.AS} {c : Ctl}
    (h : RetJS lbl fp ra σ c) (Λ : Scc.Sem.Layout) {s : State} (hr : s.st.1.regs = σ.regs) :
    Placed Λ lbl s c := by
  obtain ⟨a, t, ws, ops, pls, val, ht, -, he, hg, hn, hv, hW, -⟩ := h
  -- the index of an operand among `ops`
  let pick : Scc.IR.Operand → Nat := fun o =>
    if hx : ∃ j, ∃ hj : j < ops.length, ops[j] = o then Classical.choose hx else 0
  have hpick : ∀ o ∈ ops, ∃ hj : pick o < ops.length, ops[pick o] = o := by
    intro o ho
    have hx : ∃ j, ∃ hj : j < ops.length, ops[j] = o := List.getElem_of_mem ho
    simp only [pick, dite_eq_left hx]
    exact Classical.choose_spec hx
  let opPl : Scc.IR.Operand → Place (machine (kernel 1)).I.RegId := fun o =>
    .reg (.x (Scc.Emit.A64.argRegs.getD (pick o) .X0).idx)
  have hopPl : ∀ o ∈ ops, ∀ v, val o = some v → placeVal (machine (kernel 1)) s (opPl o) = some v := by
    intro o ho v hvo
    obtain ⟨hj, hoj⟩ := hpick o ho
    have hr' : pick o < Scc.Emit.A64.argRegs.length := Nat.lt_of_lt_of_le hj hn
    have h1 := hv (pick o) hj hr'
    rw [hoj, hvo] at h1
    rw [Option.some.inj h1]
    show some (Scc.Sem.A64.regVal s (.x _)).toNat = _
    rw [regVal_idx, hr, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr']; rfl
  let wpR : WordPl → WordPlace (machine (kernel 1)).I.RegId
    | .one o => .one (opPl o)
    | .loc b off => .loc (opPl b) (.at (opPl off))
  let envm : String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId) := fun x k =>
    if a = .var x then pls[k]?.map wpR else none
  have hlen := hW.length
  refine ⟨envm, fun x ty' ws' hl k wd wp hwd hem => ?_, fun x hx ty' ws' hl k hk => ?_, fun x k n hem => ?_⟩
  · simp only [envm] at hem
    split at hem
    · rename_i hax
      subst hax
      rw [show TermRun.lookupE c.env x = TermRun.evalAt c.env (.var x) from rfl, he] at hl
      cases hl
      obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.mp hem
      have hR := wordsRep_get hW hwd hpl
      have hmem : ∀ o ∈ pl.opds, o ∈ ops := fun o ho => by
        rw [← group_opds hg]
        exact List.mem_flatMap.mpr ⟨pl, List.mem_of_getElem? hpl, ho⟩
      cases pl with
      | one o =>
        obtain ⟨v, hvo, hvr⟩ := hR
        exact ⟨v, hopPl o (hmem o (by simp [WordPl.opds])) v hvo, hvr⟩
      | loc b off =>
        obtain ⟨vb, vo, hvb, hvo, hlr⟩ := hR
        exact ⟨vb, vo, hopPl b (hmem b (by simp [WordPl.opds])) vb hvb,
          hopPl off (hmem off (by simp [WordPl.opds])) vo hvo, Spike.Lib.A64ConsumerS.locRep_of_form hlr⟩
    · cases hem
  · rw [ht] at hx
    cases a with
    | var y =>
      simp only [Scc.Sem.exprFv, Scc.Sem.atVars, List.mem_singleton] at hx
      rw [hx] at hl ⊢
      rw [show TermRun.lookupE c.env y = TermRun.evalAt c.env (.var y) from rfl, he] at hl
      cases hl
      refine ⟨wpR pls[k], ?_⟩
      simp only [envm, ite_true, List.getElem?_eq_getElem (show k < pls.length by omega), Option.map_some]
    | lit _ => simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
    | unit => simp [Scc.Sem.exprFv, Scc.Sem.atVars] at hx
  · simp only [envm] at hem
    split at hem
    · obtain ⟨pl, -, hpl⟩ := Option.map_eq_some_iff.mp hem
      cases pl <;> cases hpl
    · cases hem

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.RetJS.placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.RetJS.placed

/-
**A return's pair placed with its caller's frame** (x86-64): at a `ret`
whose exit is by placements (`RetJS` at the machine registers `σ`), at a
state with `σ`'s registers, the pair of the `ret`'s control and one frame
`fr` is placed (`PlacedS`) once the control `fr` pops into is placed at no
frame for some returned words: the returned atom's words at the result
registers through their placements (depth 0), the frame's environment off
its variable where the popped control has it (depth 1, the popped control's
term the frame's body).

- `placedS_retFr`: the placement at the `ret` with one frame;
- `frOk2_retFr`: `FrOk2` at the `ret` with one frame free of `ZBad`.
-/
import Spike.Lib.LowerX64.PlacedSPostC
import Spike.Lib.LowerX64.RetS
import Spike.Lib.Src.RunOk2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (WordPlace WordPlaceRep Place placeVal exprFv atVars)
open Scc.Sem.X64 (machine kernel)
open Spike.Lib.X64 (AS)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerS (PlacedS envsOf fvOf termsOf)
open Spike.Lib.Form (WordPl WordRep WordsRep)
open Spike.Lib.LowerNode (group_opds FrOk2 ZBad)

variable {lbl : WeakMem.AllocLabel → Option Nat}

open Classical in
/-- **The `ret`'s pair with one frame placed**: at `RetJS` at `σ` and a
state `s` with `σ`'s registers, if the control `fr` pops into at some
returned words `ws` is placed at no frame, the `ret`'s control with the
frame `fr` is placed. -/
theorem placedS_retFr {Λ : Scc.Sem.Layout} {fp : BitVec 64} {σ : AS} {c : Ctl} {fr : TermRun.Frame}
    {ws : List TermRun.Word} {s : State} (hJ : RetJS lbl fp σ c) (hregs : s.st.1.regs = σ.regs)
    (hP : PlacedS Λ lbl s ⟨fr.body, (fr.x, fr.ty, ws) :: fr.env, none⟩ []) :
    PlacedS Λ lbl s c [fr] := by
  obtain ⟨a, t, wa, ops, pls, val, ht, -, hev, hg, hn, hv, hW, -⟩ := hJ
  obtain ⟨envP, hrepP, htotP, himmP⟩ := hP
  -- the index of an operand among `ops`
  let pick : Scc.IR.Operand → Nat := fun o =>
    if hx : ∃ j, ∃ hj : j < ops.length, ops[j] = o then Classical.choose hx else 0
  have hpick : ∀ o ∈ ops, ∃ hj : pick o < ops.length, ops[pick o] = o := by
    intro o ho
    have hx : ∃ j, ∃ hj : j < ops.length, ops[j] = o := List.getElem_of_mem ho
    simp only [pick, dite_eq_left hx]
    exact Classical.choose_spec hx
  let opPl : Scc.IR.Operand → Place (machine (kernel 1)).I.RegId := fun o =>
    if hr : pick o < Scc.Emit.X64.retRegs.length then .reg (.r Scc.Emit.X64.retRegs[pick o]) else .reg (.r .rax)
  have hopPl : ∀ o ∈ ops, ∀ v, val o = some v → placeVal (machine (kernel 1)) s (opPl o) = some v := by
    intro o ho v hvo
    obtain ⟨hj, hoj⟩ := hpick o ho
    have hr : pick o < Scc.Emit.X64.retRegs.length := Nat.lt_of_lt_of_le hj hn
    have h1 := hv (pick o) hj hr
    rw [hoj, hvo] at h1
    simp only [opPl, dite_eq_left hr]
    show some (s.st.1.regs.get64 _).toNat = _
    rw [hregs, Option.some.inj h1]
  let wpR : WordPl → WordPlace (machine (kernel 1)).I.RegId
    | .one o => .one (opPl o)
    | .loc b off => .loc (opPl b) (.at (opPl off))
  have hlen := hW.length
  -- the returned atom's words at their placements (depth 0), the frame off its variable (depth 1)
  let envm : Nat → String → Nat → Option (WordPlace (machine (kernel 1)).I.RegId) := fun d x k =>
    match d with
    | 0 => if a = .var x then pls[k]?.map wpR else none
    | 1 => if x = fr.x then none else envP 0 x k
    | _ => none
  refine ⟨envm, ?_, ?_, ?_⟩
  · intro d env hd x ty' ws' hl k wd wp hwd hem
    rcases d with _ | _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      simp only [envm] at hem
      split at hem
      · rename_i hax
        subst hax
        rw [show TermRun.evalAt c.env (.var x) = TermRun.lookupE c.env x from rfl, hl] at hev
        cases hev
        obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.mp hem
        have hR := Spike.Lib.X64Consumer.wordsRep_get hW hwd hpl
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
            hopPl off (hmem off (by simp [WordPl.opds])) vo hvo, Spike.Lib.X64ConsumerS.locRep_of_form hlr⟩
      · cases hem
    · simp only [envsOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hd
      subst hd
      simp only [envm] at hem
      split at hem
      · cases hem
      · rename_i hne
        refine hrepP 0 ((fr.x, fr.ty, ws) :: fr.env) rfl x ty' ws' ?_ k wd wp hwd hem
        rw [lookupE_cons_ne hne]
        exact hl
    · simp [envsOf] at hd
  · intro d env xs hd hxs x hx ty' ws' hl k hk
    rcases d with _ | _ | d
    · simp only [envsOf, List.getElem?_cons_zero, Option.some.injEq] at hd
      simp only [fvOf, List.getElem?_cons_zero, Option.some.injEq] at hxs
      subst hd hxs
      rw [ht] at hx
      cases a with
      | var y =>
        simp only [exprFv, atVars, List.mem_singleton] at hx
        subst hx
        rw [show TermRun.evalAt c.env (.var x) = TermRun.lookupE c.env x from rfl, hl] at hev
        cases hev
        refine ⟨wpR pls[k], ?_⟩
        simp only [envm, ite_true, List.getElem?_eq_getElem (show k < pls.length by omega), Option.map_some]
      | lit n => simp [exprFv, atVars] at hx
      | unit => simp [exprFv, atVars] at hx
    · simp only [envsOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hd
      simp only [fvOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hxs
      subst hd hxs
      have hne : x ≠ fr.x := by
        have := (List.mem_filter.mp hx).2
        simpa using this
      have hx' : x ∈ exprFv fr.body := (List.mem_filter.mp hx).1
      obtain ⟨pl, hpl⟩ := htotP 0 ((fr.x, fr.ty, ws) :: fr.env) (exprFv fr.body) rfl rfl x hx' ty' ws'
        (by rw [lookupE_cons_ne hne]; exact hl) k hk
      exact ⟨pl, by simp only [envm, hne, ite_false]; exact hpl⟩
    · simp [envsOf] at hd
  · intro d e x k n hd hem
    rcases d with _ | _ | d
    · simp only [envm] at hem
      split at hem
      · obtain ⟨pl, -, hpl⟩ := Option.map_eq_some_iff.mp hem
        cases pl <;> cases hpl
      · cases hem
    · simp only [termsOf, List.map_cons, List.map_nil, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at hd
      subst hd
      simp only [envm] at hem
      split at hem
      · cases hem
      · exact himmP 0 _ x k n (by simp [termsOf]) hem
    · cases hem

/-- **`FrOk2` at a `ret` with one frame**: the `ret` is free of `ZBad`;
the frame's body is by `hb`. -/
theorem frOk2_retFr {c : Ctl} {fr : TermRun.Frame} {a : At} (ht : c.term = .ret a) (hb : NoS ZBad fr.body) :
    FrOk2 c [fr] :=
  ⟨by rw [ht]; trivial, by simpa using hb⟩

end Spike.Lib.LowerX64

/--
info: 'Spike.Lib.LowerX64.placedS_retFr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.placedS_retFr

/--
info: 'Spike.Lib.LowerX64.frOk2_retFr' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.LowerX64.frOk2_retFr

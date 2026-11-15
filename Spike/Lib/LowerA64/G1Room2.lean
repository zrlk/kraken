/-
**A compiled block's stack rooms from the placement check** (AArch64): the
`Accepted2` twins of `ownRoom_of_placeOK`, `calleeRoom_of_placeOK`
(`Spike/Lib/LowerA64/CalleeRoom.lean`) and `calleeLim_of_placeOK`
(`Spike/Lib/LowerA64/LimRoom.lean`) at the placement check's code facts at
the theorem's immediates (`fnCode2OfPMe`), and the prologue's limit facts
inside the assembled theorem's memory side `MSAt` (the twin of
`limOk_callee_ofPlaceOK`, `Spike/Lib/LowerA64/LimOk0.lean`).

A compiled block's IR function is `func2` of its closed form
(`fnCode2OfPMe_spec2`), stack-checked, so the placement check's `fnOk1`
gives its row of the stack need table at its frame (`needOk1`). A plain
call of `g` at a point of the block's body is a `call` of `Names.user g` in
the closed form (`call_mem_lowerC2`), so one of the function's callees, and
`g` names an earlier compiled block (`callOrder2T`): the call site's rows
`fd + ng ≤ nd`.

- `lowerC2_let_sub`, `call_mem_lowerC2`, `mem_callees_func2`: a call at a
  `TailOf` the body is in the closed form's instructions, so a callee of
  `func2`;
- `row2_of_placeOK`: a compiled block's row at its frame, with the bound on
  its callees;
- `room2Own`, `room2Callee`, `lim2Callee`, `limOk2`: `Room2OwnStmt`,
  `Room2CalleeStmt`, `Lim2CalleeStmt`, `LimOk2Stmt`
  (`Spike/Lib/LowerA64/G1FnSpec.lean`).
-/
import Spike.Lib.LowerA64.G1FnSpec
import Spike.Lib.Src.CallOrder2

namespace Spike.Lib.LowerA64

set_option autoImplicit false

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Code1A64 (needOk1 callees ctxOf fnOk1_of_fnCode1Ok)
open Scc.Cert.NeedA64 (row?)
open Spike.Lib.LowerShape (allInsts lowerC2 Res2 func2)
open Spike.Lib.LowerNode (compiled2 TailAt2 TailOf IsNum imms2Me)
open Spike.Lib.A64.Flow.Ret0 (limA pinA)

/-! ## A call in the closed form -/

/-- **A `let`'s body's closed form inside the `let`'s**: every instruction
of the body's closed form (at some environment, counter and label counter)
is one of the `let`'s. -/
theorem lowerC2_let_sub {cx : Scc.Lower.Ctx} {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat}
    {y : String} {op : Op} {e : Expr} {r : Res2} (hr : lowerC2 cx env n l k (.let_ y op e) = some r) :
    ∃ env' n' k' r', lowerC2 cx env' n' l k' e = some r' ∧
      ∀ i ∈ allInsts r'.toRes1, i ∈ allInsts r.toRes1 := by
  cases op
  all_goals first
    | (obtain ⟨t, ws, sc, hq, r', -, -, he, rfl⟩ := Spike.Lib.LowerShape.lowerC2_pure_inv rfl hr
       exact ⟨_, _, _, r', he, fun i hi => by simpa [allInsts] using hi⟩)
    | (simp [lowerC2, Spike.Lib.LowerShape.pureOp] at hr; done)
    | skip
  · obtain ⟨_, _, _, _, r', -, -, he, rfl⟩ := Spike.Lib.LowerShape.lowerC2_add_inv hr
    exact ⟨_, _, _, r', he, fun i hi => by
      simp only [allInsts, List.mem_append, List.mem_cons] at hi ⊢; rcases hi with hi | hi <;> simp [hi]⟩
  · obtain ⟨_, _, _, _, r', -, -, he, rfl⟩ := Spike.Lib.LowerShape.lowerC2_sub_inv hr
    exact ⟨_, _, _, r', he, fun i hi => by
      simp only [allInsts, List.mem_append, List.mem_cons] at hi ⊢; rcases hi with hi | hi <;> simp [hi]⟩
  · obtain ⟨_, _, _, _, _, _, _, r', -, -, -, -, -, he, rfl⟩ := Spike.Lib.LowerShape.lowerC2_newBuf_inv hr
    exact ⟨_, _, _, r', he, fun i hi => by
      simp only [allInsts, List.mem_append, List.mem_cons] at hi ⊢; rcases hi with hi | hi <;> simp [hi]⟩
  · rcases Spike.Lib.LowerShape.lowerC2_call_inv hr with
      ⟨_, _, _, r', -, -, -, -, he, rfl⟩ | ⟨_, _, _, _, _, _, _, r', -, -, -, -, he, rfl⟩
    · exact ⟨_, _, _, r', he, fun i hi => by
      simp only [allInsts, List.mem_append, List.mem_cons] at hi ⊢; rcases hi with hi | hi <;> simp [hi]⟩
    · exact ⟨_, _, _, r', he, fun i hi => by
      simp only [allInsts, List.mem_append] at hi ⊢; rcases hi with hi | hi <;> simp [hi]⟩
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r', -, -, -, -, -, -, -, -, he, rfl⟩ :=
      Spike.Lib.LowerShape.lowerC2_xchg_inv hr
    exact ⟨_, _, _, r', he, fun i hi => by
      simp only [allInsts, List.mem_append, List.mem_cons] at hi ⊢; rcases hi with hi | hi <;> simp [hi]⟩

/-- **A plain call at a `TailOf` a term is in its closed form**: a call of
`g`, not one of the lowering context's externs, at a `TailOf` `e` is a
`call` of `Names.user g` among the instructions of `e`'s closed form (from
any environment, counter, label and label counter). -/
theorem call_mem_lowerC2 {cx : Scc.Lower.Ctx} {x g : String} {is : List String} {a : At} {ts : List Ty}
    {e' e : Expr} (ht : TailOf (.let_ x (.call g is a ts) e') e) (hx : cx.externs.find? (·.1 == g) = none) :
    ∀ {env : Scc.Lower.Env} {n : Nat} {l : Scc.IR.Label} {k : Nat} {r : Res2},
      lowerC2 cx env n l k e = some r →
      ∃ ds ws, Scc.IR.Inst.call ds (Scc.Lower.Names.user g) ws ∈ allInsts r.toRes1 := by
  induction ht with
  | refl =>
    intro env n l k r hr
    rcases Spike.Lib.LowerShape.lowerC2_call_inv hr with
      ⟨_, _, w, _, -, -, -, -, -, rfl⟩ | ⟨_, _, _, _, _, _, _, _, hxe, -⟩
    · exact ⟨[Scc.Lower.Inv.regName "r" n], [w], by simp [allInsts]⟩
    · rw [hx] at hxe; cases hxe
  | let_ y op _ ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, r', he, hsub⟩ := lowerC2_let_sub hr
    obtain ⟨ds, ws, hm⟩ := ih he
    exact ⟨ds, ws, hsub _ hm⟩
  | split a' y z _ ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, _, -, -, -, he⟩ := Spike.Lib.LowerShape.lowerC2_split_inv hr
    exact ih he
  | unpack a' i y _ ih =>
    intro env n l k r hr
    obtain ⟨_, _, -, he⟩ := Spike.Lib.LowerShape.lowerC2_unpack_inv hr
    exact ih he
  | unpackT a' α y _ ih =>
    intro env n l k r hr
    simp [lowerC2] at hr
  | yes a' b no _ ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, ry, rn, -, -, hy, -, rfl⟩ := Spike.Lib.LowerShape.lowerC2_ifeq_inv hr
    obtain ⟨ds, ws, hm⟩ := ih hy
    refine ⟨ds, ws, ?_⟩
    simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons] at hm ⊢
    rcases hm with hm | ⟨b, hb, hm⟩
    · exact .inr ⟨_, .inl (.inl rfl), hm⟩
    · exact .inr ⟨b, .inl (.inr hb), hm⟩
  | no a' b yes _ ih =>
    intro env n l k r hr
    obtain ⟨_, _, _, _, ry, rn, -, -, -, hn, rfl⟩ := Spike.Lib.LowerShape.lowerC2_ifeq_inv hr
    obtain ⟨ds, ws, hm⟩ := ih hn
    refine ⟨ds, ws, ?_⟩
    simp only [allInsts, List.mem_append, List.mem_flatMap, List.mem_cons] at hm ⊢
    rcases hm with hm | ⟨b, hb, hm⟩
    · exact .inr ⟨_, .inr (.inl rfl), hm⟩
    · exact .inr ⟨b, .inr (.inr hb), hm⟩

/-- **A `call` of a closed form is a callee of its `func2`** (`callees`). -/
theorem mem_callees_func2 {name : Scc.IR.Sym} {ps sc hq : List Scc.IR.Reg} {r : Res2} {ds : List Scc.IR.Reg}
    {g : Scc.IR.Sym} {ws : List Scc.IR.Operand} (h : Scc.IR.Inst.call ds g ws ∈ allInsts r.toRes1) :
    g ∈ (callees (func2 name ps sc hq r)).1 := by
  simp only [allInsts, List.mem_append, List.mem_flatMap] at h
  simp only [callees, func2, List.flatMap_cons, List.mem_append, List.mem_flatMap, List.mem_filterMap]
  rcases h with h | ⟨b, hb, h⟩
  · exact .inl ⟨_, h, rfl⟩
  · exact .inr ⟨b, hb, _, h, rfl⟩

/-! ## The rows -/

section Place

variable {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)) = true)

set_option hygiene false in
/-- The output. -/
local notation "OUT" => Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)

set_option hygiene false in
/-- The `j`th compiled block's code facts at the theorem's immediates. -/
local notation "FC" j:max d:max hd:max => fnCode2OfPMe hp h Λ j d hd

/-- **A compiled block's row at its frame** from the placement check: the
`j`th compiled block's closed form (`LowC2`, data `w`) and its row of the
stack need table at its code facts' frame `fd`, with a need `nf ≥ fd`
covering `fd` and each callee's need. -/
theorem row2_of_placeOK (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) :
    ∃ (w : Spike.Lib.LowerNode.Low2) (a : String) (nf : Nat),
      Spike.Lib.LowerNode.LowC2 p cfg.layout.obj d w ∧
      row? (OUT).place.need (Scc.Lower.Names.user d.name) = some (a, (FC j d hd).cx.frame, nf) ∧
      (FC j d hd).cx.frame ≤ nf ∧
      ∀ g ∈ (callees (func2 (Scc.Lower.Names.user d.name) (Spike.Lib.LowerShape.paramsR d w.na) w.sc w.hp
          w.r)).1, ∀ a' fg ng, row? (OUT).place.need g = some (a', fg, ng) → (FC j d hd).cx.frame + ng ≤ nf := by
  obtain ⟨w, fi, hw, -, hmem, hcx⟩ := fnCode2OfPMe_spec2 hp h Λ j d hd
  have hc := fnCode1_of_placeOKAt h (lowerAll_place_ir cfg p)
  have h1 := needOk1_of_fnOk1 (fnOk1_of_fnCode1Ok hc hmem rfl)
  rw [← hcx] at h1
  obtain ⟨a, nf, hr, hle, hcal⟩ := needOk1_row h1
  exact ⟨w, a, nf, hw, hr, hle, hcal⟩

/-- **`Room2OwnStmt`**: a compiled block's room covers its frame and the
slack (its row's need is at least its frame). -/
theorem room2Own (hp : Scc.Lower.Accepted2 p = true) : Room2OwnStmt h hp := by
  intro j d hd s lo hR
  obtain ⟨-, a, nf, -, hr, hle, -⟩ := row2_of_placeOK h hp hd
  obtain ⟨a', f', n, hr', hlo⟩ := hR
  rw [hr] at hr'
  cases hr'
  omega

/-- **The callee of a plain call at a point of a compiled block**: the
earlier compiled block `dg` named `g`, and the call site's rows: the
caller's need `nd` covers its frame and `g`'s need `ng`. -/
theorem callee2_of_placeOK (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {x g : String} {a : At} {e : Expr}
    (ht : TailAt2 p j (.let_ x (.call g [] a []) e)) (hcl : Spike.Lib.LowerCall.Callee (FC j d hd).lcx g) :
    ∃ (j' : Nat) (dg : Decl) (_ : (compiled2 p)[j']? = some dg), j' < j ∧ dg.name = g ∧
      ∃ (a1 : String) (nd : Nat) (a2 : String) (fg ng : Nat),
        row? (OUT).place.need (Scc.Lower.Names.user d.name) = some (a1, (FC j d hd).cx.frame, nd) ∧
        row? (OUT).place.need (Scc.Lower.Names.user g) = some (a2, fg, ng) ∧
        (FC j d hd).cx.frame + ng ≤ nd := by
  have hl := (fnCode2OfPMe_spec hp h Λ j d hd).1
  obtain ⟨hx, dg, hf, -⟩ := hcl
  rw [hl] at hx hf
  obtain ⟨j', hlt, hj'⟩ := Spike.Lib.LowerNode.callOrder2T hp hd (ht d hd) hx hf
  have hn : dg.name = g := by simpa using List.find?_some hf
  obtain ⟨w, a1, nd, hw, hr, -, hcal⟩ := row2_of_placeOK h hp hd
  obtain ⟨-, a2, ng, -, hrg, -, -⟩ := row2_of_placeOK h hp hj'
  rw [hn] at hrg
  obtain ⟨ds, ws, hm⟩ := call_mem_lowerC2 (cx := Spike.Lib.LowerNode.lcx2 p cfg.layout.obj d) (ht d hd) hx hw.2.2
  exact ⟨j', dg, hj', hlt, hn, a1, nd, a2, _, ng, hr, hrg, hcal _ (mem_callees_func2 hm) _ _ _ hrg⟩

/-- **`Room2CalleeStmt`**: at a plain call of `g` at a point of the `j`th
compiled block whose room is at `lo`, the callee is an earlier compiled
block named `g` whose room is at `lo + fd` (right below the caller's
frame `fd`). -/
theorem room2Callee (hp : Scc.Lower.Accepted2 p = true) : Room2CalleeStmt h hp := by
  intro j d hd x g a e s lo ht hcl hR
  obtain ⟨j', dg, hj', hlt, hn, a1, nd, a2, fg, ng, hr, hrg, hle⟩ := callee2_of_placeOK h hp hd ht hcl
  refine ⟨j', dg, hj', hlt, hn, a2, fg, ng, hrg, ?_⟩
  obtain ⟨a', f', n, hr', hlo⟩ := hR
  rw [hr] at hr'
  cases hr'
  omega

/-- **`Lim2CalleeStmt`**: at the same call, the caller's limit room at
`sp` gives the callee's at its entry `sp'` right below the caller's
frame. -/
theorem lim2Callee (hp : Scc.Lower.Accepted2 p = true) : Lim2CalleeStmt h hp := by
  intro j d hd x g a e G sp sp' ht hcl hsp hL
  obtain ⟨j', dg, hj', hlt, hn, a1, nd, a2, fg, ng, hr, hrg, hle⟩ := callee2_of_placeOK h hp hd ht hcl
  refine ⟨a2, fg, ng, hrg, fun v hv => ?_⟩
  obtain ⟨a', f', n, hr', hv'⟩ := hL
  rw [hr] at hr'
  cases hr'
  have := hv' v hv
  omega

set_option hygiene false in
/-- The runtime's layout of the output at the theorem's immediates. -/
local notation "Ly" => Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK h (imms2Me Λ p)

set_option hygiene false in
/-- The canonical load's memory of the output. -/
local notation "M0" => Spike.Lib.A64.PhRec.m0Of (Ly).Λ (Scc.Cert.PlaceOK.Out.prog (OUT)) (OUT).secs

/-- **`LimOk2Stmt`**: the prologue's limit facts inside `MSAt` at any
frames, the abort and the invariant: the limit word a runtime word, mapped
(`rt_limOk` at no label placed, `limOk_toAX`), unmapped in `F` and with
room by the premises, at the state's `TPIDR_EL0` (`limOk_tpidr`). -/
theorem limOk2 (hp : Scc.Lower.Accepted2 p = true) : LimOk2Stmt h hp := by
  intro J F fs σ fsz htp hun hroom
  refine limOk_tpidr htp ?_
  have e : UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64) = UInt64.ofBitVec ((Ly).pinA + 0#64 + 8#64) := by
    rw [Spike.Lib.A64.Rt.pinA_lab0 (Ly)]
  have h0 := Spike.Lib.A64.Rt.rt_limOk (L := Ly) (μ := Spike.Lib.A64.PhRec.μ (Ly)) (rd := IsNum)
    (G := Spike.Lib.A64.PhRec.GOf Ly M0) (own := Spike.Lib.A64.PhRec.own (Ly)) (lbl := fun _ => none)
    (lsize := fun _ => 0) (Spike.Lib.A64.Rt.rtFree_none _ fun _ => rfl) (Z := BitVec.allOnes 64)
    (fun v _ => by have := (v.setWidth 64).isLt; simp only [BitVec.toNat_allOnes]; omega)
  have h1 := limOk_toAX (p := p) (ar := Spike.Lib.A64.Rt.arOf (Ly).Λ)
    (J := Spike.Lib.AllocReach.IN (Spike.Lib.A64.Rt.arOf (Ly).Λ) (fun _ => none) (fun _ => 0) J)
    (ab := ab2 p (Ly).lab) h0
  rw [← e] at h1
  revert hroom
  generalize ab2 p (Ly).lab = ab at h1 ⊢
  cases ab <;> exact fun hroom => ⟨h1.rt, h1.mp, hun, hroom⟩

end Place

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.lowerC2_let_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.lowerC2_let_sub

/-- info: 'Spike.Lib.LowerA64.call_mem_lowerC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.call_mem_lowerC2

/-- info: 'Spike.Lib.LowerA64.mem_callees_func2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.mem_callees_func2

/-- info: 'Spike.Lib.LowerA64.row2_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.row2_of_placeOK

/-- info: 'Spike.Lib.LowerA64.room2Own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.room2Own

/-- info: 'Spike.Lib.LowerA64.callee2_of_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.callee2_of_placeOK

/-- info: 'Spike.Lib.LowerA64.room2Callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.room2Callee

/-- info: 'Spike.Lib.LowerA64.lim2Callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.lim2Callee

/-- info: 'Spike.Lib.LowerA64.limOk2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.limOk2

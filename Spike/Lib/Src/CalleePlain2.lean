/-
**A plain call of an `Accepted2` program names an ordinary block**
(ISA-neutral): the block a plain call names on a compiled block's walk is
`plain2`, `f(x : Int) : Int` without buffers, so it returns `Int` and
allocates no buffer on its own walk.

- `body2_of_compiledR`: `body2_of_compiled` with the body's reserved names
  the program's (`reserved (setupOf p) (hasPrint p)`);
- `callee_plain2`: at a call of `g` at a `TailOf` a compiled block's body,
  `g` not among the frontend's externs, the block named `g` is `plain2`;
- `callee_nilIdx`: such a call has no indices and no type arguments;
- `plain2_retTy`, `plain2_argTy`, `plain2_noNewBuf`: a `plain2` block
  returns `Int`, takes `Int` and has no buffer allocation at a `TailOf` its
  body;
- `callee_int`, `callee_argInt`, `callee_noNewBuf`: the three at a called
  block.
-/
import Spike.Lib.Src.Walk2Facts

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (Cx2 body2 callee2 decl2 decls2 main2 setup2 plain2 reserved hasPrint isPrintExt Accepted2 setupOf)

/-- **The body check of a compiled block, with its reserved names**
(`body2_of_compiled`): the body's context reserves the program's names
(`reserved (setupOf p) (hasPrint p)`). -/
theorem body2_of_compiledR {p : Prog} (hacc : Accepted2 p = true) {A B : Prog} {d : Decl}
    (hp : p = A ++ d :: B) (hc : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false) :
    ∃ (c2 : Cx2) (cs bufs : List (String × Nat)) (scope : List String),
      body2 c2 cs bufs scope d.body = true ∧ c2.ext = hasPrint p ∧
      c2.excl = reserved (setupOf p) (hasPrint p) ∧
      ∀ g ∈ c2.earlier, g ∈ A.map (·.name) := by
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hacc; exact hacc.1.1.1.1.1.1.1.2
  have hdm : d ∈ p := by rw [hp]; simp
  have hds' : decls2 [] (setupOf p) (hasPrint p) (A ++ d :: B) = true := by rw [← hp]; exact hds
  have hE := decl2_of_split A [] hds'
  simp only [List.append_nil] at hE
  have hpe := isPrintExt_false_of_compiled hdm hc
  have hEs : ∀ g ∈ (A.map (·.name)).reverse, g ∈ A.map (·.name) := fun g h => List.mem_reverse.1 h
  unfold decl2 at hE
  simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hE
  split at hE
  · rename_i hl
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    have hx : Scc.Frontend.externOf d = some .print := by
      unfold Scc.Frontend.externOf
      have : (d.name == "print") = false := by rw [hl.2]; decide
      simp [hl.2, hE]
    have hm : (d.name, Scc.Frontend.Extern.print) ∈ Scc.Frontend.externs p :=
      List.mem_filterMap.2 ⟨d, hdm, by rw [hx]; rfl⟩
    have : ((Scc.Frontend.externs p).any (·.1 == d.name)) = true := List.any_eq_true.2 ⟨_, hm, by simp⟩
    rw [hc] at this; cases this
  split at hE
  · unfold main2 at hE
    simp only [Bool.and_eq_true] at hE
    exact ⟨_, _, _, _, hE.2, rfl, rfl, hEs⟩
  split at hE
  · split at hE
    · unfold setup2 at hE
      simp only [Bool.and_eq_true] at hE
      exact ⟨_, _, _, _, hE.2, rfl, rfl, fun g h => hEs g (List.erase_subset h)⟩
    · unfold plain2 at hE
      simp only [Bool.and_eq_true] at hE
      exact ⟨_, _, _, _, hE.2, rfl, rfl, hEs⟩
  · unfold plain2 at hE
    simp only [Bool.and_eq_true] at hE
    exact ⟨_, _, _, _, hE.2, rfl, rfl, hEs⟩

/-- **The block a plain call names is `plain2`**: at a call of `g` at a
`TailOf` the `j`th compiled block's body, `g` not among the frontend's
externs, the block `dg` named `g` is an ordinary block (`callee2` rules out
`main` and the reserved names, the externs rule out the output extern). -/
theorem callee_plain2 {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') d.body)
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = none)
    {dg : Decl} (hf : p.find? (·.name == g) = some dg) :
    ∃ (E excl : List String) (ext : Bool), plain2 E excl ext dg = true := by
  have hjm := List.mem_of_getElem? hj
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 hjm
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hp⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, hext, hexcl, -⟩ := body2_of_compiledR hacc hp hdc'
  have hcl : callee2 c2 g = true := by
    rcases body2_callT ht hb with hpr | hcl
    · exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at hpr
      obtain ⟨hpe, rfl⟩ := hpr
      have := externs_print (hext ▸ hpe)
      rw [hx] at this; cases this
    · exact hcl
  simp only [callee2, Scc.Lower.callee1, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hcl
  obtain ⟨⟨-, hnm⟩, hne⟩ := hcl
  rw [hexcl] at hne
  have hdgm := List.mem_of_find?_eq_some hf
  have hdgn : dg.name = g := by simpa using List.find?_some hf
  -- `dg`'s own `decl2` check
  have hds : decls2 [] (setupOf p) (hasPrint p) p = true := by
    simp only [Accepted2, Bool.and_eq_true] at hacc; exact hacc.1.1.1.1.1.1.1.2
  obtain ⟨A', B', hp'⟩ := List.append_of_mem hdgm
  have hds' : decls2 [] (setupOf p) (hasPrint p) (A' ++ dg :: B') = true := by rw [← hp']; exact hds
  have hE := decl2_of_split A' [] hds'
  simp only [List.append_nil] at hE
  have hgc : ((Scc.Frontend.externs p).any (·.1 == dg.name)) = false := by
    have := List.find?_eq_none.1 hx
    simp only [List.any_eq_false]
    intro y hy; have := this y hy; rw [hdgn]; simpa using this
  have hpe := isPrintExt_false_of_compiled hdgm hgc
  unfold decl2 at hE
  simp only [hpe, Bool.false_eq_true, ↓reduceIte] at hE
  split at hE
  · rename_i hl
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq] at hl
    rw [← hdgn, hl.2] at hne
    simp [reserved, hl.1] at hne
  split at hE
  · rename_i hm
    exfalso
    simp only [beq_iff_eq] at hm
    exact hnm (hdgn ▸ hm)
  split at hE
  · rename_i s hs
    split at hE
    · rename_i hr
      exfalso
      simp only [beq_iff_eq] at hr
      rw [← hdgn, hr] at hne
      simp [reserved, hs] at hne
    · exact ⟨_, _, _, hE⟩
  · exact ⟨_, _, _, hE⟩

/-- **A plain call has no indices and no type arguments**: at a call of `g`
at a `TailOf` a compiled block's body, `g` not among the frontend's externs
(so not the output call), `body2`'s check of an ordinary callee. -/
theorem callee_nilIdx {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') d.body)
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = none) : is = [] ∧ ts = [] := by
  have hjm := List.mem_of_getElem? hj
  obtain ⟨hdp, hdc⟩ := List.mem_filter.1 hjm
  have hdc' : ((Scc.Frontend.externs p).any (·.1 == d.name)) = false := by simpa using hdc
  obtain ⟨A, B, hp⟩ := List.append_of_mem hdp
  obtain ⟨c2, cs, bufs, scope, hb, hext, -, -⟩ := body2_of_compiledR hacc hp hdc'
  obtain ⟨_, _, _, hb'⟩ := body2_tail ht hb
  simp only [body2, Bool.and_eq_true] at hb'
  have hc := hb'.1.1
  revert hc
  split
  · rename_i hh
    intro _
    exfalso
    simp only [beq_iff_eq] at hh
    obtain ⟨hpe, rfl⟩ := hh
    have := externs_print (hext ▸ hpe)
    rw [hx] at this; cases this
  · intro hc
    simp only [Bool.and_eq_true, List.isEmpty_iff] at hc
    exact ⟨hc.1.2, hc.2⟩

/-- A `plain2` block returns `Int`. -/
theorem plain2_retTy {E excl : List String} {ext : Bool} {d : Decl} (h : plain2 E excl ext d = true) :
    d.retTy = .int := by
  simp only [plain2, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

/-- A `plain2` block takes `Int`. -/
theorem plain2_argTy {E excl : List String} {ext : Bool} {d : Decl} (h : plain2 E excl ext d = true) :
    d.argTy = .int := by
  simp only [plain2, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

/-- **A `plain2` block allocates no buffer** at a `TailOf` its body (its
body's context has no allocations). -/
theorem plain2_noNewBuf {E excl : List String} {ext : Bool} {d : Decl} (h : plain2 E excl ext d = true)
    {x : String} {n : At} {τ : Ty} {e : Expr} (ht : TailOf (.let_ x (.newBuf n τ) e) d.body) : False := by
  simp only [plain2, Bool.and_eq_true] at h
  obtain ⟨_, _, _, hb⟩ := body2_tail ht h.2
  simp [body2] at hb

/-- **A called block returns `Int`** (`callee_plain2`). -/
theorem callee_int {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') d.body)
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = none)
    {dg : Decl} (hf : p.find? (·.name == g) = some dg) : dg.retTy = .int :=
  let ⟨_, _, _, h⟩ := callee_plain2 hacc hj ht hx hf
  plain2_retTy h

/-- **A called block takes `Int`** (`callee_plain2`). -/
theorem callee_argInt {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') d.body)
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = none)
    {dg : Decl} (hf : p.find? (·.name == g) = some dg) : dg.argTy = .int :=
  let ⟨_, _, _, h⟩ := callee_plain2 hacc hj ht hx hf
  plain2_argTy h

/-- **A called block allocates no buffer on its walk** (`callee_plain2`):
no buffer allocation at a `TailOf` its body. -/
theorem callee_noNewBuf {p : Prog} (hacc : Accepted2 p = true) {j : Nat} {d : Decl}
    (hj : (compiled2 p)[j]? = some d) {x g : String} {is : List String} {a : At} {ts : List Ty} {e' : Expr}
    (ht : TailOf (.let_ x (.call g is a ts) e') d.body)
    (hx : (Scc.Frontend.externs p).find? (·.1 == g) = none)
    {dg : Decl} (hf : p.find? (·.name == g) = some dg)
    {y : String} {n : At} {τ : Ty} {e : Expr} (hn : TailOf (.let_ y (.newBuf n τ) e) dg.body) : False :=
  let ⟨_, _, _, h⟩ := callee_plain2 hacc hj ht hx hf
  plain2_noNewBuf h hn

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.callee_plain2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callee_plain2

/-- info: 'Spike.Lib.LowerNode.callee_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callee_int

/-- info: 'Spike.Lib.LowerNode.callee_argInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callee_argInt

/-- info: 'Spike.Lib.LowerNode.callee_noNewBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callee_noNewBuf

/-- info: 'Spike.Lib.LowerNode.callee_nilIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.callee_nilIdx

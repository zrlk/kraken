import Spike.Lib.Src.ImmsMeTail
import Spike.Lib.LowerShapeC2Some

/-!
**A buffer allocation's count in an `Accepted2` block** (ISA-neutral). At
every allocation `let x = newBuf cn τ in e` still to lower in a compiled
block of an `Accepted2` program (`TailAt2`), the element type is one word
(`elem2`) and the count is a value `k` known before run time with
`1 ≤ k < 2 ^ 28` (`body2`): a literal, or a variable whose literal words at
that point of the block's literal walk are `k`, hence `imms2Of p`'s entry
there (`immsCoherent2`).

- `CsLits`: `body2`'s known values against the literal walk (each a leaf
  with its value as literal); `body2_let_cs` keeps it past a `let`;
- `newBufK_walk`: along a `body2` body, every allocation's facts at its
  point of the literal walk;
- `newBufK_of_accepted2`: at a compiled block's allocation, `elem2` and the
  count `k` (a literal, or `imms2Of p`'s entry for the variable);
- `newBufKv_of_accepted2`: the lowering's immediate count `kv` at that
  allocation (one immediate word in a grouped environment whose immediates
  are the theorem's table `imms2Me Λ p`) is `k`, so `1 ≤ kv < 2 ^ 28`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.Lower (LitV litAt opLit litWalk2 litWalks2 body2 Cx2 constOf bindC unbuf elem2 params2 shapeOf wordLit
  imms2Of immsCoherent2)
open Scc.Lower.Inv (atomV)

/-- **`body2`'s known values against the literal walk**: each known
variable's literal words a leaf with its value. -/
def CsLits (cs : List (String × Nat)) (lits : List (String × LitV)) : Prop :=
  ∀ y k, cs.lookup y = some k → lits.lookup y = some (.leaf (some k))

theorem CsLits.unbuf {cs : List (String × Nat)} {lits : List (String × LitV)} (h : CsLits cs lits)
    (x : String) (L : LitV) : CsLits (Scc.Lower.unbuf x cs) ((x, L) :: lits) := by
  intro y k hy
  rw [lookup_unbuf] at hy
  rw [lookup_cons_name]
  split at hy
  · cases hy
  · rename_i hyx; simp only [hyx, ite_false]; exact h y k hy

theorem CsLits.sub {cs : List (String × Nat)} {lits : List (String × LitV)} (h : CsLits cs lits)
    (i : String) : CsLits (Scc.Lower.unbuf i cs) lits := by
  intro y k hy
  rw [lookup_unbuf] at hy
  split at hy
  · cases hy
  · exact h y k hy

/-- A known atom's literal words are a leaf with its value. -/
theorem CsLits.constOf {cs : List (String × Nat)} {lits : List (String × LitV)} (h : CsLits cs lits) {a : At}
    {k : Nat} (hk : constOf cs a = some k) : litAt lits a = .leaf (some k) := by
  cases a with
  | var y =>
    simp only [Scc.Lower.constOf] at hk
    simp [litAt, h y k hk]
  | lit n =>
    simp only [Scc.Lower.constOf, Option.some.injEq] at hk
    subst hk; rfl
  | unit => simp [Scc.Lower.constOf] at hk

theorem CsLits.bind {cs : List (String × Nat)} {lits : List (String × LitV)} (h : CsLits cs lits)
    (x : String) (a : At) : CsLits (bindC x (Scc.Lower.constOf cs a) cs) ((x, litAt lits a) :: lits) := by
  cases hk : Scc.Lower.constOf cs a with
  | none => exact h.unbuf x _
  | some k =>
    intro y k' hy
    simp only [Scc.Lower.bindC] at hy
    rw [lookup_cons_name] at hy
    rw [lookup_cons_name]
    split at hy
    · rename_i hyx; cases hy; simp only [hyx, ite_true, h.constOf hk]
    · rename_i hyx
      simp only [hyx, ite_false]
      rw [lookup_unbuf] at hy
      simp only [hyx, ite_false] at hy
      exact h y k' hy

/-- **A `body2` `let`'s body is `body2`** with the known values against the
literal walk past the `let` (`opLit`). -/
theorem body2_let_cs (p : Prog) {cx2 : Cx2} {cs bufs : List (String × Nat)} {scope : List String} {x : String}
    {op : Op} {e : Expr} {lits : List (String × LitV)} (hb : body2 cx2 cs bufs scope (.let_ x op e) = true)
    (hC : CsLits cs lits) :
    ∃ cs' bufs', body2 cx2 cs' bufs' (x :: scope) e = true ∧ CsLits cs' ((x, opLit p lits op) :: lits) := by
  cases op with
  | atom a =>
    simp only [body2, Bool.and_eq_true] at hb
    exact ⟨_, _, hb.2, hC.bind x a⟩
  | nameI a =>
    simp only [body2, Bool.and_eq_true] at hb
    exact ⟨_, _, hb.2, hC.bind x a⟩
  | newBuf n τ =>
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨-, hm⟩ := hb
    split at hm
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      exact ⟨_, _, hm.2, hC.unbuf x _⟩
    · cases hm
  | xchgAt b i v =>
    cases b <;> cases i <;> simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb <;>
      exact ⟨_, _, hb.2, hC.unbuf x _⟩
  | _ => simp only [body2, Bool.and_eq_true, Bool.false_eq_true] at hb <;> exact ⟨_, _, hb.2, hC.unbuf x _⟩

/-- **Every allocation along a `body2` body**: at an allocation
`let x = newBuf cn τ in e'` still to lower (`TailOf`), a point of the
literal walk with layouts `lits'`, the element one word, and the count a
known value `k`, `1 ≤ k < 2 ^ 28`: a literal, or a variable with literal
words `k` at `lits'`. -/
theorem newBufK_walk (p : Prog) (cx2 : Cx2) {x : String} {cn : At} {τ : Ty} {e' : Expr} {e : Expr}
    (ht : TailOf (.let_ x (.newBuf cn τ) e') e) :
    ∀ (cs bufs : List (String × Nat)) (scope : List String) (lits : List (String × LitV)),
      body2 cx2 cs bufs scope e = true → CsLits cs lits →
      ∃ lits' k, (.let_ x (.newBuf cn τ) e', lits') ∈ litWalk2 p lits e ∧ elem2 τ = true ∧ 1 ≤ k ∧ k < 2 ^ 28 ∧
        (cn = .lit k ∨ ∃ y, cn = .var y ∧ lits'.lookup y = some (.leaf (some k))) := by
  induction ht with
  | refl =>
    intro cs bufs scope lits hb hC
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨⟨⟨-, -⟩, hel⟩, hm⟩ := hb
    split at hm
    · rename_i k hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      refine ⟨lits, k, by rw [litWalk2]; exact List.mem_cons_self .., hel, hm.1.1, hm.1.2, ?_⟩
      cases cn with
      | lit n =>
        simp only [Scc.Lower.constOf, Option.some.injEq] at hk
        exact .inl (by rw [hk])
      | var y =>
        simp only [Scc.Lower.constOf] at hk
        exact .inr ⟨y, rfl, hC y k hk⟩
      | unit => simp [Scc.Lower.constOf] at hk
    · cases hm
  | let_ y op _ ih =>
    intro cs bufs scope lits hb hC
    obtain ⟨cs', bufs', hb', hC'⟩ := body2_let_cs p hb hC
    obtain ⟨lits', k, hm, H⟩ := ih cs' bufs' _ _ hb' hC'
    exact ⟨lits', k, by rw [litWalk2]; exact List.mem_cons_of_mem _ hm, H⟩
  | @split a y z e0 _ ih =>
    intro cs bufs scope lits hb hC
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨l, r, hlw⟩ : ∃ l r, litWalk2 p lits (.split a y z e0) =
        (.split a y z e0, lits) :: litWalk2 p ((z, r) :: (y, l) :: lits) e0 := by
      rw [litWalk2]; split <;> exact ⟨_, _, rfl⟩
    obtain ⟨lits', k, hm, H⟩ := ih _ _ _ _ hb.2 ((hC.unbuf y l).unbuf z r)
    exact ⟨lits', k, by rw [hlw]; exact List.mem_cons_of_mem _ hm, H⟩
  | unpack a i y _ ih =>
    intro cs bufs scope lits hb hC
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨lits', k, hm, H⟩ := ih _ _ _ _ hb.2 ((hC.sub i).unbuf y _)
    exact ⟨lits', k, by rw [litWalk2]; exact List.mem_cons_of_mem _ hm, H⟩
  | unpackT a α y _ _ =>
    intro cs bufs scope lits hb _
    simp [body2] at hb
  | yes a b no _ ih =>
    intro cs bufs scope lits hb hC
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨lits', k, hm, H⟩ := ih _ _ _ _ hb.1.2 hC
    exact ⟨lits', k, by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hm), H⟩
  | no a b yes _ ih =>
    intro cs bufs scope lits hb hC
    simp only [body2, Bool.and_eq_true] at hb
    obtain ⟨lits', k, hm, H⟩ := ih _ _ _ _ hb.2 hC
    exact ⟨lits', k, by rw [litWalk2]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hm), H⟩

/-- **A compiled block's allocation's count** in an `Accepted2` program: at
an allocation `let x = newBuf cn τ in e` of the `j`th compiled block
(`TailAt2`), the element one word (`elem2`) and the count a value `k`
known before run time, `1 ≤ k < 2 ^ 28`: the literal `k`, or a variable
`y` with `imms2Of p`'s entry `k` at the allocation (`immsCoherent2` at the
point of the block's literal walk, `newBufK_walk`). -/
theorem newBufK_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {j : Nat} {d : Decl}
    (hd : (compiled2 p)[j]? = some d) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (ht : TailAt2 p j (.let_ x (.newBuf cn τ) e)) :
    elem2 τ = true ∧ ∃ k, 1 ≤ k ∧ k < 2 ^ 28 ∧
      (cn = .lit k ∨ ∃ y, cn = .var y ∧ imms2Of p (.let_ x (.newBuf cn τ) e) y 0 = some k) := by
  obtain ⟨hdp, hne, hnl⟩ := compiled2_facts hp (List.mem_of_getElem? hd)
  obtain ⟨-, -, cx2, hb⟩ := decl2_src hp hdp hne hnl
  obtain ⟨lits', k, hm, hel, hk1, hk2, hc⟩ :=
    newBufK_walk p cx2 (ht d hd) [] [] _ ((params2 d).map (·, shapeOf d.argTy)) hb (fun _ _ h => by cases h)
  refine ⟨hel, k, hk1, hk2, ?_⟩
  rcases hc with hc | ⟨y, rfl, hy⟩
  · exact .inl hc
  · refine .inr ⟨y, rfl, ?_⟩
    have hco : immsCoherent2 p = true := by
      simp only [Scc.Lower.Accepted2, Bool.and_eq_true] at hp
      exact hp.1.1.1.1.1.2
    have hw : (Expr.let_ x (.newBuf (.var y) τ) e, lits') ∈ litWalks2 p := List.mem_flatMap.2 ⟨d, hdp, hm⟩
    have hq := List.all_eq_true.mp (List.all_eq_true.mp hco _ hw) _ (lookup_mem' hy)
    have := List.all_eq_true.mp hq 0 (List.mem_range.2 (by simp [LitV.words]))
    have hwl : wordLit lits' y 0 = some k := by simp [wordLit, hy, LitV.words]
    simp only [hwl, beq_iff_eq] at this
    exact this

/-- **The lowering's immediate count at a compiled block's allocation** in
an `Accepted2` program: the count atom `cn` lowered to one immediate `kv`
(`atomV`) in a grouped environment (`GrpL`) whose immediates at the
allocation are the theorem's table (`ImmIn (imms2Me Λ p)`) is
`newBufK_of_accepted2`'s `k`, so `1 ≤ kv < 2 ^ 28`. -/
theorem newBufKv_of_accepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {Λ : Scc.Sem.Layout} {j : Nat}
    {d : Decl} (hd : (compiled2 p)[j]? = some d) {x : String} {cn : At} {τ : Ty} {e : Expr}
    (ht : TailAt2 p j (.let_ x (.newBuf cn τ) e)) {env : Scc.Lower.Env} (hg : GrpL env)
    (hi : ImmIn (imms2Me Λ p) (ofEnv2 env) (.let_ x (.newBuf cn τ) e))
    {tk : Ty} {kv : UInt64} (hat : atomV env cn = some (tk, [.imm kv])) :
    1 ≤ kv.toNat ∧ kv.toNat < 2 ^ 28 := by
  obtain ⟨-, k, hk1, hk2, hc⟩ := newBufK_of_accepted2 hp hd ht
  suffices kv.toNat = k by omega
  rcases hc with rfl | ⟨y, rfl, hy⟩
  · have h0 := Spike.Lib.LowerShape.atomV_lit hat
    obtain ⟨-, h2⟩ := Prod.mk.inj h0
    obtain ⟨h3, -⟩ := List.cons.inj h2
    have hk : kv = UInt64.ofNat k := Scc.IR.Operand.imm.inj h3
    subst hk
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  · obtain ⟨b, hb, hv⟩ := Spike.Lib.LowerShape.atomV_var hat
    obtain ⟨rfl, hw⟩ := Prod.mk.inj hv.symm
    obtain ⟨pls, hpl⟩ := Option.isSome_iff_exists.mp (hg _ _ hb)
    rw [hw] at hpl
    have h1 := group_one hpl
    have hl : Spike.Lib.Form.lookupS (ofEnv2 env) y = some (b.2.1, [.one (.imm kv)]) := by
      rw [lookupS_ofEnv2, hb]; simp [hw, hpl, h1]
    have h2 := hi y 0 kv (by rw [hl]; rfl)
    rw [imms2Me_tailAt2 hp hd ht, hy] at h2
    exact (Option.some.inj h2).symm

end Spike.Lib.LowerNode

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerNode.newBufK_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.newBufK_walk

/-- info: 'Spike.Lib.LowerNode.newBufK_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.newBufK_of_accepted2

/-- info: 'Spike.Lib.LowerNode.newBufKv_of_accepted2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerNode.newBufKv_of_accepted2

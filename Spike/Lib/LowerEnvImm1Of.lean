/-
**The lowering's immediates of an `Accepted1` program are its table
`imms1Of`** (ISA-neutral).

`Scc.Lower.imms1Of p` keys the immediates by remaining term, from the
literal bindings along each code block's body (`litWalk`); the lowering
binds a variable to an immediate exactly through literal `let`s and copies
of them. Along the walk the lowering's environment and the literal bindings
are related (`LitRel`): an immediate word is word 0 of a variable bound to
that literal. With coherent immediates (`immsCoherent`, part of
`Accepted1`) the literal bindings at a point are `imms1Of`'s entries there.

- `LitRel env lits`: every immediate word of `env` is word 0 of a variable
  that `lits` binds to its value.
- `walk_lits`: each point of the walk `lowerEnvs1` is a point of `litWalk`
  with related literal bindings (both arms of an `if`).
- `immIn_imms1Of`: at each point of the walk of an `Accepted1` program's
  code block, the lowering's environment has its immediates in `imms1Of`.
-/
import Spike.Lib.LowerEnvImm1

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Spike.Lib
open Spike.Lib.Form (SEnv lookupS WordPl)
open Scc.Lower (litWalk litWalks litOf imms1Of immsCoherent Accepted1 params1)
open Scc.Lower.Inv (atomV env1 params1R)

/-- **The lowering's environment `env` and the literal bindings `lits` are
related**: every immediate word of `env` is word 0 of a variable that `lits`
binds to its value. -/
def LitRel (env : Scc.Lower.Env) (lits : List (String × Option Nat)) : Prop :=
  ∀ x k v, (env.find? (·.1 == x)).bind (·.2.2[k]?) = some (.imm v) → k = 0 ∧ (lits.lookup x).join = some v.toNat

/-- Binding `x` on both sides keeps `LitRel`, if `x`'s immediate words are
word 0 with `x`'s literal. -/
theorem litRel_cons {env : Scc.Lower.Env} {lits : List (String × Option Nat)} (h : LitRel env lits)
    (x : String) (t : Ty) (ws : List Scc.IR.Operand) (o : Option Nat)
    (hw : ∀ k v, ws[k]? = some (.imm v) → k = 0 ∧ o = some v.toNat) :
    LitRel ((x, t, ws) :: env) ((x, o) :: lits) := by
  intro y k v hy
  by_cases hxy : x = y
  · subst hxy
    simp only [List.find?_cons, beq_self_eq_true, Option.bind_some] at hy
    simpa [List.lookup] using hw k v hy
  · have hb : (x == y) = false := by simp [hxy]
    have hb' : (y == x) = false := by simp [Ne.symm hxy]
    simp only [List.find?_cons, hb] at hy
    simpa [List.lookup, hb'] using h y k v hy

/-- A register binding has no immediate word. -/
theorem reg_noImm (r : Scc.IR.Reg) (o : Option Nat) :
    ∀ k v, ([Scc.IR.Operand.reg r] : List Scc.IR.Operand)[k]? = some (.imm v) → k = 0 ∧ o = some v.toNat := by
  intro k v h
  cases k <;> simp at h

/-- An atom's immediate words are word 0 with its literal (`litOf`). -/
theorem atom_lits {env : Scc.Lower.Env} {lits : List (String × Option Nat)} (h : LitRel env lits) {a : At}
    {t : Ty} {ws : List Scc.IR.Operand} (ha : atomV env a = some (t, ws)) :
    ∀ k v, ws[k]? = some (.imm v) → k = 0 ∧ litOf lits a = some v.toNat := by
  intro k v hk
  cases a with
  | var y =>
    simp only [atomV, Option.map_eq_some_iff] at ha
    obtain ⟨b, hb, hbe⟩ := ha
    obtain ⟨-, rfl⟩ := Prod.mk.inj hbe
    exact h y k v (by simp [hb, hk])
  | lit n =>
    simp only [atomV] at ha
    split at ha
    · cases ha
    · rename_i hn
      simp only [Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨-, rfl⟩ := ha
      cases k with
      | succ k => simp at hk
      | zero =>
        simp only [Scc.Lower.imm, List.getElem?_cons_zero, Option.some.injEq, Scc.IR.Operand.imm.injEq] at hk
        subst hk
        refine ⟨rfl, ?_⟩
        simp only [litOf, Option.some.injEq]
        exact (Nat.mod_eq_of_lt (by omega)).symm
  | unit =>
    simp only [atomV, Option.some.injEq, Prod.mk.injEq] at ha
    obtain ⟨-, rfl⟩ := ha
    simp at hk

/-- A term is the first point of its literal walk. -/
theorem litWalk_head (lits : List (String × Option Nat)) (e : Expr) : (e, lits) ∈ litWalk lits e := by
  cases e <;> simp [litWalk]

/-- **Each point of the lowering's walk is a point of the literal walk**,
with related literal bindings (`LitRel`). -/
theorem walk_lits : ∀ (e : Expr) (env : Scc.Lower.Env) (n : Nat) (lits : List (String × Option Nat)),
    LitRel env lits → ∀ q ∈ lowerEnvs1 env n e, ∃ lits', (q.1, lits') ∈ litWalk lits e ∧ LitRel q.2.1 lits' := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n lits h q hq
    cases op with
    | atom a =>
      simp only [lowerEnvs1, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨lits, litWalk_head _ _, h⟩
      · cases ha : atomV env a with
        | none => simp [ha] at hq
        | some v =>
          obtain ⟨t, ws⟩ := v
          simp only [ha] at hq
          obtain ⟨l', hl', hr'⟩ :=
            ih _ n _ (litRel_cons h x t ws (litOf lits a) (atom_lits h ha)) q hq
          exact ⟨l', by simp [litWalk, hl'], hr'⟩
    | add a b | sub a b =>
      simp only [lowerEnvs1, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨lits, litWalk_head _ _, h⟩
      · obtain ⟨l', hl', hr'⟩ := ih _ (n + 1) _ (litRel_cons h x .int _ none (reg_noImm _ _)) q hq
        exact ⟨l', by simp [litWalk, hl'], hr'⟩
    | _ =>
      simp only [lowerEnvs1, List.mem_singleton] at hq
      subst hq
      exact ⟨lits, litWalk_head _ _, h⟩
  | ifeq a b yes no ihy ihn =>
    intro env n lits h q hq
    simp only [lowerEnvs1, List.mem_cons, List.mem_append] at hq
    rcases hq with rfl | hq | hq
    · exact ⟨lits, litWalk_head _ _, h⟩
    · obtain ⟨l', hl', hr'⟩ := ihy env _ lits h q hq
      exact ⟨l', by simp [litWalk, hl'], hr'⟩
    · obtain ⟨l', hl', hr'⟩ := ihn env _ lits h q hq
      exact ⟨l', by simp [litWalk, hl'], hr'⟩
  | _ =>
    intro env n lits h q hq
    simp only [lowerEnvs1, List.mem_singleton] at hq
    subst hq
    exact ⟨lits, litWalk_head _ _, h⟩

/-- A code block's parameter is bound to registers: no immediates. -/
theorem litRel_env1 (d : Decl) (lits : List (String × Option Nat)) : LitRel (env1 d) lits := by
  intro x k v h
  by_cases hx : d.arg = x
  · simp [env1, hx, List.getElem?_map] at h
  · have hb : (d.arg == x) = false := by simp [hx]
    simp [env1, hb] at h

theorem lookup_mem {lits : List (String × Option Nat)} {x : String} {o : Option Nat}
    (h : lits.lookup x = some o) : ∃ b ∈ lits, b.1 = x := by
  induction lits with
  | nil => simp at h
  | cons b lits ih =>
    by_cases hb : x = b.1
    · exact ⟨b, by simp, hb.symm⟩
    · have : (x == b.1) = false := by simp [hb]
      simp only [List.lookup, this] at h
      obtain ⟨c, hc, hcx⟩ := ih h
      exact ⟨c, by simp [hc], hcx⟩

/-- **At each point of the walk of an `Accepted1` program's code block, the
lowering's environment has its immediates in `imms1Of`.** -/
theorem immIn_imms1Of {p : CoreTerm.Prog} (hp : Accepted1 p = true) {d : Decl} (hd : d ∈ p) :
    ∀ q ∈ lowerEnvs1 (env1 d) 0 d.body, ImmIn (imms1Of p) (ofEnv q.2.1) q.1 := by
  intro q hq x k v h
  obtain ⟨lits, hl, hr⟩ := walk_lits d.body (env1 d) 0 _ (litRel_env1 d _) q hq
  rw [lookupS_ofEnv] at h
  have h' : (q.2.1.find? (·.1 == x)).bind (·.2.2[k]?) = some (.imm v) := by
    cases hf : q.2.1.find? (·.1 == x) with
    | none => simp [hf] at h
    | some b =>
      simp only [hf, Option.map_some, Option.bind_some, List.getElem?_map] at h ⊢
      cases hk : b.2.2[k]? with
      | none => simp [hk] at h
      | some o => simp only [hk, Option.map_some, Option.some.injEq, WordPl.one.injEq] at h; rw [h]
  obtain ⟨rfl, hn⟩ := hr x k v h'
  have hc : immsCoherent p = true := by
    simp only [Accepted1, Bool.and_eq_true] at hp
    exact hp.2
  have hw : (q.1, lits) ∈ litWalks p := by
    simp only [litWalks, List.mem_flatMap]
    exact ⟨d, hd, hl⟩
  have hq' := List.all_eq_true.mp (List.all_eq_true.mp hc _ hw)
  have ho : lits.lookup x = some (some v.toNat) := by
    cases hlk : lits.lookup x with
    | none => simp [hlk] at hn
    | some o => simp only [hlk, Option.join_some] at hn; rw [hn]
  obtain ⟨b, hb, rfl⟩ := lookup_mem ho
  have := hq' b hb
  simp only [hn] at this
  simpa using this

end Spike.Lib.LowerNode

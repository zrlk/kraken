import Spike.Lib.Src.AbortImm2
import Spike.Lib.LowerEnvImm1

/-!
**On a call-free `Accepted1` body the lowering's own walk is the closed
form's** (`lowerEnvs2` is `lowerEnvs1`), and on one-word environments its
symbolic environment `ofEnv2` is `ofEnv`: so a premise over the walk at
`ofEnv2` (what `walk_imms2Of` gives) is the closed form's premise at
`ofEnv` (what `body1_seg` takes).

- `grp_scalar`, `group_scalar1`: a scalar one-word type groups its word as
  one placement;
- `Grp1 env`: every binding of `env` groups its words one placement each;
  `grp1_nil`, `grp1_unit`;
- `lowerEnvs2_eq1`: where `lower1` succeeds, `lowerEnvs2 lc` is `lowerEnvs1`
  (any lowering context `lc`: the call-free fragment reads none of it);
- `grp1_walk1`: `Grp1` holds at each point of the closed form's walk;
- `walk1_of_walk2`: the premise over `lowerEnvs2` at `ofEnv2` gives the one
  over `lowerEnvs1` at `ofEnv`.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm
open Scc.IR
open Scc.Lower (Env lowerExpr)
open Scc.Lower.Inv (lower1 atomV Res1 scalar1 regName lowerExpr_lower1)
open Spike.Lib.Form (SEnv WordPl)

/-! ## Scalar one-word types group as one placement -/

/-- **An all-scalar layout groups each word as one placement.** -/
theorem grp_scalar : ∀ (t : Ty) (s r : Nat) (sl : List (Bool × Nat)), Scc.Obj.slots t s r = some sl →
    (∀ x ∈ sl, x.1 = false) → ∀ (os rest : List Operand), os.length = sl.length →
      Spike.Lib.Form.grp t (os ++ rest) = some (os.map .one, rest) := by
  intro t
  induction t with
  | prod a b iha ihb =>
    intro s r sl hs hf os rest hl
    simp only [Scc.Obj.slots] at hs
    cases ha : Scc.Obj.slots a s r with
    | none => simp [ha] at hs
    | some la =>
      cases hb : Scc.Obj.slots b (s + la.countP (!·.1)) (r + la.countP (·.1)) with
      | none => simp [ha, hb] at hs
      | some lb =>
        simp only [ha, hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hs
        subst hs
        simp only [List.length_append] at hl
        have h1 := iha s r la ha (fun x hx => hf x (List.mem_append_left _ hx)) (os.take la.length)
          (os.drop la.length ++ rest) (by simp; omega)
        have h2 := ihb _ _ lb hb (fun x hx => hf x (List.mem_append_right _ hx)) (os.drop la.length) rest
          (by simp; omega)
        have : os ++ rest = os.take la.length ++ (os.drop la.length ++ rest) := by
          rw [← List.append_assoc, List.take_append_drop]
        rw [this]
        simp only [Spike.Lib.Form.grp, h1, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          ← List.map_append, List.take_append_drop]
  | refine t _ ih => intro s r sl hs; exact ih s r sl hs
  | iall t ih => intro s r sl hs; exact ih s r sl hs
  | mu t ih => intro s r sl hs; exact ih s r sl hs
  | iex b ih =>
    intro s r sl hs hf os rest hl
    simp only [Scc.Obj.slots] at hs
    split at hs
    · simp at hs
    · rename_i hc
      simp only [Spike.Lib.Form.grp, hc]
      exact ih s r sl hs hf os rest hl
  | tex k b ih =>
    intro s r sl hs hf os rest hl
    simp only [Scc.Obj.slots] at hs
    split at hs
    · simp at hs
    · rename_i hc
      simp only [Spike.Lib.Form.grp, hc]
      exact ih s r sl hs hf os rest hl
  | _ =>
    intro s r sl hs hf os rest hl
    simp only [Scc.Obj.slots, Option.some.injEq, reduceCtorEq] at hs
    all_goals subst hs
    all_goals rcases os with _ | ⟨o, _ | ⟨_, _⟩⟩
    all_goals simp_all [Spike.Lib.Form.grp]

/-- **A scalar one-word type groups its word as one placement.** -/
theorem group_scalar1 {t : Ty} (ht : scalar1 t = true) (w : Operand) :
    Spike.Lib.Form.group t [w] = some [.one w] := by
  simp only [scalar1, Scc.Obj.traceMask, beq_iff_eq] at ht
  cases hs : Scc.Obj.slots t 0 0 with
  | none => simp [hs] at ht
  | some sl =>
    rw [hs] at ht
    rcases sl with _ | ⟨⟨c, k⟩, _ | _⟩ <;> simp at ht
    subst ht
    have := grp_scalar t 0 0 _ hs (by simp) [w] [] rfl
    simp only [List.append_nil] at this
    simp [Spike.Lib.Form.group, this]

/-! ## One-placement environments -/

/-- **Every binding of `env` groups its words one placement each.** -/
def Grp1 (env : Env) : Prop := ∀ b ∈ env, Spike.Lib.Form.group b.2.1 b.2.2 = some (b.2.2.map .one)

theorem grp1_nil : Grp1 [] := fun _ h => nomatch h

theorem grp1_cons {env : Env} (h : Grp1 env) {x : String} {t : Ty} {ws : List Operand}
    (hb : Spike.Lib.Form.group t ws = some (ws.map .one)) : Grp1 ((x, t, ws) :: env) := by
  intro b hb'
  rcases List.mem_cons.1 hb' with rfl | hb'
  · exact hb
  · exact h b hb'

/-- A `unit` argument with no words. -/
theorem grp1_unit (x : String) : Grp1 [(x, .unit, [])] :=
  grp1_cons grp1_nil (by simp [Spike.Lib.Form.group, Spike.Lib.Form.grp])

/-! ## The two walks -/

/-- **Where the closed form succeeds the lowering's walk is its walk**: same
points, environments and counters. -/
theorem lowerEnvs2_eq1 (lc : Scc.Lower.Ctx) :
    ∀ (e : Expr) (env : Env) (n : Nat) (r : Res1), lower1 env n e = some r →
      lowerEnvs2 lc env n e = lowerEnvs1 env n e := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr
    cases op with
    | atom a =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
          rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases ht : scalar1 t with
        | false => simp [ht] at hr
        | true =>
          cases hr' : lower1 ((x, t, [w]) :: env) n e with
          | none => simp [ht, hr'] at hr
          | some r' =>
            simp only [lowerEnvs2, lowerEnvs1, runB_letStep_scalar ha ht, ha]
            rw [ih _ n r' hr']
    | add a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [lowerEnvs2, lowerEnvs1, runB_letStep_add ha hb]
            rw [ih _ _ r' hr']
    | sub a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            simp only [lowerEnvs2, lowerEnvs1, runB_letStep_sub ha hb]
            rw [ih _ _ r' hr']
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n r hr
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
        rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
      cases hb : atomV env b with
      | none => simp [hb] at hr
      | some u =>
        obtain ⟨t', us⟩ := u
        rw [hb] at hr
        obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
          rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hy : lower1 env (n + 2) yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy, hn] at hr
          | some rn =>
            have hly : runB (lowerExpr lc env yes) (n + 2) = some ((), ry.next) :=
              runB_eq (lowerExpr_lower1 lc yes env { next := n + 2 } "entry" #[] ry rfl hy)
            simp only [lowerEnvs2, lowerEnvs1, runB_ifStep ha hb, hly]
            rw [ihy env _ ry hy, ihn env _ rn hn, ← lower1_next yes env (n + 2) ry hy]
  | ret a => intro _ _ _ _; simp [lowerEnvs2, lowerEnvs1]
  | _ => intro env n r hr; simp [lower1] at hr

/-- **`Grp1` holds at each point of the closed form's walk.** -/
theorem grp1_walk1 :
    ∀ (e : Expr) (env : Env) (n : Nat) (r : Res1), lower1 env n e = some r → Grp1 env →
      ∀ q ∈ lowerEnvs1 env n e, Grp1 q.2.1 := by
  intro e
  induction e with
  | let_ x op e ih =>
    intro env n r hr hg
    cases op with
    | atom a =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨w, rfl⟩ : ∃ w, ws = [w] := by
          rcases ws with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases ht : scalar1 t with
        | false => simp [ht] at hr
        | true =>
          cases hr' : lower1 ((x, t, [w]) :: env) n e with
          | none => simp [ht, hr'] at hr
          | some r' =>
            intro q hq
            simp only [lowerEnvs1, ha, List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hg
            · exact ih _ n r' hr' (grp1_cons hg (group_scalar1 ht w)) q hq
    | add a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            intro q hq
            simp only [lowerEnvs1, List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hg
            · exact ih _ _ r' hr' (grp1_cons hg rfl) q hq
    | sub a b =>
      simp only [lower1] at hr
      cases ha : atomV env a with
      | none => simp [ha] at hr
      | some v =>
        obtain ⟨t, ws⟩ := v
        rw [ha] at hr
        obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
          rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hb : atomV env b with
        | none => simp [hb] at hr
        | some u =>
          obtain ⟨t', us⟩ := u
          rw [hb] at hr
          obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
            rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
          cases hr' : lower1 ((x, .int, [.reg (regName x n)]) :: env) (n + 1) e with
          | none => simp [hr'] at hr
          | some r' =>
            intro q hq
            simp only [lowerEnvs1, List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hg
            · exact ih _ _ r' hr' (grp1_cons hg rfl) q hq
    | _ => simp [lower1] at hr
  | ifeq a b yes no ihy ihn =>
    intro env n r hr hg
    simp only [lower1] at hr
    cases ha : atomV env a with
    | none => simp [ha] at hr
    | some v =>
      obtain ⟨t, ws⟩ := v
      rw [ha] at hr
      obtain ⟨p, rfl⟩ : ∃ p, ws = [p] := by
        rcases ws with _ | ⟨p, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
      cases hb : atomV env b with
      | none => simp [hb] at hr
      | some u =>
        obtain ⟨t', us⟩ := u
        rw [hb] at hr
        obtain ⟨q, rfl⟩ : ∃ q, us = [q] := by
          rcases us with _ | ⟨q, _ | ⟨_, _⟩⟩ <;> first | exact ⟨_, rfl⟩ | simp at hr
        cases hy : lower1 env (n + 2) yes with
        | none => simp [hy] at hr
        | some ry =>
          cases hn : lower1 env ry.next no with
          | none => simp [hy, hn] at hr
          | some rn =>
            intro q hq
            simp only [lowerEnvs1, List.mem_cons, List.mem_append] at hq
            rcases hq with rfl | hq | hq
            · exact hg
            · exact ihy env _ ry hy hg q hq
            · rw [← lower1_next yes env (n + 2) ry hy] at hq
              exact ihn env _ rn hn hg q hq
  | ret a =>
    intro env n r _ hg q hq
    simp only [lowerEnvs1, List.mem_cons, List.not_mem_nil, or_false] at hq
    subst hq
    exact hg
  | _ => intro env n r hr; simp [lower1] at hr

/-- **The walk premise at `ofEnv2` is the closed form's at `ofEnv`**: where
`lower1` succeeds from a one-placement environment. -/
theorem walk1_of_walk2 (lc : Scc.Lower.Ctx) {e : Expr} {env : Env} {n : Nat} {r : Res1}
    (hr : lower1 env n e = some r) (hg : Grp1 env) {P : Expr → SEnv → Prop}
    (h : ∀ q ∈ lowerEnvs2 lc env n e, P q.1 (ofEnv2 q.2.1)) :
    ∀ q ∈ lowerEnvs1 env n e, P q.1 (ofEnv q.2.1) := by
  intro q hq
  have h' := h q (by rw [lowerEnvs2_eq1 lc e env n r hr]; exact hq)
  rwa [ofEnv2_eq_ofEnv (grp1_walk1 e env n r hr hg q hq)] at h'

end Spike.Lib.LowerNode

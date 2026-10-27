/-
# UTstep — parametricity of the core thread step in its continuations (UnElab T2)

The UnElab machine (`USem.ustep`) runs the core `TermRun.tstep` on *sentinel* terms: a head form whose
continuation slots hold the placeholders `S0`/`S1`.  This module proves that this is faithful: for every
head form `h` other than a call, `callc`, `ret` or `tail` (`IsHead h`), the step of `mapHead f h` (the
same head, its continuations replaced by `f` of them) is the step of `h` with `f` applied to the result
term, and the stack is never read or changed (`tstep_head_subst`).  `tstep_let_cont` is the `let` case
(any non-call operation).  Nothing here mentions UnElab: these are facts about `tstep`.
-/
import WeakCore.TermRun

set_option linter.unusedSimpArgs false

namespace UnElab
open CoreLang CoreTerm TermRun
open WeakMem (Memory Ts)

/-- The sentinel continuations. -/
def S0 : Expr := .ret (.var "#0")
def S1 : Expr := .ret (.var "#1")

/-- `f` applied to the continuation slots of a head form; `ret`/`tail` (no slots) unchanged. -/
def mapHead (f : Expr → Expr) : Expr → Expr
  | .let_ x op e => .let_ x op (f e)
  | .split a x y e => .split a x y (f e)
  | .unpack a i x e => .unpack a i x (f e)
  | .unpackT a al x e => .unpackT a al x (f e)
  | .region a r p t e => .region a r p t (f e)
  | .openPub a r p c e => .openPub a r p c (f e)
  | .case a x e₁ y e₂ => .case a x (f e₁) y (f e₂)
  | .ifnull a e₁ x e₂ => .ifnull a (f e₁) x (f e₂)
  | .parity a k ev od => .parity a k (f ev) (f od)
  | .ifeq a b yes no => .ifeq a b (f yes) (f no)
  | .cas acq rel w e v t ok fail => .cas acq rel w e v t (f ok) (f fail)
  | .casp acq rel w e0 e1 v0 v1 t ok fail => .casp acq rel w e0 e1 v0 v1 t (f ok) (f fail)
  | .ret a => .ret a
  | .tail g is a ts => .tail g is a ts

/-- An operation that is not a call: its `let` is an ordinary thread step. -/
def NotCall : Op → Prop
  | .call .. => False
  | .callc .. => False
  | _ => True

/-- A head form whose step `tstep` takes without looking at its continuations or the stack. -/
def IsHead : Expr → Prop
  | .let_ _ op _ => NotCall op
  | .ret _ => False
  | .tail .. => False
  | _ => True

/-- Re-attach a continuation-image and a stack to a step result. -/
def reTerm (f : Expr → Expr) (s : List Frame) (r : Memory × List Ts × TTh) : Memory × List Ts × TTh :=
  (r.1, r.2.1, { r.2.2 with term := f r.2.2.term, stack := s })

/-- The `let` arm of `tstep` for a non-call operation. -/
theorem tstep_let {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {op : Op} {e : Expr}
    (hop : NotCall op) (ht : th.term = .let_ x op e) :
    tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) op).map fun (s', t, ws) =>
      (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
  cases op <;> first | exact absurd hop id | (unfold tstep; rw [ht])


theorem tstep_split_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a x y e :
    tstep g mem pairs { th with term := .split a x y (f e), stack := s } =
      (tstep g mem pairs { th with term := .split a x y e, stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_unpack_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a i x e :
    tstep g mem pairs { th with term := .unpack a i x (f e), stack := s } =
      (tstep g mem pairs { th with term := .unpack a i x e, stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_unpackT_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a al x e :
    tstep g mem pairs { th with term := .unpackT a al x (f e), stack := s } =
      (tstep g mem pairs { th with term := .unpackT a al x e, stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_region_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a r p t e :
    tstep g mem pairs { th with term := .region a r p t (f e), stack := s } =
      (tstep g mem pairs { th with term := .region a r p t e, stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_openPub_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a r p c e :
    tstep g mem pairs { th with term := .openPub a r p c (f e), stack := s } =
      (tstep g mem pairs { th with term := .openPub a r p c e, stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_case_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a x y e e' :
    tstep g mem pairs { th with term := .case a x (f e) y (f e'), stack := s } =
      (tstep g mem pairs { th with term := .case a x e y e', stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  split
  · rw [List.map_flatMap]
    congr 1
    funext r
    split <;> simp [reTerm, stOf, withS]
  · rfl

theorem tstep_ifnull_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a x e e' :
    tstep g mem pairs { th with term := .ifnull a (f e) x (f e'), stack := s } =
      (tstep g mem pairs { th with term := .ifnull a e x e', stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_parity_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a k e e' :
    tstep g mem pairs { th with term := .parity a k (f e) (f e'), stack := s } =
      (tstep g mem pairs { th with term := .parity a k e e', stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_ifeq_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    a b e e' :
    tstep g mem pairs { th with term := .ifeq a b (f e) (f e'), stack := s } =
      (tstep g mem pairs { th with term := .ifeq a b e e', stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_cas_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    acq rel w v0 v t e e' :
    tstep g mem pairs { th with term := .cas acq rel w v0 v t (f e) (f e'), stack := s } =
      (tstep g mem pairs { th with term := .cas acq rel w v0 v t e e', stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

theorem tstep_casp_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (th : TTh) (s : List Frame)
    acq rel w x0 x1 v0 v1 t e e' :
    tstep g mem pairs { th with term := .casp acq rel w x0 x1 v0 v1 t (f e) (f e'), stack := s } =
      (tstep g mem pairs { th with term := .casp acq rel w x0 x1 v0 v1 t e e', stack := [] }).map (reTerm f s) := by
  simp only [tstep]
  repeat' split
  all_goals simp [reTerm, stOf, withS]
  all_goals (intro _ _ _; split <;> simp)

/-- **Parametricity of `tstep` in the continuations** (`tstep_head_subst`): for a
head form `h` (`IsHead`: a non-call `let`, or one of the 11 branching/destructuring heads), stepping `mapHead f h`
with any stack `s` is stepping `h` with the empty stack, then applying `f` to the result term and putting `s`
back.  So the result term is always one of `h`'s continuations, nothing else in the outcome depends on them, and
the stack is neither read nor changed. -/
theorem tstep_head_subst {g : G} {mem : Memory} {pairs : List Ts} (f : Expr → Expr) (h : Expr) (hh : IsHead h)
    (th : TTh) (s : List Frame) :
    tstep g mem pairs { th with term := mapHead f h, stack := s } =
      (tstep g mem pairs { th with term := h, stack := [] }).map (reTerm f s) := by
  cases h with
  | let_ x op e =>
    rw [tstep_let hh rfl, tstep_let hh rfl, List.map_map]
    rfl
  | split => exact tstep_split_subst f th s _ _ _ _
  | unpack => exact tstep_unpack_subst f th s _ _ _ _
  | unpackT => exact tstep_unpackT_subst f th s _ _ _ _
  | region => exact tstep_region_subst f th s _ _ _ _ _
  | openPub => exact tstep_openPub_subst f th s _ _ _ _ _
  | case => exact tstep_case_subst f th s _ _ _ _ _
  | ifnull => exact tstep_ifnull_subst f th s _ _ _ _
  | parity => exact tstep_parity_subst f th s _ _ _ _
  | ifeq => exact tstep_ifeq_subst f th s _ _ _ _
  | cas => exact tstep_cas_subst f th s _ _ _ _ _ _ _ _
  | casp => exact tstep_casp_subst f th s _ _ _ _ _ _ _ _ _ _
  | ret a => exact absurd hh id
  | tail _ _ _ _ => exact absurd hh id

/-- **`tstep_let_cont`**: for an operation that is not a call, the step of
`let x = op in e` depends on `e` only as the new term, and leaves the stack alone. -/
theorem tstep_let_cont {g : G} {mem : Memory} {pairs : List Ts} {x : String} {op : Op} (hop : NotCall op)
    (e e' : Expr) (th : TTh) (s : List Frame) :
    tstep g mem pairs { th with term := .let_ x op e, stack := s } =
      (tstep g mem pairs { th with term := .let_ x op e', stack := [] }).map (reTerm (fun _ => e) s) :=
  tstep_head_subst (fun _ => e) (.let_ x op e') hop th s

/-- The names a head form binds in the environment. -/
def binders : Expr → List String
  | .let_ x _ _ => [x]
  | .split _ x y _ => [x, y]
  | .unpack _ _ x _ => [x]
  | .unpackT _ _ x _ => [x]
  | .region _ _ p t _ => [p, t]
  | .openPub _ _ p c _ => [p, c]
  | .case _ x _ y _ => [x, y]
  | .ifnull _ _ x _ => [x]
  | .cas _ _ _ _ _ t _ _ => [t]
  | .casp _ _ _ _ _ _ _ t _ _ => [t]
  | _ => []

set_option hygiene false in
/-- Close `y.1 ∈ binders h ∨ y ∈ th.env` from `hy : y ∈ b₁ :: … :: th.env` (at most two new bindings). -/
local macro "envfin" : tactic => `(tactic| (
  first
    | exact Or.inr hy
    | (rcases List.mem_cons.mp hy with rfl | hy
       · exact Or.inl (by simp [binders])
       first
         | exact Or.inr hy
         | (rcases List.mem_cons.mp hy with rfl | hy
            · exact Or.inl (by simp [binders])
            exact Or.inr hy))))

/-- A head step only adds bindings of the head's own binders to the environment (used by the hygiene
invariant). -/
theorem tstep_head_env {g : G} {mem : Memory} {pairs : List Ts} (h : Expr) (hh : IsHead h) (th : TTh)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs { th with term := h, stack := [] }) :
    ∀ y ∈ r.2.2.env, y.1 ∈ binders h ∨ y ∈ th.env := by
  cases h with
  | let_ x op e =>
    rw [tstep_let hh rfl] at hr
    simp only [List.mem_map] at hr
    obtain ⟨⟨s', t, ws⟩, _, rfl⟩ := hr
    intro y hy
    simp only [withS, List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact Or.inl (by simp [binders])
    · exact Or.inr hy
  | ret a => exact absurd hh id
  | tail _ _ _ _ => exact absurd hh id
  | _ =>
    simp only [tstep] at hr
    repeat' split at hr
    all_goals simp [withS] at hr
    all_goals intro y hy
    all_goals first
      | (subst hr; simp only [withS] at hy; envfin)
      | (obtain ⟨_, j, _, _, _, _, _, rfl⟩ := hr
         simp only [List.mem_cons] at hy
         rcases hy with rfl | hy
         · left; split <;> simp [binders]
         · exact Or.inr hy)
      | (obtain ⟨_, _, _, rfl⟩ := hr
         simp only [withS] at hy
         split at hy <;> (simp only at hy; envfin))
      | (obtain ⟨_, _, _, _, rfl⟩ := hr
         simp only [withS] at hy
         split at hy <;> (simp only at hy; envfin))

end UnElab

#print axioms UnElab.tstep_let
#print axioms UnElab.tstep_head_subst
#print axioms UnElab.tstep_let_cont
#print axioms UnElab.tstep_head_env

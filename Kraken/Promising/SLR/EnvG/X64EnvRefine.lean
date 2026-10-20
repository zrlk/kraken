/-
Environment refinement and the value-restricted purity environment, x64.
Program-independent.

- `Safely.refine`: a `Safely` judgment of `instrStepEnv E₁` is one of
  `instrStepEnv E₂` when `E₂` permits what `E₁` does and every `E₂` outcome
  is an `E₁` outcome along a state map `f` (more permissions needed, fewer
  outcomes); per instruction `instrStepEnv_refine`, per event tree
  `Effects.AllEnv.refine`.
- `relInvX S G`: the purity environment with the value invariant's
  permissions (`inv S G` and `relPureQ Arch.tso ⊥` both permit the access)
  and load and RMW answers in `G`; its simp lemmas and `Skips`.
  `Safely.relInvX_inv`: a judgment in it is one in `inv S G` (a `ThreadSpec`
  of the invariant link `InvLinkX64`); `Safely.relInvX_top`: at `G = ⊤` it
  is a purity judgment in `(relPureQ Arch.tso ⊥).within S`.
- `RelPureSpecQX.HoldsV G sp`: `RelPureSpecQX.Holds` with the judgment in
  `relInvX sp.S G`.
-/
import Kraken.Promising.SLR.EnvG.RelPureEnvX64

namespace Kraken.Promising.X64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64

/-! ## Environment refinement -/

section Refine

variable {E₁ E₂ : SharedEnv} (f : E₁.State → E₂.State)
  (hok : ∀ a g, E₁.ok a g → E₂.ok a (f g))
  (hst : ∀ a g r g₂, E₂.step a (f g) r g₂ → ∃ g', g₂ = f g' ∧ E₁.step a g r g')

include hok hst in
/-- **A judgment of `E₁` is one of `E₂`** when `E₂` permits what `E₁` does
and every `E₂` outcome is an `E₁` outcome (along `f`). -/
theorem Effects.AllEnv.refine {post₁ : MachineState → E₁.State → Prop} {post₂ : MachineState → E₂.State → Prop}
    (hp : ∀ s g, post₁ s g → post₂ s (f g)) (e : Effects) :
    ∀ g, e.AllEnv E₁ g post₁ → e.AllEnv E₂ (f g) post₂ := by
  have pl : ∀ (addr : BitVec 64) n g (k₁ : List (BitVec 64) → E₁.State → Prop) (k₂ : List (BitVec 64) → E₂.State → Prop),
      (∀ vs g, k₁ vs g → k₂ vs (f g)) → E₁.LoadPieces addr n g k₁ → E₂.LoadPieces addr n (f g) k₂ := by
    intro addr n
    induction n generalizing addr with
    | zero => exact fun g k₁ k₂ hk h => hk _ _ h
    | succ n ih =>
      refine fun g k₁ k₂ hk h => ⟨hok _ _ h.1, fun v g₂ hs => ?_⟩
      obtain ⟨g', rfl, hs'⟩ := hst _ _ _ _ hs
      exact ih _ g' _ _ (fun vs g'' => hk _ g'') (h.2 v g' hs')
  have ps : ∀ (ps : List (BitVec 64)) (addr : BitVec 64) g (k₁ : E₁.State → Prop) (k₂ : E₂.State → Prop),
      (∀ g, k₁ g → k₂ (f g)) → E₁.StorePieces addr ps g k₁ → E₂.StorePieces addr ps (f g) k₂ := by
    intro ps
    induction ps with
    | nil => exact fun addr g k₁ k₂ hk h => hk _ h
    | cons p ps ih =>
      refine fun addr g k₁ k₂ hk h => ⟨hok _ _ h.1, fun b g₂ hs => ?_⟩
      obtain ⟨g', rfl, hs'⟩ := hst _ _ _ _ hs
      exact ih _ g' _ _ hk (h.2 b g' hs')
  have one : ∀ {a : SharedAccess} {g : E₁.State} {K₁ : a.Ret → E₁.State → Prop} {K₂ : a.Ret → E₂.State → Prop},
      (∀ r g, K₁ r g → K₂ r (f g)) → (E₁.ok a g ∧ ∀ r g', E₁.step a g r g' → K₁ r g') →
      (E₂.ok a (f g) ∧ ∀ r g₂, E₂.step a (f g) r g₂ → K₂ r g₂) := by
    intro a g K₁ K₂ hk h
    refine ⟨hok _ _ h.1, fun r g₂ hs => ?_⟩
    obtain ⟨g', rfl, hs'⟩ := hst _ _ _ _ hs
    exact hk _ _ (h.2 r g' hs')
  induction e with
  | done a => exact fun g h => hp _ _ h
  | unimplemented => exact fun _ h => h
  | gp_unaligned => exact fun _ h => h
  | nonmem_load dmem addr w ret ih => exact fun g h => one (fun v g' h => ih _ _ g' h) h
  | nonmem_store dmem addr v ret ih => exact fun g h => one (fun _ g' h => ih _ g' h) h
  | undefined ret ih => exact fun g h v => ih v g (h v)
  | require_read_access _ _ ok ih => exact fun g h => ih () g h
  | require_write_access _ _ ok ih => exact fun g h => ih () g h
  | require_exec_access _ ok ih => exact fun g h => ih () g h
  | sync_load k xcl dmem addr w ret ih => exact fun g h => one (fun v g' h => ih _ _ g' h) h
  | sync_store k xcl dmem addr v ret ih => exact fun g h => one (fun b g' h => ih _ _ g' h) h
  | rmw k dmem addr w op ret ih => exact fun g h => one (fun v g' h => ih _ _ g' h) h
  | fence k ok ih =>
    refine fun g h => ⟨hok _ _ h.1, fun g₂ hs => ?_⟩
    obtain ⟨g', rfl, hs'⟩ := hst _ _ _ _ hs
    exact ih () g' (h.2 g' hs')
  | require_read_access_avx _ _ _ ok ih => exact fun g h => ih () g h
  | require_write_access_avx _ _ _ ok ih => exact fun g h => ih () g h
  | nonmem_load_avx atomic dmem addr w ret ih =>
    cases atomic
    · exact fun g h => pl _ _ g _ _ (fun vs g' => ih _ _ g') h
    · exact fun g h => one (fun v g' h => ih _ _ g' h) h
  | nonmem_store_avx atomic dmem addr v ret ih =>
    cases atomic
    · exact fun g h => ps _ _ g _ _ (fun g' => ih _ g') h
    · exact fun g h => one (fun _ g' h => ih _ g' h) h
  | rmw16 k dmem addr op ret ih => exact fun g h => one (fun v g' h => ih _ _ g' h) h

include hok hst in
/-- An instruction step of `E₁` is one of `E₂`. -/
theorem instrStepEnv_refine {e : Kraken.Executable Directive} {st : MachineState × E₁.State}
    {R : MachineState × E₁.State → Prop} (h : e.instrStepEnv E₁ st R) :
    e.instrStepEnv E₂ (st.1, f st.2) (fun y => ∃ x', y = (x'.1, f x'.2) ∧ R x') := by
  obtain ⟨d, z, rest, hcode, hstep⟩ := h
  refine ⟨d, z, rest, hcode, ?_⟩
  rcases hstep with h | h
  · refine .inl (Effects.AllEnv.refine f hok hst ?_ _ _ h)
    intro s g h; exact ⟨_, rfl, h⟩
  · refine .inr (Effects.AllEnv.refine f hok hst ?_ _ _ h)
    intro s g h; exact ⟨_, rfl, h⟩

include hok hst in
/-- **`Safely` along an environment refinement.** -/
theorem Safely.refine {e : Kraken.Executable Directive} {post : MachineState × E₁.State → Prop}
    {x : MachineState} {g : E₁.State} (h : Safely (e.instrStepEnv E₁) post (x, g)) :
    Safely (e.instrStepEnv E₂) (fun y => ∃ g', y.2 = f g' ∧ post (y.1, g')) (x, f g) := by
  have hs := h.sim (fun (x : MachineState × E₁.State) (y : MachineState × E₂.State) => y = (x.1, f x.2))
    (fun x y R hxy hT => by subst hxy; exact instrStepEnv_refine f hok hst hT)
    (y := (x, f g)) rfl
  exact hs.mono fun y ⟨x', hy, hx⟩ => ⟨x'.2, by rw [hy], by rw [hy]; exact hx⟩

end Refine

/-! ## The value-restricted purity environment -/

/-- **The purity environment with the value invariant's permissions**:
an access is permitted when `inv S G` and `relPureQ Arch.tso ⊥` both permit
it (a location of `S`; a written value in `G`; a release write); a load or an
RMW answers a value in `G`. -/
def relInvX (S : SharedEnv.Layout) (G : Loc → Val → Prop) : SharedEnv where
  State := Unit
  ok a g := (SharedEnv.inv S G).ok a g ∧ (SharedEnv.relPureQ Arch.tso fun _ _ => False).ok a g
  step a _ r _ := match a, r with
    | .load _ _ addr n, v => G ⟨addr, n⟩ v
    | .rmw _ addr n _, old => G ⟨addr, n⟩ old
    | _, _ => True

instance (S : SharedEnv.Layout) (G : Loc → Val → Prop) : (relInvX S G).Skips :=
  ⟨fun _ _ => ⟨⟨trivial, trivial⟩, fun _ _ => rfl⟩⟩

section Simp

variable {S : SharedEnv.Layout} {G : Loc → Val → Prop} {g g' : (relInvX S G).State}

@[simp] theorem relInvX_ok (a : SharedAccess) :
    (relInvX S G).ok a g ↔ (SharedEnv.inv S G).ok a () ∧ (SharedEnv.relPureQ Arch.tso fun _ _ => False).ok a () :=
  Iff.rfl

@[simp] theorem relInvX_step_load {k : LoadKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} :
    (relInvX S G).step (.load k xcl addr n) g v g' ↔ G ⟨addr, n⟩ v := Iff.rfl

@[simp] theorem relInvX_step_store {k : StoreKind} {xcl : Bool} {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool} :
    (relInvX S G).step (.store k xcl addr n v) g b g' ↔ True := Iff.rfl

@[simp] theorem relInvX_step_rmw {k : RmwKind} {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val} :
    (relInvX S G).step (.rmw k addr n op) g old g' ↔ G ⟨addr, n⟩ old := Iff.rfl

end Simp

/-- **A judgment in `relInvX S G` is one in `inv S G`** (fewer permissions
needed; `inv`'s outcomes are `relInvX`'s). -/
theorem Safely.relInvX_inv {S : SharedEnv.Layout} {G : Loc → Val → Prop} {e : Kraken.Executable Directive}
    {post : MachineState × Unit → Prop} {x : MachineState}
    (h : Safely (e.instrStepEnv (relInvX S G)) post (x, ())) :
    Safely (e.instrStepEnv (SharedEnv.inv S G)) post (x, ()) :=
  (Safely.refine (E₁ := relInvX S G) (E₂ := SharedEnv.inv S G) id (fun _ _ h => h.1)
    (fun a _ r _ h => ⟨(), rfl, by cases a <;> first | exact h | trivial⟩) h).mono fun _ ⟨_, _, h⟩ => h

/-- **At `G = ⊤`, a judgment in `relInvX S ⊤` is a purity judgment** in
`(relPureQ Arch.tso ⊥).within S`. -/
theorem Safely.relInvX_top {S : SharedEnv.Layout} {e : Kraken.Executable Directive}
    {post : MachineState × Unit → Prop} {x : MachineState}
    (h : Safely (e.instrStepEnv (relInvX S fun _ _ => True)) post (x, ())) :
    Safely (e.instrStepEnv ((SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)) post (x, ()) :=
  (Safely.refine (E₁ := relInvX S fun _ _ => True) (E₂ := (SharedEnv.relPureQ Arch.tso fun _ _ => False).within S)
    id (fun a _ h => by
      cases a <;> first | exact ⟨h.2, h.1⟩ | exact ⟨h.2, h.1.1⟩ | exact ⟨h.2, trivial⟩)
    (fun a _ r _ _ => ⟨(), rfl, by cases a <;> trivial⟩) h).mono fun _ ⟨_, _, h⟩ => h

/-- The purity specification holds at a thread state with its judgment in
`relInvX sp.S G` (`RelPureSpecQX.Holds` under the value invariant). -/
def RelPureSpecQX.HoldsV {Q : Loc → Val → Prop} (G : Loc → Val → Prop)
    (sp : RelPureSpecQX Arch.tso Q) (st : State) : Prop :=
  st.exe = sp.e ∧ st.endPc = sp.endPc ∧ st.decls = {} ∧ Split sp.S st.st.1.dmem ∧
    Safely (sp.e.instrStepEnv (relInvX sp.S G)) sp.post (st.st, ())

end Kraken.Promising.X64.EnvG

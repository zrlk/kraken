/-
**Fuel-free reachability along `SuccKind` steps, and the K world's
vocabulary**. ISA-neutral.

- `ReachableK` and `ReachableK.of_reachable` (moved here verbatim from
  `LiveBridge.lean`, which re-exports them, so that the Stage 2 helper
  lemmas of `ReleasePrefix.lean` onwards can be stated over it).
  `ReachableK.of_reachableSem` stays in `LiveBridge.lean`.
- `ReachableK.{trans, single, inv}`: its basic closure facts.
- The **K world**, a fuel-phantom copy of the executable machine's
  vocabulary that the `#chaink_clone` modules (`ChainK/Clone.lean`) are
  elaborated against: `KSet`, `succsK` (the `SuccKind` successors, shaped
  like `succs`), `succsK_cases`, `ReachableKF A fuel` (an `abbrev` for
  `ReachableK A`) with `refl`, `step`, `trans`, `single`, `inv` in the shapes of
  `Reachable`'s (`Machine.lean`, `Rel.lean`), and `Config.LiveK` (fuel-free)
  with the phantom-fuel `Config.LiveKF`. A cloned statement over
  `ReachableKF A fuel` is, by unfolding, the fuel-free statement over
  `ReachableK A`.
-/
import Kraken.Promising.PromiseSafe

namespace Kraken.Promising.Live.Bridge

open Kraken.Promising

variable {I : ISA}

/-- Reachability along `SuccKind` steps: instruction steps of any thread
(no certification check) and promises of `CertWrite`s. Fuel-free; contains
both machines' reachability (`of_reachable`, `of_reachableSem`). -/
inductive ReachableK (A : Arch) : Config I → Config I → Prop
  | refl (c : Config I) : ReachableK A c c
  | step {c c' c'' : Config I} : SuccKind A c c' → ReachableK A c' c'' → ReachableK A c c''

/-- **The executable machine is inside `ReachableK`** (`succs_cases`). -/
theorem ReachableK.of_reachable [I.LawfulState] {A : Arch} {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') : ReachableK A c c' := by
  induction h with
  | refl c => exact .refl c
  | step hs _ ih => exact .step (succs_cases hs) ih

theorem ReachableK.trans {A : Arch} {a b c : Config I} (h₁ : ReachableK A a b) (h₂ : ReachableK A b c) :
    ReachableK A a c := by
  induction h₁ with
  | refl => exact h₂
  | step hs _ ih => exact .step hs (ih h₂)

theorem ReachableK.single {A : Arch} {c c' : Config I} (h : SuccKind A c c') : ReachableK A c c' :=
  .step h (.refl c')

/-- **Invariant induction over `ReachableK`** (the `Reachable.inv` of the K
world). -/
theorem ReachableK.inv {A : Arch} {P : Config I → Prop} (hstep : ∀ c c', P c → SuccKind A c c' → P c')
    {c c' : Config I} (h : ReachableK A c c') (h0 : P c) : P c' := by
  induction h with
  | refl => exact h0
  | step hs _ ih => exact ih (hstep _ _ h0 hs)

end Kraken.Promising.Live.Bridge

namespace Kraken.Promising

open Kraken.Promising.Live.Bridge

variable {I : ISA}

/-! ## The K world (fuel phantom) -/

/-- Sets as predicates, for `c' ∈ (succsK A c fuel).1`. -/
def KSet (α : Type) := α → Prop

instance {α : Type} : Membership α (KSet α) := ⟨fun s a => s a⟩

/-- The `SuccKind` successors, shaped like `succs` (`fuel` is a phantom; no
bound hit, no faults). -/
def succsK (A : Arch) (c : Config I) (_fuel : Nat) : KSet (Config I) × Bool × List String :=
  (fun c' => SuccKind A c c', false, [])

/-- The `succs_cases` of the K world (the identity; stated on `SuccKind`
without the phantom `fuel`, so that it applies to a `succsK` membership at
any `fuel` by unfolding). -/
theorem succsK_cases {A : Arch} {c c' : Config I} (h : SuccKind A c c') : SuccKind A c c' := h

/-- `Reachable`'s shape over `succsK`: `ReachableK` with a phantom `fuel`. -/
abbrev ReachableKF (A : Arch) (_fuel : Nat) : Config I → Config I → Prop := ReachableK A

theorem ReachableKF.refl {A : Arch} {fuel : Nat} (c : Config I) : ReachableKF A fuel c c :=
  ReachableK.refl c

theorem ReachableKF.step {A : Arch} {fuel : Nat} {c c' c'' : Config I} (h : c' ∈ (succsK A c fuel).1)
    (h' : ReachableKF A fuel c' c'') : ReachableKF A fuel c c'' :=
  ReachableK.step h h'

theorem ReachableKF.trans (A : Arch) (fuel : Nat) {a b c : Config I} (h₁ : ReachableKF A fuel a b)
    (h₂ : ReachableKF A fuel b c) : ReachableKF A fuel a c :=
  ReachableK.trans h₁ h₂

theorem ReachableKF.single (A : Arch) (fuel : Nat) {c c' : Config I} (h : c' ∈ (succsK A c fuel).1) :
    ReachableKF A fuel c c' :=
  ReachableK.single h

theorem ReachableKF.inv {A : Arch} {fuel : Nat} {P : Config I → Prop}
    (hstep : ∀ c c', P c → c' ∈ (succsK A c fuel).1 → P c') {c c' : Config I} (h : ReachableKF A fuel c c')
    (h0 : P c) : P c' :=
  ReachableK.inv hstep h h0

/-- The executable machine is inside the K world, at every `fuel`. -/
theorem ReachableKF.of_reachable [I.LawfulState] {A : Arch} {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') : ReachableKF A fuel c c' :=
  ReachableK.of_reachable h

/-- The executable machine's reachability as `ReachableK` (written at the
chain's call sites of `ReachableK`-stated helpers; the clone maps it to
`ReachableKF.toK`, the identity). -/
theorem Reachable.toK [I.LawfulState] {A : Arch} {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') : ReachableK A c c' :=
  ReachableK.of_reachable h

/-- `Reachable.toK` of the K world: the identity. -/
theorem ReachableKF.toK {A : Arch} {fuel : Nat} {c c' : Config I} (h : ReachableKF A fuel c c') :
    ReachableK A c c' :=
  h

/-- A configuration without threads has no successor. -/
theorem Reachable.eq_of_init_nil {A : Arch} {fuel : Nat} {initMem : List (Loc × Val)} {c : Config I}
    (h : Reachable A fuel (Config.init [] initMem) c) : c = Config.init [] initMem := by
  cases h with
  | refl => rfl
  | step hs _ => simp [succs, succsL, Config.init] at hs

/-- `Reachable.eq_of_init_nil` of the K world. -/
theorem ReachableKF.eq_of_init_nil {A : Arch} {fuel : Nat} {initMem : List (Loc × Val)} {c : Config I}
    (h : ReachableKF A fuel (Config.init [] initMem) c) : c = Config.init [] initMem := by
  cases h with
  | refl => rfl
  | step hs _ =>
    cases hs with
    | instr ht _ _ => simp [Config.init] at ht
    | promise ht _ => simp [Config.init] at ht

/-- `c` is *live along `SuccKind`*: some final configuration is
`ReachableK`-reachable from it (fuel-free). -/
def Config.LiveK (A : Arch) (c : Config I) : Prop :=
  ∃ cf, ReachableK A c cf ∧ cf.final = true

/-- `Config.Live`'s shape in the K world: `Config.LiveK` with a phantom
`fuel`. -/
abbrev Config.LiveKF (A : Arch) (_fuel : Nat) (c : Config I) : Prop := c.LiveK A

/-- A live configuration of the executable machine is `LiveK`. -/
theorem Config.LiveK.of_live [I.LawfulState] {A : Arch} {fuel : Nat} {c : Config I} (h : c.Live A fuel) :
    c.LiveK A :=
  let ⟨cf, hr, hf⟩ := h
  ⟨cf, .of_reachable hr, hf⟩

end Kraken.Promising

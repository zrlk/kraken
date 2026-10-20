/-
Whole-thread environment: **the sibling environment
`EnvGLR` for load-then-release trees** (the load-then-release design's option (b)). ISA-neutral.

On x64 under `Arch.tso` every store is release-kind, so an instruction that
loads and then writes (`incl (m)`, `addl $1,(m)` without `lock`) may fulfil a
prepaid release promise *after* a load. The link of such a tree runs the load
while the release is in flight (`pf = some`), where the actual resource is
the one *after* the release, not the env's virtual `σ.r`. `EnvG`'s load
outcome (`LoadOut`, `Facts.lean`, frozen) adds `ClAt tid σ.r …` to `cl`, which
the link cannot justify then.

`EnvGLR I A tid pl` is `EnvG` with one change: **a load leaves `cl`
unchanged** (`LoadOutLR`; the rest of `LoadOut` verbatim). Everything else
(`ok`, the store, RMW and fence outcomes) is `EnvG`'s, by definition. A
program proof in `EnvGLR` therefore gets the same facts as in `EnvG` except
the clean-erasure conjunct of a load (weaker conclusions, never none). What
a later release write of the same tree needs from the load is exactly this:
its prepay fixed the split's knowledge at `σ.cl`, and after the load the env's
knowledge is still `σ.cl` (`Inflight`'s `cl → P`), so the in-flight link
needs no `ClAt` at the load.

- `LoadOutLR`, `EnvGLR`; `LoadFactsLR` and `step_loadFactsLR`;
- the other step facts at `EnvGLR` (`stepLR_storeFacts`, `stepLR_rmwFacts`,
  `stepLR_fenceFacts`, `stepLR_store_true`), by `EnvG`'s;
- `envGLR_ok_eq`: `EnvGLR`'s `ok` is `EnvG`'s; `loadOut_toLR`: every `EnvG`
  load outcome gives an `EnvGLR` one with the same state but the old `cl`.

Phase-1 limits apply (single release in flight; read-side acquire only; no
release-kind RMW on this route: x64 `lock` RMWs use the `…RC` routes).
-/
import Kraken.Promising.SLR.EnvG.Env

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **A load outcome of `EnvGLR`**: `LoadOut` with `cl` unchanged. -/
def LoadOutLR (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (xcl : Bool) (l : Loc) (v : Val) : Prop :=
  AnchorOk tid σ σ'.snap σ'.g ∧ σ'.r = σ.r ∧ σ'.cl = σ.cl ∧
    ∃ tr cx', (tr, v, cx') ∈ readSuccs A iv0 (envCtx tid σ.vs σ'.snap) k xcl l ∧ σ'.vs = cx'.views ∧
      σ'.seen = seenAfter A k σ σ'.g l tr ∧ σ'.fencedR = false ∧ σ'.fencedW = σ.fencedW

/-- **The load-then-release sibling of `EnvG`**: `EnvG` whose loads leave
`cl` unchanged (`LoadOutLR`). -/
def _root_.Kraken.Promising.SLR.EnvGLR (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := match a with
    | .load .. => True
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v
    | .rmw k addr n op => RmwOk A tid pl σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutLR A tid σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

@[simp] theorem envGLR_ok_load (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : LoadKind) (xcl : Bool)
    (addr : BitVec 64) (n : Nat) : (EnvGLR I A tid pl).ok (.load k xcl addr n) σ := trivial

@[simp] theorem envGLR_ok_fence (A : Arch) (tid : Nat) (pl : Plan) (σ : State I) (k : FenceKind) :
    (EnvGLR I A tid pl).ok (.fence k) σ := trivial

/-- `EnvGLR`'s permissions are `EnvG`'s. -/
theorem envGLR_ok_eq (A : Arch) (tid : Nat) (pl : Plan) (a : SharedAccess) (σ : State I) :
    (EnvGLR I A tid pl).ok a σ = (EnvG I A tid pl).ok a σ := by
  cases a <;> rfl

/-- **What a load of `EnvGLR` exposes**: `LoadFacts` with `cl` unchanged. -/
def LoadFactsLR (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (l : Loc) (v : Val) : Prop :=
  AnchorOk tid σ σ'.snap σ'.g ∧ σ'.r = σ.r ∧ σ'.cl = σ.cl ∧
    ∃ tr, ReadAt A tid σ.vs σ'.snap k l tr v ∧ LoadViews A σ.vs σ'.vs k l tr ∧
      σ'.seen = seenAfter A k σ σ'.g l tr ∧ σ'.fencedR = false ∧ σ'.fencedW = σ.fencedW

theorem loadOutLR_facts {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc} {v : Val}
    (h : LoadOutLR A tid σ σ' k xcl l v) : LoadFactsLR A tid σ σ' k l v := by
  obtain ⟨hanc, hr, hcl, tr, cx', hx, hvs, hseen, hfR, hfW⟩ := h
  obtain ⟨t, v', he, -, hrd, hwi, hp⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [readBound_eq] at hwi
  exact ⟨hanc, hr, hcl, tr, ⟨hrd, hp, hwi⟩,
    by rw [hvs]; exact loadViews_readNext A (envCtx tid σ.vs σ'.snap) k xcl l tr v, hseen, hfR, hfW⟩

/-- **What a load of `EnvGLR` exposes.** -/
theorem step_loadFactsLR {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} (h : (EnvGLR I A tid pl).step (.load k xcl addr n) σ v σ') :
    LoadFactsLR A tid σ σ' k ⟨addr, n⟩ v :=
  loadOutLR_facts h

/-- **What a store of `EnvGLR` exposes** (`EnvG`'s). -/
theorem stepLR_storeFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGLR I A tid pl).step (.store k xcl addr n v) σ b σ') : StoreFacts A tid pl σ σ' k ⟨addr, n⟩ v :=
  storeOut_facts h

/-- A store's outcome reports success (`EnvGLR`). -/
theorem stepLR_store_true {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : StoreKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} {b : Bool}
    (h : (EnvGLR I A tid pl).step (.store k xcl addr n v) σ b σ') : b = true :=
  h.2.1

/-- **What an RMW of `EnvGLR` exposes** (`EnvG`'s). -/
theorem stepLR_rmwFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind} {addr : BitVec 64}
    {n : Nat} {op : Val → Option Val} {old : Val} (h : (EnvGLR I A tid pl).step (.rmw k addr n op) σ old σ') :
    RmwFacts A tid pl σ σ' k ⟨addr, n⟩ op old :=
  rmwOut_facts h

/-- **What a fence of `EnvGLR` exposes** (`EnvG`'s). -/
theorem stepLR_fenceFacts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : FenceKind} {u : Unit}
    (h : (EnvGLR I A tid pl).step (.fence k) σ u σ') : FenceFacts σ σ' k :=
  h

/-- An `EnvG` load outcome, with the old `cl`, is an `EnvGLR` load outcome. -/
theorem loadOut_toLR {A : Arch} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc} {v : Val}
    (h : LoadOut A tid σ σ' k xcl l v) : LoadOutLR A tid σ { σ' with cl := σ.cl } k xcl l v := by
  obtain ⟨hanc, hr, -, rest⟩ := h
  exact ⟨hanc, hr, rfl, rest⟩

end Kraken.Promising.SLR.EnvG

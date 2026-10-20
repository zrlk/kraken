/-
Whole-thread environment: **the
sibling environment `EnvGLRV`, `EnvGLR` with in-flight-aware load knowledge**.
ISA-neutral.

`EnvGLR` (`LREnv.lean`) drops the clean-erasure conjunct of a load
(`LoadOutLR`: `cl` unchanged) because `EnvG`'s conjunct, `ClAt tid σ.r …`,
names the env's *virtual* resource, and with a release in flight the
thread's actual resource is `Plan.after … σ.r`, not `σ.r`: the link cannot
justify it. The consequence (`X64_KNOWN_GAPS.md`) is that a program on `EnvGLR`
never learns anything
about a loaded value under the clean erasure, so a release whose value is a
function of a load (`incl` writing `1`, a ticket `owner + 1`) cannot be
tied to the value the reader relies on.

`EnvGLRV` keeps the conjunct but names the resource the link actually has:
**`ClAtV`**, clean erasure at the load's anchor for *some* thread resource
`r` that is related to the virtual one by the in-flight relation
(`Inflight`, `NodeRel.lean`): `r = σ.r` with no own pending promise, or
`r = Plan.after l v ts P σ.r` for the single own pending promise `ts` of
`⟨l, v⟩`. The link justifies it from the instruction's start knowledge
`cl ∧ Erase (setRes rF tid r) g ⊥ c` with `r` the actual start resource
(`LRValLink.lean`). Everything else (`ok`, stores, RMWs, fences) is `EnvG`'s
(`envGLRV_ok_eq`).

- `ClAtV`, `ClAtV.of_clAt` (no release in flight);
- `LoadOutLRV`, `EnvGLRV`, `LoadFactsLRV`, `step_loadFactsLRV`;
- `loadOutLRV_toLR`: forgetting the conjunct gives an `EnvGLR` outcome.

Limits: as `EnvGLR` (one release in flight; read-side acquire only; no
release-kind RMW). The rule link additionally needs whole plan entries for
the releases (`LRValLink.lean`, module docstring).
-/
import Kraken.Promising.SLR.EnvG.LREnv
import Kraken.Promising.SLR.EnvG.NodeRel

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **In-flight-aware clean knowledge** at anchor `(c, g)`: clean erasure with
thread `tid` holding some `r` that is the virtual resource `rv`, or `rv`
after the thread's single pending own release (`Inflight` at the env's
knowledge `cl`, the anchor's promises and memory). -/
def ClAtV (tid : Nat) (pl : Plan) (cl : Prop) (rv : Res) (g : Ghost) (c : Config I) : Prop :=
  ∃ r, ClAt tid r g c ∧ Inflight tid pl cl rv r g (ownProm tid c) c.mem

/-- Without an own pending promise, `ClAt` at the virtual resource is
`ClAtV`. -/
theorem ClAtV.of_clAt {tid : Nat} {pl : Plan} {cl : Prop} {rv : Res} {g : Ghost} {c : Config I}
    (h : ClAt tid rv g c) (hn : ∀ ts ∈ ownProm tid c, ts ∉ g.pend) : ClAtV tid pl cl rv g c :=
  ⟨rv, h, .inl ⟨rfl, hn⟩⟩

/-- **A load outcome of `EnvGLRV`**: `LoadOutLR` whose `cl` gains `ClAtV` at
the anchor. -/
def LoadOutLRV (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : LoadKind) (xcl : Bool) (l : Loc)
    (v : Val) : Prop :=
  AnchorOk tid σ σ'.snap σ'.g ∧ σ'.r = σ.r ∧ σ'.cl = (σ.cl ∧ ClAtV tid pl σ.cl σ.r σ'.g σ'.snap) ∧
    ∃ tr cx', (tr, v, cx') ∈ readSuccs A iv0 (envCtx tid σ.vs σ'.snap) k xcl l ∧ σ'.vs = cx'.views ∧
      σ'.seen = seenAfter A k σ σ'.g l tr ∧ σ'.fencedR = false ∧ σ'.fencedW = σ.fencedW

/-- **The load-value sibling of `EnvGLR`**: loads add `ClAtV`. -/
def _root_.Kraken.Promising.SLR.EnvGLRV (I : ISA) (A : Arch) (tid : Nat) (pl : Plan) : SharedEnv where
  State := State I
  ok a σ := match a with
    | .load .. => True
    | .fence _ => True
    | .store k xcl addr n v => StoreOk A tid pl σ k xcl ⟨addr, n⟩ v
    | .rmw k addr n op => RmwOk A tid pl σ k ⟨addr, n⟩ op
  step a σ ret σ' := match a, ret with
    | .load k xcl addr n, v => LoadOutLRV A tid pl σ σ' k xcl ⟨addr, n⟩ v
    | .store k xcl addr n v, b => StoreOut A tid pl σ σ' k xcl ⟨addr, n⟩ v b
    | .rmw k addr n op, old => RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old
    | .fence k, _ => FenceOut σ σ' k

/-- `EnvGLRV`'s permissions are `EnvG`'s. -/
theorem envGLRV_ok_eq (A : Arch) (tid : Nat) (pl : Plan) (a : SharedAccess) (σ : State I) :
    (EnvGLRV I A tid pl).ok a σ = (EnvG I A tid pl).ok a σ := by
  cases a <;> rfl

/-- **What a load of `EnvGLRV` exposes**: `LoadFactsLR` with `ClAtV` in `cl`. -/
def LoadFactsLRV (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : LoadKind) (l : Loc) (v : Val) : Prop :=
  AnchorOk tid σ σ'.snap σ'.g ∧ σ'.r = σ.r ∧ σ'.cl = (σ.cl ∧ ClAtV tid pl σ.cl σ.r σ'.g σ'.snap) ∧
    ∃ tr, ReadAt A tid σ.vs σ'.snap k l tr v ∧ LoadViews A σ.vs σ'.vs k l tr ∧
      σ'.seen = seenAfter A k σ σ'.g l tr ∧ σ'.fencedR = false ∧ σ'.fencedW = σ.fencedW

/-- An `EnvGLRV` load outcome with its `cl` reset is an `EnvGLR` one. -/
theorem loadOutLRV_toLR {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool} {l : Loc}
    {v : Val} (h : LoadOutLRV A tid pl σ σ' k xcl l v) : LoadOutLR A tid σ { σ' with cl := σ.cl } k xcl l v := by
  obtain ⟨hanc, hr, -, rest⟩ := h
  exact ⟨hanc, hr, rfl, rest⟩

theorem loadOutLRV_facts {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {l : Loc} {v : Val} (h : LoadOutLRV A tid pl σ σ' k xcl l v) : LoadFactsLRV A tid pl σ σ' k l v := by
  have hcl := h.2.2.1
  obtain ⟨hanc, hr, -, tr, hrd, hv, hseen, hfR, hfW⟩ := loadOutLR_facts (loadOutLRV_toLR h)
  exact ⟨hanc, hr, hcl, tr, hrd, hv, hseen, hfR, hfW⟩

/-- **What a load of `EnvGLRV` exposes.** -/
theorem step_loadFactsLRV {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {addr : BitVec 64} {n : Nat} {v : Val} (h : (EnvGLRV I A tid pl).step (.load k xcl addr n) σ v σ') :
    LoadFactsLRV A tid pl σ σ' k ⟨addr, n⟩ v :=
  loadOutLRV_facts h

end Kraken.Promising.SLR.EnvG

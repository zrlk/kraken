/-
**Liveness with declarations, AArch64: the bridge.**

The AArch64 instance of `LiveRunnerSim`: the map is `State.noDecls` (drop the
thread's declarations), as on x64 (`LiveRunnerX64`). Unlike x64, AArch64
addresses are register values, so no static per-image fact says which
locations a cell touches; the set of states is **dynamic**:

- `WithDeclsD ds S` (the safety side's `A64Whole.WithDeclsD`): the state has
  declarations `ds`, and without them it satisfies a per-lock invariant `S`
  (in the instances: the existing liveness proofs' `Static` facts — program,
  end address, address registers, private memory — and the pc on one of the
  worker's positions);
- `StepOK ds e S`: every `S`-state runs `e`, has no declarations, and its
  tree is `TreeOK ds S`: every access event `ds` resolves to its own
  location (`Decls.AgreesAt`, as on x64) and every leaf is in `S` again.

Under these the tree of a state with declarations is its `decls = {}` tree
with the declarations put back (`A64DeclsBridge.exec_reresolve`, whose
no-pair-merge condition is the static `Executable.noPairs e`, plus
`reresolve_of_treeOK`), so `execSimA` is an `ExecSim` and every promise-free
liveness theorem at `decls = {}` transfers to `decls = ds`
(`liveFrom_transfer`, `progressFrom_transfer`).

`AgreesAt` at the accessed words is the hypothesis, as on x64. The safety
side's `ds.StrictSized` neither implies nor is needed by it: safety reads a
mixed-size access as a fault, which every tree judgment accepts; liveness
needs the same tree, and with a mixed-size declaration of a lock word the
thread faults and never progresses.
-/
import Kraken.Promising.LiveRunnerSim
import Kraken.Promising.SLR.EnvG.A64DeclsRunner
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.Promising.Live.RunnerA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.Live Kraken.Promising.Live.RunnerSim
open Kraken.Promising.SLR.EnvG.A64Whole (WithDeclsD)

/-! ## Trees whose accesses agree -/

/-- **Every access agrees and every leaf is in `S`**: each load, store and
RMW event is at a location `ds` resolves to itself; each `done` leaf
satisfies `S`. -/
def TreeOK {σ : Type} (ds : Decls) (S : σ → Prop) : EvTree σ → Prop
  | .done s => S s
  | .fault _ => True
  | .choose _ k => ∀ i, TreeOK ds S (k i)
  | .load _ _ l ret => ds.AgreesAt l.addr l.bytes ∧ ∀ v, TreeOK ds S (ret v)
  | .store _ _ l _ ret => ds.AgreesAt l.addr l.bytes ∧ ∀ b, TreeOK ds S (ret b)
  | .rmw _ _ l _ ret => ds.AgreesAt l.addr l.bytes ∧ ∀ v, TreeOK ds S (ret v)
  | .fence _ ret => TreeOK ds S (ret ())

theorem access_self {σ : Type} {ds : Decls} {l : Loc} (h : ds.AgreesAt l.addr l.bytes) (k : Loc → EvTree σ) :
    EvTree.access ds l.addr l.bytes k = k l := by
  unfold EvTree.access; rw [show ds.resolve l.addr l.bytes = .ok l from h]

/-- **Re-resolving an agreeing tree changes nothing.** -/
theorem reresolve_of_treeOK {σ : Type} {ds : Decls} {S : σ → Prop} :
    ∀ t : EvTree σ, TreeOK ds S t → t.reresolve ds = t
  | .done _, _ => rfl
  | .fault _, _ => rfl
  | .choose _ k, h => by
    simp only [EvTree.reresolve]; congr 1; funext i; exact reresolve_of_treeOK (k i) (h i)
  | .load _ _ l ret, h => by
    simp only [EvTree.reresolve, access_self h.1]; congr 1; funext v; exact reresolve_of_treeOK (ret v) (h.2 v)
  | .store _ _ l _ ret, h => by
    simp only [EvTree.reresolve, access_self h.1]; congr 1; funext v; exact reresolve_of_treeOK (ret v) (h.2 v)
  | .rmw _ _ l _ ret, h => by
    simp only [EvTree.reresolve, access_self h.1]; congr 1; funext v; exact reresolve_of_treeOK (ret v) (h.2 v)
  | .fence _ ret, h => by
    simp only [EvTree.reresolve]; congr 1; funext u; exact reresolve_of_treeOK (ret ()) h

/-- The leaves of an agreeing tree are in `S`. -/
theorem all_of_treeOK {σ : Type} {ds : Decls} {S : σ → Prop} : ∀ t : EvTree σ, TreeOK ds S t → t.All S
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => all_of_treeOK (k i) (h i)
  | .load _ _ _ ret, h => fun v => all_of_treeOK (ret v) (h.2 v)
  | .store _ _ _ _ ret, h => fun b => all_of_treeOK (ret b) (h.2 b)
  | .rmw _ _ _ _ ret, h => fun v => all_of_treeOK (ret v) (h.2 v)
  | .fence _ ret, h => fun _ => all_of_treeOK (ret ()) h

/-- A map that fixes every leaf fixes the tree. -/
theorem map_eq_self {σ : Type} {P : σ → Prop} (f : σ → σ) (hf : ∀ s, P s → f s = s) :
    ∀ t : EvTree σ, t.All P → t.map f = t
  | .done s, h => by simp only [EvTree.map, hf s h]
  | .fault _, _ => rfl
  | .choose _ k, h => by simp only [EvTree.map]; congr 1; funext i; exact map_eq_self f hf (k i) (h i)
  | .load _ _ _ ret, h => by simp only [EvTree.map]; congr 1; funext v; exact map_eq_self f hf (ret v) (h v)
  | .store _ _ _ _ ret, h => by simp only [EvTree.map]; congr 1; funext v; exact map_eq_self f hf (ret v) (h v)
  | .rmw _ _ _ _ ret, h => by simp only [EvTree.map]; congr 1; funext v; exact map_eq_self f hf (ret v) (h v)
  | .fence _ ret, h => by simp only [EvTree.map]; congr 1; funext u; exact map_eq_self f hf (ret u) (h u)

/-- A leaf condition for a tree, from one for its map. -/
theorem all_map {σ τ : Type} {P : σ → Prop} {Q : τ → Prop} (f : σ → τ) (hf : ∀ s, P s → Q (f s)) :
    ∀ t : EvTree σ, t.All P → (t.map f).All Q
  | .done s, h => hf s h
  | .fault _, _ => trivial
  | .choose _ k, h => fun i => all_map f hf (k i) (h i)
  | .load _ _ _ ret, h => fun v => all_map f hf (ret v) (h v)
  | .store _ _ _ _ ret, h => fun b => all_map f hf (ret b) (h b)
  | .rmw _ _ _ _ ret, h => fun v => all_map f hf (ret v) (h v)
  | .fence _ ret, h => fun u => all_map f hf (ret u) (h u)

/-! ## The bridge -/

/-- **The per-lock obligation**: every state of the invariant `S` runs `e`
with no declarations, and its tree agrees with `ds` and stays in `S`. -/
structure StepOK (ds : Decls) (e : Kraken.Executable Directive) (S : State → Prop) : Prop where
  exe : ∀ s, S s → s.exe = e
  decls : ∀ s, S s → s.decls = {}
  ok : ∀ s, S s → ∀ t, isa.exec s = some t → TreeOK ds S t

theorem noDecls_withDecls_of {S : State → Prop} {ds : Decls} {e : Kraken.Executable Directive} (h : StepOK ds e S) {s : State} (hs : S s) :
    State.noDecls (State.withDecls ds s) = s := by
  have := h.decls s hs
  cases s; simp_all

/-- **The AArch64 simulation**: `State.noDecls` commutes with `exec` on the
dynamic set `WithDeclsD ds S`, for an executable without `LDXP`/`STXP` and
an invariant `S` whose trees agree with `ds` (`StepOK`). -/
theorem execSimA {ds : Decls} {e : Kraken.Executable Directive} [hv : Kraken.Executable.ValidLayout e]
    (hnp : Kraken.Executable.noPairs e = true) {S : State → Prop} (h : StepOK ds e S) :
    ExecSim (I := isa) State.noDecls (WithDeclsD ds S) where
  exec s hs := by
    obtain ⟨hd, hS⟩ := hs
    have he : s.exe = e := h.exe s.noDecls hS
    haveI : Kraken.Executable.ValidLayout s.exe := he ▸ hv
    show isa.exec s.noDecls = (isa.exec s).map _
    rw [exec_reresolve s (he ▸ hnp)]
    cases hx : isa.exec s.noDecls with
    | none => rfl
    | some t0 =>
      have hok := h.ok _ hS t0 hx
      simp only [Option.map_some, hd, reresolve_of_treeOK t0 hok]
      exact congrArg some ((evTree_map_map (σ := State) (State.withDecls ds) State.noDecls t0).trans
        (map_eq_self (P := S) _ (fun s' hs' => noDecls_withDecls_of h hs') t0 (all_of_treeOK t0 hok))).symm
  deps _ _ := rfl
  showInstr _ _ := rfl
  leaves s hs tree hx := by
    obtain ⟨hd, hS⟩ := hs
    have he : s.exe = e := h.exe s.noDecls hS
    haveI : Kraken.Executable.ValidLayout s.exe := he ▸ hv
    rw [exec_reresolve s (he ▸ hnp)] at hx
    obtain ⟨t0, h0, rfl⟩ := Option.map_eq_some_iff.mp hx
    have hok := h.ok _ hS t0 h0
    rw [hd, reresolve_of_treeOK t0 hok]
    exact all_map _ (fun s' hs' => ⟨rfl, by rw [noDecls_withDecls_of h hs']; exact hs'⟩) t0 (all_of_treeOK t0 hok)
  inj s s' hs hs' e' := by
    obtain ⟨hd, -⟩ := hs
    obtain ⟨hd', -⟩ := hs'
    have e2 := congrArg (State.withDecls ds) e'
    cases s; cases s'
    simp only [State.withDecls] at e2 hd hd'
    subst hd hd'
    exact e2

/-- A start configuration of `WithDeclsD` states is `GoodC`. -/
theorem goodC_initA {ds : Decls} {S : State → Prop} {states : List State} (initMem : List (Loc × Val))
    (h : ∀ s ∈ states, WithDeclsD ds S s) : GoodC (WithDeclsD ds S) (Config.init (I := isa) states initMem) :=
  goodC_init initMem h

end Kraken.Promising.Live.RunnerA64

open Kraken.Promising.Live.RunnerA64 in
#print axioms execSimA

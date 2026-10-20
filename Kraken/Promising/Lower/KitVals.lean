/-
The AArch64 lowering kit over value-restricted environments.

`Kit.lower_promising_vals` states each thread's `main` triple in the
value-restricted `counted (EnvGCAdjV A tid pl G)` and its value triple in
`counted (inv S G)`, but its purity triple stays in plain
`counted (relPure A rel)`. A thread whose private memory is non-empty needs
the value restriction in its purity proof too: its shared accesses miss the
private memory only for the values `G` allows (an address read from a shared
cell), and in plain `relPure` that address is arbitrary. This file gives the
kit the form where all three triples assume `G` of load answers:

- `LowerThreadW A tid rel B S G`: layout, text, plan, static facts,
  stuck-at-end, the post `Q` with `hB`; the purity triple `pure` in
  `counted (valsEnv (relPure A rel) G)`; `main` in
  `counted (EnvGCAdjV A tid pl G)`; the value triple `vals` in
  `counted (inv S G)`. `LowerThreadW.Start`: the start state.
- **`lower_promising_valsW`**: per-thread `LowerThreadW`s at their `Start`s,
  `MemInv G` of the initial memory and a final reading `hfin` give `Φ c` for
  every final `c` reachable under `A`. Sound because the value triples keep
  `MemInv G` at every reachable configuration, so purity is needed only on
  the `G`-branches (`KitVals.envGValsBridge_ofSpecsP`).
- `LowerThreadW.ofV` and **`lower_promising_vals_viaW`**: every
  `Kit.LowerThreadV` is a `LowerThreadW` (a judgment of `E` is one of
  `valsEnv E G`), and `Kit.lower_promising_vals` is re-derived through the
  new form with its exact statement.
- Generic: `Effects.AllEnv.substep`, `Safely.substep` (fewer outcomes, same
  permissions), `PartialTripleEnv.countedVals`.

Machine: the executable Promising machine (`Reachable A`). Phase-1 limits
apply (`Phase1TreeF`), as in `Kit`.
-/
import Kraken.Promising.Lower.KitValsPure
import Kraken.Promising.Lower.EnvSubstep

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.KitVals

open Kraken.Promising.SLR.EnvG.Vals (valsEnv)
open Kraken.Promising.AArch64.EnvG.Vals (EnvGCAdjV)
open Kraken.Promising.Lower.Kit (LowerThreadV emptyExe)

/-! ## Fewer outcomes, same permissions

The generic forms are `Lower.Effects.AllEnv.substep`, `Lower.Safely.substep`
and `Lower.PartialTripleEnv.countedVals` (`Lower/EnvSubstep.lean`); the names
below are kept as aliases. -/

/-- **A judgment of `E` is one of every environment with `E`'s state and
permissions and fewer outcomes.** -/
theorem Effects.AllEnv.substep {E : SharedEnv} {st : (a : SharedAccess) → E.State → a.Ret → E.State → Prop}
    (hst : ∀ a g r g', st a g r g' → E.step a g r g') {post : MachineState → E.State → Prop}
    (ef : Effects) : ∀ g, ef.AllEnv E g post → ef.AllEnv ⟨E.State, E.ok, st⟩ g post :=
  Kraken.Promising.Lower.Effects.AllEnv.substep hst ef

/-- **`Safely` with fewer outcomes** (`Effects.AllEnv.substep`). -/
theorem Safely.substep {E : SharedEnv} {st : (a : SharedAccess) → E.State → a.Ret → E.State → Prop}
    (hst : ∀ a g r g', st a g r g' → E.step a g r g') {e : Kraken.Executable Directive}
    {post : MachineState × E.State → Prop} {x : MachineState × E.State}
    (h : Safely (e.instrStepEnv E) post x) : Safely (e.instrStepEnv ⟨E.State, E.ok, st⟩) post x :=
  Kraken.Promising.Lower.Safely.substep hst h

/-- **A counted partial triple of `E` is one of `valsEnv E G`.** -/
theorem PartialTripleEnv.countedVals [CodeEnv] {E : SharedEnv} {G : Loc → Val → Prop}
    {P : MachineData → (SharedEnv.counted E).State → Prop} {q : Program}
    {Q : MachineData → (SharedEnv.counted E).State → Prop}
    {Ex : Int64 → MachineData → (SharedEnv.counted E).State → Prop}
    (h : PartialTripleEnv (SharedEnv.counted E) P q Q Ex) :
    PartialTripleEnv (SharedEnv.counted (valsEnv E G)) P q Q Ex :=
  Kraken.Promising.Lower.PartialTripleEnv.countedVals h

/-! ## The value-restricted kit -/

/-- **A lowered thread over value-restricted environments**: `Kit.LowerCore`'s
data with the purity triple `pure` in `counted (valsEnv (relPure A rel) G)`,
the whole-text `main` triple in `counted (EnvGCAdjV A tid pl G)` and the value
triple `vals` in `counted (inv S G)` (every shared write of the thread
satisfies `G`, every access is an `S`-location). -/
structure LowerThreadW (A : Arch) (tid : Nat) (rel : Loc → Pred) (B : Config isa → Res → Ghost → Prop)
    (S : SharedEnv.Layout) (G : Loc → Val → Prop) where
  l : _root_.Layout
  p : Program
  valid : Kraken.Executable.ValidLayout (l p)
  pl : Plan
  hpl : pl.Valid
  live : (l p).rmwLive = true
  shape : Phase1TreeF (l p)
  stuck : ∀ (env : SharedEnv) x R, x.1.2 = (l p).addrOf p.length → ¬ (l p).instrStepEnv env x R
  Q : MachineData → EStateA × Nat → Prop
  hB : ∀ (c : Config isa) (t : Thread isa) r g cl (σ : EStateA),
    postOf (layout := l) p (fun s g => ∃ n, Q s (g, n)) (t.st.st, σ) →
    t.prom = [] → EnvRel tid pl σ c t r g cl → cl → B c r g
  PreR : MachineData → (SharedEnv.counted (valsEnv (SharedEnv.relPure A rel) G)).State → Prop
  QR : MachineData → (SharedEnv.counted (valsEnv (SharedEnv.relPure A rel) G)).State → Prop
  pure : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (valsEnv (SharedEnv.relPure A rel) G)) PreR p QR
    (fun _ _ _ => False)
  Pre : MachineData → (SharedEnv.counted (EnvGCAdjV A tid pl G)).State → Prop
  main : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (EnvGCAdjV A tid pl G)) Pre p Q (fun _ _ _ => False)
  PreV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop
  QV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop
  vals : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (SharedEnv.inv S G)) PreV p QV (fun _ _ _ => False)

variable {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
  {S : SharedEnv.Layout} {G : Loc → Val → Prop}

/-- **A thread's start state**: `T`'s code, no declarations, at the start of
the text returning to its end, with the three preconditions (`σ` the env
state the kit starts the thread in, `σInit`). -/
structure LowerThreadW.Start (T : LowerThreadW A tid rel B S G) (σ : EStateA) (s : isa.State) : Prop where
  exe : s.exe = T.l T.p
  decls : s.decls = {}
  endPc : s.endPc = (T.l T.p).addrOf T.p.length
  pc : s.st.2 = (T.l T.p).addrOf 0
  preR : ∃ n, T.PreR s.st.1 ((), n)
  pre : ∃ n, T.Pre s.st.1 (σ, n)
  preV : ∃ n, T.PreV s.st.1 ((), n)

/-- The purity specification of a lowered thread. -/
def LowerThreadW.pureSpec (T : LowerThreadW A tid rel B S G) : RelPureSpec A rel :=
  @RelPureSpec.ofProgram A rel T.l T.p T.valid fun s g => ∃ n, T.QR s (g, n)

/-- The value specification of a lowered thread. -/
def LowerThreadW.valSpec (T : LowerThreadW A tid rel B S G) : ThreadSpec S G :=
  @ThreadSpec.ofSafely S G (T.l T.p) T.valid ((T.l T.p).addrOf T.p.length)
    (fun x => (x.1.2 = (T.l T.p).addrOf T.p.length ∧ ∃ n, T.QV x.1.1 (x.2, n)) ∨ False)
    (fun _ h => h.elim And.left False.elim)

/-- The purity specifications of a family of threads (`emptyExe` beyond `k`). -/
def pureSpecsW {k : Nat} (T : ∀ tid, tid < k → LowerThreadW A tid rel B S G) (tid : Nat) : RelPureSpec A rel :=
  if h : tid < k then (T tid h).pureSpec
  else ⟨emptyExe, inferInstance, 0, fun _ => False, fun _ h => h.elim⟩

/-- The value specifications of a family of threads (`emptyExe` beyond `k`). -/
def valSpecsW {k : Nat} (T : ∀ tid, tid < k → LowerThreadW A tid rel B S G) (tid : Nat) : ThreadSpec S G :=
  if h : tid < k then (T tid h).valSpec
  else ⟨emptyExe, inferInstance, 0, fun _ => False, fun _ => False, fun _ h => h.elim, fun _ h => h.elim⟩

theorem LowerThreadW.pureSpec_holdsV (T : LowerThreadW A tid rel B S G) {σ : EStateA} {s : isa.State}
    (hS : T.Start σ s) : T.pureSpec.HoldsV G s := by
  letI : CodeEnv := ⟨T.l T.p⟩
  letI := T.valid
  obtain ⟨he, hds, hend, hpc, hR, -, -⟩ := hS
  exact RelPureSpec.holdsV_of_partialTripleEnv (layout := T.l) T.pure.uncount rfl he hds hend hpc hR

theorem LowerThreadW.valSpec_holds (T : LowerThreadW A tid rel B S G) {σ : EStateA} {s : isa.State}
    (hS : T.Start σ s) : T.valSpec.Holds s := by
  letI : CodeEnv := ⟨T.l T.p⟩
  letI := T.valid
  obtain ⟨he, hds, hend, hpc, -, -, hV⟩ := hS
  exact ⟨he, hend, hds, safely_start_of_partialTripleEnv (layout := T.l) T.vals.uncount rfl hpc hV (by simp)⟩

/-- **The lowering kit over value-restricted environments**: two-or-more-
thread AArch64 programs, each thread a `LowerThreadW` started at its `Start`
(in `σInit` of the initial configuration, resource `rF tid`, ghost `g₀`);
with `Erase` of the initial configuration, no pending ghost mark,
no-promise-of-the-future (`hH`) and `MemInv G` of the initial memory, every
final configuration `c` reachable under `A` satisfies `Φ` as soon as the
final reading `hfin` turns the done threads' shared postconditions into `Φ`. -/
theorem lower_promising_valsW (A : Arch) (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (G : Loc → Val → Prop)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (hm0 : MemInv G (Config.init states initMem).mem)
    (T : ∀ tid, tid < states.length → LowerThreadW A tid g₀.rel B S G)
    (hS : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInit (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  classical
  let pl : Nat → Plan := fun tid => if h : tid < states.length then (T tid h).pl else ⟨[]⟩
  let e : Nat → Kraken.Executable Directive := fun tid =>
    if h : tid < states.length then (T tid h).l (T tid h).p else emptyExe
  let endPc : Nat → Int64 := fun tid =>
    if h : tid < states.length then ((T tid h).l (T tid h).p).addrOf (T tid h).p.length else 0
  let post : Nat → MachineState × EStateA → Prop := fun tid =>
    if h : tid < states.length then
      postOf (layout := (T tid h).l) (T tid h).p (fun s g => ∃ n, (T tid h).Q s (g, n))
    else fun _ => False
  refine envGValsBridge_ofSpecsP G (valSpecsW T) A fuel states initMem rF g₀ B Φ pl e endPc post hH hE hpend
    (pureSpecsW T) ?_ hm0 ?_ ?_ c hc hf hfin
  · intro tid s hs
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hs
    rw [show pureSpecsW T tid = (T tid h).pureSpec from dite_eq_left_of_eq_true (eq_true h)]
    exact (T tid h).pureSpec_holdsV (hS tid h)
  · intro tid t ht
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hs
    rw [show valSpecsW T tid = (T tid h).valSpec from dite_eq_left_of_eq_true (eq_true h)]
    exact (T tid h).valSpec_holds (hS tid h)
  · intro tid h
    have hpl : pl tid = (T tid h).pl := dite_eq_left_of_eq_true (eq_true h)
    have he : e tid = (T tid h).l (T tid h).p := dite_eq_left_of_eq_true (eq_true h)
    have hend : endPc tid = ((T tid h).l (T tid h).p).addrOf (T tid h).p.length :=
      dite_eq_left_of_eq_true (eq_true h)
    have hpost : post tid = postOf (layout := (T tid h).l) (T tid h).p (fun s g => ∃ n, (T tid h).Q s (g, n)) :=
      dite_eq_left_of_eq_true (eq_true h)
    rw [hpl, he, hend, hpost]
    obtain ⟨hex, hds, hendS, hpc, -, hP, -⟩ := hS tid h
    let Tt := T tid h
    letI : CodeEnv := ⟨Tt.l Tt.p⟩
    letI := Tt.valid
    exact ⟨Tt.valid, Tt.hpl, Tt.live, Tt.shape, postOf_end (layout := Tt.l), Tt.stuck _, Tt.hB, states[tid],
      List.getElem?_eq_getElem h, hex, hds, hendS,
      safely_start_of_partialTripleEnv (layout := Tt.l) Tt.main.uncount rfl hpc hP (by simp)⟩

/-! ## The frame + value-bridge kit is an instance -/

/-- **Every `Kit.LowerThreadV` is a `LowerThreadW`**: its plain purity triple
is one of the value-restricted purity environment. -/
def LowerThreadW.ofV (T : LowerThreadV A tid rel B S G) : LowerThreadW A tid rel B S G where
  l := T.l
  p := T.p
  valid := T.valid
  pl := T.pl
  hpl := T.hpl
  live := T.live
  shape := T.shape
  stuck := T.stuck
  Q := T.Q
  hB := T.hB
  PreR := T.PreR
  QR := T.QR
  pure := @PartialTripleEnv.countedVals ⟨T.l T.p⟩ _ G _ _ _ _ T.pure
  Pre := T.Pre
  main := T.main
  PreV := T.PreV
  QV := T.QV
  vals := T.vals

/-- **`Kit.lower_promising_vals`, through the value-restricted kit**: the
exact statement of the original theorem, proved by `lower_promising_valsW`. -/
theorem lower_promising_vals_viaW (A : Arch) (fuel : Nat) {states : List isa.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop}
    {Φ : Config isa → Prop} {S : SharedEnv.Layout} (G : Loc → Val → Prop)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (hm0 : MemInv G (Config.init states initMem).mem)
    (T : ∀ tid, tid < states.length → LowerThreadV A tid g₀.rel B S G)
    (hS : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInit (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  lower_promising_valsW A fuel G hH hE hpend hm0 (fun tid h => LowerThreadW.ofV (T tid h))
    (fun tid h => let ⟨⟨he, hds, hend, hpc, hR⟩, hP, hV⟩ := hS tid h; ⟨he, hds, hend, hpc, hR, hP, hV⟩) hc hf hfin

end Kraken.Promising.Lower.KitVals

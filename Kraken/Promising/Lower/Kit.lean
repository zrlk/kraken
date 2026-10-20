/-
**The AArch64 lowering assembly kit.** ISA: AArch64 (`isa`); machine: the
executable Promising machine
(`Reachable A`), through Theorem 1′ for `NPSafeF` (`theorem1FChain`).

Every lowering pilot (the first lowering pilot `pilot_promising`, the stack-frame pilot/the unconditional stack-frame pilot `pilot2_promising`,
the MS queue pilot `msqPilot_promising`) assembled its whole-program theorem by hand
from the same pieces: the whole-text `main` partial triple in the counted
`EnvGCAdj` env (resp. its value-restricted `EnvGCAdjV`), its relPure twin,
the static `rmwLive`/`Phase1TreeF`/`ValidLayout` facts, stuck-at-end, `hB`
(the post read as the shared postcondition) and the start facts. This file
packages them per thread and proves the assembly once:

- `LowerCore`: what both variants share (layout, text, plan, static facts,
  stuck-at-end, the counted post `Q` with its `hB`, the relPure twin).
- `LowerThread` (frameless): `LowerCore` plus `main` in
  `counted (EnvGCAdjA A tid pl)`. `LowerThread.Start`: the start state.
  **`lower_promising`**: per-thread `LowerThread`s at their `Start`s and a
  final-state reading `hfin` give `Φ c` for every final `c` reachable under
  `A` (`final_of_relPureSafelyF`).
- `LowerThreadV` (frame + value bridge): `main` in
  `counted (EnvGCAdjV A tid pl G)` and the value triple `vals` in
  `counted (inv S G)`. **`lower_promising_vals`**: the same conclusion from
  `MemInv G` of the initial memory in addition (`envGValsBridge_ofSpecs`).

What stays per program: the triples themselves, `hB` (usually 10 lines,
mechanical), the start structure and its discharge, and the final reading
`hfin` (a property of the shared data structure, reusable across lowerings
of the same structure).

Phase-1 limits apply (`Phase1TreeF`: single-access trees, read-side acquire
only, releases are stores or `casal`).
-/
import Kraken.Promising.SLR.EnvG.ValsA64
import Kraken.Promising.SLR.EnvG.AdjVCGenA64

open Std.WP Kraken Kraken.Promising Kraken.Promising.AArch64 MachineWP
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.Lower.Kit

/-! ## Per-thread contracts -/

/-- **What a lowered thread provides, in both variants**: layout `l` and text
`p` (validly laid out), plan `pl`, the static facts, no step at the end of the
text in any environment (`not_instrStepEnv_of_end_labels _ k`), the post `Q`
read as the shared postcondition `B` (`hB`), and the relPure twin `pure` of
the whole text (counted `relPure A rel`, from `PreR` to `QR`, no other exit). -/
structure LowerCore (A : Arch) (tid : Nat) (rel : Loc → Pred) (B : Config isa → Res → Ghost → Prop) where
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
  PreR : MachineData → (SharedEnv.counted (SharedEnv.relPure A rel)).State → Prop
  QR : MachineData → (SharedEnv.counted (SharedEnv.relPure A rel)).State → Prop
  pure : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (SharedEnv.relPure A rel)) PreR p QR (fun _ _ _ => False)

/-- **A frameless lowered thread**: `LowerCore` and the whole-text `main`
triple in `counted (EnvGCAdjA A tid pl)` from `Pre` to `Q`, no other exit. -/
structure LowerThread (A : Arch) (tid : Nat) (rel : Loc → Pred) (B : Config isa → Res → Ghost → Prop)
    extends LowerCore A tid rel B where
  Pre : MachineData → (SharedEnv.counted (EnvGCAdjA A tid pl)).State → Prop
  main : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (EnvGCAdjA A tid pl)) Pre p Q (fun _ _ _ => False)

/-- **A thread's start state**: `T`'s code, no declarations, at the start of
the text returning to its end, with both preconditions (`σ` the env state the
kit starts the thread in, `σInit`). -/
structure LowerCore.StartC {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    (T : LowerCore A tid rel B) (s : isa.State) : Prop where
  exe : s.exe = T.l T.p
  decls : s.decls = {}
  endPc : s.endPc = (T.l T.p).addrOf T.p.length
  pc : s.st.2 = (T.l T.p).addrOf 0
  preR : ∃ n, T.PreR s.st.1 ((), n)

/-- `LowerCore.StartC` and `Pre` at `σ`. -/
structure LowerThread.Start {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    (T : LowerThread A tid rel B) (σ : EStateA) (s : isa.State) : Prop extends T.StartC s where
  pre : ∃ n, T.Pre s.st.1 (σ, n)

/-! ## The frameless kit -/

/-- An empty executable: validly laid out (fills out-of-range thread ids). -/
def emptyExe : Kraken.Executable Directive := (0, [])

instance emptyExe_valid : Kraken.Executable.ValidLayout emptyExe where
  label_size _ _ _ h := by simp [emptyExe] at h
  instr_size _ _ _ h := by simp [emptyExe] at h
  data_size _ _ _ h := by simp [emptyExe] at h
  no_wrap := by simp [emptyExe]

/-- The relPure specification of a lowered thread. -/
def LowerCore.pureSpec {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    (T : LowerCore A tid rel B) : RelPureSpec A rel :=
  @RelPureSpec.ofProgram A rel T.l T.p T.valid fun s g => ∃ n, T.QR s (g, n)

/-- The purity specifications of a family of threads (`emptyExe` beyond `k`). -/
def pureSpecs {A : Arch} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop} {k : Nat}
    (T : ∀ tid, tid < k → LowerCore A tid rel B) (tid : Nat) : RelPureSpec A rel :=
  if h : tid < k then (T tid h).pureSpec
  else ⟨emptyExe, inferInstance, 0, fun _ => False, fun _ h => h.elim⟩

theorem LowerCore.pureSpec_holds {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} (T : LowerCore A tid rel B) {s : isa.State} (hS : T.StartC s) :
    T.pureSpec.Holds s := by
  letI : CodeEnv := ⟨T.l T.p⟩
  letI := T.valid
  obtain ⟨he, hds, hend, hpc, hR⟩ := hS
  exact RelPureSpec.holds_of_partialTripleEnv (layout := T.l) T.pure.uncount rfl he hds hend hpc hR

theorem pureSpecs_holds {A : Arch} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    {states : List isa.State} (T : ∀ tid, tid < states.length → LowerCore A tid rel B)
    (hS : ∀ tid (h : tid < states.length), (T tid h).StartC states[tid]) :
    ∀ tid s, states[tid]? = some s → (pureSpecs T tid).Holds s := by
  intro tid s hs
  obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hs
  rw [show pureSpecs T tid = (T tid h).pureSpec from dite_eq_left_of_eq_true (eq_true h)]
  exact (T tid h).pureSpec_holds (hS tid h)

/-- **The frameless lowering kit**: two-or-more-thread AArch64 programs, each
thread a `LowerThread` started at its `Start` (in `σInit` of the initial
configuration, resource `rF tid`, ghost `g₀`); with `Erase` of the initial
configuration, no pending ghost mark and no-promise-of-the-future (`hH`),
every final configuration `c` reachable under `A` satisfies `Φ` as soon as the
final reading `hfin` turns the done threads' shared postconditions into `Φ`. -/
theorem lower_promising (A : Arch) (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (T : ∀ tid, tid < states.length → LowerThread A tid g₀.rel B)
    (hS : ∀ tid (h : tid < states.length),
      (T tid h).Start (σInit (Config.init states initMem) (rF tid) g₀) states[tid])
    {c : Config isa} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c := by
  refine final_of_relPureSafelyF A fuel hH hE (by simp [hpend]) (pureSpecs fun tid h => (T tid h).toLowerCore)
    (pureSpecs_holds _ fun tid h => (hS tid h).toStartC) ?_ hc hf hfin
  intro tid h n m
  have hs : states[tid]? = some states[tid] := List.getElem?_eq_getElem h
  obtain ⟨⟨he, hds, hend, hpc, -⟩, hP⟩ := hS tid h
  let Tt := T tid h
  letI : CodeEnv := ⟨Tt.l Tt.p⟩
  letI := Tt.valid
  exact npSafeF_of_safelyEnvGFCAdj Tt.hpl Tt.live Tt.shape (postOf_end (layout := Tt.l)) (Tt.stuck _) Tt.hB n m
    (invGFCAdj_init hs hpend (qa64CAdj_of_partialTripleEnv (layout := Tt.l) Tt.main.uncount rfl he hds hend hpc hP))

/-! ## The frame + value-bridge kit -/

/-- **A lowered thread with a `dmem` frame**: `LowerCore`, the whole-text
`main` triple in the value-restricted `counted (EnvGCAdjV A tid pl G)` (load
answers satisfy `G`), and the value triple `vals` in `counted (inv S G)` (every
shared write of the thread satisfies `G`, every load is an `S`-location). -/
structure LowerThreadV (A : Arch) (tid : Nat) (rel : Loc → Pred) (B : Config isa → Res → Ghost → Prop)
    (S : SharedEnv.Layout) (G : Loc → Val → Prop) extends LowerCore A tid rel B where
  Pre : MachineData → (SharedEnv.counted (Vals.EnvGCAdjV A tid pl G)).State → Prop
  main : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (Vals.EnvGCAdjV A tid pl G)) Pre p Q (fun _ _ _ => False)
  PreV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop
  QV : MachineData → (SharedEnv.counted (SharedEnv.inv S G)).State → Prop
  vals : @PartialTripleEnv ⟨l p⟩ (SharedEnv.counted (SharedEnv.inv S G)) PreV p QV (fun _ _ _ => False)

/-- `LowerCore.StartC`, `Pre` at `σ` and `PreV`. -/
structure LowerThreadV.Start {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    {S : SharedEnv.Layout} {G : Loc → Val → Prop} (T : LowerThreadV A tid rel B S G) (σ : EStateA)
    (s : isa.State) : Prop extends T.StartC s where
  pre : ∃ n, T.Pre s.st.1 (σ, n)
  preV : ∃ n, T.PreV s.st.1 ((), n)

/-- The value specification of a lowered thread (`ThreadSpec.ofSafely` of its
text, the end of the text and `QV`). -/
def LowerThreadV.valSpec {A : Arch} {tid : Nat} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop}
    {S : SharedEnv.Layout} {G : Loc → Val → Prop} (T : LowerThreadV A tid rel B S G) : ThreadSpec S G :=
  @ThreadSpec.ofSafely S G (T.l T.p) T.valid ((T.l T.p).addrOf T.p.length)
    (fun x => (x.1.2 = (T.l T.p).addrOf T.p.length ∧ ∃ n, T.QV x.1.1 (x.2, n)) ∨ False)
    (fun _ h => h.elim And.left False.elim)

/-- The value specifications of a family of threads (`emptyExe` beyond `k`). -/
def valSpecs {A : Arch} {rel : Loc → Pred} {B : Config isa → Res → Ghost → Prop} {S : SharedEnv.Layout}
    {G : Loc → Val → Prop} {k : Nat} (T : ∀ tid, tid < k → LowerThreadV A tid rel B S G) (tid : Nat) :
    ThreadSpec S G :=
  if h : tid < k then (T tid h).valSpec
  else ⟨emptyExe, inferInstance, 0, fun _ => False, fun _ => False, fun _ h => h.elim, fun _ h => h.elim⟩

theorem LowerThreadV.valSpec_holds {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} {S : SharedEnv.Layout} {G : Loc → Val → Prop}
    (T : LowerThreadV A tid rel B S G) {σ : EStateA} {s : isa.State} (hS : T.Start σ s) : T.valSpec.Holds s := by
  letI : CodeEnv := ⟨T.l T.p⟩
  letI := T.valid
  obtain ⟨⟨he, hds, hend, hpc, -⟩, -, hV⟩ := hS
  exact ⟨he, hend, hds, safely_start_of_partialTripleEnv (layout := T.l) T.vals.uncount rfl hpc hV (by simp)⟩

/-- **The frame + value-bridge lowering kit**: `lower_promising` for threads
in the value-restricted env (`LowerThreadV`), given in addition `MemInv G` of
the initial memory; the value bridge is the value bridge' `envGValsBridge_ofSpecs`, fed
by the threads' value triples. Same conclusion: every final configuration
reachable under `A` satisfies `Φ` given the final reading `hfin`. -/
theorem lower_promising_vals (A : Arch) (fuel : Nat) {states : List isa.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g₀ : Ghost} {B : Config isa → Res → Ghost → Prop} {Φ : Config isa → Prop}
    {S : SharedEnv.Layout} (G : Loc → Val → Prop)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : g₀.pend = [])
    (hm0 : MemInv G (Config.init states initMem).mem)
    (T : ∀ tid, tid < states.length → LowerThreadV A tid g₀.rel B S G)
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
  refine Vals.envGValsBridge_ofSpecs G (valSpecs T) A fuel states initMem rF g₀ B Φ pl e endPc post hH hE hpend
    (pureSpecs fun tid h => (T tid h).toLowerCore) (pureSpecs_holds _ fun tid h => (hS tid h).toStartC) hm0
    ?_ ?_ c hc hf hfin
  · intro tid t ht
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    obtain ⟨h, rfl⟩ := List.getElem?_eq_some_iff.mp hs
    rw [show valSpecs T tid = (T tid h).valSpec from dite_eq_left_of_eq_true (eq_true h)]
    exact (T tid h).valSpec_holds (hS tid h)
  · intro tid h
    have hpl : pl tid = (T tid h).pl := dite_eq_left_of_eq_true (eq_true h)
    have he : e tid = (T tid h).l (T tid h).p := dite_eq_left_of_eq_true (eq_true h)
    have hend : endPc tid = ((T tid h).l (T tid h).p).addrOf (T tid h).p.length :=
      dite_eq_left_of_eq_true (eq_true h)
    have hpost : post tid = postOf (layout := (T tid h).l) (T tid h).p (fun s g => ∃ n, (T tid h).Q s (g, n)) :=
      dite_eq_left_of_eq_true (eq_true h)
    rw [hpl, he, hend, hpost]
    obtain ⟨⟨hex, hds, hendS, hpc, -⟩, hP, -⟩ := hS tid h
    let Tt := T tid h
    letI : CodeEnv := ⟨Tt.l Tt.p⟩
    letI := Tt.valid
    exact ⟨Tt.valid, Tt.hpl, Tt.live, Tt.shape, postOf_end (layout := Tt.l), Tt.stuck _, Tt.hB, states[tid],
      List.getElem?_eq_getElem h, hex, hds, hendS,
      safely_start_of_partialTripleEnv (layout := Tt.l) Tt.main.uncount rfl hpc hP (by simp)⟩

/-! ## The thread rule and its no-fault rule -/

/-- **A frameless lowered thread's rule** (`ThreadRuleRXF.ofSafelyEnvGFCAdj`). -/
noncomputable def LowerThread.rule {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} (T : LowerThread A tid rel B) : ThreadRuleRXF (I := isa) A B tid :=
  letI := T.valid
  ThreadRuleRXF.ofSafelyEnvGFCAdj (post := postOf (layout := T.l) T.p fun s g => ∃ n, T.Q s (g, n)) T.hpl T.live
    T.shape (postOf_end (layout := T.l)) (T.stuck _) T.hB

/-- **The rule excludes faults** for fault-free code (`dirs_no_fault'`). -/
theorem LowerThread.rule_noFault {A : Arch} {tid : Nat} {rel : Loc → Pred}
    {B : Config isa → Res → Ghost → Prop} (T : LowerThread A tid rel B) (hnf : DirsNoFault (T.l T.p)) :
    NoFaultRuleF T.rule :=
  letI := T.valid
  noFaultRuleF_ofSafelyEnvGFCAdj_struct _ _ _ _ _ _ hnf

end Kraken.Promising.Lower.Kit

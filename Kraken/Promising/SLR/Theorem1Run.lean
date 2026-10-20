/-
Theorem 1′ for the SLR-adapted model, option (B): the **annotated run** that
the induction builds along a live path, and **condition (3)** (`SLR.Cond3`)
stated over it.

## Why condition (3) is stated over a whole annotated run

`NPSafe`'s step assumes only validity-free erasure (`T = fun _ => True`).
Theorem 1′'s conclusion needs full erasure (`T = ⊥`), i.e. `mayWrite` for every
non-pending outstanding promise (`Erase.validate_all`). The argument for that
(§5.5 "Condition (3)") goes *forward* along the path: the promise is
fulfilled later, by an `NPSafe` step of its owner that owns the location then,
and that permission is chased back to the earlier configuration through the
`K1`/`K2` conjuncts of the steps in between. So validity at index `j` depends
on annotations at indices after `j`. The induction (`SLR/Theorem1Proof.lean`)
therefore annotates the *whole* path, to its final configuration, without
using validity, and `Cond3` is applied afterwards to the complete run.

## The run

The real path is `π 0 = c0, …, π L` (final), each step a `succs` successor.
The annotation is a sequence of *micro-configurations* `cfg μ`, `μ ≤ N`, with
thread resources `rF μ` and ghost `g μ`, satisfying validity-free erasure. At
real index `j` the micro-configuration `cfg (pos j)` is a virtual
configuration of `π j` (`Config.VirtualOf`): threads with a prepaid release
stand just before its fulfilling instruction. Between `pos j` and
`pos (j + 1)` the micro-steps (`MicroStep`) are:

- one `np` step (an instruction of a thread that is not advanced, or the
  fulfilling instruction `F` of an advanced one: cases (a), (c));
- one `promise` step (a promise fulfilled on `π` by a non-release store, case
  (d2), `Erase.promise`);
- a replay: `np` steps of the promising thread from its virtual state up to
  just before `F` (the memory-silent advance, (S1′)), then one `prepay` step
  (case (d1), O3);
- none (case (b): a real step of an advanced thread before `F`, a stutter
  step that the virtual configuration has already taken).

Each `np` and `prepay` step records the conjuncts of `NPSafe` that condition
(3) uses: `acqLe`, ownership of written messages, `K1`, `K2`, exact pending
marks. Every thread state of a micro-configuration is a real thread state of
`π`, with its promises restricted (`real`), so the machine facts of `π`
(`Config.Live.vwNew_lt`, `readSuccs_acq_vwNew`) apply to it.

## Contents

- `Path`: a finite path of `succs` steps, as a function with a length.
- `MicroStep`: the annotated micro-steps.
- `AnnRun`: an annotated run of a path.
- `Valid`: SLR's validity of non-pending promises at one micro-configuration.
- `Cond3`: every annotated run of a path from `c0` to a final configuration
  is valid at every real index. **Open**. Theorem 1′ is proved
  from it in `SLR/Theorem1Proof.lean`.

## Generic chain

The declarations above that mention a guard or the K2 frame are stated
generically with a prime: `MicroStep' K`, `AnnRun' GV K`, `Cond3' GV K`, with
`Config.VirtualOfG GV`. The existing names (`MicroStep`, `AnnRun`, `Cond3`)
keep their statements; they are the instances at `GRF`, `K2₀` (end of file,
`SLR/NPSafePGen.lean`).
-/
import Kraken.Promising.SLR.NPSafePGen

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `Config.VirtualOf` with the advanced threads' guard `G` (the virtual
guard of the generic chain); `Config.VirtualOf` is `Config.VirtualOfG GRF`
(`Config.virtualOfG_GRF`). -/
def _root_.Kraken.Promising.Config.VirtualOfG (G : PrepayGuard I) (A : Arch) (c v : Config I) : Prop :=
  v.mem = c.mem ∧ v.threads.size = c.threads.size ∧
    ∀ i t, c.threads[i]? = some t → ∃ t', v.threads[i]? = some t' ∧ ThreadNP A i (t, c.mem) (t', c.mem) ∧
      (t' = t ∨ ∃ ts ∈ t'.prom, G A i ts t' c.mem)

theorem _root_.Kraken.Promising.Config.VirtualOfG.refl (G : PrepayGuard I) (A : Arch) (c : Config I) :
    c.VirtualOfG G A c :=
  ⟨rfl, rfl, fun _ t h => ⟨t, h, .refl _, .inl rfl⟩⟩

/-- `Config.VirtualOf.eq_of_final`, same proof (the guard is not used). -/
theorem _root_.Kraken.Promising.Config.VirtualOfG.eq_of_final {G : PrepayGuard I} {A : Arch} {c v : Config I}
    (hf : c.final = true) (hv : c.VirtualOfG G A v) : v = c := by
  obtain ⟨hm, hs, ht⟩ := hv
  have hth : v.threads = c.threads := by
    apply Array.ext_getElem?
    intro i
    cases hc : c.threads[i]? with
    | none =>
      have : c.threads.size ≤ i := by simpa using hc
      simp [Array.getElem?_eq_none (show v.threads.size ≤ i by omega)]
    | some t =>
      obtain ⟨t', hv', hr, -⟩ := ht i t hc
      have hhalt : t.halted = true := by
        obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hc
        have := (Array.all_eq_true.mp hf) i hi
        simp only [Bool.and_eq_true] at this
        exact this.1
      have := ThreadNP.eq_of_halted hhalt hr
      simp only [Prod.mk.injEq] at this
      rw [hv', this.1]
  cases v; cases c
  simp_all

/-- `Config.VirtualOf` is the instance at the guard `GRF`. -/
theorem _root_.Kraken.Promising.Config.virtualOfG_GRF {A : Arch} {c v : Config I} :
    c.VirtualOfG GRF A v ↔ c.VirtualOf A v :=
  Iff.rfl

/-- A guard below `Thread.RelFulfils` gives `Config.VirtualOf`. -/
theorem _root_.Kraken.Promising.Config.VirtualOfG.toVirtualOf {G : PrepayGuard I} {A : Arch} {c v : Config I}
    (hG : ∀ A tid ts (t : Thread I) mem, G A tid ts t mem → t.RelFulfils A tid ts mem)
    (hv : c.VirtualOfG G A v) : c.VirtualOf A v := by
  obtain ⟨hm, hs, ht⟩ := hv
  refine ⟨hm, hs, fun i t hi => ?_⟩
  obtain ⟨t', h1, h2, h3⟩ := ht i t hi
  exact ⟨t', h1, h2, h3.imp_right fun ⟨ts, hts, h⟩ => ⟨ts, hts, hG _ _ _ _ _ h⟩⟩

/-- A path of machine steps `π 0 → π 1 → … → π L`, each a `succs` successor. -/
structure Path (A : Arch) (fuel : Nat) (I : ISA) where
  /-- The configurations; only indices `≤ L` matter. -/
  cfg : Nat → Config I
  /-- The number of steps. -/
  len : Nat
  step : ∀ j, j < len → cfg (j + 1) ∈ (succs A (cfg j) fuel).1

/-- The annotated micro-steps of Theorem 1′'s induction (option (B)); see the
module docstring. `rF`, `g` before, `rF'`, `g'` after. `K` is the K2 frame
of `NPSafeP` (`K2₀` in the existing `MicroStep`). -/
inductive MicroStep' (K : K2Frame (model I)) (A : Arch) : Config I → (Nat → Res) → Ghost → Config I → (Nat → Res) → Ghost → Prop
  /-- An `NPSafe` step of thread `s` (cases (a), (c), and the replay steps of
  (d1)): the conjuncts of `NPSafe`'s step conclusion. -/
  | np {c c' : Config I} {rF rF' : Nat → Res} {g g' : Ghost} (s : Nat) (t t' : Thread I) :
      c.threads[s]? = some t → NPStepBy A s c c' → c'.threads[s]? = some t' →
      (∀ i, i ≠ s → rF' i = rF i) → g.Le g' →
      (∀ ts, ts ∈ g.pend → Outstanding c' ts → ts ∈ g'.pend) →
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend) →
      (∀ x, mayWrite (rF' s) g' x → mayWrite (rF s) g x) →
      (∀ w, Written s c c' w → 0 < ((rF s).wr w.loc).q) →
      K g g' c.mem.last →
      (∀ b, b ≤ c.mem.last → max t'.views.vwNew t'.views.vCAP ≤ b →
        ∀ x, reachB (rF' s) g' x b → reachB (rF s) g x b) →
      MicroStep' K A c rF g c' rF' g'
  /-- A promise of thread `s` that transfers nothing (case (d2),
  `Erase.promise`): resources and ghost unchanged. -/
  | promise {c : Config I} {rF : Nat → Res} {g : Ghost} (s : Nat) (t : Thread I) (w : Msg) :
      c.threads[s]? = some t → Pred.Pure (g.rel w.loc) w.val →
      MicroStep' K A c rF g (Promised c s t w) rF g
  /-- A prepaid release promise of thread `s` (case (d1), `NPSafe`'s prepay
  conjunct): the conjuncts of the prepay conclusion. -/
  | prepay {c : Config I} {rF rF' : Nat → Res} {g g' : Ghost} (s : Nat) (t : Thread I) (w : Msg) :
      c.threads[s]? = some t →
      (∀ i, i ≠ s → rF' i = rF i) → g.Le g' →
      c.mem.last + 1 ∈ g'.pend → (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) →
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = c.mem.last + 1) →
      (∀ x, mayWrite (rF' s) g' x → mayWrite (rF s) g x) →
      K g g' c.mem.last →
      (∀ b, b ≤ c.mem.last → max t.views.vwNew t.views.vCAP ≤ b →
        ∀ x, reachB (rF' s) g' x b → reachB (rF s) g x b) →
      MicroStep' K A c rF g (Promised c s t w) rF' g'

/-- **An annotated run** of the path `π` (Theorem 1′'s induction, option
(B)); see the module docstring. `GV` is the virtual guard of
`Config.VirtualOfG`, `K` the K2 frame (`GRF`, `K2₀` in the existing
`AnnRun`). -/
structure AnnRun' (GV : PrepayGuard I) (K : K2Frame (model I)) (A : Arch) {fuel : Nat} (π : Path A fuel I) where
  /-- The number of micro-steps. -/
  N : Nat
  /-- Micro-configurations, thread resources, ghost states. -/
  cfg : Nat → Config I
  rF : Nat → Nat → Res
  g : Nat → Ghost
  /-- The micro-index of real index `j`. -/
  pos : Nat → Nat
  pos_zero : pos 0 = 0
  pos_mono : ∀ j, j < π.len → pos j ≤ pos (j + 1)
  pos_len : pos π.len = N
  /-- The first micro-configuration is the initial configuration. -/
  cfg_zero : cfg 0 = π.cfg 0
  /-- Validity-free erasure everywhere. -/
  erase : ∀ μ, μ ≤ N → Erase (rF μ) (g μ) (fun _ => True) (cfg μ)
  /-- Each micro-step is annotated. -/
  step : ∀ μ, μ < N → MicroStep' K A (cfg μ) (rF μ) (g μ) (cfg (μ + 1)) (rF (μ + 1)) (g (μ + 1))
  /-- At a real index, the micro-configuration is a virtual configuration. -/
  virtual : ∀ j, j ≤ π.len → (π.cfg j).VirtualOfG GV A (cfg (pos j))
  /-- Every micro-configuration has the memory of some real configuration. -/
  mem : ∀ μ, μ ≤ N → ∃ j, j ≤ π.len ∧ (cfg μ).mem = (π.cfg j).mem
  /-- Every thread state of a micro-configuration is a real thread state of
  the path with (some of) its promises: same views, fewer promises. -/
  real : ∀ μ, μ ≤ N → ∀ (s : Nat) (t : Thread I), (cfg μ).threads[s]? = some t →
    ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧ ∀ p ∈ t.prom, p ∈ tj.prom

/-- SLR's validity of the non-pending outstanding promises (`promValid` at
`T = ⊥`) at one configuration. -/
def Valid (c : Config I) (rF : Nat → Res) (g : Ghost) : Prop :=
  ∀ i t, c.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∉ g.pend → ∀ w, c.mem.get? ts = some w →
    mayWrite (rF i) g w.loc

/-- **Condition (3) of Theorem 1′** (**open**): every annotated run of a path
from `Config.init` of a
program to a final configuration is valid at every micro index (clean flag: `NPSafe`'s flag needs validity at the pre-state of every `np` and
`prepay` micro-step, hybrid replay configurations included). The argument:
on such a path every non-pending outstanding promise is fulfilled later by an
`np` micro-step of its owner, which owns the location then; `K1`/`K2` and the
machine facts of the path (every thread state is a real one, `AnnRun'.real`)
chase that permission back to the earlier index.

Theorem 1′ uses it at the final annotated run: validity at `pos j` gives
full erasure there, validity at every micro index keeps every thread's clean
flag `True` (`SLR/Theorem1Proof.lean`). Proved by `AnnRun'.valid` (
`SLR/Cond3Proof.lean`). -/
def Cond3' (GV : PrepayGuard I) (K : K2Frame (model I)) (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val)) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ R : AnnRun' GV K A π, ∀ μ, μ ≤ R.N → Valid (R.cfg μ) (R.rF μ) (R.g μ)

/-- Validity turns validity-free erasure into full erasure
(`Erase.validate_all`). -/
theorem Valid.erase {c : Config I} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} (E : Erase rF g T c)
    (hv : Valid c rF g) : Erase rF g (fun _ => False) c :=
  Erase.validate_all E hv

/-! ## The existing names: instances at `G₀`, `GRF`, `K2₀`

Each existing declaration keeps its statement; structures and the inductive
are abbreviations of the generic ones, with their constructors and fields
restated (see `SLR/NPSafePGen.lean`). -/

section Merged

/-- The annotated micro-steps of the existing chain: `MicroStep'` at `K2₀`. -/
abbrev MicroStep (A : Arch) : Config I → (Nat → Res) → Ghost → Config I → (Nat → Res) → Ghost → Prop :=
  MicroStep' (K2₀ (model I)) A

/-- An `NPSafe` step of thread `s` (cases (a), (c), and the replay steps of
(d1)): the conjuncts of `NPSafe`'s step conclusion. -/
theorem MicroStep.np {A : Arch} {c c' : Config I} {rF rF' : Nat → Res} {g g' : Ghost} (s : Nat) (t t' : Thread I) :
      c.threads[s]? = some t → NPStepBy A s c c' → c'.threads[s]? = some t' →
      (∀ i, i ≠ s → rF' i = rF i) → g.Le g' →
      (∀ ts, ts ∈ g.pend → Outstanding c' ts → ts ∈ g'.pend) →
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend) →
      (∀ x, mayWrite (rF' s) g' x → mayWrite (rF s) g x) →
      (∀ w, Written s c c' w → 0 < ((rF s).wr w.loc).q) →
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) →
      (∀ b, b ≤ c.mem.last → max t'.views.vwNew t'.views.vCAP ≤ b →
        ∀ x, reachB (rF' s) g' x b → reachB (rF s) g x b) →
      MicroStep A c rF g c' rF' g' :=
  MicroStep'.np (K := K2₀ (model I)) s t t'

/-- A promise of thread `s` that transfers nothing (case (d2),
`Erase.promise`): resources and ghost unchanged. -/
theorem MicroStep.promise {A : Arch} {c : Config I} {rF : Nat → Res} {g : Ghost} (s : Nat) (t : Thread I) (w : Msg) :
      c.threads[s]? = some t → Pred.Pure (g.rel w.loc) w.val →
      MicroStep A c rF g (Promised c s t w) rF g :=
  MicroStep'.promise (K := K2₀ (model I)) s t w

/-- A prepaid release promise of thread `s` (case (d1), `NPSafe`'s prepay
conjunct): the conjuncts of the prepay conclusion. -/
theorem MicroStep.prepay {A : Arch} {c : Config I} {rF rF' : Nat → Res} {g g' : Ghost} (s : Nat) (t : Thread I) (w : Msg) :
      c.threads[s]? = some t →
      (∀ i, i ≠ s → rF' i = rF i) → g.Le g' →
      c.mem.last + 1 ∈ g'.pend → (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) →
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = c.mem.last + 1) →
      (∀ x, mayWrite (rF' s) g' x → mayWrite (rF s) g x) →
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) →
      (∀ b, b ≤ c.mem.last → max t.views.vwNew t.views.vCAP ≤ b →
        ∀ x, reachB (rF' s) g' x b → reachB (rF s) g x b) →
      MicroStep A c rF g (Promised c s t w) rF' g' :=
  MicroStep'.prepay (K := K2₀ (model I)) s t w

/-- **An annotated run** of the existing chain: `AnnRun'` at `GRF`, `K2₀`. -/
abbrev AnnRun (A : Arch) {fuel : Nat} (π : Path A fuel I) : Type := AnnRun' GRF (K2₀ (model I)) A π

variable {A : Arch} {fuel : Nat} {π : Path A fuel I}

/-- The number of micro-steps. -/
abbrev AnnRun.N (self : AnnRun A π) : Nat := AnnRun'.N self
/-- Micro-configurations, thread resources, ghost states. -/
abbrev AnnRun.cfg (self : AnnRun A π) : Nat → Config I := AnnRun'.cfg self
abbrev AnnRun.rF (self : AnnRun A π) : Nat → Nat → Res := AnnRun'.rF self
abbrev AnnRun.g (self : AnnRun A π) : Nat → Ghost := AnnRun'.g self
/-- The micro-index of real index `j`. -/
abbrev AnnRun.pos (self : AnnRun A π) : Nat → Nat := AnnRun'.pos self
theorem AnnRun.pos_zero (self : AnnRun A π) : self.pos 0 = 0 := AnnRun'.pos_zero self
theorem AnnRun.pos_mono (self : AnnRun A π) : ∀ j, j < π.len → self.pos j ≤ self.pos (j + 1) :=
  AnnRun'.pos_mono self
theorem AnnRun.pos_len (self : AnnRun A π) : self.pos π.len = self.N := AnnRun'.pos_len self
/-- The first micro-configuration is the initial configuration. -/
theorem AnnRun.cfg_zero (self : AnnRun A π) : self.cfg 0 = π.cfg 0 := AnnRun'.cfg_zero self
/-- Validity-free erasure everywhere. -/
theorem AnnRun.erase (self : AnnRun A π) :
    ∀ μ, μ ≤ self.N → Erase (self.rF μ) (self.g μ) (fun _ => True) (self.cfg μ) :=
  AnnRun'.erase self
/-- Each micro-step is annotated. -/
theorem AnnRun.step (self : AnnRun A π) : ∀ μ, μ < self.N →
    MicroStep A (self.cfg μ) (self.rF μ) (self.g μ) (self.cfg (μ + 1)) (self.rF (μ + 1)) (self.g (μ + 1)) :=
  AnnRun'.step self
/-- At a real index, the micro-configuration is a virtual configuration. -/
theorem AnnRun.virtual (self : AnnRun A π) : ∀ j, j ≤ π.len → (π.cfg j).VirtualOf A (self.cfg (self.pos j)) :=
  AnnRun'.virtual self
/-- Every micro-configuration has the memory of some real configuration. -/
theorem AnnRun.mem (self : AnnRun A π) : ∀ μ, μ ≤ self.N → ∃ j, j ≤ π.len ∧ (self.cfg μ).mem = (π.cfg j).mem :=
  AnnRun'.mem self
/-- Every thread state of a micro-configuration is a real thread state of
the path with (some of) its promises: same views, fewer promises. -/
theorem AnnRun.real (self : AnnRun A π) : ∀ μ, μ ≤ self.N → ∀ (s : Nat) (t : Thread I), (self.cfg μ).threads[s]? = some t →
    ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧ ∀ p ∈ t.prom, p ∈ tj.prom :=
  AnnRun'.real self

/-- The constructor of `AnnRun`. -/
abbrev AnnRun.mk (N : Nat) (cfg : Nat → Config I) (rF : Nat → Nat → Res) (g : Nat → Ghost) (pos : Nat → Nat)
    (pos_zero : pos 0 = 0) (pos_mono : ∀ j, j < π.len → pos j ≤ pos (j + 1)) (pos_len : pos π.len = N)
    (cfg_zero : cfg 0 = π.cfg 0) (erase : ∀ μ, μ ≤ N → Erase (rF μ) (g μ) (fun _ => True) (cfg μ))
    (step : ∀ μ, μ < N → MicroStep A (cfg μ) (rF μ) (g μ) (cfg (μ + 1)) (rF (μ + 1)) (g (μ + 1)))
    (virtual : ∀ j, j ≤ π.len → (π.cfg j).VirtualOf A (cfg (pos j)))
    (mem : ∀ μ, μ ≤ N → ∃ j, j ≤ π.len ∧ (cfg μ).mem = (π.cfg j).mem)
    (real : ∀ μ, μ ≤ N → ∀ (s : Nat) (t : Thread I), (cfg μ).threads[s]? = some t →
      ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧ ∀ p ∈ t.prom, p ∈ tj.prom) :
    AnnRun A π :=
  AnnRun'.mk N cfg rF g pos pos_zero pos_mono pos_len cfg_zero erase step virtual mem real

end Merged

/-- **Condition (3) of Theorem 1′** (**open**): every annotated run of a path
from `Config.init` of a
program to a final configuration is valid at every micro index (clean flag: `NPSafe`'s flag needs validity at the pre-state of every `np` and
`prepay` micro-step, hybrid replay configurations included). The argument:
on such a path every non-pending outstanding promise is fulfilled later by an
`np` micro-step of its owner, which owns the location then; `K1`/`K2` and the
machine facts of the path (every thread state is a real one, `AnnRun.real`)
chase that permission back to the earlier index.

Theorem 1′ uses it at the final annotated run: validity at `pos j` gives
full erasure there, validity at every micro index keeps every thread's clean
flag `True` (`SLR/Theorem1Proof.lean`). Proved by `AnnRun.valid` (
`SLR/Cond3Proof.lean`). The generic form is `Cond3'`. -/
def Cond3 (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val)) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ R : AnnRun A π, ∀ μ, μ ≤ R.N → Valid (R.cfg μ) (R.rF μ) (R.g μ)

end Kraken.Promising.SLR

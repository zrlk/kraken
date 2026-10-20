/-
Theorem 1′ for the SLR-adapted model under option (B): the induction along a
live path (with the
(iii)-subsumes-(ii) changes).

## Structure

Fix `c` reachable from `c0 = Config.init states initMem` and live. Choose a
path `π` from `c0` through `c = π k` to a final `π L` (`Path.ofReachable2`).
The induction annotates `π` up to every real index `J` (`Inv`): a prefix run
(`PRun`, the annotated run of `SLR/Theorem1Run.lean` cut at `J`), and per
thread a safety token and an advancement status (`ThreadOk`). At `J = L` the
prefix run is a full `AnnRun`; `Cond3` makes it valid at `k`, and the
conclusion follows (`conclude`).

## Status

Proved: cases (a)/(c) (`caseNow`, with (O7) `liveWfProm`), (b)
(`step_stutter`), (d2) (`caseD2`, from (O5) `PromisePure`). Case (d1)
(`CaseD1`, O3: replay and prepay) is proved in `SLR/Theorem1D1.lean`
(`caseD1`), which imports this file. Main theorem here:
`theorem1II_of_cond3`, a `Theorem1IIPure` (`Theorem1II` plus the hypothesis
`PromisePure` on the initial ghost) from `Cond3` and `CaseD1`; the
`CaseD1`-free form is `theorem1II_pure` in `SLR/Theorem1D1.lean`.

## Generic chain

Everything above that mentions a guard or the K2 frame is stated with a
prime, generic in the prepay guard `G` (`NPSafeP`, `RelFulfilled'`,
`PromisePure'`), the virtual guard `GV` (`Status'`, `Config.VirtualOfG`) and
the K2 frame `K`; the virtual side uses `GuardOK GV` only. The existing names
keep their statements and are the instances at `G₀`, `GRF`, `K2₀` (end of
file, `SLR/NPSafePGen.lean`).

## Step guard

The per-thread token is `NPSafePS … S` (`SLR/NPSafeP.lean`): `NPSafeP` whose
step conjunct holds under a step guard `S`. The invariant (`ThreadOkP'`,
`ThreadOk'`, `Inv'`), the case `Prop`s and `StepInv'` carry `S`; the guard is
discharged only in `caseNow'` (`hstepful`: the stepping thread is not
advanced, or its step is the fulfilling `F`) and in the replay of `caseD1'`,
from `StepFulP`. At `S := StepGuard.top _` everything is the previous chain,
definitionally (`NPSafePS_top`), so the existing names are unchanged.
`Theorem1IIPureS'` is Theorem 1′ for step-guarded tokens; `Theorem1IIPure'`
keeps its statement (`Theorem1IIPureS'.toP`).

## Erasure and promise obligation

The micro-run carries an erasure `Er` (`PRun'`, `PRun'.Clean`), the tokens
are at `modelErase I Er`, and (O5) gives an obligation `Ob`
(`PromiseObl'`), with `ChainExt Er Ob` (see the section before the
invariant). `Theorem1IIPureXS'` is Theorem 1′ for them; at `Erase`, `ObPure`
everything is the previous chain, definitionally (`chainExt_Erase`).
-/
import Kraken.Promising.SLR.Theorem1Run
import Kraken.Promising.LiveWfProm
import Kraken.Promising.RelFulfilsLive
import Kraken.Promising.PromOrder

namespace Kraken.Promising.SLR

open Kraken.Promising.Live.Bridge (ReachableK)

variable {I : ISA}

/-! ## Paths -/

/-- Prepend a step to a path. -/
def Path.cons {A : Arch} {fuel : Nat} (c : Config I) (π : Path A fuel I) (h : π.cfg 0 ∈ (succs A c fuel).1) :
    Path A fuel I where
  cfg j := if j = 0 then c else π.cfg (j - 1)
  len := π.len + 1
  step j hj := by
    by_cases h0 : j = 0
    · subst h0; simpa using h
    · have := π.step (j - 1) (by omega)
      simp only [h0, ↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
      rwa [show j - 1 + 1 = j by omega] at this

/-- The path of length `0` at `c`. -/
def Path.single (A : Arch) (fuel : Nat) (c : Config I) : Path A fuel I where
  cfg _ := c
  len := 0
  step _ h := absurd h (Nat.not_lt_zero _)

/-- A reachable configuration is the end of a path. -/
theorem Path.ofReachable {A : Arch} {fuel : Nat} {c c' : Config I} (h : Reachable A fuel c c') :
    ∃ π : Path A fuel I, π.cfg 0 = c ∧ π.cfg π.len = c' := by
  induction h with
  | refl c => exact ⟨Path.single A fuel c, rfl, rfl⟩
  | @step c c₁ c₂ hs _ ih =>
    obtain ⟨π, h0, hl⟩ := ih
    refine ⟨Path.cons c π (h0 ▸ hs), rfl, ?_⟩
    simp [Path.cons, hl]

/-- A path from `c0` through `c` to `cf`. -/
theorem Path.ofReachable2 {A : Arch} {fuel : Nat} {c0 c cf : Config I} (h₁ : Reachable A fuel c0 c)
    (h₂ : Reachable A fuel c cf) :
    ∃ (π : Path A fuel I) (k : Nat), π.cfg 0 = c0 ∧ π.cfg k = c ∧ k ≤ π.len ∧ π.cfg π.len = cf := by
  induction h₁ with
  | refl c =>
    obtain ⟨π, h0, hl⟩ := Path.ofReachable h₂
    exact ⟨π, 0, h0, h0, Nat.zero_le _, hl⟩
  | @step c c₁ c₂ hs _ ih =>
    obtain ⟨π, k, h0, hk, hle, hl⟩ := ih h₂
    refine ⟨Path.cons c π (h0 ▸ hs), k + 1, rfl, ?_, by simp [Path.cons]; omega, ?_⟩
    · simp [Path.cons, hk]
    · simp [Path.cons, hl]

/-- Every configuration of a path is reachable from its first one. -/
theorem Path.reachable {A : Arch} {fuel : Nat} (π : Path A fuel I) :
    ∀ j, j ≤ π.len → Reachable A fuel (π.cfg 0) (π.cfg j) := by
  intro j
  induction j with
  | zero => intro _; exact .refl _
  | succ j ih =>
    intro hj
    exact Reachable.trans A fuel (ih (by omega)) (Reachable.step (π.step j (by omega)) (Reachable.refl _))

/-- Every configuration of a path reaches every later one. -/
theorem Path.reachBetween {A : Arch} {fuel : Nat} (π : Path A fuel I) {a b : Nat} (hab : a ≤ b) (hb : b ≤ π.len) :
    Reachable A fuel (π.cfg a) (π.cfg b) := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
  clear hab
  induction d with
  | zero => exact Reachable.refl _
  | succ d ih =>
    exact Reachable.trans A fuel (ih (by omega))
      (Reachable.step (π.step (a + d) (by omega)) (Reachable.refl _))

/-- Every configuration of a path is reaches its last one. -/
theorem Path.reaches {A : Arch} {fuel : Nat} (π : Path A fuel I) :
    ∀ j, j ≤ π.len → Reachable A fuel (π.cfg j) (π.cfg π.len) := by
  intro j hj
  obtain ⟨d, hd⟩ : ∃ d, π.len = j + d := ⟨π.len - j, by omega⟩
  rw [hd]
  clear hj
  induction d generalizing j with
  | zero => exact Reachable.refl _
  | succ d ih =>
    have h := ih (j + 1) (by omega)
    rw [show j + 1 + d = j + (d + 1) by omega] at h
    exact Reachable.step (π.step j (by omega)) h

/-! ## Machine facts along the path -/

section Machine

variable {A : Arch} {fuel : Nat}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

theorem Path.wf [I.LawfulState] (π : Path A fuel I) {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) : ∀ j, j ≤ π.len → (π.cfg j).Wf := fun j hj => by
  have h : (π.cfg 0).Wf := by rw [h0]; exact Config.init_wf _ _
  exact h.reachable (Reachable.toK (π.reachable j hj))

theorem Path.machInv [I.LawfulState] (π : Path A fuel I) {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) : ∀ j, j ≤ π.len → (π.cfg j).MachInv := fun j hj => by
  have h : (π.cfg 0).MachInv := by rw [h0]; exact Config.init_machInv _ _
  exact h.reachable (Reachable.toK (π.reachable j hj))

/-- Promise lists are sorted along the path (`Config.PromSorted`). -/
theorem Path.promSorted [I.LawfulState] (π : Path A fuel I) {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) : ∀ j, j ≤ π.len → (π.cfg j).PromSorted := fun j hj => by
  have h : (π.cfg 0).Wf := by rw [h0]; exact Config.init_wf _ _
  have hs : (π.cfg 0).PromSorted := by rw [h0]; exact Config.init_promSorted _ _
  exact hs.reachable h (Reachable.toK (π.reachable j hj))

/-- Memory only grows along the path. -/
theorem Path.mem_prefix [I.LawfulState] (π : Path A fuel I) {j j' : Nat} (hj : j ≤ j') (hj' : j' ≤ π.len) :
    (π.cfg j).mem.Prefix (π.cfg j').mem := by
  obtain ⟨d, rfl⟩ : ∃ d, j' = j + d := ⟨j' - j, by omega⟩
  clear hj
  induction d with
  | zero => exact Memory.Prefix.refl _
  | succ d ih =>
    refine (ih (by omega)).trans ?_
    have h := Reachable.step (π.step (j + d) (by omega)) (Reachable.refl (A := A) (fuel := fuel) _)
    exact h.mem_prefix

/-- The configurations of a path from a configuration that reaches a final
one are live. -/
theorem Path.live (π : Path A fuel I) (hf : (π.cfg π.len).final = true) :
    ∀ j, j ≤ π.len → (π.cfg j).Live A fuel := fun j hj => ⟨_, π.reaches j hj, hf⟩

/-- Restricting a thread to two memories agrees if none of its promises lies
between their ends. -/
theorem Thread.restrict_eq_of_gap {t : Thread I} {M M' : Memory}
    (h : ∀ p ∈ t.prom, p ≤ M.last ∨ M'.last < p) (hle : M.last ≤ M'.last) : t.restrict M' = t.restrict M := by
  unfold Thread.restrict
  congr 1
  apply List.filter_congr
  intro p hp
  rcases h p hp with h | h
  · simp only [decide_eq_decide]; omega_t
  · simp only [decide_eq_decide]; omega_t

/-- **(S1′) with the advanced state exposed** (`Config.advanceable_of_path`,
whose statement hides it): the thread advances to its state on the path,
restricted to the current memory. -/
theorem advanceable_of_pathG' {GV : PrepayGuard I} (GVOK : GuardOK GV) {c0 c c1 : Config I}
    (h0 : c0.Wf) (hc : ReachableK A c0 c) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t)
    {ts : Time} (hts : ts ∈ t.prom) (hr : ReachableK A c c1) {t1 : Thread I}
    (ht1 : c1.threads[tid]? = some t1) (hts1 : ts ∈ t1.prom) (hrel : GV A tid ts t1 c1.mem)
    (hnt : t1.NoNTStores ts) (hnx : t1.NextNoNT A) :
    ThreadNP A tid (t, c.mem) (t1.restrict c.mem, c.mem) ∧ ts ∈ (t1.restrict c.mem).prom ∧
      GV A tid ts (t1.restrict c.mem) c.mem := by
  have hwf := h0.reachable hc
  have hwf1 := hwf.reachable hr
  have hf1 := (hwf1 tid t1 ht1).1
  have hle : ts ≤ c.mem.last := (hwf tid t ht).2 ts hts
  have hb := GVOK.relPre_lt hrel hf1
  have hnp0 : ThreadNP A tid (t, c.mem) (t.restrict c.mem, c.mem) := by
    rw [Thread.restrict_eq (hwf tid t ht).2]; exact .refl _
  have hnt' : t1.views.vwOldNT ≤ c.mem.last := by rcases hnt with h | h <;> omega_t
  exact ⟨advance_path ht1 (Nat.le_of_lt (Nat.lt_of_lt_of_le hb hle)) hr hwf (.refl _) ht hnp0 (.inr (by omega_t)),
    List.mem_filter.mpr ⟨hts1, by simpa using hle⟩, GVOK.restrict hr.mem_prefix hle hf1 hrel hnt' hnx⟩

end Machine

/-! ## The erasure and the promise obligation

The chain is generic in the erasure `Er` carried by the micro-run and asked
of the tokens' environment (`modelErase I Er`: `model I` with `erase := Er`),
and in the obligation `Ob` that (O5) gives for the promises not fulfilled by
a release store (`PromiseObl'`). `ChainExt Er Ob` is what the chain needs of
them: `Er` refines `Erase`, can be re-targeted to another exemption set along
`Erase`, and survives a `promise` micro-step whose message meets `Ob`, which
in turn makes the message pure. The existing chain is the instance at `Erase`
and `ObPure` (`chainExt_Erase`): `modelErase I Erase` is `model I` and
`PromiseObl' … (ObPure rel)` is `PromisePure' … rel`, definitionally. -/

/-- The type of an erasure (`ResModel.erase` of `model I`). -/
abbrev ErasureP (I : ISA) : Type := (Nat → Res) → Ghost → (Nat → Prop) → Config I → Prop

/-- `model I` with the erasure `Er`. -/
def modelErase (I : ISA) (Er : ErasureP I) : ResModel I := { model I with erase := Er }

theorem modelErase_Erase : modelErase I Erase = model I := rfl

/-- The type of a promise obligation: release predicates, the memory before
the promise, the promised message. -/
abbrev PromiseOb : Type := (Loc → Pred) → Memory → Msg → Prop

/-- The existing obligation: the message is pure for its release predicate. -/
abbrev ObPure : PromiseOb := fun rel _ w => Pred.Pure (rel w.loc) w.val

/-- **What the chain needs of an erasure `Er` and an obligation `Ob`** (see
the section docstring). -/
structure ChainExt (Er : ErasureP I) (Ob : PromiseOb) : Prop where
  toErase : ∀ {rF g T c}, Er rF g T c → Erase rF g T c
  retarget : ∀ {rF g T T' c}, Er rF g T c → Erase rF g T' c → Er rF g T' c
  pure : ∀ {rel mem w}, Ob rel mem w → Pred.Pure (rel w.loc) w.val
  promise : ∀ {rF g T c tid t w}, Er rF g T c → c.threads[tid]? = some t →
    Erase rF g T (Promised c tid t w) → Ob g.rel c.mem { w with tid } → Er rF g T (Promised c tid t w)

/-- The existing instance. -/
theorem chainExt_Erase : ChainExt (I := I) Erase ObPure where
  toErase h := h
  retarget _ h := h
  pure h := h
  promise _ _ h _ := h

/-! ## The induction invariant -/

section Invariant

variable (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I) (S : StepGuard (modelErase I Er)) (A : Arch) {fuel : Nat} (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost)

/-- **A prefix run** up to real index `J`: `AnnRun'` cut at `J`, plus the
world facts of the initial ghost (`le0`) and the postconditions of the
threads that are done at each real index (`doneB`, from their tokens), as
long as the run was valid before that index (the clean flags). -/
structure PRun' (J : Nat) where
  N : Nat
  cfg : Nat → Config I
  rF : Nat → Nat → Res
  g : Nat → Ghost
  pos : Nat → Nat
  pos_zero : pos 0 = 0
  pos_mono : ∀ j, j < J → pos j ≤ pos (j + 1)
  pos_J : pos J = N
  cfg_zero : cfg 0 = π.cfg 0
  erase : ∀ μ, μ ≤ N → Er (rF μ) (g μ) (fun _ => True) (cfg μ)
  step : ∀ μ, μ < N → MicroStep' K A (cfg μ) (rF μ) (g μ) (cfg (μ + 1)) (rF (μ + 1)) (g (μ + 1))
  virtual : ∀ j, j ≤ J → (π.cfg j).VirtualOfG GV A (cfg (pos j))
  mem : ∀ μ, μ ≤ N → ∃ j, j ≤ π.len ∧ (cfg μ).mem = (π.cfg j).mem
  real : ∀ μ, μ ≤ N → ∀ (s : Nat) (t : Thread I), (cfg μ).threads[s]? = some t →
    ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧
      ∀ p ∈ t.prom, p ∈ tj.prom
  le0 : ∀ μ, μ ≤ N → g0.Le (g μ)
  doneB : ∀ j, j ≤ J → (∀ μ, μ < pos j → Er (rF μ) (g μ) (fun _ => False) (cfg μ)) →
    ∀ tid, (cfg (pos j)).Done tid → B (cfg (pos j)) (rF (pos j) tid) (g (pos j))

/-- Micro-indices of real indices `≤ J` are `≤ N`. -/
theorem PRun'.pos_le {J : Nat} (R : PRun' GV K Er A π B g0 J) : ∀ j, j ≤ J → R.pos j ≤ R.N := by
  intro j hj
  rw [← R.pos_J]
  obtain ⟨d, hd⟩ : ∃ d, J = j + d := ⟨J - j, by omega⟩
  have key : ∀ d j, j + d ≤ J → R.pos j ≤ R.pos (j + d) := by
    intro d
    induction d with
    | zero => intro j _; exact Nat.le_refl _
    | succ d ih =>
      intro j h
      exact Nat.le_trans (ih j (by omega)) (by rw [← Nat.add_assoc]; exact R.pos_mono _ (by omega))
  have := key d j (by omega)
  rw [← hd] at this
  exact this

/-- A full prefix run is an annotated run. -/
def PRun'.toAnnRun (R : PRun' GV K Er A π B g0 π.len) {Ob : PromiseOb} (ErOK : ChainExt Er Ob) : AnnRun' GV K A π where
  N := R.N
  cfg := R.cfg
  rF := R.rF
  g := R.g
  pos := R.pos
  pos_zero := R.pos_zero
  pos_mono := R.pos_mono
  pos_len := R.pos_J
  cfg_zero := R.cfg_zero
  erase := fun μ h => ErOK.toErase (R.erase μ h)
  step := R.step
  virtual := R.virtual
  mem := R.mem
  real := R.real

/-- The advancement status of thread `i` at real index `J`, with target
index `p` and virtual state `v.threads[i]`:

- *not advanced*: `p = J`, the virtual thread is the real one, and no
  promise of `i` is pending;
- *advanced*: `F`, the instruction at real step `p ≥ J` of `π`, is an
  instruction of `i` that fulfils a pending promise `ts` (prepaid), which is
  outstanding at every index in `[J, p]` and which `F` can fulfil as the
  virtual guard `GV` says (a release store, `Thread.RelFulfils`, in the
  existing `Status`); the virtual thread is `i`'s real state
  at `p`, restricted to the memory at `J`. All pending promises of `i` are
  fulfilled by `F`. -/
def Status' (J : Nat) (v : Config I) (g : Ghost) (i p : Nat) : Prop :=
  (p = J ∧ v.threads[i]? = (π.cfg J).threads[i]? ∧
      ∀ t, v.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∉ g.pend) ∨
  (p < π.len ∧ ∃ tp, (π.cfg p).threads[i]? = some tp ∧ v.threads[i]? = some (tp.restrict (π.cfg J).mem) ∧
    (∃ ts ∈ g.pend, ts ∈ tp.prom ∧ G A i ts tp (π.cfg p).mem ∧
      ∀ q, J ≤ q → q ≤ p → ∃ tq, (π.cfg q).threads[i]? = some tq ∧ ts ∈ tq.prom) ∧
    (∃ tp', (π.cfg (p + 1)).threads[i]? = some tp' ∧ NPStepBy A i (π.cfg p) (π.cfg (p + 1)) ∧
      ∀ ts ∈ g.pend, ts ∈ tp.prom → ts ∉ tp'.prom))

/-- **Thread `i` is in order at real index `J`** (components (I1), (I3), (I5) of
the invariant): a safety token (`NPSafe` at a saved
configuration `s`, ghost `gs`, from which the current virtual configuration
`v` is an environment extension, with clean flag `cl`), the own-pending
condition at `v`, the step-index budget, and the advancement status. -/
def ThreadOkP' (J : Nat) (cl : Prop) (v : Config I) (rF : Nat → Res) (g : Ghost) (i p : Nat) : Prop :=
  ∃ (s : Config I) (gs : Ghost) (n : Nat), J ≤ p ∧ p ≤ π.len ∧
    NPSafePS (modelErase I Er) A B i G K S (n + 1) 0 cl s (rF i) gs ∧ EnvExt i s v ∧ gs.Le g ∧
    (∀ t, v.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ gs.pend) ∧
    (π.len - p) + (π.len - J) < n ∧
    Status' GV A π J v g i p

/-- `ThreadOkP'` for some target index `p`. -/
def ThreadOk' (J : Nat) (cl : Prop) (v : Config I) (rF : Nat → Res) (g : Ghost) (i : Nat) : Prop :=
  ∃ p, ThreadOkP' G GV K Er S A π B J cl v rF g i p

/-- The prefix run is valid (full erasure) at every micro-index below `μ'`:
the clean flag of every token at `μ'`. -/
def PRun'.Clean {J : Nat} (R : PRun' GV K Er A π B g0 J) (μ' : Nat) : Prop :=
  ∀ μ, μ < μ' → Er (R.rF μ) (R.g μ) (fun _ => False) (R.cfg μ)

/-- **The invariant at real index `J`**: a prefix run and every thread in
order at its last micro-configuration, its token's clean flag being the
validity of the run so far. -/
def Inv' (J : Nat) : Prop :=
  ∃ R : PRun' GV K Er A π B g0 J, ∀ i, i < (R.cfg R.N).threads.size →
    ThreadOk' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i

end Invariant

/-! ## The initial invariant and the conclusion -/

theorem Config.init_threads_prom {states : List I.State} {initMem : List (Loc × Val)} {i : Nat} {t : Thread I}
    (h : (Config.init states initMem : Config I).threads[i]? = some t) : t.prom = [] := by
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  rfl

/-- **`Inv' 0`**: the initial configuration, the initial resources and ghost,
every thread's token at `Config.init` with a large enough index. -/
theorem inv_zero' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) {A : Arch} {fuel : Nat} (π : Path A fuel I) {B : Config I → Res → Ghost → Prop}
    {states : List I.State} {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem)
    {rF : Nat → Res} {g : Ghost} (E : Er rF g (fun _ => False) (Config.init states initMem))
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafePS (modelErase I Er) A B tid G K S n m True (Config.init states initMem) (rF tid) g) :
    Inv' G GV K Er S A π B g 0 := by
  let c0 : Config I := Config.init states initMem
  have hsize : c0.threads.size = states.length := by simp [c0, Config.init]
  have hdone : ∀ tid, c0.Done tid → B c0 (rF tid) g := fun tid hd => by
    have ⟨_, ht, _⟩ := hd
    exact NPSafePS.done (hsafe tid (hsize ▸ lt_size_of_get? ht) 2 0) (EnvExt.refl _ _) (Ghost.Le.refl g) trivial hd
  refine ⟨{
    N := 0, cfg := fun _ => c0, rF := fun _ => rF, g := fun _ => g, pos := fun _ => 0
    pos_zero := rfl
    pos_mono := fun _ h => absurd h (Nat.not_lt_zero _)
    pos_J := rfl
    cfg_zero := h0.symm
    erase := fun _ _ => ErOK.retarget E ((ErOK.toErase E).weaken fun _ h => h.elim)
    step := fun _ h => absurd h (Nat.not_lt_zero _)
    virtual := fun j hj => by
      obtain rfl : j = 0 := by omega
      rw [h0]; exact Config.VirtualOfG.refl GV A _
    mem := fun _ _ => ⟨0, Nat.zero_le _, by rw [h0]⟩
    real := fun _ _ s t ht => ⟨0, t, Nat.zero_le _, by rw [h0]; exact ht, rfl, fun _ h => h⟩
    le0 := fun _ _ => Ghost.Le.refl g
    doneB := fun _ _ _ tid hd => hdone tid hd }, fun i hi => ?_⟩
  refine ⟨0, c0, g, 2 * π.len + 1, Nat.le_refl _, Nat.zero_le _,
    NPSafePS.mono_flag (fun _ => trivial) (hsafe i (hsize ▸ hi) _ 0), EnvExt.refl _ _,
    Ghost.Le.refl g, fun t ht ts hts => by simp [Config.init_threads_prom ht] at hts, by omega, ?_⟩
  refine .inl ⟨rfl, (congrArg (fun c : Config I => c.threads[i]?) h0).symm,
    fun t ht ts hts => by simp [Config.init_threads_prom ht] at hts⟩

/-- **The conclusion** from a full prefix run and condition (3): at real
index `k`, the micro-configuration is a virtual configuration with full
erasure, the initial world facts, and the postconditions of done threads. -/
theorem conclude' {GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) {A : Arch} {fuel : Nat} [I.LawfulState] (π : Path A fuel I) {B : Config I → Res → Ghost → Prop}
    {g0 : Ghost} {states : List I.State} {initMem : List (Loc × Val)} (h3 : Cond3' GV K A fuel states initMem)
    (h0 : π.cfg 0 = Config.init states initMem) (hf : (π.cfg π.len).final = true)
    (R : PRun' GV K Er A π B g0 π.len) {k : Nat} (hk : k ≤ π.len) :
    ∃ v rF' g', (π.cfg k).VirtualOfG GV A v ∧ Er rF' g' (fun _ => False) v ∧ g0.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' := by
  have hpos : R.pos k ≤ R.N := R.pos_le GV K Er A π B g0 k hk
  have hfull : ∀ μ, μ ≤ R.N → Er (R.rF μ) (R.g μ) (fun _ => False) (R.cfg μ) := fun μ hμ =>
    ErOK.retarget (R.erase μ hμ)
      (Valid.erase (ErOK.toErase (R.erase μ hμ)) (h3 π h0 hf (R.toAnnRun GV K Er A π B g0 ErOK) μ hμ))
  exact ⟨R.cfg (R.pos k), R.rF (R.pos k), R.g (R.pos k), R.virtual k hk, hfull _ hpos,
    R.le0 _ hpos, R.doneB k hk fun μ hμ => hfull μ (by omega)⟩

/-! ## The step of the induction: frames and the stutter case -/

section Step

variable {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {A : Arch} {fuel : Nat}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **The status of a thread that does not step** (frame): if the real step
`J → J + 1` leaves thread `i` unchanged, the virtual thread `i` is unchanged,
pending marks of `i`'s promises are kept while they are outstanding and none
are created, and restriction to the new memory agrees with restriction to the
old one on `i`'s later states (the new messages are not `i`'s), then `i`'s
status carries over to `J + 1`: a not-advanced thread stays not advanced, an
advanced one keeps its target (which is not `J`: its target step changes it). -/
theorem status_frameG [I.LawfulState] {π : Path A fuel I} {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J < π.len)
    {v v' : Config I} {g g' : Ghost} {i p : Nat}
    (hthr : (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]?)
    (hvv : v'.threads[i]? = v.threads[i]?)
    (hkeep : ∀ ts ∈ g.pend, (∃ t, v'.threads[i]? = some t ∧ ts ∈ t.prom) → ts ∈ g'.pend)
    (hback : ∀ ts ∈ g'.pend, ts ∈ g.pend)
    (hrestr : ∀ q tq, J < q → q ≤ π.len → (π.cfg q).threads[i]? = some tq →
      tq.restrict (π.cfg (J + 1)).mem = tq.restrict (π.cfg J).mem)
    (hJp : J ≤ p) (hst : Status' GV A π J v g i p) :
    ∃ p', J + 1 ≤ p' ∧ p' ≤ π.len ∧ (π.len - p') + (π.len - (J + 1)) ≤ (π.len - p) + (π.len - J) ∧
      Status' GV A π (J + 1) v' g' i p' := by
  rcases hst with ⟨hpJ, hv, hnp⟩ | ⟨hpl, tp, htp, hv, ⟨ts, hpend, htsp, hrel, hq⟩, ⟨tp', htp', hnps, hful⟩⟩
  · refine ⟨J + 1, Nat.le_refl _, hJ, by omega, .inl ⟨rfl, by rw [hvv, hv, hthr], fun t ht ts hts hp => ?_⟩⟩
    exact hnp t (by rw [← hvv]; exact ht) ts hts (hback ts hp)
  · have hpJ : J ≠ p := by
      rintro rfl
      rw [hthr, htp] at htp'
      cases htp'
      exact hful ts hpend htsp htsp
    refine ⟨p, by omega, Nat.le_of_lt hpl, by omega, .inr ⟨hpl, tp, htp, ?_,
      ⟨ts, ?_, htsp, hrel, fun q h1 h2 => hq q (by omega) h2⟩,
      ⟨tp', htp', hnps, fun ts' h' => hful ts' (hback ts' h')⟩⟩⟩
    · rw [hvv, hv, hrestr p tp (by omega) (Nat.le_of_lt hpl) htp]
    · apply hkeep ts hpend
      obtain ⟨tJ, htJ, htsJ⟩ := hq J (Nat.le_refl _) hJp
      have hle := ((π.wf h0 J (by omega)) i tJ htJ).2 ts htsJ
      refine ⟨tp.restrict (π.cfg J).mem, by rw [hvv, hv], ?_⟩
      simp only [Thread.restrict]
      exact List.mem_filter.mpr ⟨htsp, by simpa using hle⟩



/-- **The postcondition of a done thread** from its token: the budget leaves
at least one step index, so the token's Done conjunct applies at `v`, under
the clean flag. -/
theorem ThreadOkP'.done {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {J : Nat} {cl : Prop}
    {v : Config I} {rF : Nat → Res} {g : Ghost} {i p : Nat} (h : ThreadOkP' G GV K Er S A π B J cl v rF g i p)
    (hcl : cl) (hd : v.Done i) : B v (rF i) g := by
  obtain ⟨s, gs, n, -, -, hsafe, hext, hgs, -, hbud, -⟩ := h
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact NPSafePS.done hsafe hext hgs hcl hd

/-- The clean flag of a thread's token may be strengthened. -/
theorem ThreadOkP'.mono_flag {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {J : Nat} {cl cl' : Prop}
    {v : Config I} {rF : Nat → Res} {g : Ghost} {i p : Nat} (h : ThreadOkP' G GV K Er S A π B J cl v rF g i p)
    (hc : cl' → cl) : ThreadOkP' G GV K Er S A π B J cl' v rF g i p := by
  obtain ⟨s, gs, n, h1, h2, hsafe, rest⟩ := h
  exact ⟨s, gs, n, h1, h2, NPSafePS.mono_flag hc hsafe, rest⟩

/-- **(O7) Live configurations have no dead promise**: on a path to a final
configuration every outstanding promise is fulfilled by its thread, above the
thread's `coh` of its location, `vwNew` and `vCAP`, which only grow. Proved
(`liveWfProm`, from `Config.Live.wfProm` in `Promising/LiveWfProm.lean`). -/
def LiveWfProm (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (states : List I.State) (initMem : List (Loc × Val)) (c : Config I),
    Reachable A fuel (Config.init states initMem) c → c.Live A fuel → ∀ i, c.WfProm i

theorem liveWfProm [I.LawfulState] (A : Arch) (fuel : Nat) : LiveWfProm (I := I) A fuel :=
  fun _ _ _ _ hl i => hl.wfProm i

/-- **Restriction frame**: if the messages a real step `J → J + 1` appends
are thread `j`'s, the later states of another thread restrict to the new
memory as to the old one (none of its promises lies in between). -/
theorem restrict_frame [I.LawfulState] {π : Path A fuel I} {states : List I.State}
    {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J < π.len)
    {j : Nat} (hnew : ∀ ts w, (π.cfg J).mem.last < ts → (π.cfg (J + 1)).mem.get? ts = some w → w.tid = j)
    (i : Nat) (hij : i ≠ j) :
    ∀ (q : Nat) (tq : Thread I), J < q → q ≤ π.len → (π.cfg q).threads[i]? = some tq →
      tq.restrict (π.cfg (J + 1)).mem = tq.restrict (π.cfg J).mem := by
  intro q tq hq hql htq
  apply Thread.restrict_eq_of_gap _ (π.mem_prefix (Nat.le_succ J) hJ).last_le
  intro p hp
  by_cases h1 : p ≤ (π.cfg J).mem.last
  · exact .inl h1
  · by_cases h2 : (π.cfg (J + 1)).mem.last < p
    · exact .inr h2
    · exfalso
      obtain ⟨w, hw, htw⟩ := (π.machInv h0 q hql).promWf i tq htq p hp
      rw [(π.mem_prefix (show J + 1 ≤ q by omega) hql).get? (by omega_t)] at hw
      exact hij (htw.symm.trans (hnew p w (by omega_t) hw))

/-- **A thread of the virtual configuration is a real state restricted to
the memory at `J`**: the state at `J` itself (not advanced) or at the target
(advanced). -/
theorem Status'.restrictOf [I.LawfulState] {π : Path A fuel I} {states : List I.State}
    {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J ≤ π.len)
    {v : Config I} {g : Ghost} {i p : Nat} (hp : p ≤ π.len) (hJp : J ≤ p) (hst : Status' GV A π J v g i p)
    {t : Thread I} (ht : v.threads[i]? = some t) :
    ∃ (q : Nat) (tq : Thread I), J ≤ q ∧ q ≤ π.len ∧ (π.cfg q).threads[i]? = some tq ∧
      t = tq.restrict (π.cfg J).mem := by
  rcases hst with ⟨-, hv, -⟩ | ⟨-, tp, htp, hv, -⟩
  · rw [hv] at ht
    refine ⟨J, t, Nat.le_refl _, hJ, ht, ?_⟩
    rw [Thread.restrict_eq ((π.wf h0 J hJ) i t ht).2]
  · rw [hv] at ht; cases ht
    exact ⟨p, tp, hJp, hp, htp, rfl⟩

/-- **(O7, part) The machine invariants of a virtual configuration**: every
thread is a real state at a later index restricted to the memory at `J`
(`Status'.restrictOf`); restriction keeps the views and the promises up to
`|M|`, the memory is the real one at `J`, a prefix of the later ones. -/
theorem machInv_of_restrict [I.LawfulState] {π : Path A fuel I} {states : List I.State}
    {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem) {J : Nat}
    {v : Config I} (hmem : v.mem = (π.cfg J).mem)
    (hr : ∀ (i : Nat) (t : Thread I), v.threads[i]? = some t →
      ∃ (q : Nat) (tq : Thread I), J ≤ q ∧ q ≤ π.len ∧ (π.cfg q).threads[i]? = some tq ∧ t = tq.restrict (π.cfg J).mem) :
    v.MachInv := by
  have key : ∀ (i : Nat) (t : Thread I), v.threads[i]? = some t → t.Inv i v.mem := by
    intro i t ht
    obtain ⟨q, tq, hJq, hq, htq, rfl⟩ := hr i t ht
    have hI := (π.machInv h0 q hq).thread htq
    have hpre := π.mem_prefix hJq hq
    rw [hmem]
    refine ⟨fun p hp => ?_, ?_, fun ts w hw htw hts => ?_⟩
    · simp only [Thread.restrict, List.mem_filter, decide_eq_true_eq] at hp
      obtain ⟨w, hw, htw⟩ := hI.prom p hp.1
      exact ⟨w, by rw [← hpre.get? hp.2]; exact hw, htw⟩
    · exact hI.nodup.filter _
    · have hle : ts ≤ (π.cfg J).mem.last := (π.cfg J).mem.last_le_of_get?_eq_some hw
      have hts' : ts ∉ tq.prom := fun h => hts (by
        simp only [Thread.restrict, List.mem_filter, decide_eq_true_eq]; exact ⟨h, hle⟩)
      exact hI.own ts w (by rw [hpre.get? hle]; exact hw) htw hts'
  exact ⟨fun i t ht => (key i t ht).prom, fun i t ht => (key i t ht).nodup, fun i t ht => (key i t ht).own⟩

/-- **The virtual configuration from the statuses**: same memory and size as
the real configuration at `J`; a not-advanced thread is the real one, an
advanced one is the real one advanced ((S1′), `advanceable_of_pathG'`). -/
theorem virtual_of_status' [I.LawfulState] (GVOK : GuardOK GV) {π : Path A fuel I} {states : List I.State}
    {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem)
    (hNT : ∀ j, j ≤ π.len → (π.cfg j).NTFree A) {J : Nat} (hJ : J ≤ π.len) {v : Config I} {g : Ghost}
    (hmem : v.mem = (π.cfg J).mem) (hsize : v.threads.size = (π.cfg J).threads.size)
    (hst : ∀ i, i < v.threads.size → ∃ p, J ≤ p ∧ Status' GV A π J v g i p) :
    (π.cfg J).VirtualOfG GV A v := by
  have hwf0 : (π.cfg 0).Wf := by rw [h0]; exact Config.init_wf _ _
  refine ⟨hmem, hsize, fun i ti hti => ?_⟩
  obtain ⟨p, hJp, hs⟩ := hst i (by rw [hsize]; exact lt_size_of_get? hti)
  rcases hs with ⟨-, hv, -⟩ | ⟨hpl, tp, htp, hv, ⟨ts, -, htsp, hrel, hq⟩, -⟩
  · exact ⟨ti, by rw [hv, hti], .refl _, .inl rfl⟩
  · obtain ⟨tJ, htJ, htsJ⟩ := hq J (Nat.le_refl _) hJp
    rw [hti] at htJ; cases htJ
    have hpl' := Nat.le_of_lt hpl
    obtain ⟨hnp, hts', hrel'⟩ := advanceable_of_pathG' GVOK hwf0 (Reachable.toK (π.reachable J hJ)) hti htsJ
      (Reachable.toK (π.reachBetween hJp hpl')) htp htsp hrel ((hNT p hpl' i tp htp).1 ts) (hNT p hpl' i tp htp).2
    exact ⟨_, hv, hnp, .inr ⟨ts, hts', hrel'⟩⟩

/-- **Extend a prefix run by one micro-step** to the next real index: the
new micro-configuration `c'` is the virtual configuration at `J + 1`. The
postconditions of done threads at `c'` are asked under the validity of the
extended run (`R.Clean R.N` and full erasure at the old last configuration). -/
def PRun'.snoc {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}
    (R : PRun' GV K Er A π B g0 J) (c' : Config I) (rF' : Nat → Res) (g' : Ghost)
    (E : Er rF' g' (fun _ => True) c') (hstep : MicroStep' K A (R.cfg R.N) (R.rF R.N) (R.g R.N) c' rF' g')
    (hV : (π.cfg (J + 1)).VirtualOfG GV A c') (hmem : ∃ j, j ≤ π.len ∧ c'.mem = (π.cfg j).mem)
    (hreal : ∀ (s : Nat) (t : Thread I), c'.threads[s]? = some t →
      ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧
        ∀ p ∈ t.prom, p ∈ tj.prom)
    (hle : g0.Le g')
    (hdone : R.Clean GV K Er A π B g0 R.N ∧ Er (R.rF R.N) (R.g R.N) (fun _ => False) (R.cfg R.N) →
      ∀ tid, c'.Done tid → B c' (rF' tid) g') : PRun' GV K Er A π B g0 (J + 1) where
  N := R.N + 1
  cfg μ := if μ ≤ R.N then R.cfg μ else c'
  rF μ := if μ ≤ R.N then R.rF μ else rF'
  g μ := if μ ≤ R.N then R.g μ else g'
  pos k := if k ≤ J then R.pos k else R.N + 1
  pos_zero := by simp [R.pos_zero]
  pos_mono k hk := by
    by_cases h : k + 1 ≤ J
    · simp only [show k ≤ J by omega, h, ↓reduceIte]; exact R.pos_mono k (by omega)
    · simp only [show k ≤ J by omega, h, ↓reduceIte]; rw [show k = J by omega, R.pos_J]; omega
  pos_J := by simp only [show ¬ (J + 1 ≤ J) by omega, ↓reduceIte]
  cfg_zero := by simp only [Nat.zero_le, ↓reduceIte]; exact R.cfg_zero
  erase μ hμ := by
    by_cases h : μ ≤ R.N
    · simp only [h, ↓reduceIte]; exact R.erase μ h
    · simp only [h, ↓reduceIte]; exact E
  step μ hμ := by
    by_cases h : μ + 1 ≤ R.N
    · simp only [show μ ≤ R.N by omega, h, ↓reduceIte]; exact R.step μ (by omega)
    · obtain rfl : μ = R.N := by omega
      simp only [Nat.le_refl, h, ↓reduceIte]; exact hstep
  virtual k hk := by
    by_cases h : k ≤ J
    · simp only [h, R.pos_le GV K Er A π B g0 k h, ↓reduceIte]; exact R.virtual k h
    · obtain rfl : k = J + 1 := by omega
      simp only [h, show ¬ (R.N + 1 ≤ R.N) by omega, ↓reduceIte]; exact hV
  mem μ hμ := by
    by_cases h : μ ≤ R.N
    · simp only [h, ↓reduceIte]; exact R.mem μ h
    · simp only [h, ↓reduceIte]; exact hmem
  real μ hμ := by
    by_cases h : μ ≤ R.N
    · simp only [h, ↓reduceIte]; exact R.real μ h
    · simp only [h, ↓reduceIte]; exact hreal
  le0 μ hμ := by
    by_cases h : μ ≤ R.N
    · simp only [h, ↓reduceIte]; exact R.le0 μ h
    · simp only [h, ↓reduceIte]; exact hle
  doneB k hk hc tid hd := by
    by_cases h : k ≤ J
    · simp only [h, R.pos_le GV K Er A π B g0 k h, ↓reduceIte] at hc hd ⊢
      refine R.doneB k h (fun μ hμ => ?_) tid hd
      have := hc μ hμ
      simp only [show μ ≤ R.N from Nat.le_trans (Nat.le_of_lt hμ) (R.pos_le GV K Er A π B g0 k h), ↓reduceIte] at this
      exact this
    · simp only [h, show ¬ (R.N + 1 ≤ R.N) by omega, ↓reduceIte] at hc hd ⊢
      refine hdone ⟨fun μ hμ => ?_, ?_⟩ tid hd
      · have := hc μ (by omega)
        simp only [show μ ≤ R.N by omega, ↓reduceIte] at this
        exact this
      · have := hc R.N (by omega)
        simp only [Nat.le_refl, ↓reduceIte] at this
        exact this

/-- The validity of the extended run gives the validity of the old one and
full erasure at its last configuration (the clean flag of a token that took
the new micro-step). -/
theorem PRun'.snoc_clean {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}
    (R : PRun' GV K Er A π B g0 J) {c' : Config I} {rF' : Nat → Res} {g' : Ghost} {E hstep hV hmem hreal hle hdone}
    (h : (R.snoc c' rF' g' E hstep hV hmem hreal hle hdone).Clean GV K Er A π B g0 (R.N + 1)) :
    R.Clean GV K Er A π B g0 R.N ∧ Er (R.rF R.N) (R.g R.N) (fun _ => False) (R.cfg R.N) := by
  refine ⟨fun μ hμ => ?_, ?_⟩
  · have := h μ (by omega)
    simp only [PRun'.snoc, show μ ≤ R.N by omega, ↓reduceIte] at this
    exact this
  · have := h R.N (by omega)
    simp only [PRun'.snoc, Nat.le_refl, ↓reduceIte] at this
    exact this

/-- **Case (b): a stutter step of an advanced thread.** The real step `J`
is an instruction of thread `j`, which is advanced with target `p > J`. Its
promise `ts` stays outstanding, so the step is a `StutterStep`
(`stutterStep_release`): memory is unchanged. The prefix run is not extended
(`pos (J + 1) = pos J`); the virtual configuration stays a virtual
configuration of the new real one ((S1′) from `π (J + 1)` to `π p`), and
every thread keeps its token and status. -/
theorem step_stutter' [I.LawfulState] (GVOK : GuardOK GV) {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost}
    {states : List I.State} {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem)
    (hNT : ∀ j, j ≤ π.len → (π.cfg j).NTFree A) {J : Nat} (hJ : J < π.len) (R : PRun' GV K Er A π B g0 J)
    (hok : ∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i)
    {j : Nat} {t : Thread I} {outs : List (Except String (Outcome I))} {o : Outcome I}
    (ht : (π.cfg J).threads[j]? = some t) (hs : stepOne A t j (π.cfg J).mem = some outs) (ho : .ok o ∈ outs)
    (hJ1 : π.cfg (J + 1) = (π.cfg J).withThread j o.thread o.mem) {p : Nat}
    (hjok : ThreadOkP' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) j p) (hp : J < p) :
    Inv' G GV K Er S A π B g0 (J + 1) := by
  obtain ⟨s, gs, n, hJp, hpl, hsafe, hext, hgs, hown, hbud, hst⟩ := hjok
  rcases hst with ⟨rfl, -⟩ | ⟨hpl', tp, htp, hv, ⟨ts, hpend, htsp, hrel, hq⟩, hlast⟩
  · omega
  have hjn : j < (π.cfg J).threads.size := lt_size_of_get? ht
  have hthr : ∀ i, i ≠ j → (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]? := fun i hi => by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_right (Ne.symm hi)]
  have hthj : (π.cfg (J + 1)).threads[j]? = some o.thread := by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_left rfl]
  obtain ⟨tJ, htJ, htsJ⟩ := hq J (Nat.le_refl _) (Nat.le_of_lt hp)
  rw [ht] at htJ; cases htJ
  obtain ⟨tJ1, htJ1, htsJ1⟩ := hq (J + 1) (by omega) hp
  rw [hthj] at htJ1; cases htJ1
  have hwf0 : (π.cfg 0).Wf := by rw [h0]; exact Config.init_wf _ _
  have hpl'' : p ≤ π.len := Nat.le_of_lt hpl'
  have hr : Reachable A fuel ((π.cfg J).withThread j o.thread o.mem) (π.cfg p) := by
    rw [← hJ1]; exact π.reachBetween hp hpl''
  have hstut := stutterStep_path (hwf0.reachable (Reachable.toK (π.reachable J (by omega)))) ht htsJ hs ho (Reachable.toK hr) htp
    (GVOK.relPre_lt hrel ((((hwf0.reachable (Reachable.toK (π.reachable J (by omega)))).instr ht hs ho).reachable (Reachable.toK hr)) j tp htp).1)
    ((hNT p hpl'' j tp htp).1 ts)
  have hmem : (π.cfg (J + 1)).mem = (π.cfg J).mem := by
    rw [hJ1]; exact (hstut htsJ1).1
  have hV : (π.cfg (J + 1)).VirtualOfG GV A (R.cfg R.N) := by
    have hV0 := R.virtual J (Nat.le_refl _)
    rw [R.pos_J] at hV0
    obtain ⟨hvm, hvs, hvt⟩ := hV0
    refine ⟨by rw [hvm, hmem], by rw [hvs, hJ1, Config.withThread_size], fun i ti hti => ?_⟩
    by_cases hij : i = j
    · subst hij
      rw [hthj] at hti; cases hti
      obtain ⟨hnp, hts', hrel'⟩ := advanceable_of_pathG' GVOK hwf0 (Reachable.toK (π.reachable (J + 1) (by omega))) hthj htsJ1
        (Reachable.toK (π.reachBetween hp hpl'')) htp htsp hrel ((hNT p hpl'' i tp htp).1 ts) (hNT p hpl'' i tp htp).2
      exact ⟨tp.restrict (π.cfg (J + 1)).mem, by rw [hv, hmem], hnp, .inr ⟨ts, hts', hrel'⟩⟩
    · rw [hthr i hij] at hti
      obtain ⟨t', h1, h2, h3⟩ := hvt i ti hti
      exact ⟨t', h1, by rw [hmem]; exact h2, by rw [hmem]; exact h3⟩
  let R' : PRun' GV K Er A π B g0 (J + 1) := {
    R with
    pos := fun k => if k ≤ J then R.pos k else R.N
    pos_zero := by simp [R.pos_zero]
    pos_mono := fun k hk => by
      by_cases h : k + 1 ≤ J
      · simp only [show k ≤ J by omega, h, ↓reduceIte]; exact R.pos_mono k (by omega)
      · simp only [show k ≤ J by omega, h, ↓reduceIte]; rw [show k = J by omega, R.pos_J]; exact Nat.le_refl _
    pos_J := by simp only [show ¬ (J + 1 ≤ J) by omega, ↓reduceIte]
    virtual := fun k hk => by
      by_cases h : k ≤ J
      · simp only [h, ↓reduceIte]; exact R.virtual k h
      · simp only [h, ↓reduceIte]
        obtain rfl : k = J + 1 := by omega
        exact hV
    doneB := fun k hk hc tid hd => by
      by_cases h : k ≤ J
      · simp only [h, ↓reduceIte] at hc hd ⊢; exact R.doneB k h hc tid hd
      · simp only [h, ↓reduceIte] at hc hd ⊢
        have := R.doneB J (Nat.le_refl _)
        rw [R.pos_J] at this
        exact this hc tid hd }
  refine ⟨R', fun i hi => ?_⟩
  show ThreadOk' G GV K Er S A π B (J + 1) (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i
  by_cases hij : i = j
  · subst hij
    exact ⟨p, s, gs, n, by omega, hpl, hsafe, hext, hgs, hown, by omega, .inr ⟨hpl', tp, htp, by rw [hv, hmem],
      ⟨ts, hpend, htsp, hrel, fun q h1 h2 => hq q (by omega) h2⟩, hlast⟩⟩
  · obtain ⟨pi, si, gsi, ni, hJpi, -, hsafei, hexti, hgsi, howni, hbudi, hsti⟩ := hok i hi
    obtain ⟨p', h1, h2, h3, h4⟩ := status_frameG h0 hJ (hthr i hij) rfl (fun _ h _ => h) (fun _ h => h)
      (fun _ _ _ _ _ => by rw [hmem]) hJpi hsti
    exact ⟨p', si, gsi, ni, h1, h2, hsafei, hexti, hgsi, howni, by omega, h4⟩

end Step

/-! ## Promises fulfilled by a release store, and (O5) as a hypothesis -/

/-- **The promise `ts` of thread `j`, made at real step `J`, is fulfilled by
a release store on `π`**: at some later index `f`, `ts` having stayed
outstanding since `J + 1`, `j`'s next instruction can fulfil `ts` as the
prepay guard `G` says (in the existing `RelFulfilled`: a release store leaving
no promise dead, `Thread.RelFulfilsLive`, as `NPSafe`'s prepay conjunct asks)
and the real step `f` removes `ts` from `j`'s promises. Such a promise is accounted for by a `prepay` micro-step
(case (d1)); any other by a `promise` micro-step (case (d2)), which needs
the message to be pure (`PromisePure'`). -/
def RelFulfilled' (G : PrepayGuard I) {A : Arch} {fuel : Nat} (π : Path A fuel I) (J j : Nat) (ts : Time) : Prop :=
  ∃ f, J < f ∧ f < π.len ∧ (∀ q, J < q → q ≤ f → ∃ tq, (π.cfg q).threads[j]? = some tq ∧ ts ∈ tq.prom) ∧
    ∃ tf tf', (π.cfg f).threads[j]? = some tf ∧ G A j ts tf (π.cfg f).mem ∧
      (π.cfg (f + 1)).threads[j]? = some tf' ∧ ts ∉ tf'.prom

/-- **(O5) Promises not fulfilled by a release store are pure**, as an
explicit hypothesis on the program, stated *a posteriori* over the real paths
from `Config.init states initMem` to a final configuration (like `Cond3'`),
for the release predicates `rel` of the initial ghost (`Ghost.Le` keeps
`rel`, so they are those of every later ghost): on such a path, a promise of
`pw` by thread `j` at real step `J` that is not `RelFulfilled'` writes a value
that is pure for its location's release predicate. This is what
`MicroStep'.promise` (`Erase.promise`, SLR Lemmas 23–24) needs; `Erase.pure`
is unchanged (option (B) rejected). For the
spinlocks: the stores that are not release stores write values whose release
predicate is `emp` (lock value 1) or pure (data, counters). -/
def PromisePure' (G : PrepayGuard I) (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State)
    (initMem : List (Loc × Val)) (rel : Loc → Pred) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J, J < π.len → ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    ¬ RelFulfilled' G π J j ((π.cfg J).mem.last + 1) →
    Pred.Pure (rel pw.1.loc) pw.1.val

/-- **(O5) with an obligation `Q`**: `PromisePure'` whose
conclusion is `Q` of the memory before the promise and the promised message.
At `Q := ObPure rel` it is `PromisePure' … rel`, definitionally. -/
def PromiseObl' (G : PrepayGuard I) (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State)
    (initMem : List (Loc × Val)) (Q : Memory → Msg → Prop) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J, J < π.len → ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    ¬ RelFulfilled' G π J j ((π.cfg J).mem.last + 1) →
    Q (π.cfg J).mem { pw.1 with tid := j }

/-- `PromiseObl'` at the existing obligation is `PromisePure'`. -/
theorem promiseObl_pure' {G : PrepayGuard I} {A : Arch} {fuel : Nat} [I.LawfulState] {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} :
    PromiseObl' G A fuel states initMem (ObPure rel) = PromisePure' G A fuel states initMem rel := rfl

/-! ## The remaining cases of the step, as `Prop`s -/

/-- **Cases (a) and (c)** (`Prop`; proved as `caseNow'` from (O7) `liveWfProm`): the real step `J` is an
instruction of thread `j` whose target is `J` itself: `j` is not advanced, or
it is advanced and the step is its fulfilling instruction `F`. The micro-run
takes one `np` step at the virtual configuration with the real outcome. -/
def CaseNow' (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I) (S : StepGuard (modelErase I Er)) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) →
    ∀ J, J < π.len → ∀ R : PRun' GV K Er A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (outs : List (Except String (Outcome I))) (o : Outcome I),
    (π.cfg J).threads[j]? = some t → stepOne A t j (π.cfg J).mem = some outs → .ok o ∈ outs →
    π.cfg (J + 1) = (π.cfg J).withThread j o.thread o.mem →
    ThreadOkP' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) j J →
    Inv' G GV K Er S A π B g0 (J + 1)

/-- **Case (d)**: the real step `J` is a (certified) promise of thread `j`,
under (O5) `PromisePure'` for the initial ghost's release predicates. Split
(`casePromise_of'`) into (d1) `CaseD1'` (`RelFulfilled'`) and (d2) `CaseD2'`. -/
def CasePromise' (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I) (S : StepGuard (modelErase I Er)) (Ob : PromiseOb) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromiseObl' G A fuel states initMem (Ob g0.rel) →
    ∀ J, J < π.len → ∀ R : PRun' GV K Er A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    Inv' G GV K Er S A π B g0 (J + 1)

/-- **Case (d1)** (`Prop`; O3, proved as `caseD1'` in `SLR/Theorem1D1.lean`): the promise is `RelFulfilled'` at
some `f > J`. Replay `j`'s promise-free steps up to `f` on hybrid
configurations (`j`'s real states restricted to the memory at `J`; they are
`StutterStep`s since `ts` stays outstanding), then a `prepay` micro-step from
`j`'s token; `j` becomes advanced with target `f`. -/
def CaseD1' (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I) (S : StepGuard (modelErase I Er)) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) →
    ∀ J, J < π.len → ∀ R : PRun' GV K Er A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    RelFulfilled' G π J j ((π.cfg J).mem.last + 1) →
    Inv' G GV K Er S A π B g0 (J + 1)

/-- **Case (d2)** (`Prop`; proved: `caseD2'`): the promise is not
`RelFulfilled'`; by `PromisePure'` its message is pure, a `promise` micro-step
that transfers nothing. -/
def CaseD2' (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I) (S : StepGuard (modelErase I Er)) (Ob : PromiseOb) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromiseObl' G A fuel states initMem (Ob g0.rel) →
    ∀ J, J < π.len → ∀ R : PRun' GV K Er A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk' G GV K Er S A π B J (R.Clean GV K Er A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    ¬ RelFulfilled' G π J j ((π.cfg J).mem.last + 1) →
    Inv' G GV K Er S A π B g0 (J + 1)

/-- Case (d) from its two sub-cases. -/
theorem casePromise_of' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} [I.LawfulState] {A : Arch} {fuel : Nat} (hd1 : CaseD1' (I := I) G GV K Er S A fuel)
    (hd2 : CaseD2' (I := I) G GV K Er S Ob A fuel) : CasePromise' (I := I) G GV K Er S Ob A fuel := by
  intro π B g0 states initMem h0 hfin hNT hpure J hJ R hok j t pw ht hw hJ1
  by_cases hrel : RelFulfilled' G π J j ((π.cfg J).mem.last + 1)
  · exact hd1 π B g0 states initMem h0 hfin hNT J hJ R hok j t pw ht hw hJ1 hrel
  · exact hd2 π B g0 states initMem h0 hfin hNT hpure J hJ R hok j t pw ht hw hJ1 hrel

/-- **Cases (a) and (c), proved from (O7)**: the real step is an
instruction of thread `j` with target `J`. The virtual thread `j` is the real
one (not advanced, or advanced with all promises below `|M|`), so the real
outcome is an `NPStepBy` at the virtual configuration; `j`'s token gives the
step (`NPSafePS.stepAt`: own-pending from `ThreadOk'`, erasure from the run, the
machine invariants of the virtual configuration from `machInv_of_restrict`,
`WfProm` from (O7)), recorded as an `np` micro-step. Afterwards `j` is not
advanced (none of its promises is pending: those pending before are
fulfilled by `F`, others are other threads'); every other thread keeps its
token (environment extension) and status (`status_frameG`, `restrict_frame`). -/
theorem caseNow' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) (GVOK : GuardOK GV) [I.LawfulState] {A : Arch} {fuel : Nat} (hO7 : LiveWfProm (I := I) A fuel) :
    CaseNow' (I := I) G GV K Er S A fuel := by
  intro π B g0 states initMem h0 hfin hNT J hJ R hok j t outs o ht hs ho hJ1 hjok
  obtain ⟨s, gs, n, -, -, hsafe, hext, hgs, hown, hbud, hst⟩ := hjok
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 + 1 := ⟨n - 2, by omega⟩
  have hV := R.virtual J (Nat.le_refl _)
  rw [R.pos_J] at hV
  obtain ⟨hvm, hvs, -⟩ := hV
  have hjn : j < (π.cfg J).threads.size := lt_size_of_get? ht
  have hthj : (π.cfg (J + 1)).threads[j]? = some o.thread := by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_left rfl]
  have hthr : ∀ i, i ≠ j → (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]? := fun i hi => by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_right (Ne.symm hi)]
  have hJ1m : (π.cfg (J + 1)).mem = o.mem := by rw [hJ1]; rfl
  have hwfJ := π.wf h0 J (by omega)
  have hvj : (R.cfg R.N).threads[j]? = some t := by
    rcases hst with ⟨-, hv, -⟩ | ⟨-, tp, htp, hv, -⟩
    · rw [hv, ht]
    · rw [ht] at htp; cases htp; rw [hv, Thread.restrict_eq (hwfJ j t ht).2]
  have hjv : j < (R.cfg R.N).threads.size := by rw [hvs]; exact hjn
  -- the micro-step
  have hv'j : ((R.cfg R.N).withThread j o.thread o.mem).threads[j]? = some o.thread := by
    rw [Config.withThread_get? _ _ _ hjv, ite_eq_left rfl]
  have hv'r : ∀ i, i ≠ j → ((R.cfg R.N).withThread j o.thread o.mem).threads[i]? = (R.cfg R.N).threads[i]? :=
    fun i hi => by rw [Config.withThread_get? _ _ _ hjv, ite_eq_right (Ne.symm hi)]
  have hnp : NPStepBy A j (R.cfg R.N) ((R.cfg R.N).withThread j o.thread o.mem) :=
    ⟨t, o.thread, o.mem, hvj, ⟨outs, o, by rw [hvm]; exact hs, ho, rfl⟩, rfl⟩
  have hrestr : ∀ (i : Nat) (ti : Thread I), (R.cfg R.N).threads[i]? = some ti →
      ∃ (q : Nat) (tq : Thread I), J ≤ q ∧ q ≤ π.len ∧ (π.cfg q).threads[i]? = some tq ∧
        ti = tq.restrict (π.cfg J).mem := by
    intro i ti hti
    obtain ⟨pi, _, _, _, hJpi, hpli, _, _, _, _, _, hsti⟩ := hok i (lt_size_of_get? hti)
    exact Status'.restrictOf h0 (by omega) hpli hJpi hsti hti
  have hinv : (R.cfg R.N).MachInv := machInv_of_restrict h0 hvm hrestr
  have hlive : ∀ q, q ≤ π.len → ∀ i, (π.cfg q).WfProm i := fun q hq i =>
    hO7 states initMem _ (by rw [← h0]; exact π.reachable q hq) (π.live hfin q hq) i
  have hw : (R.cfg R.N).WfProm j := fun t' ht' => by
    rw [hvj] at ht'; cases ht'; rw [hvm]; exact hlive J (by omega) j t ht
  have hw' : ((R.cfg R.N).withThread j o.thread o.mem).WfProm j := fun t' ht' => by
    rw [hv'j] at ht'; cases ht'
    show o.thread.hasDeadPromise o.mem = false
    rw [← hJ1m]; exact hlive (J + 1) hJ j o.thread hthj
  have E0 := R.erase R.N (Nat.le_refl _)
  have hupd : (modelErase I Er).upd (R.rF R.N) j (R.rF R.N j) = R.rF R.N := funext fun i => by
    simp only [ResModel.upd]
    by_cases h : i = j <;> simp only [h, ↓reduceIte] <;> exact rfl
  -- the step fulfils every pending promise of `j` (the step guard's condition): `j` is not
  -- advanced (nothing pending), or advanced and the step is its fulfilling `F`
  have hstepful : StepFulP (model I) j (R.cfg R.N) (R.g R.N) ((R.cfg R.N).withThread j o.thread o.mem) := by
    intro t1 t1' ht1 ht1' ts hts hp hts'
    rw [hvj] at ht1; cases ht1
    rw [hv'j] at ht1'; cases ht1'
    rcases hst with ⟨-, -, hnp0⟩ | ⟨-, tp, htp, -, -, ⟨tp', htp', -, hful⟩⟩
    · exact hnp0 _ hvj ts hts hp
    · rw [ht] at htp; cases htp
      rw [hthj] at htp'; cases htp'
      exact hful ts hp hts hts'
  obtain ⟨r', g', E', hg', hkeep, hback, hsafe', hacq, howns, hK2, hK1⟩ :=
    NPSafePS.stepAt hsafe hext hgs hown (R.rF R.N) ((R.cfg R.N).withThread j o.thread o.mem)
      (by rw [hupd]; exact E0) hnp hinv hw hw' hstepful
  have hrF'j : (modelErase I Er).upd (R.rF R.N) j r' j = r' := by simp only [ResModel.upd, ↓reduceIte]
  have hrF'o : ∀ i, i ≠ j → (modelErase I Er).upd (R.rF R.N) j r' i = R.rF R.N i := fun i hi => by
    simp only [ResModel.upd, hi, ↓reduceIte] <;> exact rfl
  -- after the step, no promise of `j` is pending
  have hnopend : ∀ ts ∈ o.thread.prom, ts ∉ g'.pend := by
    intro ts hts hp
    have hp0 : ts ∈ (R.g R.N).pend := hback ts hp
    obtain ⟨-, i, ti, hti, htsi⟩ := (ErOK.toErase E0).pend ts hp0
    by_cases hij : i = j
    · subst hij
      rw [hvj] at hti; cases hti
      rcases hst with ⟨-, -, hnp0⟩ | ⟨-, tp, htp, -, -, ⟨tp', htp', -, hful⟩⟩
      · exact hnp0 _ hvj ts htsi hp0
      · rw [ht] at htp; cases htp
        rw [hthj] at htp'; cases htp'
        exact hful ts hp0 htsi hts
    · obtain ⟨w, hw1, hw2⟩ := hinv.promWf i ti hti ts htsi
      obtain ⟨w', hw1', hw2'⟩ := (π.machInv h0 (J + 1) hJ).promWf j o.thread hthj ts hts
      rw [hvm] at hw1
      have hle := (π.cfg J).mem.last_le_of_get?_eq_some hw1
      rw [(π.mem_prefix (Nat.le_succ J) hJ).get? hle, hw1] at hw1'
      cases hw1'
      exact hij (hw2.symm.trans hw2')
  have hnew : ∀ ts w, (π.cfg J).mem.last < ts → (π.cfg (J + 1)).mem.get? ts = some w → w.tid = j := by
    intro ts w hlt hw
    rw [hJ1m] at hw
    exact (stepOne_inv A hs ho ((π.machInv h0 J (by omega)).thread ht)).2.2 ts w hlt hw
  -- every thread in order at `J + 1`, with flag `cl'`
  have hok' : ∀ i, i < ((R.cfg R.N).withThread j o.thread o.mem).threads.size →
      ∃ p, ThreadOkP' G GV K Er S A π B (J + 1)
        (R.Clean GV K Er A π B g0 R.N ∧ Er (R.rF R.N) (R.g R.N) (fun _ => False) (R.cfg R.N))
        ((R.cfg R.N).withThread j o.thread o.mem) ((modelErase I Er).upd (R.rF R.N) j r') g' i p := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      refine ⟨J + 1, (R.cfg R.N).withThread i o.thread o.mem, g', k + 1, Nat.le_refl _, hJ, ?_,
        EnvExt.refl _ _, Ghost.Le.refl _, fun _ _ _ _ hp => hp, by omega,
        .inl ⟨rfl, by rw [hv'j, hthj], fun t' ht' ts hts hp => ?_⟩⟩
      · rw [hrF'j]
        exact NPSafePS.mono_flag (fun h => ⟨h.1, by rw [hupd]; exact h.2⟩) hsafe'
      · rw [hv'j] at ht'; cases ht'; exact hnopend ts hts hp
    · rw [Config.withThread_size] at hi
      obtain ⟨pi, si, gsi, ni, hJpi, hpli, hsafei, hexti, hgsi, howni, hbudi, hsti⟩ := hok i hi
      obtain ⟨p', h1, h2, h3, h4⟩ := status_frameG h0 hJ (hthr i hij) (hv'r i hij)
        (fun ts h ⟨t', ht', hts⟩ => hkeep ts h ⟨i, t', ht', hts⟩) hback
        (restrict_frame h0 hJ hnew i hij) hJpi hsti
      refine ⟨p', si, gsi, ni, h1, h2, ?_, hexti.trans (hnp.envExt_other (Ne.symm hij)), hgsi.trans hg',
        fun t' ht' ts hts hp => howni t' (by rw [← hv'r i hij]; exact ht') ts hts (hback ts hp), by omega, h4⟩
      rw [hrF'o i hij]
      exact NPSafePS.mono_flag (fun h => h.1) hsafei
  have hV' : (π.cfg (J + 1)).VirtualOfG GV A ((R.cfg R.N).withThread j o.thread o.mem) :=
    virtual_of_status' GVOK h0 hNT hJ (by rw [hJ1m]; rfl) (by rw [Config.withThread_size, hvs, hJ1, Config.withThread_size])
      (fun i hi => by
        obtain ⟨p, _, _, _, hJp, _, _, _, _, _, _, hst'⟩ := hok' i hi
        exact ⟨p, hJp, hst'⟩)
  have hstep : MicroStep' K A (R.cfg R.N) (R.rF R.N) (R.g R.N) ((R.cfg R.N).withThread j o.thread o.mem)
      ((modelErase I Er).upd (R.rF R.N) j r') g' :=
    MicroStep'.np j t o.thread hvj hnp hv'j hrF'o hg' (fun ts h ho => hkeep ts h ho) hback
      (fun x hx => hacq x (by rw [← hrF'j]; exact hx)) (fun w hw => howns w hw)
      hK2
      (fun b hb hmax x h => hK1 b hb (fun t' ht' => by rw [hv'j] at ht'; cases ht'; exact hmax) x
        (by rw [← hrF'j]; exact h))
  let R' := R.snoc ((R.cfg R.N).withThread j o.thread o.mem) ((modelErase I Er).upd (R.rF R.N) j r') g' E' hstep hV'
    ⟨J + 1, hJ, by rw [hJ1m]; rfl⟩
    (fun s' t' ht' => by
      by_cases hs' : s' = j
      · subst hs'; rw [hv'j] at ht'; cases ht'
        exact ⟨J + 1, o.thread, hJ, hthj, rfl, fun _ h => h⟩
      · rw [hv'r s' hs'] at ht'; exact R.real R.N (Nat.le_refl _) s' t' ht')
    ((R.le0 R.N (Nat.le_refl _)).trans hg')
    (fun hcl tid hd => by
      obtain ⟨t', ht', hrest⟩ := hd
      obtain ⟨p, hP⟩ := hok' tid (lt_size_of_get? ht')
      exact ThreadOkP'.done hP hcl ⟨t', ht', hrest⟩)
  refine ⟨R', fun i hi => ?_⟩
  have hc : R'.cfg R'.N = (R.cfg R.N).withThread j o.thread o.mem := by
    simp [R', PRun'.snoc, show ¬ (R.N + 1 ≤ R.N) by omega]
  have hr : R'.rF R'.N = (modelErase I Er).upd (R.rF R.N) j r' := by
    simp [R', PRun'.snoc, show ¬ (R.N + 1 ≤ R.N) by omega] <;> exact rfl
  have hg : R'.g R'.N = g' := by simp [R', PRun'.snoc, show ¬ (R.N + 1 ≤ R.N) by omega] <;> exact rfl
  rw [hc] at hi
  obtain ⟨p, hP⟩ := hok' i hi
  refine ⟨p, ?_⟩
  rw [hc, hr, hg]
  exact hP.mono_flag (fun h => R.snoc_clean h)

/-- `omega` on `Time`/`View`. -/
local macro "omega_t2" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **Case (d2), proved from (O5) `PromisePure'`**: the promise of `pw` by
thread `j` at real step `J` is not `RelFulfilled'`, so its message is pure for
the initial (= current) ghost's release predicate, and the micro-run takes a
`promise` micro-step at the virtual configuration (`Erase.promise`), with
resources and ghost unchanged. The promising thread keeps its token
(environment extension `EnvExt.promise`; the new promise is not pending).
If `j` is not advanced it stays so, with the real state at `J + 1`. If it is
advanced with target `p`, `p ≠ J` (the step at `p` fulfils the pending
promise, a promise step does not), the new promise `ts = |M_J| + 1` is still
outstanding at `p` (otherwise `j` fulfilled it before `p`, raising its
`relPre`/`vwOldNT` to `ts` above the pending `ts0`, which the release store at
`p` forbids: `Thread.HasOrPassed`, `Thread.RelFulfils.relPre_lt`,
`Thread.NoNTStores`); promise lists being sorted (`Path.promSorted`), the
virtual state with `ts` added is the target state restricted to `M_{J+1}`
(`filter_le_succ_of_sorted`). Other threads keep token and status
(`status_frameG`, `restrict_frame`). -/
theorem caseD2' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) (GVOK : GuardOK GV) [I.LawfulState] {A : Arch} {fuel : Nat} : CaseD2' (I := I) G GV K Er S Ob A fuel := by
  intro π B g0 states initMem h0 hfin hNT hpure J hJ R hok j t pw ht hw hJ1 hnrel
  have hpw := hpure π h0 hfin J hJ j t pw ht hw hJ1 hnrel
  have hV := R.virtual J (Nat.le_refl _)
  rw [R.pos_J] at hV
  obtain ⟨hvm, hvs, -⟩ := hV
  have hjn : j < (π.cfg J).threads.size := lt_size_of_get? ht
  have hjv : j < (R.cfg R.N).threads.size := by rw [hvs]; exact hjn
  have hthj : (π.cfg (J + 1)).threads[j]? = some { t with prom := t.prom ++ [(π.cfg J).mem.last + 1] } := by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_left rfl]; rfl
  have hthr : ∀ i, i ≠ j → (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]? := fun i hi => by
    rw [hJ1, Config.withThread_get? _ _ _ hjn, ite_eq_right (Ne.symm hi)]
  have hJ1m : (π.cfg (J + 1)).mem = ((π.cfg J).mem.append { pw.1 with tid := j }).1 := by rw [hJ1]; rfl
  have hJ1last : (π.cfg (J + 1)).mem.last = (π.cfg J).mem.last + 1 := by rw [hJ1m, Memory.last_append]
  have E0 := R.erase R.N (Nat.le_refl _)
  have hnp_new : (R.cfg R.N).mem.last + 1 ∉ (R.g R.N).pend := fun h => by
    have := (ErOK.toErase E0).pend_le h; omega_t2
  obtain ⟨p, s, gs, n, hJp, hpl, hsafe, hext, hgs, hown, hbud, hst⟩ := hok j hjv
  -- the virtual thread of `j`, and its status after the promise
  have claim : ∃ tv, (R.cfg R.N).threads[j]? = some tv ∧ ∃ p', J + 1 ≤ p' ∧ p' ≤ π.len ∧
      (π.len - p') + (π.len - (J + 1)) < n ∧
      Status' GV A π (J + 1) (Promised (R.cfg R.N) j tv pw.1) (R.g R.N) j p' := by
    rcases hst with ⟨hpJ, hv, hnp⟩ | ⟨hpl', tp, htp, hv, ⟨ts0, hpend, htsp, hrel, hq⟩, hlast⟩
    · have hvj : (R.cfg R.N).threads[j]? = some t := by rw [hv, ht]
      have hv'j : (Promised (R.cfg R.N) j t pw.1).threads[j]? =
          some { t with prom := t.prom ++ [(π.cfg J).mem.last + 1] } := by
        rw [promised_get? hvj, ite_eq_left rfl, hvm]
      refine ⟨t, hvj, J + 1, Nat.le_refl _, hJ, by omega, .inl ⟨rfl, by rw [hv'j, hthj], fun t' ht' ts' hts' hp' => ?_⟩⟩
      rw [hv'j] at ht'; cases ht'
      rcases List.mem_append.mp hts' with h | h
      · exact hnp t hvj ts' h hp'
      · rw [List.mem_singleton] at h; subst h; rw [← hvm] at hp'; exact hnp_new hp'
    · obtain ⟨tJ, htJ, hts0J⟩ := hq J (Nat.le_refl _) hJp
      rw [ht] at htJ; cases htJ
      have hJp' : J < p := by
        rcases Nat.lt_or_ge J p with h | h
        · exact h
        · exfalso
          obtain rfl : J = p := by omega
          obtain ⟨tp', htp', -, hful⟩ := hlast
          rw [ht] at htp; cases htp
          rw [hthj] at htp'; cases htp'
          exact hful ts0 hpend htsp (List.mem_append_left _ htsp)
      have hwfJ1 := π.wf h0 (J + 1) hJ
      have hplp : p ≤ π.len := Nat.le_of_lt hpl'
      obtain ⟨tp2, htp2, hop⟩ := Thread.HasOrPassed.reachable hwfJ1 (Reachable.toK (π.reachBetween hJp' hplp)) hthj
        (ts := (π.cfg J).mem.last + 1) (.inl (List.mem_append_right _ (List.mem_singleton_self _)))
      rw [htp] at htp2; cases htp2
      have htsp' : (π.cfg J).mem.last + 1 ∈ tp.prom := by
        rcases hop with h | h
        · exact h
        · exfalso
          have hwfp := π.wf h0 p hplp
          have hb := GVOK.relPre_lt hrel (hwfp j tp htp).1
          have hnt := (hNT p hplp j tp htp).1 ts0
          have hle := (π.wf h0 J (by omega) j t ht).2 ts0 hts0J
          unfold Thread.NoNTStores at hnt
          omega_t2
      have hsorted := Path.promSorted π h0 p hplp j tp htp
      have hres : tp.restrict (π.cfg (J + 1)).mem =
          { tp.restrict (π.cfg J).mem with prom := (tp.restrict (π.cfg J).mem).prom ++ [(π.cfg J).mem.last + 1] } := by
        simp only [Thread.restrict, hJ1last]
        rw [filter_le_succ_of_sorted hsorted htsp']
      have hv'j : (Promised (R.cfg R.N) j (tp.restrict (π.cfg J).mem) pw.1).threads[j]? =
          some (tp.restrict (π.cfg (J + 1)).mem) := by
        rw [promised_get? hv, ite_eq_left rfl, hvm, hres]
      exact ⟨tp.restrict (π.cfg J).mem, hv, p, by omega, hplp, by omega,
        .inr ⟨hpl', tp, htp, hv'j, ⟨ts0, hpend, htsp, hrel, fun q h1 h2 => hq q (by omega) h2⟩, hlast⟩⟩
  obtain ⟨tv, hvj, pj, hpj1, hpj2, hpj3, hstj⟩ := claim
  let v' := Promised (R.cfg R.N) j tv pw.1
  have hv'r : ∀ i, i ≠ j → v'.threads[i]? = (R.cfg R.N).threads[i]? := fun i hi => by
    show (Promised (R.cfg R.N) j tv pw.1).threads[i]? = _
    rw [promised_get? hvj, ite_eq_right (Ne.symm hi)]
  have hv'm : v'.mem = (π.cfg (J + 1)).mem := by
    show (Promised (R.cfg R.N) j tv pw.1).mem = _
    rw [promised_mem, hvm, hJ1m]
  have hnew : ∀ ts w, (π.cfg J).mem.last < ts → (π.cfg (J + 1)).mem.get? ts = some w → w.tid = j := by
    intro ts w hlt hw
    rw [hJ1m] at hw
    rcases Memory.get?_append_eq_some _ _ hw with ⟨hle, -⟩ | ⟨-, rfl⟩
    · omega_t2
    · rfl
  have hext' : ∀ i, EnvExt i (R.cfg R.N) v' := fun i => EnvExt.promise hvj
  -- every thread in order at `J + 1`
  have hok' : ∀ i, i < v'.threads.size →
      ∃ p, ThreadOkP' G GV K Er S A π B (J + 1)
        (R.Clean GV K Er A π B g0 R.N ∧ Er (R.rF R.N) (R.g R.N) (fun _ => False) (R.cfg R.N))
        v' (R.rF R.N) (R.g R.N) i p := by
    intro i hi
    by_cases hij : i = j
    · subst hij
      refine ⟨pj, s, gs, n, hpj1, hpj2, NPSafePS.mono_flag (fun h => h.1) hsafe, hext.trans (hext' i), hgs,
        fun t' ht' ts' hts' hp' => ?_, hpj3, hstj⟩
      have ht'' : v'.threads[i]? = some { tv with prom := tv.prom ++ [(R.cfg R.N).mem.last + 1] } := by
        show (Promised (R.cfg R.N) i tv pw.1).threads[i]? = _
        rw [promised_get? hvj, ite_eq_left rfl]
      rw [ht''] at ht'; cases ht'
      rcases List.mem_append.mp hts' with h | h
      · exact hown tv hvj ts' h hp'
      · rw [List.mem_singleton] at h; subst h; exact absurd hp' hnp_new
    · have hi' : i < (R.cfg R.N).threads.size := by
        have : v'.threads.size = (R.cfg R.N).threads.size := promised_size
        omega
      obtain ⟨pi, si, gsi, ni, hJpi, -, hsafei, hexti, hgsi, howni, hbudi, hsti⟩ := hok i hi'
      obtain ⟨p', h1, h2, h3, h4⟩ := status_frameG h0 hJ (hthr i hij) (hv'r i hij) (fun _ h _ => h) (fun _ h => h)
        (restrict_frame h0 hJ hnew i hij) hJpi hsti
      exact ⟨p', si, gsi, ni, h1, h2, NPSafePS.mono_flag (fun h => h.1) hsafei, hexti.trans (hext' i), hgsi,
        fun t' ht' => howni t' (by rw [← hv'r i hij]; exact ht'), by omega, h4⟩
  have hV' : (π.cfg (J + 1)).VirtualOfG GV A v' :=
    virtual_of_status' GVOK h0 hNT hJ hv'm
      (by
        show (Promised (R.cfg R.N) j tv pw.1).threads.size = _
        rw [promised_size, hvs, hJ1, Config.withThread_size])
      (fun i hi => by
        obtain ⟨p, _, _, _, hJp, _, _, _, _, _, _, hst'⟩ := hok' i hi
        exact ⟨p, hJp, hst'⟩)
  have hob : Ob (R.g R.N).rel (R.cfg R.N).mem { pw.1 with tid := j } := by
    rw [(R.le0 R.N (Nat.le_refl _)).rel, hvm]; exact hpw
  have hpure' : Pred.Pure ((R.g R.N).rel pw.1.loc) pw.1.val := ErOK.pure (w := { pw.1 with tid := j }) hob
  have E' : Er (R.rF R.N) (R.g R.N) (fun _ => True) v' :=
    ErOK.promise E0 hvj ((ErOK.toErase E0).promise hvj (fun h => absurd trivial h) hpure') hob
  have hstep : MicroStep' K A (R.cfg R.N) (R.rF R.N) (R.g R.N) v' (R.rF R.N) (R.g R.N) :=
    MicroStep'.promise j tv pw.1 hvj hpure'
  let R' := R.snoc v' (R.rF R.N) (R.g R.N) E' hstep hV' ⟨J + 1, hJ, hv'm⟩
    (fun s' t' ht' => by
      obtain ⟨p, _, _, _, hJp, hp, _, _, _, _, _, hst'⟩ := hok' s' (lt_size_of_get? ht')
      obtain ⟨q, tq, -, hq, htq, rfl⟩ := Status'.restrictOf h0 hJ hp hJp hst' ht'
      exact ⟨q, tq, hq, htq, rfl, fun x hx => (List.mem_filter.mp hx).1⟩)
    (R.le0 R.N (Nat.le_refl _))
    (fun hcl tid hd => by
      obtain ⟨t', ht', hrest⟩ := hd
      obtain ⟨p, hP⟩ := hok' tid (lt_size_of_get? ht')
      exact ThreadOkP'.done hP hcl ⟨t', ht', hrest⟩)
  refine ⟨R', fun i hi => ?_⟩
  have hc : R'.cfg R'.N = v' := by
    simp [R', PRun'.snoc, show ¬ (R.N + 1 ≤ R.N) by omega]
  have hr : R'.rF R'.N = R.rF R.N := by
    simp [R', PRun'.snoc, show ¬ (R.N + 1 ≤ R.N) by omega]
  have hg : R'.g R'.N = R.g R.N := by simp [R', PRun'.snoc, show ¬ (R.N + 1 ≤ R.N) by omega]
  rw [hc] at hi
  obtain ⟨p, hP⟩ := hok' i hi
  refine ⟨p, ?_⟩
  rw [hc, hr, hg]
  exact hP.mono_flag (fun h => R.snoc_clean h)

/-- **The step of the induction from its cases**: the real step is an
instruction (`succs_cases`) of a thread whose target is later (case (b),
`step_stutter'`, proved) or now (`CaseNow'`), or a promise (`CasePromise'`). -/
theorem stepInv_of_cases' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I} {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (GVOK : GuardOK GV) [I.LawfulState] {A : Arch} {fuel : Nat} (hnow : CaseNow' (I := I) G GV K Er S A fuel)
    (hprom : CasePromise' (I := I) G GV K Er S Ob A fuel) :
    ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromiseObl' G A fuel states initMem (Ob g0.rel) →
    ∀ J, J < π.len → Inv' G GV K Er S A π B g0 J → Inv' G GV K Er S A π B g0 (J + 1) := by
  intro π B g0 states initMem h0 hfin hNT hpure J hJ hinv
  obtain ⟨R, hok⟩ := hinv
  have hsk := succs_cases (π.step J hJ)
  generalize hc' : π.cfg (J + 1) = c' at hsk
  cases hsk with
  | @instr j t outs o ht hs ho =>
    have hV := R.virtual J (Nat.le_refl _)
    rw [R.pos_J] at hV
    have hj : j < (R.cfg R.N).threads.size := by rw [hV.2.1]; exact lt_size_of_get? ht
    obtain ⟨p, hP⟩ := hok j hj
    have hJp : J ≤ p := by obtain ⟨_, _, _, h, _⟩ := hP; exact h
    by_cases hlt : J < p
    · exact step_stutter' GVOK h0 hNT hJ R hok ht hs ho hc' hP hlt
    · obtain rfl : J = p := by omega
      exact hnow π B g0 states initMem h0 hfin hNT J hJ R hok j t outs o ht hs ho hc' hP
  | @promise j t pw ht hw =>
    exact hprom π B g0 states initMem h0 hfin hNT hpure J hJ R hok j t pw ht hw hc'

/-! ## Theorem 1′ from the step of the induction and condition (3) -/

/-- **The step of the induction** (`Prop`): along a path from `Config.init` to
a final configuration within the scope `Config.NTFree`, under (O5)
`PromisePure'` for the initial ghost, the invariant at `J` gives the invariant
at `J + 1`. Its cases are the lemmas above. -/
def StepInv' (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I) (S : StepGuard (modelErase I Er)) (Ob : PromiseOb) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromiseObl' G A fuel states initMem (Ob g0.rel) →
    ∀ J, J < π.len → Inv' G GV K Er S A π B g0 J → Inv' G GV K Er S A π B g0 (J + 1)

/-- **Theorem 1′ for the SLR-adapted model, under (O5)**: `Theorem1II`
(`NPSafeImpliesAdequateV` for `model`, `VirtualRel.ii`, scope
`Config.NTFree`) with the extra hypothesis `PromisePure'` for the initial
ghost's release predicates. (The laws arguments of `NPSafeImpliesAdequateV`
are not used and are dropped.) The per-thread `NPSafe` is required only for
the threads of the initial configuration (`tid < states.length`): machine
steps keep the number of threads, and for a nonexistent `tid` `EnvExt` does
not constrain the extended configuration, so `NPSafe` there is not provable
in general.

Generic in the prepay guard `G` (`NPSafeP`, `PromisePure'`), the virtual
guard `GV` (the conclusion's `Config.VirtualOfG`) and the K2 frame `K`; the
existing `Theorem1IIPure` is the instance at `G₀`, `GRF`, `K2₀` (with
`VirtualRel.ii`, i.e. `Config.VirtualOf`, for `Config.VirtualOfG GRF`). -/
def Theorem1IIPure' (G GV : PrepayGuard I) (K : K2Frame (model I)) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    PromisePure' G A fuel states initMem g.rel →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid G K n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', c.VirtualOfG GV A v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- **Theorem 1′ with a step guard**: `Theorem1IIPure'` whose
per-thread hypothesis is `NPSafePS … S` (`SLR/NPSafeP.lean`), i.e. `NPSafeP`
whose step conjunct is asked only under the step guard `S`. At
`S := StepGuard.top _` it is `Theorem1IIPure'`, definitionally
(`NPSafePS_top`); every `S` gives `Theorem1IIPure'` (`Theorem1IIPureS'.toP`).
At `S := StepGuard.ful _` the per-thread hypothesis is the failing-RMW route's `NPSafeF`
(`EnvG/RmwFailChain.lean`). -/
def Theorem1IIPureS' (G GV : PrepayGuard I) (K : K2Frame (model I)) (S : StepGuard (model I)) (A : Arch) (fuel : Nat)
    [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    PromisePure' G A fuel states initMem g.rel →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafePS (model I) A B tid G K S n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', c.VirtualOfG GV A v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- The step-guarded Theorem 1′ gives the unguarded one (`NPSafeP.toS`). -/
theorem Theorem1IIPureS'.toP {G GV : PrepayGuard I} {K : K2Frame (model I)} {S : StepGuard (model I)}
    [I.LawfulState] {A : Arch} {fuel : Nat} (h : Theorem1IIPureS' (I := I) G GV K S A fuel) :
    Theorem1IIPure' (I := I) G GV K A fuel :=
  fun B states initMem rF g hNT E hp hpure hs c hc hl =>
    h B states initMem rF g hNT E hp hpure (fun tid htid n m => NPSafeP.toS S (hs tid htid n m)) c hc hl

/-- **Theorem 1′ with an erasure, an obligation and a step guard**: `Theorem1IIPureS'` where the micro-run carries the erasure `Er`
(the tokens are at `modelErase I Er`, the initial configuration and the
conclusion's virtual configuration satisfy `Er`), and (O5) gives the
obligation `Ob` (`PromiseObl'`). Proved for every `Er`, `Ob` with
`ChainExt Er Ob` (`theorem1II_of_cond3'`, `theorem1IIPureXS'`). At `Erase`,
`ObPure` it is `Theorem1IIPureS'`, definitionally (`modelErase_Erase`,
`promiseObl_pure'`). -/
def Theorem1IIPureXS' (G GV : PrepayGuard I) (K : K2Frame (model I)) (Er : ErasureP I)
    (S : StepGuard (modelErase I Er)) (Ob : PromiseOb) (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Er rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    PromiseObl' G A fuel states initMem (Ob g.rel) →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafePS (modelErase I Er) A B tid G K S n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', c.VirtualOfG GV A v ∧ Er rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- **Theorem 1′ for the SLR-adapted model** (`Theorem1IIPureXS'`) from condition
(3) and the step of the induction. -/
theorem theorem1II_of_step' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I}
    {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) [I.LawfulState] {A : Arch} {fuel : Nat}
    (h3 : ∀ states initMem, Cond3' (I := I) GV K A fuel states initMem) (hstep : StepInv' (I := I) G GV K Er S Ob A fuel) :
    Theorem1IIPureXS' (I := I) G GV K Er S Ob A fuel := by
  intro B states initMem rF g hH E _ hpure hsafe c hc hlive
  obtain ⟨cf, hcf, hfin⟩ := hlive
  obtain ⟨π, k, h0, hk, hkl, hl⟩ := Path.ofReachable2 hc hcf
  have hfin' : (π.cfg π.len).final = true := hl ▸ hfin
  have hNT : ∀ j, j ≤ π.len → (π.cfg j).NTFree A := fun j hj => hH _ (h0 ▸ π.reachable j hj)
  have hinv : ∀ J, J ≤ π.len → Inv' G GV K Er S A π B g J := by
    intro J
    induction J with
    | zero => intro _; exact inv_zero' ErOK π h0 E hsafe
    | succ J ih => intro hJ; exact hstep π B g states initMem h0 hfin' hNT hpure J (by omega) (ih (by omega))
  obtain ⟨R, -⟩ := hinv π.len (Nat.le_refl _)
  obtain ⟨v, rF', g', hv, E', hle, hB⟩ := conclude' ErOK π (h3 states initMem) h0 hfin' R hkl
  exact ⟨v, rF', g', hk ▸ hv, E', hle, hB⟩

/-- **Theorem 1′ for the SLR-adapted model from condition (3)**, under (O5)
`PromisePure'` (in `Theorem1IIPure'`; `PromiseObl'` in general), and the open case (d1) of the induction
step (`CaseD1'`, O3 replay and prepay; discharged by `caseD1'` in
`SLR/Theorem1D1.lean`, see `theorem1II_pure'`). Cases (a)/(c) are proved
(`caseNow'`, with (O7) `liveWfProm`), case (b) too (`step_stutter'`), case (d2)
from `PromisePure'` (`caseD2'`). -/
theorem theorem1II_of_cond3' {G GV : PrepayGuard I} {K : K2Frame (model I)} {Er : ErasureP I}
    {S : StepGuard (modelErase I Er)} {Ob : PromiseOb} (ErOK : ChainExt Er Ob) (GVOK : GuardOK GV) [I.LawfulState] {A : Arch} {fuel : Nat}
    (h3 : ∀ states initMem, Cond3' (I := I) GV K A fuel states initMem)
    (hd1 : CaseD1' (I := I) G GV K Er S A fuel) :
    Theorem1IIPureXS' (I := I) G GV K Er S Ob A fuel :=
  theorem1II_of_step' ErOK h3
    (stepInv_of_cases' GVOK (caseNow' ErOK GVOK (liveWfProm A fuel)) (casePromise_of' hd1 (caseD2' ErOK GVOK)))

/-! ## The existing names: instances at `G₀`, `GRF`, `K2₀` (`SLR/NPSafePGen.lean`)

Statements verbatim from the existing chain; the `Prop` definitions keep their
existing bodies (definitionally the generic ones at `G₀`, `GRF`, `K2₀`, with
`NPSafe` for `NPSafeP … G₀ (K2₀ _)`). -/

section MergedMachine

variable {A : Arch} {fuel : Nat}


/-- **(S1′) with the advanced state exposed** (`Config.advanceable_of_path`,
whose statement hides it): the thread advances to its state on the path,
restricted to the current memory. -/
theorem advanceable_of_path' {c0 c c1 : Config I}
    (h0 : c0.Wf) (hc : ReachableK A c0 c) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t)
    {ts : Time} (hts : ts ∈ t.prom) (hr : ReachableK A c c1) {t1 : Thread I}
    (ht1 : c1.threads[tid]? = some t1) (hts1 : ts ∈ t1.prom) (hrel : t1.RelFulfils A tid ts c1.mem)
    (hnt : t1.NoNTStores ts) (hnx : t1.NextNoNT A) :
    ThreadNP A tid (t, c.mem) (t1.restrict c.mem, c.mem) ∧ ts ∈ (t1.restrict c.mem).prom ∧
      (t1.restrict c.mem).RelFulfils A tid ts c.mem := by
  npgen advanceable_of_pathG'


end MergedMachine

section MergedInvariant

variable (A : Arch) {fuel : Nat} (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost)


/-- **A prefix run** of the existing chain: `PRun'` at `GRF`, `K2₀`. -/
abbrev PRun (J : Nat) : Type := PRun' GRF (K2₀ (model I)) Erase A π B g0 J

end MergedInvariant

section MergedPRunFields

variable {A : Arch} {fuel : Nat} {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}

abbrev PRun.N (self : PRun A π B g0 J) : Nat := PRun'.N self
abbrev PRun.cfg (self : PRun A π B g0 J) : Nat → Config I := PRun'.cfg self
abbrev PRun.rF (self : PRun A π B g0 J) : Nat → Nat → Res := PRun'.rF self
abbrev PRun.g (self : PRun A π B g0 J) : Nat → Ghost := PRun'.g self
abbrev PRun.pos (self : PRun A π B g0 J) : Nat → Nat := PRun'.pos self
theorem PRun.pos_zero (self : PRun A π B g0 J) : self.pos 0 = 0 := PRun'.pos_zero self
theorem PRun.pos_mono (self : PRun A π B g0 J) : ∀ j, j < J → self.pos j ≤ self.pos (j + 1) :=
  PRun'.pos_mono self
theorem PRun.pos_J (self : PRun A π B g0 J) : self.pos J = self.N := PRun'.pos_J self
theorem PRun.cfg_zero (self : PRun A π B g0 J) : self.cfg 0 = π.cfg 0 := PRun'.cfg_zero self
theorem PRun.erase (self : PRun A π B g0 J) :
    ∀ μ, μ ≤ self.N → Erase (self.rF μ) (self.g μ) (fun _ => True) (self.cfg μ) :=
  PRun'.erase self
theorem PRun.step (self : PRun A π B g0 J) : ∀ μ, μ < self.N →
    MicroStep A (self.cfg μ) (self.rF μ) (self.g μ) (self.cfg (μ + 1)) (self.rF (μ + 1)) (self.g (μ + 1)) :=
  PRun'.step self
theorem PRun.virtual (self : PRun A π B g0 J) : ∀ j, j ≤ J → (π.cfg j).VirtualOf A (self.cfg (self.pos j)) :=
  PRun'.virtual self
theorem PRun.mem (self : PRun A π B g0 J) : ∀ μ, μ ≤ self.N → ∃ j, j ≤ π.len ∧ (self.cfg μ).mem = (π.cfg j).mem :=
  PRun'.mem self
theorem PRun.real (self : PRun A π B g0 J) : ∀ μ, μ ≤ self.N → ∀ (s : Nat) (t : Thread I),
    (self.cfg μ).threads[s]? = some t →
    ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧
      ∀ p ∈ t.prom, p ∈ tj.prom :=
  PRun'.real self
theorem PRun.le0 (self : PRun A π B g0 J) : ∀ μ, μ ≤ self.N → g0.Le (self.g μ) := PRun'.le0 self
theorem PRun.doneB (self : PRun A π B g0 J) : ∀ j, j ≤ J →
    (∀ μ, μ < self.pos j → Erase (self.rF μ) (self.g μ) (fun _ => False) (self.cfg μ)) →
    ∀ tid, (self.cfg (self.pos j)).Done tid →
      B (self.cfg (self.pos j)) (self.rF (self.pos j) tid) (self.g (self.pos j)) :=
  PRun'.doneB self

/-- The constructor of `PRun`. -/
abbrev PRun.mk (N : Nat) (cfg : Nat → Config I) (rF : Nat → Nat → Res) (g : Nat → Ghost) (pos : Nat → Nat)
    (pos_zero : pos 0 = 0) (pos_mono : ∀ j, j < J → pos j ≤ pos (j + 1)) (pos_J : pos J = N)
    (cfg_zero : cfg 0 = π.cfg 0) (erase : ∀ μ, μ ≤ N → Erase (rF μ) (g μ) (fun _ => True) (cfg μ))
    (step : ∀ μ, μ < N → MicroStep A (cfg μ) (rF μ) (g μ) (cfg (μ + 1)) (rF (μ + 1)) (g (μ + 1)))
    (virtual : ∀ j, j ≤ J → (π.cfg j).VirtualOf A (cfg (pos j)))
    (mem : ∀ μ, μ ≤ N → ∃ j, j ≤ π.len ∧ (cfg μ).mem = (π.cfg j).mem)
    (real : ∀ μ, μ ≤ N → ∀ (s : Nat) (t : Thread I), (cfg μ).threads[s]? = some t →
      ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧
        ∀ p ∈ t.prom, p ∈ tj.prom)
    (le0 : ∀ μ, μ ≤ N → g0.Le (g μ))
    (doneB : ∀ j, j ≤ J → (∀ μ, μ < pos j → Erase (rF μ) (g μ) (fun _ => False) (cfg μ)) →
      ∀ tid, (cfg (pos j)).Done tid → B (cfg (pos j)) (rF (pos j) tid) (g (pos j))) :
    PRun A π B g0 J :=
  PRun'.mk N cfg rF g pos pos_zero pos_mono pos_J cfg_zero erase step virtual mem real le0 doneB

end MergedPRunFields

section MergedInvariant'

variable (A : Arch) {fuel : Nat} (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost)


/-- Micro-indices of real indices `≤ J` are `≤ N`. -/
theorem PRun.pos_le {J : Nat} (R : PRun A π B g0 J) : ∀ j, j ≤ J → R.pos j ≤ R.N := by
  npgen PRun'.pos_le

/-- A full prefix run is an annotated run. -/
def PRun.toAnnRun (R : PRun A π B g0 π.len) : AnnRun A π := by
  npgen PRun'.toAnnRun

/-- The advancement status of thread `i` at real index `J`, with target
index `p` and virtual state `v.threads[i]`:

- *not advanced*: `p = J`, the virtual thread is the real one, and no
  promise of `i` is pending;
- *advanced*: `F`, the instruction at real step `p ≥ J` of `π`, is an
  instruction of `i` that fulfils a pending promise `ts` (prepaid), which is
  outstanding at every index in `[J, p]` and which `F` can fulfil with a
  release store (`Thread.RelFulfils`); the virtual thread is `i`'s real state
  at `p`, restricted to the memory at `J`. All pending promises of `i` are
  fulfilled by `F`. -/
def Status (J : Nat) (v : Config I) (g : Ghost) (i p : Nat) : Prop :=
  (p = J ∧ v.threads[i]? = (π.cfg J).threads[i]? ∧
      ∀ t, v.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∉ g.pend) ∨
  (p < π.len ∧ ∃ tp, (π.cfg p).threads[i]? = some tp ∧ v.threads[i]? = some (tp.restrict (π.cfg J).mem) ∧
    (∃ ts ∈ g.pend, ts ∈ tp.prom ∧ tp.RelFulfils A i ts (π.cfg p).mem ∧
      ∀ q, J ≤ q → q ≤ p → ∃ tq, (π.cfg q).threads[i]? = some tq ∧ ts ∈ tq.prom) ∧
    (∃ tp', (π.cfg (p + 1)).threads[i]? = some tp' ∧ NPStepBy A i (π.cfg p) (π.cfg (p + 1)) ∧
      ∀ ts ∈ g.pend, ts ∈ tp.prom → ts ∉ tp'.prom))

/-- **Thread `i` is in order at real index `J`** (components (I1), (I3), (I5) of
the invariant): a safety token (`NPSafe` at a saved
configuration `s`, ghost `gs`, from which the current virtual configuration
`v` is an environment extension, with clean flag `cl`), the own-pending
condition at `v`, the step-index budget, and the advancement status. -/
def ThreadOkP (J : Nat) (cl : Prop) (v : Config I) (rF : Nat → Res) (g : Ghost) (i p : Nat) : Prop :=
  ∃ (s : Config I) (gs : Ghost) (n : Nat), J ≤ p ∧ p ≤ π.len ∧
    NPSafe (model I) A B i (n + 1) 0 cl s (rF i) gs ∧ EnvExt i s v ∧ gs.Le g ∧
    (∀ t, v.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ gs.pend) ∧
    (π.len - p) + (π.len - J) < n ∧
    Status A π J v g i p

/-- `ThreadOkP` for some target index `p`. -/
def ThreadOk (J : Nat) (cl : Prop) (v : Config I) (rF : Nat → Res) (g : Ghost) (i : Nat) : Prop :=
  ∃ p, ThreadOkP A π B J cl v rF g i p

/-- The prefix run is valid (full erasure) at every micro-index below `μ'`:
the clean flag of every token at `μ'`. -/
def PRun.Clean {J : Nat} (R : PRun A π B g0 J) (μ' : Nat) : Prop :=
  ∀ μ, μ < μ' → Erase (R.rF μ) (R.g μ) (fun _ => False) (R.cfg μ)

/-- **The invariant at real index `J`**: a prefix run and every thread in
order at its last micro-configuration, its token's clean flag being the
validity of the run so far. -/
def Inv (J : Nat) : Prop :=
  ∃ R : PRun A π B g0 J, ∀ i, i < (R.cfg R.N).threads.size →
    ThreadOk A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i


end MergedInvariant'


/-- **`Inv 0`**: the initial configuration, the initial resources and ghost,
every thread's token at `Config.init` with a large enough index. -/
theorem inv_zero {A : Arch} {fuel : Nat} (π : Path A fuel I) {B : Config I → Res → Ghost → Prop}
    {states : List I.State} {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem)
    {rF : Nat → Res} {g : Ghost} (E : Erase rF g (fun _ => False) (Config.init states initMem))
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g) :
    Inv A π B g 0 := by
  npgen inv_zero'

/-- **The conclusion** from a full prefix run and condition (3): at real
index `k`, the micro-configuration is a virtual configuration with full
erasure, the initial world facts, and the postconditions of done threads. -/
theorem conclude {A : Arch} {fuel : Nat} [I.LawfulState] (π : Path A fuel I) {B : Config I → Res → Ghost → Prop}
    {g0 : Ghost} {states : List I.State} {initMem : List (Loc × Val)} (h3 : Cond3 A fuel states initMem)
    (h0 : π.cfg 0 = Config.init states initMem) (hf : (π.cfg π.len).final = true)
    (R : PRun A π B g0 π.len) {k : Nat} (hk : k ≤ π.len) :
    ∃ v rF' g', (π.cfg k).VirtualOf A v ∧ Erase rF' g' (fun _ => False) v ∧ g0.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' := by
  npgen conclude'


section MergedStep

variable {A : Arch} {fuel : Nat}


/-- **The status of a thread that does not step** (frame): if the real step
`J → J + 1` leaves thread `i` unchanged, the virtual thread `i` is unchanged,
pending marks of `i`'s promises are kept while they are outstanding and none
are created, and restriction to the new memory agrees with restriction to the
old one on `i`'s later states (the new messages are not `i`'s), then `i`'s
status carries over to `J + 1`: a not-advanced thread stays not advanced, an
advanced one keeps its target (which is not `J`: its target step changes it). -/
theorem status_frame [I.LawfulState] {π : Path A fuel I} {states : List I.State} {initMem : List (Loc × Val)}
    (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J < π.len)
    {v v' : Config I} {g g' : Ghost} {i p : Nat}
    (hthr : (π.cfg (J + 1)).threads[i]? = (π.cfg J).threads[i]?)
    (hvv : v'.threads[i]? = v.threads[i]?)
    (hkeep : ∀ ts ∈ g.pend, (∃ t, v'.threads[i]? = some t ∧ ts ∈ t.prom) → ts ∈ g'.pend)
    (hback : ∀ ts ∈ g'.pend, ts ∈ g.pend)
    (hrestr : ∀ q tq, J < q → q ≤ π.len → (π.cfg q).threads[i]? = some tq →
      tq.restrict (π.cfg (J + 1)).mem = tq.restrict (π.cfg J).mem)
    (hJp : J ≤ p) (hst : Status A π J v g i p) :
    ∃ p', J + 1 ≤ p' ∧ p' ≤ π.len ∧ (π.len - p') + (π.len - (J + 1)) ≤ (π.len - p) + (π.len - J) ∧
      Status A π (J + 1) v' g' i p' := by
  npgen status_frameG

/-- `NPSafe`'s Done conjunct at an environment extension, from a token with
at least two step indices. -/
theorem NPSafe.done {M : ResModel I} {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafe M A B tid (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁) (hcl : cl) (hd : c₁.Done tid) : B c₁ r g₁ := by
  rw [NPSafe] at h
  have h1 := h (0 + 1)
  rw [NPSafe] at h1
  exact (h1 c₁ g₁ he hg).1 hcl hd

/-- `NPSafe`'s step at an environment extension, from a token with at least
two step indices: the continuation keeps one. -/
theorem NPSafe.stepAt {M : ResModel I} {B : Config I → M.R → M.Ghost → Prop} {tid k : Nat} {cl : Prop}
    {c c₁ : Config I} {r : M.R} {g g₁ : M.Ghost} (h : NPSafe M A B tid (k + 1 + 1) 0 cl c r g)
    (he : EnvExt tid c c₁) (hg : M.ghostLe g g₁)
    (hown : ∀ t, c₁.threads[tid]? = some t → ∀ ts ∈ t.prom, M.pendingAt g₁ ts → M.pendingAt g ts)
    (rF : Nat → M.R) (c' : Config I) (E : M.erase (M.upd rF tid r) g₁ (fun _ => True) c₁)
    (hs : NPStepBy A tid c₁ c') (hinv : c₁.MachInv) (hw : c₁.WfProm tid) (hw' : c'.WfProm tid) :
    ∃ r' g', M.erase (M.upd rF tid r') g' (fun _ => True) c' ∧ M.ghostLe g₁ g' ∧
      (∀ ts, M.pendingAt g₁ ts → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
        M.pendingAt g' ts) ∧
      (∀ ts, M.pendingAt g' ts → M.pendingAt g₁ ts) ∧
      NPSafe M A B tid (k + 1) 0 (cl ∧ M.erase (M.upd rF tid r) g₁ (fun _ => False) c₁) c' r' g' ∧
      M.acqLe r' g' r g₁ ∧
      (∀ w, Written tid c₁ c' w → M.owns r w.loc) ∧
      (∀ b, b ≤ c₁.mem.last → ∀ ρ x, M.reach ρ g' x b → M.reach ρ g₁ x b) ∧
      (∀ b, b ≤ c₁.mem.last →
        (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
        ∀ x, M.reach r' g' x b → M.reach r g₁ x b) := by
  rw [NPSafe] at h
  have h1 := h (0 + 1)
  rw [NPSafe] at h1
  exact (h1 c₁ g₁ he hg).2.1 rF c' E hs hinv hw hw' hown

/-- **The postcondition of a done thread** from its token: the budget leaves
at least one step index, so the token's Done conjunct applies at `v`, under
the clean flag. -/
theorem ThreadOkP.done {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {J : Nat} {cl : Prop}
    {v : Config I} {rF : Nat → Res} {g : Ghost} {i p : Nat} (h : ThreadOkP A π B J cl v rF g i p)
    (hcl : cl) (hd : v.Done i) : B v (rF i) g := by
  npgen ThreadOkP'.done

/-- The clean flag of a thread's token may be strengthened. -/
theorem ThreadOkP.mono_flag {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {J : Nat} {cl cl' : Prop}
    {v : Config I} {rF : Nat → Res} {g : Ghost} {i p : Nat} (h : ThreadOkP A π B J cl v rF g i p)
    (hc : cl' → cl) : ThreadOkP A π B J cl' v rF g i p := by
  npgen ThreadOkP'.mono_flag

/-- **A thread of the virtual configuration is a real state restricted to
the memory at `J`**: the state at `J` itself (not advanced) or at the target
(advanced). -/
theorem Status.restrictOf [I.LawfulState] {π : Path A fuel I} {states : List I.State}
    {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem) {J : Nat} (hJ : J ≤ π.len)
    {v : Config I} {g : Ghost} {i p : Nat} (hp : p ≤ π.len) (hJp : J ≤ p) (hst : Status A π J v g i p)
    {t : Thread I} (ht : v.threads[i]? = some t) :
    ∃ (q : Nat) (tq : Thread I), J ≤ q ∧ q ≤ π.len ∧ (π.cfg q).threads[i]? = some tq ∧
      t = tq.restrict (π.cfg J).mem := by
  npgen Status'.restrictOf

/-- **The virtual configuration from the statuses**: same memory and size as
the real configuration at `J`; a not-advanced thread is the real one, an
advanced one is the real one advanced ((S1′), `advanceable_of_path'`). -/
theorem virtual_of_status [I.LawfulState] {π : Path A fuel I} {states : List I.State}
    {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem)
    (hNT : ∀ j, j ≤ π.len → (π.cfg j).NTFree A) {J : Nat} (hJ : J ≤ π.len) {v : Config I} {g : Ghost}
    (hmem : v.mem = (π.cfg J).mem) (hsize : v.threads.size = (π.cfg J).threads.size)
    (hst : ∀ i, i < v.threads.size → ∃ p, J ≤ p ∧ Status A π J v g i p) :
    (π.cfg J).VirtualOf A v := by
  npgen virtual_of_status'

/-- **Extend a prefix run by one micro-step** to the next real index: the
new micro-configuration `c'` is the virtual configuration at `J + 1`. The
postconditions of done threads at `c'` are asked under the validity of the
extended run (`R.Clean R.N` and full erasure at the old last configuration). -/
def PRun.snoc {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}
    (R : PRun A π B g0 J) (c' : Config I) (rF' : Nat → Res) (g' : Ghost)
    (E : Erase rF' g' (fun _ => True) c') (hstep : MicroStep A (R.cfg R.N) (R.rF R.N) (R.g R.N) c' rF' g')
    (hV : (π.cfg (J + 1)).VirtualOf A c') (hmem : ∃ j, j ≤ π.len ∧ c'.mem = (π.cfg j).mem)
    (hreal : ∀ (s : Nat) (t : Thread I), c'.threads[s]? = some t →
      ∃ (j : Nat) (tj : Thread I), j ≤ π.len ∧ (π.cfg j).threads[s]? = some tj ∧ t.views = tj.views ∧
        ∀ p ∈ t.prom, p ∈ tj.prom)
    (hle : g0.Le g')
    (hdone : R.Clean A π B g0 R.N ∧ Erase (R.rF R.N) (R.g R.N) (fun _ => False) (R.cfg R.N) →
      ∀ tid, c'.Done tid → B c' (rF' tid) g') : PRun A π B g0 (J + 1) := by
  npgen PRun'.snoc

/-- The validity of the extended run gives the validity of the old one and
full erasure at its last configuration (the clean flag of a token that took
the new micro-step). -/
theorem PRun.snoc_clean {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost} {J : Nat}
    (R : PRun A π B g0 J) {c' : Config I} {rF' : Nat → Res} {g' : Ghost} {E hstep hV hmem hreal hle hdone}
    (h : (R.snoc c' rF' g' E hstep hV hmem hreal hle hdone).Clean A π B g0 (R.N + 1)) :
    R.Clean A π B g0 R.N ∧ Erase (R.rF R.N) (R.g R.N) (fun _ => False) (R.cfg R.N) := by
  npgen PRun'.snoc_clean

/-- **Case (b): a stutter step of an advanced thread.** The real step `J`
is an instruction of thread `j`, which is advanced with target `p > J`. Its
promise `ts` stays outstanding, so the step is a `StutterStep`
(`stutterStep_release`): memory is unchanged. The prefix run is not extended
(`pos (J + 1) = pos J`); the virtual configuration stays a virtual
configuration of the new real one ((S1′) from `π (J + 1)` to `π p`), and
every thread keeps its token and status. -/
theorem step_stutter [I.LawfulState] {π : Path A fuel I} {B : Config I → Res → Ghost → Prop} {g0 : Ghost}
    {states : List I.State} {initMem : List (Loc × Val)} (h0 : π.cfg 0 = Config.init states initMem)
    (hNT : ∀ j, j ≤ π.len → (π.cfg j).NTFree A) {J : Nat} (hJ : J < π.len) (R : PRun A π B g0 J)
    (hok : ∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i)
    {j : Nat} {t : Thread I} {outs : List (Except String (Outcome I))} {o : Outcome I}
    (ht : (π.cfg J).threads[j]? = some t) (hs : stepOne A t j (π.cfg J).mem = some outs) (ho : .ok o ∈ outs)
    (hJ1 : π.cfg (J + 1) = (π.cfg J).withThread j o.thread o.mem) {p : Nat}
    (hjok : ThreadOkP A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) j p) (hp : J < p) :
    Inv A π B g0 (J + 1) := by
  npgen step_stutter'


end MergedStep


/-- **The promise `ts` of thread `j`, made at real step `J`, is fulfilled by
a release store on `π`**: at some later index `f`, `ts` having stayed
outstanding since `J + 1`, `j`'s next instruction can fulfil `ts` with a
release store leaving no promise dead (`Thread.RelFulfilsLive`, as `NPSafe`'s
prepay conjunct asks) and the real step `f` removes `ts` from `j`'s promises. Such a promise is accounted for by a `prepay` micro-step
(case (d1)); any other by a `promise` micro-step (case (d2)), which needs
the message to be pure (`PromisePure`). -/
def RelFulfilled {A : Arch} {fuel : Nat} (π : Path A fuel I) (J j : Nat) (ts : Time) : Prop :=
  ∃ f, J < f ∧ f < π.len ∧ (∀ q, J < q → q ≤ f → ∃ tq, (π.cfg q).threads[j]? = some tq ∧ ts ∈ tq.prom) ∧
    ∃ tf tf', (π.cfg f).threads[j]? = some tf ∧ tf.RelFulfilsLive A j ts (π.cfg f).mem ∧
      (π.cfg (f + 1)).threads[j]? = some tf' ∧ ts ∉ tf'.prom

/-- **(O5) Promises not fulfilled by a release store are pure**, as an
explicit hypothesis on the program, stated *a posteriori* over the real paths
from `Config.init states initMem` to a final configuration (like `Cond3`),
for the release predicates `rel` of the initial ghost (`Ghost.Le` keeps
`rel`, so they are those of every later ghost): on such a path, a promise of
`pw` by thread `j` at real step `J` that is not `RelFulfilled` writes a value
that is pure for its location's release predicate. This is what
`MicroStep.promise` (`Erase.promise`, SLR Lemmas 23–24) needs; `Erase.pure`
is unchanged (option (B) rejected). For the
spinlocks: the stores that are not release stores write values whose release
predicate is `emp` (lock value 1) or pure (data, counters). -/
def PromisePure (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State)
    (initMem : List (Loc × Val)) (rel : Loc → Pred) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J, J < π.len → ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    ¬ RelFulfilled π J j ((π.cfg J).mem.last + 1) →
    Pred.Pure (rel pw.1.loc) pw.1.val

/-- **Cases (a) and (c)** (`Prop`; proved as `caseNow` from (O7) `liveWfProm`): the real step `J` is an
instruction of thread `j` whose target is `J` itself: `j` is not advanced, or
it is advanced and the step is its fulfilling instruction `F`. The micro-run
takes one `np` step at the virtual configuration with the real outcome. -/
def CaseNow (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) →
    ∀ J, J < π.len → ∀ R : PRun A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (outs : List (Except String (Outcome I))) (o : Outcome I),
    (π.cfg J).threads[j]? = some t → stepOne A t j (π.cfg J).mem = some outs → .ok o ∈ outs →
    π.cfg (J + 1) = (π.cfg J).withThread j o.thread o.mem →
    ThreadOkP A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) j J →
    Inv A π B g0 (J + 1)

/-- **Case (d)**: the real step `J` is a (certified) promise of thread `j`,
under (O5) `PromisePure` for the initial ghost's release predicates. Split
(`casePromise_of`) into (d1) `CaseD1` (`RelFulfilled`) and (d2) `CaseD2`. -/
def CasePromise (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromisePure A fuel states initMem g0.rel →
    ∀ J, J < π.len → ∀ R : PRun A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    Inv A π B g0 (J + 1)

/-- **Case (d1)** (`Prop`; O3, proved as `caseD1` in `SLR/Theorem1D1.lean`): the promise is `RelFulfilled` at
some `f > J`. Replay `j`'s promise-free steps up to `f` on hybrid
configurations (`j`'s real states restricted to the memory at `J`; they are
`StutterStep`s since `ts` stays outstanding), then a `prepay` micro-step from
`j`'s token; `j` becomes advanced with target `f`. -/
def CaseD1 (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) →
    ∀ J, J < π.len → ∀ R : PRun A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    RelFulfilled π J j ((π.cfg J).mem.last + 1) →
    Inv A π B g0 (J + 1)

/-- **Case (d2)** (`Prop`; proved: `caseD2`): the promise is not
`RelFulfilled`; by `PromisePure` its message is pure, a `promise` micro-step
that transfers nothing. -/
def CaseD2 (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromisePure A fuel states initMem g0.rel →
    ∀ J, J < π.len → ∀ R : PRun A π B g0 J,
    (∀ i, i < (R.cfg R.N).threads.size →
      ThreadOk A π B J (R.Clean A π B g0 R.N) (R.cfg R.N) (R.rF R.N) (R.g R.N) i) →
    ∀ (j : Nat) (t : Thread I) (pw : Msg × View),
    (π.cfg J).threads[j]? = some t → CertWrite A j t (π.cfg J).mem pw →
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1 →
    ¬ RelFulfilled π J j ((π.cfg J).mem.last + 1) →
    Inv A π B g0 (J + 1)

/-- Case (d) from its two sub-cases. -/
theorem casePromise_of [I.LawfulState] {A : Arch} {fuel : Nat} (hd1 : CaseD1 (I := I) A fuel)
    (hd2 : CaseD2 (I := I) A fuel) : CasePromise (I := I) A fuel := by
  npgen casePromise_of'

/-- **Cases (a) and (c), proved from (O7)**: the real step is an
instruction of thread `j` with target `J`. The virtual thread `j` is the real
one (not advanced, or advanced with all promises below `|M|`), so the real
outcome is an `NPStepBy` at the virtual configuration; `j`'s token gives the
step (`NPSafe.stepAt`: own-pending from `ThreadOk`, erasure from the run, the
machine invariants of the virtual configuration from `machInv_of_restrict`,
`WfProm` from (O7)), recorded as an `np` micro-step. Afterwards `j` is not
advanced (none of its promises is pending: those pending before are
fulfilled by `F`, others are other threads'); every other thread keeps its
token (environment extension) and status (`status_frame`, `restrict_frame`). -/
theorem caseNow [I.LawfulState] {A : Arch} {fuel : Nat} (hO7 : LiveWfProm (I := I) A fuel) :
    CaseNow (I := I) A fuel := by
  npgen caseNow'

/-- **Case (d2), proved from (O5) `PromisePure`**: the promise of `pw` by
thread `j` at real step `J` is not `RelFulfilled`, so its message is pure for
the initial (= current) ghost's release predicate, and the micro-run takes a
`promise` micro-step at the virtual configuration (`Erase.promise`), with
resources and ghost unchanged. The promising thread keeps its token
(environment extension `EnvExt.promise`; the new promise is not pending).
If `j` is not advanced it stays so, with the real state at `J + 1`. If it is
advanced with target `p`, `p ≠ J` (the step at `p` fulfils the pending
promise, a promise step does not), the new promise `ts = |M_J| + 1` is still
outstanding at `p` (otherwise `j` fulfilled it before `p`, raising its
`relPre`/`vwOldNT` to `ts` above the pending `ts0`, which the release store at
`p` forbids: `Thread.HasOrPassed`, `Thread.RelFulfils.relPre_lt`,
`Thread.NoNTStores`); promise lists being sorted (`Path.promSorted`), the
virtual state with `ts` added is the target state restricted to `M_{J+1}`
(`filter_le_succ_of_sorted`). Other threads keep token and status
(`status_frame`, `restrict_frame`). -/
theorem caseD2 [I.LawfulState] {A : Arch} {fuel : Nat} : CaseD2 (I := I) A fuel := by
  npgen caseD2'

/-- **The step of the induction from its cases**: the real step is an
instruction (`succs_cases`) of a thread whose target is later (case (b),
`step_stutter`, proved) or now (`CaseNow`), or a promise (`CasePromise`). -/
theorem stepInv_of_cases [I.LawfulState] {A : Arch} {fuel : Nat} (hnow : CaseNow (I := I) A fuel)
    (hprom : CasePromise (I := I) A fuel) :
    ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromisePure A fuel states initMem g0.rel →
    ∀ J, J < π.len → Inv A π B g0 J → Inv A π B g0 (J + 1) := by
  npgen stepInv_of_cases'

/-- **The step of the induction** (`Prop`): along a path from `Config.init` to
a final configuration within the scope `Config.NTFree`, under (O5)
`PromisePure` for the initial ghost, the invariant at `J` gives the invariant
at `J + 1`. Its cases are the lemmas above. -/
def StepInv (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (π : Path A fuel I) (B : Config I → Res → Ghost → Prop) (g0 : Ghost) (states : List I.State)
    (initMem : List (Loc × Val)), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    (∀ j, j ≤ π.len → (π.cfg j).NTFree A) → PromisePure A fuel states initMem g0.rel →
    ∀ J, J < π.len → Inv A π B g0 J → Inv A π B g0 (J + 1)

/-- **Theorem 1′ for the SLR-adapted model, under (O5)**: `Theorem1II`
(`NPSafeImpliesAdequateV` for `model`, `VirtualRel.ii`, scope
`Config.NTFree`) with the extra hypothesis `PromisePure` for the initial
ghost's release predicates. (The laws arguments of `NPSafeImpliesAdequateV`
are not used and are dropped.) The per-thread `NPSafe` is required only for
the threads of the initial configuration (`tid < states.length`): machine
steps keep the number of threads, and for a nonexistent `tid` `EnvExt` does
not constrain the extended configuration, so `NPSafe` there is not provable
in general. -/
def Theorem1IIPure (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    PromisePure A fuel states initMem g.rel →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', (VirtualRel.ii A).rel c v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- `Theorem1II` is `Theorem1IIPure` when `PromisePure` holds for every
initial ghost (e.g. for programs without promises of impure values). -/
theorem Theorem1IIPure.theorem1II [I.LawfulState] {A : Arch} {fuel : Nat} (h : Theorem1IIPure (I := I) A fuel)
    (hp : ∀ states initMem (g : Ghost), PromisePure (I := I) A fuel states initMem g.rel) :
    Theorem1II (I := I) A fuel := by
  intro _ _ B states initMem rF g hH E hnp hsafe c hc hlive
  exact h B states initMem rF g hH E hnp (hp states initMem g) hsafe c hc hlive

/-- **Theorem 1′ for the SLR-adapted model** (`Theorem1IIPure`) from condition
(3) and the step of the induction. -/
theorem theorem1II_of_step [I.LawfulState] {A : Arch} {fuel : Nat}
    (h3 : ∀ states initMem, Cond3 (I := I) A fuel states initMem) (hstep : StepInv (I := I) A fuel) :
    Theorem1IIPure (I := I) A fuel := by
  npgen theorem1II_of_step'

/-- **Theorem 1′ for the SLR-adapted model from condition (3)**, under (O5)
`PromisePure` (in `Theorem1IIPure`), and the open case (d1) of the induction
step (`CaseD1`, O3 replay and prepay; discharged by `caseD1` in
`SLR/Theorem1D1.lean`, see `theorem1II_pure`). Cases (a)/(c) are proved
(`caseNow`, with (O7) `liveWfProm`), case (b) too (`step_stutter`), case (d2)
from `PromisePure` (`caseD2`). -/
theorem theorem1II_of_cond3 [I.LawfulState] {A : Arch} {fuel : Nat}
    (h3 : ∀ states initMem, Cond3 (I := I) A fuel states initMem)
    (hd1 : CaseD1 (I := I) A fuel) :
    Theorem1IIPure (I := I) A fuel := by
  npgen theorem1II_of_cond3'

end Kraken.Promising.SLR

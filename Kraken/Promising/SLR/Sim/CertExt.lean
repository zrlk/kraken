/-
Simulation library, part 5: B2, the certification-extension lemma

A thread's certification run at memory `M` (`CertOk`) still certifies when
other threads append messages, before the run or *between* its replayed
steps. The replay is the `SimState` game of `Run.lean`: a source step is
matched by a target step (`SimState.step`), a foreign append adds the current
source memory size as a threshold (`SimState.appendForeign`).

## The side condition `StaleFree` is the consumer's

`StaleFree` is the hypothesis the proof uses: the replay matches a source
step only where its event tree is `StaleFree` at the thresholds in force.
Whether B2 holds from `CertOk` alone, without it, is open. What it asks
(`StaleFree`, `Run.lean`): a read of a watched location (one the foreign
messages write) from a timestamp at most a threshold has its read bound at
most that threshold, and an exclusive or RMW write to a watched location is
paired with a read above it. Once the run has seen past the base memory, it
never reads a base message of a location the other threads write, and never
claims atomicity over one.
(The machine does not depend on the answer: `succsL` re-certifies only the
thread that steps, so a thread that stopped certifying, if that can happen,
is stuck, not unsound.)

So the hypothesis the consumer supplies is precisely: the certification run,
interleaved with the foreign appends (`SchedSF`), is `StaleFree` at every
threshold in force at each of its steps, for the locations `L` the foreign
messages write. For appends that all happen before the run (one threshold,
`|M|`), that is `ThreadSF A tid |M| L` (`certOk_memExt`, `certOk_envExt`).

## Contents

- `SchedSF`: the source side of a schedule (`none` = the certifying thread's
  next step, `some w` = a foreign append of `w`), with `StaleFree` at the
  thresholds in force; `SchedRun`: the target side (thread steps and the
  appends, in schedule order), with `SchedRun.append` / `SchedRun.ofNP`.
- `SchedSF.sim`: the induction over the schedule on top of `SimState`.
- `certOk_extAppend` (**B2**): a run that empties the promise set at `M`,
  replayed under any schedule of foreign appends, empties it at the end of
  the interleaved run; `certOk_extAppend_mid`: `CertOk` at every point of the
  schedule after which no further foreign append happens.
- `certOk_envExt`: the configuration-level corollary: the other threads'
  appends (`EnvExt`, the thread itself unchanged) preserve its certification.
-/
import Kraken.Promising.SLR.Sim.Instances

namespace Kraken.Promising

namespace Sim

section CertExt

variable {I : ISA} (A : Arch) (tid : Nat)

/-- **Source side of a replay schedule.** The certifying thread's solo run
from `p` to `r`, interleaved with foreign appends: `none` is the thread's next
step, whose event tree must be `StaleFree` at every threshold in force;
`some w` is another thread appending `w` (to a watched location), which adds
the current source memory size as a threshold. -/
inductive SchedSF (L : Loc → Prop) : (Nat → Prop) → Thread I × Memory → List (Option Msg) →
    Thread I × Memory → Prop
  | nil (N : Nat → Prop) (p : Thread I × Memory) : SchedSF L N p [] p
  | append {N : Nat → Prop} {p r : Thread I × Memory} {ws : List (Option Msg)} (w : Msg) : L w.loc →
      SchedSF L (fun n => N n ∨ n = p.2.last) p ws r → SchedSF L N p (some w :: ws) r
  | step {N : Nat → Prop} {p p₁ r : Thread I × Memory} {ws : List (Option Msg)} : ThreadStep A tid p p₁ →
      (∀ tree, I.exec p.1.st = some tree → ∀ n, N n → StaleFree A tid (instrViews p.1 (I.deps p.1.st)) n L
        { views := p.1.views, prom := p.1.prom, mem := p.2, log := [.instr tid (I.showInstr p.1.st)] } tree) →
      SchedSF L N p₁ ws r → SchedSF L N p (none :: ws) r

/-- **Target side of a replay schedule.** The thread's steps (`none`) and the
foreign appends (`some w`) to its memory, in schedule order. -/
inductive SchedRun : Thread I × Memory → List (Option Msg) → Thread I × Memory → Prop
  | nil (q : Thread I × Memory) : SchedRun q [] q
  | append {q r : Thread I × Memory} {ws : List (Option Msg)} (w : Msg) :
      SchedRun (q.1, (q.2.append w).1) ws r → SchedRun q (some w :: ws) r
  | step {q q₁ r : Thread I × Memory} {ws : List (Option Msg)} : ThreadStep A tid q q₁ →
      SchedRun q₁ ws r → SchedRun q (none :: ws) r

variable {A tid}

/-- A schedule run splits at any point of the schedule. -/
theorem SchedRun.split {q r : Thread I × Memory} :
    ∀ {s₁ s₂ : List (Option Msg)}, SchedRun A tid q (s₁ ++ s₂) r →
      ∃ q₁, SchedRun A tid q s₁ q₁ ∧ SchedRun A tid q₁ s₂ r
  | [], _, h => ⟨q, .nil q, h⟩
  | some w :: s₁, s₂, h => by
    cases h with
    | append _ h =>
      obtain ⟨q₁, h1, h2⟩ := SchedRun.split (s₁ := s₁) h
      exact ⟨q₁, .append w h1, h2⟩
  | none :: s₁, s₂, h => by
    cases h with
    | step hs h =>
      obtain ⟨q₁, h1, h2⟩ := SchedRun.split (s₁ := s₁) h
      exact ⟨q₁, .step hs h1, h2⟩

/-- A schedule run without foreign appends is a promise-free solo run. -/
theorem SchedRun.toNP {q r : Thread I × Memory} :
    ∀ {k : Nat}, SchedRun A tid q (List.replicate k none) r → ThreadNP A tid q r
  | 0, h => by cases h; exact .refl _
  | k + 1, h => by
    cases h with
    | step hs h => exact .step hs (SchedRun.toNP (k := k) h)

/-- `PromRel` relates no source promise to no target promise. -/
theorem PromRel.nil_left {ρ : TMap} {xs ys : List Time} (h : PromRel ρ xs ys) (e : xs = []) : ys = [] := by
  cases h with
  | nil => rfl
  | keep => cases e
  | drop => cases e

variable {L : Loc → Prop} {N : Nat → Prop}

/-- **The replay, over a schedule.** From a `SimState`, a source schedule
(`SchedSF`) is matched by a target schedule run (`SchedRun`) with the same
foreign appends, ending in a `SimState` for an extension of the map and the
final set of thresholds. -/
theorem SchedSF.sim {p r : Thread I × Memory} {sched : List (Option Msg)} (h : SchedSF A tid L N p sched r) :
    ∀ (ρ : TMap) (q : Thread I × Memory), SimState ρ N L p q →
      ∃ (ρ' : TMap) (N' : Nat → Prop) (q' : Thread I × Memory), SchedRun A tid q sched q' ∧
        SimState ρ' N' L r q' := by
  induction h with
  | nil N p =>
    intro ρ q hs
    exact ⟨ρ, N, q, .nil q, hs⟩
  | append w hw _ ih =>
    intro ρ q hs
    obtain ⟨t', M'⟩ := q
    obtain ⟨ρ', N', q', h', hs'⟩ := ih ρ (t', (M'.append w).1) (hs.appendForeign hw)
    exact ⟨ρ', N', q', .append w h', hs'⟩
  | step hstep hsf _ ih =>
    intro ρ q hs
    obtain ⟨ρ1, q₁, hq, hs1, -⟩ := hs.step A tid hstep hsf
    obtain ⟨ρ', N', q', h', hs'⟩ := ih ρ1 q₁ hs1
    exact ⟨ρ', N', q', .step hq h', hs'⟩

/-- The start of a certification replay: a bounded thread, its promises in
`M`, related to itself on `M` at the single threshold `|M|`. -/
theorem SimState.cert {t : Thread I} {M : Memory} (hb : t.Bnd M.last) (hpb : ∀ s ∈ t.prom, s ≤ M.last) :
    SimState (TMap.idUpTo M.last) (· = M.last) L (t, M) (t, M) :=
  SimState.memExt hb hpb (Memory.Prefix.refl M)
    (fun _ _ h hw => absurd (M.last_le_of_get?_eq_some hw) (Nat.not_le_of_lt h))

/-- **B2: certification under interleaved foreign appends.** A bounded thread
(promises in `M`) whose certification run at `M` (a solo run emptying its
promise set) is replayed under a schedule of foreign appends to watched
locations, `StaleFree` at the thresholds in force at each step (`SchedSF`),
has a matching interleaved run from `(t, M)` with the same appends that
empties its promise set too. -/
theorem certOk_extAppend {t : Thread I} {M : Memory} (hb : t.Bnd M.last) (hpb : ∀ s ∈ t.prom, s ≤ M.last)
    {sched : List (Option Msg)} {r : Thread I × Memory} (h : SchedSF A tid L (· = M.last) (t, M) sched r)
    (hr : r.1.prom = []) :
    ∃ q, SchedRun A tid (t, M) sched q ∧ q.1.prom = [] := by
  obtain ⟨ρ', N', q, hq, hs⟩ := h.sim _ _ (SimState.cert hb hpb)
  exact ⟨q, hq, PromRel.nil_left hs.thread.prom hr⟩

/-- **B2, `CertOk` form.** At every point of the schedule after which only
replayed steps remain (no further foreign append), the replayed thread
certifies (`CertOk`) against the memory it has then: the original memory with
the foreign messages appended so far interleaved with its own writes. -/
theorem certOk_extAppend_mid {t : Thread I} {M : Memory} (hb : t.Bnd M.last) (hpb : ∀ s ∈ t.prom, s ≤ M.last)
    {s₁ : List (Option Msg)} {k : Nat} {r : Thread I × Memory}
    (h : SchedSF A tid L (· = M.last) (t, M) (s₁ ++ List.replicate k none) r) (hr : r.1.prom = []) :
    ∃ q₁, SchedRun A tid (t, M) s₁ q₁ ∧ CertOk A tid q₁.1 q₁.2 := by
  obtain ⟨q, hq, hp⟩ := certOk_extAppend hb hpb h hr
  obtain ⟨q₁, h1, h2⟩ := hq.split
  exact ⟨q₁, h1, q.1, q.2, h2.toNP, hp⟩

/-- **B2, configuration level.** If the other threads' steps take `c` to `c'`
(`EnvExt`: the memory only grows) and leave thread `tid` unchanged, a
certification run of `tid` at `c` that is `StaleFree` at `|c.mem|` for the
locations the new messages write transfers to `c'`. -/
theorem certOk_envExt {c c' : Config I} (he : EnvExt tid c c') {t : Thread I} (ht' : c'.threads[tid]? = some t) (hb : t.Bnd c.mem.last) (hpb : ∀ s ∈ t.prom, s ≤ c.mem.last)
    (hL : ∀ s' w, c.mem.last < s' → c'.mem.get? s' = some w → L w.loc)
    {r : Thread I × Memory} (h : ThreadSF A tid c.mem.last L (t, c.mem) r) (hr : r.1.prom = []) :
    ∃ t₁, c'.threads[tid]? = some t₁ ∧ CertOk A tid t₁ c'.mem :=
  ⟨t, ht', certOk_memExt A tid hb hpb ⟨he.1, he.2.1⟩ hL h hr⟩

end CertExt

end Sim

end Kraken.Promising

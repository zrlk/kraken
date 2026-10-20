/-
Condition (3) of Theorem 1′ (obligations O6a/O6c and the argument): **bounded
reach** and the a-posteriori argument that every
outstanding non-pending promise on a live path is valid.

## Why `NPSafe` alone does not give (3)

`Theorem1II` takes `NPSafe` as a hypothesis, so the witnesses `(r', g')` of
each step are constrained only by erasure, `ghostLe`, `acqLe` and `owns`.
Erasure allows a step to move a slot out of `u` into the thread's resource
without reading its message: e.g. a claim `((y, q), tw)` for any settled `tw`
above `q` with no message in between satisfies `claimsAt`, or a relaxed read
can take a slot without raising `vwNew`. And `Ghost.Le` leaves `u`, `relMsgs`
and `claims` free, so slots can appear on *old* messages (growing `upd` even
forces them through `slotsDom`). `acqLe` speaks of unbounded `mayWrite`,
which other threads' fresh release writes legitimately enlarge (an unlock
adds an update slot every thread may acquire). So `owns` at the fulfilling
step cannot be pulled back to an earlier configuration through
environment steps. Concretely, along a live path the ghost states that
`NPSafe` hands back may let thread `k` take, at a step that reads nothing
(or reads it relaxed, with no fence or dependency after), the slot of a
message `q` written after `k` promised `ts < q`, and then fulfil `ts` with
that permission; `k`'s write floor stays below `ts` throughout, and the
promise is invalid at its promise along those ghosts. This is an obstruction
to the proof route, not a counterexample to `Theorem1II` (another choice of
ghosts may exist); a well-behaved rule never does it: the assertion logic's
`▽` and acquire rules only hand over what an acquire-type event ordered
before every later write (`Views.wfloor`; control dependencies count, via
`vCAP`). The conjuncts below make that discipline part of `NPSafe`.

## Bounded reach (the proposed `NPSafe` conjunct, O6a + O6c)

`reachB r g x b`: `r` owns a write permission for `x`, or may acquire one
through a chain of slots **all of whose messages are at or below `b`**
(`CanAcqB`). The proposed conjuncts of `NPSafe`'s step (whose shape the induction step of
`theorem1II_pure` fixes):

- `ReachFrame g₁ g' c₁.mem.last` (K2, O6a "no retroactive release mode"): no
  resource's bounded reach through messages already in memory grows. Fresh
  release writes attach slots above `c₁.mem.last`; claims and acquisitions
  only remove slots; a non-pending promise fulfilled by a release store stays
  relaxed (it is pure, `Erase.pure`, having been promised pure).
- `ReachOwn r g₁ r' g' c₁.mem.last tid c'` (K1, O6c "acquisition trace"): the
  stepping thread's own bounded reach grows only from messages above its new
  write floor (`Views.wfloor`). An acquire-type event from `q` puts the floor at
  `q` or above (`AcqStep.le_finish`, `AcqFloor.lean`), so a rule that moves the
  slots of `q` into the thread at an acquire-type event satisfies it
  (`ReachOwn.of_cover`), and a relaxed read must leave them in `u` until the
  fence-acquire (SLR's `▽`).

## The argument (`cond3_of_run`)

Fix a configuration `c_j` on a path to a final configuration, a thread `k`
and an outstanding non-pending promise `ts` of `k` to `x`. It is fulfilled at
a later step `f` of `k`, which owns `x` before it (`NPSafe`'s `owns`).
With `b := ts - 1` (below every memory size from `j` on) bounded reach is
pulled back from `f` to `j`: across other threads' steps by K2, across `k`'s
steps by K1, since `k`'s floor stays below `ts` while `ts` is outstanding
(`Config.Live.wfloor_lt`). Bounded reach gives `mayWrite`. This holds at
**every** configuration of the path, for every thread and promise; with
`Erase.validate_all` it turns validity-free erasure into full erasure.
-/
import Kraken.Promising.SLR.Theorem1
import Kraken.Promising.AcqFloor

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Bounded `canAcq` and bounded reach

`CanAcqB` and `reachB` (bounded reach, `ResModel.reach` of the instance) are
defined in `SLR/Erasure.lean`; here are the facts condition (3) needs. -/

theorem CanAcqB.key_le {u : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat} {b : Time} {k : Key}
    {ι : PredId} (h : CanAcqB u U A b k ι) : k.2 ≤ b := by
  cases h with
  | base _ hb _ => exact hb
  | upd _ hb _ => exact hb
  | step _ _ _ hb _ => exact hb

/-- What a thread owns is in its bounded reach, for every bound
(the proposed law `owns_reach`). -/
theorem reachB_of_owns {r : Res} {x : Loc} (g : Ghost) (b : Time) (h : 0 < (r.wr x).q) : reachB r g x b := .inl h

/-- Bounded reach is reach (the proposed law `reach_mayWrite`). -/
theorem reachB.mayWrite {r : Res} {g : Ghost} {x : Loc} {b : Time} (h : reachB r g x b) : mayWrite r g x :=
  reachB_mayWrite h

theorem CanAcqB.mono_bound {u : List Slot} {U : Loc → List PredId} {A : Loc → PredId → Nat} {b b' : Time}
    {k : Key} {ι : PredId} (hb : b ≤ b') (h : CanAcqB u U A b k ι) : CanAcqB u U A b' k ι := by
  induction h with
  | base hs hk ha => exact .base hs (Nat.le_trans hk hb) ha
  | upd hs hk hU => exact .upd hs (Nat.le_trans hk hb) hU
  | step _ hs hs' hk ha ih => exact .step ih hs hs' (Nat.le_trans hk hb) ha

theorem reachB.mono_bound {r : Res} {g : Ghost} {x : Loc} {b b' : Time} (hb : b ≤ b') (h : reachB r g x b) :
    reachB r g x b' := by
  rcases h with h | ⟨s, hs, hk, hc, hq⟩
  · exact .inl h
  · exact .inr ⟨s, hs, Nat.le_trans hk hb, hc.mono_bound hb, hq⟩

/-- **Covering** (the acquisition lemma): if every acquire id of `r'` is held
by `r` or by a slot `r` may acquire at `g` through messages up to `b`, every
slot of `g'` at or below `b` is a slot of `g`, and update ids only shrink, then
a bounded chain at `g'` from `r'` is one at `g` from `r`. -/
theorem CanAcqB.cover {g g' : Ghost} {r r' : Res} {b : Time}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ b → s ∈ g.u) (hU : ∀ x ι, ι ∈ g'.upd x → ι ∈ g.upd x)
    (hA : ∀ x ι, 1 ≤ r'.acq x ι → 1 ≤ r.acq x ι ∨
      ∃ s ∈ g.u, CanAcqB g.u g.upd r.acq b s.key s.id ∧ 1 ≤ s.res.acq x ι)
    {k : Key} {ι : PredId} (h : CanAcqB g'.u g'.upd r'.acq b k ι) : CanAcqB g.u g.upd r.acq b k ι := by
  induction h with
  | @base s hs hk ha =>
    rcases hA _ _ ha with ha | ⟨s₀, hs₀, hc₀, ha₀⟩
    · exact .base (hu s hs hk) hk ha
    · exact .step hc₀ hs₀ (hu s hs hk) hk ha₀
  | upd hs hk hU' => exact .upd (hu _ hs hk) hk (hU _ _ hU')
  | @step s s' h₁ hs hs' hk ha ih => exact .step ih (hu s hs h₁.key_le) (hu s' hs' hk) hk ha

/-- Bounded reach under covering: also the write permissions of `r'` must be
in `r`'s bounded reach at `g`. -/
theorem reachB.cover {g g' : Ghost} {r r' : Res} {b : Time}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ b → s ∈ g.u) (hU : ∀ x ι, ι ∈ g'.upd x → ι ∈ g.upd x)
    (hA : ∀ x ι, 1 ≤ r'.acq x ι → 1 ≤ r.acq x ι ∨
      ∃ s ∈ g.u, CanAcqB g.u g.upd r.acq b s.key s.id ∧ 1 ≤ s.res.acq x ι)
    (hW : ∀ x, 0 < (r'.wr x).q → reachB r g x b) {x : Loc} (h : reachB r' g' x b) : reachB r g x b := by
  rcases h with h | ⟨s, hs, hk, hc, hq⟩
  · exact hW x h
  · exact .inr ⟨s, hu s hs hk, hk, hc.cover hu hU hA, hq⟩

/-- The frame case of covering: the resource is unchanged. -/
theorem reachB.frame {g g' : Ghost} {r : Res} {b : Time}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ b → s ∈ g.u) (hU : ∀ x ι, ι ∈ g'.upd x → ι ∈ g.upd x)
    {x : Loc} (h : reachB r g' x b) : reachB r g x b :=
  h.cover hu hU (fun _ _ h => .inl h) (fun _ h => .inl h)

/-- **Acquiring a slot**: a thread that takes the slot `s`, which it may
acquire through messages up to `b` (in particular: it holds `s.id` for
`s.key.1`, or `s.id` is an update id), into its resource, while no slot at or
below `b` appears, keeps its bounded reach. -/
theorem reachB.acquire {g g' : Ghost} {r : Res} {s : Slot} {b : Time} (hs : s ∈ g.u)
    (hc : CanAcqB g.u g.upd r.acq b s.key s.id)
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ b → s ∈ g.u) (hU : ∀ x ι, ι ∈ g'.upd x → ι ∈ g.upd x)
    {x : Loc} (h : reachB (r.op s.res) g' x b) : reachB r g x b := by
  refine h.cover hu hU (fun y ι ha => ?_) (fun y hy => ?_)
  · simp only [Res.op] at ha
    by_cases h1 : 1 ≤ r.acq y ι
    · exact .inl h1
    · exact .inr ⟨s, hs, hc, by omega⟩
  · rcases Res.pos_op.mp hy with h1 | h1
    · exact .inl h1
    · exact .inr ⟨s, hs, hc.key_le, hc, h1⟩

/-! ## The proposed `NPSafe` conjuncts -/

/-- **K2, the frame conjunct** (O6a, "no retroactive release mode"): from
`g₁` to `g'` no resource's reach through messages at or below any `b ≤ bound`
grows. For a step from `c₁`, `bound = c₁.mem.last`: slots may appear only on
messages the step appends. -/
def ReachFrame (g₁ g' : Ghost) (bound : Time) : Prop :=
  ∀ b, b ≤ bound → ∀ (ρ : Res) (x : Loc), reachB ρ g' x b → reachB ρ g₁ x b

/-- **K1, the own-acquisition conjunct** (O6c, "the acquisition trace"): the
stepping thread `tid` (resource `r` at `g₁` before, `r'` at `g'` after, state
in `c'` after) gains bounded reach through messages up to `b ≤ bound` only if
its write floor after the step is above `b`, i.e. only by acquire-type events
(`AcqStep.le_finish`). -/
def ReachOwn (r : Res) (g₁ : Ghost) (r' : Res) (g' : Ghost) (bound : Time) (tid : Nat) (c' : Config I) : Prop :=
  ∀ b, b ≤ bound → (∀ t', c'.threads[tid]? = some t' → t'.views.wfloor ≤ b) →
    ∀ x, reachB r' g' x b → reachB r g₁ x b

/-- K2 from the slot discipline: no slot at or below `bound` appears, and no
update id is added. -/
theorem ReachFrame.of_slots {g₁ g' : Ghost} {bound : Time}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ bound → s ∈ g₁.u) (hU : ∀ x ι, ι ∈ g'.upd x → ι ∈ g₁.upd x) :
    ReachFrame g₁ g' bound :=
  fun _ hb _ _ h => h.frame (fun s hs hk => hu s hs (Nat.le_trans hk hb)) hU

theorem ReachFrame.refl (g : Ghost) (bound : Time) : ReachFrame g g bound := fun _ _ _ _ h => h

theorem ReachFrame.trans {g₁ g₂ g₃ : Ghost} {bound : Time} (h₁ : ReachFrame g₁ g₂ bound)
    (h₂ : ReachFrame g₂ g₃ bound) : ReachFrame g₁ g₃ bound :=
  fun b hb ρ x h => h₁ b hb ρ x (h₂ b hb ρ x h)

theorem ReachFrame.mono {g₁ g' : Ghost} {bound bound' : Time} (hb : bound' ≤ bound) (h : ReachFrame g₁ g' bound) :
    ReachFrame g₁ g' bound' :=
  fun b hb' => h b (Nat.le_trans hb' hb)

/-- K1 for a thread that changes neither its resource nor the reach of
anyone (a register step, a load that acquires nothing, a step after which
the thread holds less). -/
theorem ReachOwn.of_frame {r : Res} {g₁ g' : Ghost} {bound : Time} {tid : Nat} {c' : Config I}
    (h : ReachFrame g₁ g' bound) : ReachOwn r g₁ r g' bound tid c' :=
  fun b hb _ x hr => h b hb r x hr

/-- K1 for a step whose new resource is covered by the old one plus slots
the thread may acquire through messages at or below its new write floor (for
any `b` at least the floor). The acquire-read rule's case: the slots of the
message `q` it acquired from, with `q ≤ wfloor` by `AcqStep.le_finish`. -/
theorem ReachOwn.of_cover {r r' : Res} {g₁ g' : Ghost} {bound : Time} {tid : Nat} {c' : Config I}
    (hu : ∀ s ∈ g'.u, s.key.2 ≤ bound → s ∈ g₁.u) (hU : ∀ x ι, ι ∈ g'.upd x → ι ∈ g₁.upd x)
    (hcov : ∀ b, b ≤ bound → (∀ t', c'.threads[tid]? = some t' → t'.views.wfloor ≤ b) →
      (∀ x ι, 1 ≤ r'.acq x ι → 1 ≤ r.acq x ι ∨
        ∃ s ∈ g₁.u, CanAcqB g₁.u g₁.upd r.acq b s.key s.id ∧ 1 ≤ s.res.acq x ι) ∧
      ∀ x, 0 < (r'.wr x).q → reachB r g₁ x b) :
    ReachOwn r g₁ r' g' bound tid c' := by
  intro b hb hf x h
  obtain ⟨hA, hW⟩ := hcov b hb hf
  exact h.cover (fun s hs hk => hu s hs (Nat.le_trans hk hb)) hU hA hW

/-! ## The argument -/

/-- Backward chaining of a property along a run. -/
theorem chain_back {R G : Type} (P : R → G → Prop) (r : Nat → R) (g : Nat → G) {j f : Nat} (hjf : j ≤ f)
    (hstep : ∀ i, j ≤ i → i < f → P (r (i + 1)) (g (i + 1)) → P (r i) (g i)) (hf : P (r f) (g f)) :
    P (r j) (g j) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjf
  induction d with
  | zero => exact hf
  | succ d ih =>
    exact ih (Nat.le_add_right _ _) (fun i hi hif => hstep i hi (by omega))
      (hstep (j + d) (Nat.le_add_right _ _) (by omega) hf)

/-- **Condition (3) along an annotated run** (steps
1–5), from thread `k`'s point of view. The run is `i ↦ (c i, rF i, g i)` for
`j ≤ i ≤ f`; `ts` (a message to `x`, an outstanding promise of `k` at `c j`)
is still outstanding at every `c i` with `i ≤ f` and is fulfilled by `k`'s
step at `f`, which owns `x` before it (`NPSafe`'s `owns`). Each transition
pulls bounded reach back, given that `k`'s write floor after it is at most
`b` (`hstep`): for a step of another thread, or a promise, prepayment or
ghost-only move, this is K2 (`ReachFrame`, with `rF (i+1) k = rF i k`); for a
step of `k`, K1 (`ReachOwn`). The floor hypothesis is discharged by liveness
(`Config.Live.wfloor_lt`: `k`'s floor stays below the outstanding `ts`). Then
`k` may write `x` at `c j`. -/
theorem cond3_of_run {c : Nat → Config I} {rF : Nat → Nat → Res} {g : Nat → Ghost} {k : Nat} {ts : Time}
    {x : Loc} {j f : Nat} (hjf : j ≤ f)
    (hmem : ∀ i, j ≤ i → i ≤ f → ts ≤ (c i).mem.last)
    (hstep : ∀ i, j ≤ i → i < f → ∀ b, b ≤ (c i).mem.last →
      (∀ t', (c (i + 1)).threads[k]? = some t' → t'.views.wfloor ≤ b) →
      reachB (rF (i + 1) k) (g (i + 1)) x b → reachB (rF i k) (g i) x b)
    (hfloor : ∀ i, j < i → i ≤ f → ∀ t', (c i).threads[k]? = some t' → t'.views.wfloor < ts)
    (hown : 0 < ((rF f k).wr x).q) :
    mayWrite (rF j k) (g j) x := by
  have hb : reachB (rF j k) (g j) x (ts - 1) :=
    chain_back (fun r g => reachB r g x (ts - 1)) (fun i => rF i k) g hjf
      (fun i hi hif h => hstep i hi hif (ts - 1) (by have := hmem i hi (Nat.le_of_lt hif); omega_t)
        (fun t' ht' => by have := hfloor (i + 1) (by omega) hif t' ht'; omega_t) h)
      (reachB_of_owns _ _ hown)
  exact hb.mayWrite

/-- The transition lemma for another thread's step (or a promise, a
prepayment, a ghost-only move): `k`'s resource is unchanged and the step
satisfies K2 for the memory before it. -/
theorem pull_frame {c₁ : Config I} {r r' : Res} {g₁ g' : Ghost} {x : Loc} {b : Time} (hr : r' = r)
    (hK2 : ReachFrame g₁ g' c₁.mem.last) (hb : b ≤ c₁.mem.last) (h : reachB r' g' x b) : reachB r g₁ x b :=
  hr ▸ hK2 b hb r' x h

/-- The transition lemma for a step of `k` itself: K1. -/
theorem pull_own {c₁ c' : Config I} {k : Nat} {r r' : Res} {g₁ g' : Ghost} {x : Loc} {b : Time}
    (hK1 : ReachOwn r g₁ r' g' c₁.mem.last k c') (hb : b ≤ c₁.mem.last)
    (hf : ∀ t', c'.threads[k]? = some t' → t'.views.wfloor ≤ b) (h : reachB r' g' x b) : reachB r g₁ x b :=
  hK1 b hb hf x h

/-- **Condition (3) at a configuration, all threads at once**: if every
outstanding non-pending promise of every thread is in the situation of
`cond3_of_run` (the a-posteriori annotation of a live path supplies this at
*every* configuration of the path), validity-free erasure is full erasure
(`Erase.validate_all`). -/
theorem Erase.of_cond3 {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I} (E : Erase rF g T c)
    (h3 : ∀ i t, c.threads[i]? = some t → ∀ ts ∈ t.prom, ts ∉ g.pend → ∀ w, c.mem.get? ts = some w →
      ∃ b, reachB (rF i) g w.loc b) :
    Erase rF g (fun _ => False) c :=
  E.validate_all fun i t ht ts hts hp w hw => (h3 i t ht ts hts hp w hw).elim fun _ h => h.mayWrite

/-! ## Generic form

The same argument over any resource model with a bounded reach `Rch`
satisfying `owns r x → Rch r g x b` and `Rch r g x b → mayWrite r g x` (the
proposed `ResModel` member `reach` and `Laws` fields `owns_reach`,
`reach_mayWrite`). -/

theorem cond3_of_run_generic {R G : Type} (owns : R → Loc → Prop) (mayWrite : R → G → Loc → Prop)
    (Rch : R → G → Loc → Time → Prop) (owns_reach : ∀ r g x b, owns r x → Rch r g x b)
    (reach_mayWrite : ∀ r g x b, Rch r g x b → mayWrite r g x)
    {c : Nat → Config I} {rF : Nat → Nat → R} {g : Nat → G} {k : Nat} {ts : Time}
    {x : Loc} {j f : Nat} (hjf : j ≤ f)
    (hmem : ∀ i, j ≤ i → i ≤ f → ts ≤ (c i).mem.last)
    (hstep : ∀ i, j ≤ i → i < f → ∀ b, b ≤ (c i).mem.last →
      (∀ t', (c (i + 1)).threads[k]? = some t' → t'.views.wfloor ≤ b) →
      Rch (rF (i + 1) k) (g (i + 1)) x b → Rch (rF i k) (g i) x b)
    (hfloor : ∀ i, j < i → i ≤ f → ∀ t', (c i).threads[k]? = some t' → t'.views.wfloor < ts)
    (hown : owns (rF f k) x) :
    mayWrite (rF j k) (g j) x := by
  have hb : Rch (rF j k) (g j) x (ts - 1) :=
    chain_back (fun r g => Rch r g x (ts - 1)) (fun i => rF i k) g hjf
      (fun i hi hif h => hstep i hi hif (ts - 1) (by have := hmem i hi (Nat.le_of_lt hif); omega_t)
        (fun t' ht' => by have := hfloor (i + 1) (by omega) hif t' ht'; omega_t) h)
      (owns_reach _ _ _ _ hown)
  exact reach_mayWrite _ _ _ _ hb

end Kraken.Promising.SLR

/-
`NPSafe` from a per-thread invariant:
the analogue, for the SLR-adapted resource model, of the invariant environment's `ThreadSpec` for
the invariant environment. A program proof is a predicate `Inv` on (the
configuration as thread `tid` sees it, its resource, the ghost state) that
the environment cannot break, that gives the postcondition when the thread
is done, and that every instruction step re-establishes together with
erasure. Then `NPSafe` holds for every step index (`NPSafe.of_inv`).

## Contents

- `ThreadInv`: the invariant and its three obligations at the level of
  `NPStepBy` (`env`, `done`, `step`); `NPSafe.of_inv`: `Inv → NPSafe n m`
  for all `n m`.
- `Erase.npStep_fin`: `Erase.npStep` (SLR's Lemma 21 frame for one
  instruction) that also returns the instruction's final thread state, so a
  postcondition can be stated about the configuration after the step.
- `WrittenCx`, `WpPost`, `ThreadRule`, `ThreadRule.toThreadInv`,
  `NPSafe.of_rule`: the `step` obligation from the instruction's erasure WP
  (`EvTree.EraseWP`, `SLR/Lift.lean`) with postcondition `WpPost`: ghost
  growth, pending marks kept, `acqLe`, ownership of every written message
  (context level), and `Inv` of the configuration after the step. This is
  the form an instruction rule (`eraseWP_load`/`_store`/`_rmw`,
  `npStep_silent`) feeds.

## Shape

Written against `NPSafe`'s shape (option (B)): validity-free erasure
`T = ⊤` before and after, `c₁.MachInv`, own pending promises pending in the
instance's ghost state, no new pending marks, bounded reach `K1`/`K2`
(`reachB`), and the prepay conjunct for promised releases
(`ThreadInv.prepay`, passed through unchanged by `ThreadRule`).

The clean flag: `Inv` takes `NPSafe`'s flag `cl` as its first
argument. `done` may use it; `step`/`prepay` re-establish `Inv` at the
continuation flag `cl ∧ Erase (setRes rF tid r) g (fun _ => False) c` (full
erasure at the pre-state), so an instruction rule can case-split on full
erasure: with it, validity facts are available (e.g. foreign promises are
valid); without it, the continuation is unclean but must still carry every
resource conjunct. A flag-uniform `Inv` (one that ignores `cl`) is a proof
for every flag.
-/
import Kraken.Promising.SLR.Theorem1

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## The rule at the level of instruction steps -/

/-- The configuration after thread `tid` (state `t`) promises `w`, as
`NPSafe`'s prepay conjunct writes it (`SLR.Promised` with the thread state
spelled out). -/
abbrev PromisedBy (c : Config I) (tid : Nat) (t : Thread I) (w : Msg) : Config I :=
  c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] } (c.mem.append { w with tid }).1

/-- **A per-thread invariant for `NPSafe`** (thread `tid`, postcondition `B`):
`Inv c r g` is what thread `tid` knows in configuration `c` with resource `r`
and ghost state `g`.

- `env`: the environment (other threads' steps, `tid`'s own promises: an
  `EnvExt`) and world growth (`Ghost.Le`) keep it;
- `done`: a done thread meets `B`;
- `step`: every instruction step of `tid` from a configuration satisfying it,
  with validity-free erasure, re-establishes erasure for some `(r', g')`,
  with the conditions of `NPSafe`'s step (ghost growth, pending marks kept
  while outstanding, no new marks, `acqLe`, ownership of every written
  message, bounded reach `K1`/`K2`), and `Inv` after it;
- `prepay` (option (B)): a promise by `tid` of a release that its
  next instruction (after a promise-free advance) fulfils is prepaid: erasure
  of the configuration with the promise, marked pending, for some
  `(r', g')`, with `Inv` there.

`g₀` in `step`/`prepay` is the ghost state of the `NPSafe` instance the
obligation is discharged for (before the environment's growth to `g`): the
thread's own pending promises are pending in `g₀` already. -/
structure ThreadInv (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  env : ∀ {cl : Prop} {c c₁ : Config I} {r : Res} {g g₁ : Ghost}, Inv cl c r g → EnvExt tid c c₁ → g.Le g₁ →
    Inv cl c₁ r g₁
  done : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost}, Inv cl c r g → cl → c.Done tid → B c r g
  step : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (c' : Config I),
    Inv cl c r g →
    g₀.Le g → Erase (setRes rF tid r) g (fun _ => True) c → NPStepBy A tid c c' → c.MachInv → c.WfProm tid →
    c'.WfProm tid → (∀ t, c.threads[tid]? = some t → ∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) c' ∧ g.Le g' ∧
      (∀ ts, ts ∈ g.pend → (∃ (i : Nat) (t' : Thread I), c'.threads[i]? = some t' ∧ ts ∈ t'.prom) →
        ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c' r' g' ∧ (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ w, Written tid c c' w → 0 < (r.wr w.loc).q) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t', c'.threads[tid]? = some t' → max t'.views.vwNew t'.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)
  prepay : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c r g → g₀.Le g → c.threads[tid]? = some t₁ → Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv →
    (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfils A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧ (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- **`NPSafe` from a per-thread invariant**: a configuration, resource and
ghost state satisfying `Inv` are non-promisingly safe for every step index.
SLR's `npsafe` coinduction, here an induction on `(n, m)`: `Inv` is closed
under the environment (`env`), so it holds at every `EnvExt` extension `c₁`
and ghost `g₁ ≥ g`, where `done`, `step` and `prepay` give the three
conjuncts. -/
theorem NPSafe.of_inv {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat} (J : ThreadInv A B tid) :
    ∀ (n m : Nat) (cl : Prop) (c : Config I) (r : (model I).R) (g : (model I).Ghost), J.Inv cl c r g →
      NPSafe (model I) A B tid n m cl c r g
  | 0, _, _, _, _, _, _ => by simp [NPSafe]
  | n + 1, 0, cl, c, r, g, h => by
    rw [NPSafe]
    exact fun m => NPSafe.of_inv J n m cl c r g h
  | n + 1, m + 1, cl, c, r, g, h => by
    rw [NPSafe]
    intro c₁ g₁ he hg
    have h₁ : J.Inv cl c₁ r g₁ := J.env h he hg
    refine ⟨J.done h₁, fun rF c' E hs hinv hwf hwf' hnp => ?_, fun rF t₁ w ht₁ E hinv hnp hrel => ?_⟩
    · obtain ⟨r', g', E', hg', hkeep, hnew, h', hacq, hown, hk1, hk2⟩ :=
        J.step g rF c' h₁ hg E hs hinv hwf hwf' hnp
      exact ⟨r', g', E', hg', hkeep, hnew, NPSafe.of_inv J (n + 1) m _ c' r' g' h', hacq, hown, hk1, hk2⟩
    · obtain ⟨r', g', E', hg', hpend, hkeep, hnew, h', hacq, hk1, hk2⟩ :=
        J.prepay g rF t₁ w h₁ hg ht₁ E hinv hnp hrel.toRelFulfils
      exact ⟨r', g', E', hg', hpend, hkeep, hnew, NPSafe.of_inv J (n + 1) m _ _ r' g' h', hacq, hk1, hk2⟩
termination_by n m => (n, m)

/-- `NPSafe.of_inv` at every thread of a configuration, in the form of
`NPSafeImpliesAdequateV`'s hypothesis (for the threads `tid < k`; `k` is
`states.length` there). -/
theorem NPSafe.of_inv_all {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} (J : ∀ tid, ThreadInv A B tid)
    {cl : Prop} {c : Config I} {rF : Nat → (model I).R} {g : (model I).Ghost} {k : Nat}
    (h : ∀ tid, tid < k → (J tid).Inv cl c (rF tid) g) :
    ∀ tid, tid < k → ∀ n m, NPSafe (model I) A B tid n m cl c (rF tid) g :=
  fun tid htid n m => NPSafe.of_inv (J tid) n m cl c (rF tid) g (h tid htid)

/-! ## The per-instruction lemma, with the final thread state -/

/-- **`Erase.npStep` with the final thread state**: the same frame (SLR's
Lemma 21 for one instruction), also returning the thread `t'` the step
produced (a `finishInstr` outcome of the run's final ISA state and context),
so that a postcondition can speak about the configuration after the step,
`c' = c.withThread tid t' cx'.mem`. -/
theorem Erase.npStep_fin {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c c' : Config I}
    {tid : Nat} {r : Res} {Post : Thread I → I.State → Res → Ghost → Ctx → Prop}
    (hinv : c.MachInv) (E : Erase (setRes rF tid r) g T c) (hs : NPStepBy A tid c c')
    (hwp : ∀ t tree, c.threads[tid]? = some t → I.exec t.st = some tree →
      tree.EraseWP A tid (instrViews t (I.deps t.st)) rF T c t (Post t) r g (ctx₀ t tid c.mem)) :
    ∃ t t' st r' g' cx', c.threads[tid]? = some t ∧ t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx' ∧
      c' = c.withThread tid t' cx'.mem ∧ Post t st r' g' cx' ∧ Erase (setRes rF tid r') g' T c' := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hstep, ho, he⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hn := lt_size_of_get? ht
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨res, hr, ho⟩ := ho
    cases res with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, cx'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have E0 : ErAt rF T c t tid r g (ctx₀ t tid c.mem) := by
        unfold ErAt
        rw [Config.withThread_self c ht]
        exact E
      obtain ⟨r', g', E', hpost⟩ := runTree_eraseWP A tid _ rF T c t (Post t) tree r g _ st cx' hr E0
        (hinv.ctxInv ht _) (hwp t tree ht hex)
      exact ⟨t, th, st, r', g', cx', ht, hth, rfl, hpost, Erase.withThread_prom E' hn (finishInstr_relKey hth).1⟩

/-! ## The rule at the level of event trees -/

/-- `Written` at context level: the message `w` at `ts` is in the final
memory of the instruction (context `cx'`), not an outstanding promise of the
thread afterwards, and either appended by the instruction or an outstanding
promise of the thread before it (state `t` in `c`). -/
def WrittenCx (c : Config I) (t : Thread I) (cx' : Ctx) (w : Msg) : Prop :=
  ∃ ts, cx'.mem.get? ts = some w ∧ ts ∉ cx'.prom ∧ (c.mem.last < ts ∨ ts ∈ t.prom)

/-- The postcondition an instruction rule establishes over its erasure WP
(thread `tid` in state `t` of `c`, resource `r`, ghost `g` before the
instruction; `(st, r', g', cx')` after it): the conditions of `NPSafe`'s step
(world growth, every pending mark kept while outstanding, no new mark,
`acqLe`, a write permission for every written message, `K1`) and, for every
`finishInstr` outcome whose promises are not dead (`NPSafe`'s `c'.WfProm`),
`K2` at its views and `Inv` (at flag `cl`) of the configuration after the
step. -/
def WpPost (Inv : Prop → Config I → Res → Ghost → Prop) (cl : Prop) (c : Config I) (tid : Nat) (r : Res) (g : Ghost) (t : Thread I) :
    I.State → Res → Ghost → Ctx → Prop :=
  fun st r' g' cx' => g.Le g' ∧
    (∀ ts, ts ∈ g.pend → (ts ∈ cx'.prom ∨ ∃ (i : Nat) (t' : Thread I), i ≠ tid ∧ c.threads[i]? = some t' ∧ ts ∈ t'.prom) →
      ts ∈ g'.pend) ∧
    (∀ ts, ts ∈ g'.pend → ts ∈ g.pend) ∧ (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
    (∀ w, WrittenCx c t cx' w → 0 < (r.wr w.loc).q) ∧
    (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
    ∀ t' ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st cx', t'.hasDeadPromise cx'.mem = false →
      (∀ b, b ≤ c.mem.last → max t'.views.vwNew t'.views.vCAP ≤ b → ∀ x, reachB r' g' x b → reachB r g x b) ∧
      Inv cl (c.withThread tid t' cx'.mem) r' g'

/-- **A per-thread invariant with per-instruction erasure WPs**: as
`ThreadInv`, with `step` replaced by `wp`, the erasure WP of the thread's
next instruction (`EvTree.EraseWP`, at validity-free erasure) with
postcondition `WpPost Inv` at the continuation flag. The hypotheses are
those of `NPSafe`'s step (erasure, machine invariants, live promises, own
pending promises pending in `g₀`). `prepay` is `ThreadInv.prepay`. -/
structure ThreadRule (A : Arch) (B : Config I → (model I).R → (model I).Ghost → Prop) (tid : Nat) where
  Inv : Prop → Config I → Res → Ghost → Prop
  env : ∀ {cl : Prop} {c c₁ : Config I} {r : Res} {g g₁ : Ghost}, Inv cl c r g → EnvExt tid c c₁ → g.Le g₁ →
    Inv cl c₁ r g₁
  done : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost}, Inv cl c r g → cl → c.Done tid → B c r g
  wp : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t : Thread I)
    (tree : EvTree I.State), Inv cl c r g → g₀.Le g → c.threads[tid]? = some t → I.exec t.st = some tree →
    Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv → c.WfProm tid →
    (∀ ts ∈ t.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    tree.EraseWP A tid (instrViews t (I.deps t.st)) rF (fun _ => True) c t
      (WpPost Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) r g (ctx₀ t tid c.mem)
  prepay : ∀ {cl : Prop} {c : Config I} {r : Res} {g : Ghost} (g₀ : Ghost) (rF : Nat → Res) (t₁ : Thread I)
    (w : Msg), Inv cl c r g → g₀.Le g → c.threads[tid]? = some t₁ → Erase (setRes rF tid r) g (fun _ => True) c → c.MachInv →
    (∀ ts ∈ t₁.prom, ts ∈ g.pend → ts ∈ g₀.pend) →
    { t₁ with prom := t₁.prom ++ [(c.mem.append { w with tid }).2] }.RelFulfils A tid
      (c.mem.append { w with tid }).2 (c.mem.append { w with tid }).1 →
    ∃ r' g', Erase (setRes rF tid r') g' (fun _ => True) (PromisedBy c tid t₁ w) ∧ g.Le g' ∧
      (c.mem.append { w with tid }).2 ∈ g'.pend ∧ (∀ ts, ts ∈ g.pend → ts ∈ g'.pend) ∧
      (∀ ts, ts ∈ g'.pend → ts ∈ g.pend ∨ ts = (c.mem.append { w with tid }).2) ∧
      Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) (PromisedBy c tid t₁ w) r' g' ∧ (∀ x, mayWrite r' g' x → mayWrite r g x) ∧
      (∀ b, b ≤ c.mem.last → ∀ ρ x, reachB ρ g' x b → reachB ρ g x b) ∧
      (∀ b, b ≤ c.mem.last → (∀ t, c.threads[tid]? = some t → max t.views.vwNew t.views.vCAP ≤ b) →
        ∀ x, reachB r' g' x b → reachB r g x b)

/-- `Written` across an instruction step is `WrittenCx` of the run. -/
theorem written_cx {c : Config I} {tid : Nat} {t t' : Thread I} {cx' : Ctx} (ht : c.threads[tid]? = some t)
    (hp : t'.prom = cx'.prom) {w : Msg} (hw : Written tid c (c.withThread tid t' cx'.mem) w) : WrittenCx c t cx' w := by
  obtain ⟨ts, hget, hnot, hnew⟩ := hw
  have hn := lt_size_of_get? ht
  have ht' : (c.withThread tid t' cx'.mem).threads[tid]? = some t' := by
    rw [Config.withThread_get? c t' cx'.mem hn, ite_eq_left rfl]
  refine ⟨ts, hget, fun h => hnot t' ht' (hp ▸ h), ?_⟩
  rcases hnew with h | h
  · exact .inl h
  · exact .inr (h t ht)

/-- **The erasure-WP rule gives the step-level rule.** `Erase.npStep_fin`
runs the WP; `WpPost` is exactly what `ThreadInv.step` asks, with
`c'.WfProm tid` supplying the live-promise hypothesis of `Inv`. -/
def ThreadRule.toThreadInv {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat} (R : ThreadRule A B tid) :
    ThreadInv A B tid where
  Inv := R.Inv
  env := R.env
  done := R.done
  step := by
    intro cl c r g g₀ rF c' h hle E hs hinv hwf hwf' hnp
    obtain ⟨t, t', st, r', g', cx', ht, hth, rfl, hpost, E'⟩ := Erase.npStep_fin
      (Post := fun t => WpPost R.Inv (cl ∧ Erase (setRes rF tid r) g (fun _ => False) c) c tid r g t) hinv E hs
      (fun t tree ht hex => R.wp g₀ rF t tree h hle ht hex E hinv hwf (hnp t ht))
    obtain ⟨hg, hkeep, hnew, hacq, hown, hk1, hfin⟩ := hpost
    have hn := lt_size_of_get? ht
    have ht' : (c.withThread tid t' cx'.mem).threads[tid]? = some t' := by
      rw [Config.withThread_get? c t' cx'.mem hn, ite_eq_left rfl]
    have hdead : t'.hasDeadPromise cx'.mem = false := by
      have := hwf' t' ht'
      simpa [Config.withThread] using this
    obtain ⟨hk2, hinv'⟩ := hfin t' hth hdead
    refine ⟨r', g', E', hg, ?_, hnew, hinv', hacq, fun w hw => hown w ?_, hk1, ?_⟩
    · rintro ts hts ⟨i, ti, hi, htsi⟩
      refine hkeep ts hts ?_
      rw [Config.withThread_get? c t' cx'.mem hn] at hi
      split at hi
      · next he =>
        subst he
        cases hi
        exact .inl ((finishInstr_relKey hth).1 ▸ htsi)
      · next he => exact .inr ⟨i, ti, Ne.symm he, hi, htsi⟩
    · exact written_cx ht (finishInstr_relKey hth).1 hw
    · intro b hb hv x hx
      exact hk2 b hb (hv t' ht') x hx
  prepay := R.prepay

/-- **`NPSafe` from per-instruction erasure WPs.** -/
theorem NPSafe.of_rule {A : Arch} {B : Config I → (model I).R → (model I).Ghost → Prop} {tid : Nat} (R : ThreadRule A B tid)
    (n m : Nat) {cl : Prop} {c : Config I} {r : (model I).R} {g : (model I).Ghost} (h : R.Inv cl c r g) :
    NPSafe (model I) A B tid n m cl c r g :=
  NPSafe.of_inv R.toThreadInv n m cl c r g h

end Kraken.Promising.SLR

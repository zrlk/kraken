/-
Erasure at virtual configurations (design (V) variant (ii)).

A virtual configuration `v` of `c` (`Config.VirtualOf`) has the memory of `c`
and advances threads along memory-silent promise-free runs, which can only
fulfil outstanding promises (`ThreadNP.prom_sub_of_silent`, a machine fact
about every program). Erasure (`SLR.Erase`) looks at threads only through
their promise sets, so erasure at `v` and erasure at `c` differ only in which
messages count as written. The pending-release clause makes them agree:

- `Erase.fulfil` / `Erase.virtualOf`: erasure at `c`, in which every promise
  the advance fulfils is pending, gives erasure at `v`;
- `Erase.unfulfil` / `Erase.ofVirtualOf`: erasure at `v` gives erasure at
  `c` with the promises the advance fulfilled marked pending.

So `Config.Advanceable.virtualOf`'s `v` satisfies erasure exactly when the
real configuration does with its pending releases marked, which is how
Theorem 1′ (`NPSafeImpliesAdequateV`) is to get erasure at `v` from the
erasure it maintains along the real path.
-/
import Kraken.Promising.SLR.Erasure

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Machine fact: a memory-silent run only fulfils promises -/

private theorem ite_none_left'' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

/-- Along an instruction's event tree, memory only grows and every new
outstanding promise is a message appended on the way. -/
structure Ctx.PromNew (c c' : Ctx) : Prop where
  last : c.mem.last ≤ c'.mem.last
  prom : ∀ p ∈ c'.prom, p ∈ c.prom ∨ (c.mem.last < p ∧ p ≤ c'.mem.last)

theorem Ctx.PromNew.refl (c : Ctx) : c.PromNew c := ⟨Nat.le_refl _, fun _ hp => .inl hp⟩

theorem Ctx.PromNew.trans {c c' c'' : Ctx} (h₁ : c.PromNew c') (h₂ : c'.PromNew c'') : c.PromNew c'' := by
  refine ⟨Nat.le_trans h₁.last h₂.last, fun p hp => ?_⟩
  rcases h₂.prom p hp with h | ⟨h1, h2⟩
  · rcases h₁.prom p h with h | ⟨h1', h2'⟩
    · exact .inl h
    · exact .inr ⟨h1', Nat.le_trans h2' h₂.last⟩
  · exact .inr ⟨Nat.lt_of_le_of_lt h₁.last h1, h2⟩

theorem Ctx.PromNew.of_eq {c c' : Ctx} (hm : c'.mem = c.mem) (hp : c'.prom = c.prom) : c.PromNew c' :=
  ⟨by rw [hm]; exact Nat.le_refl _, fun p h => .inl (hp ▸ h)⟩

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_promNew {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.PromNew x.2.2 := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left'' ht
    simp only [Option.some.injEq] at h
    subst h
    exact .of_eq rfl rfl

theorem writeSuccs_promNew {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c.PromNew c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨_, -, h⟩ | h
  · split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨by simp only [afterWrite]; exact Nat.le_refl _, fun p hp => .inl ?_⟩
      simp only [afterWrite] at hp
      exact List.mem_of_mem_erase hp
    · cases h
  · split at h
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    have ht : t = c.mem.last + 1 := (congrArg Prod.snd hok).symm
    have hm : mem' = (c.mem.append { loc := l, val := v, tid }).1 := (congrArg Prod.fst hok).symm
    have hl : mem'.last = c.mem.last + 1 := hm ▸ Memory.last_append _ _
    refine ⟨?_, fun p hp => ?_⟩
    · simp only [afterWrite]; rw [hl]; omega_t
    · simp only [afterWrite] at hp
      rcases List.mem_append.mp (List.mem_of_mem_erase hp) with h | h
      · exact .inl h
      · rw [List.mem_singleton.mp h]; right; simp only [afterWrite]; rw [hl, ht]; omega_t

theorem Ctx.PromNew.fenceStep (c : Ctx) (k : FenceKind) : c.PromNew (Kraken.Promising.fenceStep c k) :=
  .of_eq (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1

theorem Ctx.PromNew.fenceOpt (c : Ctx) (b : Bool) (k : FenceKind) :
    c.PromNew (if b then Kraken.Promising.fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact .fenceStep c k

theorem Ctx.PromNew.rmwPost (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) :
    c.PromNew (Kraken.Promising.rmwPost A k noRet l c) := by
  unfold Kraken.Promising.rmwPost
  split
  · exact .of_eq rfl rfl
  · exact .of_eq rfl rfl

theorem runTree_promNew {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.PromNew c' := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .refl _
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h
  | load k xcl l ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact (readSuccs_promNew A iv hx).trans (ih x.2.1 x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_promNew A tid _ hc0).trans (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have h0 : c.PromNew { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq rfl rfl
      exact h0.trans (ih false _ s c' h.2)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (Ctx.PromNew.fenceStep c k).trans (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := Ctx.PromNew.fenceOpt c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_promNew A iv h2)
    simp only at h
    split at h
    · exact (h12.trans (Ctx.PromNew.fenceOpt c2 A.rmwFence .sy)).trans (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine ((h12.trans (writeSuccs_promNew A tid _ hc3)).trans ?_).trans (ih old _ s c' h)
      exact (Ctx.PromNew.rmwPost A c3 k noRet l).trans (Ctx.PromNew.fenceOpt _ A.rmwFence .sy)

end Rules

/-- One instruction: memory only grows, and every new outstanding promise is
a message it appended. -/
theorem stepOne_promNew (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    mem.last ≤ o.mem.last ∧ ∀ p ∈ o.thread.prom, p ∈ t.prom ∨ (mem.last < p ∧ p ≤ o.mem.last) := by
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      have hw := runTree_promNew A tid _ tree _ st c' hr
      obtain ⟨hp, -⟩ := finishInstr_relKey hth
      simp only [hp]
      exact ⟨hw.last, hw.prom⟩

/-- A promise-free run: memory only grows, and every new outstanding promise
is a message appended on the way. -/
theorem ThreadNP.promNew {A : Arch} {tid : Nat} {p q : Thread I × Memory} (h : ThreadNP A tid p q) :
    p.2.last ≤ q.2.last ∧ ∀ ts ∈ q.1.prom, ts ∈ p.1.prom ∨ (p.2.last < ts ∧ ts ≤ q.2.last) := by
  induction h with
  | refl p => exact ⟨Nat.le_refl _, fun ts h => .inl h⟩
  | step hs _ ih =>
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    obtain ⟨hl, hp⟩ := stepOne_promNew A hstep ho
    obtain ⟨hl', hp'⟩ := ih
    refine ⟨Nat.le_trans hl hl', fun ts h => ?_⟩
    rcases hp' ts h with h | ⟨h1, h2⟩
    · rcases hp ts h with h | ⟨h1', h2'⟩
      · exact .inl h
      · exact .inr ⟨h1', Nat.le_trans h2' hl'⟩
    · exact .inr ⟨Nat.lt_of_le_of_lt hl h1, h2⟩

/-- **A memory-silent promise-free run only fulfils promises**: every
promise outstanding at its end was outstanding at its start. -/
theorem ThreadNP.prom_sub_of_silent {A : Arch} {tid : Nat} {t t' : Thread I} {mem : Memory}
    (h : ThreadNP A tid (t, mem) (t', mem)) : ∀ ts ∈ t'.prom, ts ∈ t.prom := by
  intro ts hts
  rcases (ThreadNP.promNew h).2 ts hts with h | ⟨h1, h2⟩
  · exact h
  · exact absurd (Nat.lt_of_lt_of_le h1 h2) (Nat.lt_irrefl _)

end Kraken.Promising

namespace Kraken.Promising.SLR

variable {I : ISA}

/-! ## Erasure across fulfilment of pending promises -/

/-- `v` has the memory of `c` and the same threads, each with a subset of
its promises. -/
structure PromSub (c v : Config I) : Prop where
  mem : v.mem = c.mem
  size : v.threads.size = c.threads.size
  sub : ∀ (i : Nat) (t' : Thread I), v.threads[i]? = some t' →
    ∃ t : Thread I, c.threads[i]? = some t ∧ ∀ p ∈ t'.prom, p ∈ t.prom

theorem PromSub.outstanding {c v : Config I} (h : PromSub c v) {ts : Time} (ho : Outstanding v ts) :
    Outstanding c ts := by
  obtain ⟨i, t', hi, hts⟩ := ho
  obtain ⟨t, ht, hsub⟩ := h.sub i t' hi
  exact ⟨i, t, ht, hsub ts hts⟩

theorem PromSub.total {c v : Config I} (h : PromSub c v) (rF : Nat → Res) (g g' : Ghost) (hu : g'.u = g.u) :
    SLR.total rF g' v = SLR.total rF g c := by
  simp only [SLR.total, h.size, Ghost.slotsRes, hu]

/-- **Fulfilling pending promises keeps erasure.** If `v` differs from `c`
only in having fewer outstanding promises, all of them pending in `c`, then
erasure at `c` gives erasure at `v` (the pending set restricted to what is
still outstanding). -/
theorem Erase.fulfil {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c v : Config I} (E : Erase rF g T c)
    (hv : PromSub c v) (hcov : ∀ ts, Outstanding c ts → ¬ Outstanding v ts → ts ∈ g.pend)
    {pend' : List Time} (hpend : ∀ ts, ts ∈ pend' ↔ ts ∈ g.pend ∧ Outstanding v ts) :
    Erase rF { g with pend := pend' } T v := by
  have htot := hv.total rF g { g with pend := pend' } rfl
  have hset : ∀ p, Settled v { g with pend := pend' } p ↔ Settled c g p := by
    intro p
    unfold Settled
    simp only [hpend]
    constructor
    · rintro (h | ⟨h, -⟩)
      · by_cases ho : Outstanding c p
        · exact .inr (hcov p ho h)
        · exact .inl ho
      · exact .inr h
    · rintro (h | h)
      · exact .inl fun h' => h (hv.outstanding h')
      · by_cases ho : Outstanding v p
        · exact .inr ⟨h, ho⟩
        · exact .inl ho
  have hmem := hv.mem
  have hfulf : ∀ x p, Fulf v { g with pend := pend' } x p ↔ Fulf c g x p := by
    intro x p; unfold Fulf; simp only [hset, hmem]
  have htr : ∀ r x, Tracked v { g with pend := pend' } r x ↔ Tracked c g r x := by
    intro r x; unfold Tracked; simp only [hset, hmem]
  exact {
    valid := htot ▸ E.valid
    slotIds := E.slotIds
    acqIds := htot ▸ E.acqIds
    relAcq := htot ▸ E.relAcq
    writes := by
      rw [htot]
      intro x hx p
      rw [hfulf]
      exact E.writes x ((htr _ x).mp hx) p
    pure := by rw [hmem]; exact E.pure
    relExists := by rw [hmem]; exact E.relExists
    slotsNodup := E.slotsNodup
    slotsDom := htot ▸ E.slotsDom
    slotsPred := by rw [hmem]; exact E.slotsPred
    promWf := by
      intro i t' hi ts hts
      obtain ⟨t, ht, hsub⟩ := hv.sub i t' hi
      rw [hmem]
      exact E.promWf i t ht ts (hsub ts hts)
    promValid := by
      intro i t' hi hT ts hts hp w hw
      obtain ⟨t, ht, hsub⟩ := hv.sub i t' hi
      have hp' : ts ∉ g.pend := fun h => hp ((hpend ts).mpr ⟨h, ⟨i, t', hi, hts⟩⟩)
      rw [hmem] at hw
      exact E.promValid i t ht hT ts (hsub ts hts) hp' w hw
    pend := by
      intro ts hts
      obtain ⟨h, ho⟩ := (hpend ts).mp hts
      obtain ⟨hw, -⟩ := E.pend ts h
      exact ⟨hmem ▸ hw, ho⟩
    updIds := htot ▸ E.updIds
    relSettled := fun k hk => (hset k.2).mpr (E.relSettled k hk)
    claimsNodup := E.claimsNodup
    claimsAt := by
      intro k tw hk
      obtain ⟨hlt, w', hw', hl, hs, hb⟩ := E.claimsAt k tw hk
      exact ⟨hlt, w', hmem ▸ hw', hl, (hset tw).mpr hs, fun ts w'' h1 h2 hw'' => hb ts w'' h1 h2 (hmem ▸ hw'')⟩
    claimFulf := fun k tw hk ho => E.claimFulf k tw hk (hv.outstanding ho) }

/-- **Un-fulfilling, with the fulfilled promises marked pending.** If `v`
differs from `c` only in having fewer outstanding promises, erasure at `v`
gives erasure at `c` with every promise outstanding in `c` but not in `v`
pending. `hwf`: every promise of `c` is a message of its thread (an invariant
of reachable configurations). `hcl`: no claimer is outstanding in `c`
(`Erase.claimFulf`; the un-fulfilled promises claim nothing). This
generalises `Erase.pendingOfFulfil` to several threads. -/
theorem Erase.unfulfil {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c v : Config I} (E : Erase rF g T v)
    (hv : PromSub c v)
    (hwf : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → ∀ p ∈ t.prom, ∃ w, c.mem.get? p = some w ∧ w.tid = i)
    (hcl : ∀ k tw, (k, tw) ∈ g.claims → ¬ Outstanding c tw)
    {pend' : List Time} (hpend : ∀ ts, ts ∈ pend' ↔ ts ∈ g.pend ∨ (Outstanding c ts ∧ ¬ Outstanding v ts)) :
    Erase rF { g with pend := pend' } T c := by
  have htot : SLR.total rF { g with pend := pend' } c = SLR.total rF g v := (hv.total rF { g with pend := pend' } g rfl).symm
  have hset : ∀ p, Settled c { g with pend := pend' } p ↔ Settled v g p := by
    intro p
    unfold Settled
    simp only [hpend]
    constructor
    · rintro (h | h | ⟨-, h⟩)
      · exact .inl fun h' => h (hv.outstanding h')
      · exact .inr h
      · exact .inl h
    · rintro (h | h)
      · by_cases ho : Outstanding c p
        · exact .inr (.inr ⟨ho, h⟩)
        · exact .inl ho
      · exact .inr (.inl h)
  have hmem := hv.mem
  have hfulf : ∀ x p, Fulf c { g with pend := pend' } x p ↔ Fulf v g x p := by
    intro x p; unfold Fulf; simp only [hset, hmem]
  have htr : ∀ r x, Tracked c { g with pend := pend' } r x ↔ Tracked v g r x := by
    intro r x; unfold Tracked; simp only [hset, hmem]
  exact {
    valid := htot ▸ E.valid
    slotIds := E.slotIds
    acqIds := htot ▸ E.acqIds
    relAcq := htot ▸ E.relAcq
    writes := by
      rw [htot]
      intro x hx p
      rw [hfulf]
      exact E.writes x ((htr _ x).mp hx) p
    pure := by rw [← hmem]; exact E.pure
    relExists := by rw [← hmem]; exact E.relExists
    slotsNodup := E.slotsNodup
    slotsDom := htot ▸ E.slotsDom
    slotsPred := by rw [← hmem]; exact E.slotsPred
    promWf := hwf
    promValid := by
      intro i t ht hT ts hts hp w hw
      simp only [hpend, not_or, not_and, Classical.not_not] at hp
      have ho : Outstanding v ts := hp.2 ⟨i, t, ht, hts⟩
      obtain ⟨j, tj, hj, htsj⟩ := ho
      -- the thread holding `ts` in `v` is its writer, i.e. `i`
      obtain ⟨w', hw', htid'⟩ := E.promWf j tj hj ts htsj
      obtain ⟨w'', hw'', htid''⟩ := hwf i t ht ts hts
      rw [hmem] at hw'
      have : w' = w'' := Option.some.inj (hw'.symm.trans hw'')
      subst this
      have hij : j = i := htid'.symm.trans htid''
      subst hij
      rw [← hmem] at hw
      exact E.promValid j tj hj hT ts htsj hp.1 w hw
    pend := by
      intro ts hts
      rcases (hpend ts).mp hts with h | ⟨ho, -⟩
      · obtain ⟨hw, ho⟩ := E.pend ts h
        exact ⟨hmem ▸ hw, hv.outstanding ho⟩
      · obtain ⟨i, t, ht, hts'⟩ := ho
        obtain ⟨w, hw, -⟩ := hwf i t ht ts hts'
        exact ⟨⟨w, hw⟩, ⟨i, t, ht, hts'⟩⟩
    updIds := htot ▸ E.updIds
    relSettled := fun k hk => (hset k.2).mpr (E.relSettled k hk)
    claimsNodup := E.claimsNodup
    claimsAt := by
      intro k tw hk
      obtain ⟨hlt, w', hw', hl, hs, hb⟩ := E.claimsAt k tw hk
      exact ⟨hlt, w', hmem ▸ hw', hl, (hset tw).mpr hs, fun ts w'' h1 h2 hw'' => hb ts w'' h1 h2 (hmem ▸ hw'')⟩
    claimFulf := hcl }

/-! ## Virtual configurations -/

/-- A virtual configuration has fewer outstanding promises per thread. -/
theorem PromSub.of_virtualOf {A : Arch} {c v : Config I} (h : c.VirtualOf A v) : PromSub c v := by
  obtain ⟨hm, hs, ht⟩ := h
  refine ⟨hm, hs, fun i t' hi => ?_⟩
  have hi' : i < c.threads.size := hs ▸ lt_size_of_get? hi
  obtain ⟨t'', hv, hnp, -⟩ := ht i c.threads[i] (Array.getElem?_eq_getElem hi')
  rw [hi] at hv; cases hv
  exact ⟨c.threads[i], Array.getElem?_eq_getElem hi', ThreadNP.prom_sub_of_silent hnp⟩

/-- **Erasure at a virtual configuration** (design (V) variant (ii)): from
erasure at the real configuration in which every promise the advance
fulfils is pending. -/
theorem Erase.virtualOf {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c v : Config I}
    (E : Erase rF g T c) (hv : c.VirtualOf A v) (hcov : ∀ ts, Outstanding c ts → ¬ Outstanding v ts → ts ∈ g.pend)
    {pend' : List Time} (hpend : ∀ ts, ts ∈ pend' ↔ ts ∈ g.pend ∧ Outstanding v ts) :
    Erase rF { g with pend := pend' } T v :=
  E.fulfil (PromSub.of_virtualOf hv) hcov hpend

/-- **Erasure at the real configuration from a virtual one**: the promises
the advance fulfilled become pending. -/
theorem Erase.ofVirtualOf {A : Arch} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c v : Config I}
    (E : Erase rF g T v) (hv : c.VirtualOf A v)
    (hwf : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → ∀ p ∈ t.prom, ∃ w, c.mem.get? p = some w ∧ w.tid = i)
    (hcl : ∀ k tw, (k, tw) ∈ g.claims → ¬ Outstanding c tw)
    {pend' : List Time} (hpend : ∀ ts, ts ∈ pend' ↔ ts ∈ g.pend ∨ (Outstanding c ts ∧ ¬ Outstanding v ts)) :
    Erase rF { g with pend := pend' } T c :=
  E.unfulfil (PromSub.of_virtualOf hv) hwf hcl hpend

end Kraken.Promising.SLR

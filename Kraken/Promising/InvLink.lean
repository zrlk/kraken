/-
The invariant environment and the full Promising machine, ISA-free part
(design note `Kraken/Promising/EnvWP.md`, "Invariant
environment").

A thread proved in `SharedEnv.inv S G` relies only on `G` holding of every
value it reads and guarantees `G` of every value it writes. Kang et al.'s write
invariant (`write_invariant`, in SLR's architecture) is exactly what makes
that sound over the whole machine, any number of threads, promises included.
What a thread's proof gives, per instruction, is a predicate `J tid` on its
ISA state that one instruction preserves from any memory satisfying
`MemInv G` (`StepPreserves`). From it:

- `configInv_reachable`: every configuration `Reachable` from one satisfying
  `MemInv G` and every `J tid` satisfies them again. Promise steps are
  handled once, as in `write_invariant`: the promised message is written on a
  promise-free run of the thread alone (`CertWrite`), along which `J` and
  `MemInv G` are carried; a promise step changes only the thread's promise
  set, never its ISA state.
- `writesPreserve_of_stepPreserves`: the premise `WritesPreserve` of
  `write_invariant`, so the per-thread proofs discharge the write invariant's
  obligation and `write_invariant` applies as it stands.

Per instruction, `EvTree.AllInv G Q` is the event-tree judgment an
`AllEnv (inv S G)` judgment becomes under each ISA's adapter (reads return any
value satisfying `G`; writes satisfy `G`), and `stepOne_allInv` is what one
instruction of the machine does with it: the new ISA state satisfies `Q` and
the memory keeps `MemInv G` (a write appends a message satisfying `G`, or
fulfils an existing promise and appends nothing).

The ISA parts (`InvLinkX64.lean`, `InvLinkAArch64.lean`) build `J` from a
`Safely`/`Eventually` judgment of `instrStepEnv (inv S G)`.
-/
import Kraken.Promising.PromiseSafe
import Kraken.Promising.ReachableK

namespace Kraken.Promising

variable {I : ISA}

/-! ## Event trees in the invariant environment -/

/-- Every run of the tree in which every read returns a value satisfying `G`
writes only values satisfying `G` and ends in a state satisfying `Q`. A store
succeeds, or fails if it is exclusive (as `runTree` runs it). An
`rmw`'s operation must map every old value satisfying `G` to one satisfying
`G`. Faults (no run) are vacuous. -/
def EvTree.AllInv {σ : Type} (G : Loc → Val → Prop) (Q : σ → Prop) : EvTree σ → Prop
  | .done s => Q s
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).AllInv G Q
  | .load _ _ l ret => ∀ v, G l v → (ret v).AllInv G Q
  | .store _ xcl l v ret => G l v ∧ ∀ b, (b = true ∨ xcl = true) → (ret b).AllInv G Q
  | .rmw _ _ l op ret => ∀ old, G l old → (∀ v, op old = some v → G l v) ∧ (ret old).AllInv G Q
  | .fence _ ret => ∀ u, (ret u).AllInv G Q

theorem EvTree.allInv_map {σ τ : Type} (G : Loc → Val → Prop) (f : σ → τ) (Q : τ → Prop) :
    ∀ t : EvTree σ, (t.map f).AllInv G Q ↔ t.AllInv G (fun s => Q (f s))
  | .done _ => Iff.rfl
  | .fault _ => Iff.rfl
  | .choose _ k => forall_congr' fun i => allInv_map G f Q (k i)
  | .load _ _ _ ret => forall_congr' fun v => imp_congr_right fun _ => allInv_map G f Q (ret v)
  | .store _ _ _ _ ret => and_congr_right fun _ => forall_congr' fun b =>
      imp_congr_right fun _ => allInv_map G f Q (ret b)
  | .rmw _ _ _ _ ret => forall_congr' fun v => imp_congr_right fun _ =>
      and_congr_right fun _ => allInv_map G f Q (ret v)
  | .fence _ ret => forall_congr' fun u => allInv_map G f Q (ret u)

theorem EvTree.AllInv.mono {σ : Type} {G : Loc → Val → Prop} {Q Q' : σ → Prop} (hQ : ∀ s, Q s → Q' s) :
    ∀ {t : EvTree σ}, t.AllInv G Q → t.AllInv G Q'
  | .done _, h => hQ _ h
  | .fault _, h => h
  | .choose _ _, h => fun i => mono hQ (h i)
  | .load _ _ _ _, h => fun v hv => mono hQ (h v hv)
  | .store _ _ _ _ _, h => ⟨h.1, fun b hb => mono hQ (h.2 b hb)⟩
  | .rmw _ _ _ _ _, h => fun v hv => ⟨(h v hv).1, mono hQ (h v hv).2⟩
  | .fence _ _, h => fun u => mono hQ (h u)

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

private theorem ite_none_right' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then y else none) = some x) : y = some x := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

private theorem ite_none_left' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

private theorem mem_ite_nil' {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α}
    (h : x ∈ (if p then ys else [])) : x ∈ ys := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

/-- A read returns a value of the memory at the location, and leaves the
memory unchanged. -/
theorem readSuccs_read {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) :
    c.mem.read? l x.1 = some x.2.1 ∧ x.2.2.mem = c.mem := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · rename_i v hv
    have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨hv, rfl⟩

/-- A write keeps `MemInv G` if its value satisfies `G`: it fulfils a
promise (no new message) or appends its message. -/
theorem writeSuccs_memInv {xr : View} {G : Loc → Val → Prop} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hm : MemInv G c.mem) (hG : G l v) : MemInv G c'.mem := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, ht⟩ | h
  · split at ht
    · have h := ite_none_right' ht
      simp only [Option.some.injEq] at h
      subst h
      exact hm
    · cases ht
  · have h := mem_ite_nil' h
    rw [List.mem_singleton] at h
    subst h
    exact hm.append (w := { loc := l, val := v, tid }) hG

private theorem fenceOpt_mem (c : Ctx) (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).mem = c.mem := by
  cases b
  · rfl
  · exact fenceStep_mem c k

/-- **One tree, from a memory satisfying `MemInv G`**: every successful run
ends in a state satisfying `Q` and a memory satisfying `MemInv G`. -/
theorem runTree_allInv {σ : Type} {G : Loc → Val → Prop} {Q : σ → Prop} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → tree.AllInv G Q →
      MemInv G c.mem → Q s ∧ MemInv G c'.mem := by
  induction tree with
  | done s0 =>
    intro c s c' h hQ hm
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hQ, hm⟩
  | fault msg =>
    intro c s c' h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' h hQ hm
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hi (hQ i) hm
  | load k xcl l ret ih =>
    intro c s c' h hQ hm
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    obtain ⟨hr, hm0⟩ := readSuccs_read A iv h0
    exact ih v c0 s c' h (hQ v (hm.read? hr)) (hm0 ▸ hm)
  | store k xcl l v ret ih =>
    intro c s c' h hQ hm
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true c0 s c' h (hQ.2 true (.inl rfl)) (writeSuccs_memInv A tid _ hc0 hm hQ.1)
    · rw [List.mem_ite_nil_right] at h
      exact ih false _ s c' h.2 (hQ.2 false (.inr h.1)) hm
  | fence k ret ih =>
    intro c s c' h hQ hm
    simp only [runTree] at h
    exact ih () _ s c' h (hQ ()) ((fenceStep_mem c k).symm ▸ hm)
  | rmw k noRet l op ret ih =>
    intro c s c' h hQ hm
    simp only [runTree] at h
    have h1 := fenceOpt_mem c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    obtain ⟨hr, hm2⟩ := readSuccs_read A iv h2
    have hm1 : MemInv G c1.mem := h1 ▸ hm
    have hGold := hm1.read? hr
    obtain ⟨hop, hret⟩ := hQ old hGold
    have hmc2 : MemInv G c2.mem := hm2 ▸ hm1
    simp only at h
    split at h
    · exact ih old _ s c' h hret ((fenceOpt_mem c2 A.rmwFence .sy).symm ▸ hmc2)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have hm3 := writeSuccs_memInv A tid _ hc3 hmc2 (hop new hnew)
      refine ih old _ s c' h hret ?_
      rw [fenceOpt_mem]
      split <;> exact hm3

end Rules

/-- **One instruction, from a memory satisfying `MemInv G`.** If the
instruction's event tree satisfies `AllInv G Q`, every outcome's ISA state
satisfies `Q` and its memory `MemInv G`. -/
theorem stepOne_allInv (A : Arch) {G : Loc → Val → Prop} {Q : I.State → Prop} {t : Thread I} {tid : Nat}
    {mem : Memory} {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hQ : ∀ tree, I.exec t.st = some tree → tree.AllInv G Q)
    (hm : MemInv G mem) : Q o.thread.st ∧ MemInv G o.mem := by
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
      rw [finishInstr_st hth]
      exact runTree_allInv A tid _ tree _ st c' hr (hQ tree hex) hm

/-! ## Per-thread invariants over the full machine -/

/-- One instruction of thread `tid`, from an ISA state satisfying `J tid` and
a memory satisfying `MemInv G`, yields an ISA state satisfying `J tid` and a
memory satisfying `MemInv G`. Each thread id may have its own `J` (its own
program). Nothing is assumed of the views or promises. -/
def StepPreserves (A : Arch) (G : Loc → Val → Prop) (J : Nat → I.State → Prop) : Prop :=
  ∀ (tid : Nat) (t : Thread I) (mem : Memory) (outs : List (Except String (Outcome I))) (o : Outcome I),
    J tid t.st → MemInv G mem → stepOne A t tid mem = some outs → .ok o ∈ outs →
      J tid o.thread.st ∧ MemInv G o.mem

/-- The memory satisfies `MemInv G` and every thread's ISA state its `J`. -/
def ConfigInv (G : Loc → Val → Prop) (J : Nat → I.State → Prop) (c : Config I) : Prop :=
  MemInv G c.mem ∧ ∀ tid t, c.threads[tid]? = some t → J tid t.st

/-- `StepPreserves` along a promise-free run of one thread. -/
theorem ThreadNP.stepPreserves {A : Arch} {G : Loc → Val → Prop} {J : Nat → I.State → Prop}
    (hJ : StepPreserves A G J) {tid : Nat} {p q : Thread I × Memory} (h : ThreadNP A tid p q) :
    J tid p.1.st → MemInv G p.2 → J tid q.1.st ∧ MemInv G q.2 := by
  induction h with
  | refl => exact fun h1 h2 => ⟨h1, h2⟩
  | step hs _ ih =>
    intro h1 h2
    obtain ⟨outs, o, h3, h4, rfl⟩ := hs
    obtain ⟨h5, h6⟩ := hJ _ _ _ _ _ h1 h2 h3 h4
    exact ih h5 h6

theorem withThread_threads {c : Config I} {tid : Nat} {th : Thread I} {mem : Memory}
    {P : Nat → Thread I → Prop} (hc : ∀ tid' t', c.threads[tid']? = some t' → P tid' t') (hth : P tid th) :
    ∀ tid' t', (c.withThread tid th mem).threads[tid']? = some t' → P tid' t' := by
  intro tid' t' h
  simp only [Config.withThread, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds] at h
  split at h
  · rename_i heq
    subst heq
    split at h
    · cases h; exact hth
    · cases h
  · exact hc tid' t' h

/-- `configInv_reachable` along `ReachableK` (the `ReachableK` twin, fuel-free). -/
theorem configInv_reachableK {A : Arch} {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop} (hJ : StepPreserves A G J) {c0 c : Config I} (h0 : ConfigInv G J c0)
    (h : Live.Bridge.ReachableK A c0 c) : ConfigInv G J c := by
  refine h.inv (fun c c' h0 hs => ?_) h0
  obtain ⟨hm, hth⟩ := h0
  cases hs with
  | @instr tid t outs o ht hstep ho =>
    obtain ⟨hJo, hmo⟩ := hJ _ _ _ _ _ (hth tid t ht) hm hstep ho
    exact ⟨hmo, withThread_threads (P := fun tid t => J tid t.st) hth hJo⟩
  | @promise tid t p ht hw =>
    obtain ⟨t1, mem1, outs, o, hnp, hstep, ho, hp⟩ := hw
    obtain ⟨hJ1, hm1⟩ := hnp.stepPreserves hJ (hth tid t ht) hm
    obtain ⟨-, hmo⟩ := hJ _ _ _ _ _ hJ1 hm1 hstep ho
    obtain ⟨hi, hmsgs⟩ := stepOne_ext A hstep ho
    have hG := ((MemInv.of_ext hi hmsgs).mp hmo).2 p.1 (List.mem_map_of_mem hp)
    exact ⟨hm.append hG, withThread_threads (P := fun tid t => J tid t.st) hth (hth tid t ht)⟩

/-- **Per-thread invariants hold at every reachable configuration of the full
machine, promises included.** If every thread's instruction steps preserve its
`J` and `MemInv G` (`StepPreserves`), then from a configuration satisfying
them every `Reachable` configuration does too. A promise step appends a
message written by a promise-free run of the thread alone, along which `J`
and `MemInv G` are carried, and leaves the thread's ISA state unchanged. -/
theorem configInv_reachable {A : Arch} [I.LawfulState] {fuel : Nat} {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop} (hJ : StepPreserves A G J) {c0 c : Config I} (h0 : ConfigInv G J c0)
    (h : Reachable A fuel c0 c) : ConfigInv G J c :=
  configInv_reachableK hJ h0 (.of_reachable h)

/-- **The write obligation, from per-thread invariants.** `StepPreserves`
and the invariants at `c0` discharge `write_invariant`'s premise. -/
theorem writesPreserve_of_stepPreserves {A : Arch} [I.LawfulState] {fuel : Nat} {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop} (hJ : StepPreserves A G J) {c0 : Config I} (h0 : ConfigInv G J c0) :
    WritesPreserve A fuel G c0 := by
  intro c hc tid t ht t1 mem1 hnp hm1 outs o hstep ho
  obtain ⟨hm, hth⟩ := configInv_reachable hJ h0 hc
  obtain ⟨hJ1, -⟩ := hnp.stepPreserves hJ (hth tid t ht) hm
  exact (hJ _ _ _ _ _ hJ1 hm1 hstep ho).2

/-- `write_invariant` through the per-thread invariants: `MemInv G` at every
reachable configuration. (Also a direct corollary of `configInv_reachable`;
stated through `write_invariant` to show that its premise is met.) -/
theorem memInv_reachable {A : Arch} [I.LawfulState] {fuel : Nat} {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop} (hJ : StepPreserves A G J) {c0 c : Config I} (h0 : ConfigInv G J c0)
    (h : Reachable A fuel c0 c) : MemInv G c.mem :=
  write_invariant h0.1 (writesPreserve_of_stepPreserves hJ h0) h

/-! ## The initial memory -/

/-- A message-free memory whose declared initial values satisfy `G`, where
`G` holds of `0` everywhere (the fallback of undeclared locations), satisfies
`MemInv G`. -/
theorem MemInv.of_init {G : Loc → Val → Prop} {m : Memory} (hmsgs : m.msgs = #[]) (h0 : ∀ l, G l 0)
    (hinit : ∀ p ∈ m.init, G p.1 p.2) : MemInv G m := by
  refine ⟨fun l => ?_, fun w hw => by simp [hmsgs] at hw⟩
  unfold Memory.initVal
  cases hf : m.init.find? (·.1 == l) with
  | none => exact h0 l
  | some p =>
    have hp := List.mem_of_find?_eq_some hf
    have hl : p.1 = l := by simpa using List.find?_some hf
    simpa [hl] using hinit p hp

/-- The common shape `G l v := l ∈ S → P l v`, with `P` true of `0`: a
message-free memory whose declared values satisfy `P` on `S` satisfies it. -/
theorem MemInv.of_init_on {S : List Loc} {P : Loc → Val → Prop} {m : Memory} (hmsgs : m.msgs = #[])
    (h0 : ∀ l ∈ S, P l 0) (hinit : ∀ p ∈ m.init, p.1 ∈ S → P p.1 p.2) :
    MemInv (fun l v => l ∈ S → P l v) m :=
  MemInv.of_init hmsgs (fun l hl => h0 l hl) hinit

end Kraken.Promising

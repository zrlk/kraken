/-
Termination on the Promising machine (design note `Kraken/Promising/EnvWP.md`, "Termination").

`SeqReach.sim`/`reachablePF_sim` (`Kraken.Promising.SeqLink`) say what an
`Eventually` judgment gives along promise-free runs that *exist*. They say
nothing about runs that never end. This file turns a total (`Eventually`)
judgment into termination statements about the promise-free fragment of the
one-thread machine. ISA-free; each ISA's environment link instantiates it.

- `StepPF A fuel`: the promise-free machine step in `Eventually`'s shape,
  *without* asking for a successor: every successor of `succs` that leaves no
  promise outstanding is in the post-set. `Eventually (StepPF A fuel) Q c`
  therefore says: **no infinite promise-free run from `c` avoids `Q`**; every
  maximal promise-free run meets `Q` or stops (has no promise-free successor).
  A configuration where the thread faults has no successor, so it satisfies
  `Eventually (StepPF A fuel) Q` vacuously (`reachablePF_sim_noDiv`).
- `BoundedPF A fuel Q n c`: every promise-free run from `c` meets `Q` within
  `n` steps or stops before. `Eventually (StepPF A fuel)` gives some bound
  (`eventually_stepPF_bounded`, by finiteness of `succs`).
- `StepPF'`: `StepPF` that also asks for a promise-free successor.
  `Eventually (StepPF' A fuel) Q c` is termination proper: every maximal
  promise-free run meets `Q`, none stops before. This needs completeness of
  the machine for the instructions met (`seqProgress`): `EvTree.SeqOk tid mem t`
  (a sequential run of `t` that the machine takes too) at every step, which
  `runTree_seqOk` and `succs_seqOk` turn into a promise-free successor
  (`reachablePF_sim_term`). `EvTree.NoFault` (no fault leaf, every `choose`
  nonempty) implies `SeqOk` at every memory (`EvTree.NoFault.seqOk`).

`fuel` (the certification budget) plays no role in a promise-free step: an
instruction step of a promise-free thread certifies nothing, and every
promise step leaves a promise outstanding. The statements hold for every
`fuel`.

Why `SeqOk` is a hypothesis: the ISA adapters translate an `undefined` value
of a register, vector or flags type, and a line-crossing vector piece, into
`.fault`, where Kraken's single-threaded semantics (`Effects.All`, `AllEnv`)
lets the value be arbitrary. So a total environment judgment does not by
itself exclude a promise-free run that faults (EnvWP.md, open items).
-/
import Kraken.Promising.SeqLink

namespace Kraken.Promising

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## A tree the machine can run sequentially -/

/-- The tree has a sequential run that the promise-free machine takes as
well: a non-exclusive store succeeds, an exclusive store fails (the machine
always has the failing branch; the succeeding one needs a pairing load
exclusive), a `choose` takes some branch, and no `fault` is met. -/
def EvTree.SeqOk {σ : Type} (tid : Nat) (mem : Memory) : EvTree σ → Prop
  | .done _ => True
  | .fault _ => False
  | .choose _ k => ∃ i, (k i).SeqOk tid mem
  | .load _ _ l ret => (ret (mem.finalVal l)).SeqOk tid mem
  | .store _ xcl l v ret =>
    if xcl then (ret false).SeqOk tid mem
    else (ret true).SeqOk tid (mem.append { loc := l, val := v, tid }).1
  | .rmw _ _ l op ret =>
    match op (mem.finalVal l) with
    | some v => (ret (mem.finalVal l)).SeqOk tid (mem.append { loc := l, val := v, tid }).1
    | none => (ret (mem.finalVal l)).SeqOk tid mem
  | .fence _ ret => (ret ()).SeqOk tid mem

/-- No `fault` leaf anywhere in the tree, and every `choose` has a branch. -/
def EvTree.NoFault {σ : Type} : EvTree σ → Prop
  | .done _ => True
  | .fault _ => False
  | .choose n k => 0 < n ∧ ∀ i, (k i).NoFault
  | .load _ _ _ ret => ∀ v, (ret v).NoFault
  | .store _ _ _ _ ret => ∀ b, (ret b).NoFault
  | .rmw _ _ _ _ ret => ∀ v, (ret v).NoFault
  | .fence _ ret => (ret ()).NoFault

/-- A tree without faults has a sequential run the machine takes, at every
memory. -/
theorem EvTree.NoFault.seqOk {σ : Type} (tid : Nat) {t : EvTree σ} (h : t.NoFault) :
    ∀ mem, t.SeqOk tid mem := by
  induction t with
  | done s => intro mem; trivial
  | fault m => exact h.elim
  | choose n k ih => intro mem; exact ⟨⟨0, h.1⟩, ih _ (h.2 _) mem⟩
  | load k xcl l ret ih => intro mem; exact ih _ (h _) mem
  | store k xcl l v ret ih =>
    intro mem
    simp only [SeqOk]
    split
    · exact ih _ (h _) mem
    · exact ih _ (h _) _
  | rmw k noRet l op ret ih =>
    intro mem
    simp only [SeqOk]
    split <;> exact ih _ (h _) _
  | fence k ret ih => intro mem; exact ih _ h mem

theorem EvTree.seqOk_map {σ τ : Type} (tid : Nat) (f : σ → τ) (t : EvTree σ) :
    ∀ mem, (t.map f).SeqOk tid mem ↔ t.SeqOk tid mem := by
  induction t with
  | done s => intro mem; exact Iff.rfl
  | fault m => intro mem; exact Iff.rfl
  | choose n k ih => intro mem; exact exists_congr fun i => ih i mem
  | load k xcl l ret ih => intro mem; exact ih _ mem
  | store k xcl l v ret ih =>
    intro mem
    simp only [EvTree.map, SeqOk]
    split
    · exact ih _ mem
    · exact ih _ _
  | rmw k noRet l op ret ih =>
    intro mem
    simp only [EvTree.map, SeqOk]
    split <;> exact ih _ _
  | fence k ret ih => intro mem; exact ih _ mem

theorem EvTree.noFault_map {σ τ : Type} (f : σ → τ) (t : EvTree σ) : (t.map f).NoFault ↔ t.NoFault := by
  induction t with
  | done s => exact Iff.rfl
  | fault m => exact Iff.rfl
  | choose n k ih => exact and_congr Iff.rfl (forall_congr' fun i => ih i)
  | load k xcl l ret ih => exact forall_congr' fun v => ih v
  | store k xcl l v ret ih => exact forall_congr' fun b => ih b
  | rmw k noRet l op ret ih => exact forall_congr' fun v => ih v
  | fence k ret ih => exact ih ()

/-! ## Completeness: a `SeqOk` tree has a promise-free run -/

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- From a `Seq` context, a `SeqOk` tree has a successful promising run (by
`runTree_sound`, it is a sequential run and ends in a `Seq` context). Unlike
`runTree_complete`, RMWs and store exclusives are allowed. -/
theorem runTree_seqOk {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx), c.Seq tid → iv.Le c.mem.last → tree.SeqOk tid c.mem →
      ∃ s c', .ok (s, c') ∈ runTree A tid iv c tree := by
  induction tree with
  | done s0 =>
    intro c _ _ _
    exact ⟨s0, c, by simp [runTree]⟩
  | fault msg =>
    intro c _ _ h
    exact h.elim
  | choose n k ih =>
    intro c hc hiv h
    obtain ⟨i, hi⟩ := h
    obtain ⟨s, c', h1⟩ := ih i c hc hiv hi
    exact ⟨s, c', by simp only [runTree, List.mem_flatMap]; exact ⟨i, List.mem_finRange i, h1⟩⟩
  | load k xcl l ret ih =>
    intro c hc hiv h
    obtain ⟨c0, hread, hm0, hs0⟩ := readSuccs_eq A tid iv k xcl l false hc hiv
    simp only [EvTree.SeqOk] at h
    rw [← hm0] at h
    obtain ⟨s, c', h1⟩ := ih _ c0 hs0 (hm0 ▸ hiv) h
    refine ⟨s, c', ?_⟩
    simp only [runTree, hread, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← hm0]
    exact h1
  | store k xcl l v ret ih =>
    intro c hc hiv h
    cases xcl with
    | true =>
      simp only [EvTree.SeqOk, ite_true] at h
      obtain ⟨s, c', h1⟩ := ih false _ (Ctx.Seq.xclFail tid hc l) hiv h
      refine ⟨s, c', ?_⟩
      simp only [runTree, ite_true, List.mem_append]
      exact .inr h1
    | false =>
      simp only [EvTree.SeqOk, Bool.false_eq_true, ite_false] at h
      obtain ⟨c0, hw, hm0, hs0⟩ := writeSuccs_eq A tid _ k false l v none 0 hc (hiv.forStore c.stores)
        (Nat.zero_le _) (fun _ h => by cases h)
      rw [← hm0] at h
      have hlast : c.mem.last ≤ c0.mem.last := by rw [hm0, Memory.last_append]; omega_t
      obtain ⟨s, c', h1⟩ := ih true c0 hs0 (hiv.mono hlast) h
      refine ⟨s, c', ?_⟩
      simp only [runTree, Bool.false_and, Bool.false_eq_true, ite_false, List.append_nil]
      rw [hw]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact h1
  | fence k ret ih =>
    intro c hc hiv h
    simp only [EvTree.SeqOk] at h
    rw [← fenceStep_mem c k] at h
    obtain ⟨s, c', h1⟩ := ih () _ (fenceStep_seq tid k hc) (by rw [fenceStep_mem]; exact hiv) h
    exact ⟨s, c', by simp only [runTree]; exact h1⟩
  | rmw k noRet l op ret ih =>
    intro c hc hiv h
    simp only [runTree]
    obtain ⟨hc1seq, hc1mem⟩ := Ctx.Seq.fenceOpt tid hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at hc1seq hc1mem ⊢
    obtain ⟨c2, hread, hm2, hs2⟩ :=
      readSuccs_eq A tid iv (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet hc1seq (hc1mem ▸ hiv)
    rw [hread]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hc1mem] at hm2 ⊢
    simp only [EvTree.SeqOk] at h
    cases hop : op (c.mem.finalVal l) with
    | none =>
      rw [hop] at h
      obtain ⟨hc3, hm3⟩ := Ctx.Seq.fenceOpt tid hs2 A.rmwFence .sy
      exact ih _ _ hc3 (by rw [hm3, hm2]; exact hiv) (by rw [hm3, hm2]; exact h)
    | some new =>
      rw [hop] at h
      simp only [List.mem_flatMap]
      have hextra : c2.loadViews.getLastD 0 ≤ c2.mem.last := by
        rw [List.getLastD_eq_getLast?]
        match hx : c2.loadViews.getLast? with
        | none => exact Nat.zero_le _
        | some a => exact hs2.loadViews a (List.mem_of_getLast? hx)
      have htr : ∀ t0, some (c.mem.lastWrite l) = some t0 → t0 ≤ c2.mem.last ∧
          ∀ (t' : Nat) (w : Msg), t0 < t' → c2.mem.get? t' = some w → w.loc = l → w.tid = tid := by
        intro t0 ht0
        cases ht0
        rw [hm2]
        exact ⟨c.mem.lastWrite_le l, fun t' w hlt hw hl => absurd hl (c.mem.not_write_of_lastWrite_lt l hlt hw)⟩
      obtain ⟨c3', hw, hm3, hs3⟩ :=
        writeSuccs_eq A tid iv (A.rmwKind k).storeKind true l new _ _ hs2 (hm2 ▸ hiv) hextra htr
      rw [hw]
      obtain ⟨hc5, hm5⟩ := Ctx.Seq.rmwTail tid hs3 l A.rmwFence (A.rmwKind k == .acqRel && !noRet)
      have hlast : c.mem.last ≤ c3'.mem.last := by rw [hm3, hm2, Memory.last_append]; omega_t
      obtain ⟨s, c', h1⟩ := ih _ _ hc5 (by rw [hm5]; exact hiv.mono hlast) (by rw [hm5, hm3, hm2]; exact h)
      exact ⟨s, c', _, List.mem_singleton_self _, h1⟩

end Rules

/-! ## The promise-free step of a one-thread configuration -/

section Machine

variable {I : ISA}

/-- The promise-free machine step in `Eventually`'s shape, without asking for
a successor: every successor that leaves no promise outstanding is in `R`.
`Eventually (StepPF A fuel) Q c`: no infinite promise-free run from `c`
avoids `Q` (a run may also stop where it has no promise-free successor). -/
def StepPF (A : Arch) (fuel : Nat) (c : Config I) (R : Config I → Prop) : Prop :=
  ∀ c' ∈ (succs A c fuel).1, c'.PromFree → R c'

/-- `StepPF` with a promise-free successor: `Eventually (StepPF' A fuel) Q c`
is termination: every maximal promise-free run from `c` is finite and ends
in `Q`. -/
def StepPF' (A : Arch) (fuel : Nat) (c : Config I) (R : Config I → Prop) : Prop :=
  (∃ c' ∈ (succs A c fuel).1, c'.PromFree) ∧ StepPF A fuel c R

theorem Config.eq_one {c : Config I} {t : Thread I} (h : c.threads = #[t]) : c = ⟨#[t], c.mem⟩ := by
  cases c; simp only at h; rw [h]

/-- The instruction-step successors `succsL` keeps: every successful outcome
whose thread has no promise outstanding. -/
private theorem mem_foldl_outcomes (A : Arch) (fuel : Nat) (c : Config I) (tid : Nat)
    (outs : List (Except String (Outcome I)))
    (init : List (Config I × List TraceEv) × Bool × List String × CertCache I) :
    ∀ x, (x ∈ init.1 ∨ ∃ o, .ok o ∈ outs ∧ o.thread.prom = [] ∧ x = (c.withThread tid o.thread o.mem, o.log)) →
      x ∈ (outs.foldl (fun (next, bound, faults, cache) (o : Except String (Outcome I)) =>
        match o with
        | .error m => (next, bound, faults ++ [m], cache)
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: next, bound, faults, cache)
          else
            let (r, cache) := certify A cache o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: next, bound || r.boundHit, faults, cache)
            else (next, bound || r.boundHit, faults, cache)) init).1 := by
  induction outs generalizing init with
  | nil =>
    rintro x (hx | ⟨o, ho, -⟩)
    · exact hx
    · exact absurd ho List.not_mem_nil
  | cons o0 outs ih =>
    rintro x hx
    rw [List.foldl_cons]
    apply ih
    rcases hx with hx | ⟨o, ho, hprom, rfl⟩
    · left
      obtain ⟨next, bound, faults, cache⟩ := init
      cases o0 with
      | error m => exact hx
      | ok o =>
        simp only
        split
        · exact List.mem_cons_of_mem _ hx
        · split
          · exact List.mem_cons_of_mem _ hx
          · exact hx
    · rcases List.mem_cons.mp ho with h | h
      · left
        subst h
        obtain ⟨next, bound, faults, cache⟩ := init
        simp only [hprom, List.isEmpty_nil, ite_true]
        exact List.mem_cons_self
      · exact .inr ⟨o, h, hprom, rfl⟩

/-- A promise-free successor exists when the instruction's tree is `SeqOk`:
the machine takes the sequential run. -/
theorem succs_seqOk (A : Arch) (fuel : Nat) {t : Thread I} {mem : Memory} (ht : t.Seq 0 mem)
    {tree : EvTree I.State} (hex : I.exec t.st = some tree) (hok : tree.SeqOk 0 mem) :
    ∃ c' ∈ (succs A ⟨#[t], mem⟩ fuel).1, c'.PromFree := by
  have hregs : t.RegsLe mem.last := ⟨ht.rview, ht.wview⟩
  have hc : Ctx.Seq 0 { views := t.views, prom := t.prom, mem, log := [.instr 0 (I.showInstr t.st)] } :=
    ⟨ht.prom, ht.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩
  have hiv := instrViews_le hregs (I.deps t.st)
  obtain ⟨s, c', hrun⟩ := runTree_seqOk A 0 _ tree _ hc hiv hok
  obtain ⟨hseq, hc'⟩ := runTree_sound A 0 _ tree _ hc hiv s c' hrun
  have hlast := seqRun_last_le 0 tree mem s c'.mem hseq
  -- `finishInstr` returns at least one thread, each `Seq`
  have hne : finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s c' ≠ [] := by
    unfold finishInstr
    simp only
    split <;> simp
  obtain ⟨th, hth⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨-, hth'⟩ := finishInstr_seq hc' (hiv.mono hlast) (hregs.mono hlast) th hth
  let o : Outcome I := { thread := th, mem := c'.mem, promisedNow := c'.promisedNow, log := c'.log }
  obtain ⟨outs, houts⟩ : ∃ outs, stepOne A t 0 mem = some outs := by
    unfold stepOne
    rw [hex]
    exact ⟨_, rfl⟩
  have ho : (.ok o : Except String (Outcome I)) ∈ outs := by
    have h := houts
    unfold stepOne at h
    rw [hex] at h
    have h' : _ = outs := Option.some.inj h
    subst h'
    rw [List.mem_flatMap]
    exact ⟨.ok (s, c'), hrun, by simp only [List.mem_map]; exact ⟨th, hth, rfl⟩⟩
  have hr : List.range (#[t] : Array (Thread I)).size = [0] := rfl
  have hget : (#[t] : Array (Thread I))[0]? = some t := rfl
  refine ⟨Config.withThread ⟨#[t], mem⟩ 0 th c'.mem, ?_, ?_⟩
  · simp only [succs, succsL, hr, List.foldl_cons, List.foldl_nil, stepThread_one, houts, certifiedPromises,
      hget, List.map_append, List.mem_append]
    left
    rw [List.mem_map]
    refine ⟨(_, o.log), ?_, rfl⟩
    rw [List.mem_reverse]
    exact mem_foldl_outcomes A fuel ⟨#[t], mem⟩ 0 outs ([], false, [], ∅) _ (.inr ⟨o, ho, hth'.prom, rfl⟩)
  · intro t' ht'
    rw [Config.withThread_one, Array.mem_singleton] at ht'
    subst ht'
    exact hth'.prom

/-! ## Carrying a total judgment to the machine -/

section Sim

variable {β : Type}

/-- The step-wise part of the termination link: from a `Seq` one-thread
configuration related to a state with an `Eventually T P` judgment, no
infinite promise-free run avoids the configurations related to a `P` state. -/
theorem seqSim_noDiv (A : Arch) (fuel : Nat) {Rel : I.State × Memory → β → Prop}
    {T : β → (β → Prop) → Prop} (hsim : SeqSim I 0 Rel T) {P : β → Prop} {y : β}
    (hev : Eventually T P y) :
    ∀ (t : Thread I) (mem : Memory), t.Seq 0 mem → Rel (t.st, mem) y →
      Eventually (StepPF A fuel)
        (fun c => ∃ t' y', c.threads = #[t'] ∧ t'.Seq 0 c.mem ∧ Rel (t'.st, c.mem) y' ∧ P y')
        ⟨#[t], mem⟩ := by
  induction hev with
  | done y hP => intro t mem ht hr; exact .done _ ⟨t, y, rfl, ht, hr, hP⟩
  | step y mid hT _ ih =>
    intro t mem ht hr
    refine .step _ (fun c' => c' ∈ (succs A ⟨#[t], mem⟩ fuel).1 ∧ c'.PromFree) (fun c' h1 h2 => ⟨h1, h2⟩) ?_
    rintro c' ⟨hc', hpf⟩
    obtain ⟨t', tree, hth, hex, hseq, ht'⟩ := succs_sound A fuel ht hc' hpf
    obtain ⟨y', hr', hmid⟩ := (tree.allSeq_iff 0 mem _).mp (hsim (t.st, mem) y mid hr hT tree hex) _ hseq
    rw [Config.eq_one hth]
    exact ih y' hmid t' c'.mem ht' hr'

/-- As `seqSim_noDiv`, with `StepPF'`: when every related state with a `T`
step has a `SeqOk` instruction tree (`hprog`), every promise-free run from
the configuration terminates in a configuration related to a `P` state. -/
theorem seqSim_term (A : Arch) (fuel : Nat) {Rel : I.State × Memory → β → Prop}
    {T : β → (β → Prop) → Prop} (hsim : SeqSim I 0 Rel T)
    (hprog : ∀ x y R, Rel x y → T y R → ∃ tree, I.exec x.1 = some tree ∧ tree.SeqOk 0 x.2)
    {P : β → Prop} {y : β} (hev : Eventually T P y) :
    ∀ (t : Thread I) (mem : Memory), t.Seq 0 mem → Rel (t.st, mem) y →
      Eventually (StepPF' A fuel)
        (fun c => ∃ t' y', c.threads = #[t'] ∧ t'.Seq 0 c.mem ∧ Rel (t'.st, c.mem) y' ∧ P y')
        ⟨#[t], mem⟩ := by
  induction hev with
  | done y hP => intro t mem ht hr; exact .done _ ⟨t, y, rfl, ht, hr, hP⟩
  | step y mid hT _ ih =>
    intro t mem ht hr
    obtain ⟨tree0, hex0, hok0⟩ := hprog (t.st, mem) y mid hr hT
    refine .step _ (fun c' => c' ∈ (succs A ⟨#[t], mem⟩ fuel).1 ∧ c'.PromFree)
      ⟨succs_seqOk A fuel ht hex0 hok0, fun c' h1 h2 => ⟨h1, h2⟩⟩ ?_
    rintro c' ⟨hc', hpf⟩
    obtain ⟨t', tree, hth, hex, hseq, ht'⟩ := succs_sound A fuel ht hc' hpf
    obtain ⟨y', hr', hmid⟩ := (tree.allSeq_iff 0 mem _).mp (hsim (t.st, mem) y mid hr hT tree hex) _ hseq
    rw [Config.eq_one hth]
    exact ih y' hmid t' c'.mem ht' hr'

/-- **No divergence**, for a fresh thread: an `Eventually T P` judgment
about the start state, simulating the sequential runs, gives: no infinite
promise-free run of the one-thread configuration avoids the configurations
whose thread is related to a `P` state. A run that stops (no promise-free
successor, e.g. the thread faults) counts as not diverging. -/
theorem reachablePF_sim_noDiv (A : Arch) (fuel : Nat) {Rel : I.State × Memory → β → Prop}
    {T : β → (β → Prop) → Prop} (hsim : SeqSim I 0 Rel T) {P : β → Prop}
    {st : I.State} {mem : Memory} (hm : mem.msgs = #[]) {y : β} (hxy : Rel (st, mem) y)
    (hev : Eventually T P y) :
    Eventually (StepPF A fuel) (fun c => ∃ t' y', c.threads = #[t'] ∧ t'.Seq 0 c.mem ∧ Rel (t'.st, c.mem) y' ∧ P y')
      ⟨#[Thread.init st], mem⟩ :=
  seqSim_noDiv A fuel hsim hev _ mem (Thread.init_seq 0 st hm) hxy

/-- **Termination**, for a fresh thread: as `reachablePF_sim_noDiv`, and
with `hprog` (the machine can run the instruction at every related state
with a `T` step) every maximal promise-free run is finite and ends related to
a `P` state. -/
theorem reachablePF_sim_term (A : Arch) (fuel : Nat) {Rel : I.State × Memory → β → Prop}
    {T : β → (β → Prop) → Prop} (hsim : SeqSim I 0 Rel T)
    (hprog : ∀ x y R, Rel x y → T y R → ∃ tree, I.exec x.1 = some tree ∧ tree.SeqOk 0 x.2) {P : β → Prop}
    {st : I.State} {mem : Memory} (hm : mem.msgs = #[]) {y : β} (hxy : Rel (st, mem) y)
    (hev : Eventually T P y) :
    Eventually (StepPF' A fuel) (fun c => ∃ t' y', c.threads = #[t'] ∧ t'.Seq 0 c.mem ∧ Rel (t'.st, c.mem) y' ∧ P y')
      ⟨#[Thread.init st], mem⟩ :=
  seqSim_term A fuel hsim hprog hev _ mem (Thread.init_seq 0 st hm) hxy

end Sim

/-! ## A bound -/

/-- Every promise-free run from `c` meets `Q` within `n` steps, or stops
before (has no promise-free successor). -/
def BoundedPF (A : Arch) (fuel : Nat) (Q : Config I → Prop) : Nat → Config I → Prop
  | 0, c => Q c
  | n + 1, c => Q c ∨ ∀ c' ∈ (succs A c fuel).1, c'.PromFree → BoundedPF A fuel Q n c'

theorem BoundedPF.mono {A : Arch} {fuel : Nat} {Q : Config I → Prop} :
    ∀ {n m : Nat} {c : Config I}, n ≤ m → BoundedPF A fuel Q n c → BoundedPF A fuel Q m c
  | 0, 0, _, _, h => h
  | 0, _ + 1, _, _, h => .inl h
  | _ + 1, 0, _, hnm, _ => absurd hnm (by omega)
  | _ + 1, _ + 1, _, hnm, h => h.imp id fun h c' hc hp => BoundedPF.mono (by omega) (h c' hc hp)

/-- Finitely many configurations, each with a bound, have a common bound. -/
private theorem BoundedPF.list {A : Arch} {fuel : Nat} {Q : Config I → Prop} (cs : List (Config I))
    (h : ∀ c ∈ cs, c.PromFree → ∃ n, BoundedPF A fuel Q n c) :
    ∃ N, ∀ c ∈ cs, c.PromFree → BoundedPF A fuel Q N c := by
  induction cs with
  | nil => exact ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | cons c cs ih =>
    obtain ⟨N, hN⟩ := ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    by_cases hp : c.PromFree
    · obtain ⟨n, hn⟩ := h c List.mem_cons_self hp
      refine ⟨max n N, fun c' hc' hp' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hn.mono (by omega)
      · exact (hN c' hc' hp').mono (by omega)
    · refine ⟨N, fun c' hc' hp' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact absurd hp' hp
      · exact hN c' hc' hp'

/-- No divergence gives a bound: `succs` is a finite list, so the
promise-free run tree is finitely branching (König). -/
theorem eventually_stepPF_bounded {A : Arch} {fuel : Nat} {Q : Config I → Prop} {c : Config I}
    (h : Eventually (StepPF A fuel) Q c) : ∃ n, BoundedPF A fuel Q n c := by
  induction h with
  | done c hQ => exact ⟨0, hQ⟩
  | step c mid hT _ ih =>
    obtain ⟨N, hN⟩ := BoundedPF.list (A := A) (fuel := fuel) (Q := Q) (succs A c fuel).1
      fun c' hc' hp => ih c' (hT c' hc' hp)
    exact ⟨N + 1, .inr hN⟩

theorem StepPF'.stepPF {A : Arch} {fuel : Nat} {c : Config I} {R : Config I → Prop}
    (h : StepPF' A fuel c R) : StepPF A fuel c R := h.2

/-- Termination implies no divergence. -/
theorem eventually_stepPF_of_stepPF' {A : Arch} {fuel : Nat} {Q : Config I → Prop} {c : Config I}
    (h : Eventually (StepPF' A fuel) Q c) : Eventually (StepPF A fuel) Q c := by
  induction h with
  | done c hQ => exact .done c hQ
  | step c mid hT _ ih => exact .step c mid hT.2 ih

end Machine

/-! ## A helper of the `dirs_no_fault` tactics -/

/-- A property of both branches holds of an `if`, at any decidability
instance. The `dirs_no_fault` tactics (`EnvLinkTermX64.lean`,
`EnvLinkTermAArch64.lean`) close a leftover flag test with it: x64 `je` keeps
a `CondCode.interp` instance after `simp`, which `split`, `rw [if_pos]` and
`simp` do not see through (the x64 Treiber proof's `TreiberX.prop_ite`, now an alias). -/
theorem prop_ite {α : Sort _} {P : α → Prop} {c : Prop} {h : Decidable c} {a b : α} (ha : P a) (hb : P b) :
    P (if c then a else b) := by
  split <;> assumption

end Kraken.Promising

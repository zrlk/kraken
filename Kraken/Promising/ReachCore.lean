/-
**Replaying a witness run as a `Reachable` proof**.

A *trace* is a list of steps `(tid, sel)`: run thread `tid`'s next
instruction and keep the first outcome whose read/write timestamps, in log
order, are `sel` (`ReachSel`) and that leaves the thread with no outstanding
promise. `reachRun A c tr` replays a trace from `c`; it is an ordinary
total function of the configuration, so `decide` evaluates it in the
kernel.

`reachRun_sound`: whatever `reachRun` returns is `Reachable` from where it
started. The proof never evaluates `succs`: an instruction outcome with no
outstanding promise is a member of `succs` whatever the certification cache
holds (`reach_mem_succs`), which matters because the cache is a hash map
(`mixHash` is opaque to the kernel).

`reach_witness`: the shape every reachability theorem takes, `∃ c,
Reachable A fuel c0 c ∧ c.final ∧ P c`, from one Boolean evaluation.

Promise steps are not covered (no target's witness needs one).
-/
import Kraken.Promising.Rel

namespace Kraken.Promising

variable {I : ISA}

/-! ## Membership in `succs` without evaluating certification -/

/-- The accumulator of `succsL`'s folds. -/
private abbrev ReachAcc (I : ISA) := List (Config I × List TraceEv) × Bool × List String × CertCache I

/-- A list fold whose accumulator only grows keeps a member. -/
private theorem reach_foldl_keeps {α β γ : Type} (proj : α → List γ) (f : α → β → α) (m : γ)
    (hmono : ∀ a b, m ∈ proj a → m ∈ proj (f a b)) :
    ∀ (l : List β) (a : α), m ∈ proj a → m ∈ proj (l.foldl f a)
  | [], _, h => h
  | b :: l, a, h => reach_foldl_keeps proj f m hmono l (f a b) (hmono a b h)

/-- …and has a member once some element adds it. -/
private theorem reach_foldl_adds {α β γ : Type} (proj : α → List γ) (f : α → β → α) (m : γ)
    (hmono : ∀ a b, m ∈ proj a → m ∈ proj (f a b)) (b₀ : β) (hadd : ∀ a, m ∈ proj (f a b₀)) :
    ∀ (l : List β) (a : α), b₀ ∈ l → m ∈ proj (l.foldl f a)
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact reach_foldl_keeps proj f m hmono l _ (hadd a)
    · exact reach_foldl_adds proj f m hmono b₀ hadd l (f a b) h

/-- The inner (per-outcome) fold of `succsL` only grows the successor list,
as configurations. -/
private theorem reach_inner_keeps (A : Arch) (c : Config I) (tid fuel : Nat) (m : Config I) :
    ∀ (a : ReachAcc I) (o : Except String (Outcome I)), m ∈ a.1.map (·.1) →
      m ∈ (match o with
        | .error msg => (a.1, a.2.1, a.2.2.1 ++ [msg], a.2.2.2)
        | .ok o =>
          let c' := c.withThread tid o.thread o.mem
          if o.thread.prom.isEmpty then ((c', o.log) :: a.1, a.2.1, a.2.2.1, a.2.2.2)
          else
            let (r, cache) := certify A a.2.2.2 o.thread tid o.mem fuel
            if r.certified then ((c', o.log) :: a.1, a.2.1 || r.boundHit, a.2.2.1, cache)
            else (a.1, a.2.1 || r.boundHit, a.2.2.1, cache) : ReachAcc I).1.map (·.1) := by
  rintro ⟨next, bound, faults, cache⟩ o hm
  simp only at hm ⊢
  split
  · exact hm
  · split
    · simp [hm]
    · split <;> simp_all

/-- **An instruction outcome with no outstanding promise is a successor**,
whatever certification computes. -/
theorem reach_mem_succs (A : Arch) (fuel : Nat) {c : Config I} {tid : Nat}
    {outs : List (Except String (Outcome I))} (hs : stepThread A c tid = some outs)
    {o : Outcome I} (ho : Except.ok o ∈ outs) (hp : o.thread.prom.isEmpty = true) :
    c.withThread tid o.thread o.mem ∈ (succs A c fuel).1 := by
  have hlt : tid < c.threads.size := by
    simp only [stepThread] at hs
    cases ht : c.threads[tid]? with
    | none => simp [ht] at hs
    | some t => exact (Array.getElem?_eq_some_iff.mp ht).1
  let m := c.withThread tid o.thread o.mem
  show m ∈ (succsL A {} c fuel none).1.map (·.1)
  unfold succsL
  refine reach_foldl_adds (fun x : ReachAcc I => x.1.map (·.1)) _ m ?_ tid ?_ _ _
    (List.mem_range.mpr hlt)
  · rintro ⟨next, bound, faults, cache⟩ t hm
    simp only
    split
    · simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
      exact Or.inl hm
    · rename_i outs' _
      simp only [List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
      left
      exact reach_foldl_keeps (fun x : ReachAcc I => x.1.map (·.1)) _ m
        (reach_inner_keeps A c t fuel m) outs' _ hm
  · rintro ⟨next, bound, faults, cache⟩
    simp only [hs, List.map_append, List.mem_append, List.map_reverse, List.mem_reverse]
    left
    refine reach_foldl_adds (fun x : ReachAcc I => x.1.map (·.1)) _ m
      (reach_inner_keeps A c tid fuel m) (.ok o) ?_ outs _ ho
    rintro ⟨next, bound, faults, cache⟩
    simp [hp, m]

/-! ## The checker -/

/-- The timestamps of an outcome's reads and writes, in log order: what a
trace step selects an outcome by. -/
def reachStamps (log : List TraceEv) : List Nat :=
  log.filterMap fun
    | .read _ t _ _ => some t
    | .write _ t _ _ => some t
    | _ => none

/-- An outcome a trace step accepts: no outstanding promise, and the
selected timestamps. -/
def ReachSel (sel : List Nat) (o : Except String (Outcome I)) : Option (Outcome I) :=
  match o with
  | .ok o => if o.thread.prom.isEmpty && reachStamps o.log == sel then some o else none
  | .error _ => none

/-- `stepOne` with the ISA's `exec` and `deps` replaced by `ex` and `dp`
(`reachStepOne_eq`: the same function when they are equal). An ISA whose
`exec` the kernel cannot evaluate (well-founded recursion with
`simp`-built decreasing proofs, e.g. `Executable.withAddresses`) supplies
a provably equal `ex` it can. -/
def reachStepOne (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId)
    (A : Arch) (t : Thread I) (tid : Nat) (mem : Memory) : Option (List (Except String (Outcome I))) := do
  let tree ← ex t.st
  let d := dp t.st
  let iv := instrViews t d
  let ctx : Ctx := { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }
  return (runTree A tid iv ctx tree).flatMap fun
    | .error m => [.error m]
    | .ok (st, c') => (finishInstr t d iv st c').map fun th =>
        .ok { thread := th, mem := c'.mem, promisedNow := c'.promisedNow, log := c'.log }

theorem reachStepOne_eq (A : Arch) (t : Thread I) (tid : Nat) (mem : Memory) :
    reachStepOne I.exec I.deps A t tid mem = stepOne A t tid mem := rfl

/-- One trace step: thread `tid`'s next instruction, the first outcome
`ReachSel sel` accepts. -/
def reachStep (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId)
    (A : Arch) (c : Config I) (tid : Nat) (sel : List Nat) : Option (Config I) :=
  match c.threads[tid]? with
  | none => none
  | some t => match reachStepOne ex dp A t tid c.mem with
    | none => none
    | some outs => (outs.findSome? (ReachSel sel)).map fun o => c.withThread tid o.thread o.mem

/-- Replay a trace. -/
def reachRun (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch) :
    Config I → List (Nat × List Nat) → Option (Config I)
  | c, [] => some c
  | c, (tid, sel) :: tr => (reachStep ex dp A c tid sel).bind fun c' => reachRun ex dp A c' tr

/-- **What a replayed step is** (shared by `reachStep_sound` and
`Live.reachStep_instrBy`): an accepted outcome of thread `tid`'s next
instruction, with no outstanding promise. -/
theorem reachStep_cases (A : Arch) {c c' : Config I} {tid : Nat} {sel : List Nat}
    (h : reachStep I.exec I.deps A c tid sel = some c') :
    ∃ t outs o, c.threads[tid]? = some t ∧ stepOne A t tid c.mem = some outs ∧ Except.ok o ∈ outs ∧
      o.thread.prom.isEmpty = true ∧ c' = c.withThread tid o.thread o.mem := by
  unfold reachStep at h
  split at h
  · cases h
  · rename_i t ht
    rw [reachStepOne_eq] at h
    split at h
    · cases h
    · rename_i outs hs
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨e, he, hsel⟩ := List.exists_of_findSome?_eq_some ho
      unfold ReachSel at hsel
      split at hsel
      · split at hsel
        · rename_i hc
          cases hsel
          exact ⟨t, outs, _, ht, hs, he, (Bool.and_eq_true _ _ ▸ hc).1, rfl⟩
        · cases hsel
      · cases hsel

theorem reachStep_sound (A : Arch) (fuel : Nat) {c c' : Config I} {tid : Nat} {sel : List Nat}
    (h : reachStep I.exec I.deps A c tid sel = some c') : c' ∈ (succs A c fuel).1 := by
  obtain ⟨t, outs, o, ht, hs, he, hp, rfl⟩ := reachStep_cases A h
  exact reach_mem_succs A fuel (by simp [stepThread, ht, hs]) he hp

/-- **Soundness of the checker**: a replayed trace is a run. -/
theorem reachRun_sound (A : Arch) (fuel : Nat) :
    ∀ {c c' : Config I} {tr : List (Nat × List Nat)}, reachRun I.exec I.deps A c tr = some c' →
      Reachable A fuel c c'
  | c, c', [], h => by cases h; exact .refl c
  | c, c', (tid, sel) :: tr, h => by
    simp only [reachRun] at h
    obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.mp h
    exact .step (reachStep_sound A fuel hm) (reachRun_sound A fuel hr)

/-- `Config.final` with `ex` for the ISA's `exec`. -/
def reachFinal (ex : I.State → Option (EvTree I.State)) (c : Config I) : Bool :=
  c.threads.all fun t => (ex t.st).isNone && t.prom.isEmpty

/-- The Boolean a reachability theorem evaluates: the trace replays to a
final configuration satisfying `p`. -/
def reachCheck (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (c0 : Config I) (tr : List (Nat × List Nat)) (p : Config I → Bool) : Bool :=
  match reachRun ex dp A c0 tr with
  | some c => reachFinal ex c && p c
  | none => false

/-- **A witness from one evaluation**: if `reachCheck` holds with an `ex`
and `dp` equal to the ISA's, some final configuration satisfying `p` is
reachable, at every fuel. -/
theorem reach_witness (A : Arch) (fuel : Nat) {ex : I.State → Option (EvTree I.State)}
    {dp : I.State → InstrDeps I.RegId} (hex : ex = I.exec) (hdp : dp = I.deps) {c0 : Config I}
    {tr : List (Nat × List Nat)} {p : Config I → Bool} (h : reachCheck ex dp A c0 tr p = true) :
    ∃ c, Reachable A fuel c0 c ∧ c.final = true ∧ p c = true := by
  subst hex hdp
  unfold reachCheck at h
  split at h
  · rename_i c hc
    exact ⟨c, reachRun_sound A fuel hc, (Bool.and_eq_true _ _ ▸ h).1, (Bool.and_eq_true _ _ ▸ h).2⟩
  · cases h

/-- `reach_witness` for a decidable property: the shape of the `Reach*`
theorems. -/
theorem reach_witness_prop (A : Arch) (fuel : Nat) {ex : I.State → Option (EvTree I.State)}
    {dp : I.State → InstrDeps I.RegId} (hex : ex = I.exec) (hdp : dp = I.deps) {c0 : Config I}
    {tr : List (Nat × List Nat)} {P : Config I → Prop} [DecidablePred P]
    (h : reachCheck ex dp A c0 tr (fun c => decide (P c)) = true) :
    ∃ c, Reachable A fuel c0 c ∧ c.final = true ∧ P c :=
  let ⟨c, hr, hf, hp⟩ := reach_witness A fuel hex hdp h
  ⟨c, hr, hf, of_decide_eq_true hp⟩

end Kraken.Promising

#print axioms Kraken.Promising.reachRun_sound
#print axioms Kraken.Promising.reach_witness

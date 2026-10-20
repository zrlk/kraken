/-
(O5) `PromisePure` from a per-instruction condition (ISA-neutral; option (C)): **impure values are written only by release writes**.

`PromisePure` (`SLR/Theorem1Proof.lean`) is a path property: on every real
path to a final configuration, a promise that is not `RelFulfilled` writes a
value that is pure for its location's release predicate. It does **not**
follow from `NPSafe` and the initial erasure alone: messages carry no mode,
the ghost's `relMsgs` may hold a plain write, so a plain store of an impure
value has an `NPSafe` proof, and its promise (fulfilled by the plain store) is
neither `RelFulfilled` nor pure. This file
replaces the path property by a condition on the instructions the program can
run, checked cell by cell like `promisePure_of_cells`:

- `EvTree.RelWrites A Q`: every store and every RMW write of the tree whose
  effective kind (`A.storeKind`) is not a release satisfies `Q`.
- `EvTree.NonRelWrite A l v`: the tree has a non-release write of `v` to `l`;
  `EvTree.relWrites_iff`: `RelWrites A Q` is "`Q` at every non-release write".
- `runTree_relFulfilsLive_of_relWrites`: a run of a `RelWrites A Q` tree that
  removes the promise `ts`, whose message fails `Q`, is a live release
  fulfilment (`EvTree.RelFulfilsLive`): the fulfilling write is a release
  write (store or RMW, anywhere in the tree). Generalises
  `relFulfils_of_store` (a single release store) and
  `runTree_relFulfils` (every write a release, `Arch.RelStores`).
- `promisePure_of_relWrites`: **`PromisePure` when every instruction at every
  reachable thread state writes impure values (for `rel`) only with release
  writes.** A corollary of the general forms:
  - `FulfilCell`, `promisePure_of_fulfilCell`: the cell condition asked only
    at the states where the promising thread still holds its promise;
  - `promisePure_of_relWritesT`: with a thread-local invariant
    `Jinv : Nat → Thread I → Prop` (per thread id, on the whole thread);
    `ThreadReach`, `promisePure_of_relWritesReach`: at its strongest instance,
    thread-local reachability;
  - `theorem1IIPure_of_relWritesT`: Theorem 1′ with the thread-local form.
- `promisePure_of_cells'`, `promisePure_tso'`: the existing
  `promisePure_of_cells` and `promisePure_tso` re-derived through it.
- `promisePure_of_pureNonRel`, `promisePure_of_allPure`: the trivial
  instances: release predicates pure at every location the program writes
  non-release (no program facts beyond which locations those are), or pure
  everywhere (no program facts at all). Every program gets Theorem 1′, with
  weaker predicates, never none.
- `Theorem1IIRelWrites`, `theorem1IIPure_of_relWrites`: Theorem 1′
  (`Theorem1IIPure`) with `PromisePure` replaced by the per-instruction
  condition.
-/
import Kraken.Promising.SLR.Theorem1Final
import Kraken.Promising.SLR.TsoPromisePure

namespace Kraken.Promising.EvTree

/-! ## Release writes in an event tree -/

/-- Every store and every RMW write of the tree whose effective kind is not a
release (`A.storeKind … ≠ .rel`) satisfies `Q`. Release writes are
unconstrained. -/
def RelWrites {σ : Type} (A : Arch) (Q : Loc → Val → Prop) : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).RelWrites A Q
  | .load _ _ _ ret => ∀ v, (ret v).RelWrites A Q
  | .store k _ l v ret => (A.storeKind k ≠ .rel → Q l v) ∧ ∀ b, (ret b).RelWrites A Q
  | .rmw k _ l op ret =>
    (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q l new) ∧
      ∀ v, (ret v).RelWrites A Q
  | .fence _ ret => ∀ u, (ret u).RelWrites A Q

/-- The tree has a non-release write (store or RMW write) of `v` to `l`. -/
def NonRelWrite {σ : Type} (A : Arch) (l : Loc) (v : Val) : EvTree σ → Prop
  | .done _ => False
  | .fault _ => False
  | .choose _ k => ∃ i, (k i).NonRelWrite A l v
  | .load _ _ _ ret => ∃ x, (ret x).NonRelWrite A l v
  | .store k _ l' v' ret => (A.storeKind k ≠ .rel ∧ l' = l ∧ v' = v) ∨ ∃ b, (ret b).NonRelWrite A l v
  | .rmw k _ l' op ret =>
    (A.storeKind (A.rmwKind k).storeKind ≠ .rel ∧ l' = l ∧ ∃ old, op old = some v) ∨
      ∃ x, (ret x).NonRelWrite A l v
  | .fence _ ret => ∃ u, (ret u).NonRelWrite A l v

variable {σ : Type} {A : Arch}

/-- `RelWrites A Q` is "`Q` holds at every non-release write". -/
theorem relWrites_iff {Q : Loc → Val → Prop} (tree : EvTree σ) :
    tree.RelWrites A Q ↔ ∀ l v, tree.NonRelWrite A l v → Q l v := by
  induction tree with
  | done _ => simp [RelWrites, NonRelWrite]
  | fault _ => simp [RelWrites, NonRelWrite]
  | choose _ k ih =>
    simp only [RelWrites, NonRelWrite, ih]
    exact ⟨fun h l v ⟨i, hi⟩ => h i l v hi, fun h i l v hi => h l v ⟨i, hi⟩⟩
  | load _ _ _ ret ih =>
    simp only [RelWrites, NonRelWrite, ih]
    exact ⟨fun h l v ⟨x, hx⟩ => h x l v hx, fun h x l v hx => h l v ⟨x, hx⟩⟩
  | fence _ ret ih =>
    simp only [RelWrites, NonRelWrite, ih]
    exact ⟨fun h l v ⟨x, hx⟩ => h x l v hx, fun h x l v hx => h l v ⟨x, hx⟩⟩
  | store k _ l' v' ret ih =>
    simp only [RelWrites, NonRelWrite, ih]
    constructor
    · rintro ⟨h1, h2⟩ l v (⟨hk, rfl, rfl⟩ | ⟨b, hb⟩)
      · exact h1 hk
      · exact h2 b l v hb
    · intro h
      exact ⟨fun hk => h l' v' (.inl ⟨hk, rfl, rfl⟩), fun b l v hb => h l v (.inr ⟨b, hb⟩)⟩
  | rmw k _ l' op ret ih =>
    simp only [RelWrites, NonRelWrite, ih]
    constructor
    · rintro ⟨h1, h2⟩ l v (⟨hk, rfl, old, hold⟩ | ⟨x, hx⟩)
      · exact h1 hk old v hold
      · exact h2 x l v hx
    · intro h
      exact ⟨fun hk old new hnew => h l' new (.inl ⟨hk, rfl, old, hnew⟩), fun x l v hx => h l v (.inr ⟨x, hx⟩)⟩

theorem RelWrites.mono {Q Q' : Loc → Val → Prop} (hQ : ∀ l v, Q l v → Q' l v) {tree : EvTree σ}
    (h : tree.RelWrites A Q) : tree.RelWrites A Q' :=
  (relWrites_iff tree).mpr fun l v hw => hQ l v ((relWrites_iff tree).mp h l v hw)

/-- A tree all of whose writes satisfy `Q` (`EvTree.Writes`) satisfies it at
its non-release writes. -/
theorem Writes.relWrites {Q : Loc → Val → Prop} :
    ∀ {tree : EvTree σ}, tree.Writes Q → tree.RelWrites A Q
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => Writes.relWrites (h i)
  | .load _ _ _ _, h => fun v => Writes.relWrites (h v)
  | .fence _ _, h => fun u => Writes.relWrites (h u)
  | .store _ _ _ _ _, h => ⟨fun _ => h.1, fun b => Writes.relWrites (h.2 b)⟩
  | .rmw _ _ _ _ _, h => ⟨fun _ => h.1, fun v => Writes.relWrites (h.2 v)⟩

/-- Under an architecture whose non-`.nt` stores are releases (`Arch.tso`),
an NT-free tree has no non-release write. -/
theorem NoNT.relWrites (hA : A.RelStores) {Q : Loc → Val → Prop} :
    ∀ {tree : EvTree σ}, tree.NoNT A → tree.RelWrites A Q
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => NoNT.relWrites hA (h i)
  | .load _ _ _ _, h => fun v => NoNT.relWrites hA (h v)
  | .fence _ _, h => fun _ => NoNT.relWrites hA h
  | .store _ _ _ _ _, h => ⟨fun hk => absurd (hA _ h.1) hk, fun b => NoNT.relWrites hA (h.2 b)⟩
  | .rmw _ _ _ _ _, h => ⟨fun hk => absurd (hA _ h.1) hk, fun v => NoNT.relWrites hA (h.2 v)⟩

/-- A single release store has no non-release write. -/
theorem relWrites_relStore {Q : Loc → Val → Prop} {k : StoreKind} {l : Loc} {v : Val} {s : σ}
    (hk : A.storeKind k = .rel) : (EvTree.store k false l v fun _ => .done s).RelWrites A Q :=
  ⟨fun h => absurd hk h, fun _ => trivial⟩

end Kraken.Promising.EvTree

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

/-! ## A fulfilment of an impure promise is a release fulfilment -/

private theorem mem_of_ite_nil' {α : Type} {p : Prop} [Decidable p] {x : α} {l : List α}
    (h : x ∈ (if p then [] else l)) : x ∈ l := by
  split at h
  · simp at h
  · exact h

/-- **A run that removes a promise whose message fails `Q`, of a tree whose
non-release writes satisfy `Q`, is a live release fulfilment**: the write
that removes the promise writes its message (`writeSuccs_unpromise`), so it
is a release write; a run that ends with no dead promise has none right after
that write (`Ctx.NoDead.back`). Stores and RMW writes alike, anywhere in the
tree. -/
theorem runTree_relFulfilsLive_of_relWrites (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type}
    {Q : Loc → Val → Prop} {ts : Time} {w : Msg} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.RelWrites A Q → ts ∈ c.prom → ts ∉ c'.prom → c.mem.get? ts = some w → ¬ Q w.loc w.val →
      c'.NoDead → EvTree.RelFulfilsLive A tid iv ts c tree
  | .done _, c, s, c', h, _, hin, hout, _, _, _ => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd hin hout
  | .fault _, c, s, c', h, _, _, _, _, _, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hQ, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ⟨i, runTree_relFulfilsLive_of_relWrites A tid iv (k i) c s c' h (hQ i) hin hout hw hb hnd⟩
  | .load _ _ _ ret, c, s, c', h, hQ, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    exact ⟨x, hx, runTree_relFulfilsLive_of_relWrites A tid iv _ _ s c' h (hQ _) (hp ▸ hin) hout (hm ▸ hw) hb hnd⟩
  | .store k xcl l v ret, c, s, c', h, hQ, hin, hout, hw, hb, hnd => by
    rw [runTree, List.mem_append] at h
    rcases h with h | h
    · have h := mem_of_ite_nil' h
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      by_cases hk : ts ∈ c''.prom
      · exact .inl ⟨c'', hc'', .inr (runTree_relFulfilsLive_of_relWrites A tid iv _ c'' s c' h (hQ.2 true) hk
          hout (writeSuccs_get? hc'' hw) hb hnd)⟩
      · obtain ⟨w', hw', hl, hv⟩ := writeSuccs_unpromise hc'' hin hk
        rw [hw] at hw'
        cases hw'
        have hrel : A.storeKind k = .rel := Classical.byContradiction fun hne => hb (hl ▸ hv ▸ hQ.1 hne)
        exact .inl ⟨c'', hc'', .inl ⟨⟨hrel, hin, hk⟩,
          hnd.back (runTree_dord A tid iv _ _ s c' h) (runTree_word A tid iv _ _ s c' h)⟩⟩
    · split at h
      · exact .inr (runTree_relFulfilsLive_of_relWrites A tid iv _ _ s c' h (hQ.2 false) hin hout hw hb hnd)
      · simp at h
  | .fence k ret, c, s, c', h, hQ, hin, hout, hw, hb, hnd => by
    simp only [runTree] at h
    obtain ⟨hm, hp⟩ := fenceStep_mem_prom c k
    exact runTree_relFulfilsLive_of_relWrites A tid iv (ret ()) _ s c' h (hQ ()) (hp ▸ hin) hout (hm ▸ hw) hb hnd
  | .rmw k noRet l op ret, c, s, c', h, hQ, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    have hfp : ∀ c0 : Ctx, (if A.rmwFence then fenceStep c0 .sy else c0).mem = c0.mem ∧
        (if A.rmwFence then fenceStep c0 .sy else c0).prom = c0.prom := fun c0 => by
      split
      · exact fenceStep_mem_prom c0 .sy
      · exact ⟨rfl, rfl⟩
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    rw [(hfp c).1] at hm
    rw [(hfp c).2] at hp
    have hin' : ts ∈ x.2.2.prom := by rw [hp]; exact hin
    have hw' : x.2.2.mem.get? ts = some w := by rw [hm]; exact hw
    refine ⟨x, hx, ?_⟩
    split at h
    · exact .inl (runTree_relFulfilsLive_of_relWrites A tid iv _ _ s c' h (hQ.2 _) (by rw [(hfp _).2]; exact hin')
        hout (by rw [(hfp _).1]; exact hw') hb hnd)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      refine .inr ⟨new, hnew, c'', hc'', ?_⟩
      by_cases hk : ts ∈ c''.prom
      · refine .inr (runTree_relFulfilsLive_of_relWrites A tid iv _ _ s c' h (hQ.2 _) ?_ hout ?_ hb hnd)
        · rw [(hfp _).2, rmwPost_prom]
          exact hk
        · rw [(hfp _).1]
          unfold rmwPost
          split <;> exact writeSuccs_get? hc'' hw'
      · obtain ⟨w', hw'', hl, hv⟩ := writeSuccs_unpromise hc'' hin' hk
        rw [hw'] at hw''
        cases hw''
        have hrel : A.storeKind (A.rmwKind k).storeKind = .rel :=
          Classical.byContradiction fun hne => hb (hl ▸ hv ▸ hQ.1 hne _ _ hnew)
        refine .inl ⟨⟨hrel, hin', hk⟩, hnd.back ?_ ?_⟩
        · exact ((Ctx.DOrd.rmwPost A c'' k noRet l).trans (Ctx.DOrd.fenceOpt _ A.rmwFence .sy)).trans
            (runTree_dord A tid iv _ _ s c' h)
        · exact ((Ctx.WOrd.rmwPost A c'' k noRet l).trans (Ctx.WOrd.fenceOpt _ A.rmwFence .sy)).trans
            (runTree_word A tid iv _ _ s c' h)

/-- **One instruction**: a step of thread `tid` whose tree's non-release
writes satisfy `Q`, removing the outstanding promise `ts` whose message fails
`Q` and leaving no promise dead, is a live release fulfilment of `ts`. -/
theorem stepOne_relFulfilsLive_of_relWrites (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Q : Loc → Val → Prop} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree) (hQ : tree.RelWrites A Q) {ts : Time} (hin : ts ∈ t.prom)
    (hout : ts ∉ o.thread.prom) {w : Msg} (hw : mem.get? ts = some w) (hb : ¬ Q w.loc w.val)
    (hlive : o.thread.hasDeadPromise o.mem = false) : t.RelFulfilsLive A tid ts mem := by
  refine ⟨tree, hex, ?_⟩
  unfold stepOne at hstep
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
    rw [(finishInstr_relKey hth).1] at hout
    exact runTree_relFulfilsLive_of_relWrites A tid _ tree _ st c' hr hQ hin hout hw hb
      (Ctx.noDead_of_finish hth hlive)

/-! ## `PromisePure` from the cell condition at held states

The proof of `PromisePure` from a cell condition asks the condition at one
state only: the state of the promising thread `j` at the step `f` that
removes the promise, which `j` holds on `(J, f]`. `FulfilCell` asks it
exactly there; `promisePure_of_relWritesT` asks it at every thread state
reachable for its thread (a per-thread invariant `Jinv tid t`, which may
depend on the thread id and on the whole thread: views, promises), and
`promisePure_of_relWrites` at every reachable `I.State`. -/

variable {A : Arch} {fuel : Nat} in
/-- The promise step of `PromisePure`: thread `j` at real step `J` promises
`pw` (certified), at timestamp `(π.cfg J).mem.last + 1`. -/
def PromStep (π : Path A fuel I) (J j : Nat) (t : Thread I) (pw : Msg × View) : Prop :=
  (π.cfg J).threads[j]? = some t ∧ CertWrite A j t (π.cfg J).mem pw ∧
    π.cfg (J + 1) = (π.cfg J).withThread j { t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }
      ((π.cfg J).mem.append { pw.1 with tid := j }).1

variable {A : Arch} {fuel : Nat} in
/-- Thread `j` holds `ts` at every step of `(J, f]`. -/
def HeldOn (π : Path A fuel I) (J f j : Nat) (ts : Time) : Prop :=
  ∀ q, J < q → q ≤ f → ∃ tq, (π.cfg q).threads[j]? = some tq ∧ ts ∈ tq.prom

/-- **The cell condition at held states**: on a path to a final
configuration, while thread `j` holds a promise it made at step `J`, its next
instruction's non-release writes are pure for `rel`. -/
def FulfilCell (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val))
    (rel : Loc → Pred) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J f j t pw, J < f → f < π.len → PromStep π J j t pw → HeldOn π J f j ((π.cfg J).mem.last + 1) →
    ∀ tf tree, (π.cfg f).threads[j]? = some tf → I.exec tf.st = some tree →
      tree.RelWrites A fun l v => Pred.Pure (rel l) v

/-- **`FulfilCell` gives `PromisePure`**: on a path to a final configuration
a promise of an impure value is removed by an instruction of its thread
(`Path.first_removal`, `removal_is_instr`), at a held state, that writes the
promised message, hence with a release write, leaving no promise dead (the
path is live): the promise is `RelFulfilled`. -/
theorem promisePure_of_fulfilCell [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (hcell : FulfilCell A fuel states initMem rel) :
    PromisePure A fuel states initMem rel := by
  intro π h0 hfin J hJl j t pw ht hcw hstep hnot
  apply Classical.byContradiction
  intro hpure
  apply hnot
  have hh : HoldsProm (π.cfg (J + 1)) j ((π.cfg J).mem.last + 1) := by
    refine ⟨{ t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }, ?_,
      List.mem_append_right _ (List.mem_singleton_self _)⟩
    rw [hstep, Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
    simp only [↓reduceIte]
  obtain ⟨f, hJf, hf, hheld, hgone⟩ := π.first_removal hfin hJl hh
  obtain ⟨tf, outs, o, htf, hstepf, ho, htf', hmf, hin, hout⟩ :=
    removal_is_instr (succs_cases (π.step f hf)) (hheld f hJf (Nat.le_refl f)) hgone
  -- the promised message stays at its timestamp
  have hwJ : (π.cfg (J + 1)).mem.get? ((π.cfg J).mem.last + 1) = some { pw.1 with tid := j } := by
    rw [hstep]; exact Memory.get?_append_last _ _
  have hwf : (π.cfg f).mem.get? ((π.cfg J).mem.last + 1) = some { pw.1 with tid := j } := by
    rw [(π.mem_prefix hJf (by omega)).get? (by
      rw [hstep]; simp only [Config.withThread, Memory.last_append]; exact Nat.le_refl _)]
    exact hwJ
  have hlive : o.thread.hasDeadPromise o.mem = false := by
    rw [← hmf]
    exact liveWfProm A fuel states initMem _ (by rw [← h0]; exact π.reachable (f + 1) hf) (π.live hfin (f + 1) hf)
      j o.thread htf'
  cases hex : I.exec tf.st with
  | none => unfold stepOne at hstepf; rw [hex] at hstepf; cases hstepf
  | some tree =>
    have hc := hcell π h0 hfin J f j t pw hJf hf ⟨ht, hcw, hstep⟩ (fun q hq1 hq2 => hheld q hq1 hq2) tf tree htf hex
    exact ⟨f, hJf, hf, fun q hq1 hq2 => hheld q hq1 hq2, tf, o.thread, htf,
      stepOne_relFulfilsLive_of_relWrites A hstepf ho hex hc hin hout hwf hpure hlive,
      htf', hout⟩

/-- **(O5) `PromisePure` from release writes, thread-local invariant.**
Every thread `t` reachable at position `tid` from the initial configuration
satisfies `Jinv tid t` (a per-thread invariant: it may depend on the thread
id, e.g. a different program per thread, and on the whole thread, views and
promises included), and under it every non-release write of `t`'s next
instruction writes a value pure for its location's release predicate. The
cell condition is used only at the fulfilling state (`FulfilCell`). -/
theorem promisePure_of_relWritesT [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Jinv : Nat → Thread I → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t)
    (hcell : ∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWrites A fun l v => Pred.Pure (rel l) v) :
    PromisePure A fuel states initMem rel :=
  promisePure_of_fulfilCell fun π h0 _ _ f j _ _ _ hf _ _ tf tree htf hex =>
    hcell j tf tree (hJ _ (h0 ▸ π.reachable f (by omega)) j tf htf) hex

/-- The strongest thread-local invariant: `t` is reachable at position `tid`. -/
def ThreadReach (A : Arch) (fuel : Nat) (states : List I.State) (initMem : List (Loc × Val))
    (tid : Nat) (t : Thread I) : Prop :=
  ∃ c, Reachable A fuel (Config.init states initMem) c ∧ c.threads[tid]? = some t

/-- `promisePure_of_relWritesT` at the strongest invariant (thread-local
reachability): the cell condition only at reachable threads. -/
theorem promisePure_of_relWritesReach [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred}
    (hcell : ∀ tid t tree, ThreadReach A fuel states initMem tid t → I.exec t.st = some tree →
      tree.RelWrites A fun l v => Pred.Pure (rel l) v) :
    PromisePure A fuel states initMem rel :=
  promisePure_of_relWritesT (ThreadReach A fuel states initMem) (fun c hc _ _ ht => ⟨c, hc, ht⟩) hcell

/-! ## `PromisePure` from release writes -/

/-- **(O5) `PromisePure` from release writes.** Every thread state reachable
from the initial configuration satisfies `Jinv`, and at such a state every
non-release write of the next instruction (store or RMW write) writes a value
that is pure for its location's release predicate. Then on a path to a final
configuration a promise of an impure value is removed by an instruction of its
thread (`Path.first_removal`, `removal_is_instr`) that writes the promised
message, hence with a release write, leaving no promise dead (the path is
live): the promise is `RelFulfilled`. (A corollary of
`promisePure_of_relWritesT`.) -/
theorem promisePure_of_relWrites [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Jinv : I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree → tree.RelWrites A fun l v => Pred.Pure (rel l) v) :
    PromisePure A fuel states initMem rel :=
  promisePure_of_relWritesT (fun _ t => Jinv t.st) hJ fun _ t tree h hex => hcell t.st tree h hex

/-! ## The existing instances, through `promisePure_of_relWrites` -/

/-- `promisePure_of_cells` re-derived: a cell writing no `Bad` message
or a single release store has no impure non-release write. -/
theorem promisePure_of_cells' [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Bad : Loc → Val → Prop)
    (hrel : ∀ l v, ¬ Bad l v → Pred.Pure (rel l) v) (Jinv : I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I), c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree →
      tree.Writes (fun l v => ¬ Bad l v) ∨
        ∃ k l v s, A.storeKind k = .rel ∧ tree = .store k false l v (fun _ => .done s)) :
    PromisePure A fuel states initMem rel :=
  promisePure_of_relWrites Jinv hJ fun st tree hst hex => by
    rcases hcell st tree hst hex with hW | ⟨k, l, v, s, hk, rfl⟩
    · exact (EvTree.Writes.relWrites hW).mono hrel
    · exact EvTree.relWrites_relStore hk

/-- `promisePure_tso` re-derived: under `Arch.tso` an NT-free program
has no non-release write at all. -/
theorem promisePure_tso' [I.LawfulState] {fuel : Nat} {P : I.State → Prop} (hP : I.NoNTInv Arch.tso P)
    {states : List I.State} {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, P s) (rel : Loc → Pred) :
    PromisePure Arch.tso fuel states initMem rel :=
  promisePure_of_relWrites P
    (fun _ hc tid t ht => (hc.noNTInv hP (Config.noNTInvAt_init hs) tid t ht).1)
    fun st tree hst hex => EvTree.NoNT.relWrites tso_storeKind_rel (hP.noNT st hst tree hex)

/-! ## The trivial instances: weaker predicates, never none -/

/-- The location `l` is written non-release by some instruction of some
thread state reachable from the initial configuration. -/
def NonRelWritten (A : Arch) (fuel : Nat) (states : List I.State) (initMem : List (Loc × Val)) (l : Loc) : Prop :=
  ∃ c, Reachable A fuel (Config.init states initMem) c ∧ ∃ (tid : Nat) (t : Thread I) (tree : EvTree I.State) (v : Val),
    c.threads[tid]? = some t ∧ I.exec t.st = some tree ∧ tree.NonRelWrite A l v

/-- **Trivial instance**: release predicates that are pure (at every value)
at every location the program writes non-release give `PromisePure`, with no
other program facts. Any program thus satisfies (O5), and so Theorem 1′
(`theorem1IIPure_of_relWrites`), for such predicates: weaker predicates,
never no theorem. -/
theorem promisePure_of_pureNonRel [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred}
    (hpure : ∀ l, NonRelWritten A fuel states initMem l → ∀ v, Pred.Pure (rel l) v) :
    PromisePure A fuel states initMem rel :=
  promisePure_of_relWrites
    (fun st => ∃ c, Reachable A fuel (Config.init states initMem) c ∧ ∃ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t ∧ t.st = st)
    (fun c hc tid t ht => ⟨c, hc, tid, t, ht, rfl⟩)
    fun _ tree ⟨c, hc, tid, t, ht, hst⟩ hex =>
      (EvTree.relWrites_iff tree).mpr fun l v hw =>
        hpure l ⟨c, hc, tid, t, tree, v, ht, hst ▸ hex, hw⟩ v

/-- **Trivial instance, no program facts**: release predicates pure
everywhere give `PromisePure` for every program. -/
theorem promisePure_of_allPure [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (hpure : ∀ l v, Pred.Pure (rel l) v) :
    PromisePure A fuel states initMem rel :=
  promisePure_of_pureNonRel fun l _ v => hpure l v

/-! ## Theorem 1′ with the per-instruction condition -/

/-- **Theorem 1′ for the SLR-adapted model, release-write form**:
`Theorem1IIPure` with the path property `PromisePure` replaced by the
per-instruction condition of `promisePure_of_relWrites`: at every reachable
thread state (an invariant `Jinv`), the next instruction's non-release writes
write values pure for the initial ghost's release predicates. -/
def Theorem1IIRelWrites (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    ∀ (Jinv : I.State → Prop),
    (∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv t.st) →
    (∀ st tree, Jinv st → I.exec st = some tree → tree.RelWrites A fun l v => Pred.Pure (g.rel l) v) →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', (VirtualRel.ii A).rel c v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- **Theorem 1′, release-write form** (`theorem1IIPure` through
`promisePure_of_relWrites`). -/
theorem theorem1IIPure_of_relWrites [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIRelWrites (I := I) A fuel := by
  intro B states initMem rF g hH E hnp Jinv hJ hcell hsafe c hc hlive
  exact theorem1IIPure A fuel B states initMem rF g hH E hnp (promisePure_of_relWrites Jinv hJ hcell) hsafe c hc hlive

/-- **Theorem 1′, release-write form with a thread-local invariant**
(`theorem1IIPure` through `promisePure_of_relWritesT`): as
`theorem1IIPure_of_relWrites`, with `Jinv : Nat → Thread I → Prop` holding of
every thread reachable at its position. -/
theorem theorem1IIPure_of_relWritesT [I.LawfulState] (A : Arch) (fuel : Nat)
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (E : Erase rF g (fun _ => False) (Config.init states initMem)) (hnp : ∀ ts, ts ∉ g.pend)
    (Jinv : Nat → Thread I → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t)
    (hcell : ∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWrites A fun l v => Pred.Pure (g.rel l) v)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g)
    (c : Config I) (hc : Reachable A fuel (Config.init states initMem) c) (hlive : c.Live A fuel) :
    ∃ v rF' g', (VirtualRel.ii A).rel c v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' :=
  theorem1IIPure A fuel B states initMem rF g hH E hnp (promisePure_of_relWritesT Jinv hJ hcell) hsafe c hc hlive

/-- **Program-agnostic adequacy from `theorem1IIPure_of_relWrites`**: as
`final_of_theorem1Pure`, with `PromisePure` replaced by the per-instruction
condition of `Theorem1IIRelWrites` (a reachable-state invariant `Jinv` under
which every instruction's non-release writes are pure for the initial
ghost). `Mp.mp_armv8` is an instance. -/
theorem final_of_relWrites [I.LawfulState] (A : Arch) (fuel : Nat) {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop}
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (Jinv : I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree → tree.RelWrites A fun l v => Pred.Pure (g₀.rel l) v)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_virtual hc hf
    (theorem1IIPure_of_relWrites A fuel B states initMem rF g₀ hH hE hpend Jinv hJ hcell hsafe c hc ⟨c, .refl c, hf⟩)
    hfin

end Kraken.Promising.SLR

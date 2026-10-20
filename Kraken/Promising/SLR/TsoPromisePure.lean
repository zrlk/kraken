/-
(O5) `PromisePure` from "every fulfilment is a release fulfilment": the TSO story of Theorem 1′'s promise cases.

`PromisePure` (`SLR/Theorem1Proof.lean`) asks, on every real path to a final
configuration, that a promise which is not `RelFulfilled` (fulfilled later by
a release store of its thread) write a value that is pure for its location's
release predicate. On a path to a final configuration every promise is
fulfilled; promises are removed only by an instruction step of their own
thread. If every such removal is a release fulfilment (`FulfilIsRel`), then
every promise is `RelFulfilled`: the premise `¬ RelFulfilled` of
`PromisePure` never holds, and `PromisePure` holds for **every** choice of
release predicates (`promisePure_of_fulfilIsRel`).

Under `Arch.tso` every store kind except `.nt` is a release (`plain ↦ rel`),
and every RMW writes with a release kind, so for programs without
non-temporal stores (`ISA.NoNTInv Arch.tso P`, `NTFreeTso.lean`) every
fulfilment is a release fulfilment. All promises then go through case (d1)
of Theorem 1′'s induction (prepay, option (B)); case (d2) never arises. For
the x64 spinlock this means: the counter store `movl %ecx,(%rsi)` and the
unlock `movl $0,(%rdi)` are both release stores, any promise of either is
prepaid, and the counter's release predicate plays no role in (O5) (it can
stay the trivially pure one).

## Contents

- `FulfilIsRel A P`: at a `P` state, an instruction step that removes an
  outstanding promise of the thread can fulfil it with a release store
  (`Thread.RelFulfils`).
- `Path.first_removal`: on a path to a final configuration, a promise made at
  step `J` is removed at a first step `f`, by an instruction step of its
  thread.
- `promisePure_of_fulfilIsRel`: `PromisePure` for every `rel`.
- `Arch.RelStores`, `tso_storeKind_rel`: every non-`.nt` store kind is a
  release under `Arch.tso`.
- `runTree_relFulfils`: under such an architecture a run of an NT-free tree
  that removes a promise is `EvTree.RelFulfils` (stores and RMW writes; the
  run-level generalisation of `relFulfils_of_store`, which covers a
  single store); `fulfilIsRel_of_noNT`.
- `promisePure_tso`: **(O5) holds under `Arch.tso` for every NT-free program
  and every choice of release predicates.**

`HoldsProm`, `removal_is_instr` and `Path.first_removal` restate, for this
generic setting, the path argument inside `promisePure_of_cells`
(`SLR/PromiseFulfil.lean`, whose `first_exit` they reuse); that theorem
handles release fulfilments by a single store only, hence this file.
-/
import Kraken.Promising.SLR.PromiseFulfil
import Kraken.Promising.NTFreeTso

namespace Kraken.Promising.SLR

variable {I : ISA}

/-- **Every fulfilment is a release fulfilment** (at `P` states): an
instruction step of thread `j` that removes its outstanding promise `ts`,
leaving no promise dead, can fulfil `ts` with a release store that leaves no
promise dead (`Thread.RelFulfilsLive`). -/
def FulfilIsRel (I : ISA) (A : Arch) (P : I.State → Prop) : Prop :=
  ∀ (t : Thread I) (j : Nat) (mem : Memory) (outs : List (Except String (Outcome I))) (o : Outcome I)
    (ts : Time), P t.st → stepOne A t j mem = some outs → .ok o ∈ outs → ts ∈ t.prom →
    ts ∉ o.thread.prom → o.thread.hasDeadPromise o.mem = false → t.RelFulfilsLive A j ts mem

/-- Thread `j` holds the outstanding promise `ts` at configuration `c`. -/
def HoldsProm (c : Config I) (j : Nat) (ts : Time) : Prop :=
  ∃ t, c.threads[j]? = some t ∧ ts ∈ t.prom

/-- A machine step that removes `ts` from thread `j`'s promises is an
instruction step of `j`. -/
theorem removal_is_instr {A : Arch} {c c' : Config I}
    (hs : SuccKind A c c') {j : Nat} {ts : Time} (hh : HoldsProm c j ts) (hn : ¬ HoldsProm c' j ts) :
    ∃ t outs o, c.threads[j]? = some t ∧ stepOne A t j c.mem = some outs ∧ .ok o ∈ outs ∧
      c'.threads[j]? = some o.thread ∧ c'.mem = o.mem ∧ ts ∈ t.prom ∧ ts ∉ o.thread.prom := by
  obtain ⟨t, ht, hts⟩ := hh
  cases hs with
  | @instr i ti outs o hi hstep ho =>
    have hget := Config.withThread_get? c (i := j) o.thread o.mem (lt_size_of_get? hi)
    by_cases hij : i = j
    · subst hij
      rw [hi] at ht
      cases ht
      simp only [↓reduceIte] at hget
      exact ⟨t, outs, o, hi, hstep, ho, hget, rfl, hts, fun h => hn ⟨_, hget, h⟩⟩
    · simp only [hij, ↓reduceIte] at hget
      exact absurd ⟨t, hget.trans ht, hts⟩ hn
  | @promise i ti p hi _ =>
    have hget := Config.withThread_get? c (i := j)
      { ti with prom := ti.prom ++ [(c.mem.append { p.1 with tid := i }).2] }
      (c.mem.append { p.1 with tid := i }).1 (lt_size_of_get? hi)
    by_cases hij : i = j
    · subst hij
      rw [hi] at ht
      cases ht
      simp only [↓reduceIte] at hget
      exact absurd ⟨_, hget, List.mem_append_left _ hts⟩ hn
    · simp only [hij, ↓reduceIte] at hget
      exact absurd ⟨t, hget.trans ht, hts⟩ hn

/-- **The first removal of a promise.** On a path to a final configuration,
a promise `ts` that thread `j` holds at step `J + 1` is removed at a first
step `f ≥ J + 1`: held at every step in `(J, f]`, gone at `f + 1`. -/
theorem Path.first_removal {A : Arch} [I.LawfulState] {fuel : Nat} (π : Path A fuel I)
    (hfin : (π.cfg π.len).final = true) {J : Nat} (hJ : J < π.len) {j : Nat} {ts : Time}
    (hh : HoldsProm (π.cfg (J + 1)) j ts) :
    ∃ f, J < f ∧ f < π.len ∧ (∀ q, J < q → q ≤ f → HoldsProm (π.cfg q) j ts) ∧
      ¬ HoldsProm (π.cfg (f + 1)) j ts := by
  have hend : ¬ HoldsProm (π.cfg π.len) j ts := by
    rintro ⟨t, ht, hts⟩
    rw [Config.final_prom hfin ht] at hts
    cases hts
  obtain ⟨f, h1, h2, h3, h4⟩ := first_exit (p := fun q => HoldsProm (π.cfg q) j ts) hh π.len (by omega) hend
  exact ⟨f, by omega, h2, fun q hq1 hq2 => h3 q (by omega) hq2, h4⟩

/-- **(O5) from release fulfilments.** If `P` is an invariant of the
program (`ISA.NoNTInv A P`, with all initial states in `P`) at whose states
every fulfilment is a release fulfilment (`FulfilIsRel A P`), then
`PromisePure` holds for every choice of release predicates: every promise on
a path to a final configuration is `RelFulfilled`. -/
theorem promisePure_of_fulfilIsRel {A : Arch} [I.LawfulState] {fuel : Nat} {P : I.State → Prop}
    (hP : I.NoNTInv A P) (hF : FulfilIsRel I A P) {states : List I.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, P s) (rel : Loc → Pred) : PromisePure A fuel states initMem rel := by
  intro π h0 hfin J hJ j t pw ht _ hstep hnot
  exfalso
  apply hnot
  -- the promise is held right after step `J`
  have hh : HoldsProm (π.cfg (J + 1)) j ((π.cfg J).mem.last + 1) := by
    refine ⟨{ t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] }, ?_,
      List.mem_append_right _ (List.mem_singleton_self _)⟩
    rw [hstep, Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
    simp only [↓reduceIte]
  obtain ⟨f, hJf, hf, hheld, hgone⟩ := π.first_removal hfin hJ hh
  obtain ⟨tf, outs, o, htf, hstepf, ho, htf', hmf, hin, hout⟩ :=
    removal_is_instr (succs_cases (π.step f hf)) (hheld f hJf (Nat.le_refl f)) hgone
  have hPf : P tf.st := by
    have hinv := (h0 ▸ π.reachable f (by omega)).noNTInv hP (Config.noNTInvAt_init hs)
    exact (hinv j tf htf).1
  refine ⟨f, hJf, hf, fun q hq1 hq2 => hheld q hq1 hq2, tf, o.thread, htf, ?_, htf', hout⟩
  have hlive : o.thread.hasDeadPromise o.mem = false := by
    rw [← hmf]
    exact liveWfProm A fuel states initMem _ (by rw [← h0]; exact π.reachable (f + 1) hf) (π.live hfin (f + 1) hf)
      j o.thread htf'
  exact hF tf j _ outs o _ hPf hstepf ho hin hout hlive

/-! ## Under `Arch.tso` every fulfilment is a release fulfilment -/

/-- Every store kind but `.nt` is a release (`A.storeKind`); true of
`Arch.tso` (`tso_storeKind_rel`), false of `Arch.armv8` (plain stores stay
plain). -/
def _root_.Kraken.Promising.Arch.RelStores (A : Arch) : Prop := ∀ k, A.storeKind k ≠ .nt → A.storeKind k = .rel

theorem tso_storeKind_rel : Arch.tso.RelStores := by
  intro k hk
  cases k <;> simp_all [Arch.storeKind, Arch.tso]

private theorem mem_of_ite_nil {α : Type} {p : Prop} [Decidable p] {x : α} {l : List α}
    (h : x ∈ (if p then [] else l)) : x ∈ l := by
  split at h
  · simp at h
  · exact h

theorem rmwPost_prom (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwPost A k noRet l c).prom = c.prom := by
  unfold rmwPost
  split <;> rfl

/-- **A run that removes a promise is a release fulfilment**, for a tree
without non-temporal stores under an architecture whose other stores are
all releases (`Arch.RelStores`): stores and RMW writes alike. The RMW
counterpart of `relFulfils_of_store`, at the level of `runTree`. A run that
ends with no dead promise (`Ctx.NoDead`) has none right after the fulfilling
write either (`Ctx.NoDead.back`), so the fulfilment is `RelFulfilsLive`. -/
theorem runTree_relFulfils (A : Arch) (hA : A.RelStores) (tid : Nat) (iv : InstrViews) {σ : Type}
    {ts : Time} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.NoNT A → ts ∈ c.prom → ts ∉ c'.prom → c'.NoDead → EvTree.RelFulfilsLive A tid iv ts c tree
  | .done _, c, s, c', h, _, hin, hout, _ => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd hin hout
  | .fault _, c, s, c', h, _, _, _, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hno, hin, hout, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ⟨i, runTree_relFulfils A hA tid iv (k i) c s c' h (hno i) hin hout hnd⟩
  | .load _ _ _ ret, c, s, c', h, hno, hin, hout, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨-, hp⟩ := readSuccs_memProm A iv hx
    exact ⟨x, hx, runTree_relFulfils A hA tid iv _ _ s c' h (hno _) (hp ▸ hin) hout hnd⟩
  | .store k xcl l v ret, c, s, c', h, hno, hin, hout, hnd => by
    rw [runTree, List.mem_append] at h
    rcases h with h | h
    · have h := mem_of_ite_nil h
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      by_cases hk : ts ∈ c''.prom
      · exact .inl ⟨c'', hc'', .inr (runTree_relFulfils A hA tid iv _ c'' s c' h (hno.2 true) hk hout hnd)⟩
      · exact .inl ⟨c'', hc'', .inl ⟨⟨hA k hno.1, hin, hk⟩,
          hnd.back (runTree_dord A tid iv _ _ s c' h) (runTree_word A tid iv _ _ s c' h)⟩⟩
    · split at h
      · exact .inr (runTree_relFulfils A hA tid iv _ _ s c' h (hno.2 false) hin hout hnd)
      · simp at h
  | .fence k ret, c, s, c', h, hno, hin, hout, hnd => by
    simp only [runTree] at h
    obtain ⟨-, hp⟩ := fenceStep_mem_prom c k
    exact runTree_relFulfils A hA tid iv (ret ()) _ s c' h hno (hp ▸ hin) hout hnd
  | .rmw k noRet l op ret, c, s, c', h, hno, hin, hout, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    have hfp : ∀ c0 : Ctx, (if A.rmwFence then fenceStep c0 .sy else c0).prom = c0.prom := fun c0 => by
      split
      · exact (fenceStep_mem_prom c0 .sy).2
      · rfl
    obtain ⟨-, hp⟩ := readSuccs_memProm A iv hx
    rw [hfp] at hp
    have hin' : ts ∈ x.2.2.prom := by rw [hp]; exact hin
    refine ⟨x, hx, ?_⟩
    split at h
    · exact .inl (runTree_relFulfils A hA tid iv _ _ s c' h (hno.2 _) (by rw [hfp]; exact hin') hout hnd)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      refine .inr ⟨new, hnew, c'', hc'', ?_⟩
      by_cases hk : ts ∈ c''.prom
      · refine .inr (runTree_relFulfils A hA tid iv _ _ s c' h (hno.2 _) ?_ hout hnd)
        rw [hfp, rmwPost_prom]
        exact hk
      · refine .inl ⟨⟨hA _ hno.1, hin', hk⟩, hnd.back ?_ ?_⟩
        · exact ((Ctx.DOrd.rmwPost A c'' k noRet l).trans (Ctx.DOrd.fenceOpt _ A.rmwFence .sy)).trans
            (runTree_dord A tid iv _ _ s c' h)
        · exact ((Ctx.WOrd.rmwPost A c'' k noRet l).trans (Ctx.WOrd.fenceOpt _ A.rmwFence .sy)).trans
            (runTree_word A tid iv _ _ s c' h)

/-- **Every fulfilment is a release fulfilment** for a program without
non-temporal stores, under an architecture whose other stores are all
releases (`Arch.tso`). -/
theorem fulfilIsRel_of_noNT {A : Arch} (hA : A.RelStores) {P : I.State → Prop} (hP : I.NoNTInv A P) :
    FulfilIsRel I A P := by
  intro t j mem outs o ts hPt hstep ho hin hout hlive
  unfold stepOne at hstep
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    refine ⟨tree, hex, ?_⟩
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
      exact runTree_relFulfils A hA j _ tree _ st c' hr (hP.noNT _ hPt tree hex) hin hout
        (Ctx.noDead_of_finish hth hlive)

/-- **(O5) under TSO for every NT-free program**: `PromisePure` holds for
every choice of release predicates. -/
theorem promisePure_tso [I.LawfulState] {fuel : Nat} {P : I.State → Prop} (hP : I.NoNTInv Arch.tso P)
    {states : List I.State} {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, P s) (rel : Loc → Pred) :
    PromisePure Arch.tso fuel states initMem rel :=
  promisePure_of_fulfilIsRel hP (fulfilIsRel_of_noNT tso_storeKind_rel hP) hs rel

end Kraken.Promising.SLR

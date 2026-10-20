/-
Purity under a global value invariant, ISA-neutral part: `PromisePure` from
purity judgments that hold only on the branches whose load answers satisfy a
global value invariant `G`.

The purity step of the Theorem 1′ chain (`promisePure_of_relWrites`) asks
every non-release write of every reachable instruction to write a pure value,
on every branch of the instruction's event tree. When every thread keeps
`MemInv G` (a value specification, `EvTree.AllInv G`), every load of a
reachable run answers a `G`-value, so the branches with other answers are
never run, and purity on the `G`-branches suffices.

- `EvTree.RelWritesV A Q G R`: `RelWrites A Q` on the branches whose load
  answers satisfy `G`, leaves in `R`; `EvTree.AllInv.and_relWritesV`;
  `EvTree.AllInv.of_all_writes` (leaves in `Q` and writes in `G` give
  `AllInv G Q`).
- `runTree_relFulfilsLive_of_relWritesV`,
  `stepOne_relFulfilsLive_of_relWritesV`: the run lemmas of
  `PromisePureGeneral` from a memory satisfying `MemInv G` and a tree
  satisfying `AllInv G` (the memory stays in `MemInv G` along the run).
- **`promisePure_of_relWritesV`**: `PromisePure` from per-thread
  invariants `J` whose trees satisfy `AllInv G J` and `RelWritesV`, `MemInv G`
  initially and `J` at the initial states.
- `Config.ntFree_of_configInv` (and `…K`, `…_initK` along `ReachableK`): Theorem 1′'s
  scope `NTFree` from the same kind of invariants, closed only on the
  `G`-branches, whose trees make no non-temporal store
  (`Config.ntFree_of_noNTInv` needs the invariant on every branch).
- **`Vals.final_of_chainVP`**: `final_of_chainV` with `NTFree` and
  `PromisePure` from one per-thread tree law (`AllInv G`, `NoNT`,
  `RelWritesV`).

The AArch64 layer is `Lower/KitValsPure.lean`, the x64 layer
`Lower/KitX64ValsPure.lean`. Machine: the executable Promising machine
(`Reachable A`).
-/
import Kraken.Promising.SLR.EnvG.ValsChain
import Kraken.Promising.SLR.PromisePureGeneral
import Kraken.Promising.SLR.TsoPromisePure

namespace Kraken.Promising.EvTree

open Kraken.Promising

/-- **Release writes on the `G`-branches**: every non-release write of the
tree satisfies `Q`, and every leaf `R`, on the branches whose load answers
satisfy `G` (an RMW's old value is unrestricted, as in `valsEnv`). -/
def RelWritesV {σ : Type} (A : Arch) (Q G : Loc → Val → Prop) (R : σ → Prop) : EvTree σ → Prop
  | .done s => R s
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).RelWritesV A Q G R
  | .load _ _ l ret => ∀ v, G l v → (ret v).RelWritesV A Q G R
  | .store k _ l v ret => (A.storeKind k ≠ .rel → Q l v) ∧ ∀ b, (ret b).RelWritesV A Q G R
  | .rmw k _ l op ret =>
    (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q l new) ∧
      ∀ v, (ret v).RelWritesV A Q G R
  | .fence _ ret => ∀ u, (ret u).RelWritesV A Q G R

/-- A value specification and a value-restricted purity judgment of one tree
combine into a value specification of both leaf predicates. -/
theorem AllInv.and_relWritesV {σ : Type} {A : Arch} {Q G : Loc → Val → Prop} {P R : σ → Prop} :
    ∀ {t : EvTree σ}, t.AllInv G P → t.RelWritesV A Q G R → t.AllInv G (fun s => P s ∧ R s)
  | .done _, h1, h2 => ⟨h1, h2⟩
  | .fault _, _, _ => trivial
  | .choose _ _, h1, h2 => fun i => and_relWritesV (h1 i) (h2 i)
  | .load _ _ _ _, h1, h2 => fun v hv => and_relWritesV (h1 v hv) (h2 v hv)
  | .store _ _ _ _ _, h1, h2 => ⟨h1.1, fun b hb => and_relWritesV (h1.2 b hb) (h2.2 b)⟩
  | .rmw _ _ _ _ _, h1, h2 => fun old hold => ⟨(h1 old hold).1, and_relWritesV (h1 old hold).2 (h2.2 old)⟩
  | .fence _ _, h1, h2 => fun u => and_relWritesV (h1 u) (h2 u)

/-- **A value specification from leaves and writes**: a tree whose leaves all
satisfy `Q` and whose writes all satisfy `G` is a value specification
`AllInv G Q` (whatever its loads answer). -/
theorem AllInv.of_all_writes {σ : Type} {G : Loc → Val → Prop} {Q : σ → Prop} :
    ∀ {t : EvTree σ}, t.All Q → t.Writes G → t.AllInv G Q
  | .done _, h1, _ => h1
  | .fault _, _, _ => trivial
  | .choose _ _, h1, h2 => fun i => of_all_writes (h1 i) (h2 i)
  | .load _ _ _ _, h1, h2 => fun v _ => of_all_writes (h1 v) (h2 v)
  | .store _ _ _ _ _, h1, h2 => ⟨h2.1, fun b _ => of_all_writes (h1 b) (h2.2 b)⟩
  | .rmw _ _ _ _ _, h1, h2 => fun old _ => ⟨h2.1 old, of_all_writes (h1 old) (h2.2 old)⟩
  | .fence _ _, h1, h2 => fun u => of_all_writes (h1 u) (h2 u)

end Kraken.Promising.EvTree

namespace Kraken.Promising.SLR

open Kraken Kraken.Promising

variable {I : ISA}

private theorem mem_of_ite_nilV {α : Type} {p : Prop} [Decidable p] {x : α} {l : List α}
    (h : x ∈ (if p then [] else l)) : x ∈ l := by
  split at h
  · simp at h
  · exact h

/-- **`runTree_relFulfilsLive_of_relWrites` on the `G`-branches**: from a
memory satisfying `MemInv G`, a run of a tree satisfying `AllInv G P` reads
only `G`-values (the memory stays in `MemInv G`), so `RelWritesV` covers it. -/
theorem runTree_relFulfilsLive_of_relWritesV (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type}
    {Q G : Loc → Val → Prop} {P R : σ → Prop} {ts : Time} {w : Msg} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.AllInv G P → tree.RelWritesV A Q G R → MemInv G c.mem →
      ts ∈ c.prom → ts ∉ c'.prom → c.mem.get? ts = some w → ¬ Q w.loc w.val →
      c'.NoDead → EvTree.RelFulfilsLive A tid iv ts c tree
  | .done _, c, s, c', h, _, _, _, hin, hout, _, _, _ => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd hin hout
  | .fault _, c, s, c', h, _, _, _, _, _, _, _, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hI, hQ, hm, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ⟨i, runTree_relFulfilsLive_of_relWritesV A tid iv (k i) c s c' h (hI i) (hQ i) hm hin hout hw hb hnd⟩
  | .load _ _ _ ret, c, s, c', h, hI, hQ, hm, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hmx, hp⟩ := readSuccs_memProm A iv hx
    have hG := hm.read? (Kraken.Promising.readSuccs_read A iv hx).1
    exact ⟨x, hx, runTree_relFulfilsLive_of_relWritesV A tid iv _ _ s c' h (hI _ hG) (hQ _ hG) (hmx ▸ hm)
      (hp ▸ hin) hout (hmx ▸ hw) hb hnd⟩
  | .store k xcl l v ret, c, s, c', h, hI, hQ, hm, hin, hout, hw, hb, hnd => by
    rw [runTree, List.mem_append] at h
    rcases h with h | h
    · have h := mem_of_ite_nilV h
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      by_cases hk : ts ∈ c''.prom
      · exact .inl ⟨c'', hc'', .inr (runTree_relFulfilsLive_of_relWritesV A tid iv _ c'' s c' h
          (hI.2 true (.inl rfl)) (hQ.2 true) (writeSuccs_memInv A tid _ hc'' hm hI.1) hk
          hout (writeSuccs_get? hc'' hw) hb hnd)⟩
      · obtain ⟨w', hw', hl, hv⟩ := writeSuccs_unpromise hc'' hin hk
        rw [hw] at hw'
        cases hw'
        have hrel : A.storeKind k = .rel := Classical.byContradiction fun hne => hb (hl ▸ hv ▸ hQ.1 hne)
        exact .inl ⟨c'', hc'', .inl ⟨⟨hrel, hin, hk⟩,
          hnd.back (runTree_dord A tid iv _ _ s c' h) (runTree_word A tid iv _ _ s c' h)⟩⟩
    · split at h
      · rename_i hx
        exact .inr (runTree_relFulfilsLive_of_relWritesV A tid iv _ _ s c' h (hI.2 false (.inr hx))
          (hQ.2 false) hm hin hout hw hb hnd)
      · simp at h
  | .fence k ret, c, s, c', h, hI, hQ, hm, hin, hout, hw, hb, hnd => by
    simp only [runTree] at h
    obtain ⟨hmf, hp⟩ := fenceStep_mem_prom c k
    exact runTree_relFulfilsLive_of_relWritesV A tid iv (ret ()) _ s c' h (hI ()) (hQ ()) (hmf ▸ hm)
      (hp ▸ hin) hout (hmf ▸ hw) hb hnd
  | .rmw k noRet l op ret, c, s, c', h, hI, hQ, hm, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    have hfp : ∀ c0 : Ctx, (if A.rmwFence then fenceStep c0 .sy else c0).mem = c0.mem ∧
        (if A.rmwFence then fenceStep c0 .sy else c0).prom = c0.prom := fun c0 => by
      split
      · exact fenceStep_mem_prom c0 .sy
      · exact ⟨rfl, rfl⟩
    have hr := (Kraken.Promising.readSuccs_read A iv hx).1
    rw [(hfp c).1] at hr
    have hG := hm.read? hr
    obtain ⟨hop, hI'⟩ := hI x.2.1 hG
    obtain ⟨hmx, hp⟩ := readSuccs_memProm A iv hx
    rw [(hfp c).1] at hmx
    rw [(hfp c).2] at hp
    have hin' : ts ∈ x.2.2.prom := by rw [hp]; exact hin
    have hw' : x.2.2.mem.get? ts = some w := by rw [hmx]; exact hw
    have hm' : MemInv G x.2.2.mem := by rw [hmx]; exact hm
    refine ⟨x, hx, ?_⟩
    split at h
    · exact .inl (runTree_relFulfilsLive_of_relWritesV A tid iv _ _ s c' h hI' (hQ.2 _)
        (by rw [(hfp _).1]; exact hm') (by rw [(hfp _).2]; exact hin') hout (by rw [(hfp _).1]; exact hw') hb hnd)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      have hm'' : MemInv G c''.mem := writeSuccs_memInv A tid _ hc'' hm' (hop new hnew)
      refine .inr ⟨new, hnew, c'', hc'', ?_⟩
      by_cases hk : ts ∈ c''.prom
      · refine .inr (runTree_relFulfilsLive_of_relWritesV A tid iv _ _ s c' h hI' (hQ.2 _) ?_ ?_ hout ?_ hb hnd)
        · rw [(hfp _).1]
          unfold rmwPost
          split <;> exact hm''
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

/-- **One instruction** (`stepOne_relFulfilsLive_of_relWrites` on the
`G`-branches, from a memory satisfying `MemInv G`). -/
theorem stepOne_relFulfilsLive_of_relWritesV (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Q G : Loc → Val → Prop} {P R : I.State → Prop}
    {tree : EvTree I.State} (hex : I.exec t.st = some tree) (hI : tree.AllInv G P)
    (hQ : tree.RelWritesV A Q G R) (hm : MemInv G mem) {ts : Time} (hin : ts ∈ t.prom)
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
    exact runTree_relFulfilsLive_of_relWritesV A tid _ tree _ st c' hr hI hQ hm hin hout hw hb
      (Ctx.noDead_of_finish hth hlive)

/-- **`PromisePure` under a global value invariant.** Per-thread invariants
`J` whose instruction trees satisfy `AllInv G (J tid)` (every write keeps
`G`, the leaves keep `J`) and `RelWritesV` (non-release writes on the
`G`-branches are pure), with `MemInv G` initially and `J` at the initial
states: every reachable memory satisfies `MemInv G` (`configInv_reachable`),
so the fulfilling run reads only `G`-values. -/
theorem promisePure_of_relWritesV [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (G : Loc → Val → Prop) (J : Nat → I.State → Prop)
    (hcell : ∀ tid st tree, J tid st → I.exec st = some tree →
      tree.AllInv G (J tid) ∧ ∃ R : I.State → Prop, tree.RelWritesV A (fun l v => Pred.Pure (rel l) v) G R)
    (hm0 : MemInv G (Config.init states initMem).mem) (h0 : ∀ tid s, states[tid]? = some s → J tid s) :
    PromisePure A fuel states initMem rel := by
  have hP : StepPreserves (I := I) A G J := fun tid t mem outs o hJ hm hs ho =>
    stepOne_allInv A hs ho (fun tree hex => (hcell tid _ tree hJ hex).1) hm
  have hci : ConfigInv G J (Config.init states initMem) := ⟨hm0, fun tid t ht => by
    obtain ⟨s, hs, rfl⟩ := Config.init_get?_thread ht
    exact h0 tid s hs⟩
  intro π h0' hfin Jt hJl j t pw ht hcw hstep hnot
  apply Classical.byContradiction
  intro hpure
  apply hnot
  have hh : HoldsProm (π.cfg (Jt + 1)) j ((π.cfg Jt).mem.last + 1) := by
    refine ⟨{ t with prom := t.prom ++ [((π.cfg Jt).mem.append { pw.1 with tid := j }).2] }, ?_,
      List.mem_append_right _ (List.mem_singleton_self _)⟩
    rw [hstep, Config.withThread_get? _ _ _ (lt_size_of_get? ht)]
    simp only [↓reduceIte]
  obtain ⟨f, hJf, hf, hheld, hgone⟩ := π.first_removal hfin hJl hh
  obtain ⟨tf, outs, o, htf, hstepf, ho, htf', hmf, hin, hout⟩ :=
    removal_is_instr (succs_cases (π.step f hf)) (hheld f hJf (Nat.le_refl f)) hgone
  have hwJ : (π.cfg (Jt + 1)).mem.get? ((π.cfg Jt).mem.last + 1) = some { pw.1 with tid := j } := by
    rw [hstep]; exact Memory.get?_append_last _ _
  have hwf : (π.cfg f).mem.get? ((π.cfg Jt).mem.last + 1) = some { pw.1 with tid := j } := by
    rw [(π.mem_prefix hJf (by omega)).get? (by
      rw [hstep]; simp only [Config.withThread, Memory.last_append]; exact Nat.le_refl _)]
    exact hwJ
  have hlive : o.thread.hasDeadPromise o.mem = false := by
    rw [← hmf]
    exact liveWfProm A fuel states initMem _ (by rw [← h0']; exact π.reachable (f + 1) hf) (π.live hfin (f + 1) hf)
      j o.thread htf'
  obtain ⟨hmem, hth⟩ := configInv_reachable hP hci (h0' ▸ π.reachable f (by omega))
  cases hex : I.exec tf.st with
  | none => unfold stepOne at hstepf; rw [hex] at hstepf; cases hstepf
  | some tree =>
    obtain ⟨hI, R, hQ⟩ := hcell j tf.st tree (hth j tf htf) hex
    exact ⟨f, hJf, hf, fun q hq1 hq2 => hheld q hq1 hq2, tf, o.thread, htf,
      stepOne_relFulfilsLive_of_relWritesV A hstepf ho hex hI hQ hmem hin hout hwf hpure hlive,
      htf', hout⟩

end Kraken.Promising.SLR

namespace Kraken.Promising

open Kraken.Promising.SLR.EnvG.Vals (stepPreserves_of_allInv)

variable {I : ISA}

/-! ## No non-temporal store under a global value invariant -/

/-- **`Config.NTFree` from value-guarded per-thread invariants**
(`Config.ntFree_of_noNTInvK` with the invariant closed only on the
`G`-branches): per-thread invariants `J` whose instruction trees satisfy
`AllInv G (J tid)` and make no non-temporal store, `J` and `MemInv G` at
`c0` and `vwOldNT = 0` there. Along `ReachableK` the memory keeps `MemInv G`
and every thread `J` (`configInv_reachableK`), so `vwOldNT` stays `0`. -/
theorem Config.ntFree_of_configInvK {A : Arch} {G : Loc → Val → Prop} {J : Nat → I.State → Prop}
    (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid))
    (hnt : ∀ tid st tree, J tid st → I.exec st = some tree → tree.NoNT A) {c0 c : Config I}
    (h : Live.Bridge.ReachableK A c0 c) (h0 : ConfigInv G J c0)
    (hv : ∀ (i : Nat) (t : Thread I), c0.threads[i]? = some t → t.views.vwOldNT = 0) : c.NTFree A := by
  induction h with
  | refl => exact fun i t ht => ⟨fun _ => .inl (hv i t ht), fun tree hex => hnt i t.st tree (h0.2 i t ht) hex⟩
  | @step ca c1 c2 hs _ ih =>
    apply ih (configInv_reachableK (stepPreserves_of_allInv hJ) h0 (.step hs (.refl _)))
    intro i t ht
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      rw [Config.withThread_get? ca _ _ (lt_size_of_get? hj)] at ht
      split at ht
      · cases ht
        exact (stepOne_vwOldNT _ hstep ho (fun tree hex => hnt j tj.st tree (h0.2 j tj hj) hex)).trans
          (hv j tj hj)
      · exact hv i t ht
    | @promise j tj p hj _ =>
      rw [Config.withThread_get? ca _ _ (lt_size_of_get? hj)] at ht
      split at ht
      · cases ht
        exact hv j tj hj
      · exact hv i t ht

/-- **`Config.ntFree_of_configInvK` from the initial configuration**: along
`ReachableK` from `Config.init states initMem`, every configuration satisfies
`Config.NTFree A` when the threads' trees keep `J` on the `G`-branches and
make no non-temporal store, `MemInv G` holds initially and `J` at the initial
states. Stated on `ReachableK`, so the K-world clone of `Vals.final_of_chainVP`
(`ChainK/ValsChainN.lean`) uses it unchanged. -/
theorem Config.ntFree_of_configInv_initK {A : Arch} {G : Loc → Val → Prop} {J : Nat → I.State → Prop}
    (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid))
    (hnt : ∀ tid st tree, J tid st → I.exec st = some tree → tree.NoNT A)
    {states : List I.State} {initMem : List (Loc × Val)}
    (hm0 : MemInv G (Config.init states initMem).mem) (h0 : ∀ tid s, states[tid]? = some s → J tid s)
    {c : Config I} (hc : Live.Bridge.ReachableK A (Config.init states initMem) c) : c.NTFree A := by
  refine Config.ntFree_of_configInvK hJ hnt hc ⟨hm0, fun tid t ht => ?_⟩ fun i t ht => ?_
  · obtain ⟨s, hs, rfl⟩ := SLR.Config.init_get?_thread ht
    exact h0 tid s hs
  · obtain ⟨s, -, rfl⟩ := SLR.Config.init_get?_thread ht
    rfl

/-- **Theorem 1′'s scope from value-guarded per-thread invariants**: every
configuration reachable from `Config.init states initMem` satisfies
`Config.NTFree A` when the threads' trees keep `J` on the `G`-branches
(`AllInv G`) and make no non-temporal store, `MemInv G` holds initially and
`J` at the initial states. -/
theorem Config.ntFree_of_configInv {A : Arch} [I.LawfulState] {G : Loc → Val → Prop}
    {J : Nat → I.State → Prop}
    (hJ : ∀ tid st tree, J tid st → I.exec st = some tree → tree.AllInv G (J tid))
    (hnt : ∀ tid st tree, J tid st → I.exec st = some tree → tree.NoNT A) {fuel : Nat}
    {states : List I.State} {initMem : List (Loc × Val)}
    (hm0 : MemInv G (Config.init states initMem).mem) (h0 : ∀ tid s, states[tid]? = some s → J tid s)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) : c.NTFree A := by
  refine Config.ntFree_of_configInvK hJ hnt (.of_reachable hc) ⟨hm0, fun tid t ht => ?_⟩ fun i t ht => ?_
  · obtain ⟨s, hs, rfl⟩ := SLR.Config.init_get?_thread ht
    exact h0 tid s hs
  · obtain ⟨s, -, rfl⟩ := SLR.Config.init_get?_thread ht
    rfl

end Kraken.Promising

namespace Kraken.Promising.SLR.EnvG.Vals

open Kraken Kraken.Promising Kraken.Promising.SLR

variable {I : ISA}

/-- **`final_of_chainV` from one per-thread tree law**: per-thread
invariants `J` whose instruction trees keep `J` on the `G`-branches
(`AllInv G`), make no non-temporal store, and write pure values by every
non-release write on the `G`-branches (`RelWritesV`) give the scope `NTFree`
(`Config.ntFree_of_configInv`) and `PromisePure` (`promisePure_of_relWritesV`)
of `final_of_chainV`. ISA-neutral; one value-restricted purity judgment per
thread supplies the law. -/
theorem final_of_chainVP [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rF : Nat → Res} {g₀ : Ghost} {B : Config I → Res → Ghost → Prop}
    {Φ : Config I → Prop} (G : Loc → Val → Prop) (J : Nat → I.State → Prop)
    (hJ : ∀ tid st tree, J tid st → I.exec st = some tree →
      tree.AllInv G (J tid) ∧ tree.NoNT A ∧
        ∃ R : I.State → Prop, tree.RelWritesV A (fun l v => Pred.Pure (g₀.rel l) v) G R)
    (hE : Erase rF g₀ (fun _ => False) (Config.init states initMem)) (hpend : ∀ ts, ts ∉ g₀.pend)
    (hm0 : MemInv G (Config.init states initMem).mem) (h0v : ∀ tid s, states[tid]? = some s → J tid s)
    (hsafe : ∀ tid, tid < states.length → ∀ n m,
      NPSafeF (modelX I (MemInvX G)) A B tid n m True (Config.init states initMem) (rF tid) g₀)
    {c : Config I} (hc : Reachable A fuel (Config.init states initMem) c) (hf : c.final = true)
    (hfin : ∀ (rF' : Nat → Res) (g' : Ghost), Erase rF' g' (fun _ => False) c → g₀.Le g' →
      c.threads.size = states.length → (∀ tid, c.Done tid → B c (rF' tid) g') → Φ c) :
    Φ c :=
  final_of_chainV G J (fun tid st tree h hex => (hJ tid st tree h hex).1)
    (fun _ hc' => Config.ntFree_of_configInv_initK (fun tid st tree h hex => (hJ tid st tree h hex).1)
      (fun tid st tree h hex => (hJ tid st tree h hex).2.1) hm0 h0v (Reachable.toK hc'))
    hE hpend hm0 h0v
    (promisePure_of_relWritesV G J (fun tid st tree h hex => ⟨(hJ tid st tree h hex).1, (hJ tid st tree h hex).2.2⟩)
      hm0 h0v)
    hsafe hc hf hfin

end Kraken.Promising.SLR.EnvG.Vals

#print axioms Kraken.Promising.Config.ntFree_of_configInv
#print axioms Kraken.Promising.SLR.EnvG.Vals.final_of_chainVP

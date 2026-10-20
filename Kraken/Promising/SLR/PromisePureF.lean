/-
`PromisePure'` at the fence-aware guards from a per-instruction condition: **impure values are written only by release writes or by
fence-released writes** (`dmb ish; str`). The `GF`/`GHyb` analogue of
`SLR/PromisePureGeneral.lean`'s `G₀` chain (ISA-neutral).

A *fence-released* write is a write issued from `Views.FenceRel` views
(`Promising/FenceRelease.lean`): after `dmb ish`/`dsb sy` (`fence .sy`,
`fenceStep_sy_fenceRel`) with no access in between, a plain store is
release-bounded exactly as `stlr` is. The cell condition tracks this
syntactically inside one instruction's tree and takes the thread's views at
the instruction's start as the initial flag (`t.views.FenceRel`), so a
`dmb ish` in an earlier instruction counts. `dmb ishst`/`dsb st` (`.st`,
`.stAll`) never set the flag (herd allows LB+dmb.st), and neither do `.ld` or
`isb`; every fence keeps it (`fenceStep_fenceRel`, fences only raise
`vrNew`/`vwNew`). Any load, store or RMW clears it (conservative: no access
in between).

- `EvTree.RelWritesF A Q F`: every write of the tree that is neither a
  release write nor fence-released (the flag `F` for the context at the
  tree's root) satisfies `Q`. RMW writes must be releases or satisfy `Q` (an
  RMW reads first).
- `EvTree.RelWrites.relWritesF`: `RelWrites → RelWritesF` at every flag, so
  every existing cell proof transfers.
- `runTree_relFulfilsLiveF_of_relWritesF`, `stepOne_relFulfilsLiveF_of_relWritesF`:
  a run that removes a promise whose message fails `Q` does so with a
  release or fence-released write, i.e. a fence-aware live release
  fulfilment (`EvTree.RelFulfilsLiveF`, `Thread.RelFulfilsLiveF`).
- `finishInstr_fenceRel`, `stepOne_fenceRel`, `stepOne_fenceRel_of_fence_sy`,
  `stepOne_fenceRel_of_done`: `FenceRel` across instructions (for the thread
  invariant that supplies the flag): `dmb ish` establishes it, a silent
  instruction keeps it.
- `GuardCoversF G rel`: the prepay guard `G` holds at every fence-aware live
  fulfilment of an impure message; `guardCoversF_GF`, `guardCoversF_GHyb`
  (the impure-value conjunct of `GHyb` is exactly what `¬ Pred.Pure` gives).
- `FulfilCellF`, `promisePure'_of_fulfilCellF`, `promisePure'_of_relWritesFT`,
  `promisePure'_of_relWritesFReach`: `PromisePure' G` for every covering
  guard; `promisePure_of_relWritesF` (at `GF`) and
  `promisePureHyb_of_relWritesF` (at `GHyb rel`).
- `Theorem1IIRelWritesF`, `theorem1IIPure_of_relWritesF`: Theorem 1′
  through `theorem1IIPure_Hyb_S`, with `NPSafeP (GHyb g.rel) (K2Scope AllocIds)`
  per thread; `Theorem1IIRelWritesF_GF`, `theorem1IIPure_of_relWritesF_GF`
  through `theorem1IIPure_F_S` (`NPSafeP GF (K2Scope AllocIds)`).
- `relWritesF_hyps_of_relWrites`, `theorem1IIPure_of_relWrites_viaF`: the
  hypotheses of `theorem1IIPure_of_relWrites`, with `NPSafe` obtained (as for
  every existing program) from `ThreadRuleRX` rules with `RelPure`, imply those
  of `theorem1IIPure_of_relWritesF`. An arbitrary `NPSafe` (`G₀`) proof does
  not transfer by itself: `GHyb` asks for more prepayments (`NPSafeP.mono` is
  antitone in the guard), and the collapse `GHyb.toG₀` needs the cell
  condition at the prepaying state, which `NPSafe` alone does not provide.

Phase-1 limits do not apply here (this is the `PromisePure'` side only). What
remains for a program whose impure value is published by a fence-released
store is the `NPSafeP (GHyb g.rel)` side: a rule that prepays at
`Thread.RelFulfilsLiveF` for impure messages (see `KNOWN_GAPS.md`).
-/
import Kraken.Promising.SLR.PromisePureGeneral
import Kraken.Promising.SLR.Theorem1FinalP
import Kraken.Promising.SLR.NPSafePHyb

namespace Kraken.Promising

/-- **Every fence keeps `FenceRel`**: fences only raise `vrNew`/`vwNew`;
`relPre` and `vCAP` are unchanged. -/
theorem fenceStep_fenceRel {c : Ctx} (h : c.views.FenceRel) (k : FenceKind) :
    (fenceStep c k).views.FenceRel := by
  cases k <;> simp only [fenceStep, Views.FenceRel, Views.relPre] at h ⊢ <;>
    (try simp only [View] at *) <;> omega

namespace EvTree

/-! ## Release or fence-released writes in an event tree -/

/-- **Release or fence-released writes**: every store of the tree that is not
a release (`A.storeKind k ≠ .rel`) and not fence-released satisfies `Q`, and
so does every non-release RMW write. The flag `F` says that the context at
the root is fence-released (`Views.FenceRel`); a `fence .sy` sets it, other
fences keep it, and every access clears it. -/
def RelWritesF {σ : Type} (A : Arch) (Q : Loc → Val → Prop) : Prop → EvTree σ → Prop
  | _, .done _ => True
  | _, .fault _ => True
  | F, .choose _ k => ∀ i, (k i).RelWritesF A Q F
  | _, .load _ _ _ ret => ∀ v, (ret v).RelWritesF A Q False
  | F, .store k _ l v ret => (A.storeKind k ≠ .rel → ¬ F → Q l v) ∧ ∀ b, (ret b).RelWritesF A Q False
  | _, .rmw k _ l op ret =>
    (A.storeKind (A.rmwKind k).storeKind ≠ .rel → ∀ old new, op old = some new → Q l new) ∧
      ∀ v, (ret v).RelWritesF A Q False
  | F, .fence k ret => ∀ u, (ret u).RelWritesF A Q (F ∨ k = .sy)

variable {σ : Type} {A : Arch}

/-- `RelWritesF` is monotone in `Q` and in the flag. -/
theorem RelWritesF.mono {Q Q' : Loc → Val → Prop} (hQ : ∀ l v, Q l v → Q' l v) :
    ∀ {tree : EvTree σ} {F F' : Prop}, (F → F') → tree.RelWritesF A Q F → tree.RelWritesF A Q' F'
  | .done _, _, _, _, _ => trivial
  | .fault _, _, _, _, _ => trivial
  | .choose _ _, _, _, hF, h => fun i => RelWritesF.mono hQ hF (h i)
  | .load _ _ _ _, _, _, _, h => fun v => RelWritesF.mono hQ id (h v)
  | .store _ _ _ _ _, _, _, hF, h =>
    ⟨fun hk hn => hQ _ _ (h.1 hk (fun f => hn (hF f))), fun b => RelWritesF.mono hQ id (h.2 b)⟩
  | .rmw _ _ _ _ _, _, _, _, h =>
    ⟨fun hk old new hn => hQ _ _ (h.1 hk old new hn), fun v => RelWritesF.mono hQ id (h.2 v)⟩
  | .fence _ _, _, _, hF, h => fun u => RelWritesF.mono hQ (Or.imp_left hF) (h u)

/-- **`RelWrites` gives `RelWritesF` at every flag**: every existing cell
proof transfers. -/
theorem RelWrites.relWritesF {Q : Loc → Val → Prop} :
    ∀ {tree : EvTree σ} {F : Prop}, tree.RelWrites A Q → tree.RelWritesF A Q F
  | .done _, _, _ => trivial
  | .fault _, _, _ => trivial
  | .choose _ _, _, h => fun i => RelWrites.relWritesF (h i)
  | .load _ _ _ _, _, h => fun v => RelWrites.relWritesF (h v)
  | .store _ _ _ _ _, _, h => ⟨fun hk _ => h.1 hk, fun b => RelWrites.relWritesF (h.2 b)⟩
  | .rmw _ _ _ _ _, _, h => ⟨h.1, fun v => RelWrites.relWritesF (h.2 v)⟩
  | .fence _ _, _, h => fun u => RelWrites.relWritesF (h u)

end EvTree

end Kraken.Promising

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

/-! ## A fulfilment of an impure promise is a fence-aware release fulfilment -/

private theorem mem_of_ite_nilF {α : Type} {p : Prop} [Decidable p] {x : α} {l : List α}
    (h : x ∈ (if p then [] else l)) : x ∈ l := by
  split at h
  · simp at h
  · exact h

/-- **A run that removes a promise whose message fails `Q`, of a tree whose
writes that are neither release nor fence-released satisfy `Q`, is a live
fence-aware release fulfilment** (the F-analogue of
`runTree_relFulfilsLive_of_relWrites`): the write that removes the promise
writes its message (`writeSuccs_unpromise`), so it is a release write or a
store issued under `FenceRel` (the flag `F`, which holds of the context
whenever the tree says so). -/
theorem runTree_relFulfilsLiveF_of_relWritesF (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type}
    {Q : Loc → Val → Prop} {ts : Time} {w : Msg} :
    ∀ (tree : EvTree σ) (F : Prop) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.RelWritesF A Q F → (F → c.views.FenceRel) → ts ∈ c.prom → ts ∉ c'.prom → c.mem.get? ts = some w →
      ¬ Q w.loc w.val → c'.NoDead → EvTree.RelFulfilsLiveF A tid iv ts c tree
  | .done _, _, c, s, c', h, _, _, hin, hout, _, _, _ => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd hin hout
  | .fault _, _, c, s, c', h, _, _, _, _, _, _, _ => by simp [runTree] at h
  | .choose _ k, F, c, s, c', h, hQ, hF, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ⟨i, runTree_relFulfilsLiveF_of_relWritesF A tid iv (k i) F c s c' h (hQ i) hF hin hout hw hb hnd⟩
  | .load _ _ _ ret, _, c, s, c', h, hQ, _, hin, hout, hw, hb, hnd => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    exact ⟨x, hx, runTree_relFulfilsLiveF_of_relWritesF A tid iv _ False _ s c' h (hQ _) False.elim
      (hp ▸ hin) hout (hm ▸ hw) hb hnd⟩
  | .store k xcl l v ret, F, c, s, c', h, hQ, hF, hin, hout, hw, hb, hnd => by
    rw [runTree, List.mem_append] at h
    rcases h with h | h
    · have h := mem_of_ite_nilF h
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      by_cases hk : ts ∈ c''.prom
      · exact .inl ⟨c'', hc'', .inr (runTree_relFulfilsLiveF_of_relWritesF A tid iv _ False c'' s c' h (hQ.2 true)
          False.elim hk hout (writeSuccs_get? hc'' hw) hb hnd)⟩
      · obtain ⟨w', hw', hl, hv⟩ := writeSuccs_unpromise hc'' hin hk
        rw [hw] at hw'
        cases hw'
        have hrel : A.storeKind k = .rel ∨ c.views.FenceRel := by
          by_cases hr : A.storeKind k = .rel
          · exact .inl hr
          · exact .inr (hF (Classical.byContradiction fun hnF => hb (hl ▸ hv ▸ hQ.1 hr hnF)))
        exact .inl ⟨c'', hc'', .inl ⟨⟨hrel, hin, hk⟩,
          hnd.back (runTree_dord A tid iv _ _ s c' h) (runTree_word A tid iv _ _ s c' h)⟩⟩
    · split at h
      · exact .inr (runTree_relFulfilsLiveF_of_relWritesF A tid iv _ False _ s c' h (hQ.2 false) False.elim
          hin hout hw hb hnd)
      · simp at h
  | .fence k ret, F, c, s, c', h, hQ, hF, hin, hout, hw, hb, hnd => by
    simp only [runTree] at h
    obtain ⟨hm, hp⟩ := fenceStep_mem_prom c k
    have hF' : (F ∨ k = .sy) → (fenceStep c k).views.FenceRel := by
      rintro (hf | rfl)
      · exact fenceStep_fenceRel (hF hf) k
      · exact fenceStep_sy_fenceRel c
    exact runTree_relFulfilsLiveF_of_relWritesF A tid iv (ret ()) _ _ s c' h (hQ ()) hF' (hp ▸ hin) hout
      (hm ▸ hw) hb hnd
  | .rmw k noRet l op ret, _, c, s, c', h, hQ, _, hin, hout, hw, hb, hnd => by
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
    · exact .inl (runTree_relFulfilsLiveF_of_relWritesF A tid iv _ False _ s c' h (hQ.2 _) False.elim
        (by rw [(hfp _).2]; exact hin') hout (by rw [(hfp _).1]; exact hw') hb hnd)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      refine .inr ⟨new, hnew, c'', hc'', ?_⟩
      by_cases hk : ts ∈ c''.prom
      · refine .inr (runTree_relFulfilsLiveF_of_relWritesF A tid iv _ False _ s c' h (hQ.2 _) False.elim ?_ hout ?_
          hb hnd)
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
        refine .inl ⟨⟨.inl hrel, hin', hk⟩, hnd.back ?_ ?_⟩
        · exact ((Ctx.DOrd.rmwPost A c'' k noRet l).trans (Ctx.DOrd.fenceOpt _ A.rmwFence .sy)).trans
            (runTree_dord A tid iv _ _ s c' h)
        · exact ((Ctx.WOrd.rmwPost A c'' k noRet l).trans (Ctx.WOrd.fenceOpt _ A.rmwFence .sy)).trans
            (runTree_word A tid iv _ _ s c' h)

/-- **One instruction** (the F-analogue of
`stepOne_relFulfilsLive_of_relWrites`): a step of thread `tid` whose tree
satisfies `RelWritesF` with the flag `t.views.FenceRel`, removing the
outstanding promise `ts` whose message fails `Q` and leaving no promise dead,
is a live fence-aware release fulfilment of `ts`. -/
theorem stepOne_relFulfilsLiveF_of_relWritesF (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Q : Loc → Val → Prop} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree) (hQ : tree.RelWritesF A Q t.views.FenceRel) {ts : Time} (hin : ts ∈ t.prom)
    (hout : ts ∉ o.thread.prom) {w : Msg} (hw : mem.get? ts = some w) (hb : ¬ Q w.loc w.val)
    (hlive : o.thread.hasDeadPromise o.mem = false) : t.RelFulfilsLiveF A tid ts mem := by
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
    exact runTree_relFulfilsLiveF_of_relWritesF A tid _ tree _ _ st c' hr hQ id hin hout hw hb
      (Ctx.noDead_of_finish hth hlive)

/-! ## `FenceRel` across instructions

A cell condition with the flag `t.views.FenceRel` needs, in the thread
invariant, that the views are fence-released where the program relies on it.
`dmb ish` establishes it, and a silent instruction keeps it
(`finishInstr` changes only register views and raises `vCAP`). -/

/-- `finishInstr` keeps `FenceRel`. -/
theorem finishInstr_fenceRel {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State}
    {c : Ctx} {th : Thread I} (h : th ∈ finishInstr t d iv st c) (hF : c.views.FenceRel) :
    th.views.FenceRel := by
  obtain ⟨h1, h2, h3, h4⟩ := finishInstr_vmono h
  have h5 := congrArg Views.vwOld (finishInstr_relKey h).2
  simp only at h5
  simp only [Views.FenceRel, Views.relPre] at hF ⊢
  rw [h1, h2, h3, h5]
  simp only [View] at *
  omega

/-- The outcomes of a step whose run ends in `FenceRel` contexts are
`FenceRel`. -/
theorem stepOne_fenceRel {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hF : ∀ s c', .ok (s, c') ∈ runTree A tid (instrViews t (I.deps t.st))
      { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } tree → c'.views.FenceRel) :
    o.thread.views.FenceRel := by
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
    exact finishInstr_fenceRel hth (hF st c' hr)

/-- **After `dmb ish`** (a cell whose tree is `fence .sy` then done) the
thread's views are `FenceRel`. -/
theorem stepOne_fenceRel_of_fence_sy {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {s : I.State} (hex : I.exec t.st = some (.fence .sy fun _ => .done s)) :
    o.thread.views.FenceRel :=
  stepOne_fenceRel hstep ho hex fun s' c' h => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fenceStep_sy_fenceRel _

/-- **A silent instruction keeps `FenceRel`.** -/
theorem stepOne_fenceRel_of_done {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {s : I.State} (hex : I.exec t.st = some (.done s))
    (hF : t.views.FenceRel) : o.thread.views.FenceRel :=
  stepOne_fenceRel hstep ho hex fun s' c' h => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hF

/-! ## Guards that cover fence-aware fulfilments of impure messages -/

/-- **The prepay guard `G` covers fence-aware live fulfilments of impure
messages** for the release predicates `rel`. -/
def GuardCoversF (G : PrepayGuard I) (rel : Loc → Pred) : Prop :=
  ∀ (A : Arch) (tid : Nat) (ts : Time) (t : Thread I) (mem : Memory) (w : Msg),
    t.RelFulfilsLiveF A tid ts mem → mem.get? ts = some w → ¬ Pred.Pure (rel w.loc) w.val → G A tid ts t mem

theorem guardCoversF_GF (rel : Loc → Pred) : GuardCoversF (I := I) GF rel :=
  fun _ _ _ _ _ _ h _ _ => h

/-- The impure-value conjunct of `GHyb rel` is exactly what the producer has. -/
theorem guardCoversF_GHyb (rel : Loc → Pred) : GuardCoversF (I := I) (GHyb rel) rel :=
  fun _ _ _ _ _ w h hw hb => .inr ⟨h, w, hw, hb⟩

/-! ## `PromisePure'` from the cell condition at held states -/

/-- **The fence-aware cell condition at held states** (`FulfilCell` with
`RelWritesF`): on a path to a final configuration, while thread `j` holds a
promise it made at step `J`, its next instruction's writes that are neither
release nor fence-released (from `j`'s current views) are pure for `rel`. -/
def FulfilCellF (A : Arch) (fuel : Nat) [I.LawfulState] (states : List I.State) (initMem : List (Loc × Val))
    (rel : Loc → Pred) : Prop :=
  ∀ (π : Path A fuel I), π.cfg 0 = Config.init states initMem → (π.cfg π.len).final = true →
    ∀ J f j t pw, J < f → f < π.len → PromStep π J j t pw → HeldOn π J f j ((π.cfg J).mem.last + 1) →
    ∀ tf tree, (π.cfg f).threads[j]? = some tf → I.exec tf.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (rel l) v) tf.views.FenceRel

/-- `FulfilCell` gives `FulfilCellF`. -/
theorem FulfilCell.toF [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (h : FulfilCell A fuel states initMem rel) :
    FulfilCellF A fuel states initMem rel :=
  fun π h0 hf J f j t pw hJf hfl hs hh tf tree htf hex =>
    (h π h0 hf J f j t pw hJf hfl hs hh tf tree htf hex).relWritesF

/-- **`FulfilCellF` gives `PromisePure' G` for every covering guard**
(`promisePure_of_fulfilCell` with the fence-aware fulfilment): on a path to a
final configuration a promise of an impure value is removed by an instruction
of its thread, at a held state, that writes the promised message, hence with
a release or fence-released write, leaving no promise dead: a fence-aware
live fulfilment, which `G` covers. -/
theorem promisePure'_of_fulfilCellF [I.LawfulState] {G : PrepayGuard I} {A : Arch} {fuel : Nat}
    {states : List I.State} {initMem : List (Loc × Val)} {rel : Loc → Pred} (hG : GuardCoversF G rel)
    (hcell : FulfilCellF A fuel states initMem rel) :
    PromisePure' G A fuel states initMem rel := by
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
      hG A j _ tf _ _ (stepOne_relFulfilsLiveF_of_relWritesF A hstepf ho hex hc hin hout hwf hpure hlive) hwf hpure,
      htf', hout⟩

/-- **`PromisePure' G` from release-or-fence-released writes, thread-local
invariant** (`promisePure_of_relWritesT` with `RelWritesF`): every thread `t`
reachable at position `tid` satisfies `Jinv tid t`, and under it the next
instruction's writes that are neither release nor fence-released (from `t`'s
views) write values pure for `rel`. The invariant must range over whole
threads: whether the views are `FenceRel` is a fact about `t.views`. -/
theorem promisePure'_of_relWritesFT [I.LawfulState] {G : PrepayGuard I} {A : Arch} {fuel : Nat}
    {states : List I.State} {initMem : List (Loc × Val)} {rel : Loc → Pred} (hG : GuardCoversF G rel)
    (Jinv : Nat → Thread I → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t)
    (hcell : ∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (rel l) v) t.views.FenceRel) :
    PromisePure' G A fuel states initMem rel :=
  promisePure'_of_fulfilCellF hG fun π h0 _ _ f j _ _ _ hf _ _ tf tree htf hex =>
    hcell j tf tree (hJ _ (h0 ▸ π.reachable f (by omega)) j tf htf) hex

/-- `promisePure'_of_relWritesFT` at the strongest invariant (`ThreadReach`). -/
theorem promisePure'_of_relWritesFReach [I.LawfulState] {G : PrepayGuard I} {A : Arch} {fuel : Nat}
    {states : List I.State} {initMem : List (Loc × Val)} {rel : Loc → Pred} (hG : GuardCoversF G rel)
    (hcell : ∀ tid t tree, ThreadReach A fuel states initMem tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (rel l) v) t.views.FenceRel) :
    PromisePure' G A fuel states initMem rel :=
  promisePure'_of_relWritesFT hG (ThreadReach A fuel states initMem) (fun c hc _ _ ht => ⟨c, hc, ht⟩) hcell

/-- **The producer at `GF`**: `PromisePure' GF` from release-or-fence-released
writes (thread-local invariant). -/
theorem promisePure_of_relWritesF [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Jinv : Nat → Thread I → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t)
    (hcell : ∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (rel l) v) t.views.FenceRel) :
    PromisePure' GF A fuel states initMem rel :=
  promisePure'_of_relWritesFT (guardCoversF_GF rel) Jinv hJ hcell

/-- **The producer at `GHyb rel`**: `PromisePure' (GHyb rel)` from
release-or-fence-released writes (thread-local invariant). -/
theorem promisePureHyb_of_relWritesF [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Jinv : Nat → Thread I → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t)
    (hcell : ∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (rel l) v) t.views.FenceRel) :
    PromisePure' (GHyb rel) A fuel states initMem rel :=
  promisePure'_of_relWritesFT (guardCoversF_GHyb rel) Jinv hJ hcell

/-! ## Theorem 1′ with the release-or-fence-released condition -/

/-- **Theorem 1′, release-or-fence-released form** (at `GHyb g.rel` and
option (S)'s frame): `Theorem1IIPure'` at `theorem1IIPure_Hyb_S`'s guards with
`PromisePure'` replaced by the per-instruction condition of
`promisePureHyb_of_relWritesF`. Each thread must supply
`NPSafeP (GHyb g.rel) (K2Scope AllocIds)`: a prepayment at every promise its
next instruction can fulfil with a live release (the old guard) or with a
live fence-released store of an impure value. Every rule with (i‴)
(`RelPure`) gives it with no new prepayment (`NPSafeP.of_relPure_S`; the four
existing rules: `…_npSafeP_hyb_S`). The conclusion's virtual relation is
`Config.VirtualOfG (GHyb g.rel)`. -/
def Theorem1IIRelWritesF (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    ∀ (Jinv : Nat → Thread I → Prop),
    (∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t) →
    (∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (g.rel l) v) t.views.FenceRel) →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid (GHyb g.rel) (K2Scope (model I) AllocIds) n m True
        (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', c.VirtualOfG (GHyb g.rel) A v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- **Theorem 1′, release-or-fence-released form** (`theorem1IIPure_Hyb_S`
through `promisePureHyb_of_relWritesF`). -/
theorem theorem1IIPure_of_relWritesF [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIRelWritesF (I := I) A fuel := by
  intro B states initMem rF g hH E hnp Jinv hJ hcell hsafe c hc hlive
  exact theorem1IIPure_Hyb_S g.rel A fuel B states initMem rF g hH E hnp
    (promisePureHyb_of_relWritesF Jinv hJ hcell) hsafe c hc hlive

/-- **Theorem 1′, release-or-fence-released form at `GF`**: as
`Theorem1IIRelWritesF`, through `theorem1IIPure_F_S`. Each thread supplies
`NPSafeP GF (K2Scope AllocIds)`, i.e. prepays at *every* fence-aware live
fulfilment, pure or not (the existing rules do not give this; prefer
`theorem1IIPure_of_relWritesF`). -/
def Theorem1IIRelWritesF_GF (A : Arch) (fuel : Nat) [I.LawfulState] : Prop :=
  ∀ (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost),
    (∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A) →
    Erase rF g (fun _ => False) (Config.init states initMem) → (∀ ts, ts ∉ g.pend) →
    ∀ (Jinv : Nat → Thread I → Prop),
    (∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv tid t) →
    (∀ tid t tree, Jinv tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (g.rel l) v) t.views.FenceRel) →
    (∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid GF (K2Scope (model I) AllocIds) n m True (Config.init states initMem) (rF tid) g) →
    ∀ c, Reachable A fuel (Config.init states initMem) c → c.Live A fuel →
      ∃ v rF' g', c.VirtualOfG GF A v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
        ∀ tid, v.Done tid → B v (rF' tid) g'

/-- `Theorem1IIRelWritesF_GF` (`theorem1IIPure_F_S` through
`promisePure_of_relWritesF`). -/
theorem theorem1IIPure_of_relWritesF_GF [I.LawfulState] (A : Arch) (fuel : Nat) :
    Theorem1IIRelWritesF_GF (I := I) A fuel := by
  intro B states initMem rF g hH E hnp Jinv hJ hcell hsafe c hc hlive
  exact theorem1IIPure_F_S A fuel B states initMem rF g hH E hnp
    (promisePure_of_relWritesF Jinv hJ hcell) hsafe c hc hlive

/-! ## The release-write form's hypotheses give the new form's -/

/-- **The hypotheses of `theorem1IIPure_of_relWrites` give those of
`theorem1IIPure_of_relWritesF`**, when each thread's `NPSafe` comes, as for
every existing program, from a `ThreadRuleRX` with (i‴) (`RelPure`) holding at
the initial configuration (`NPSafe.of_ruleRX`; the old `hsafe` is the last
conjunct): the state invariant lifts to threads, `RelWrites` gives
`RelWritesF` (`EvTree.RelWrites.relWritesF`), and the rules give `NPSafeP`
at `GHyb g.rel` in the frame `K2Scope AllocIds` (`NPSafeP.of_relPure_S`). So
the new form is strictly more general: it also accepts fence-released stores
of impure values (the KNOWN_GAPS writer, `SLR/PromisePureFTests.lean`). An
arbitrary `NPSafe` proof does not transfer by itself (`GHyb` asks for more
prepayments than `G₀`). -/
theorem relWritesF_hyps_of_relWrites [I.LawfulState] {A : Arch} {fuel : Nat}
    {B : Config I → Res → Ghost → Prop} {states : List I.State} {initMem : List (Loc × Val)}
    {rF : Nat → Res} {g : Ghost} (Jinv : I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree → tree.RelWrites A fun l v => Pred.Pure (g.rel l) v)
    (R : ∀ tid, ThreadRuleRX A B tid) (hR : ∀ tid, RelPure (R tid))
    (hinit : ∀ tid, tid < states.length → (R tid).Inv True (Config.init states initMem) (rF tid) g) :
    (∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → (fun (_ : Nat) (t : Thread I) => Jinv t.st) tid t) ∧
    (∀ tid t tree, (fun (_ : Nat) (t : Thread I) => Jinv t.st) tid t → I.exec t.st = some tree →
      tree.RelWritesF A (fun l v => Pred.Pure (g.rel l) v) t.views.FenceRel) ∧
    (∀ tid, tid < states.length → ∀ n m,
      NPSafeP (model I) A B tid (GHyb g.rel) (K2Scope (model I) AllocIds) n m True
        (Config.init states initMem) (rF tid) g) ∧
    (∀ tid, tid < states.length → ∀ n m,
      NPSafe (model I) A B tid n m True (Config.init states initMem) (rF tid) g) :=
  ⟨hJ, fun _ t tree h hex => (hcell t.st tree h hex).relWritesF,
    fun tid htid n m => NPSafeP.of_relPure_S (R tid) (hR tid) n m True _ _ g (hinit tid htid),
    fun tid htid n m => NPSafe.of_ruleRX (R tid) n m True _ _ g (hinit tid htid)⟩

/-- `theorem1IIPure_of_relWritesF` from the release-write form's hypotheses
(rules with `RelPure`; `relWritesF_hyps_of_relWrites`). -/
theorem theorem1IIPure_of_relWrites_viaF [I.LawfulState] (A : Arch) (fuel : Nat)
    (B : Config I → Res → Ghost → Prop) (states : List I.State) (initMem : List (Loc × Val))
    (rF : Nat → Res) (g : Ghost)
    (hH : ∀ c, Reachable A fuel (Config.init states initMem) c → c.NTFree A)
    (E : Erase rF g (fun _ => False) (Config.init states initMem)) (hnp : ∀ ts, ts ∉ g.pend)
    (Jinv : I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I),
      c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree → tree.RelWrites A fun l v => Pred.Pure (g.rel l) v)
    (R : ∀ tid, ThreadRuleRX A B tid) (hR : ∀ tid, RelPure (R tid))
    (hinit : ∀ tid, tid < states.length → (R tid).Inv True (Config.init states initMem) (rF tid) g)
    (c : Config I) (hc : Reachable A fuel (Config.init states initMem) c) (hlive : c.Live A fuel) :
    ∃ v rF' g', c.VirtualOfG (GHyb g.rel) A v ∧ Erase rF' g' (fun _ => False) v ∧ g.Le g' ∧
      ∀ tid, v.Done tid → B v (rF' tid) g' :=
  let H := relWritesF_hyps_of_relWrites (fuel := fuel) Jinv hJ hcell R hR hinit
  theorem1IIPure_of_relWritesF A fuel B states initMem rF g hH E hnp _ H.1 H.2.1 H.2.2.1 c hc hlive

end Kraken.Promising.SLR

#print axioms Kraken.Promising.SLR.runTree_relFulfilsLiveF_of_relWritesF
#print axioms Kraken.Promising.SLR.stepOne_relFulfilsLiveF_of_relWritesF
#print axioms Kraken.Promising.SLR.promisePure'_of_fulfilCellF
#print axioms Kraken.Promising.SLR.promisePure_of_relWritesF
#print axioms Kraken.Promising.SLR.promisePureHyb_of_relWritesF
#print axioms Kraken.Promising.SLR.theorem1IIPure_of_relWritesF
#print axioms Kraken.Promising.SLR.theorem1IIPure_of_relWritesF_GF
#print axioms Kraken.Promising.SLR.relWritesF_hyps_of_relWrites
#print axioms Kraken.Promising.SLR.stepOne_fenceRel_of_fence_sy
#print axioms Kraken.Promising.SLR.stepOne_fenceRel_of_done
#print axioms Kraken.Promising.SLR.theorem1IIPure_of_relWrites_viaF

/-
Which instruction fulfils a promise, and (O5) `PromisePure` from the
program's stores (ISA-neutral).

- `writeSuccs_unpromise`: a write that removes the outstanding promise `ts`
  writes the message at `ts` (location and value).
- `EvTree.Writes Q`: every store and every RMW write of the tree satisfies
  `Q`; `stepOne_unpromise`: an instruction whose tree only writes `Q` and
  that removes the promise `ts` from the thread's promises has `Q` at the
  message of `ts`.
- `relFulfils_of_store`: **a fulfilling step by a single release store is
  `Thread.RelFulfils`** (the store's `A.storeKind` is `.rel`, its tree is
  `.store k false l v (fun _ => .done s)`).
- `promisePure_of_cells`: `PromisePure` for a program whose reachable
  thread states (an invariant `Jinv`) run either a cell writing no `Bad`
  message, or a single release store, where `Bad` covers every impure value
  of the release predicates: a promise of a `Bad` message is fulfilled (the
  path ends in a final configuration) by an instruction of its thread, which
  can then only be a release store, so the promise is `RelFulfilled`.
-/
import Kraken.Promising.SLR.Theorem1Proof
import Kraken.Promising.SLR.Lift
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR

open Kraken.Promising

variable {I : ISA}

/-! ## Writes that remove a promise -/

/-- A write that removes the outstanding promise `ts` writes the message at
`ts`. -/
theorem writeSuccs_unpromise {xr : View} {A : Arch} {tid : Nat} {iv : InstrViews} {c : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {c' : Ctx}
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) {ts : Time} (hin : ts ∈ c.prom) (hout : ts ∉ c'.prom) :
    ∃ w, c.mem.get? ts = some w ∧ w.loc = l ∧ w.val = v := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, w, hw, hl, hv, -, -, rfl⟩ | ⟨-, rfl⟩
  · simp only [afterWrite] at hout
    by_cases hne : ts = t
    · subst hne; exact ⟨w, hw, hl, hv⟩
    · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
  · exfalso
    apply hout
    simp only [afterWrite]
    by_cases hne : ts = c.mem.last + 1
    · subst hne
      rw [List.erase_append_left _ hin]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

/-- A write keeps the message at an existing timestamp. -/
theorem writeSuccs_get? {xr : View} {A : Arch} {tid : Nat} {iv : InstrViews} {c : Ctx} {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {c' : Ctx}
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) {ts : Time} {w : Msg} (hw : c.mem.get? ts = some w) :
    c'.mem.get? ts = some w := by
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, -, -, -, -, -, -, rfl⟩ | ⟨-, rfl⟩
  · exact hw
  · simp only [afterWrite]
    rw [Memory.get?_append_of_le _ _ _ (Memory.last_le_of_get?_eq_some _ hw)]
    exact hw

theorem fenceStep_mem_prom (c : Ctx) (k : FenceKind) :
    (fenceStep c k).mem = c.mem ∧ (fenceStep c k).prom = c.prom := by
  cases k <;> exact ⟨rfl, rfl⟩

private theorem mem_of_mem_ite_nil {α : Type} {p : Prop} [Decidable p] {x : α} {l : List α}
    (h : x ∈ (if p then [] else l)) : x ∈ l := by
  split at h
  · simp at h
  · exact h

/-- Every store and every RMW write of the tree satisfies `Q`. -/
def _root_.Kraken.Promising.EvTree.Writes {σ : Type} (Q : Loc → Val → Prop) : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, (k i).Writes Q
  | .load _ _ _ ret => ∀ v, (ret v).Writes Q
  | .store _ _ l v ret => Q l v ∧ ∀ b, (ret b).Writes Q
  | .rmw _ _ l op ret => (∀ old new, op old = some new → Q l new) ∧ ∀ v, (ret v).Writes Q
  | .fence _ ret => ∀ u, (ret u).Writes Q

/-- A run of a tree writing only `Q` that removes the outstanding promise
`ts` has `Q` at the message of `ts`. -/
theorem runTree_unpromise (A : Arch) (tid : Nat) (iv : InstrViews) {σ : Type} {Q : Loc → Val → Prop}
    {ts : Time} {w : Msg} :
    ∀ (tree : EvTree σ) (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      tree.Writes Q → ts ∈ c.prom → ts ∉ c'.prom → c.mem.get? ts = some w → Q w.loc w.val
  | .done _, c, s, c', h, _, hin, hout, _ => by
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact absurd hin hout
  | .fault _, c, s, c', h, _, _, _, _ => by simp [runTree] at h
  | .choose _ k, c, s, c', h, hQ, hin, hout, hw => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact runTree_unpromise A tid iv (k i) c s c' h (hQ i) hin hout hw
  | .load _ _ _ ret, c, s, c', h, hQ, hin, hout, hw => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    exact runTree_unpromise A tid iv _ _ s c' h (hQ _) (hp ▸ hin) hout (hm ▸ hw)
  | .store _ xcl l v ret, c, s, c', h, hQ, hin, hout, hw => by
    rw [runTree, List.mem_append] at h
    rcases h with h | h
    · have h := mem_of_mem_ite_nil h
      · rw [List.mem_flatMap] at h
        obtain ⟨c'', hc'', h⟩ := h
        by_cases hk : ts ∈ c''.prom
        · exact runTree_unpromise A tid iv _ c'' s c' h (hQ.2 true) hk hout (writeSuccs_get? hc'' hw)
        · obtain ⟨w', hw', hl, hv⟩ := writeSuccs_unpromise hc'' hin hk
          rw [hw] at hw'
          cases hw'
          rw [hl, hv]; exact hQ.1
    · split at h
      · exact runTree_unpromise A tid iv _ _ s c' h (hQ.2 false) hin hout hw
      · simp at h
  | .fence k ret, c, s, c', h, hQ, hin, hout, hw => by
    simp only [runTree] at h
    obtain ⟨hm, hp⟩ := fenceStep_mem_prom c k
    exact runTree_unpromise A tid iv _ _ s c' h (hQ ()) (hp ▸ hin) hout (hm ▸ hw)
  | .rmw k noRet l op ret, c, s, c', h, hQ, hin, hout, hw => by
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    have h0 : (if A.rmwFence then fenceStep c .sy else c).mem = c.mem ∧
        (if A.rmwFence then fenceStep c .sy else c).prom = c.prom := by
      split
      · exact fenceStep_mem_prom c .sy
      · exact ⟨rfl, rfl⟩
    obtain ⟨hm, hp⟩ := readSuccs_memProm A iv hx
    rw [h0.1] at hm
    rw [h0.2] at hp
    have hfp : ∀ c0 : Ctx, (if A.rmwFence then fenceStep c0 .sy else c0).mem = c0.mem ∧
        (if A.rmwFence then fenceStep c0 .sy else c0).prom = c0.prom := fun c0 => by
      split
      · exact fenceStep_mem_prom c0 .sy
      · exact ⟨rfl, rfl⟩
    split at h
    · obtain ⟨hm', hp'⟩ := hfp x.2.2
      exact runTree_unpromise A tid iv _ _ s c' h (hQ.2 _) (by rw [hp', hp]; exact hin) hout
        (by rw [hm', hm]; exact hw)
    · rename_i new hnew
      rw [List.mem_flatMap] at h
      obtain ⟨c'', hc'', h⟩ := h
      have hin' : ts ∈ x.2.2.prom := by rw [hp]; exact hin
      have hw' : x.2.2.mem.get? ts = some w := by rw [hm]; exact hw
      by_cases hk : ts ∈ c''.prom
      · refine runTree_unpromise A tid iv _ _ s c' h (hQ.2 _) ?_ hout ?_
        · rw [(hfp _).2]; split <;> exact hk
        · rw [(hfp _).1]; split <;> exact writeSuccs_get? hc'' hw'
      · obtain ⟨w', hw'', hl, hv⟩ := writeSuccs_unpromise hc'' hin' hk
        rw [hw'] at hw''
        cases hw''
        rw [hl, hv]; exact hQ.1 _ _ hnew

/-- An instruction whose tree writes only `Q` and that removes the
outstanding promise `ts` has `Q` at the message of `ts`. -/
theorem stepOne_unpromise (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {Q : Loc → Val → Prop} {tree : EvTree I.State}
    (hex : I.exec t.st = some tree) (hQ : tree.Writes Q) {ts : Time} (hin : ts ∈ t.prom)
    (hout : ts ∉ o.thread.prom) {w : Msg} (hw : mem.get? ts = some w) : Q w.loc w.val := by
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
    exact runTree_unpromise A tid _ tree _ st c' hr hQ hin hout hw

/-- **A fulfilling step by a release store is `Thread.RelFulfils`**: the
instruction is a single non-exclusive store whose effective kind is a
release, and the step removes the outstanding promise `ts`. -/
theorem relFulfils_of_store (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hk : A.storeKind k = .rel)
    {ts : Time} (hin : ts ∈ t.prom) (hout : ts ∉ o.thread.prom)
    (hlive : o.thread.hasDeadPromise o.mem = false) : t.RelFulfilsLive A tid ts mem := by
  refine ⟨_, hex, ?_⟩
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
    simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_flatMap, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨c'', hc'', -, rfl⟩ := hr
    exact .inl ⟨c', hc'', .inl ⟨⟨hk, hin, hout⟩, Ctx.noDead_of_finish hth hlive⟩⟩

/-! ## `PromisePure` from the program's cells -/

private theorem first_exit_aux {p : Nat → Prop} {a : Nat} (ha : p a) (b : Nat) :
    (∀ q, a ≤ q → q ≤ b → p q) ∨ ∃ f, a ≤ f ∧ f < b ∧ (∀ q, a ≤ q → q ≤ f → p q) ∧ ¬ p (f + 1) := by
  induction b with
  | zero =>
    left
    intro q h1 h2
    obtain rfl : q = 0 := by omega
    obtain rfl : a = 0 := by omega
    exact ha
  | succ b ih =>
    rcases ih with hl | ⟨f, hf1, hf2, hf3, hf4⟩
    · by_cases hp : p (b + 1)
      · left
        intro q h1 h2
        by_cases hq : q = b + 1
        · subst hq; exact hp
        · exact hl q h1 (by omega)
      · by_cases hab : a ≤ b
        · exact .inr ⟨b, hab, by omega, hl, hp⟩
        · left
          intro q h1 h2
          obtain rfl : q = b + 1 := by omega
          obtain rfl : a = b + 1 := by omega
          exact ha
    · exact .inr ⟨f, hf1, by omega, hf3, hf4⟩

/-- The first exit of a property that holds at `a` and fails at `b`. -/
theorem first_exit {p : Nat → Prop} {a : Nat} (ha : p a) (b : Nat) (hab : a ≤ b) (hb : ¬ p b) :
    ∃ f, a ≤ f ∧ f < b ∧ (∀ q, a ≤ q → q ≤ f → p q) ∧ ¬ p (f + 1) :=
  (first_exit_aux ha b).resolve_left fun h => hb (h b hab (Nat.le_refl _))

/-- **(O5) `PromisePure` from the program's cells.** `Bad` covers every
impure value of the release predicates `rel`. Every thread state reachable
from the initial configuration satisfies `Jinv`, and at such a state the
next instruction either writes no `Bad` message, or is a single release
store. A promise of a `Bad` message is outstanding until the final
configuration fails to hold it; the step that removes it is an instruction
of its own thread (a promise step only adds promises, another thread's step
leaves the thread alone), which writes the promised message: not a cell
without `Bad` writes, so a release store, and the promise is
`RelFulfilled`. -/
theorem promisePure_of_cells [I.LawfulState] {A : Arch} {fuel : Nat} {states : List I.State}
    {initMem : List (Loc × Val)} {rel : Loc → Pred} (Bad : Loc → Val → Prop)
    (hrel : ∀ l v, ¬ Bad l v → Pred.Pure (rel l) v) (Jinv : I.State → Prop)
    (hJ : ∀ c, Reachable A fuel (Config.init states initMem) c → ∀ (tid : Nat) (t : Thread I), c.threads[tid]? = some t → Jinv t.st)
    (hcell : ∀ st tree, Jinv st → I.exec st = some tree →
      tree.Writes (fun l v => ¬ Bad l v) ∨
        ∃ k l v s, A.storeKind k = .rel ∧ tree = .store k false l v (fun _ => .done s)) :
    PromisePure A fuel states initMem rel := by
  intro π h0 hfin J hJl j t pw htJ _ hstep hnot
  apply Classical.byContradiction
  intro hpure
  have hbad : Bad pw.1.loc pw.1.val := Classical.byContradiction fun hb => hpure (hrel _ _ hb)
  apply hnot
  -- the promise `ts` of `j`, outstanding from `J + 1`
  let ts := (π.cfg J).mem.last + 1
  let p : Nat → Prop := fun q => ∃ tq, (π.cfg q).threads[j]? = some tq ∧ ts ∈ tq.prom
  have hjn := lt_size_of_get? htJ
  have hp1 : p (J + 1) := by
    refine ⟨{ t with prom := t.prom ++ [((π.cfg J).mem.append { pw.1 with tid := j }).2] },
      by rw [hstep, Config.withThread_get? _ _ _ hjn]; simp only [↓reduceIte], ?_⟩
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have hpl : ¬ p π.len := fun ⟨tq, htq, hts⟩ => by
    rw [Config.final_prom hfin htq] at hts; cases hts
  obtain ⟨f, hf1, hf2, hf3, hf4⟩ := first_exit hp1 π.len (by omega) hpl
  obtain ⟨tf, htf, htsf⟩ := hf3 f hf1 (Nat.le_refl _)
  -- the promised message stays at `ts`
  have hwJ : (π.cfg (J + 1)).mem.get? ts = some { pw.1 with tid := j } := by
    rw [hstep]; exact Memory.get?_append_last _ _
  have hwf : (π.cfg f).mem.get? ts = some { pw.1 with tid := j } := by
    rw [(π.mem_prefix hf1 (by omega)).get? (by
      rw [hstep]; simp only [Config.withThread, Memory.last_append]; exact Nat.le_refl _)]
    exact hwJ
  -- the step `f`
  have hsame : ∀ i (th : Thread I) mem, i ≠ j → π.cfg (f + 1) = (π.cfg f).withThread i th mem →
      (π.cfg f).threads[i]? ≠ none → False := fun i th mem hij he hi => by
    apply hf4
    refine ⟨tf, ?_, htsf⟩
    rw [he, Config.withThread_get? _ _ _ (by
      cases h : (π.cfg f).threads[i]? with
      | none => exact absurd h hi
      | some _ => exact lt_size_of_get? h)]; simp only [hij, ↓reduceIte]
    exact htf
  have hs := succs_cases (π.step f hf2)
  generalize hc1 : π.cfg (f + 1) = c1 at hs
  cases hs with
  | @instr i ti outs o hti hstepi hoi =>
    by_cases hij : i = j
    · subst hij
      rw [hti] at htf
      obtain rfl : ti = tf := Option.some.inj htf
      have hout : ts ∉ o.thread.prom := fun h => hf4 ⟨o.thread, by
        rw [hc1, Config.withThread_get? _ _ _ (lt_size_of_get? hti)]; simp only [↓reduceIte], h⟩
      have hJf := hJ _ (h0 ▸ π.reachable f (by omega)) i ti hti
      cases hex : I.exec ti.st with
      | none => unfold stepOne at hstepi; rw [hex] at hstepi; cases hstepi
      | some tree =>
        rcases hcell _ tree hJf hex with hW | ⟨k, l, v, s, hk, rfl⟩
        · exact ((stepOne_unpromise (w := { pw.1 with tid := i }) A hstepi hoi hex hW htsf hout hwf) hbad).elim
        · have hthf : (π.cfg (f + 1)).threads[i]? = some o.thread := by
            rw [hc1, Config.withThread_get? _ _ _ (lt_size_of_get? hti)]; simp only [↓reduceIte]
          have hlive : o.thread.hasDeadPromise o.mem = false := by
            have h := liveWfProm A fuel states initMem _ (by rw [← h0]; exact π.reachable (f + 1) hf2)
              (π.live hfin (f + 1) hf2) i o.thread hthf
            rw [hc1] at h; exact h
          refine ⟨f, by omega, hf2, fun q h1 h2 => hf3 q (by omega) h2, ti, o.thread, hti,
            relFulfils_of_store A hstepi hoi hex hk htsf hout hlive, ?_, hout⟩
          rw [hc1, Config.withThread_get? _ _ _ (lt_size_of_get? hti)]; simp only [↓reduceIte]
    · exact (hsame i o.thread o.mem hij hc1 (by rw [hti]; simp)).elim
  | @promise i ti pw' hti _ =>
    by_cases hij : i = j
    · subst hij
      rw [hti] at htf
      obtain rfl : ti = tf := Option.some.inj htf
      exact (hf4 ⟨{ ti with prom := ti.prom ++ [((π.cfg f).mem.append { pw'.1 with tid := i }).2] },
        by rw [hc1, Config.withThread_get? _ _ _ (lt_size_of_get? hti)]; simp only [↓reduceIte],
        List.mem_append_left _ htsf⟩).elim
    · exact (hsame i _ _ hij hc1 (by rw [hti]; simp)).elim

end Kraken.Promising.SLR

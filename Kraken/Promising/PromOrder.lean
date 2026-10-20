/-
Promise sets are sorted, and fulfilment raises `vwAll` (case (d) of
Theorem 1′'s induction).

Two machine facts about outstanding promises:

- **Sortedness** (`Config.PromSorted`): every thread's promise list is
  strictly increasing. A promise step appends `|M| + 1`, above every
  outstanding promise (`Config.Wf`); an instruction only erases promises
  (`fulfil`), or appends and erases the fresh `|M| + 1` ("promise now"). So
  restricting a thread's promises to a memory prefix is a prefix of its
  promise list (used to add a new promise to an advanced thread's virtual
  state).
- **Fulfilment raises `vwAll`** (`stepOne_fulfil`): an instruction that
  removes an outstanding promise `ts` of its thread leaves `ts ≤ vwAll`
  (`afterWrite` raises `vwOld`, or `vwOldNT` for a non-temporal store, to the
  timestamp written). Since `vwOld` enters a release store's pre-view
  (`Thread.RelFulfils.relPre_lt`), a thread that has fulfilled `ts` cannot
  later fulfil a smaller promise with a release store.

Machine facts only; no hypothesis on the program.
-/
import Kraken.Promising.ReleasePrefixNT

namespace Kraken.Promising

open Kraken.Promising.Live.Bridge

variable {I : ISA}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

private theorem mem_ite_nil'' {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α}
    (h : x ∈ (if p then ys else [])) : x ∈ ys := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

private theorem ite_none_left'' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

/-! ## One context step -/

/-- Promises `c` had and `c'` lost lie at or below `c'`'s `vwAll`. -/
def Ctx.FulfilBound (c c' : Ctx) : Prop :=
  ∀ ts ∈ c.prom, ts ∉ c'.prom → ts ≤ c'.views.vwAll

theorem Ctx.FulfilBound.of_prom {c c' : Ctx} (hp : c'.prom = c.prom) : c.FulfilBound c' :=
  fun _ h h' => absurd (hp ▸ h) h'

theorem Ctx.FulfilBound.trans {c c1 c' : Ctx} (h1 : c.FulfilBound c1) (hs : c1.Silent c')
    (h2 : c1.FulfilBound c') : c.FulfilBound c' := fun ts hin hout => by
  by_cases h : ts ∈ c1.prom
  · exact h2 ts h hout
  · exact Nat.le_trans (h1 ts hin h) hs.vwAll

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_prom {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : x.2.2.prom = c.prom := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left'' ht
    simp only [Option.some.injEq] at h
    subst h
    rfl

theorem writeSuccs_fulfilBound {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c.FulfilBound c' := by
  intro ts hin hout
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp only [afterWrite] at hout
      have hts : ts = t := by
        by_cases hne : ts = t
        · exact hne
        · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
      subst hts
      simp only [afterWrite, Views.vwAll, Views.setCoh]
      split <;> omega_t
    · cases h
  · have h := mem_ite_nil'' h
    rw [List.mem_singleton] at h
    subst h
    exfalso
    apply hout
    simp only [afterWrite]
    by_cases hne : ts = c.mem.msgs.size + 1
    · subst hne
      rw [List.erase_append_left _ hin]
      exact List.mem_append_right _ (List.mem_singleton_self _)
    · exact (List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)

theorem writeSuccs_sorted {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hb : ∀ p ∈ c.prom, p ≤ c.mem.last) (hs : c.prom.Pairwise (· < ·)) : c'.prom.Pairwise (· < ·) := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      exact hs.sublist (List.erase_sublist)
    · cases h
  · have h := mem_ite_nil'' h
    rw [List.mem_singleton] at h
    subst h
    simp only [afterWrite]
    refine List.Pairwise.sublist List.erase_sublist ?_
    rw [List.pairwise_append]
    refine ⟨hs, List.pairwise_singleton _ _, fun a ha b hb' => ?_⟩
    rw [List.mem_singleton] at hb'
    subst hb'
    have := hb a ha
    simp only [Memory.last] at this
    omega_t

end Rules

/-! ## Event trees -/

section Tree

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem runTree_fulfil {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.views.FwdOk → .ok (s, c') ∈ runTree A tid iv c tree → c.FulfilBound c' := by
  induction tree with
  | done s0 =>
    intro c s c' _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact .of_prom rfl
  | fault msg => intro c s c' _ h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' hf h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hf hi
  | load k xcl l ret ih =>
    intro c s c' hf h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hs0 := readSuccs_silent A iv hf h0
    exact (Ctx.FulfilBound.of_prom (readSuccs_prom A iv h0)).trans (runTree_silent A tid iv _ _ _ _ hs0.fwd h)
      (ih v c0 s c' hs0.fwd h)
  | store k xcl l v ret ih =>
    intro c s c' hf h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      have hs0 := writeSuccs_silent A tid _ hf hc0
      exact (writeSuccs_fulfilBound A tid _ hc0).trans (runTree_silent A tid iv _ _ _ _ hs0.fwd h)
        (ih true c0 s c' hs0.fwd h)
    · rw [List.mem_ite_nil_right] at h
      have hs0 : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      have hb0 : c.FulfilBound
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_prom rfl
      exact hb0.trans (runTree_silent A tid iv _ _ _ _ hs0.fwd h.2) (ih false _ s c' hs0.fwd h.2)
  | fence k ret ih =>
    intro c s c' hf h
    simp only [runTree] at h
    have hs0 := Ctx.Silent.fenceStep hf k
    exact (Ctx.FulfilBound.of_prom (fenceStep_fields c k).2.2.2.2.1).trans
      (runTree_silent A tid iv _ _ _ _ hs0.fwd h) (ih () _ s c' hs0.fwd h)
  | rmw k noRet l op ret ih =>
    intro c s c' hf h
    simp only [runTree] at h
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have hp1 : (if A.rmwFence then fenceStep c .sy else c).prom = c.prom := by
      cases A.rmwFence
      · rfl
      · exact (fenceStep_fields c .sy).2.2.2.2.1
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1 hp1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : c.Silent c2 := h1.trans (readSuccs_silent A iv h1.fwd h2)
    have hp2 : c2.prom = c.prom := (readSuccs_prom A iv h2).trans hp1
    simp only at h
    split at h
    · have h3 := Ctx.Silent.fenceOpt h12.fwd A.rmwFence .sy
      have hp3 : (if A.rmwFence then fenceStep c2 .sy else c2).prom = c.prom := by
        cases A.rmwFence
        · exact hp2
        · exact (fenceStep_fields c2 .sy).2.2.2.2.1.trans hp2
      exact (Ctx.FulfilBound.of_prom hp3).trans (runTree_silent A tid iv _ _ _ _ h3.fwd h)
        (ih old _ s c' h3.fwd h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have hs3 := writeSuccs_silent A tid _ h12.fwd hc3
      have hb3 : c2.FulfilBound c3 := writeSuccs_fulfilBound A tid _ hc3
      have h4 : c3.Silent (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) :=
        (Ctx.Silent.rmwPost hs3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt (Ctx.Silent.rmwPost hs3.fwd A k noRet l).fwd _ _)
      have hp4 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3).prom =
          c3.prom := by
        have : (rmwPost A k noRet l c3).prom = c3.prom := by
          unfold rmwPost; split <;> rfl
        cases A.rmwFence
        · exact this
        · exact (fenceStep_fields _ .sy).2.2.2.2.1.trans this
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      have hrest := runTree_silent A tid iv _ _ _ _ h4.fwd h
      have hb34 : c3.FulfilBound c' :=
        (Ctx.FulfilBound.of_prom hp4).trans hrest (ih old _ s c' h4.fwd h)
      have hb24 : c2.FulfilBound c' := hb3.trans (h4.trans hrest) hb34
      exact (Ctx.FulfilBound.of_prom hp2).trans (h4.trans hrest |> hs3.trans) hb24

theorem runTree_sorted {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.views.FwdOk → (∀ p ∈ c.prom, p ≤ c.mem.last) →
      c.prom.Pairwise (· < ·) → .ok (s, c') ∈ runTree A tid iv c tree → c'.prom.Pairwise (· < ·) := by
  induction tree with
  | done s0 =>
    intro c s c' _ _ hs h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact hs
  | fault msg => intro c s c' _ _ _ h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' hf hb hs h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hf hb hs hi
  | load k xcl l ret ih =>
    intro c s c' hf hb hs h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hs0 := readSuccs_silent A iv hf h0
    exact ih v c0 s c' hs0.fwd (hs0.prom hb) (by rw [readSuccs_prom A iv h0]; exact hs) h
  | store k xcl l v ret ih =>
    intro c s c' hf hb hs h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      have hs0 := writeSuccs_silent A tid _ hf hc0
      exact ih true c0 s c' hs0.fwd (hs0.prom hb) (writeSuccs_sorted A tid _ hc0 hb hs) h
    · rw [List.mem_ite_nil_right] at h
      have hs0 : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact ih false _ s c' hs0.fwd (hs0.prom hb) hs h.2
  | fence k ret ih =>
    intro c s c' hf hb hs h
    simp only [runTree] at h
    have hs0 := Ctx.Silent.fenceStep hf k
    exact ih () _ s c' hs0.fwd (hs0.prom hb) (by rw [(fenceStep_fields c k).2.2.2.2.1]; exact hs) h
  | rmw k noRet l op ret ih =>
    intro c s c' hf hb hs h
    simp only [runTree] at h
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have hp1 : (if A.rmwFence then fenceStep c .sy else c).prom = c.prom := by
      cases A.rmwFence
      · rfl
      · exact (fenceStep_fields c .sy).2.2.2.2.1
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1 hp1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : c.Silent c2 := h1.trans (readSuccs_silent A iv h1.fwd h2)
    have hp2 : c2.prom = c.prom := (readSuccs_prom A iv h2).trans hp1
    simp only at h
    split at h
    · have h3 := Ctx.Silent.fenceOpt h12.fwd A.rmwFence .sy
      have hp3 : (if A.rmwFence then fenceStep c2 .sy else c2).prom = c.prom := by
        cases A.rmwFence
        · exact hp2
        · exact (fenceStep_fields c2 .sy).2.2.2.2.1.trans hp2
      exact ih old _ s c' h3.fwd ((h12.trans h3).prom hb) (by rw [hp3]; exact hs) h
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have hs3 := writeSuccs_silent A tid _ h12.fwd hc3
      have hsort3 := writeSuccs_sorted A tid _ hc3 (h12.prom hb) (by rw [hp2]; exact hs)
      have h4 : c3.Silent (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) :=
        (Ctx.Silent.rmwPost hs3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt (Ctx.Silent.rmwPost hs3.fwd A k noRet l).fwd _ _)
      have hp4 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3).prom =
          c3.prom := by
        have : (rmwPost A k noRet l c3).prom = c3.prom := by
          unfold rmwPost; split <;> rfl
        cases A.rmwFence
        · exact this
        · exact (fenceStep_fields _ .sy).2.2.2.2.1.trans this
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      exact ih old _ s c' h4.fwd (((h12.trans hs3).trans h4).prom hb) (by rw [hp4]; exact hsort3) h

end Tree

/-! ## One instruction -/

/-- **Fulfilment raises `vwAll`**: a promise an instruction removes from its
thread's promise set lies at or below the thread's new `vwAll`. -/
theorem stepOne_fulfil (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) :
    ∀ ts ∈ t.prom, ts ∉ o.thread.prom → ts ≤ o.thread.views.vwAll := by
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
      have hb := runTree_fulfil A tid _ tree _ st c' hf hr
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      obtain ⟨-, hvw, -⟩ := Views.relPre_congr hv
      have hnt := Views.vwOldNT_congr hv
      have hall : th.views.vwAll = c'.views.vwAll := by simp only [Views.vwAll, hvw, hnt]
      intro ts h1 h2
      simp only [hp] at h2
      rw [hall]
      exact hb ts h1 h2

/-- **An instruction keeps its thread's promises sorted** (given that they
are below `|M|`). -/
theorem stepOne_sorted (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) (hb : ∀ p ∈ t.prom, p ≤ mem.last)
    (hs : t.prom.Pairwise (· < ·)) : o.thread.prom.Pairwise (· < ·) := by
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
      obtain ⟨hp, -⟩ := finishInstr_relKey hth
      simp only [hp]
      exact runTree_sorted A tid _ tree _ st c' hf hb hs hr

/-! ## Configurations -/

/-- Every thread's promise list is strictly increasing. -/
def Config.PromSorted (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.prom.Pairwise (· < ·)

theorem Config.init_promSorted (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem : Config I).PromSorted := by
  intro i t h
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  exact List.Pairwise.nil

theorem Config.PromSorted.succ {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (hs : c.PromSorted) (h : SuccKind A c c') : c'.PromSorted := by
  cases h with
  | @instr tid t outs o ht hstep ho =>
    intro i t' hi
    rw [Config.withThread_get? c _ _ (lt_size_of_get? ht)] at hi
    split at hi
    · cases hi
      exact stepOne_sorted A hstep ho (hwf tid t ht).1 (hwf tid t ht).2 (hs tid t ht)
    · exact hs i t' hi
  | @promise tid t pw ht _ =>
    intro i t' hi
    rw [Config.withThread_get? c _ _ (lt_size_of_get? ht)] at hi
    split at hi
    · cases hi
      simp only
      rw [List.pairwise_append]
      refine ⟨hs tid t ht, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      have := (hwf tid t ht).2 a ha
      show a < c.mem.last + 1
      omega_t
    · exact hs i t' hi

theorem Config.PromSorted.reachable {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (hs : c.PromSorted) (h : ReachableK A c c') : c'.PromSorted := by
  induction h with
  | refl => exact hs
  | step hst _ ih => exact ih (hwf.succ hst) (hs.succ hwf hst)

/-- In a sorted promise list containing `L + 1`, the promises up to `L + 1`
are those up to `L`, then `L + 1`. -/
theorem filter_le_succ_of_sorted {l : List Time} (hs : l.Pairwise (· < ·)) {L : Time} (hm : L + 1 ∈ l) :
    l.filter (fun x => decide (x ≤ L + 1)) = l.filter (fun x => decide (x ≤ L)) ++ [L + 1] := by
  induction l with
  | nil => simp at hm
  | cons a l ih =>
    rw [List.pairwise_cons] at hs
    by_cases ha : a = L + 1
    · subst ha
      have h1 : l.filter (fun x => decide (x ≤ L + 1)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by have := hs.1 b hb; simp only [decide_eq_true_eq]; omega_t
      have h2 : l.filter (fun x => decide (x ≤ L)) = [] :=
        List.filter_eq_nil_iff.mpr fun b hb => by have := hs.1 b hb; simp only [decide_eq_true_eq]; omega_t
      have e1 : ¬ (L + 1 ≤ L) := by omega_t
      simp [h1, h2, e1]
    · have hm' : L + 1 ∈ l := by
        rcases List.mem_cons.mp hm with h | h
        · exact absurd h.symm ha
        · exact h
      have hal : a ≤ L := by have := hs.1 _ hm'; omega_t
      have e2 : a ≤ L + 1 := by omega_t
      simp [e2, hal, ih hs.2 hm']

/-- **Thread `t` has the promise `ts` outstanding, or has passed it**: its
`relPre` or `vwOldNT` is at least `ts` (after fulfilling `ts`,
`stepOne_fulfil`). -/
def Thread.HasOrPassed (t : Thread I) (ts : Time) : Prop :=
  ts ∈ t.prom ∨ ts ≤ max t.views.relPre t.views.vwOldNT

/-- `Thread.HasOrPassed` is kept by every machine step. -/
theorem Thread.HasOrPassed.succ {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (h : SuccKind A c c') {j : Nat} {t : Thread I} (ht : c.threads[j]? = some t) {ts : Time}
    (hp : t.HasOrPassed ts) : ∃ t', c'.threads[j]? = some t' ∧ t'.HasOrPassed ts := by
  cases h with
  | @instr tid t0 outs o ht0 hstep ho =>
    rw [Config.withThread_get? c _ _ (lt_size_of_get? ht0)]
    by_cases hj : tid = j
    · subst hj
      rw [ht] at ht0; cases ht0
      refine ⟨o.thread, by rw [ite_eq_left rfl], ?_⟩
      obtain ⟨hrel, hnt, -⟩ := stepOne_silent_nt A hstep ho (hwf tid t ht).1
      rcases hp with hp | hp
      · by_cases ho' : ts ∈ o.thread.prom
        · exact .inl ho'
        · right
          have := stepOne_fulfil A hstep ho (hwf tid t ht).1 ts hp ho'
          simp only [Views.vwAll, Views.relPre] at this ⊢
          omega_t
      · right; omega_t
    · exact ⟨t, by rw [ite_eq_right hj]; exact ht, hp⟩
  | @promise tid t0 pw ht0 _ =>
    rw [Config.withThread_get? c _ _ (lt_size_of_get? ht0)]
    by_cases hj : tid = j
    · subst hj
      rw [ht] at ht0; cases ht0
      refine ⟨_, by rw [ite_eq_left rfl], ?_⟩
      rcases hp with hp | hp
      · exact .inl (List.mem_append_left _ hp)
      · exact .inr hp
    · exact ⟨t, by rw [ite_eq_right hj]; exact ht, hp⟩

theorem Thread.HasOrPassed.reachable {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (h : ReachableK A c c') {j : Nat} {t : Thread I} (ht : c.threads[j]? = some t) {ts : Time}
    (hp : t.HasOrPassed ts) : ∃ t', c'.threads[j]? = some t' ∧ t'.HasOrPassed ts := by
  induction h generalizing t with
  | refl => exact ⟨t, ht, hp⟩
  | step hst _ ih =>
    obtain ⟨t1, ht1, hp1⟩ := hp.succ hwf hst ht
    exact ih (hwf.succ hst) ht1 hp1

/-! ## Promises do not come back -/

section Sub

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem writeSuccs_promSub {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hb : ∀ p ∈ c.prom, p ≤ c.mem.last) : ∀ x ∈ c'.prom, x ∈ c.prom := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      exact fun x hx => List.mem_of_mem_erase hx
    · cases h
  · have h := mem_ite_nil'' h
    rw [List.mem_singleton] at h
    subst h
    have hnot : c.mem.msgs.size + 1 ∉ c.prom := fun hm => by
      have := hb _ hm; simp only [Memory.last] at this; omega_t
    intro x hx
    simp only [afterWrite, List.erase_append_right _ hnot, List.erase_cons_head,
      List.append_nil] at hx
    exact hx

theorem runTree_promSub {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.views.FwdOk → (∀ p ∈ c.prom, p ≤ c.mem.last) →
      .ok (s, c') ∈ runTree A tid iv c tree → ∀ x ∈ c'.prom, x ∈ c.prom := by
  induction tree with
  | done s0 =>
    intro c s c' _ _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact fun _ h => h
  | fault msg => intro c s c' _ _ h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' hf hb h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hf hb hi
  | load k xcl l ret ih =>
    intro c s c' hf hb h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have hs0 := readSuccs_silent A iv hf h0
    intro x hx
    have := ih v c0 s c' hs0.fwd (hs0.prom hb) h x hx
    rwa [readSuccs_prom A iv h0] at this
  | store k xcl l v ret ih =>
    intro c s c' hf hb h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      have hs0 := writeSuccs_silent A tid _ hf hc0
      exact fun x hx => writeSuccs_promSub A tid _ hc0 hb x (ih true c0 s c' hs0.fwd (hs0.prom hb) h x hx)
    · rw [List.mem_ite_nil_right] at h
      have hs0 : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact ih false { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
        s c' hs0.fwd (hs0.prom hb) h.2
  | fence k ret ih =>
    intro c s c' hf hb h
    simp only [runTree] at h
    have hs0 := Ctx.Silent.fenceStep hf k
    intro x hx
    have := ih () _ s c' hs0.fwd (hs0.prom hb) h x hx
    rwa [(fenceStep_fields c k).2.2.2.2.1] at this
  | rmw k noRet l op ret ih =>
    intro c s c' hf hb h
    simp only [runTree] at h
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have hp1 : (if A.rmwFence then fenceStep c .sy else c).prom = c.prom := by
      cases A.rmwFence
      · rfl
      · exact (fenceStep_fields c .sy).2.2.2.2.1
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1 hp1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : c.Silent c2 := h1.trans (readSuccs_silent A iv h1.fwd h2)
    have hp2 : c2.prom = c.prom := (readSuccs_prom A iv h2).trans hp1
    simp only at h
    split at h
    · have h3 := Ctx.Silent.fenceOpt h12.fwd A.rmwFence .sy
      have hp3 : (if A.rmwFence then fenceStep c2 .sy else c2).prom = c.prom := by
        cases A.rmwFence
        · exact hp2
        · exact (fenceStep_fields c2 .sy).2.2.2.2.1.trans hp2
      intro x hx
      have := ih old _ s c' h3.fwd ((h12.trans h3).prom hb) h x hx
      rwa [hp3] at this
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have hs3 := writeSuccs_silent A tid _ h12.fwd hc3
      have hsub3 := writeSuccs_promSub A tid _ hc3 (h12.prom hb)
      have h4 : c3.Silent (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) :=
        (Ctx.Silent.rmwPost hs3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt (Ctx.Silent.rmwPost hs3.fwd A k noRet l).fwd _ _)
      have hp4 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3).prom =
          c3.prom := by
        have : (rmwPost A k noRet l c3).prom = c3.prom := by
          unfold rmwPost; split <;> rfl
        cases A.rmwFence
        · exact this
        · exact (fenceStep_fields _ .sy).2.2.2.2.1.trans this
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      intro x hx
      have := ih old _ s c' h4.fwd (((h12.trans hs3).trans h4).prom hb) h x hx
      rw [hp4] at this
      have := hsub3 x this
      rwa [hp2] at this

end Sub

/-- **An instruction only removes promises** (given that they are below
`|M|`). -/
theorem stepOne_promSub (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) (hb : ∀ p ∈ t.prom, p ≤ mem.last) :
    ∀ x ∈ o.thread.prom, x ∈ t.prom := by
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
      obtain ⟨hp, -⟩ := finishInstr_relKey hth
      simp only [hp]
      exact runTree_promSub A tid _ tree _ st c' hf hb hr

/-- **A promise, once gone, does not come back**: a timestamp in memory that
is not an outstanding promise of thread `j` is not one in any successor. -/
theorem Thread.notProm_succ {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (h : SuccKind A c c') {j : Nat} {ts : Time} (hle : ts ≤ c.mem.last)
    (hn : ∀ t, c.threads[j]? = some t → ts ∉ t.prom) : ∀ t', c'.threads[j]? = some t' → ts ∉ t'.prom := by
  cases h with
  | @instr tid t0 outs o ht0 hstep ho =>
    intro t' ht'
    rw [Config.withThread_get? c _ _ (lt_size_of_get? ht0)] at ht'
    split at ht'
    · next he =>
      subst he; cases ht'
      exact fun hm => hn t0 ht0 (stepOne_promSub A hstep ho (hwf _ t0 ht0).1 (hwf _ t0 ht0).2 ts hm)
    · exact hn t' ht'
  | @promise tid t0 pw ht0 _ =>
    intro t' ht'
    rw [Config.withThread_get? c _ _ (lt_size_of_get? ht0)] at ht'
    split at ht'
    · next he =>
      subst he; cases ht'
      intro hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hn t0 ht0 hm
      · rw [List.mem_singleton] at hm
        have : (c.mem.append { pw.1 with tid := tid }).2 = c.mem.last + 1 := rfl
        omega_t
    · exact hn t' ht'

theorem Thread.notProm_reachable {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (h : ReachableK A c c') {j : Nat} {ts : Time} (hle : ts ≤ c.mem.last)
    (hn : ∀ t, c.threads[j]? = some t → ts ∉ t.prom) : ∀ t', c'.threads[j]? = some t' → ts ∉ t'.prom := by
  induction h with
  | refl => exact hn
  | step hst hr ih =>
    have hpre := (ReachableK.single hst).mem_prefix
    exact ih (hwf.succ hst) (Nat.le_trans hle hpre.last_le) (Thread.notProm_succ hwf hst hle hn)

/-- No dead promise after restriction to a memory prefix. -/
theorem Thread.hasDeadPromise_restrict {t : Thread I} {M M' : Memory} (hM : M.Prefix M')
    (h : t.hasDeadPromise M' = false) : (t.restrict M).hasDeadPromise M = false := by
  simp only [Thread.hasDeadPromise, List.any_eq_false] at h ⊢
  intro p hp
  simp only [Thread.restrict, List.mem_filter, decide_eq_true_eq] at hp
  rw [← hM.get? hp.2]
  exact h p hp.1

end Kraken.Promising

/-
Design (V)'s machine facts: the
release pre-view makes a thread *silent* before a release store.

A release store's pre-view (`writeSuccs`) includes
`relPre = vrOld ⊔ vrOldNR ⊔ vwOld`, and its timestamp lies above it. `relPre`
bounds every read and every write the thread has performed (`Ctx.Silent`):
a fresh write ("promise now") puts `vwOld` above the old `|M|`, and a read of
timestamp `t` puts `vrOld` or `vrOldNR` at `t` or above, except a read
forwarded from the thread's own write, whose timestamp is at most `vwOld`
(`Views.FwdOk`, an invariant of every reachable configuration). Views only
grow. So while a promise `ts ≤ |M|` is outstanding and the thread's state is
*release-bounded* for it (`relPre < ts`, which every state before a release
store fulfilling `ts` is, `EvTree.RelFulfils.relPre_lt`), each of its
instructions appends nothing and reads only messages below `ts`:

- `stepOne_silent`, `stutterStep_of_relPre`: one instruction (S2);
- `stutterStep_path`: (S2) on machine paths: every instruction of the thread
  between a configuration and a later one where it is release-bounded (e.g.
  its next instruction is a release store fulfilling `ts`) is a
  `StutterStep`;
- `Config.Wf` (`FwdOk` and "every promise is a message") holds in every
  configuration reachable from a well-formed one (`Config.Wf.reachable`;
  `Config.init_wf`), so no hypothesis restricts programs.

Nothing here depends on certification: (S2) is a consequence of the views,
and holds of raw `stepOne` outcomes. (S1′) is in the second part of the file.

**Non-temporal stores (x86 `movnti`): a temporary restriction of
the logic only.** A non-temporal store raises `vwOldNT`, not `vwOld`, and a
later release store's pre-view does not include it (the SDM lets an ordinary
store overtake an older `movnti`). So a thread with an outstanding release
promise may still append a non-temporal message, and the unrestricted (S2)
and (S1′) are false. The internal lemmas are stated for the general machine
(`stepOne_silent_nt`, `Ctx.Silent` with `vwAll`/`relPreNT`); the (S2)/(S1′)
theorems take, as their last arguments, `Thread.NoNTStores` (no non-temporal
store at or after `ts`) and, for (S1′), `Thread.NextNoNT`. Both hold for
every reachable thread under `Arch.armv8` (`Thread.noNTStores_armv8`,
`Thread.nextNoNT_armv8`), so only x86 programs using `movnti` are excluded.
The machine semantics is unaffected.

*The restriction lifted:* `Kraken/Promising/ReleasePrefixNT.lean` proves (S2′)
(`stutterStepNT_release`) and (S1′) (`Config.advanceableNT_of_path`, to
`Config.AdvanceableNT`) for every program with no non-temporal hypothesis,
and `Config.VirtualOfNT`/`VirtualRel.nt`. The restricted statements here are
the special case in which the advancing run appends nothing
(`Config.Advanceable.advanceableNT`).
-/
import Kraken.Promising.PromiseSafe
import Kraken.Promising.ReachableK

namespace Kraken.Promising

open Kraken.Promising.Live.Bridge

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

private theorem ite_none_left' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

private theorem ite_none_right' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then y else none) = some x) : y = some x := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

private theorem mem_ite_nil' {α : Type} {p : Prop} [Decidable p] {ys : List α} {x : α}
    (h : x ∈ (if p then ys else [])) : x ∈ ys := by
  by_cases hp : p
  · rwa [ite_eq_left hp] at h
  · rw [ite_eq_right hp] at h; cases h

/-! ## Release-bounded views -/

/-- The part of a release store's pre-view that the thread's own accesses
raise: every earlier read (`vrOld`, `vrOldNR`) and write (`vwOld`). -/
def Views.relPre (vs : Views) : View := max (max vs.vrOld vs.vrOldNR) vs.vwOld

/-- Every write of the thread, ordinary (`vwOld`) or non-temporal (`vwOldNT`)
lies at or below `vwAll`. -/
def Views.vwAll (vs : Views) : View := max vs.vwOld vs.vwOldNT

/-- `relPre` together with the thread's non-temporal writes: a bound on every
access the thread has performed. A release store's pre-view does not include
the non-temporal writes (they may become visible after it), so only `relPre`
is below a release store's timestamp. -/
def Views.relPreNT (vs : Views) : View := max vs.relPre vs.vwOldNT

theorem Views.vwAll_le_relPreNT (vs : Views) : vs.vwAll ≤ vs.relPreNT := by
  simp only [vwAll, relPreNT, relPre]; omega_t

theorem Views.relPre_le_relPreNT (vs : Views) : vs.relPre ≤ vs.relPreNT := by
  simp only [relPreNT]; omega_t

/-- Every store-forwarding entry is a write of the thread, at most `vwAll`. -/
def Views.FwdOk (vs : Views) : Prop := ∀ p ∈ vs.fwdb, p.2.time ≤ vs.vwAll

theorem Views.mem_setSorted {β : Type} {xs : List (Loc × β)} {l : Loc} {b : β} {p : Loc × β}
    (h : p ∈ setSorted xs l b) : p = (l, b) ∨ p ∈ xs := by
  induction xs with
  | nil => simp only [setSorted, List.mem_singleton] at h; exact .inl h
  | cons q rest ih =>
    simp only [setSorted] at h
    split at h
    · rcases List.mem_cons.mp h with h | h
      · exact .inl h
      · exact .inr h
    · rcases List.mem_cons.mp h with h | h
      · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
    · rcases List.mem_cons.mp h with h | h
      · exact .inr (h ▸ List.mem_cons_self)
      · rcases ih h with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)

theorem Views.getFwd_mem {vs : Views} {l : Loc} {f : FwdItem} (h : vs.getFwd l = some f) : (l, f) ∈ vs.fwdb := by
  unfold getFwd at h
  cases hf : vs.fwdb.find? (·.1 == l) with
  | none => rw [hf] at h; cases h
  | some p =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hp := List.mem_of_find?_eq_some hf
    have hl := List.find?_some hf
    simp only [beq_iff_eq] at hl
    obtain ⟨l', f'⟩ := p
    simp only at hl h
    subst hl h
    exact hp

/-! ## What an instruction's run preserves -/

/-- From `c` to `c'` along an instruction's event tree: the views a release
pre-view takes, and `vwOldNT`, only grow; forwarding entries stay below
`vwAll`; memory is unchanged unless `vwAll` passed the old `|M|`; every read
logged since `c` is at most `relPreNT` (a read may forward from the thread's
own non-temporal write); every outstanding promise stays a message. -/
structure Ctx.Silent (c c' : Ctx) : Prop where
  vrOld : c.views.vrOld ≤ c'.views.vrOld
  vrOldNR : c.views.vrOldNR ≤ c'.views.vrOldNR
  vwOld : c.views.vwOld ≤ c'.views.vwOld
  vwOldNT : c.views.vwOldNT ≤ c'.views.vwOldNT
  fwd : c'.views.FwdOk
  mem : c'.mem = c.mem ∨ c.mem.last < c'.views.vwAll
  reads : ∃ new : List TraceEv, c'.log = c.log ++ new ∧
    ∀ l t v ν, TraceEv.read l t v ν ∈ new → t ≤ c'.views.relPreNT
  prom : (∀ p ∈ c.prom, p ≤ c.mem.last) → ∀ p ∈ c'.prom, p ≤ c'.mem.last

theorem Ctx.Silent.relPre {c c' : Ctx} (h : c.Silent c') : c.views.relPre ≤ c'.views.relPre := by
  have h1 := h.vrOld; have h2 := h.vrOldNR; have h3 := h.vwOld
  unfold Views.relPre
  omega_t

theorem Ctx.Silent.relPreNT {c c' : Ctx} (h : c.Silent c') : c.views.relPreNT ≤ c'.views.relPreNT := by
  have h1 := h.relPre; have h2 := h.vwOldNT
  unfold Views.relPreNT
  omega_t

theorem Ctx.Silent.vwAll {c c' : Ctx} (h : c.Silent c') : c.views.vwAll ≤ c'.views.vwAll := by
  have h1 := h.vwOld; have h2 := h.vwOldNT
  unfold Views.vwAll
  omega_t

theorem Ctx.Silent.refl {c : Ctx} (h : c.views.FwdOk) : c.Silent c :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h, .inl rfl, ⟨[], by simp, by simp⟩, id⟩

theorem Ctx.Silent.trans {c c' c'' : Ctx} (h₁ : c.Silent c') (h₂ : c'.Silent c'') : c.Silent c'' := by
  refine ⟨Nat.le_trans h₁.vrOld h₂.vrOld, Nat.le_trans h₁.vrOldNR h₂.vrOldNR, Nat.le_trans h₁.vwOld h₂.vwOld,
    Nat.le_trans h₁.vwOldNT h₂.vwOldNT, h₂.fwd, ?_, ?_, fun hp => h₂.prom (h₁.prom hp)⟩
  · rcases h₁.mem with h1 | h1
    · rcases h₂.mem with h2 | h2
      · exact .inl (h2.trans h1)
      · exact .inr (h1 ▸ h2)
    · exact .inr (Nat.lt_of_lt_of_le h1 h₂.vwAll)
  · obtain ⟨n1, hl1, hr1⟩ := h₁.reads
    obtain ⟨n2, hl2, hr2⟩ := h₂.reads
    refine ⟨n1 ++ n2, by rw [hl2, hl1, List.append_assoc], fun l t v ν hm => ?_⟩
    rcases List.mem_append.mp hm with hm | hm
    · exact Nat.le_trans (hr1 l t v ν hm) h₂.relPreNT
    · exact hr2 l t v ν hm

/-- A step that leaves the release views, forwarding, memory and promises
alone and logs no read. -/
theorem Ctx.Silent.of_eq {c c' : Ctx} (hf : c.views.FwdOk) (h1 : c'.views.vrOld = c.views.vrOld)
    (h2 : c'.views.vrOldNR = c.views.vrOldNR) (h3 : c'.views.vwOld = c.views.vwOld)
    (h3' : c'.views.vwOldNT = c.views.vwOldNT)
    (h4 : c'.views.fwdb = c.views.fwdb) (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hl : ∃ new : List TraceEv, c'.log = c.log ++ new ∧ ∀ l t v ν, TraceEv.read l t v ν ∉ new) : c.Silent c' := by
  obtain ⟨new, hl, hn⟩ := hl
  refine ⟨Nat.le_of_eq h1.symm, Nat.le_of_eq h2.symm, Nat.le_of_eq h3.symm, Nat.le_of_eq h3'.symm, fun p hp' => ?_,
    .inl hm, ⟨new, hl, fun l t v ν h => absurd h (hn l t v ν)⟩, fun h p hp' => ?_⟩
  · rw [h4] at hp'; simp only [Views.vwAll, h3, h3']; exact hf p hp'
  · rw [hp] at hp'; rw [hm]; exact h p hp'

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_silent {c : Ctx} (hf : c.views.FwdOk) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.Silent x.2.2 := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    clear ht
    refine ⟨?_, ?_, Nat.le_refl _, Nat.le_refl _, ?_, .inl rfl, ⟨[_], rfl, ?_⟩, fun h => h⟩
    · show c.views.vrOld ≤ (if noRet = true then _ else _)
      split <;> omega_t
    · show c.views.vrOldNR ≤ (if noRet = true then _ else _)
      split <;> omega_t
    · intro p hp; exact hf p hp
    · intro l' t' v' ν' hm
      rw [List.mem_singleton] at hm
      injection hm with _ hm2
      subst hm2
      have key : t' ≤ readView A (A.loadKind k) (c.views.getFwd l) t' ∨ t' ≤ c.views.vwAll := by
        cases hfw : c.views.getFwd l with
        | none => left; simp [readView]
        | some f =>
          simp only [readView]
          split
          · rename_i hc
            rw [Bool.and_eq_true] at hc
            have h1 := of_decide_eq_true hc.1
            have := hf _ (Views.getFwd_mem hfw)
            simp only at this
            exact .inr (h1 ▸ this)
          · left; exact Nat.le_refl _
      simp only [Views.relPreNT, Views.relPre, Views.vwAll, Views.setCoh] at key ⊢
      cases noRet <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega_t

theorem afterWrite_fwdOk {xr : View} {c : Ctx} (hf : c.views.FwdOk) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val)
    (t : Time) (νfwd : View) (ful : Bool) : (afterWrite A iv c k xcl l v t νfwd ful xr).views.FwdOk := by
  intro p hp
  simp only [afterWrite, Views.setFwd, Views.setCoh, Views.vwAll] at hp ⊢
  rcases Views.mem_setSorted hp with rfl | hp
  · simp only; split <;> omega_t
  · have := hf p hp; simp only [Views.vwAll] at this; split <;> omega_t

theorem writeSuccs_silent {xr : View} {c : Ctx} (hf : c.views.FwdOk) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    c.Silent c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · have h := ite_none_right' h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨by simp [afterWrite, Views.setCoh], by simp [afterWrite, Views.setCoh],
        by simp only [afterWrite, Views.setCoh]; split <;> omega_t,
        by simp only [afterWrite, Views.setCoh]; split <;> omega_t, afterWrite_fwdOk A iv hf _ _ _ _ _ _ _, .inl rfl,
        ⟨[_], rfl, by simp⟩, fun hp p hp' => hp p (List.mem_of_mem_erase hp')⟩
    · cases h
  · have h := mem_ite_nil' h
    rw [List.mem_singleton] at h
    subst h
    refine ⟨by simp [afterWrite, Views.setCoh], by simp [afterWrite, Views.setCoh],
      by simp only [afterWrite, Views.setCoh]; split <;> omega_t,
      by simp only [afterWrite, Views.setCoh]; split <;> omega_t, ?_, .inr ?_,
      ⟨[_], rfl, by simp⟩, fun hp p hp' => ?_⟩
    · apply afterWrite_fwdOk; exact hf
    · simp only [afterWrite, Views.setCoh, Memory.last, Views.vwAll]; split <;> omega_t
    · have hp' := List.mem_of_mem_erase hp'
      simp only [afterWrite, Memory.last, Array.size_push] at hp' ⊢
      rcases List.mem_append.mp hp' with hp' | hp'
      · have := hp p hp'; simp only [Memory.last] at this; omega_t
      · rw [List.mem_singleton] at hp'; omega_t

theorem fenceStep_fields (c : Ctx) (k : FenceKind) :
    (fenceStep c k).views.vrOld = c.views.vrOld ∧ (fenceStep c k).views.vrOldNR = c.views.vrOldNR ∧
      (fenceStep c k).views.vwOld = c.views.vwOld ∧ (fenceStep c k).views.fwdb = c.views.fwdb ∧
      (fenceStep c k).prom = c.prom ∧ (fenceStep c k).log = c.log ++ [.fence k] ∧
      (fenceStep c k).views.vwOldNT = c.views.vwOldNT := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Ctx.Silent.fenceStep {c : Ctx} (hf : c.views.FwdOk) (k : FenceKind) : c.Silent (fenceStep c k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := fenceStep_fields c k
  exact .of_eq hf h1 h2 h3 h7 h4 (fenceStep_mem c k) h5 ⟨_, h6, by simp⟩

theorem Ctx.Silent.fenceOpt {c : Ctx} (hf : c.views.FwdOk) (b : Bool) (k : FenceKind) :
    c.Silent (if b then Kraken.Promising.fenceStep c k else c) := by
  cases b
  · exact .refl hf
  · exact .fenceStep hf k

theorem Ctx.Silent.rmwPost {c : Ctx} (hf : c.views.FwdOk) (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) :
    c.Silent (Kraken.Promising.rmwPost A k noRet l c) := by
  unfold Kraken.Promising.rmwPost
  split
  · exact .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp, by simp⟩
  · exact .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp, by simp⟩

theorem runTree_silent {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.views.FwdOk → .ok (s, c') ∈ runTree A tid iv c tree → c.Silent c' := by
  induction tree with
  | done s0 =>
    intro c s c' hf h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl hf
  | fault msg =>
    intro c s c' _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' hf h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' hf hi
  | load k xcl l ret ih =>
    intro c s c' hf h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    have h0 := readSuccs_silent A iv hf h0
    exact h0.trans (ih v c0 s c' h0.fwd h)
  | store k xcl l v ret ih =>
    intro c s c' hf h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      have h0 := writeSuccs_silent A tid _ hf hc0
      exact h0.trans (ih true c0 s c' h0.fwd h)
    · rw [List.mem_ite_nil_right] at h
      have h0 : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } := .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact h0.trans (ih false _ s c' h0.fwd h.2)
  | fence k ret ih =>
    intro c s c' hf h
    simp only [runTree] at h
    have h0 := Ctx.Silent.fenceStep hf k
    exact h0.trans (ih () _ s c' h0.fwd h)
  | rmw k noRet l op ret ih =>
    intro c s c' hf h
    simp only [runTree] at h
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : c.Silent c2 := h1.trans (readSuccs_silent A iv h1.fwd h2)
    simp only at h
    split at h
    · have h3 := Ctx.Silent.fenceOpt h12.fwd A.rmwFence .sy
      exact (h12.trans h3).trans (ih old _ s c' h3.fwd h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have h23 := h12.trans (writeSuccs_silent A tid _ h12.fwd hc3)
      have h4 : c.Silent (if (A.rmwKind k == .acqRel && !noRet) = true then
          { c3 with rmwWrote := true, views := { c3.views with
              vrNew := max c3.views.vrNew (c3.views.getCoh l), vwNew := max c3.views.vwNew (c3.views.getCoh l) } }
          else { c3 with rmwWrote := true }) := by
        refine h23.trans ?_
        split
        · exact .of_eq h23.fwd rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp, by simp⟩
        · exact .of_eq h23.fwd rfl rfl rfl rfl rfl rfl rfl ⟨[], by simp, by simp⟩
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      exact h5.trans (ih old _ s c' h5.fwd h)

end Rules

/-! ## One instruction -/

private theorem foldl_pres {α β : Type} (g : Thread I → β) (f : Thread I → α → Thread I)
    (hf : ∀ t a, g (f t a) = g t) : ∀ (l : List α) (t : Thread I), g (l.foldl f t) = g t
  | [], _ => rfl
  | a :: l, t => (foldl_pres g f hf l (f t a)).trans (hf t a)

/-- The views and promises of a thread, but for `vCAP` (the only view a
branch changes). -/
private def relKey (t : Thread I) : List Time × Views := (t.prom, { t.views with vCAP := 0 })

/-- Close `relKey (l₁.foldl f₁ (… (lₙ.foldl fₙ t))) = k` where each `fᵢ` only
sets register views. -/
local macro "key_foldl" : tactic =>
  `(tactic| (repeat (refine (foldl_pres relKey _ ?_ _ _).trans ?_; (intro t a; first | rfl | (cases a; rfl)))
             try rfl))

/-- `finishInstr` takes the context's promises and views; it changes only
register views and, for a branch, `vCAP`. -/
theorem finishInstr_relKey {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {th : Thread I} (h : th ∈ finishInstr t d iv st c) :
    th.prom = c.prom ∧ ({ th.views with vCAP := 0 } : Views) = { c.views with vCAP := 0 } := by
  suffices hk : relKey th = (c.prom, { c.views with vCAP := 0 }) by
    simp only [relKey, Prod.mk.injEq] at hk; exact hk
  unfold finishInstr at h
  simp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> split <;> (try split) <;> key_foldl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    split <;> split <;> key_foldl

theorem Views.relPre_congr {a b : Views} (h : ({ a with vCAP := 0 } : Views) = { b with vCAP := 0 }) :
    a.relPre = b.relPre ∧ a.vwOld = b.vwOld ∧ (a.FwdOk ↔ b.FwdOk) := by
  have h1 := congrArg Views.vrOld h
  have h2 := congrArg Views.vrOldNR h
  have h3 := congrArg Views.vwOld h
  have h4 := congrArg Views.fwdb h
  have h5 := congrArg Views.vwOldNT h
  simp only at h1 h2 h3 h4 h5
  refine ⟨by simp only [relPre, h1, h2, h3], h3, ?_⟩
  simp only [FwdOk, vwAll, h3, h4, h5]

theorem Views.vwOldNT_congr {a b : Views} (h : ({ a with vCAP := 0 } : Views) = { b with vCAP := 0 }) :
    a.vwOldNT = b.vwOldNT := by
  have h5 := congrArg Views.vwOldNT h
  simpa using h5

/-- **One instruction, against the release views, with non-temporal
stores.** From a thread whose forwarding entries are its own writes:
`relPre` and `vwOldNT` only grow, the forwarding invariant is kept, memory is
unchanged unless `vwAll` passed `|M|`, every read is at most the new
`relPreNT`, and outstanding promises stay messages. -/
theorem stepOne_silent_nt (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) :
    t.views.relPre ≤ o.thread.views.relPre ∧ t.views.vwOldNT ≤ o.thread.views.vwOldNT ∧
      o.thread.views.FwdOk ∧
      (o.mem = mem ∨ mem.last < o.thread.views.vwAll) ∧
      (∀ l tr v ν, TraceEv.read l tr v ν ∈ o.log → tr ≤ o.thread.views.relPreNT) ∧
      ((∀ p ∈ t.prom, p ≤ mem.last) → ∀ p ∈ o.thread.prom, p ≤ o.mem.last) := by
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
      have hs := runTree_silent A tid _ tree _ st c' hf hr
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      obtain ⟨hrel, hvw, hfw⟩ := Views.relPre_congr hv
      have hnt := Views.vwOldNT_congr hv
      have hall : th.views.vwAll = c'.views.vwAll := by simp only [Views.vwAll, hvw, hnt]
      have hrelNT : th.views.relPreNT = c'.views.relPreNT := by simp only [Views.relPreNT, hrel, hnt]
      simp only
      refine ⟨hrel ▸ hs.relPre, hnt ▸ hs.vwOldNT, hfw.mpr hs.fwd, hall ▸ hs.mem, ?_, fun h => hp ▸ hs.prom h⟩
      obtain ⟨new, hl, hn⟩ := hs.reads
      intro l tr v ν hm
      rw [hl] at hm
      rcases List.mem_append.mp hm with hm | hm
      · simp at hm
      · exact hrelNT ▸ hn l tr v ν hm

/-- **One instruction, against the release views.** From a thread whose
forwarding entries are its own writes: `relPre` only grows, the forwarding
invariant is kept, memory is unchanged unless `vwOld` passed `|M|`, every
read is at most the new `relPre`, and outstanding promises stay messages. -/
theorem stepOne_silent (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) (hnt : o.thread.views.vwOldNT = 0) :
    t.views.relPre ≤ o.thread.views.relPre ∧ o.thread.views.FwdOk ∧
      (o.mem = mem ∨ mem.last < o.thread.views.vwOld) ∧
      (∀ l tr v ν, TraceEv.read l tr v ν ∈ o.log → tr ≤ o.thread.views.relPre) ∧
      ((∀ p ∈ t.prom, p ≤ mem.last) → ∀ p ∈ o.thread.prom, p ≤ o.mem.last) := by
  obtain ⟨h1, -, h2, h3, h4, h5⟩ := stepOne_silent_nt A hstep ho hf
  have hall : o.thread.views.vwAll = o.thread.views.vwOld := by simp only [Views.vwAll, hnt]; omega_t
  have hrel : o.thread.views.relPreNT = o.thread.views.relPre := by simp only [Views.relPreNT, hnt]; omega_t
  exact ⟨h1, h2, hall ▸ h3, hrel ▸ h4, h5⟩

/-- The thread has made no non-temporal store at timestamp `ts` or later
(`vwOldNT = 0`: none at all; timestamps of messages are positive).

**A temporary restriction of the logic, not of the machine** (lifted in `ReleasePrefixNT.lean`): a non-temporal store does not enter a later release store's
pre-view (`writeSuccs`), so while a promise is outstanding the thread may
append a non-temporal message above it, and (S2)/(S1′) as stated fail. The
theorems below assume this predicate for the thread at the end of the path;
it holds for every thread under `Arch.armv8` (`Thread.noNTStores_armv8`), so
it restricts only x86 programs that use `movnti`. -/
def Thread.NoNTStores (t : Thread I) (ts : Time) : Prop :=
  t.views.vwOldNT = 0 ∨ t.views.vwOldNT < ts

theorem Thread.NoNTStores.relPreNT_lt {t : Thread I} {ts : Time} (h : t.NoNTStores ts)
    (hb : t.views.relPre < ts) : t.views.relPreNT < ts := by
  simp only [Views.relPreNT]
  rcases h with h | h <;> omega_t

theorem Thread.NoNTStores.mono {t t' : Thread I} {ts : Time} (h : t'.NoNTStores ts)
    (hle : t.views.vwOldNT ≤ t'.views.vwOldNT) : t.NoNTStores ts := by
  rcases h with h | h
  · exact .inl (by omega_t)
  · exact .inr (by omega_t)

/-- No store event of the tree is non-temporal under the profile (after
`Arch.storeKind`; an RMW's write after `Arch.rmwKind`). -/
def EvTree.NoNT {σ : Type} (A : Arch) : EvTree σ → Prop
  | .done _ => True
  | .fault _ => True
  | .choose _ k => ∀ i, NoNT A (k i)
  | .load _ _ _ ret => ∀ v, NoNT A (ret v)
  | .store k _ _ _ ret => A.storeKind k ≠ .nt ∧ ∀ b, NoNT A (ret b)
  | .rmw k _ _ _ ret => A.storeKind (A.rmwKind k).storeKind ≠ .nt ∧ ∀ v, NoNT A (ret v)
  | .fence _ ret => NoNT A (ret ())

/-- The thread's next instruction makes no non-temporal store. Together with
`Thread.NoNTStores`, the temporary restriction of (S1′) (see there; lifted by
`Config.advanceableNT_of_path`, `ReleasePrefixNT.lean`). -/
def Thread.NextNoNT (A : Arch) (t : Thread I) : Prop :=
  ∀ tree, I.exec t.st = some tree → tree.NoNT A

/-- **(S2), one instruction.** If the thread's state after the instruction is
release-bounded for a message `ts` of the memory (`relPre < ts ≤ |M|`), the
instruction appended nothing and read only messages below `ts`. -/
theorem silent_of_relPre (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) {ts : Time} (hts : ts ≤ mem.last)
    (hb : o.thread.views.relPre < ts) (hnt : o.thread.NoNTStores ts) :
    o.mem = mem ∧ ∀ l tr v ν, TraceEv.read l tr v ν ∈ o.log → tr < ts := by
  obtain ⟨-, -, -, hm, hr, -⟩ := stepOne_silent_nt A hstep ho hf
  have hb' := hnt.relPreNT_lt hb
  have hvw := o.thread.views.vwAll_le_relPreNT
  refine ⟨?_, fun l tr v ν h => Nat.lt_of_le_of_lt (hr l tr v ν h) hb'⟩
  rcases hm with hm | hm
  · exact hm
  · omega_t

theorem StutterStep.of_relPre (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) {ts : Time} (hts : ts ≤ mem.last)
    (hb : o.thread.views.relPre < ts) (hnt : o.thread.NoNTStores ts) : StutterStep ts mem o :=
  fun _ => silent_of_relPre A hstep ho hf hts hb hnt

/-! ## Reachable configurations are well formed -/

/-- Every thread's forwarding entries are its own writes, and every
outstanding promise is a message of the memory. Holds initially
(`Config.init_wf`) and in every reachable configuration
(`Config.Wf.reachable`). -/
def Config.Wf (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.views.FwdOk ∧ ∀ p ∈ t.prom, p ≤ c.mem.last

theorem Config.init_wf (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem : Config I).Wf := by
  intro i t h
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  exact ⟨fun p hp => by simp [Thread.init] at hp, fun p hp => by simp [Thread.init] at hp⟩

theorem Config.withThread_get? (c : Config I) {tid i : Nat} (t : Thread I) (mem : Memory)
    (ht : tid < c.threads.size) :
    (c.withThread tid t mem).threads[i]? = if tid = i then some t else c.threads[i]? := by
  simp only [Config.withThread, Array.set!, Array.getElem?_setIfInBounds]
  split <;> simp_all

theorem Config.withThread_size (c : Config I) (tid : Nat) (t : Thread I) (mem : Memory) :
    (c.withThread tid t mem).threads.size = c.threads.size := by
  simp [Config.withThread, Array.set!]

theorem lt_size_of_get? {c : Config I} {i : Nat} {t : Thread I} (h : c.threads[i]? = some t) : i < c.threads.size := by
  obtain ⟨hi, -⟩ := Array.getElem?_eq_some_iff.mp h
  exact hi

/-- An instruction step keeps the configuration well formed. -/
theorem Config.Wf.instr {A : Arch} {c : Config I} (hwf : c.Wf) {tid : Nat} {t : Thread I}
    (ht : c.threads[tid]? = some t) {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : (c.withThread tid o.thread o.mem).Wf := by
  obtain ⟨hf, hp⟩ := hwf tid t ht
  obtain ⟨-, -, hf', -, -, hp'⟩ := stepOne_silent_nt A hstep ho hf
  obtain ⟨-, hext⟩ := stepOne_ext A hstep ho
  have hlast : c.mem.last ≤ o.mem.last := by
    simp only [Memory.last, ← Array.length_toList, hext, List.length_append]; omega_t
  intro i t' h
  rw [Config.withThread_get? c _ _ (lt_size_of_get? ht)] at h
  split at h
  · cases h; exact ⟨hf', hp' hp⟩
  · obtain ⟨h1, h2⟩ := hwf i t' h
    exact ⟨h1, fun p hp => Nat.le_trans (h2 p hp) hlast⟩

/-- A promise step keeps the configuration well formed. -/
theorem Config.Wf.promise {c : Config I} (hwf : c.Wf) {tid : Nat} {t : Thread I}
    (ht : c.threads[tid]? = some t) (w : Msg) :
    (c.withThread tid { t with prom := t.prom ++ [(c.mem.append w).2] } (c.mem.append w).1).Wf := by
  obtain ⟨hf, hp⟩ := hwf tid t ht
  intro i t' h
  rw [Config.withThread_get? c _ _ (lt_size_of_get? ht)] at h
  simp only [Config.withThread, Memory.append, Memory.last, Array.size_push] at h ⊢
  split at h
  · cases h
    refine ⟨hf, fun p hp' => ?_⟩
    rcases List.mem_append.mp hp' with hp' | hp'
    · have := hp p hp'; simp only [Memory.last] at this; omega_t
    · rw [List.mem_singleton] at hp'; omega_t
  · obtain ⟨h1, h2⟩ := hwf i t' h
    exact ⟨h1, fun p hp => by have := h2 p hp; simp only [Memory.last] at this; omega_t⟩

theorem Config.Wf.succ {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (h : SuccKind A c c') : c'.Wf := by
  cases h with
  | instr ht hstep ho => exact hwf.instr ht hstep ho
  | promise ht _ => exact hwf.promise ht _

/-- **Every reachable configuration is well formed** (from a well-formed one,
e.g. `Config.init`). -/
theorem Config.Wf.reachable {A : Arch} {c c' : Config I} (hwf : c.Wf)
    (h : ReachableK A c c') : c'.Wf := by
  induction h with
  | refl => exact hwf
  | step hs _ ih => exact ih (hwf.succ hs)

/-- Along any `ReachableK` path a measure `f` of a thread's views that each
of its own instructions raises only grows (the `ReachableK` twin of
`Reachable.views_mono`). -/
theorem Live.Bridge.ReachableK.views_mono {A : Arch} (f : Views → Nat)
    (hf : ∀ {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome I))} {o : Outcome I},
      stepOne A t tid mem = some outs → .ok o ∈ outs → t.views.FwdOk → f t.views ≤ f o.thread.views)
    {c c' : Config I}
    (h : ReachableK A c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ f t.views ≤ f t'.views := by
  induction h generalizing t with
  | refl => exact ⟨t, ht, Nat.le_refl _⟩
  | @step c c1 c2 hs _ ih =>
    have hwf1 := hwf.succ hs
    have hlt := lt_size_of_get? ht
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      by_cases hij : j = tid
      · subst hij
        rw [ht] at hj; cases hj
        have h1 : (c.withThread j o.thread o.mem).threads[j]? = some o.thread := by
          simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
        obtain ⟨t', h', hle⟩ := ih hwf1 h1
        exact ⟨t', h', Nat.le_trans (hf hstep ho (hwf j t ht).1) hle⟩
      · have h1 : (c.withThread j o.thread o.mem).threads[tid]? = some t := by
          simp only [Config.withThread_get? c _ _ (lt_size_of_get? hj), hij, ↓reduceIte, ht]
        exact ih hwf1 h1
    | @promise j tj p hj _ =>
      by_cases hij : j = tid
      · subst hij
        rw [ht] at hj; cases hj
        have h1 := (Config.withThread_get? c (i := j) { t with prom := t.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 hlt)
        simp only [↓reduceIte] at h1
        obtain ⟨t', h', hle⟩ := ih hwf1 h1
        exact ⟨t', h', hle⟩
      · have h1 := (Config.withThread_get? c (i := tid) { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 (lt_size_of_get? hj))
        simp only [hij, ↓reduceIte, ht] at h1
        exact ih hwf1 h1

/-- Along any machine path a measure `f` of a thread's views that each of its
own instructions raises only grows (nothing else touches its views). -/
theorem Reachable.views_mono {A : Arch} [I.LawfulState] (f : Views → Nat)
    (hf : ∀ {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome I))} {o : Outcome I},
      stepOne A t tid mem = some outs → .ok o ∈ outs → t.views.FwdOk → f t.views ≤ f o.thread.views)
    {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ f t.views ≤ f t'.views :=
  (ReachableK.of_reachable h).views_mono f hf hwf ht

/-- Along any `ReachableK` path a thread's `relPre` only grows (the `ReachableK` twin
of `Reachable.relPre_mono`). -/
theorem Live.Bridge.ReachableK.relPre_mono {A : Arch} {c c' : Config I}
    (h : ReachableK A c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ t.views.relPre ≤ t'.views.relPre :=
  h.views_mono Views.relPre (fun hstep ho hf => (stepOne_silent_nt _ hstep ho hf).1) hwf ht

/-- Along any machine path a thread's `relPre` only grows (its own
instructions raise it, nothing else touches its views). -/
theorem Reachable.relPre_mono {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ t.views.relPre ≤ t'.views.relPre :=
  (ReachableK.of_reachable h).relPre_mono hwf ht

/-- Along any `ReachableK` path a thread's `vwOldNT` only grows (the `ReachableK` twin
of `Reachable.vwOldNT_mono`). -/
theorem Live.Bridge.ReachableK.vwOldNT_mono {A : Arch} {c c' : Config I}
    (h : ReachableK A c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ t.views.vwOldNT ≤ t'.views.vwOldNT :=
  h.views_mono Views.vwOldNT (fun hstep ho hf => (stepOne_silent_nt _ hstep ho hf).2.1) hwf ht

/-- Along any machine path a thread's `vwOldNT` only grows. -/
theorem Reachable.vwOldNT_mono {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') (hwf : c.Wf) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) :
    ∃ t', c'.threads[tid]? = some t' ∧ t.views.vwOldNT ≤ t'.views.vwOldNT :=
  (ReachableK.of_reachable h).vwOldNT_mono hwf ht

/-- **(S2) on machine paths.** Let thread `tid` take an instruction step `o`
from a well-formed configuration `c` while its promise `ts` is outstanding,
and let the path continue, under any schedule, to a configuration where the
thread is release-bounded for `ts` (e.g. its next instruction is a release
store fulfilling `ts`: `Thread.RelFulfils.relPre_lt`). Then the step is a
`StutterStep`: it appended nothing and read only messages below `ts`. The
only hypothesis on the program is `Thread.NoNTStores` (no non-temporal store
at or after `ts`; a temporary restriction, trivial under `Arch.armv8`);
`c.Wf` holds in every reachable configuration. -/
theorem stutterStep_path {A : Arch} {c c1 : Config I} (hwf : c.Wf)
    {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) {ts : Time} (hts : ts ∈ t.prom)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hr : ReachableK A (c.withThread tid o.thread o.mem) c1)
    {t1 : Thread I} (ht1 : c1.threads[tid]? = some t1) (hb : t1.views.relPre < ts)
    (hnt : t1.NoNTStores ts) :
    StutterStep ts c.mem o := by
  have h1 : (c.withThread tid o.thread o.mem).threads[tid]? = some o.thread := by
    simp only [Config.withThread_get? c _ _ (lt_size_of_get? ht), ↓reduceIte]
  obtain ⟨t', h', hle⟩ := hr.relPre_mono (hwf.instr ht hstep ho) h1
  obtain ⟨t'', h'', hle'⟩ := hr.vwOldNT_mono (hwf.instr ht hstep ho) h1
  rw [ht1] at h' h''; cases h'; cases h''
  exact StutterStep.of_relPre A hstep ho (hwf tid t ht).1 ((hwf tid t ht).2 ts hts) (Nat.lt_of_le_of_lt hle hb)
    (hnt.mono hle')

/-! ## Release stores are release-bounded

Memory messages carry no mode in Kraken, so "a release promise" is a
property of the run that fulfils it: the store event that fulfils it is a
release (after the profile's `Arch.storeKind`: every store under TSO).
`EvTree.RelFulfils` says that some run of an instruction's event tree
fulfils `ts` with a release store; its state before the instruction is then
release-bounded for `ts` (`EvTree.RelFulfils.relPre_lt`), which is all (S2)
uses. -/


section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- The local fact: a release store that fulfils `ts` has `relPre < ts`. -/
theorem writeSuccs_rel_relPre {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hk : A.storeKind k = .rel)
    {ts : Time} (hin : ts ∈ c.prom) (hout : ts ∉ c'.prom) : c.views.relPre < ts := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      · simp only [Option.some.injEq] at h
        subst h
        simp only [afterWrite] at hout
        have hts : ts = t := by
          by_cases hne : ts = t
          · exact hne
          · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
        subst hts
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨-, hb, -⟩ := hc
        simp only [hk, show (StoreKind.rel == StoreKind.rel) = true from rfl, ↓reduceIte, Views.relPre] at hb ⊢
        omega_t
    · cases h
  · have h := mem_ite_nil' h
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

/-- **A release store fulfilling `ts` is release-bounded**: if some run of
the instruction from `c` fulfils `ts` with a release store, `c`'s `relPre`
is below `ts`. -/
theorem EvTree.RelFulfils.relPre_lt {ts : Time} {σ : Type} (tree : EvTree σ) :
    ∀ c : Ctx, c.views.FwdOk → EvTree.RelFulfils A tid iv ts c tree → c.views.relPre < ts := by
  induction tree with
  | done s => intro c _ h; exact h.elim
  | fault m => intro c _ h; exact h.elim
  | choose n k ih =>
    intro c hf ⟨i, h⟩
    exact ih i c hf h
  | load k xcl l ret ih =>
    intro c hf ⟨x, hx, h⟩
    have hs := readSuccs_silent A iv hf hx
    exact Nat.lt_of_le_of_lt hs.relPre (ih x.2.1 x.2.2 hs.fwd h)
  | store k xcl l v ret ih =>
    intro c hf h
    rcases h with ⟨c', hc', h | h⟩ | h
    · exact writeSuccs_rel_relPre A tid _ hc' h.1 h.2.1 h.2.2
    · have hs := writeSuccs_silent A tid _ hf hc'
      exact Nat.lt_of_le_of_lt hs.relPre (ih true c' hs.fwd h)
    · have hs : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact Nat.lt_of_le_of_lt hs.relPre (ih false _ hs.fwd h)
  | fence k ret ih =>
    intro c hf h
    have hs := Ctx.Silent.fenceStep hf k
    exact Nat.lt_of_le_of_lt hs.relPre (ih () _ hs.fwd h)
  | rmw k noRet l op ret ih =>
    intro c hf ⟨x, hx, h⟩
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have h2 := h1.trans (readSuccs_silent A iv h1.fwd hx)
    rcases h with h | ⟨new, -, c', hc', h | h⟩
    · have h3 := h2.trans (Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy)
      exact Nat.lt_of_le_of_lt h3.relPre (ih x.2.1 _ h3.fwd h)
    · exact Nat.lt_of_le_of_lt h2.relPre (writeSuccs_rel_relPre A tid _ hc' h.1 h.2.1 h.2.2)
    · have h3 := h2.trans (writeSuccs_silent A tid _ h2.fwd hc')
      have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      exact Nat.lt_of_le_of_lt h5.relPre (ih x.2.1 _ h5.fwd h)

end Rules


theorem Thread.RelFulfils.relPre_lt {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {mem : Memory}
    (h : t.RelFulfils A tid ts mem) (hf : t.views.FwdOk) : t.views.relPre < ts := by
  obtain ⟨tree, -, h⟩ := h
  exact EvTree.RelFulfils.relPre_lt A tid _ tree _ hf h

/-- **(S2) for release promises.** Every instruction step thread `tid` takes
from a reachable configuration while its promise `ts` is outstanding, on any
path along which the thread later reaches an instruction that fulfils `ts`
with a release store, is a `StutterStep` (provided the thread there has made
no non-temporal store at or after `ts`: `Thread.NoNTStores`). -/
theorem stutterStep_release {A : Arch} {c0 c c1 : Config I} (h0 : c0.Wf)
    (hc : ReachableK A c0 c) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) {ts : Time}
    (hts : ts ∈ t.prom) {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hr : ReachableK A (c.withThread tid o.thread o.mem) c1)
    {t1 : Thread I} (ht1 : c1.threads[tid]? = some t1) (hrel : t1.RelFulfils A tid ts c1.mem)
    (hnt : t1.NoNTStores ts) :
    StutterStep ts c.mem o := by
  have hwf := h0.reachable hc
  have hwf1 := (hwf.instr ht hstep ho).reachable hr
  exact stutterStep_path hwf ht hts hstep ho hr ht1 (hrel.relPre_lt (hwf1 tid t1 ht1).1) hnt

/-! ## (S1′): replay on a memory prefix

Along a machine path, a release-bounded thread's instructions read only
messages below `ts ≤ |M|` and append nothing (S2), while the other threads
append above `|M|`. Such instructions replay on the old memory `M`: the
messages they read are there, with the same timestamps, and a smaller memory
blocks fewer reads (`Memory.writeIn`) and fewer exclusive writes
(`Memory.atomic`). The thread's promises made after `M` (all above `|M|`)
are dropped (`Thread.restrict`): before the release they cannot be
fulfilled (that would put `vwOld` above `|M|`), so they are inert. -/

/-- `M` is a prefix of `M'`: same initial values, `M'` has only appended. -/
def Memory.Prefix (M M' : Memory) : Prop := M'.init = M.init ∧ M.msgs.toList <+: M'.msgs.toList

theorem Memory.Prefix.refl (M : Memory) : M.Prefix M := ⟨rfl, List.prefix_refl _⟩

theorem Memory.Prefix.trans {M M' M'' : Memory} (h₁ : M.Prefix M') (h₂ : M'.Prefix M'') : M.Prefix M'' :=
  ⟨h₂.1.trans h₁.1, h₁.2.trans h₂.2⟩

theorem Memory.Prefix.last_le {M M' : Memory} (h : M.Prefix M') : M.last ≤ M'.last := by
  simp only [Memory.last, ← Array.length_toList]; exact h.2.length_le

theorem Memory.Prefix.get? {M M' : Memory} (h : M.Prefix M') {t : Time} (ht : t ≤ M.last) :
    M'.get? t = M.get? t := by
  unfold Memory.get?
  split
  · rfl
  · obtain ⟨rest, hr⟩ := h.2
    rw [← Array.getElem?_toList, ← Array.getElem?_toList, ← hr, List.getElem?_append_left]
    simp only [Memory.last, ← Array.length_toList] at ht; omega_t

theorem Memory.Prefix.initVal {M M' : Memory} (h : M.Prefix M') (l : Loc) : M'.initVal l = M.initVal l := by
  simp only [Memory.initVal, h.1]

theorem Memory.Prefix.read? {M M' : Memory} (h : M.Prefix M') {l : Loc} {t : Time} (ht : t ≤ M.last) :
    M'.read? l t = M.read? l t := by
  unfold Memory.read?
  rw [h.get? ht, h.initVal]

theorem Memory.Prefix.writeIn {M M' : Memory} (h : M.Prefix M') {l : Loc} {lo hi : Time}
    (hw : M'.writeIn l lo hi = false) : M.writeIn l lo hi = false := by
  unfold Memory.writeIn at hw ⊢
  rw [List.any_eq_false] at hw ⊢
  intro i hi' hm
  apply hw i hi'
  revert hm
  cases hg : M.get? (lo + i + 1) with
  | none => simp
  | some w =>
    have hle : lo + i + 1 ≤ M.last := by
      unfold Memory.get? at hg
      split at hg
      · cases hg
      · have := (Array.getElem?_eq_some_iff.mp hg).1
        simp only [Memory.last]; omega_t
    rw [h.get? hle]
    simp [hg]

theorem Memory.Prefix.atomic {M M' : Memory} (h : M.Prefix M') {l : Loc} {tid : Nat} {tr tw : Time}
    (hlt : tr < tw) (htw : tw ≤ M.last) (ha : M'.atomic l tid tr tw = true) : M.atomic l tid tr tw = true := by
  unfold Memory.atomic at ha ⊢
  rw [h.read? (by omega_t)] at ha
  split
  · rfl
  · rename_i v hv
    rw [hv] at ha
    simp only at ha
    rw [List.all_eq_true] at ha ⊢
    intro i hi
    have := ha i hi
    rw [h.get? (by simp only [List.mem_range] at hi; omega_t)] at this
    exact this

/-- A context against the memory prefix `M`: the memory replaced by `M`,
the promises above `|M|` dropped. -/
def Ctx.restrict (M : Memory) (c : Ctx) : Ctx :=
  { c with mem := M, prom := c.prom.filter (· ≤ M.last) }

/-- A thread with its promises above `|M|` dropped. -/
def Thread.restrict (M : Memory) (t : Thread I) : Thread I :=
  { t with prom := t.prom.filter (· ≤ M.last) }

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- The timestamp a read returns is at most the reader's new `relPreNT`. -/
theorem readSuccs_le {c : Ctx} (hf : c.views.FwdOk) {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : x.1 ≤ x.2.2.views.relPreNT := by
  obtain ⟨new, hl, hn⟩ := (readSuccs_silent A iv hf hx).reads
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    simp only [List.append_cancel_left_eq] at hl
    exact hn _ _ _ _ (hl ▸ List.mem_singleton_self _)

theorem readSuccs_restrict {M : Memory} {c : Ctx} (hM : M.Prefix c.mem) {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (hle : x.1 ≤ M.last) :
    (x.1, x.2.1, x.2.2.restrict M) ∈ readSuccs A iv (c.restrict M) k xcl l noRet := by
  unfold readSuccs at hx ⊢
  rw [List.mem_filterMap] at hx ⊢
  obtain ⟨t, -, ht⟩ := hx
  refine ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le ?_), ?_⟩
  · split at ht
    · cases ht
    · have h := ite_none_left' ht
      simp only [Option.some.injEq] at h
      subst h; exact hle
  · split at ht
    · cases ht
    · rename_i v hv
      have h := ite_none_left' ht
      simp only [Option.some.injEq] at h
      subst h
      have hc : (c.mem.writeIn l t (max (max iv.addrR (max c.views.vrNew
          (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0))) (c.views.getCoh l)) ||
          c.prom.contains t) = false := by
        cases hb : (c.mem.writeIn l t (max (max iv.addrR (max c.views.vrNew
          (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0))) (c.views.getCoh l)) ||
          c.prom.contains t)
        · rfl
        · rw [hb] at ht; cases ht
      simp only [Bool.or_eq_false_iff] at hc
      simp only [Ctx.restrict]
      rw [show M.read? l t = some v from (hM.read? hle).symm.trans hv]
      simp only
      have hcond : (M.writeIn l t (max (max iv.addrR (max c.views.vrNew
          (if (A.loadKind k == LoadKind.acq) = true then c.views.vRel else 0))) (c.views.getCoh l)) ||
          (c.prom.filter (· ≤ M.last)).contains t) = false := by
        rw [Bool.or_eq_false_iff]
        refine ⟨hM.writeIn hc.1, ?_⟩
        cases hcon : (c.prom.filter (· ≤ M.last)).contains t
        · rfl
        · exfalso
          have := (List.mem_filter.mp (List.contains_iff_mem.mp hcon)).1
          rw [List.contains_iff_mem.mpr this] at hc
          cases hc.2
      simp only [hcond, Bool.false_eq_true, ↓reduceIte]

theorem afterWrite_restrict {xr : View} (M : Memory) (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time)
    (νfwd : View) (ful : Bool) :
    afterWrite A iv (c.restrict M) k xcl l v t νfwd ful xr = (afterWrite A iv c k xcl l v t νfwd ful xr).restrict M := by
  simp only [afterWrite, Ctx.restrict, List.erase_filter]

theorem fenceStep_restrict (M : Memory) (c : Ctx) (k : FenceKind) :
    fenceStep (c.restrict M) k = (fenceStep c k).restrict M := by
  cases k <;> rfl

theorem fenceOpt_restrict (M : Memory) (c : Ctx) (b : Bool) (k : FenceKind) :
    (if b then fenceStep (c.restrict M) k else c.restrict M) = (if b then fenceStep c k else c).restrict M := by
  cases b
  · rfl
  · exact fenceStep_restrict M c k

/-- A write that keeps `vwAll` within `|M|` fulfils an outstanding promise
that is a message of `M`; it replays on `M`. -/
theorem writeSuccs_restrict {xr : View} {M : Memory} {c : Ctx} (hM : M.Prefix c.mem) {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} {c' : Ctx}
    (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hle : c'.views.vwAll ≤ M.last) :
    c'.restrict M ∈ writeSuccs A tid iv (c.restrict M) k xcl l v tr extra xr := by
  unfold writeSuccs at h ⊢
  rw [List.mem_append, List.mem_filterMap] at h
  rw [List.mem_append, List.mem_filterMap]
  rcases h with ⟨t, ht, h⟩ | h
  · split at h
    · rename_i w hw
      obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      have htle : t ≤ M.last := by
        simp only [afterWrite, Views.setCoh, Views.vwAll] at hle; split at hle <;> omega_t
      left
      refine ⟨t, show t ∈ c.prom.filter (· ≤ M.last) from List.mem_filter.mpr ⟨ht, by simpa using htle⟩, ?_⟩
      rw [hM.get? htle] at hw
      rw [show (c.restrict M).mem = M from rfl, hw]
      dsimp only
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, hb, hc2⟩ := hc
      rw [Option.ite_none_right_eq_some]
      refine ⟨?_, congrArg some (afterWrite_restrict A iv M c _ _ _ _ _ _ _)⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨hc1, hb, ?_⟩
      cases tr with
      | none => rfl
      | some tr =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc2 ⊢
        exact ⟨hc2.1, hM.atomic hc2.1 htle hc2.2⟩
    · cases h
  · exfalso
    have h := mem_ite_nil' h
    rw [List.mem_singleton] at h
    subst h
    have := hM.last_le
    simp only [afterWrite, Views.setCoh, Memory.last, Views.vwAll] at hle this
    split at hle <;> omega_t


theorem rmwPost_restrict (A : Arch) (M : Memory) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    rmwPost A k noRet l (c.restrict M) = (rmwPost A k noRet l c).restrict M := by
  unfold rmwPost; split <;> rfl

theorem rmwPost_mem (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwPost A k noRet l c).mem = c.mem := by
  unfold rmwPost; split <;> rfl

/-- **Replay of an instruction on a memory prefix.** A run of an event tree
against `M'` that ends bounded within `|M|` (`relPreNT ≤ |M|`, `M` a prefix of
`M'`) is also a run against `M`, with the promises above `|M|` dropped. -/
theorem runTree_restrict {σ : Type} {M M' : Memory} (hM : M.Prefix M') (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), c.views.FwdOk → c.mem = M' → .ok (s, c') ∈ runTree A tid iv c tree →
      c'.views.relPreNT ≤ M.last → .ok (s, c'.restrict M) ∈ runTree A tid iv (c.restrict M) tree := by
  have hML := hM.last_le
  induction tree with
  | done s0 =>
    intro c s c' _ _ h _
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [runTree]
  | fault msg =>
    intro c s c' _ _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' hf hm h hb
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨i, hi, h⟩ := h
    exact ⟨i, hi, ih i c s c' hf hm h hb⟩
  | load k xcl l ret ih =>
    intro c s c' hf hm h hb
    simp only [runTree, List.mem_flatMap] at h ⊢
    obtain ⟨x, hx, h⟩ := h
    have hs0 := readSuccs_silent A iv hf hx
    have hs1 := runTree_silent A tid iv _ x.2.2 s c' hs0.fwd h
    have hle : x.1 ≤ M.last := Nat.le_trans (readSuccs_le A iv hf hx) (Nat.le_trans hs1.relPreNT hb)
    refine ⟨_, readSuccs_restrict A iv (hm ▸ hM) hx hle, ?_⟩
    exact ih x.2.1 x.2.2 s c' hs0.fwd ((readSuccs_mp A iv hx).1.trans hm) h hb
  | store k xcl l v ret ih =>
    intro c s c' hf hm h hb
    simp only [runTree, List.mem_append] at h ⊢
    rcases h with h | h
    · left
      rw [List.mem_ite_nil_left, List.mem_flatMap] at h ⊢
      obtain ⟨hp, c0, hc0, h⟩ := h
      refine ⟨hp, c0.restrict M, ?_, ?_⟩
      · have hs0 := writeSuccs_silent A tid _ hf hc0
        have hs1 := runTree_silent A tid iv _ c0 s c' hs0.fwd h
        have hvw : c0.views.vwAll ≤ M.last :=
          Nat.le_trans c0.views.vwAll_le_relPreNT (Nat.le_trans hs1.relPreNT hb)
        exact writeSuccs_restrict A tid _ (hm ▸ hM) hc0 hvw
      · have hs0 := writeSuccs_silent A tid _ hf hc0
        have hs1 := runTree_silent A tid iv _ c0 s c' hs0.fwd h
        have hm0 : c0.mem = M' := by
          rcases hs0.mem with h0 | h0
          · exact h0.trans hm
          · exfalso
            have := Nat.le_trans c0.views.vwAll_le_relPreNT (Nat.le_trans hs1.relPreNT hb)
            rw [hm] at h0; omega_t
        exact ih true c0 s c' hs0.fwd hm0 h hb
    · right
      rw [List.mem_ite_nil_right] at h ⊢
      refine ⟨h.1, ?_⟩
      have := ih false { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] }
        s c' hf hm h.2 hb
      exact this
  | fence k ret ih =>
    intro c s c' hf hm h hb
    simp only [runTree] at h ⊢
    rw [fenceStep_restrict]
    exact ih () _ s c' (Ctx.Silent.fenceStep hf k).fwd ((fenceStep_mem c k).trans hm) h hb
  | rmw k noRet l op ret ih =>
    intro c s c' hf hm h hb
    simp only [runTree] at h ⊢
    rw [fenceOpt_restrict]
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have hm1 : (if A.rmwFence then fenceStep c .sy else c).mem = M' := by
      split <;> simp only [fenceStep_mem, hm]
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1 hm1 ⊢
    rw [List.mem_flatMap] at h ⊢
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨tr, old, c2⟩ := x
    have h2 := readSuccs_silent A iv h1.fwd hx
    have hm2 : c2.mem = M' := (readSuccs_mp A iv hx).1.trans hm1
    simp only at h ⊢
    have hfin : c2.views.relPreNT ≤ M.last → (tr, old, c2.restrict M) ∈
        readSuccs A iv (c1.restrict M) (if noRet = true then LoadKind.plain else (A.rmwKind k).loadKind) false l noRet :=
      fun hle2 => readSuccs_restrict A iv (hm1 ▸ hM) hx (Nat.le_trans (readSuccs_le A iv h1.fwd hx) hle2)
    split at h
    · rename_i hop
      have h3 := Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy
      have hs := runTree_silent A tid iv _ _ s c' h3.fwd h
      refine ⟨(tr, old, c2.restrict M), hfin (Nat.le_trans (h3.trans hs).relPreNT hb), ?_⟩
      simp only [hop]
      rw [fenceOpt_restrict]
      have hm3 : (if A.rmwFence then fenceStep c2 .sy else c2).mem = M' := by
        split <;> simp only [fenceStep_mem, hm2]
      exact ih old _ s c' h3.fwd hm3 h hb
    · rename_i new hop
      rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      have h3 := writeSuccs_silent A tid iv h2.fwd hc3
      have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      have hs := runTree_silent A tid iv _ _ s c' h5.fwd h
      have hend := Nat.le_trans hs.relPreNT hb
      have hvw3 : c3.views.vwAll ≤ M.last := by
        have := (Ctx.Silent.rmwPost h3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
        exact Nat.le_trans c3.views.vwAll_le_relPreNT (Nat.le_trans this.relPreNT hend)
      have hm3 : c3.mem = M' := by
        rcases h3.mem with h0 | h0
        · exact h0.trans hm2
        · exfalso; rw [hm2] at h0; have := hM.last_le; omega_t
      refine ⟨(tr, old, c2.restrict M), hfin (Nat.le_trans h5.relPreNT hend), ?_⟩
      simp only [hop, List.mem_flatMap]
      refine ⟨c3.restrict M, writeSuccs_restrict A tid iv (hm2 ▸ hM) hc3 hvw3, ?_⟩
      change .ok (s, c'.restrict M) ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l (c3.restrict M)) .sy
          else rmwPost A k noRet l (c3.restrict M)) (ret old)
      rw [rmwPost_restrict, fenceOpt_restrict]
      have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3).mem = M' := by
        split <;> simp only [fenceStep_mem, rmwPost_mem, hm3]
      exact ih old _ s c' h5.fwd hm5 h hb

end Rules

theorem foldl_restrict {β : Type} (M : Memory) (f : Thread I → β → Thread I)
    (hf : ∀ t b, f (t.restrict M) b = (f t b).restrict M) :
    ∀ (l : List β) (t : Thread I), l.foldl f (t.restrict M) = (l.foldl f t).restrict M
  | [], _ => rfl
  | b :: l, t => by simp only [List.foldl, hf]; exact foldl_restrict M f hf l _

/-- `finishInstr` copies the context's promise list into the thread and
otherwise ignores `prom` and `mem`. -/
theorem finishInstr_restrict (M : Memory) (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews)
    (st : I.State) (c : Ctx) :
    finishInstr t d iv st (c.restrict M) = (finishInstr t d iv st c).map (Thread.restrict M) := by
  have e0 : ({ t with st, views := (c.restrict M).views, prom := (c.restrict M).prom } : Thread I) =
      Thread.restrict M { t with st, views := c.views, prom := c.prom } := rfl
  have hset : ∀ (t : Thread I) r rv wv, (t.restrict M).setRegView r rv wv = (t.setRegView r rv wv).restrict M :=
    fun _ _ _ _ => rfl
  unfold finishInstr
  simp only [e0]
  rw [foldl_restrict M _ (fun t r => hset t r _ _)]
  rw [foldl_restrict M _ (fun t r => hset t r _ _)]
  have hz : ∀ t : Thread I, (d.loadDefs.zip c.loadViews).foldl
      (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) (t.restrict M) =
      ((d.loadDefs.zip c.loadViews).foldl (fun t (rv : I.RegId × View) => t.setRegView rv.1 rv.2 rv.2) t).restrict M :=
    foldl_restrict M _ (fun t rv => hset t rv.1 _ _) _
  have hv : ∀ t : Thread I, d.loadDefs.foldl
      (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) (t.restrict M) =
      (d.loadDefs.foldl (fun t r => t.setRegView r (c.loadViews.foldl max 0) (c.loadViews.foldl max 0)) t).restrict M :=
    foldl_restrict M _ (fun t r => hset t r _ _) _
  have hrs : ∀ t : Thread I, d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r)
      (max (t.wviewOf r) (c.loadViews.foldl max 0))) (t.restrict M) =
      (d.loadDefs.foldl (fun t r => t.setRegView r (t.rviewOf r)
      (max (t.wviewOf r) (c.loadViews.foldl max 0))) t).restrict M :=
    foldl_restrict M _ (fun t r => hset t r _ _) _
  simp only [Ctx.restrict]
  by_cases hc : (d.casLike && c.rmwWrote) = true <;>
  by_cases hb : d.isBranch = true <;>
  by_cases hl : (d.loadDefs.length == c.loadViews.length) = true <;>
  simp only [hc, hb, hl, ite_true, ite_false, Bool.false_eq_true, List.map] <;>
  (try rw [hrs]) <;> (try rw [hz]) <;> (try rw [hv]) <;> rfl

/-- **One instruction, replayed on a memory prefix.** An instruction run
against `M'` whose resulting thread is bounded by a prefix `M` of `M'`
(`relPre ≤ |M|`, and its non-temporal stores in `M`) appended nothing, and the
same run is available against `M` from the thread with its promises above
`|M|` dropped. -/
theorem stepOne_restrict (A : Arch) {t : Thread I} {tid : Nat} {M M' : Memory} (hM : M.Prefix M')
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid M' = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) (hb : o.thread.views.relPre ≤ M.last)
    (hnt : o.thread.views.vwOldNT ≤ M.last) :
    o.mem = M' ∧ ∃ outs', stepOne A (t.restrict M) tid M = some outs' ∧
      .ok { o with thread := o.thread.restrict M, mem := M } ∈ outs' := by
  have hbNT : o.thread.views.relPreNT ≤ M.last := by simp only [Views.relPreNT]; omega_t
  have hmem : o.mem = M' := by
    obtain ⟨-, -, -, hm, -, -⟩ := stepOne_silent_nt A hstep ho hf
    rcases hm with hm | hm
    · exact hm
    · have := hM.last_le
      have := o.thread.views.vwAll_le_relPreNT
      omega_t
  refine ⟨hmem, ?_⟩
  unfold stepOne at hstep ⊢
  cases hex : I.exec t.st with
  | none => rw [hex] at hstep; cases hstep
  | some tree =>
    rw [hex] at hstep
    have hstep' : _ = outs := Option.some.inj hstep
    subst hstep'
    refine ⟨_, show (I.exec t.st >>= _) = _ by rw [hex]; rfl, ?_⟩
    rw [List.mem_flatMap] at ho ⊢
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      obtain ⟨-, hv⟩ := finishInstr_relKey hth
      obtain ⟨hrel, -, -⟩ := Views.relPre_congr hv
      have hrelNT : th.views.relPreNT = c'.views.relPreNT := by
        simp only [Views.relPreNT, hrel, Views.vwOldNT_congr hv]
      refine ⟨.ok (st, c'.restrict M), runTree_restrict A tid _ hM tree _ st c' hf rfl hr (hrelNT ▸ hbNT), ?_⟩
      simp only [List.mem_map, Except.ok.injEq]
      refine ⟨th.restrict M, ?_, ?_⟩
      · have := finishInstr_restrict M t (I.deps t.st) (instrViews t (I.deps t.st)) st c'
        exact this ▸ List.mem_map_of_mem hth
      · rfl

theorem Memory.Prefix.append (M : Memory) (w : Msg) : M.Prefix (M.append w).1 :=
  ⟨rfl, by simp only [Memory.append, Array.toList_push]; exact List.prefix_append _ _⟩

theorem Memory.Prefix.stepOne {A : Arch} {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : mem.Prefix o.mem := by
  obtain ⟨h1, h2⟩ := stepOne_ext A hstep ho
  exact ⟨h1, by rw [h2]; exact List.prefix_append _ _⟩

theorem Thread.restrict_eq {M : Memory} {t : Thread I} (h : ∀ p ∈ t.prom, p ≤ M.last) : t.restrict M = t := by
  show { t with prom := _ } = t
  rw [List.filter_eq_self.mpr (fun p hp => decide_eq_true (h p hp))]

/-- **(S1′) on machine paths.** Fix a memory `M`, a thread state `t`, and a
path to `c1` along which thread `tid` ends in a state `t1` bounded by `M`
(`relPre ≤ |M|`). If, at some configuration on the path, which is well formed
and whose memory extends `M`, the thread's state `tm` restricted to `M` is
reachable from `(t, M)` by a promise-free run against `M` alone, then so is
`t1` restricted to `M`. Other threads only extend memory; the thread's own
instructions on the path are bounded by `M`, so they append nothing and replay
against `M` (`stepOne_restrict`); its own promises lie above `|M|` and are
dropped by the restriction. The thread's non-temporal stores at `t1` must lie
in `M` (`Thread.NoNTStores`, a temporary restriction; trivial under
`Arch.armv8`). -/
theorem advance_path {A : Arch} {M : Memory} {tid : Nat} {t : Thread I}
    {c1 : Config I} {t1 : Thread I} (ht1 : c1.threads[tid]? = some t1) (hb : t1.views.relPre ≤ M.last)
    {c : Config I} (hr : ReachableK A c c1) (hwf : c.Wf) (hM : M.Prefix c.mem) {tm : Thread I}
    (htm : c.threads[tid]? = some tm) (hnp : ThreadNP A tid (t, M) (tm.restrict M, M))
    (hnt : t1.NoNTStores (M.last + 1)) :
    ThreadNP A tid (t, M) (t1.restrict M, M) := by
  induction hr generalizing tm with
  | refl => rw [ht1] at htm; cases htm; exact hnp
  | @step c c' c'' hs hr' ih =>
    have hwf' := hwf.succ hs
    have hlt := lt_size_of_get? htm
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      by_cases hij : j = tid
      · subst hij
        rw [htm] at hj; cases hj
        have h1 : (c.withThread j o.thread o.mem).threads[j]? = some o.thread := by
          simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
        obtain ⟨t', h', hle⟩ := hr'.relPre_mono hwf' h1
        obtain ⟨t'', h'', hle'⟩ := hr'.vwOldNT_mono hwf' h1
        rw [ht1] at h' h''; cases h'; cases h''
        have hnt' : o.thread.views.vwOldNT ≤ M.last := by rcases hnt with h | h <;> omega_t
        obtain ⟨hmem, outs', hstep', ho'⟩ :=
          stepOne_restrict A hM hstep ho (hwf j tm htm).1 (Nat.le_trans hle hb) hnt'
        refine ih ht1 hwf' (by simp only [Config.withThread]; rw [hmem]; exact hM) h1
          (hnp.tail ⟨outs', _, hstep', ho', rfl⟩)
      · have h1 : (c.withThread j o.thread o.mem).threads[tid]? = some tm := by
          simp only [Config.withThread_get? c _ _ (lt_size_of_get? hj), hij, ↓reduceIte, htm]
        exact ih ht1 hwf' (hM.trans (Memory.Prefix.stepOne hstep ho)) h1 hnp
    | @promise j tj p hj _ =>
      have hM' : M.Prefix (c.mem.append { p.1 with tid := j }).1 := hM.trans (Memory.Prefix.append _ _)
      by_cases hij : j = tid
      · subst hij
        rw [htm] at hj; cases hj
        have h1 := (Config.withThread_get? c (i := j) { tm with prom := tm.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 hlt)
        simp only [↓reduceIte] at h1
        refine ih ht1 hwf' hM' h1 ?_
        have hgt : ¬ (c.mem.append { p.1 with tid := j }).2 ≤ M.last := by
          have := hM.last_le; simp only [Memory.append, Memory.last] at this ⊢; omega_t
        have : Thread.restrict M { tm with prom := tm.prom ++ [(c.mem.append { p.1 with tid := j }).2] } =
            tm.restrict M := by
          show { tm with prom := _ } = { tm with prom := _ }
          rw [List.filter_append]
          simp only [List.filter_cons, decide_eq_true_eq, hgt, ↓reduceIte, List.filter_nil, List.append_nil]
        rw [this]; exact hnp
      · have h1 := (Config.withThread_get? c (i := tid) { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 (lt_size_of_get? hj))
        simp only [hij, ↓reduceIte, htm] at h1
        exact ih ht1 hwf' hM' h1 hnp

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- A write that fulfils the outstanding promise `ts` keeps memory and puts
`vwOld` at `ts` (or keeps it, if larger). -/
theorem writeSuccs_fulfil {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    {ts : Time} (hin : ts ∈ c.prom) (hout : ts ∉ c'.prom) :
    c'.views.vwOld ≤ max c.views.vwOld ts := by
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
      simp only [afterWrite, Views.setCoh]
      split <;> omega_t
    · cases h
  · have h := mem_ite_nil' h
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

theorem StoreKind.beq_nt_false {k : StoreKind} (hk : k ≠ .nt) : (k == StoreKind.nt) = false := by
  cases k
  · rfl
  · rfl
  · exact absurd rfl hk

/-- A store that is not non-temporal leaves `vwOldNT` alone. -/
theorem writeSuccs_vwOldNT {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (hk : A.storeKind k ≠ .nt) :
    c'.views.vwOldNT = c.views.vwOldNT := by
  have hk' := StoreKind.beq_nt_false hk
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp only [afterWrite, hk', Bool.false_eq_true, ↓reduceIte]
    · cases h
  · have h := mem_ite_nil' h
    rw [List.mem_singleton] at h
    subst h
    simp only [afterWrite, hk', Bool.false_eq_true, ↓reduceIte]

theorem readSuccs_vwOldNT {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : x.2.2.views.vwOldNT = c.views.vwOldNT := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    rfl

theorem fenceOpt_vwOldNT (c : Ctx) (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).views.vwOldNT = c.views.vwOldNT := by
  cases b
  · rfl
  · exact (fenceStep_fields c k).2.2.2.2.2.2

theorem rmwPost_vwOldNT (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwPost A k noRet l c).views.vwOldNT = c.views.vwOldNT := by
  unfold rmwPost; split <;> rfl

/-- **A release fulfilment replays on a memory prefix.** If some run of the
instruction from `c` (memory `M'`) fulfils `ts ≤ |M|` with a release store,
so does a run from `c` restricted to the prefix `M`: the run before the store
is release-bounded for `ts` (`EvTree.RelFulfils.relPre_lt`), so it reads and
writes within `|M|`, provided the thread's non-temporal stores lie in `M` and
the instruction makes none (`EvTree.NoNT`; a temporary restriction). -/
theorem EvTree.RelFulfils.restrict {M M' : Memory} (hM : M.Prefix M') {ts : Time} (hts : ts ≤ M.last)
    {σ : Type} (tree : EvTree σ) :
    ∀ c : Ctx, c.views.FwdOk → c.mem = M' → EvTree.RelFulfils A tid iv ts c tree →
      c.views.vwOldNT ≤ M.last → tree.NoNT A →
      EvTree.RelFulfils A tid iv ts (c.restrict M) tree := by
  have hML := hM.last_le
  induction tree with
  | done s => intro c _ _ h; exact h.elim
  | fault m => intro c _ _ h; exact h.elim
  | choose n k ih =>
    intro c hf hm ⟨i, h⟩ hnt hno
    exact ⟨i, ih i c hf hm h hnt (hno i)⟩
  | load k xcl l ret ih =>
    intro c hf hm ⟨x, hx, h⟩ hnt hno
    have hs := readSuccs_silent A iv hf hx
    have hnt' : x.2.2.views.vwOldNT ≤ M.last := (readSuccs_vwOldNT A iv hx) ▸ hnt
    have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ hs.fwd h
    have hle : x.1 ≤ M.last := by
      have := readSuccs_le A iv hf hx; simp only [Views.relPreNT] at this; omega_t
    exact ⟨_, readSuccs_restrict A iv (hm ▸ hM) hx hle,
      ih x.2.1 x.2.2 hs.fwd ((readSuccs_mp A iv hx).1.trans hm) h hnt' (hno x.2.1)⟩
  | store k xcl l v ret ih =>
    intro c hf hm h hnt hno
    rcases h with ⟨c', hc', h | h⟩ | h
    · have hlt := writeSuccs_rel_relPre A tid _ hc' h.1 h.2.1 h.2.2
      have hvw := writeSuccs_fulfil A tid _ hc' h.2.1 h.2.2
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hle : c'.views.vwAll ≤ M.last := by simp only [Views.relPre, Views.vwAll] at hlt ⊢; omega_t
      refine Or.inl ⟨c'.restrict M, writeSuccs_restrict A tid _ (hm ▸ hM) hc' hle, Or.inl ⟨h.1, ?_, ?_⟩⟩
      · exact List.mem_filter.mpr ⟨h.2.1, by simpa using hts⟩
      · exact fun hc => h.2.2 (List.mem_filter.mp hc).1
    · have hs := writeSuccs_silent A tid _ hf hc'
      have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ hs.fwd h
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hle : c'.views.vwAll ≤ M.last := by simp only [Views.relPre, Views.vwAll] at hlt ⊢; omega_t
      have hm' : c'.mem = M' := by
        rcases hs.mem with h0 | h0
        · exact h0.trans hm
        · exfalso; rw [hm] at h0; omega_t
      exact Or.inl ⟨c'.restrict M, writeSuccs_restrict A tid _ (hm ▸ hM) hc' hle,
        Or.inr (ih true c' hs.fwd hm' h (hnt'.symm ▸ hnt) (hno.2 true))⟩
    · have hs : Ctx.Silent c
          { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq hf rfl rfl rfl rfl rfl rfl rfl ⟨_, rfl, by simp⟩
      exact Or.inr (ih false _ hs.fwd hm h hnt (hno.2 false))
  | fence k ret ih =>
    intro c hf hm h hnt hno
    show EvTree.RelFulfils A tid iv ts (fenceStep (c.restrict M) k) (ret ())
    rw [fenceStep_restrict]
    exact ih () _ (Ctx.Silent.fenceStep hf k).fwd ((fenceStep_mem c k).trans hm) h
      ((fenceStep_fields c k).2.2.2.2.2.2 ▸ hnt) hno
  | rmw k noRet l op ret ih =>
    intro c hf hm ⟨x, hx, h⟩ hnt hno
    have h1 := Ctx.Silent.fenceOpt hf A.rmwFence .sy
    have hm1 : (if A.rmwFence then fenceStep c .sy else c).mem = M' := by
      split <;> simp only [fenceStep_mem, hm]
    have h2 := readSuccs_silent A iv h1.fwd hx
    have hm2 : x.2.2.mem = M' := (readSuccs_mp A iv hx).1.trans hm1
    have hnt2 : x.2.2.views.vwOldNT ≤ M.last := by
      rw [readSuccs_vwOldNT A iv hx, fenceOpt_vwOldNT]; exact hnt
    have hread : x.2.2.views.relPre < ts →
        (x.1, x.2.1, x.2.2.restrict M) ∈ readSuccs A iv (if A.rmwFence then fenceStep (c.restrict M) .sy
          else c.restrict M) (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet := by
      intro hlt
      rw [fenceOpt_restrict]
      refine readSuccs_restrict A iv (hm1 ▸ hM) hx ?_
      have := readSuccs_le A iv h1.fwd hx; simp only [Views.relPreNT] at this; omega_t
    rcases h with h | ⟨new, hop, c', hc', h | h⟩
    · have h3 := Ctx.Silent.fenceOpt h2.fwd A.rmwFence .sy
      have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ h3.fwd h
      refine ⟨_, hread (Nat.lt_of_le_of_lt h3.relPre hlt), Or.inl ?_⟩
      show EvTree.RelFulfils A tid iv ts (if A.rmwFence then fenceStep (x.2.2.restrict M) .sy
        else x.2.2.restrict M) (ret x.2.1)
      rw [fenceOpt_restrict]
      have hm3 : (if A.rmwFence then fenceStep x.2.2 .sy else x.2.2).mem = M' := by
        split <;> simp only [fenceStep_mem, hm2]
      exact ih x.2.1 _ h3.fwd hm3 h ((fenceOpt_vwOldNT _ _ _).symm ▸ hnt2) (hno.2 x.2.1)
    · have hlt := writeSuccs_rel_relPre A tid _ hc' h.1 h.2.1 h.2.2
      have hvw := writeSuccs_fulfil A tid _ hc' h.2.1 h.2.2
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hle : c'.views.vwAll ≤ M.last := by simp only [Views.relPre, Views.vwAll] at hlt ⊢; omega_t
      refine ⟨_, hread hlt, Or.inr ⟨new, hop, c'.restrict M,
        writeSuccs_restrict A tid _ (hm2 ▸ hM) hc' hle, Or.inl ⟨h.1, ?_, ?_⟩⟩⟩
      · exact List.mem_filter.mpr ⟨h.2.1, by simpa using hts⟩
      · exact fun hc => h.2.2 (List.mem_filter.mp hc).1
    · have h3 := writeSuccs_silent A tid _ h2.fwd hc'
      have h4 := h3.trans (Ctx.Silent.rmwPost h3.fwd A k noRet l)
      have h5 := h4.trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)
      have hlt := EvTree.RelFulfils.relPre_lt A tid iv _ _ h5.fwd h
      have hnt' := writeSuccs_vwOldNT A tid _ hc' hno.1
      have hvw3 : c'.views.vwAll ≤ M.last := by
        have := ((Ctx.Silent.rmwPost h3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)).relPre
        simp only [Views.relPre, Views.vwAll] at this hlt ⊢; omega_t
      have hm3 : c'.mem = M' := by
        rcases h3.mem with h0 | h0
        · exact h0.trans hm2
        · exfalso; rw [hm2] at h0; omega_t
      refine ⟨_, hread (Nat.lt_of_le_of_lt h3.relPre (Nat.lt_of_le_of_lt
        ((Ctx.Silent.rmwPost h3.fwd A k noRet l).trans (Ctx.Silent.fenceOpt h4.fwd A.rmwFence .sy)).relPre hlt)),
        Or.inr ⟨new, hop, c'.restrict M, writeSuccs_restrict A tid _ (hm2 ▸ hM) hc' hvw3, Or.inr ?_⟩⟩
      rw [rmwPost_restrict, fenceOpt_restrict]
      have hm5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c').mem = M' := by
        split <;> simp only [fenceStep_mem, rmwPost_mem, hm3]
      have hnt5 : (if A.rmwFence then fenceStep (rmwPost A k noRet l c') .sy else rmwPost A k noRet l c').views.vwOldNT
          ≤ M.last := by
        rw [fenceOpt_vwOldNT, rmwPost_vwOldNT, hnt']; exact hnt2
      exact ih x.2.1 _ h5.fwd hm5 h hnt5 (hno.2 x.2.1)

end Rules

theorem Thread.RelFulfils.restrict {A : Arch} {tid : Nat} {ts : Time} {t : Thread I} {M M' : Memory}
    (hM : M.Prefix M') (hts : ts ≤ M.last) (hf : t.views.FwdOk) (h : t.RelFulfils A tid ts M')
    (hnt : t.views.vwOldNT ≤ M.last) (hnx : t.NextNoNT A) :
    (t.restrict M).RelFulfils A tid ts M := by
  obtain ⟨tree, hex, h⟩ := h
  exact ⟨tree, hex, EvTree.RelFulfils.restrict A tid _ hM hts tree _ hf rfl h hnt (hnx tree hex)⟩

/-- Memory only grows along a `ReachableK` path (the `ReachableK` twin of
`Reachable.mem_prefix`). -/
theorem Live.Bridge.ReachableK.mem_prefix {A : Arch} {c c' : Config I}
    (h : ReachableK A c c') : c.mem.Prefix c'.mem := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih =>
    refine Memory.Prefix.trans ?_ ih
    cases hs with
    | instr _ hstep ho => exact Memory.Prefix.stepOne hstep ho
    | promise _ _ => exact Memory.Prefix.append _ _

/-- Memory only grows along a machine path. -/
theorem Reachable.mem_prefix {A : Arch} [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : Reachable A fuel c c') : c.mem.Prefix c'.mem :=
  (ReachableK.of_reachable h).mem_prefix

/-- **(S1′) for every program.** Let thread `tid` of a reachable
configuration `c` have the outstanding promise `ts`, and let some path from
`c`, under any schedule, reach a configuration where the thread, with `ts`
still outstanding, is about to fulfil `ts` with a release store. Then `c` is
`Advanceable` for `ts`: the thread alone, without changing memory, reaches
that state (restricted to `c.mem`), and from there its next instruction
fulfils `ts` with a release store against `c.mem`. Temporary restriction
(lifted by `Config.advanceableNT_of_path`): at `t1` the thread has made no non-temporal store at or after
`ts` and its next instruction makes none (`Thread.NoNTStores`,
`Thread.NextNoNT`; both hold under `Arch.armv8`). -/
theorem Config.advanceable_of_path {A : Arch} {c0 c c1 : Config I}
    (h0 : c0.Wf) (hc : ReachableK A c0 c) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t)
    {ts : Time} (hts : ts ∈ t.prom) (hr : ReachableK A c c1) {t1 : Thread I}
    (ht1 : c1.threads[tid]? = some t1) (hts1 : ts ∈ t1.prom) (hrel : t1.RelFulfils A tid ts c1.mem)
    (hnt : t1.NoNTStores ts) (hnx : t1.NextNoNT A) :
    c.Advanceable A tid ts := by
  have hwf := h0.reachable hc
  have hwf1 := hwf.reachable hr
  have hf1 := (hwf1 tid t1 ht1).1
  have hle : ts ≤ c.mem.last := (hwf tid t ht).2 ts hts
  have hb := hrel.relPre_lt hf1
  have hnp0 : ThreadNP A tid (t, c.mem) (t.restrict c.mem, c.mem) := by
    rw [Thread.restrict_eq (hwf tid t ht).2]; exact .refl _
  have hnt' : t1.views.vwOldNT ≤ c.mem.last := by rcases hnt with h | h <;> omega_t
  refine ⟨t, t1.restrict c.mem, ht, hts,
    advance_path ht1 (Nat.le_of_lt (Nat.lt_of_lt_of_le hb hle)) hr hwf (.refl _) ht hnp0 (.inr (by omega_t)),
    List.mem_filter.mpr ⟨hts1, by simpa using hle⟩, hrel.restrict hr.mem_prefix hle hf1 hnt' hnx⟩

/-- **(S1′) gives a variant-(ii) virtual configuration**: advance the thread
alone to the state where its release is pending at its next instruction;
memory and every other thread are unchanged. -/
theorem Config.Advanceable.virtualOf {A : Arch} {c : Config I} {tid : Nat} {ts : Time}
    (h : c.Advanceable A tid ts) :
    ∃ v t', c.VirtualOf A v ∧ v.threads[tid]? = some t' ∧ ts ∈ t'.prom ∧ t'.RelFulfils A tid ts v.mem := by
  obtain ⟨t, t', ht, -, hnp, hts', hrel⟩ := h
  have hlt := lt_size_of_get? ht
  refine ⟨c.withThread tid t' c.mem, t', ⟨rfl, Config.withThread_size c tid t' c.mem, fun i ti hi => ?_⟩,
    by simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte], hts', hrel⟩
  by_cases hij : tid = i
  · subst hij
    rw [ht] at hi; cases hi
    exact ⟨t', by simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte], hnp, .inr ⟨ts, hts', hrel⟩⟩
  · exact ⟨ti, by simp only [Config.withThread_get? c _ _ hlt, hij, ↓reduceIte, hi], .refl _, .inl rfl⟩

/-! ## The non-temporal restriction is vacuous under `Arch.armv8`

`Arch.armv8` maps every store kind, `.nt` included, to `.plain` or `.rel`, so
no thread ever performs a non-temporal store and `vwOldNT` stays `0`:
`Thread.NoNTStores` and `Thread.NextNoNT` hold for every thread of every
configuration reachable from `Config.init`, for every ISA run under the
ARMv8 profile (AArch64, and `Toy` under `.armv8`). Under `Arch.tso` they
fail only for x86 programs that use `movnti` (Toy's `st .nt`). -/

theorem Arch.armv8_storeKind_ne_nt (k : StoreKind) : Arch.armv8.storeKind k ≠ .nt := by
  cases k <;> simp [Arch.storeKind, Arch.armv8]

theorem EvTree.noNT_armv8 {σ : Type} (tree : EvTree σ) : tree.NoNT Arch.armv8 := by
  induction tree with
  | done => trivial
  | fault => trivial
  | choose n k ih => exact ih
  | load k xcl l ret ih => exact ih
  | store k xcl l v ret ih => exact ⟨Arch.armv8_storeKind_ne_nt k, ih⟩
  | rmw k noRet l op ret ih => exact ⟨Arch.armv8_storeKind_ne_nt _, ih⟩
  | fence k ret ih => exact ih ()

theorem Thread.nextNoNT_armv8 (t : Thread I) : t.NextNoNT Arch.armv8 :=
  fun tree _ => tree.noNT_armv8

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- A run of an event tree without non-temporal stores leaves `vwOldNT`
alone. -/
theorem runTree_vwOldNT {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), tree.NoNT A → .ok (s, c') ∈ runTree A tid iv c tree →
      c'.views.vwOldNT = c.views.vwOldNT := by
  induction tree with
  | done s0 =>
    intro c s c' _ h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | fault msg =>
    intro c s c' _ h
    simp [runTree] at h
  | choose n k ih =>
    intro c s c' hno h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, _, hi⟩ := h
    exact ih i c s c' (hno i) hi
  | load k xcl l ret ih =>
    intro c s c' hno h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨⟨t, v, c0⟩, h0, h⟩ := h
    exact (ih v c0 s c' (hno v) h).trans (readSuccs_vwOldNT A iv h0)
  | store k xcl l v ret ih =>
    intro c s c' hno h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (ih true c0 s c' (hno.2 true) h).trans (writeSuccs_vwOldNT A tid _ hc0 hno.1)
    · rw [List.mem_ite_nil_right] at h
      have := ih false _ s c' (hno.2 false) h.2
      exact this
  | fence k ret ih =>
    intro c s c' hno h
    simp only [runTree] at h
    exact (ih () _ s c' hno h).trans (fenceStep_fields c k).2.2.2.2.2.2
  | rmw k noRet l op ret ih =>
    intro c s c' hno h
    simp only [runTree] at h
    have h1 := fenceOpt_vwOldNT c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 : c2.views.vwOldNT = c.views.vwOldNT := (readSuccs_vwOldNT A iv h2).trans h1
    simp only at h
    split at h
    · exact (ih old _ s c' (hno.2 old) h).trans ((fenceOpt_vwOldNT c2 A.rmwFence .sy).trans h12)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      have h23 := (writeSuccs_vwOldNT A tid _ hc3 hno.1).trans h12
      refine (ih old _ s c' (hno.2 old) h).trans ?_
      rw [fenceOpt_vwOldNT]
      split
      · exact h23
      · exact h23

end Rules

/-- An instruction without non-temporal stores leaves `vwOldNT` alone. -/
theorem stepOne_vwOldNT (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hnx : t.NextNoNT A) : o.thread.views.vwOldNT = t.views.vwOldNT := by
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
      obtain ⟨-, hv⟩ := finishInstr_relKey hth
      exact (Views.vwOldNT_congr hv).trans (runTree_vwOldNT A tid _ tree _ st c' (hnx tree hex) hr)

/-- Under `Arch.armv8`, `vwOldNT = 0` for every thread, along every
`ReachableK` path (the `ReachableK` twin of `Reachable.vwOldNT_armv8`). -/
theorem Live.Bridge.ReachableK.vwOldNT_armv8 {c c' : Config I}
    (h : ReachableK Arch.armv8 c c') (h0 : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.views.vwOldNT = 0) :
    ∀ (i : Nat) (t : Thread I), c'.threads[i]? = some t → t.views.vwOldNT = 0 := by
  induction h with
  | refl => exact h0
  | @step c c1 c2 hs _ ih =>
    apply ih
    intro i t ht
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at ht
      split at ht
      · cases ht
        exact (stepOne_vwOldNT _ hstep ho (Thread.nextNoNT_armv8 tj)).trans (h0 j tj hj)
      · exact h0 i t ht
    | @promise j tj p hj _ =>
      rw [Config.withThread_get? c _ _ (lt_size_of_get? hj)] at ht
      split at ht
      · cases ht
        exact h0 j tj hj
      · exact h0 i t ht

/-- Under `Arch.armv8`, `vwOldNT = 0` for every thread, along every path. -/
theorem Reachable.vwOldNT_armv8 [I.LawfulState] {fuel : Nat} {c c' : Config I}
    (h : Reachable Arch.armv8 fuel c c') (h0 : ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → t.views.vwOldNT = 0) :
    ∀ (i : Nat) (t : Thread I), c'.threads[i]? = some t → t.views.vwOldNT = 0 :=
  (ReachableK.of_reachable h).vwOldNT_armv8 h0

/-- **The restriction holds under `Arch.armv8`**: every thread of every
configuration reachable from `Config.init` has made no non-temporal store
(and its next instruction makes none, `Thread.nextNoNT_armv8`). Discharges
the `Thread.NoNTStores` hypotheses of (S2)/(S1′) for AArch64 and `Toy`. -/
theorem Thread.noNTStores_armv8 {states : List I.State}
    {initMem : List (Loc × Val)} {c : Config I}
    (hc : ReachableK Arch.armv8 (Config.init states initMem) c) {i : Nat} {t : Thread I}
    (ht : c.threads[i]? = some t) (ts : Time) : t.NoNTStores ts := by
  refine .inl (hc.vwOldNT_armv8 (fun i t h => ?_) i t ht)
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨st, -, rfl⟩ := h
  rfl

/-! ## Live configurations: outstanding promises lie above `vwNew`

Every write of a thread, fresh or fulfilling, lies above its `vwNew`
(`writeSuccs`' pre-view), and `vwNew` only grows; an acquire read raises it
to the message read. So once a thread's `vwNew` has reached `q` (e.g. it has
acquired a message at `q`), none of its outstanding promises at or below `q`
can ever be fulfilled, and a configuration with such a promise reaches no
final configuration (`Config.Live.vwNew_lt`). This is the machine half of the
proposed R3/R2′ argument. -/

/-- One context step orders writes: `vwNew` only grows, and a promise that
disappears was fulfilled above the old `vwNew`. -/
structure Ctx.WOrd (c c' : Ctx) : Prop where
  vwNew : c.views.vwNew ≤ c'.views.vwNew
  prom : ∀ ts ∈ c.prom, ts ∉ c'.prom → c.views.vwNew < ts

theorem Ctx.WOrd.refl (c : Ctx) : c.WOrd c := ⟨Nat.le_refl _, fun _ h h' => absurd h h'⟩

theorem Ctx.WOrd.trans {c c' c'' : Ctx} (h₁ : c.WOrd c') (h₂ : c'.WOrd c'') : c.WOrd c'' := by
  refine ⟨Nat.le_trans h₁.vwNew h₂.vwNew, fun ts h h'' => ?_⟩
  by_cases h' : ts ∈ c'.prom
  · exact Nat.lt_of_le_of_lt h₁.vwNew (h₂.prom ts h' h'')
  · exact h₁.prom ts h h'

theorem Ctx.WOrd.of_eq {c c' : Ctx} (h1 : c.views.vwNew ≤ c'.views.vwNew) (h2 : c'.prom = c.prom) : c.WOrd c' :=
  ⟨h1, fun _ h h' => absurd (h2 ▸ h) h'⟩

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_word {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.WOrd x.2.2 := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    refine .of_eq ?_ rfl
    simp only
    split <;> omega_t

theorem writeSuccs_word {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c.WOrd c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨-, hb, -⟩ := hc
      refine ⟨by simp only [afterWrite, Views.setCoh]; omega_t, fun ts hin hout => ?_⟩
      simp only [afterWrite] at hout
      have hts : ts = t := by
        by_cases hne : ts = t
        · exact hne
        · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
      subst hts
      omega_t
    · cases h
  · split at h
    rename_i t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hcond, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    refine ⟨by simp only [afterWrite, Views.setCoh]; omega_t, fun ts hin hout => ?_⟩
    simp only [afterWrite] at hout
    by_cases hne : ts = t
    · subst hne; omega_t
    · exact absurd ((List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)) hout

theorem Ctx.WOrd.fenceStep (c : Ctx) (k : FenceKind) : c.WOrd (Kraken.Promising.fenceStep c k) := by
  refine .of_eq ?_ (fenceStep_fields c k).2.2.2.2.1
  cases k <;> simp only [Kraken.Promising.fenceStep] <;> omega_t

theorem Ctx.WOrd.fenceOpt (c : Ctx) (b : Bool) (k : FenceKind) :
    c.WOrd (if b then Kraken.Promising.fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact .fenceStep c k

theorem Ctx.WOrd.rmwPost (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) :
    c.WOrd (Kraken.Promising.rmwPost A k noRet l c) := by
  unfold Kraken.Promising.rmwPost
  split
  · exact .of_eq (by simp only; omega_t) rfl
  · exact .of_eq (Nat.le_refl _) rfl

theorem runTree_word {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.WOrd c' := by
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
    exact (readSuccs_word A iv hx).trans (ih x.2.1 x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_word A tid _ hc0).trans (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have h0 : c.WOrd { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq (Nat.le_refl _) rfl
      exact h0.trans (ih false _ s c' h.2)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (Ctx.WOrd.fenceStep c k).trans (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := Ctx.WOrd.fenceOpt c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_word A iv h2)
    simp only at h
    split at h
    · exact (h12.trans (Ctx.WOrd.fenceOpt c2 A.rmwFence .sy)).trans (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine ((h12.trans (writeSuccs_word A tid _ hc3)).trans ?_).trans (ih old _ s c' h)
      exact (Ctx.WOrd.rmwPost A c3 k noRet l).trans (Ctx.WOrd.fenceOpt _ A.rmwFence .sy)

end Rules

/-- An acquire read of a message not forwarded from the thread's own write
(every message of another thread) raises `vwNew` to the message read: every
later write of the thread lies above it. -/
theorem readSuccs_acq_vwNew (A : Arch) (iv : InstrViews) {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet)
    (hk : (A.loadKind k).isAcquire = true) (hfw : ∀ f, c.views.getFwd l = some f → f.time ≠ x.1) :
    x.1 ≤ x.2.2.views.vwNew := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    have : t ≤ readView A (A.loadKind k) (c.views.getFwd l) t := by
      unfold readView
      split
      · rename_i f hf
        have := hfw f hf
        simp only at this
        simp only [this, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact Nat.le_refl _
      · exact Nat.le_refl _
    simp only [hk, ↓reduceIte]
    omega_t

/-- One instruction orders the thread's writes after its `vwNew`. -/
theorem stepOne_word (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    t.views.vwNew ≤ o.thread.views.vwNew ∧ ∀ ts ∈ t.prom, ts ∉ o.thread.prom → t.views.vwNew < ts := by
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
      have hw := runTree_word A tid _ tree _ st c' hr
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      have hvw : th.views.vwNew = c'.views.vwNew := by have := congrArg Views.vwNew hv; exact this
      simp only [hvw, hp]
      exact ⟨hw.vwNew, hw.prom⟩

/-- **In a `LiveK` configuration every outstanding promise lies above its
thread's `vwNew`** (the `ReachableK` twin of `Config.Live.vwNew_lt`, fuel-free). -/
theorem Config.LiveK.vwNew_lt {A : Arch} {c : Config I} (hl : c.LiveK A)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.vwNew < ts := by
  obtain ⟨cf, hr, hf⟩ := hl
  induction hr generalizing t with
  | refl =>
    exfalso
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    have := (Array.all_eq_true.mp hf) i hi
    simp only [Bool.and_eq_true, List.isEmpty_iff] at this
    rw [this.2] at hts
    cases hts
  | @step c c' c'' hs _ ih =>
    have hlt := lt_size_of_get? ht
    cases hs with
    | @instr j tj outs o hj hstep ho =>
      by_cases hij : j = i
      · subst hij
        rw [ht] at hj; cases hj
        obtain ⟨hle, hful⟩ := stepOne_word A hstep ho
        by_cases hin : ts ∈ o.thread.prom
        · have h1 : (c.withThread j o.thread o.mem).threads[j]? = some o.thread := by
            simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
          exact Nat.lt_of_le_of_lt hle (ih h1 hin hf)
        · exact hful ts hts hin
      · have h1 : (c.withThread j o.thread o.mem).threads[i]? = some t := by
          simp only [Config.withThread_get? c _ _ (lt_size_of_get? hj), hij, ↓reduceIte, ht]
        exact ih h1 hts hf
    | @promise j tj p hj _ =>
      by_cases hij : j = i
      · subst hij
        rw [ht] at hj; cases hj
        have h1 := (Config.withThread_get? c (i := j) { t with prom := t.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 hlt)
        simp only [↓reduceIte] at h1
        have := ih h1 (List.mem_append_left _ hts) hf
        exact this
      · have h1 := (Config.withThread_get? c (i := i) { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 (lt_size_of_get? hj))
        simp only [hij, ↓reduceIte, ht] at h1
        exact ih h1 hts hf

/-- **In a live configuration every outstanding promise lies above its
thread's `vwNew`.** On a path to a final configuration every outstanding
promise is fulfilled by its thread's own instruction, above the thread's
`vwNew` at that point, which is at least its `vwNew` now. So a thread that
has acquired a message at `q` (an acquire read raises `vwNew` to `q`) has no
outstanding promise at or below `q` in any live configuration: such a
promise is *doomed*. No hypothesis on the program. -/
theorem Config.Live.vwNew_lt {A : Arch} [I.LawfulState] {fuel : Nat} {c : Config I} (hl : c.Live A fuel)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.vwNew < ts :=
  (Config.LiveK.of_live hl).vwNew_lt ht hts

end Kraken.Promising

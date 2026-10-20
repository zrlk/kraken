/-
Machine invariants of reachable configurations that the SLR-adapted
resource model's step lemmas assume.

S2a's `Erase.unfulfil` / `Erase.ofVirtualOf` take `promWf` (every outstanding
promise is a message of its thread), and S2b's `Erase.rmw_of_seen` takes the
thread half of RMW uniqueness, `Ctx.OwnCoh` (every message of the thread that
is not one of its outstanding promises is at most its coherence view of the
location). Both are machine facts about every program: this file proves them,
with the duplicate-freedom of promise sets that the lifting of write events
needs (`WriteAt.gone`), as invariants of every configuration reachable from a
well-formed one, for both ISAs (generic over `[I.LawfulState]`).

## Contents

- `Ctx.Inv`: the per-context invariant of thread `tid` (promises are
  distinct messages of `tid`; `Ctx.OwnCoh`), and `Ctx.OwnApp`: memory grows
  by messages of `tid` only. `runTree_inv`: every run of an instruction's
  event tree keeps `Ctx.Inv` and appends only `tid`'s messages.
- `Thread.Inv`, `stepOne_inv`: the same for one instruction of a thread.
- `Config.MachInv`: `promWf`, `promNodup`, `ownCoh` for every thread.
  `Config.MachInv.instr` / `.promise` / `.succ` / `.reachable` /
  `.npStepBy` / `.threadNP`, `Config.init_machInv`.
- `Config.MachInv.ctxInv`: the instruction context of a thread of a
  `MachInv` configuration satisfies `Ctx.Inv`, so `ownSeen_of_readSuccs`
  applies at every read of the instruction, not only the first.

`OwnCoh` is not stable under `EnvExt` (an environment extension may add a
message with the thread's id that is not one of its promises); the alternative
carries it, with `promWf`, as a `Reachable` invariant
(`Config.MachInv.reachable`) that Theorem 1′'s induction supplies.
-/
import Kraken.Promising.SLR.Rmw

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

private theorem ite_none_left_inv {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

/-! ## Contexts -/

/-- The invariant of thread `tid`'s context along an instruction: its
outstanding promises are distinct messages of `tid` (`promWf`), and every
other message of `tid` is at most its coherence view (`Ctx.OwnCoh`). -/
structure Ctx.Inv (tid : Nat) (c : Ctx) : Prop where
  prom : ∀ p ∈ c.prom, ∃ w, c.mem.get? p = some w ∧ w.tid = tid
  nodup : c.prom.Nodup
  own : c.OwnCoh tid

/-- From `c` to `c'` the memory grows, by messages of `tid` only. -/
structure Ctx.OwnApp (tid : Nat) (c c' : Ctx) : Prop where
  pre : c.mem.Prefix c'.mem
  tid : ∀ ts w, c.mem.last < ts → c'.mem.get? ts = some w → w.tid = tid

theorem Ctx.OwnApp.refl (tid : Nat) (c : Ctx) : c.OwnApp tid c :=
  ⟨Memory.Prefix.refl _, fun _ _ h hw => absurd (c.mem.last_le_of_get?_eq_some hw) (by omega_t)⟩

theorem Ctx.OwnApp.of_mem {tid : Nat} {c c' : Ctx} (hm : c'.mem = c.mem) : c.OwnApp tid c' := by
  refine ⟨hm ▸ Memory.Prefix.refl _, fun _ _ h hw => ?_⟩
  rw [hm] at hw
  exact absurd (c.mem.last_le_of_get?_eq_some hw) (by omega_t)

theorem Ctx.OwnApp.trans {tid : Nat} {c c' c'' : Ctx} (h₁ : c.OwnApp tid c') (h₂ : c'.OwnApp tid c'') :
    c.OwnApp tid c'' := by
  refine ⟨h₁.pre.trans h₂.pre, fun ts w hts hw => ?_⟩
  by_cases hle : ts ≤ c'.mem.last
  · rw [h₂.pre.get? hle] at hw
    exact h₁.tid ts w hts hw
  · exact h₂.tid ts w (by omega_t) hw

/-- A step that changes neither memory nor promises and only raises
coherence views keeps the invariant. -/
theorem Ctx.Inv.of_coh {tid : Nat} {c c' : Ctx} (h : c.Inv tid) (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hcoh : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) : c'.Inv tid ∧ c.OwnApp tid c' := by
  refine ⟨⟨?_, ?_, ?_⟩, .of_mem hm⟩
  · rw [hm, hp]; exact h.prom
  · rw [hp]; exact h.nodup
  · intro ts w hw htid hts
    rw [hm] at hw; rw [hp] at hts
    exact Nat.le_trans (h.own ts w hw htid hts) (hcoh _)

theorem Ctx.Inv.of_views {tid : Nat} {c c' : Ctx} (h : c.Inv tid) (hm : c'.mem = c.mem) (hp : c'.prom = c.prom)
    (hcoh : c'.views.coh = c.views.coh) : c'.Inv tid ∧ c.OwnApp tid c' :=
  h.of_coh hm hp fun l => by simp only [Views.getCoh, hcoh]; exact Nat.le_refl _

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_inv {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (h : c.Inv tid) :
    x.2.2.Inv tid ∧ c.OwnApp tid x.2.2 := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have ht := ite_none_left_inv ht
    simp only [Option.some.injEq] at ht
    subst ht
    refine h.of_coh rfl rfl fun l' => ?_
    refine Nat.le_trans ?_ (Nat.le_of_eq (Views.getCoh_setCoh c.views l l' _).symm)
    by_cases hl : l' = l
    · rw [ite_eq_left hl, hl]; exact Nat.le_max_left _ _
    · rw [ite_eq_right hl]; exact Nat.le_refl _

theorem afterWrite_getCoh {xr : View} (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time) (νfwd : View)
    (ful : Bool) (l' : Loc) :
    (afterWrite A iv c k xcl l v t νfwd ful xr).views.getCoh l' =
      if l' = l then max (c.views.getCoh l) t else c.views.getCoh l' := by
  exact Views.getCoh_setCoh c.views l l' t

theorem writeSuccs_inv {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (hc : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) (h : c.Inv tid) :
    c'.Inv tid ∧ c.OwnApp tid c' := by
  unfold writeSuccs at hc
  rw [List.mem_append, List.mem_filterMap] at hc
  rcases hc with ⟨t, htp, hc⟩ | hc
  · split at hc
    · rename_i w hw
      obtain ⟨hcond, hc⟩ := Option.ite_none_right_eq_some.mp hc
      simp only [Option.some.injEq] at hc
      subst hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨hl, -⟩, -⟩, -⟩ := hcond
      refine ⟨⟨?_, ?_, ?_⟩, .of_mem rfl⟩
      · intro p hp
        exact h.prom p (List.mem_of_mem_erase hp)
      · exact h.nodup.erase _
      · intro ts w' hw' htid hts
        change c.mem.get? ts = some w' at hw'
        change ts ∉ c.prom.erase t at hts
        rw [afterWrite_getCoh]
        by_cases hte : ts = t
        · subst hte
          rw [hw] at hw'; cases hw'
          simp only [hl, ↓reduceIte]; omega_t
        · have hts' : ts ∉ c.prom := fun hm => hts ((List.mem_erase_of_ne hte).mpr hm)
          have := h.own ts w' hw' htid hts'
          split <;> rename_i he
          · rw [he] at this; omega_t
          · exact this
    · cases hc
  · split at hc
    rename_i _ mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at hc
    obtain ⟨-, rfl⟩ := hc
    have ht : t = c.mem.last + 1 := (congrArg Prod.snd hok).symm
    have hm : mem' = (c.mem.append { loc := l, val := v, tid }).1 := (congrArg Prod.fst hok).symm
    subst ht hm
    have hnot : c.mem.last + 1 ∉ c.prom := fun hp => by
      obtain ⟨w, hw, -⟩ := h.prom _ hp
      have := c.mem.last_le_of_get?_eq_some hw
      omega_t
    have hpe : (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) = c.prom := by
      rw [List.erase_append_right _ hnot, List.erase_cons_head, List.append_nil]
    have hpre := Memory.Prefix.append c.mem { loc := l, val := v, tid }
    refine ⟨⟨?_, ?_, ?_⟩, ⟨hpre, ?_⟩⟩
    · intro p hp
      change p ∈ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) at hp
      rw [hpe] at hp
      obtain ⟨w, hw, htid⟩ := h.prom p hp
      exact ⟨w, (hpre.get? (c.mem.last_le_of_get?_eq_some hw)).trans hw, htid⟩
    · change ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).Nodup
      rw [hpe]; exact h.nodup
    · intro ts w' hw' htid hts
      change (c.mem.append { loc := l, val := v, tid }).1.get? ts = some w' at hw'
      change ts ∉ (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) at hts
      rw [hpe] at hts
      rw [afterWrite_getCoh]
      show ts ≤ if w'.loc = l then max (c.views.getCoh l) (c.mem.last + 1) else c.views.getCoh w'.loc
      rcases Memory.get?_append_eq_some _ _ hw' with ⟨hle, hw''⟩ | ⟨rfl, rfl⟩
      · have := h.own ts w' hw'' htid hts
        split <;> rename_i he
        · rw [he] at this; omega_t
        · exact this
      · simp only [↓reduceIte]; omega_t
    · intro ts w' hts hw'
      change (c.mem.append { loc := l, val := v, tid }).1.get? ts = some w' at hw'
      rcases Memory.get?_append_eq_some _ _ hw' with ⟨hle, -⟩ | ⟨-, rfl⟩
      · omega_t
      · rfl

theorem fenceStep_coh (c : Ctx) (k : FenceKind) : (fenceStep c k).views.coh = c.views.coh := by
  cases k <;> rfl

theorem fenceStep_inv {c : Ctx} (h : c.Inv tid) (k : FenceKind) :
    (fenceStep c k).Inv tid ∧ c.OwnApp tid (fenceStep c k) :=
  h.of_views (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 (fenceStep_coh c k)

theorem fenceOpt_inv {c : Ctx} (h : c.Inv tid) (b : Bool) (k : FenceKind) :
    (if b then fenceStep c k else c).Inv tid ∧ c.OwnApp tid (if b then fenceStep c k else c) := by
  cases b
  · exact ⟨h, .refl _ _⟩
  · exact fenceStep_inv tid h k

theorem rmwPost_inv {c : Ctx} (h : c.Inv tid) (k : RmwKind) (noRet : Bool) (l : Loc) :
    (rmwPost A k noRet l c).Inv tid ∧ c.OwnApp tid (rmwPost A k noRet l c) := by
  unfold rmwPost
  split
  · exact h.of_views rfl rfl rfl
  · exact h.of_views rfl rfl rfl

/-- **Every run of an instruction's event tree keeps the context invariant**
and appends only messages of the running thread. -/
theorem runTree_inv {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.Inv tid →
      c'.Inv tid ∧ c.OwnApp tid c' := by
  induction tree with
  | done s =>
    intro c s' c' h hc
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hc, .refl _ _⟩
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h hc
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h hc
  | load k xcl l ret ih =>
    intro c s c' h hc
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    obtain ⟨h1, h2⟩ := readSuccs_inv A tid iv hx hc
    obtain ⟨h3, h4⟩ := ih x.2.1 x.2.2 s c' h h1
    exact ⟨h3, h2.trans h4⟩
  | store k xcl l v ret ih =>
    intro c s c' h hc
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      obtain ⟨h1, h2⟩ := writeSuccs_inv A tid _ hc0 hc
      obtain ⟨h3, h4⟩ := ih true c0 s c' h h1
      exact ⟨h3, h2.trans h4⟩
    · rw [List.mem_ite_nil_right] at h
      have h0 : Ctx.Inv tid { c with views := { c.views with xclb := none }, succView := 0,
                                     log := c.log ++ [.xclFail l] } ∧
          c.OwnApp tid { c with views := { c.views with xclb := none }, succView := 0,
                                log := c.log ++ [.xclFail l] } := hc.of_views rfl rfl rfl
      obtain ⟨h1, h2⟩ := h0
      obtain ⟨h3, h4⟩ := ih false _ s c' h.2 h1
      exact ⟨h3, h2.trans h4⟩
  | fence k ret ih =>
    intro c s c' h hc
    simp only [runTree] at h
    obtain ⟨h1, h2⟩ := fenceStep_inv tid hc k
    obtain ⟨h3, h4⟩ := ih () _ s c' h h1
    exact ⟨h3, h2.trans h4⟩
  | rmw k noRet l op ret ih =>
    intro c s c' h hc
    simp only [runTree] at h
    obtain ⟨h1, h1'⟩ := fenceOpt_inv tid hc A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1 h1'
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    obtain ⟨h2a, h2b⟩ := readSuccs_inv A tid iv h2 h1
    simp only at h
    split at h
    · obtain ⟨h3, h3'⟩ := fenceOpt_inv tid h2a A.rmwFence .sy
      obtain ⟨h4, h4'⟩ := ih old _ s c' h h3
      exact ⟨h4, h1'.trans (h2b.trans (h3'.trans h4'))⟩
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      obtain ⟨h3, h3'⟩ := writeSuccs_inv A tid _ hc3 h2a
      obtain ⟨h4, h4'⟩ := rmwPost_inv A tid h3 k noRet l
      obtain ⟨h5, h5'⟩ := fenceOpt_inv tid h4 A.rmwFence .sy
      obtain ⟨h6, h6'⟩ := ih old _ s c' h h5
      exact ⟨h6, h1'.trans (h2b.trans (h3'.trans (h4'.trans (h5'.trans h6'))))⟩

end Rules

/-! ## One instruction of a thread -/

/-- The invariant of thread `tid` (state `t`) against `mem`: `Ctx.Inv` of its
instruction context. -/
structure Thread.Inv (tid : Nat) (t : Thread I) (mem : Memory) : Prop where
  prom : ∀ p ∈ t.prom, ∃ w, mem.get? p = some w ∧ w.tid = tid
  nodup : t.prom.Nodup
  own : ∀ ts w, mem.get? ts = some w → w.tid = tid → ts ∉ t.prom → ts ≤ t.views.getCoh w.loc

/-- The context `stepOne` starts an instruction of `t` in. -/
theorem Thread.Inv.ctx {tid : Nat} {t : Thread I} {mem : Memory} (h : t.Inv tid mem) (log : List TraceEv) :
    Ctx.Inv tid { views := t.views, prom := t.prom, mem, log } :=
  ⟨h.prom, h.nodup, h.own⟩

/-- **One instruction keeps the thread invariant** and appends only messages
of the thread. -/
theorem stepOne_inv (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (h : t.Inv tid mem) :
    o.thread.Inv tid o.mem ∧ mem.Prefix o.mem ∧ ∀ ts w, mem.last < ts → o.mem.get? ts = some w → w.tid = tid := by
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
      obtain ⟨hi, ⟨hpre, htid⟩⟩ := runTree_inv A tid _ tree _ st c' hr (h.ctx _)
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      have hcoh : th.views.coh = c'.views.coh := by
        have := congrArg Views.coh hv; simpa using this
      refine ⟨⟨?_, ?_, ?_⟩, hpre, htid⟩
      · rw [hp]; exact hi.prom
      · rw [hp]; exact hi.nodup
      · intro ts w hw ht hts
        rw [hp] at hts
        have := hi.own ts w hw ht hts
        simp only [Views.getCoh, hcoh] at this ⊢
        exact this

/-! ## Configurations -/

/- `Config.MachInv` (the machine invariants: `promWf`, `promNodup`, `ownCoh`)
is defined in `PromiseSafe.lean`, because `NPSafe`'s step
assumes it; its theorems stay here. -/

namespace Config.MachInv

variable {c : Config I}

theorem thread (h : c.MachInv) {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) : t.Inv i c.mem :=
  ⟨h.promWf i t ht, h.promNodup i t ht, h.ownCoh i t ht⟩

/-- The instruction context of thread `i` satisfies `Ctx.Inv`; in particular
`Ctx.OwnCoh`, the hypothesis of `ownSeen_of_readSuccs`. -/
theorem ctxInv (h : c.MachInv) {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) (log : List TraceEv) :
    Ctx.Inv i { views := t.views, prom := t.prom, mem := c.mem, log } :=
  (h.thread ht).ctx log

/-- `Config.Wf`'s promise half. -/
theorem prom_le (h : c.MachInv) {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) :
    ∀ p ∈ t.prom, p ≤ c.mem.last := fun p hp => by
  obtain ⟨w, hw, -⟩ := h.promWf i t ht p hp
  exact c.mem.last_le_of_get?_eq_some hw

/-- Replacing thread `tid` by a thread satisfying the invariant against a
memory that extends the old one by messages of `tid` only. -/
theorem withThread (h : c.MachInv) {tid : Nat} (hn : tid < c.threads.size) {t' : Thread I} {mem' : Memory}
    (ht' : t'.Inv tid mem') (hpre : c.mem.Prefix mem') (htid : ∀ ts w, c.mem.last < ts → mem'.get? ts = some w → w.tid = tid) :
    (c.withThread tid t' mem').MachInv := by
  have hget := fun i => Config.withThread_get? c (i := i) t' mem' hn
  have hold : ∀ ts w, mem'.get? ts = some w → w.tid ≠ tid → c.mem.get? ts = some w := by
    intro ts w hw hne
    by_cases hle : ts ≤ c.mem.last
    · rw [← hpre.get? hle]; exact hw
    · exact absurd (htid ts w (by omega_t) hw) hne
  refine ⟨fun i t hi => ?_, fun i t hi => ?_, fun i t hi => ?_⟩
  · rw [hget] at hi
    split at hi
    · next he => subst he; cases hi; exact ht'.prom
    · intro p hp
      obtain ⟨w, hw, htw⟩ := h.promWf i t hi p hp
      exact ⟨w, (hpre.get? (c.mem.last_le_of_get?_eq_some hw)).trans hw, htw⟩
  · rw [hget] at hi
    split at hi
    · next he => subst he; cases hi; exact ht'.nodup
    · exact h.promNodup i t hi
  · rw [hget] at hi
    split at hi
    · next he => subst he; cases hi; exact ht'.own
    · next he =>
      intro ts w hw htw hts
      exact h.ownCoh i t hi ts w (hold ts w hw (htw ▸ Ne.symm he)) htw hts

/-- An instruction step keeps the machine invariants. -/
theorem instr {A : Arch} (h : c.MachInv) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t)
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid c.mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : (c.withThread tid o.thread o.mem).MachInv := by
  obtain ⟨h1, h2, h3⟩ := stepOne_inv A hstep ho (h.thread ht)
  exact h.withThread (lt_size_of_get? ht) h1 h2 h3

/-- A promise step keeps the machine invariants. -/
theorem promise (h : c.MachInv) {tid : Nat} {t : Thread I} (ht : c.threads[tid]? = some t) (w : Msg) :
    (c.withThread tid { t with prom := t.prom ++ [(c.mem.append { w with tid }).2] }
      (c.mem.append { w with tid }).1).MachInv := by
  have hpre := Memory.Prefix.append c.mem { w with tid }
  have hT := h.thread ht
  have hnew : (c.mem.append { w with tid }).2 = c.mem.last + 1 := rfl
  have hnot : c.mem.last + 1 ∉ t.prom := fun hp => by
    have := h.prom_le ht _ hp; omega_t
  refine h.withThread (lt_size_of_get? ht) ⟨?_, ?_, ?_⟩ hpre ?_
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨w', hw', htw⟩ := hT.prom p hp
      exact ⟨w', (hpre.get? (c.mem.last_le_of_get?_eq_some hw')).trans hw', htw⟩
    · rw [List.mem_singleton.mp hp, hnew]
      exact ⟨_, Memory.get?_append_last _ _, rfl⟩
  · simp only
    rw [hnew, List.nodup_append]
    exact ⟨hT.nodup, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb hab => by
      rw [List.mem_singleton.mp hb] at hab; subst hab; exact hnot ha⟩
  · intro ts w' hw' htw hts
    simp only [List.mem_append, not_or] at hts
    rcases Memory.get?_append_eq_some _ _ hw' with ⟨-, hw''⟩ | ⟨he, -⟩
    · exact hT.own ts w' hw'' htw hts.1
    · exact absurd (List.mem_singleton.mpr (he.trans hnew.symm)) hts.2
  · intro ts w' hts hw'
    rcases Memory.get?_append_eq_some _ _ hw' with ⟨hle, -⟩ | ⟨-, rfl⟩
    · omega_t
    · rfl

theorem succ {A : Arch} {c' : Config I} (h : c.MachInv)
    (hs : SuccKind A c c') : c'.MachInv := by
  cases hs with
  | instr ht hstep ho => exact h.instr ht hstep ho
  | promise ht _ => exact h.promise ht _

/-- **The machine invariants hold in every configuration reachable from one
that satisfies them** (e.g. `Config.init`, `Config.init_machInv`), for every
program and both ISAs. -/
theorem reachable {A : Arch} {c' : Config I} (h : c.MachInv)
    (hr : Live.Bridge.ReachableK A c c') : c'.MachInv := by
  induction hr with
  | refl => exact h
  | step hs _ ih => exact ih (h.succ hs)

/-- An instruction step of one thread (`NPStepBy`, no consistency check)
keeps the machine invariants. -/
theorem npStepBy {A : Arch} {tid : Nat} {c' : Config I} (h : c.MachInv) (hs : NPStepBy A tid c c') :
    c'.MachInv := by
  obtain ⟨t, t', mem', ht, ⟨outs, o, hstep, ho, he⟩, rfl⟩ := hs
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h.instr ht hstep ho

end Config.MachInv

/-- A promise-free run of one thread keeps the thread invariant and appends
only messages of the thread. -/
theorem ThreadNP.inv {A : Arch} {tid : Nat} {p q : Thread I × Memory} (hr : ThreadNP A tid p q)
    (h : p.1.Inv tid p.2) :
    q.1.Inv tid q.2 ∧ p.2.Prefix q.2 ∧ ∀ ts w, p.2.last < ts → q.2.get? ts = some w → w.tid = tid := by
  induction hr with
  | refl p => exact ⟨h, Memory.Prefix.refl _, fun _ _ hts hw => absurd (p.2.last_le_of_get?_eq_some hw) (by omega_t)⟩
  | step hs _ ih =>
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    obtain ⟨h1, h2, h3⟩ := stepOne_inv _ hstep ho h
    obtain ⟨h4, h5, h6⟩ := ih h1
    refine ⟨h4, h2.trans h5, fun ts w hts hw => ?_⟩
    by_cases hle : ts ≤ o.mem.last
    · rw [h5.get? hle] at hw; exact h3 ts w hts hw
    · exact h6 ts w (by omega_t) hw

/-- A promise-free run of thread `tid` alone from a configuration keeps the
machine invariants (certification runs, `Config.VirtualOf`'s advances). -/
theorem Config.MachInv.threadNP {A : Arch} {c : Config I} (h : c.MachInv) {tid : Nat} {t t' : Thread I}
    {mem' : Memory} (ht : c.threads[tid]? = some t) (hr : ThreadNP A tid (t, c.mem) (t', mem')) :
    (c.withThread tid t' mem').MachInv := by
  obtain ⟨h1, h2, h3⟩ := hr.inv (h.thread ht)
  exact h.withThread (lt_size_of_get? ht) h1 h2 h3

/-- The initial configuration satisfies the machine invariants. -/
theorem Config.init_machInv (states : List I.State) (initMem : List (Loc × Val)) :
    (Config.init states initMem : Config I).MachInv := by
  have hnone : ∀ ts, (Config.init states initMem : Config I).mem.get? ts = none := fun ts => by
    simp [Config.init, Memory.get?]
  have hp : ∀ (i : Nat) (t : Thread I), (Config.init states initMem : Config I).threads[i]? = some t → t.prom = [] := by
    intro i t h
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨st, -, rfl⟩ := h
    rfl
  refine ⟨fun i t h p hpm => ?_, fun i t h => ?_, fun i t h ts w hw => ?_⟩
  · rw [hp i t h] at hpm; cases hpm
  · rw [hp i t h]; exact List.nodup_nil
  · rw [hnone] at hw; cases hw

end Kraken.Promising

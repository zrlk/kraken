/-
Live configurations have no dead promise (O7 of Theorem 1′'s
induction).

A promise is *dead* (`Thread.hasDeadPromise`) when its timestamp is at or
below its thread's `coh` of its location, `vwNew` or `vCAP`: `fulfil` needs it
above all three (they are part of `writeSuccs`' bound), and they only grow. So
on a path to a final configuration, where every outstanding promise is
fulfilled by its own thread, no promise is dead. `Config.Live.vwNew_lt`
(`ReleasePrefix.lean`) is the `vwNew` third; this file adds `vCAP` and `coh`
(`Ctx.DOrd`, the analogue of `Ctx.WOrd`) and concludes `Config.Live.wfProm`:
every thread of a live configuration satisfies `Config.WfProm`, which is what
`NPSafe`'s step assumes of its pre- and post-configurations.

Machine facts only; no hypothesis on the program.
-/
import Kraken.Promising.ReleasePrefixNT

namespace Kraken.Promising

variable {I : ISA}

/-- `omega` on `Time`/`View`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## One context step orders fulfilment after `vCAP` and `coh` -/

private theorem ite_none_left' {α : Type} {p : Prop} [Decidable p] {y : Option α} {x : α}
    (h : (if p then none else y) = some x) : y = some x := by
  by_cases hp : p
  · rw [ite_eq_left hp] at h; cases h
  · rwa [ite_eq_right hp] at h

/-- One context step: `vCAP` and every `coh` only grow, memory only grows,
and a promise that disappears was fulfilled above the old `vCAP` and the old
`coh` of its location. -/
structure Ctx.DOrd (c c' : Ctx) : Prop where
  vCAP : c.views.vCAP ≤ c'.views.vCAP
  coh : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l
  mem : c.mem.Prefix c'.mem
  prom : ∀ ts ∈ c.prom, ts ∉ c'.prom →
    c.views.vCAP < ts ∧ ∀ w, c.mem.get? ts = some w → c.views.getCoh w.loc < ts

theorem Ctx.DOrd.refl (c : Ctx) : c.DOrd c :=
  ⟨Nat.le_refl _, fun _ => Nat.le_refl _, Memory.Prefix.refl _, fun _ h h' => absurd h h'⟩

theorem Ctx.DOrd.trans {c c' c'' : Ctx} (h₁ : c.DOrd c') (h₂ : c'.DOrd c'') : c.DOrd c'' := by
  refine ⟨Nat.le_trans h₁.vCAP h₂.vCAP, fun l => Nat.le_trans (h₁.coh l) (h₂.coh l), h₁.mem.trans h₂.mem,
    fun ts h h'' => ?_⟩
  by_cases h' : ts ∈ c'.prom
  · obtain ⟨a, b⟩ := h₂.prom ts h' h''
    refine ⟨Nat.lt_of_le_of_lt h₁.vCAP a, fun w hw => ?_⟩
    have hw' : c'.mem.get? ts = some w := by
      rw [h₁.mem.get? (c.mem.last_le_of_get?_eq_some hw)]; exact hw
    exact Nat.lt_of_le_of_lt (h₁.coh _) (b w hw')
  · exact h₁.prom ts h h'

theorem Ctx.DOrd.of_eq {c c' : Ctx} (h1 : c.views.vCAP ≤ c'.views.vCAP)
    (h2 : ∀ l, c.views.getCoh l ≤ c'.views.getCoh l) (hm : c'.mem = c.mem) (hp : c'.prom = c.prom) :
    c.DOrd c' :=
  ⟨h1, h2, by rw [hm]; exact Memory.Prefix.refl _, fun _ h h' => absurd (hp ▸ h) h'⟩

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_dord {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) : c.DOrd x.2.2 := by
  unfold readSuccs at hx
  rw [List.mem_filterMap] at hx
  obtain ⟨t, -, ht⟩ := hx
  split at ht
  · cases ht
  · have h := ite_none_left' ht
    simp only [Option.some.injEq] at h
    subst h
    refine .of_eq ?_ (fun l' => Views.getCoh_le_setCoh _ _ _ _) rfl rfl
    simp only
    omega_t

theorem writeSuccs_dord {xr : View} {c : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {c' : Ctx} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) : c.DOrd c' := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, -, h⟩ | h
  · split at h
    · rename_i w hw
      obtain ⟨hc, h⟩ := Option.ite_none_right_eq_some.mp h
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hl, -⟩, -⟩, hb, -⟩ := hc
      refine ⟨by simp only [afterWrite]; omega_t, fun l' => Views.getCoh_le_setCoh _ _ _ _,
        Memory.Prefix.refl _, fun ts hin hout => ?_⟩
      simp only [afterWrite] at hout
      have hts : ts = t := by
        by_cases hne : ts = t
        · exact hne
        · exact absurd ((List.mem_erase_of_ne hne).mpr hin) hout
      subst hts
      refine ⟨by omega_t, fun w' hw' => ?_⟩
      rw [hw] at hw'
      cases hw'
      rw [hl]
      omega_t
    · cases h
  · split at h
    rename_i mem' t hok
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hcond, rfl⟩ := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hmem' : mem' = (c.mem.append { loc := l, val := v, tid }).1 := by rw [hok]
    have ht : t = c.mem.last + 1 := by
      have := congrArg Prod.snd hok
      simp only at this
      rw [← this]; rfl
    refine ⟨by simp only [afterWrite]; omega_t, fun l' => Views.getCoh_le_setCoh _ _ _ _,
      by simp only [afterWrite]; rw [hmem']; exact Memory.Prefix.append _ _, fun ts hin hout => ?_⟩
    simp only [afterWrite] at hout
    by_cases hne : ts = t
    · subst hne
      refine ⟨by omega_t, fun w' hw' => ?_⟩
      have := c.mem.last_le_of_get?_eq_some hw'
      omega_t
    · exact absurd ((List.mem_erase_of_ne hne).mpr (List.mem_append_left _ hin)) hout

theorem Ctx.DOrd.fenceStep (c : Ctx) (k : FenceKind) : c.DOrd (Kraken.Promising.fenceStep c k) := by
  refine .of_eq ?_ ?_ (fenceStep_mem c k) (fenceStep_fields c k).2.2.2.2.1 <;>
    cases k <;> simp only [Kraken.Promising.fenceStep] <;> intros <;> exact Nat.le_refl _

theorem Ctx.DOrd.fenceOpt (c : Ctx) (b : Bool) (k : FenceKind) :
    c.DOrd (if b then Kraken.Promising.fenceStep c k else c) := by
  cases b
  · exact .refl c
  · exact .fenceStep c k

theorem Ctx.DOrd.rmwPost (c : Ctx) (k : RmwKind) (noRet : Bool) (l : Loc) :
    c.DOrd (Kraken.Promising.rmwPost A k noRet l c) := by
  unfold Kraken.Promising.rmwPost
  split
  · exact .of_eq (Nat.le_refl _) (fun _ => Nat.le_refl _) rfl rfl
  · exact .of_eq (Nat.le_refl _) (fun _ => Nat.le_refl _) rfl rfl

theorem runTree_dord {σ : Type} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree → c.DOrd c' := by
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
    exact (readSuccs_dord A iv hx).trans (ih x.2.1 x.2.2 s c' h)
  | store k xcl l v ret ih =>
    intro c s c' h
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact (writeSuccs_dord A tid _ hc0).trans (ih true c0 s c' h)
    · rw [List.mem_ite_nil_right] at h
      have h0 : c.DOrd { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq (Nat.le_refl _) (fun _ => Nat.le_refl _) rfl rfl
      exact h0.trans (ih false _ s c' h.2)
  | fence k ret ih =>
    intro c s c' h
    simp only [runTree] at h
    exact (Ctx.DOrd.fenceStep c k).trans (ih () _ s c' h)
  | rmw k noRet l op ret ih =>
    intro c s c' h
    simp only [runTree] at h
    have h1 := Ctx.DOrd.fenceOpt c A.rmwFence .sy
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := h1.trans (readSuccs_dord A iv h2)
    simp only at h
    split at h
    · exact (h12.trans (Ctx.DOrd.fenceOpt c2 A.rmwFence .sy)).trans (ih old _ s c' h)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine ((h12.trans (writeSuccs_dord A tid _ hc3)).trans ?_).trans (ih old _ s c' h)
      exact (Ctx.DOrd.rmwPost A c3 k noRet l).trans (Ctx.DOrd.fenceOpt _ A.rmwFence .sy)

end Rules

/-! ## One instruction -/

private theorem foldl_views {α : Type} (f : Thread I → α → Thread I)
    (hf : ∀ t a, (f t a).views = t.views) : ∀ (l : List α) (t : Thread I), (l.foldl f t).views = t.views
  | [], _ => rfl
  | a :: l, t => (foldl_views f hf l (f t a)).trans (hf t a)

/-- Close `(l₁.foldl f₁ (… (lₙ.foldl fₙ t))).views = k` where each `fᵢ` only
sets register views. -/
local macro "views_foldl" : tactic =>
  `(tactic| (repeat (refine (foldl_views _ ?_ _ _).trans ?_; (intro t a; first | rfl | (cases a; rfl)))
             try rfl))

/-- `finishInstr` keeps the context's views but for `vCAP`, which a branch
raises. -/
theorem finishInstr_vCAP {t : Thread I} {d : InstrDeps I.RegId} {iv : InstrViews} {st : I.State} {c : Ctx}
    {th : Thread I} (h : th ∈ finishInstr t d iv st c) : c.views.vCAP ≤ th.views.vCAP := by
  have key : ∀ t' : Thread I, t'.views = c.views →
      c.views.vCAP ≤ (if d.isBranch then { t' with views := { t'.views with vCAP := max t'.views.vCAP iv.condW } }
        else t').views.vCAP := by
    intro t' ht'
    split
    · simp only [ht']; omega_t
    · rw [ht']; exact Nat.le_refl _
  unfold finishInstr at h
  simp only at h
  split at h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · refine key _ ?_
      views_foldl
    · refine key _ ?_
      split <;> views_foldl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    refine key _ ?_
    split <;> views_foldl

/-- **One instruction orders fulfilment after `vCAP` and `coh`**: both only
grow, and a promise the instruction fulfils lies above both (for `coh`, of the
promise's location). -/
theorem stepOne_dord (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    t.views.vCAP ≤ o.thread.views.vCAP ∧ (∀ l, t.views.getCoh l ≤ o.thread.views.getCoh l) ∧
      mem.Prefix o.mem ∧
      ∀ ts ∈ t.prom, ts ∉ o.thread.prom → t.views.vCAP < ts ∧ ∀ w, mem.get? ts = some w → t.views.getCoh w.loc < ts := by
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
      have hw := runTree_dord A tid _ tree _ st c' hr
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      have hcoh : th.views.coh = c'.views.coh := by have := congrArg Views.coh hv; exact this
      have hcap := finishInstr_vCAP hth
      refine ⟨Nat.le_trans hw.vCAP hcap, fun l => ?_, hw.mem, fun ts h1 h2 => ?_⟩
      · have := hw.coh l
        simp only [Views.getCoh, hcoh] at this ⊢
        exact this
      · simp only [hp] at h2
        exact hw.prom ts h1 h2

/-! ## Live configurations -/

/-- In a `LiveK` configuration every outstanding promise lies above its
thread's `vCAP` and `coh` (the `ReachableK` twin of `Config.Live.vCAP_coh_lt`,
fuel-free). -/
theorem Config.LiveK.vCAP_coh_lt {A : Arch} {c : Config I} (hl : c.LiveK A)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.vCAP < ts ∧ ∀ w, c.mem.get? ts = some w → t.views.getCoh w.loc < ts := by
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
      obtain ⟨hcap, hcoh, hpre, hful⟩ := stepOne_dord A hstep ho
      have hmem : ∀ w, c.mem.get? ts = some w → (c.withThread j o.thread o.mem).mem.get? ts = some w :=
        fun w hw => by
          show o.mem.get? ts = some w
          rw [hpre.get? (c.mem.last_le_of_get?_eq_some hw)]; exact hw
      by_cases hij : j = i
      · subst hij
        rw [ht] at hj; cases hj
        by_cases hin : ts ∈ o.thread.prom
        · have h1 : (c.withThread j o.thread o.mem).threads[j]? = some o.thread := by
            simp only [Config.withThread_get? c _ _ hlt, ↓reduceIte]
          obtain ⟨a, b⟩ := ih h1 hin hf
          exact ⟨Nat.lt_of_le_of_lt hcap a, fun w hw => Nat.lt_of_le_of_lt (hcoh _) (b w (hmem w hw))⟩
        · exact hful ts hts hin
      · have h1 : (c.withThread j o.thread o.mem).threads[i]? = some t := by
          simp only [Config.withThread_get? c _ _ (lt_size_of_get? hj), hij, ↓reduceIte, ht]
        obtain ⟨a, b⟩ := ih h1 hts hf
        exact ⟨a, fun w hw => b w (hmem w hw)⟩
    | @promise j tj p hj _ =>
      have hmem : ∀ w, c.mem.get? ts = some w →
          (c.withThread j { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
            (c.mem.append { p.1 with tid := j }).1).mem.get? ts = some w := fun w hw => by
        show (c.mem.append { p.1 with tid := j }).1.get? ts = some w
        rw [(Memory.Prefix.append _ _).get? (c.mem.last_le_of_get?_eq_some hw)]; exact hw
      by_cases hij : j = i
      · subst hij
        rw [ht] at hj; cases hj
        have h1 := (Config.withThread_get? c (i := j) { t with prom := t.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 hlt)
        simp only [↓reduceIte] at h1
        obtain ⟨a, b⟩ := ih h1 (List.mem_append_left _ hts) hf
        exact ⟨a, fun w hw => b w (hmem w hw)⟩
      · have h1 := (Config.withThread_get? c (i := i) { tj with prom := tj.prom ++ [(c.mem.append { p.1 with tid := j }).2] }
          (c.mem.append { p.1 with tid := j }).1 (lt_size_of_get? hj))
        simp only [hij, ↓reduceIte, ht] at h1
        obtain ⟨a, b⟩ := ih h1 hts hf
        exact ⟨a, fun w hw => b w (hmem w hw)⟩

/-- **In a live configuration every outstanding promise lies above its
thread's `vCAP` and its `coh` of the promise's location** (the `vCAP`/`coh`
companion of `Config.Live.vwNew_lt`). -/
theorem Config.Live.vCAP_coh_lt {A : Arch} [I.LawfulState] {fuel : Nat} {c : Config I} (hl : c.Live A fuel)
    {i : Nat} {t : Thread I} (ht : c.threads[i]? = some t) {ts : Time} (hts : ts ∈ t.prom) :
    t.views.vCAP < ts ∧ ∀ w, c.mem.get? ts = some w → t.views.getCoh w.loc < ts :=
  (Config.LiveK.of_live hl).vCAP_coh_lt ht hts

/-- A `LiveK` configuration has no dead promise (the `ReachableK` twin of
`Config.Live.wfProm`, fuel-free). -/
theorem Config.LiveK.wfProm {A : Arch} {c : Config I} (hl : c.LiveK A)
    (i : Nat) : c.WfProm i := by
  intro t ht
  unfold Thread.hasDeadPromise
  rw [List.any_eq_false]
  intro p hp
  have h1 := hl.vwNew_lt ht hp
  obtain ⟨h2, h3⟩ := hl.vCAP_coh_lt ht hp
  split
  · rename_i w hw
    have := h3 w hw
    simp only [decide_eq_true_eq]
    omega_t
  · simp

/-- **(O7) A live configuration has no dead promise**: every thread
satisfies `Config.WfProm` (`Config.Live.vwNew_lt`, `Config.Live.vCAP_coh_lt`). -/
theorem Config.Live.wfProm {A : Arch} [I.LawfulState] {fuel : Nat} {c : Config I} (hl : c.Live A fuel)
    (i : Nat) : c.WfProm i :=
  (Config.LiveK.of_live hl).wfProm i

end Kraken.Promising

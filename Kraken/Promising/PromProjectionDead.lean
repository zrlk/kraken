/-
**Lemma J, dead promises above the
memory.** ISA-neutral and architecture-neutral; executable `Thread` rules only.

`Thread.Bnd` bounds a thread's views and registers by the memory, but not its
promise set: a thread may hold a timestamp above `|M|` (no message yet), or the
same timestamp twice. Such a promise is *dead*: a solo run can never empty the
promise set. A promise above the memory can only be fulfilled after a fresh
write puts a message there, and that fresh write raises `coh` of its location
to the timestamp while leaving it promised; a duplicate promise, once
fulfilled, stays promised with `coh` at the timestamp. Either way `coh` of the
promise's location reaches the timestamp, and `fulfil` needs it above `coh`
(`writeSuccs`' bound), so the promise stays forever.

So the thread after a semantic promise of `w` at `|M| + 1`
(`promThread t M w`) is certifiable only if every promise of `t` is at most
`|M|` (`prom_le_of_certOkN_promThread`), with no hypothesis on `t`.

Contents:
- `Dead`: the invariant; `Dead.mono`, `Dead.of_dord`;
- `readSuccs_dead`, `writeSuccs_dead`, `runTree_dead`, `stepOne_dead`:
  one rule, one tree, one instruction keep it;
- `not_certOkN_of_dead`, `prom_le_of_certOkN_promThread` (Lemma J).
-/
import Kraken.Promising.LiveWfProm
import Kraken.Promising.LiveSem

namespace Kraken.Promising.Proj

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Sem

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- **The promise `ts` is dead** for views `vs`, promise set `prom` and memory
`mem`: it is promised, and either it is above the memory, or the message at it
is at or below `coh` of its location, or it is promised twice (and in the
memory). -/
def Dead (ts : Time) (vs : Views) (prom : List Time) (mem : Memory) : Prop :=
  ts ∈ prom ∧ (mem.last < ts ∨ (∃ x, mem.get? ts = some x ∧ ts ≤ vs.getCoh x.loc) ∨
    (2 ≤ prom.count ts ∧ ts ≤ mem.last))

theorem Dead.mono {ts : Time} {vs vs' : Views} {prom : List Time} {mem : Memory} (h : Dead ts vs prom mem)
    (hc : ∀ l, vs.getCoh l ≤ vs'.getCoh l) : Dead ts vs' prom mem := by
  obtain ⟨hm, h | ⟨x, hx, hl⟩ | h⟩ := h
  · exact ⟨hm, .inl h⟩
  · exact ⟨hm, .inr (.inl ⟨x, hx, Nat.le_trans hl (hc _)⟩)⟩
  · exact ⟨hm, .inr (.inr h)⟩

theorem Dead.of_dord {ts : Time} {c c' : Ctx} (h : Dead ts c.views c.prom c.mem) (hd : c.DOrd c')
    (hp : c'.prom = c.prom) (hm : c'.mem = c.mem) : Dead ts c'.views c'.prom c'.mem := by
  rw [hp, hm]; exact h.mono hd.coh

private theorem rmwPost_prom (A : Arch) (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) :
    (rmwPost A k noRet l c).prom = c.prom := by
  unfold rmwPost; split <;> rfl

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readSuccs_dead {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {ts : Time}
    {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet) (h : Dead ts c.views c.prom c.mem) :
    Dead ts x.2.2.views x.2.2.prom x.2.2.mem := by
  refine h.of_dord (readSuccs_dord A iv hx) ?_ (readSuccs_mp A iv hx).1
  obtain ⟨t, v, rfl, -⟩ := (mem_readSuccs A).mp hx
  rfl

theorem writeSuccs_dead {xr : View} {c c2 : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} {ts : Time} (h : c2 ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hd : Dead ts c.views c.prom c.mem) : Dead ts c2.views c2.prom c2.mem := by
  have hdo := writeSuccs_dord A tid iv h
  obtain ⟨hm, hd⟩ := hd
  rcases (mem_writeSuccs A tid).mp h with ⟨t, -, x, hx, hxl, -, -, hok, rfl⟩ | ⟨hok, rfl⟩
  · -- fulfil `t`
    by_cases hts : ts = t
    · subst hts
      rcases hd with hlt | ⟨y, hy, hle⟩ | ⟨hc, -⟩
      · have := c.mem.last_le_of_get?_eq_some hx; omega_t
      · rw [hx] at hy; cases hy
        have := hok.1; rw [hxl] at hle; omega_t
      · refine ⟨List.count_pos_iff.mp ?_, .inr (.inl ⟨x, hx, ?_⟩)⟩
        · show 0 < (c.prom.erase ts).count ts
          rw [List.count_erase_self]; omega
        · rw [afterWrite_getCoh, ite_eq_left hxl]; omega_t
    · refine Dead.mono (vs := c.views) ⟨(List.mem_erase_of_ne hts).mpr hm, ?_⟩ hdo.coh
      show c.mem.last < ts ∨ (∃ x, c.mem.get? ts = some x ∧ ts ≤ c.views.getCoh x.loc) ∨
        (2 ≤ (c.prom.erase t).count ts ∧ ts ≤ c.mem.last)
      rw [List.count_erase_of_ne hts]
      exact hd
  · -- promise now, at `|M| + 1`
    have hcoh : ∀ l', c.views.getCoh l' ≤ _ := hdo.coh
    by_cases hts : ts = c.mem.last + 1
    · subst hts
      refine ⟨List.count_pos_iff.mp ?_, .inr (.inl ⟨_, Memory.get?_append_last _ _, ?_⟩)⟩
      · show 0 < ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).count (c.mem.last + 1)
        rw [List.count_erase_self, List.count_append]
        have := List.count_pos_iff.mpr hm
        simp only [List.count_singleton_self]
        omega
      · rw [afterWrite_getCoh, ite_eq_left rfl]; omega_t
    · refine Dead.mono (vs := c.views) ⟨(List.mem_erase_of_ne hts).mpr (List.mem_append_left _ hm), ?_⟩ hcoh
      show (c.mem.append _).1.last < ts ∨ (∃ x, (c.mem.append _).1.get? ts = some x ∧ ts ≤ c.views.getCoh x.loc) ∨
        (2 ≤ ((c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1)).count ts ∧ ts ≤ (c.mem.append _).1.last)
      rw [List.count_erase_of_ne hts, List.count_append, Memory.last_append]
      rcases hd with hlt | ⟨y, hy, hle⟩ | ⟨hc, hle⟩
      · exact .inl (by omega_t)
      · refine .inr (.inl ⟨y, ?_, hle⟩)
        rw [Memory.get?_append_of_le _ _ _ (c.mem.last_le_of_get?_eq_some hy)]; exact hy
      · exact .inr (.inr ⟨by omega, by omega_t⟩)

theorem runTree_dead {σ : Type} {ts : Time} (tree : EvTree σ) :
    ∀ (c : Ctx) (s : σ) (c' : Ctx), .ok (s, c') ∈ runTree A tid iv c tree →
      Dead ts c.views c.prom c.mem → Dead ts c'.views c'.prom c'.mem := by
  induction tree with
  | done s =>
    intro c s' c' h
    simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact id
  | fault m => intro c s c' h; simp [runTree] at h
  | choose n k ih =>
    intro c s c' h
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨i, -, h⟩ := h
    exact ih i c s c' h
  | load k xcl l ret ih =>
    intro c s c' h hd
    simp only [runTree, List.mem_flatMap] at h
    obtain ⟨x, hx, h⟩ := h
    exact ih x.2.1 x.2.2 s c' h (readSuccs_dead A iv hx hd)
  | store k xcl l v ret ih =>
    intro c s c' h hd
    simp only [runTree, List.mem_append] at h
    rcases h with h | h
    · rw [List.mem_ite_nil_left, List.mem_flatMap] at h
      obtain ⟨-, c0, hc0, h⟩ := h
      exact ih true c0 s c' h (writeSuccs_dead A tid _ hc0 hd)
    · rw [List.mem_ite_nil_right] at h
      have h0 : c.DOrd { c with views := { c.views with xclb := none }, succView := 0, log := c.log ++ [.xclFail l] } :=
        .of_eq (Nat.le_refl _) (fun _ => Nat.le_refl _) rfl rfl
      exact ih false _ s c' h.2 (hd.of_dord h0 rfl rfl)
  | fence k ret ih =>
    intro c s c' h hd
    simp only [runTree] at h
    exact ih () _ s c' h (hd.of_dord (Ctx.DOrd.fenceStep c k) (fenceStep_fields c k).2.2.2.2.1 (fenceStep_mem c k))
  | rmw k noRet l op ret ih =>
    intro c s c' h hd
    simp only [runTree] at h
    have hf : ∀ (c : Ctx) (b : Bool), Dead ts c.views c.prom c.mem →
        Dead ts (if b then fenceStep c .sy else c).views (if b then fenceStep c .sy else c).prom
          (if b then fenceStep c .sy else c).mem := by
      intro c b hd
      cases b
      · exact hd
      · exact hd.of_dord (Ctx.DOrd.fenceStep c .sy) (fenceStep_fields c .sy).2.2.2.2.1 (fenceStep_mem c .sy)
    have h1 := hf c A.rmwFence hd
    generalize (if A.rmwFence then fenceStep c .sy else c) = c1 at h h1
    rw [List.mem_flatMap] at h
    obtain ⟨⟨tr, old, c2⟩, h2, h⟩ := h
    have h12 := readSuccs_dead A iv h2 h1
    simp only at h h12
    split at h
    · exact ih old _ s c' h (hf c2 A.rmwFence h12)
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      change .ok (s, c') ∈ runTree A tid iv
        (if A.rmwFence then fenceStep (rmwPost A k noRet l c3) .sy else rmwPost A k noRet l c3) (ret old) at h
      refine ih old _ s c' h (hf _ A.rmwFence ?_)
      exact (writeSuccs_dead A tid _ hc3 h12).of_dord (Ctx.DOrd.rmwPost A c3 k noRet l)
        (rmwPost_prom A k noRet l c3) (rmwPost_mem A k noRet l c3)

end Rules

/-- **One instruction keeps a dead promise dead.** -/
theorem stepOne_dead (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {ts : Time}
    {outs : List (Except String (Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) (hd : Dead ts t.views t.prom mem) :
    Dead ts o.thread.views o.thread.prom o.mem := by
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
      have hw := runTree_dead A tid _ tree _ st c' hr hd
      obtain ⟨hp, hv⟩ := finishInstr_relKey hth
      have hcoh : th.views.coh = c'.views.coh := by have := congrArg Views.coh hv; exact this
      show Dead ts th.views th.prom c'.mem
      rw [hp]
      refine hw.mono fun l => ?_
      simp only [Views.getCoh, hcoh]
      exact Nat.le_refl _

/-- **A thread with a dead promise is not certifiable**, within any fuel. -/
theorem not_certOkN_of_dead {A : Arch} {tid n : Nat} {t : Thread I} {mem : Memory} {ts : Time}
    (hd : Dead ts t.views t.prom mem) : ¬ CertOkN A tid t mem n := by
  rintro ⟨t', mem', h, hp⟩
  suffices ∀ n p q, ThreadNPn A tid n p q → Dead ts p.1.views p.1.prom p.2 →
      Dead ts q.1.views q.1.prom q.2 by
    have := (this n _ _ h hd).1
    rw [hp] at this; cases this
  intro n p q h
  induction h with
  | refl => exact id
  | step hs _ ih =>
    intro hd
    obtain ⟨outs, o, hstep, ho, rfl⟩ := hs
    exact ih (stepOne_dead A hstep ho hd)

/-- **Lemma J: after a certifiable semantic promise, the old promises are in
the old memory.** If the thread `t`, having promised `w` at `|M| + 1`, is
certifiable against `M ++ [w]` (within any fuel), then every promise of `t` is
at most `|M|`. No hypothesis on `t` (not even `t.Bnd`): a promise of `t`
above `|M| + 1` is above the memory, and one at `|M| + 1` is promised twice,
so either is `Dead`. -/
theorem prom_le_of_certOkN_promThread {A : Arch} {tid n : Nat} {t : Thread I} {mem : Memory} {w : Msg}
    (hc : CertOkN A tid (promThread t mem w) (mem.append w).1 n) : ∀ s ∈ t.prom, s ≤ mem.last := by
  intro s hs
  refine Nat.le_of_not_lt fun hlt => not_certOkN_of_dead (ts := s) ?_ hc
  refine ⟨List.mem_append_left _ hs, ?_⟩
  rw [Memory.last_append]
  by_cases he : s = mem.last + 1
  · subst he
    refine .inr (.inr ⟨?_, Nat.le_refl _⟩)
    show 2 ≤ (t.prom ++ [(mem.append w).2]).count (mem.last + 1)
    rw [Memory.append_time, List.count_append, List.count_singleton_self]
    have := List.count_pos_iff.mpr hs
    omega
  · exact .inl (by omega_t)

end Kraken.Promising.Proj

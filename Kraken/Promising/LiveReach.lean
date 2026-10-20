/-
**Stage 3 liveness: concrete traces from
`ReachCore`'s replay checker.** ISA-neutral.

`ReachCore` proves `Reachable` from one Boolean evaluation of `reachRun`.
A liveness counterexample also needs *which thread* steps (`InstrBy`) and a
*cycle* `c → … → c`, i.e. an equality of configurations. A configuration
holds functions (e.g. AArch64's `showPc`), so equality is not decidable;
`liveCfgEq_sound` decides it from `Thread`'s `==` (the dynamic part) and
`Memory`'s `==`, given that both configurations have the same static parts
(`LiveStatic`), which every replayed run preserves (`reachRun_liveStatic`).

- `reachStep_instrBy`, `reachRun_append`, `liveRunAt` (the configuration
  after the first `k` steps of a trace) and `liveRunAt_step`.
-/
import Kraken.Promising.ReachCore
import Kraken.Promising.LiveTrace

namespace Kraken.Promising.Live

open Kraken.Promising

variable {I : ISA}

/-! ## One replayed step is an instruction step of its thread -/

theorem reachStep_instrBy (A : Arch) {c c' : Config I} {tid : Nat} {sel : List Nat}
    (h : reachStep I.exec I.deps A c tid sel = some c') :
    InstrBy A tid c c' ∧ ∀ t', c'.threads[tid]? = some t' → t'.prom = [] := by
  obtain ⟨t, outs, o, ht, hs, he, hp, rfl⟩ := reachStep_cases A h
  have hlt : tid < c.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
  refine ⟨⟨t, outs, _, ht, hs, he, rfl⟩, fun t' ht' => ?_⟩
  simp only [Config.withThread, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self,
    hlt, ite_true, Option.some.injEq] at ht'
  subst ht'
  exact List.isEmpty_iff.mp hp

/-! ## Static parts -/

/-- `c'` has the threads of `c`, each with the same static part. -/
def LiveStatic [L : I.LawfulState] (c c' : Config I) : Prop :=
  c'.threads.size = c.threads.size ∧
    ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → ∃ t' : Thread I, c'.threads[i]? = some t' ∧ L.static t'.st = L.static t.st

theorem LiveStatic.refl [L : I.LawfulState] (c : Config I) : LiveStatic c c :=
  ⟨rfl, fun _ t h => ⟨t, h, rfl⟩⟩

theorem LiveStatic.trans [L : I.LawfulState] {c c' c'' : Config I} (h₁ : LiveStatic c c')
    (h₂ : LiveStatic c' c'') : LiveStatic c c'' := by
  refine ⟨h₂.1.trans h₁.1, fun i t ht => ?_⟩
  obtain ⟨t', ht', e'⟩ := h₁.2 i t ht
  obtain ⟨t'', ht'', e''⟩ := h₂.2 i t' ht'
  exact ⟨t'', ht'', e''.trans e'⟩

theorem reachStep_liveStatic (A : Arch) [L : I.LawfulState] {c c' : Config I} {tid : Nat} {sel : List Nat}
    (h : reachStep I.exec I.deps A c tid sel = some c') : LiveStatic c c' := by
  obtain ⟨⟨t, outs, o, ht, hs, ho, rfl⟩, -⟩ := reachStep_instrBy A h
  refine ⟨by simp [Config.withThread], fun i t₀ h₀ => ?_⟩
  simp only [Config.withThread, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hi : tid = i
  · subst hi
    rw [ht] at h₀; cases h₀
    have hlt : tid < c.threads.size := (Array.getElem?_eq_some_iff.mp ht).1
    exact ⟨o.thread, by simp [hlt], stepOne_static A hs ho⟩
  · exact ⟨t₀, by simp [hi, h₀], rfl⟩

theorem reachRun_liveStatic (A : Arch) [L : I.LawfulState] :
    ∀ {c c' : Config I} {tr : List (Nat × List Nat)}, reachRun I.exec I.deps A c tr = some c' → LiveStatic c c'
  | c, c', [], h => by cases h; exact .refl c
  | c, c', (tid, sel) :: tr, h => by
    simp only [reachRun] at h
    obtain ⟨m, hm, hr⟩ := Option.bind_eq_some_iff.mp h
    exact (reachStep_liveStatic A hm).trans (reachRun_liveStatic A hr)

/-! ## Deciding equality of configurations with the same static parts -/

/-- Two optional threads are `==` (both absent, or both present and `==`). -/
def liveOptBEq : Option (Thread I) → Option (Thread I) → Bool
  | some t, some t' => t == t'
  | none, none => true
  | _, _ => false

/-- Boolean equality of configurations: same thread count, `==` threads,
`==` memory. -/
def liveCfgEq (c c' : Config I) : Bool :=
  c.threads.size == c'.threads.size &&
    (List.range c.threads.size).all (fun i => liveOptBEq c.threads[i]? c'.threads[i]?) && c.mem == c'.mem

/-- **`liveCfgEq` is equality on configurations with the same static
parts.** -/
theorem liveCfgEq_sound [L : I.LawfulState] {c c' : Config I} (hs : LiveStatic c c')
    (h : liveCfgEq c c' = true) : c' = c := by
  simp only [liveCfgEq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hsz, hall⟩, hm⟩ := h
  obtain ⟨th, mem⟩ := c
  obtain ⟨th', mem'⟩ := c'
  simp only at hsz hall hm hs ⊢
  subst hm
  refine congrArg (Config.mk · mem) (Array.ext_getElem? fun i => ?_)
  by_cases hi : i < th.size
  · obtain ⟨t, ht⟩ : ∃ t, th[i]? = some t := ⟨_, Array.getElem?_eq_getElem hi⟩
    obtain ⟨t', ht', hst⟩ := hs.2 i t ht
    have hb := hall i hi
    rw [ht, ht'] at hb
    obtain ⟨h1, h2, h3, h4, h5⟩ := (Thread.beq_iff t t').mp hb
    have hst' : t'.st = t.st := L.eq_of_beq _ _ (L.beq_symm _ _ h1) hst
    rw [ht, ht']
    obtain ⟨st, rv, wv, vs, pr⟩ := t
    obtain ⟨st', rv', wv', vs', pr'⟩ := t'
    simp_all
  · have h1 : th[i]? = none := Array.getElem?_eq_none (by omega)
    have h2 : th'[i]? = none := Array.getElem?_eq_none (by omega)
    rw [h1, h2]

/-! ## Prefixes of a replayed trace -/

theorem reachRun_append (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch) :
    ∀ (c : Config I) (l₁ l₂ : List (Nat × List Nat)),
      reachRun ex dp A c (l₁ ++ l₂) = (reachRun ex dp A c l₁).bind fun c' => reachRun ex dp A c' l₂
  | c, [], l₂ => by simp [reachRun]
  | c, (tid, sel) :: l₁, l₂ => by
    simp only [List.cons_append, reachRun, Option.bind_assoc]
    congr 1
    funext c'
    exact reachRun_append ex dp A c' l₁ l₂

/-- The configuration after the first `k` steps of `tr` from `c` (`c` if
the replay fails). -/
def liveRunAt (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (c : Config I) (tr : List (Nat × List Nat)) (k : Nat) : Config I :=
  (reachRun ex dp A c (tr.take k)).getD c

/-- **Each step of a replayed trace**: if the whole trace replays, step `k`
replays from the configuration after `k` steps to the one after `k + 1`. -/
theorem liveRunAt_step (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    {c c' : Config I} {tr : List (Nat × List Nat)} (h : reachRun ex dp A c tr = some c') {k : Nat}
    (hk : k < tr.length) :
    reachStep ex dp A (liveRunAt ex dp A c tr k) tr[k].1 tr[k].2 = some (liveRunAt ex dp A c tr (k + 1)) := by
  have htr : tr = tr.take k ++ (tr[k] :: tr.drop (k + 1)) := by simp
  rw [htr, reachRun_append] at h
  obtain ⟨a, ha, hrest⟩ := Option.bind_eq_some_iff.mp h
  simp only [reachRun] at hrest
  obtain ⟨b, hb, -⟩ := Option.bind_eq_some_iff.mp hrest
  have hk1 : tr.take (k + 1) = tr.take k ++ [tr[k]] := by rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl
  have hb' : reachRun ex dp A c (tr.take (k + 1)) = some b := by
    rw [hk1, reachRun_append, ha]
    simp [reachRun, hb]
  simp only [liveRunAt, ha, hb', Option.getD_some]
  exact hb

theorem liveRunAt_length (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    {c c' : Config I} {tr : List (Nat × List Nat)} (h : reachRun ex dp A c tr = some c') :
    liveRunAt ex dp A c tr tr.length = c' := by
  simp [liveRunAt, h]

theorem liveRunAt_zero (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) (A : Arch)
    (c : Config I) (tr : List (Nat × List Nat)) : liveRunAt ex dp A c tr 0 = c := by
  simp [liveRunAt, reachRun]

end Kraken.Promising.Live

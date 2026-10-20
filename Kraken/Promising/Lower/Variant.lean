/-
**Part A, generic layer: two ISAs that differ only in
`exec` and `deps`.** ISA-neutral.

`I.withExec ex dp` is `I` with its `exec` and `deps` replaced (`isaLSE2` is
`AArch64.isa.withExec execLSE2 depsLSE2` by definition). The two ISAs have the
same `State`, `RegId`, register indexing, state equality, hash and trace
printer, but `Thread I` and `Thread (I.withExec ex dp)` (likewise `Outcome`,
`Config`) are different types, since the ISA is a parameter of the structure.
`castT`/`uncastT` and `castC`/`uncastC` are the field-by-field copies; they are
mutually inverse (`uncastC_castC`, `castC_uncastC`).

`Agree I ex dp G`: on the states `G`, `ex` is `I.exec` and `dp` is `I.deps`,
and every leaf of an instruction from `G` is in `G`. Under it, on threads
whose states are in `G` (`GoodC` for configurations), both machines take the
same steps, by cast:

- one instruction: `stepOne_castT`;
- runs of a thread alone and certification: `threadNP_castT_iff`,
  `threadNPn_castT_iff`, `certOkN_castT_iff`, `certOk_castT_iff`,
  `certWrite_castT_iff`;
- the semantic machine (`LiveSem.lean`, `LiveSemInf.lean`, `LiveBridge.lean`):
  `instrSem_castC_iff`, `promSem_castC_iff`, `stepSem_castC_iff`,
  `instrSemInf_castC_iff`, `promSemInf_castC_iff`, `stepSemInf_castC_iff`,
  and reachability in both directions, `reachableSem_castC`/`.uncastC`,
  `reachableSemInf_castC`/`.uncastC`;
- the K world (`ReachableK.lean`): `succKind_castC_iff`,
  `reachableK_castC`/`.uncastC` (the executable machine `Reachable`/`succs`
  enters through `ReachableK.of_reachable`; see `LSE2Transfer.lean`);
- final configurations: `final_castC`.

The executable machine itself (`succs`, with `certify` and its hash-map
caches keyed on `Thread I`) is not transferred: relating two caches over
different key types is out of proportion to its use. A theorem about
`Reachable` transfers through its `#chaink_clone` K twin
(`Lower/PilotLSE2.lean`).
-/
import Kraken.Promising.LiveSemInf

namespace Kraken.Promising

/-- `I` with its `exec` and `deps` replaced; every other field is `I`'s. -/
abbrev ISA.withExec (I : ISA) (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId) :
    ISA :=
  { I with exec := ex, deps := dp }

namespace Lower.Variant

open Live Live.Sem Live.Bridge Live.Inf

variable {I : ISA} {ex : I.State → Option (EvTree I.State)} {dp : I.State → InstrDeps I.RegId}

/-- **`ex`/`dp` agree with `I` on the step-closed set `G`.** -/
structure Agree (I : ISA) (ex : I.State → Option (EvTree I.State)) (dp : I.State → InstrDeps I.RegId)
    (G : I.State → Prop) : Prop where
  exec : ∀ s, G s → ex s = I.exec s
  deps : ∀ s, G s → dp s = I.deps s
  leaves : ∀ s, G s → ∀ tree, I.exec s = some tree → tree.All G

/-! ## The casts -/

/-- A thread of `I` as a thread of `I.withExec ex dp`. -/
def castT (t : Thread I) : Thread (I.withExec ex dp) := ⟨t.st, t.rview, t.wview, t.views, t.prom⟩

/-- A thread of `I.withExec ex dp` as a thread of `I`. -/
def uncastT (t : Thread (I.withExec ex dp)) : Thread I := ⟨t.st, t.rview, t.wview, t.views, t.prom⟩

@[simp] theorem uncastT_castT (t : Thread I) : uncastT (castT (ex := ex) (dp := dp) t) = t := rfl
@[simp] theorem castT_uncastT (t : Thread (I.withExec ex dp)) : castT (uncastT t) = t := rfl
@[simp] theorem castT_st (t : Thread I) : (castT (ex := ex) (dp := dp) t).st = t.st := rfl
@[simp] theorem castT_prom (t : Thread I) : (castT (ex := ex) (dp := dp) t).prom = t.prom := rfl
@[simp] theorem uncastT_st (t : Thread (I.withExec ex dp)) : (uncastT t).st = t.st := rfl
@[simp] theorem uncastT_prom (t : Thread (I.withExec ex dp)) : (uncastT t).prom = t.prom := rfl

theorem castT_injective {t t' : Thread I} (h : castT (ex := ex) (dp := dp) t = castT t') : t = t' := by
  rw [← uncastT_castT (ex := ex) (dp := dp) t, h, uncastT_castT]

/-- An outcome of `I` as an outcome of `I.withExec ex dp`. -/
def castO (o : Outcome I) : Outcome (I.withExec ex dp) :=
  { thread := castT o.thread, mem := o.mem, promisedNow := o.promisedNow, log := o.log }

/-- A configuration of `I` as a configuration of `I.withExec ex dp`. -/
def castC (c : Config I) : Config (I.withExec ex dp) := ⟨c.threads.map castT, c.mem⟩

/-- A configuration of `I.withExec ex dp` as a configuration of `I`. -/
def uncastC (c : Config (I.withExec ex dp)) : Config I := ⟨c.threads.map uncastT, c.mem⟩

@[simp] theorem uncastC_castC (c : Config I) : uncastC (castC (ex := ex) (dp := dp) c) = c := by
  obtain ⟨ts, m⟩ := c
  simp only [castC, uncastC, Array.map_map]
  congr 1
  exact Array.map_id' ts

@[simp] theorem castC_uncastC (c : Config (I.withExec ex dp)) : castC (uncastC c) = c := by
  obtain ⟨ts, m⟩ := c
  simp only [castC, uncastC, Array.map_map]
  congr 1
  exact Array.map_id' ts

theorem castC_injective {c c' : Config I} (h : castC (ex := ex) (dp := dp) c = castC c') : c = c' := by
  rw [← uncastC_castC (ex := ex) (dp := dp) c, h, uncastC_castC]

@[simp] theorem castC_mem (c : Config I) : (castC (ex := ex) (dp := dp) c).mem = c.mem := rfl
@[simp] theorem uncastC_mem (c : Config (I.withExec ex dp)) : (uncastC c).mem = c.mem := rfl

@[simp] theorem castC_get? (c : Config I) (i : Nat) :
    (castC (ex := ex) (dp := dp) c).threads[i]? = c.threads[i]?.map castT := by
  simp [castC]

@[simp] theorem uncastC_get? (c : Config (I.withExec ex dp)) (i : Nat) :
    (uncastC c).threads[i]? = c.threads[i]?.map uncastT := by
  simp [uncastC]

@[simp] theorem castC_size (c : Config I) : (castC (ex := ex) (dp := dp) c).threads.size = c.threads.size := by
  simp [castC]

theorem castC_withThread (c : Config I) (tid : Nat) (t : Thread I) (mem : Memory) :
    castC (ex := ex) (dp := dp) (c.withThread tid t mem) = (castC c).withThread tid (castT t) mem := by
  simp only [castC, Config.withThread, Array.set!, Array.map_setIfInBounds]

/-- The initial configuration is its own cast. -/
theorem castC_init (states : List I.State) (initMem : List (Loc × Val)) :
    castC (ex := ex) (dp := dp) (Config.init states initMem) =
      (Config.init states initMem : Config (I.withExec ex dp)) := by
  simp only [castC, Config.init, List.map_toArray, List.map_map]
  rfl

/-! ## One instruction -/

theorem foldl_castT {α : Type} (F : Thread (I.withExec ex dp) → α → Thread (I.withExec ex dp)) :
    ∀ (l : List α) (t : Thread I), l.foldl F (castT t) = castT (l.foldl (fun t a => uncastT (F (castT t) a)) t)
  | [], _ => rfl
  | a :: l, t => by
    simp only [List.foldl_cons]
    rw [← foldl_castT F l]
    rfl

/-- **`finishInstr` of a cast thread is `finishInstr`, cast.** -/
theorem finishInstr_castT (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx) :
    finishInstr (castT (ex := ex) (dp := dp) t) d iv st c = (finishInstr t d iv st c).map castT := by
  have h0 : ({ castT (ex := ex) (dp := dp) t with st, views := c.views, prom := c.prom } :
      Thread (I.withExec ex dp)) = castT { t with st, views := c.views, prom := c.prom } := rfl
  simp only [finishInstr]
  rw [h0]
  repeat rw [foldl_castT]
  split <;> (try split) <;> (try split) <;> (try split) <;> rfl

variable {G : I.State → Prop}

/-- **One instruction of a cast thread is the instruction, cast.** -/
theorem stepOne_castT (hA : Agree I ex dp G) (A : Arch) {t : Thread I} (hG : G t.st) (tid : Nat)
    (mem : Memory) :
    stepOne A (castT (ex := ex) (dp := dp) t) tid mem = (stepOne A t tid mem).map (List.map (Except.map castO)) := by
  have he : (I.withExec ex dp).exec (castT (ex := ex) (dp := dp) t).st = I.exec t.st := hA.exec _ hG
  have hd : (I.withExec ex dp).deps (castT (ex := ex) (dp := dp) t).st = I.deps t.st := hA.deps _ hG
  unfold stepOne
  rw [he, hd]
  cases I.exec t.st with
  | none => rfl
  | some tree =>
    show some _ = some _
    rw [List.map_flatMap]
    refine congrArg (fun g => some (List.flatMap g _)) (funext fun x => ?_)
    rcases x with m | ⟨st, c'⟩
    · rfl
    · show List.map _ (finishInstr (castT t) _ _ st c') = _
      rw [finishInstr_castT, List.map_map, List.map_map]
      rfl

/-- The outcomes of a cast thread are the cast outcomes. -/
theorem ok_mem_castT (hA : Agree I ex dp G) {A : Arch} {t : Thread I} (hG : G t.st) {tid : Nat} {mem : Memory}
    {outs' : List (Except String (Outcome (I.withExec ex dp)))}
    (hs : stepOne A (castT (ex := ex) (dp := dp) t) tid mem = some outs') {o' : Outcome (I.withExec ex dp)}
    (ho : .ok o' ∈ outs') :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o' = castO o := by
  rw [stepOne_castT hA A hG] at hs
  cases h : stepOne A t tid mem with
  | none => rw [h] at hs; cases hs
  | some outs =>
    rw [h] at hs
    cases hs
    obtain ⟨r, hr, hro⟩ := List.mem_map.mp ho
    rcases r with m | o
    · cases hro
    · exact ⟨outs, o, rfl, hr, (Except.ok.inj hro).symm⟩

theorem ok_mem_castT_of (hA : Agree I ex dp G) {A : Arch} {t : Thread I} (hG : G t.st) {tid : Nat}
    {mem : Memory} {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) :
    stepOne A (castT (ex := ex) (dp := dp) t) tid mem = some (outs.map (Except.map castO)) ∧
      .ok (castO (ex := ex) (dp := dp) o) ∈ outs.map (Except.map castO) := by
  rw [stepOne_castT hA A hG, hs]
  exact ⟨rfl, List.mem_map.mpr ⟨_, ho, rfl⟩⟩

/-- An instruction from `G` lands in `G`. -/
theorem good_of_stepOne (hA : Agree I ex dp G) {A : Arch} {t : Thread I} (hG : G t.st) {tid : Nat}
    {mem : Memory} {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs)
    {o : Outcome I} (ho : .ok o ∈ outs) : G o.thread.st :=
  stepOne_leaf A hs ho (hA.leaves _ hG)

/-! ## Runs of one thread and certification -/

theorem threadStep_castT_iff (hA : Agree I ex dp G) {A : Arch} {tid : Nat} {t t' : Thread I} {m m' : Memory}
    (hG : G t.st) :
    ThreadStep A tid (castT (ex := ex) (dp := dp) t, m) (castT t', m') ↔ ThreadStep A tid (t, m) (t', m') := by
  constructor
  · rintro ⟨outs', o', hs, ho, he⟩
    obtain ⟨outs, o, hs', ho', rfl⟩ := ok_mem_castT hA hG hs ho
    simp only [Prod.mk.injEq] at he
    exact ⟨outs, o, hs', ho', by rw [castT_injective he.1, he.2]; rfl⟩
  · rintro ⟨outs, o, hs, ho, he⟩
    obtain ⟨hs', ho'⟩ := ok_mem_castT_of (ex := ex) (dp := dp) hA hG hs ho
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨_, _, hs', ho', rfl⟩

theorem threadStep_uncastT (hA : Agree I ex dp G) {A : Arch} {tid : Nat}
    {p q : Thread (I.withExec ex dp) × Memory} (hG : G p.1.st) (h : ThreadStep A tid p q) :
    ThreadStep A tid (uncastT p.1, p.2) (uncastT q.1, q.2) :=
  (threadStep_castT_iff hA (t := uncastT p.1) hG).mp h

theorem good_of_threadStep (hA : Agree I ex dp G) {A : Arch} {tid : Nat} {p q : Thread I × Memory}
    (hG : G p.1.st) (h : ThreadStep A tid p q) : G q.1.st := by
  obtain ⟨outs, o, hs, ho, rfl⟩ := h
  exact good_of_stepOne hA hG hs ho

theorem threadNP_castT_iff (hA : Agree I ex dp G) {A : Arch} {tid : Nat} {t t' : Thread I} {m m' : Memory}
    (hG : G t.st) :
    ThreadNP A tid (castT (ex := ex) (dp := dp) t, m) (castT t', m') ↔ ThreadNP A tid (t, m) (t', m') := by
  constructor
  · intro h
    suffices H : ∀ p q, ThreadNP A tid p q → G (uncastT p.1).st →
        ThreadNP A tid (uncastT p.1, p.2) (uncastT q.1, q.2) from H _ _ h hG
    intro p q h
    induction h with
    | refl => exact fun _ => .refl _
    | step hs _ ih =>
      intro hg
      have h1 := threadStep_uncastT hA hg hs
      exact .step h1 (ih (good_of_threadStep hA hg h1))
  · intro h
    suffices H : ∀ p q, ThreadNP A tid p q → G p.1.st →
        ThreadNP A tid (castT (ex := ex) (dp := dp) p.1, p.2) (castT q.1, q.2) from H _ _ h hG
    intro p q h
    induction h with
    | refl => exact fun _ => .refl _
    | step hs _ ih =>
      intro hg
      exact .step ((threadStep_castT_iff hA hg).mpr hs) (ih (good_of_threadStep hA hg hs))

theorem threadNPn_castT_iff (hA : Agree I ex dp G) {A : Arch} {tid n : Nat} {t t' : Thread I} {m m' : Memory}
    (hG : G t.st) :
    ThreadNPn A tid n (castT (ex := ex) (dp := dp) t, m) (castT t', m') ↔ ThreadNPn A tid n (t, m) (t', m') := by
  constructor
  · intro h
    suffices H : ∀ n p q, ThreadNPn A tid n p q → G (uncastT p.1).st →
        ThreadNPn A tid n (uncastT p.1, p.2) (uncastT q.1, q.2) from H _ _ _ h hG
    intro n p q h
    induction h with
    | refl => exact fun _ => .refl _ _
    | step hs _ ih =>
      intro hg
      have h1 := threadStep_uncastT hA hg hs
      exact .step h1 (ih (good_of_threadStep hA hg h1))
  · intro h
    suffices H : ∀ n p q, ThreadNPn A tid n p q → G p.1.st →
        ThreadNPn A tid n (castT (ex := ex) (dp := dp) p.1, p.2) (castT q.1, q.2) from H _ _ _ h hG
    intro n p q h
    induction h with
    | refl => exact fun _ => .refl _ _
    | step hs _ ih =>
      intro hg
      exact .step ((threadStep_castT_iff hA hg).mpr hs) (ih (good_of_threadStep hA hg hs))

theorem certOkN_castT_iff (hA : Agree I ex dp G) {A : Arch} {tid n : Nat} {t : Thread I} {m : Memory}
    (hG : G t.st) : CertOkN A tid (castT (ex := ex) (dp := dp) t) m n ↔ CertOkN A tid t m n := by
  constructor
  · rintro ⟨t', m', h, hp⟩
    exact ⟨uncastT t', m', (threadNPn_castT_iff hA (t' := uncastT t') hG).mp h, hp⟩
  · rintro ⟨t', m', h, hp⟩
    exact ⟨castT t', m', (threadNPn_castT_iff hA hG).mpr h, hp⟩

theorem certOk_castT_iff (hA : Agree I ex dp G) {A : Arch} {tid : Nat} {t : Thread I} {m : Memory}
    (hG : G t.st) : CertOk A tid (castT (ex := ex) (dp := dp) t) m ↔ CertOk A tid t m := by
  constructor
  · rintro ⟨t', m', h, hp⟩
    exact ⟨uncastT t', m', (threadNP_castT_iff hA (t' := uncastT t') hG).mp h, hp⟩
  · rintro ⟨t', m', h, hp⟩
    exact ⟨castT t', m', (threadNP_castT_iff hA hG).mpr h, hp⟩

theorem good_of_threadNP (hA : Agree I ex dp G) {A : Arch} {tid : Nat} {p q : Thread I × Memory}
    (h : ThreadNP A tid p q) (hG : G p.1.st) : G q.1.st := by
  induction h with
  | refl => exact hG
  | step hs _ ih => exact ih (good_of_threadStep hA hG hs)

theorem certWrite_castT_iff (hA : Agree I ex dp G) {A : Arch} {tid : Nat} {t : Thread I} {m : Memory}
    {p : Msg × View} (hG : G t.st) : CertWrite A tid (castT (ex := ex) (dp := dp) t) m p ↔ CertWrite A tid t m p := by
  constructor
  · rintro ⟨t1, m1, outs', o', h, hs, ho, hp⟩
    have h' := (threadNP_castT_iff hA (t' := uncastT t1) hG).mp h
    have hg1 := good_of_threadNP hA h' hG
    obtain ⟨outs, o, hs', ho', rfl⟩ := ok_mem_castT hA (t := uncastT t1) hg1 hs ho
    exact ⟨_, _, outs, o, h', hs', ho', hp⟩
  · rintro ⟨t1, m1, outs, o, h, hs, ho, hp⟩
    have hg1 := good_of_threadNP hA h hG
    obtain ⟨hs', ho'⟩ := ok_mem_castT_of (ex := ex) (dp := dp) hA hg1 hs ho
    exact ⟨castT t1, m1, _, _, (threadNP_castT_iff hA hG).mpr h, hs', ho', hp⟩

/-! ## Configurations -/

/-- Every thread of `c` is in `G`. -/
def GoodC (G : I.State → Prop) (c : Config I) : Prop :=
  ∀ (i : Nat) (t : Thread I), c.threads[i]? = some t → G t.st

theorem GoodC.withThread {G : I.State → Prop} {c : Config I} (hc : GoodC G c) {tid : Nat} {t0 t : Thread I}
    {mem : Memory} (h0 : c.threads[tid]? = some t0) (ht : G t.st) : GoodC G (c.withThread tid t mem) := by
  intro i t' h
  by_cases hi : i = tid
  · subst hi
    rw [withThread_get_self h0] at h
    cases h; exact ht
  · rw [withThread_get_ne h0 hi] at h
    exact hc i t' h

theorem goodC_init {G : I.State → Prop} {states : List I.State} (h : ∀ s ∈ states, G s)
    (initMem : List (Loc × Val)) : GoodC G (Config.init states initMem) := by
  intro i t ht
  simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  exact h s (List.mem_of_getElem? hs)

/-- A final configuration of `I` in `G` is a final configuration of its cast. -/
theorem final_castC (hA : Agree I ex dp G) {c : Config I} (hc : GoodC G c) :
    (castC (ex := ex) (dp := dp) c).final = c.final := by
  simp only [Config.final, castC, Array.all_map]
  apply Bool.eq_iff_iff.mpr
  simp only [Array.all_eq_true]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  have hg := hc i c.threads[i] (Array.getElem?_eq_getElem hi)
  simp only [Function.comp, Thread.halted, castT_st, castT_prom]
  show ((ex c.threads[i].st).isNone && _) = true ↔ _
  rw [hA.exec _ hg]

/-! ## The semantic machine -/

section Sem

variable (hA : Agree I ex dp G) {A : Arch} {c : Config I} (hc : GoodC G c)
include hA hc

theorem instrSem_castC_iff {fuel tid : Nat} {c' : Config I} :
    InstrSem A fuel tid (castC (ex := ex) (dp := dp) c) (castC c') ↔ InstrSem A fuel tid c c' := by
  constructor
  · rintro ⟨t', outs', o', ht, hs, ho, hcert, he⟩
    simp only [castC_get?, Option.map_eq_some_iff] at ht
    obtain ⟨t, ht, rfl⟩ := ht
    obtain ⟨outs, o, hs', ho', rfl⟩ := ok_mem_castT hA (hc tid t ht) hs ho
    refine ⟨t, outs, o, ht, hs', ho', (certOkN_castT_iff hA (good_of_stepOne hA (hc tid t ht) hs' ho')).mp hcert,
      castC_injective (he.trans (castC_withThread c tid o.thread o.mem).symm)⟩
  · rintro ⟨t, outs, o, ht, hs, ho, hcert, rfl⟩
    obtain ⟨hs', ho'⟩ := ok_mem_castT_of (ex := ex) (dp := dp) hA (hc tid t ht) hs ho
    refine ⟨castT t, _, castO o, by simp [ht], hs', ho',
      (certOkN_castT_iff hA (good_of_stepOne hA (hc tid t ht) hs ho)).mpr hcert, castC_withThread c tid _ _⟩

theorem promSem_castC_iff {fuel tid : Nat} {c' : Config I} :
    PromSem A fuel tid (castC (ex := ex) (dp := dp) c) (castC c') ↔ PromSem A fuel tid c c' := by
  constructor
  · rintro ⟨t', w, ht, hw, hcert, he⟩
    simp only [castC_get?, Option.map_eq_some_iff] at ht
    obtain ⟨t, ht, rfl⟩ := ht
    exact ⟨t, w, ht, hw, (certOkN_castT_iff hA (t := promThread t c.mem w) (hc tid t ht)).mp hcert,
      castC_injective (he.trans (castC_withThread c tid (promThread t c.mem w) _).symm)⟩
  · rintro ⟨t, w, ht, hw, hcert, rfl⟩
    exact ⟨castT t, w, by simp [ht], hw, (certOkN_castT_iff hA (t := promThread t c.mem w) (hc tid t ht)).mpr hcert,
      castC_withThread c tid (promThread t c.mem w) _⟩

theorem stepSem_castC_iff {fuel tid : Nat} {c' : Config I} :
    StepSem A fuel tid (castC (ex := ex) (dp := dp) c) (castC c') ↔ StepSem A fuel tid c c' :=
  or_congr (instrSem_castC_iff hA hc) (promSem_castC_iff hA hc)

theorem instrSemInf_castC_iff {tid : Nat} {c' : Config I} :
    InstrSemInf A tid (castC (ex := ex) (dp := dp) c) (castC c') ↔ InstrSemInf A tid c c' := by
  constructor
  · rintro ⟨t', outs', o', ht, hs, ho, hcert, he⟩
    simp only [castC_get?, Option.map_eq_some_iff] at ht
    obtain ⟨t, ht, rfl⟩ := ht
    obtain ⟨outs, o, hs', ho', rfl⟩ := ok_mem_castT hA (hc tid t ht) hs ho
    refine ⟨t, outs, o, ht, hs', ho', (certOk_castT_iff hA (good_of_stepOne hA (hc tid t ht) hs' ho')).mp hcert,
      castC_injective (he.trans (castC_withThread c tid o.thread o.mem).symm)⟩
  · rintro ⟨t, outs, o, ht, hs, ho, hcert, rfl⟩
    obtain ⟨hs', ho'⟩ := ok_mem_castT_of (ex := ex) (dp := dp) hA (hc tid t ht) hs ho
    refine ⟨castT t, _, castO o, by simp [ht], hs', ho',
      (certOk_castT_iff hA (good_of_stepOne hA (hc tid t ht) hs ho)).mpr hcert, castC_withThread c tid _ _⟩

theorem promSemInf_castC_iff {tid : Nat} {c' : Config I} :
    PromSemInf A tid (castC (ex := ex) (dp := dp) c) (castC c') ↔ PromSemInf A tid c c' := by
  constructor
  · rintro ⟨t', w, ht, hw, hcert, he⟩
    simp only [castC_get?, Option.map_eq_some_iff] at ht
    obtain ⟨t, ht, rfl⟩ := ht
    exact ⟨t, w, ht, hw, (certOk_castT_iff hA (t := promThread t c.mem w) (hc tid t ht)).mp hcert,
      castC_injective (he.trans (castC_withThread c tid (promThread t c.mem w) _).symm)⟩
  · rintro ⟨t, w, ht, hw, hcert, rfl⟩
    exact ⟨castT t, w, by simp [ht], hw, (certOk_castT_iff hA (t := promThread t c.mem w) (hc tid t ht)).mpr hcert,
      castC_withThread c tid (promThread t c.mem w) _⟩

theorem stepSemInf_castC_iff {tid : Nat} {c' : Config I} :
    StepSemInf A tid (castC (ex := ex) (dp := dp) c) (castC c') ↔ StepSemInf A tid c c' :=
  or_congr (instrSemInf_castC_iff hA hc) (promSemInf_castC_iff hA hc)

/-- **`SuccKind` (the K world's step) agrees.** -/
theorem succKind_castC_iff {c' : Config I} :
    SuccKind A (castC (ex := ex) (dp := dp) c) (castC c') ↔ SuccKind A c c' := by
  constructor
  · intro h
    generalize hx : castC (ex := ex) (dp := dp) c' = x at h
    cases h with
    | @instr tid t' outs' o' ht hs ho =>
      simp only [castC_get?, Option.map_eq_some_iff] at ht
      obtain ⟨t, ht, rfl⟩ := ht
      obtain ⟨outs, o, hs', ho', rfl⟩ := ok_mem_castT hA (hc tid t ht) hs ho
      rw [castC_injective (hx.trans (castC_withThread c tid o.thread o.mem).symm)]
      exact .instr ht hs' ho'
    | @promise tid t' p ht hw =>
      simp only [castC_get?, Option.map_eq_some_iff] at ht
      obtain ⟨t, ht, rfl⟩ := ht
      rw [castC_injective (hx.trans (castC_withThread c tid { t with prom := t.prom ++ [(c.mem.append
        { p.1 with tid }).2] } _).symm)]
      exact .promise ht ((certWrite_castT_iff hA (hc tid t ht)).mp hw)
  · intro h
    cases h with
    | @instr tid t outs o ht hs ho =>
      obtain ⟨hs', ho'⟩ := ok_mem_castT_of (ex := ex) (dp := dp) hA (hc tid t ht) hs ho
      rw [castC_withThread]
      exact .instr (o := castO o) (by simp [ht]) hs' ho'
    | @promise tid t p ht hw =>
      have hw' := (certWrite_castT_iff (ex := ex) (dp := dp) hA (hc tid t ht)).mpr hw
      have hk := SuccKind.promise (A := A) (c := castC (ex := ex) (dp := dp) c) (t := castT t) (p := p)
        (by simp [ht]) hw'
      rw [castC_withThread]
      exact hk

omit hc in
theorem goodC_of_stepSem {fuel tid : Nat} {c c' : Config I} (hc : GoodC G c) (h : StepSem A fuel tid c c') :
    GoodC G c' := by
  rcases h with ⟨t, outs, o, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · exact hc.withThread ht (good_of_stepOne hA (hc tid t ht) hs ho)
  · exact hc.withThread ht (hc tid t ht)

omit hc in
theorem goodC_of_stepSemInf {tid : Nat} {c c' : Config I} (hc : GoodC G c) (h : StepSemInf A tid c c') :
    GoodC G c' := by
  rcases h with ⟨t, outs, o, ht, hs, ho, -, rfl⟩ | ⟨t, w, ht, -, -, rfl⟩
  · exact hc.withThread ht (good_of_stepOne hA (hc tid t ht) hs ho)
  · exact hc.withThread ht (hc tid t ht)

omit hc in
theorem goodC_of_succKind {c c' : Config I} (hc : GoodC G c) (h : SuccKind A c c') : GoodC G c' := by
  cases h with
  | instr ht hs ho => exact hc.withThread ht (good_of_stepOne hA (hc _ _ ht) hs ho)
  | promise ht _ => exact hc.withThread ht (hc _ _ ht :)

end Sem

section Reach

variable (hA : Agree I ex dp G) {A : Arch}
include hA

/-- **`ReachableSem` of `I` gives `ReachableSem` of the variant**, by cast. -/
theorem reachableSem_castC {fuel : Nat} {c c' : Config I} (h : ReachableSem A fuel c c') (hc : GoodC G c) :
    ReachableSem A fuel (castC (ex := ex) (dp := dp) c) (castC c') := by
  induction h with
  | refl => exact .refl _
  | step tid hs _ ih => exact .step tid ((stepSem_castC_iff hA hc).mpr hs) (ih (goodC_of_stepSem hA hc hs))

/-- **`ReachableSem` of the variant gives `ReachableSem` of `I`**, by uncast. -/
theorem reachableSem_uncastC {fuel : Nat} {c : Config I} {x : Config (I.withExec ex dp)}
    (h : ReachableSem A fuel (castC c) x) (hc : GoodC G c) : ReachableSem A fuel c (uncastC x) := by
  generalize hy : castC (ex := ex) (dp := dp) c = y at h
  induction h generalizing c with
  | refl => subst hy; rw [uncastC_castC]; exact .refl _
  | @step _ c' _ tid hs _ ih =>
    subst hy
    rw [← castC_uncastC c'] at hs
    have hs' := (stepSem_castC_iff hA hc).mp hs
    exact .step tid hs' (ih (goodC_of_stepSem hA hc hs') (castC_uncastC _))

theorem reachableSemInf_castC {c c' : Config I} (h : ReachableSemInf A c c') (hc : GoodC G c) :
    ReachableSemInf A (castC (ex := ex) (dp := dp) c) (castC c') := by
  induction h with
  | refl => exact .refl _
  | step tid hs _ ih => exact .step tid ((stepSemInf_castC_iff hA hc).mpr hs) (ih (goodC_of_stepSemInf hA hc hs))

theorem reachableSemInf_uncastC {c : Config I} {x : Config (I.withExec ex dp)}
    (h : ReachableSemInf A (castC c) x) (hc : GoodC G c) : ReachableSemInf A c (uncastC x) := by
  generalize hy : castC (ex := ex) (dp := dp) c = y at h
  induction h generalizing c with
  | refl => subst hy; rw [uncastC_castC]; exact .refl _
  | @step _ c' _ tid hs _ ih =>
    subst hy
    rw [← castC_uncastC c'] at hs
    have hs' := (stepSemInf_castC_iff hA hc).mp hs
    exact .step tid hs' (ih (goodC_of_stepSemInf hA hc hs') (castC_uncastC _))

theorem reachableK_castC {c c' : Config I} (h : ReachableK A c c') (hc : GoodC G c) :
    ReachableK A (castC (ex := ex) (dp := dp) c) (castC c') := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step ((succKind_castC_iff hA hc).mpr hs) (ih (goodC_of_succKind hA hc hs))

theorem reachableK_uncastC {c : Config I} {x : Config (I.withExec ex dp)}
    (h : ReachableK A (castC c) x) (hc : GoodC G c) : ReachableK A c (uncastC x) := by
  generalize hy : castC (ex := ex) (dp := dp) c = y at h
  induction h generalizing c with
  | refl => subst hy; rw [uncastC_castC]; exact .refl _
  | @step _ c' _ hs _ ih =>
    subst hy
    rw [← castC_uncastC c'] at hs
    have hs' := (succKind_castC_iff hA hc).mp hs
    exact .step hs' (ih (goodC_of_succKind hA hc hs') (castC_uncastC _))

/-- Reachable configurations of `I` from `G` stay in `G`. -/
theorem goodC_of_reachableK {c c' : Config I} (h : ReachableK A c c') (hc : GoodC G c) : GoodC G c' :=
  h.inv (fun _ _ hg hs => goodC_of_succKind hA hg hs) hc

end Reach

end Lower.Variant

end Kraken.Promising

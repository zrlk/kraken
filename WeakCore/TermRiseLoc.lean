import WeakCore.TermLiveProps

/-! # TermRiseLoc: a thread step raising a coherence view lands it on a message at its address

`tstep_riseLoc`: no `CohAt`/`CfgCoh` hypothesis.  Adapted from `TermLiveProps` (§ machine rules,
state helpers), dropping `CohAt` and keeping only the landing half of `Moves`. -/

namespace TermRiseLoc
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
open Promises.Sim (MemExt)
open TermLiveProps (get_ext loc_of_readable coh_le_storeOb push2_fst push2_snd ite_fence_coh stepFence_coh fold_get)

/-- A view moves from `x` to `x'`: it stays, or lands on a message at `b`. -/
def Mv1 (mem' : Memory) (b : Address) (x x' : Ts) : Prop :=
  x' = x ∨ ∃ m, mem'[x']? = some m ∧ m.loc = b

theorem cohStepE {mem mem' : Memory} {vs vs' : VState} (he : MemExt mem mem')
    (h : ∀ b, Mv1 mem' b (vs.coh b) (vs'.coh b)) : MemExt mem mem' ∧ ∀ b, Mv1 mem' b (vs.coh b) (vs'.coh b) :=
  ⟨he, h⟩

theorem mv_max {mem' : Memory} {b : Address} {x t : Ts} {m : Msg} (hm : mem'[t]? = some m)
    (hl : m.loc = b) : Mv1 mem' b x (max x t) := by
  rcases Nat.le_total x t with h | h
  · exact Or.inr ⟨m, by rw [Nat.max_eq_right h]; exact hm, hl⟩
  · exact Or.inl (Nat.max_eq_left h)

theorem stepLoad_coh {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) :
    MemExt mem mem ∧ ∀ b, Mv1 mem b (th.vs.coh b) (th'.vs.coh b) := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨_, hr⟩, rfl⟩ := h
  obtain ⟨m, hm, hl⟩ := loc_of_readable hr
  refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
  by_cases hb : b = a
  · subst hb; simp only [eq_self, ↓reduceIte]; exact mv_max hm hl
  · simp only [hb, ↓reduceIte]; exact Or.inl rfl

theorem stepLoadPair_coh {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th d0 d1 a deps acq) :
    MemExt mem mem ∧ ∀ b, Mv1 mem b (th.vs.coh b) (th'.vs.coh b) := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hs⟩ := h
  split at hs
  · cases hs
  · cases hs
    obtain ⟨m0, hm0, hl0⟩ := loc_of_readable hr0
    obtain ⟨m1, hm1, hl1⟩ := loc_of_readable hr1
    refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
    by_cases hb : b = a
    · subst hb; simp only [eq_self, ↓reduceIte]; exact mv_max hm0 hl0
    · by_cases hb1 : b = a.next
      · subst hb1; simp only [hb, eq_self, ↓reduceIte]; exact mv_max hm1 hl1
      · simp only [hb, hb1, ↓reduceIte]; exact Or.inl rfl

theorem stepStore_coh {k : Promises.Knobs} {arch : Arch} {mem : Memory} {th : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} {mem' : Memory}
    {th' : Promises.Thread} (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel)
    : MemExt mem mem' ∧ ∀ b, Mv1 mem' b (th.vs.coh b) (th'.vs.coh b) := by
  simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
  rcases h with h | ⟨t, _, hf⟩
  · cases h
    refine cohStepE (Promises.Sim.MemExt.push _ _) fun b => ?_
    by_cases hb : b = a
    · subst hb; simp only [eq_self, ↓reduceIte]
      exact Or.inr ⟨_, Array.getElem?_push_size, rfl⟩
    · simp only [hb, ↓reduceIte]; exact Or.inl rfl
  · split at hf
    · cases hf
    · rename_i m hm
      simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hf
      obtain ⟨hcond, hf⟩ := hf
      cases hf
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
      obtain ⟨⟨⟨hl, _⟩, _⟩, hob⟩ := hcond
      refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
      by_cases hb : b = a
      · subst hb; simp only [eq_self, ↓reduceIte]
        exact Or.inr ⟨_, hm, hl⟩
      · simp only [hb, ↓reduceIte]; exact Or.inl rfl

theorem stepStorePair_coh {mem : Memory} {pairs : List Ts} {th : Promises.Thread} {a : Address}
    {e0 e1 : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool} :
    MemExt mem (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1 ∧
    ∀ b, Mv1 (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1 b (th.vs.coh b)
      ((Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2.vs.coh b) := by
  refine cohStepE (Promises.Sim.MemExt.trans (Promises.Sim.MemExt.push _ _)
    (Promises.Sim.MemExt.push _ _)) fun b => ?_
  simp only [Promises.stepStorePair]
  by_cases hb : b = a
  · subst hb; simp only [eq_self, ↓reduceIte]
    exact Or.inr ⟨_, (push2_fst _ _ _), rfl⟩
  · by_cases hb1 : b = a.next
    · subst hb1; simp only [hb, eq_self, ↓reduceIte]
      exact Or.inr ⟨_, (push2_snd _ _ _), rfl⟩
    · simp only [hb, hb1, ↓reduceIte]; exact Or.inl rfl

theorem stepRmw_coh_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a cmp newv deps acq rel)
    : MemExt mem mem' ∧ ∀ b, Mv1 mem' b (th.vs.coh b) (th'.vs.coh b) := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨_, hr⟩, hbody⟩ := h
  obtain ⟨m, hm, hl⟩ := loc_of_readable hr
  split at hbody
  · rw [List.mem_singleton] at hbody
    cases hbody
    refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
    rw [ite_fence_coh]
    by_cases hb : b = a
    · subst hb; simp only [eq_self, ↓reduceIte]; exact mv_max hm hl
    · simp only [hb, ↓reduceIte]; exact Or.inl rfl
  · rw [List.mem_append] at hbody
    rcases hbody with happ | hful
    · split at happ
      · rw [List.mem_singleton] at happ
        cases happ
        refine cohStepE (Promises.Sim.MemExt.push _ _) fun b => ?_
        rw [ite_fence_coh]
        by_cases hb : b = a
        · subst hb; simp only [eq_self, ↓reduceIte]
          exact Or.inr ⟨_, Array.getElem?_push_size, rfl⟩
        · simp only [hb, ↓reduceIte]; exact Or.inl rfl
      · simp at happ
    · obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
      split at hft
      · cases hft
      · rename_i pm hpm
        simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
        obtain ⟨hcond, hft⟩ := hft
        cases hft
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
        obtain ⟨⟨⟨⟨hl', _⟩, _⟩, hob⟩, _⟩ := hcond
        refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
        rw [ite_fence_coh]
        by_cases hb : b = a
        · subst hb
          simp only [eq_self, ↓reduceIte] at hob ⊢
          exact Or.inr ⟨_, hpm, hl'⟩
        · simp only [hb, ↓reduceIte]; exact Or.inl rfl

theorem stepRmw_coh {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a cmp newv deps acq rel)
    : MemExt mem mem' ∧ ∀ b, Mv1 mem' b (th.vs.coh b) (th'.vs.coh b) := by
  have hx := stepRmw_coh_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rw [ite_fence_coh] at hx
  exact hx

theorem stepRmwPair_coh_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    : MemExt mem mem' ∧ ∀ b, Mv1 mem' b (th.vs.coh b) (th'.vs.coh b) := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨_, hr0⟩, t1, ⟨_, hr1⟩, hbody⟩ := h
  obtain ⟨m0, hm0, hl0⟩ := loc_of_readable hr0
  obtain ⟨m1, hm1, hl1⟩ := loc_of_readable hr1
  split at hbody
  · simp at hbody
  · split at hbody
    · rw [List.mem_singleton] at hbody
      cases hbody
      refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
      rw [ite_fence_coh]
      by_cases hb : b = a
      · subst hb; simp only [eq_self, ↓reduceIte]; exact mv_max hm0 hl0
      · by_cases hb1 : b = a.next
        · subst hb1; simp only [hb, eq_self, ↓reduceIte]; exact mv_max hm1 hl1
        · simp only [hb, hb1, ↓reduceIte]; exact Or.inl rfl
    · rw [List.mem_append] at hbody
      rcases hbody with happ | hful
      · split at happ
        · rw [List.mem_singleton] at happ
          cases happ
          refine cohStepE (Promises.Sim.MemExt.trans (Promises.Sim.MemExt.push _ _)
            (Promises.Sim.MemExt.push _ _)) fun b => ?_
          rw [ite_fence_coh]
          by_cases hb : b = a
          · subst hb; simp only [eq_self, ↓reduceIte]
            exact Or.inr ⟨_, (push2_fst _ _ _), rfl⟩
          · by_cases hb1 : b = a.next
            · subst hb1; simp only [hb, eq_self, ↓reduceIte]
              exact Or.inr ⟨_, (push2_snd _ _ _), rfl⟩
            · simp only [hb, hb1, ↓reduceIte]; exact Or.inl rfl
        · simp at happ
      · obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
        split at hft
        · rename_i pm0 pm1 hpm0 hpm1
          simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
          obtain ⟨hcond, hft⟩ := hft
          · cases hft
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hla⟩, _⟩, _⟩, hlb⟩, _⟩, _⟩, hob⟩, _⟩, hadj1⟩ := hcond
            refine cohStepE (Promises.Sim.MemExt.refl _) fun b => ?_
            rw [ite_fence_coh]
            by_cases hb : b = a
            · subst hb
              simp only [eq_self, ↓reduceIte] at hob ⊢
              exact Or.inr ⟨_, hpm0, hla⟩
            · by_cases hb1 : b = a.next
              · subst hb1; simp only [hb, eq_self, ↓reduceIte]
                exact Or.inr ⟨_, hpm1, hlb⟩
              · simp only [hb, hb1, ↓reduceIte]; exact Or.inl rfl
        · cases hft

theorem stepRmwPair_coh {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    : MemExt mem mem' ∧ ∀ b, Mv1 mem' b (th.vs.coh b) (th'.vs.coh b) := by
  have hx := stepRmwPair_coh_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  rw [ite_fence_coh] at hx
  exact hx

/-! ### The state helpers -/

/-- `s'` extends memory and each view stays or lands at its address. -/
def Mono (s s' : St) : Prop :=
  MemExt s.mem s'.mem ∧ ∀ b, Mv1 s'.mem b (s.vs.coh b) (s'.vs.coh b)

@[simp] theorem Mono.reflE (s : St) : Mono s s := ⟨Promises.Sim.MemExt.refl _, fun _ => Or.inl rfl⟩

theorem Mono.trans {s1 s2 s3 : St} (a : Mono s1 s2) (b : Mono s2 s3) : Mono s1 s3 := by
  refine ⟨Promises.Sim.MemExt.trans a.1 b.1, fun x => ?_⟩
  rcases b.2 x with e3 | h3
  · rcases a.2 x with e2 | ⟨m, hm, hl⟩
    · exact Or.inl (e3.trans e2)
    · exact Or.inr ⟨m, by rw [e3]; exact get_ext b.1 hm, hl⟩
  · exact Or.inr h3

@[simp] theorem fenceS_mono (s : St) (f : WeakMem.Fence) : Mono s (fenceS s f) := by
  have e : (fenceS s f).vs.coh = s.vs.coh := stepFence_coh _ f
  exact ⟨Promises.Sim.MemExt.refl _, fun b => Or.inl (by rw [e])⟩

theorem loadUnits_mono (arch : Arch) (pw : Word) (a : Address) (acq : Bool) :
    ∀ (us : List Acc) (k : Nat) (s : St) {s' : St} {ws : List Word},
    (s', ws) ∈ loadUnits arch pw a acq us k s → Mono s s'
  | [], k, s, s', ws, h => by
      simp only [loadUnits, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Mono.reflE _
  | .one :: us, k, s, s', ws, h => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, hth, ⟨s2, ws2⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Mono.trans ?_ (loadUnits_mono arch pw a acq us _ _ hin)
      exact stepLoad_coh hth
  | .two :: us, k, s, s', ws, h => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at h
      obtain ⟨th, hth, ⟨s2, ws2⟩, hin, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      refine Mono.trans ?_ (loadUnits_mono arch pw a acq us _ _ hin)
      exact stepLoadPair_coh hth

theorem storeUnits_mono (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St},
    s' ∈ storeUnits k arch pw a rel us ws i s → Mono s s'
  | [], ws, i, s, s', h => by
      simp only [storeUnits, List.mem_singleton] at h
      subst h; exact Mono.reflE _
  | .one :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .one :: us, w :: ws, i, s, s', h => by
      simp only [storeUnits, List.mem_flatMap] at h
      obtain ⟨⟨mem', th⟩, hst, hin⟩ := h
      refine Mono.trans ?_ (storeUnits_mono k arch pw a rel us ws _ _ hin)
      exact stepStore_coh hst
  | .two :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, [_], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, w0 :: w1 :: ws, i, s, s', h => by
      have hp := stepStorePair_coh (mem := s.mem) (pairs := s.pairs) (th := mth s pw w0 w1) (a := offs a i)
        (e0 := dataE 1 w0) (e1 := dataE 2 w1) (deps := [0]) (rel := rel)
      unfold storeUnits at h
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel = q at h hp
      obtain ⟨mem', pairs', th⟩ := q
      refine Mono.trans ?_ (storeUnits_mono k arch pw a rel us ws _ _ h)
      exact hp

theorem fold_get (f : Nat → Msg) : ∀ (l : List Nat) (m : Memory) (i : Nat) (hi : i < l.length),
    (l.foldl (fun m j => m.push (f j)) m)[m.size + i]? = some (f l[i])
  | [], m, i, hi => by simp at hi
  | j :: l, m, 0, _ => by
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      exact get_ext (TermArch.fold_push_ext f l _) Array.getElem?_push_size
  | j :: l, m, i + 1, hi => by
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := fold_get f l (m.push (f j)) i (by simp at hi; omega)
      rw [Array.size_push] at this
      rw [show m.size + (i + 1) = m.size + 1 + i by omega]
      exact this

/-- The views `new`/`newBuf` set: each fresh cell's sits on its first message,
which is above every old view. -/
theorem allocCoh {mem : Memory} {vs : VState} (lbl : AllocLabel) (n : Nat)
    (g : Nat → Val) :
    MemExt mem ((List.range n).foldl (fun m j => m.push ⟨offs ⟨lbl, 0⟩ j, g j, 0⟩) mem) ∧
    ∀ b, Mv1 ((List.range n).foldl (fun m j => m.push ⟨offs ⟨lbl, 0⟩ j, g j, 0⟩) mem) b (vs.coh b)
      (if b.label = lbl ∧ b.offset < n then mem.size + b.offset else vs.coh b) := by
  refine ⟨TermArch.fold_push_ext _ _ _, fun b => ?_⟩
  split
  · rename_i hb
    obtain ⟨hl, ho⟩ := hb
    refine Or.inr ⟨_, fold_get _ _ _ _ (by simpa using ho), ?_⟩
    simp only [List.getElem_range, offs]
    cases b; simp_all
  · exact Or.inl rfl

theorem alloc_mono {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : Mono s s' := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  refine Mono.trans ?_ (storeUnits_mono k arch _ _ false us ws 0 _ hs2)
  exact allocCoh (mem := s.mem) (vs := s.vs) lbl (nWords us) (fun _ => .undef)

@[simp] theorem allocBuf_mono (lbl : AllocLabel) (n : Nat) (zero : Option (List Val)) (s : St) :
    Mono s (allocBuf lbl n zero s).1 := allocCoh lbl n _

macro "flatR" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, Mono.reflE, fenceS_mono, allocBuf_mono, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

macro "close_rmono" : tactic => `(tactic| first
    | done
    | exact Mono.reflE _
    | exact fenceS_mono _ _
    | exact allocBuf_mono _ _ _ _
    | exact loadUnits_mono _ _ _ _ _ _ _ (by assumption)
    | exact storeUnits_mono _ _ _ _ _ _ _ _ _ (by assumption)
    | exact alloc_mono (by assumption)
    | exact Mono.trans (loadUnits_mono _ _ _ _ _ _ _ (by assumption))
        (storeUnits_mono _ _ _ _ _ _ _ _ _ (by assumption))
    | exact Mono.trans (alloc_mono (by assumption)) (fenceS_mono _ _)
    | exact Mono.trans (loadUnits_mono _ _ _ _ _ _ _ (by assumption))
        (loadUnits_mono _ _ _ _ _ _ _ (by assumption)))

macro "crushR1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flatR)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try close_rmono)))

macro "crushR" : tactic => `(tactic| (
  intro r hin
  revert hin
  crushR1
  all_goals (try (rename_i hh; revert hh; crushR1))
  all_goals (try (rename_i hh; revert hh; crushR1))))

theorem projM_mono (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, Mono s r.1 := by
  unfold projM
  crushR

theorem injM_mono (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, Mono s r.1 := by
  unfold injM
  crushR

theorem rmw_mono {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : Mono s s' := by
  have := stepRmw_coh h
  subst hs; unfold Mono; rw [hm, hv]; exact this

theorem evalOp_mono (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, Mono s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crushR
  all_goals first
    | exact Mono.trans (projM_mono _ _ _ _ _ (by assumption)) (injM_mono _ _ _ _ _ _ (by assumption))
    | exact rmw_mono (by assumption) (by rfl) (by rfl) (by rfl)

theorem enter_vsE {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.vs = th.vs := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Prod.exists] at h
  obtain ⟨_, _, _, _, _, rfl⟩ := h
  rfl

theorem enter_mono {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hv : th0.vs = th.vs) :
    Mono (stOf mem pairs th) (stOf mem pairs th') := by
  have e : th'.vs = th.vs := (enter_vsE h).trans hv
  show MemExt mem mem ∧ ∀ b, Mv1 mem b (th.vs.coh b) (th'.vs.coh b)
  rw [e]; exact ⟨Promises.Sim.MemExt.refl _, fun _ => Or.inl rfl⟩

theorem rmwPair_mono {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : Mono s s' := by
  have := stepRmwPair_coh h
  subst hs; unfold Mono; rw [hm, hv]; exact this

/-- A thread step: each view stays or lands at its address. -/
theorem tstep_mono (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, Mono (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crushR
  all_goals first
    | exact evalOp_mono _ _ _ _ _ _ (by assumption)
    | exact Mono.trans (projM_mono _ _ _ _ _ (by assumption)) (injM_mono _ _ _ _ _ _ (by assumption))
    | exact enter_mono (by assumption) (by rfl)
    | exact rmw_mono (by assumption) (by rfl) (by rfl) (by rfl)
    | exact rmwPair_mono (by assumption) (by rfl) (by rfl) (by rfl)


/-- **A rise lands**: a thread step that changes the coherence view at `b` puts it on a message at `b`. -/
theorem tstep_riseLoc {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (h : r ∈ tstep g mem pairs th) {b : Address} (hb : th.vs.coh b < r.2.2.vs.coh b) :
    ∃ m, r.1[r.2.2.vs.coh b]? = some m ∧ m.loc = b :=
  ((tstep_mono g mem pairs th r h).2 b).resolve_left (fun e => Nat.lt_irrefl _ (e ▸ hb))

#print axioms tstep_riseLoc

end TermRiseLoc

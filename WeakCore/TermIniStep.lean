import WeakCore.TermStepper

/-!
# Holder bound, step 1: a thread step fulfils only below its new `vWr`

`tstep_vful`: across a thread step, memory extends, `vWr` grows, and every
promise (at a message) the step removes lies at or below the new `vWr`.  The
`VMono` framework of TermStepper, with `VFul` in place of `VMono`.
-/

namespace TermIniStep

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermFul
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (projM_keep stepRmwPair_shape loadUnits_keep)

/-- Memory extends, `vWr` grows, and a removed promise at a message lies at or
below the new `vWr`. -/
def VFul (s s' : St) : Prop :=
  MemExt s.mem s'.mem ∧ s.vs.vWr ≤ s'.vs.vWr ∧
    ∀ t ∈ s.promises, t < s.mem.size → t ∉ s'.promises → t ≤ s'.vs.vWr

theorem VFul.refl' (s : St) : VFul s s := ⟨MemExt.rfl' _, Nat.le_refl _, fun _ h _ h' => absurd h h'⟩

theorem VFul.trans {s1 s2 s3 : St} (a : VFul s1 s2) (b : VFul s2 s3) : VFul s1 s3 := by
  refine ⟨a.1.trans b.1, Nat.le_trans a.2.1 b.2.1, fun t h1 hl h3 => ?_⟩
  by_cases h2 : t ∈ s2.promises
  · exact b.2.2 t h2 (Nat.lt_of_lt_of_le hl (memExt_size a.1)) h3
  · exact Nat.le_trans (a.2.2 t h1 hl h2) b.2.1

theorem VFul.of_keep {s s' : St} (h : KeepR s s') (hv : s.vs.vWr ≤ s'.vs.vWr) : VFul s s' :=
  ⟨h.1, hv, fun t ht hl hn => absurd (h.2.2 t ht hl) hn⟩

theorem VFul.of_eq {s s' : St} (hm : s'.mem = s.mem) (hp : s'.promises = s.promises)
    (hv : s.vs.vWr ≤ s'.vs.vWr) : VFul s s' :=
  VFul.of_keep (keepR_eq hm hp) hv

theorem VFul.of_fulW {s s' : St} (hm : MemExt s.mem s'.mem) (h : FulW s.vs s.promises s'.vs s'.promises) :
    VFul s s' :=
  ⟨hm, h.1, fun t ht _ hn => h.2 t ht hn⟩

theorem VFul.toFulW {s s' : St} (h : VFul s s') (hlt : ∀ t ∈ s.promises, t < s.mem.size) :
    FulW s.vs s.promises s'.vs s'.promises :=
  ⟨h.2.1, fun t ht hn => h.2.2 t ht (hlt t ht) hn⟩

theorem lockFence_prom (arch : Arch) (x : Promises.Thread) :
    (if arch = .tso then Promises.stepFence x .sy else x).promises = x.promises := by
  split <;> rfl

@[simp] theorem fenceS_vful (s : St) (f : WeakMem.Fence) : VFul s (fenceS s f) :=
  VFul.of_eq rfl rfl (by cases f <;> exact Nat.le_refl _)

@[simp] theorem allocBuf_vful (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St) :
    VFul s (allocBuf lbl n zero s).1 :=
  VFul.of_keep allocBuf_keep (by dsimp only [allocBuf]; exact Nat.le_max_left _ _)

theorem loadUnits_vful (arch : Arch) (pw : Word) (a : Address) (acq : Bool) (us : List Acc) (k : Nat) (s : St)
    {s' : St} {ws : List Word} (h : (s', ws) ∈ loadUnits arch pw a acq us k s) : VFul s s' := by
  have e := loadUnits_keep us k s (s', ws) h
  have e2 := loadUnits_vWr us k s (s', ws) h
  simp only at e e2
  exact VFul.of_eq e.1 e.2.2 (by rw [e2]; exact Nat.le_refl _)

theorem storeUnits_vful (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool)
    (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St}
    (h : s' ∈ storeUnits k arch pw a rel us ws i s) : VFul s s' :=
  VFul.of_fulW (storeUnits_grow us ws i s s' h).1 (storeUnits_fulW us ws i s s' h)

theorem alloc_vful {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : VFul s s' :=
  VFul.of_fulW (alloc_grow h).1 (alloc_fulW h)

/-- An RMW: `FulW` (a fulfil raises `vWr` to the fulfilled index). -/
theorem stepRmw_fulW_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    FulW th.vs th.promises th'.vs th'.promises := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, -, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by rw [lockFence_vWr]; exact Nat.le_refl _, fun t h1 h2 => absurd ?_ h2⟩
    rw [lockFence_prom]; exact h1
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by rw [lockFence_vWr]; exact Nat.le_max_left _ _, fun t h1 h2 => absurd ?_ h2⟩
        rw [lockFence_prom]; exact h1
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          refine ⟨by rw [lockFence_vWr]; exact Nat.le_max_left _ _, fun t h1 h2 => ?_⟩
          rw [lockFence_vWr]
          rw [lockFence_prom] at h2
          by_cases e : t = tw
          · subst e; exact Nat.le_max_right _ _
          · exact absurd ((List.mem_erase_of_ne e).2 h1) h2

theorem stepRmw_fulW {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    FulW th.vs th.promises th'.vs th'.promises := by
  obtain ⟨h1, h2⟩ := stepRmw_fulW_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  refine ⟨by rw [lockFence_vWr] at h1; exact h1, fun t ht hn => h2 t (by rw [lockFence_prom]; exact ht) hn⟩

/-- A pair RMW: `FulW`. -/
theorem stepRmwPair_fulW_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    FulW th.vs th.promises th'.vs th'.promises := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨by rw [lockFence_vWr]; exact Nat.le_refl _, fun t h1 h2 => absurd ?_ h2⟩
    rw [lockFence_prom]; exact h1
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      refine ⟨by rw [lockFence_vWr]; exact Nat.le_max_left _ _, fun t h1 h2 => absurd ?_ h2⟩
      rw [lockFence_prom]; exact h1
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      refine ⟨by rw [lockFence_vWr]; exact Nat.le_max_left _ _, fun t h1 h2 => ?_⟩
      rw [lockFence_vWr]
      rw [lockFence_prom] at h2
      by_cases e1 : t = tw + 1
      · subst e1; exact Nat.le_max_right _ _
      · by_cases e0 : t = tw
        · subst e0; exact Nat.le_trans (Nat.le_succ _) (Nat.le_max_right _ _)
        · exact absurd ((List.mem_erase_of_ne e1).2 ((List.mem_erase_of_ne e0).2 h1)) h2
    · cases hf

theorem stepRmwPair_fulW {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    FulW th.vs th.promises th'.vs th'.promises := by
  obtain ⟨h1, h2⟩ := stepRmwPair_fulW_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  refine ⟨by rw [lockFence_vWr] at h1; exact h1, fun t ht hn => h2 t (by rw [lockFence_prom]; exact ht) hn⟩

theorem rmw_vful {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) (hp : s'.promises = th'.promises) :
    VFul s s' := by
  have e := (stepRmw_ful h).1
  have f := stepRmw_fulW h
  refine VFul.of_fulW (by rw [hm, hs]; exact e) ?_
  rw [hv, hp]; exact f

theorem rmwPair_vful {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) (hp : s'.promises = th'.promises) :
    VFul s s' := by
  have e := (stepRmwPair_grow h).1
  have f := stepRmwPair_fulW h
  refine VFul.of_fulW (by rw [hm, hs]; exact e) ?_
  rw [hv, hp]; exact f

macro "flatVF" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, VFul.refl', fenceS_vful, allocBuf_vful, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

macro "closeVF" : tactic => `(tactic| first
    | done
    | exact VFul.refl' _
    | exact fenceS_vful _ _
    | exact allocBuf_vful _ _ _ _
    | exact loadUnits_vful _ _ _ _ _ _ _ (by assumption)
    | exact storeUnits_vful _ _ _ _ _ _ _ _ _ (by assumption)
    | exact alloc_vful (by assumption)
    | exact VFul.trans (loadUnits_vful _ _ _ _ _ _ _ (by assumption))
        (storeUnits_vful _ _ _ _ _ _ _ _ _ (by assumption))
    | exact VFul.trans (alloc_vful (by assumption)) (fenceS_vful _ _)
    | exact VFul.trans (loadUnits_vful _ _ _ _ _ _ _ (by assumption))
        (loadUnits_vful _ _ _ _ _ _ _ (by assumption)))

macro "crushVF1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flatVF)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try closeVF)))

macro "crushVF" : tactic => `(tactic| (
  intro r hin
  revert hin
  crushVF1
  all_goals (try (rename_i hh; revert hh; crushVF1))
  all_goals (try (rename_i hh; revert hh; crushVF1))))

theorem projM_vful (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, VFul s r.1 := by
  unfold projM
  crushVF

theorem injM_vful (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, VFul s r.1 := by
  unfold injM
  crushVF

set_option maxHeartbeats 400000 in
theorem evalOp_vful (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, VFul s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crushVF
  all_goals first
    | exact VFul.trans (projM_vful _ _ _ _ _ (by assumption)) (injM_vful _ _ _ _ _ _ (by assumption))
    | exact rmw_vful (by assumption) (by rfl) (by rfl) (by rfl) (by rfl)

theorem enter_vful {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hv : th0.vs = th.vs)
    (hp : th0.promises = th.promises) :
    VFul (stOf mem pairs th) (stOf mem pairs th') := by
  have e := enter_eq h
  refine VFul.of_eq rfl (e.2.trans hp) ?_
  show th.vs.vWr ≤ th'.vs.vWr
  rw [e.1, hv]; exact Nat.le_refl _

/-- **A thread step fulfils only at or below its new `vWr`.** -/
theorem tstep_vful (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, VFul (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crushVF
  all_goals first
    | exact evalOp_vful _ _ _ _ _ _ (by assumption)
    | exact VFul.trans (projM_vful _ _ _ _ _ (by assumption)) (injM_vful _ _ _ _ _ _ (by assumption))
    | exact enter_vful (by assumption) (by rfl) (by rfl)
    | exact rmw_vful (by assumption) (by rfl) (by rfl) (by rfl) (by rfl)
    | exact rmwPair_vful (by assumption) (by rfl) (by rfl) (by rfl) (by rfl)

theorem tstep_fulW {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hr : r ∈ tstep g mem pairs th) (hlt : ∀ t ∈ th.promises, t < mem.size) :
    FulW th.vs th.promises r.2.2.vs r.2.2.promises :=
  (tstep_vful g mem pairs th r hr).toFulW hlt

end TermIniStep

#print axioms TermIniStep.stepRmw_fulW
#print axioms TermIniStep.stepRmwPair_fulW
#print axioms TermIniStep.tstep_vful
#print axioms TermIniStep.tstep_fulW

import WeakCore.TermBoxOwn

/-!
# TermVwrLt: `vWr` stays strictly below memory (`vwrLt`, `boxFrLt`)

`VWrLe` gives `vWr ≤ size`; T.pay (`runAgree_payW` at `n + 1 = size`) needs
`B.fr ≤ size - 1`.  A thread step raises `vWr` only to a timestamp that is a
message (`max vWr t`, `t < size'`) or, at an allocation, to `size + n - 1`
(`≤ size' - 1`, also for `n = 0`).  The framework is a copy of
`TermStepper`'s `VMono` with `size - 1` in place of `size`.
-/

namespace TermVwrLt

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (projM_keep stepRmwPair_shape loadUnits_keep)

def VLt (s s' : St) : Prop := s.vs.vWr ≤ s.mem.size - 1 → s'.vs.vWr ≤ s'.mem.size - 1

@[simp] theorem VLt.refl' (s : St) : VLt s s := id

theorem VLt.trans {s1 s2 s3 : St} (a : VLt s1 s2) (b : VLt s2 s3) : VLt s1 s3 := fun h => b (a h)

@[simp] theorem fenceS_vlt (s : St) (f : WeakMem.Fence) : VLt s (fenceS s f) := fun h => by
  cases f <;> exact h

theorem loadUnits_vlt (arch : Arch) (pw : Word) (a : Address) (acq : Bool) (us : List Acc) (k : Nat) (s : St)
    {s' : St} {ws : List Word} (h : (s', ws) ∈ loadUnits arch pw a acq us k s) : VLt s s' := fun hv => by
  have e1 := (loadUnits_keep us k s (s', ws) h).1
  have e2 := loadUnits_vWr us k s (s', ws) h
  simp only at e1 e2
  rw [e1, e2]; exact hv

theorem storeUnits_vlt (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St},
    s' ∈ storeUnits k arch pw a rel us ws i s → VLt s s'
  | [], ws, i, s, s', h => by
      simp only [storeUnits, List.mem_singleton] at h
      subst h; exact VLt.refl' _
  | .one :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .one :: us, w :: ws, i, s, s', h => by
      simp only [storeUnits, List.mem_flatMap] at h
      obtain ⟨⟨mem', th⟩, hst, hin⟩ := h
      refine VLt.trans ?_ (storeUnits_vlt k arch pw a rel us ws _ _ hin)
      intro hv
      obtain ⟨t, hc, -, -, hw⟩ := stepStore_casesC hst
      show th.vs.vWr ≤ mem'.size - 1
      rw [hw]
      refine Nat.max_le.2 ⟨?_, ?_⟩
      · rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
        · exact Nat.le_trans hv (by simp only [Array.size_push]; omega)
        · exact hv
      · rcases hc with ⟨rfl, rfl, -⟩ | ⟨rfl, -, -, -, m, hm, -⟩
        · simp only [Array.size_push]; omega
        · have := lt_of_get hm; omega
  | .two :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, [_], i, s, s', h => by simp [storeUnits] at h
  | .two :: us, w0 :: w1 :: ws, i, s, s', h => by
      obtain ⟨q1, -, -, -, -⟩ := TermMem.stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      have q6 := stepStorePair_vWr s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      unfold storeUnits at h
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel = q at h q1 q6
      obtain ⟨mem', pairs', th⟩ := q
      refine VLt.trans ?_ (storeUnits_vlt k arch pw a rel us ws _ _ h)
      intro hv
      show th.vs.vWr ≤ mem'.size - 1
      simp only at q1 q6
      rw [q6, q1]; simp only [Array.size_push]
      exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩

theorem alloc_vlt {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : VLt s s' := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  refine VLt.trans ?_ (storeUnits_vlt k arch _ _ false us ws 0 _ hs2)
  intro hv
  dsimp only
  rw [fold_size]
  exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩

@[simp] theorem allocBuf_vlt (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St) :
    VLt s (allocBuf lbl n zero s).1 := fun hv => by
  dsimp only [allocBuf]
  rw [fold_size]
  exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩

theorem stepRmw_vlt_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hv : th.vs.vWr ≤ mem.size - 1) : th'.vs.vWr ≤ mem'.size - 1 := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, -, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [TermStepper.lockFence_vWr]; exact hv
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [TermStepper.lockFence_vWr]; simp only [Array.size_push]
        exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          rw [TermStepper.lockFence_vWr]; have := lt_of_get hm; exact Nat.max_le.2 ⟨hv, by omega⟩

theorem stepRmw_vlt {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hv : th.vs.vWr ≤ mem.size - 1) : th'.vs.vWr ≤ mem'.size - 1 := by
  exact stepRmw_vlt_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [TermStepper.lockFence_vWr]; exact hv)

theorem stepRmwPair_vlt_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hv : th.vs.vWr ≤ mem.size - 1) : th'.vs.vWr ≤ mem'.size - 1 := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [TermStepper.lockFence_vWr]; exact hv
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [TermStepper.lockFence_vWr]; simp only [Array.size_push]
      exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      rw [TermStepper.lockFence_vWr]; have := lt_of_get (by assumption); exact Nat.max_le.2 ⟨hv, by omega⟩
    · cases hf

theorem stepRmwPair_vlt {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hv : th.vs.vWr ≤ mem.size - 1) : th'.vs.vWr ≤ mem'.size - 1 := by
  exact stepRmwPair_vlt_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [TermStepper.lockFence_vWr]; exact hv)

theorem rmw_vlt {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : VLt s s' := fun hw => by
  rw [hm, hv]; exact stepRmw_vlt h (by rw [← hs]; exact hw)

theorem rmwPair_vlt {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : VLt s s' := fun hw => by
  rw [hm, hv]; exact stepRmwPair_vlt h (by rw [← hs]; exact hw)

macro "flatVL" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, VLt.refl', fenceS_vlt, allocBuf_vlt, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

macro "closeVL" : tactic => `(tactic| first
    | done
    | exact VLt.refl' _
    | exact fenceS_vlt _ _
    | exact allocBuf_vlt _ _ _ _
    | exact loadUnits_vlt _ _ _ _ _ _ _ (by assumption)
    | exact storeUnits_vlt _ _ _ _ _ _ _ _ _ (by assumption)
    | exact alloc_vlt (by assumption)
    | exact VLt.trans (loadUnits_vlt _ _ _ _ _ _ _ (by assumption))
        (storeUnits_vlt _ _ _ _ _ _ _ _ _ (by assumption))
    | exact VLt.trans (alloc_vlt (by assumption)) (fenceS_vlt _ _)
    | exact VLt.trans (loadUnits_vlt _ _ _ _ _ _ _ (by assumption))
        (loadUnits_vlt _ _ _ _ _ _ _ (by assumption)))

macro "crushVL1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flatVL)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try closeVL)))

macro "crushVL" : tactic => `(tactic| (
  intro r hin
  revert hin
  crushVL1
  all_goals (try (rename_i hh; revert hh; crushVL1))
  all_goals (try (rename_i hh; revert hh; crushVL1))))

theorem projM_vlt (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, VLt s r.1 := by
  unfold projM
  crushVL

theorem injM_vlt (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, VLt s r.1 := by
  unfold injM
  crushVL

theorem evalOp_vlt (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, VLt s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crushVL
  all_goals first
    | exact VLt.trans (projM_vlt _ _ _ _ _ (by assumption)) (injM_vlt _ _ _ _ _ _ (by assumption))
    | exact rmw_vlt (by assumption) (by rfl) (by rfl) (by rfl)

theorem enter_vlt {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hv : th0.vs = th.vs) :
    VLt (stOf mem pairs th) (stOf mem pairs th') := fun hw => by
  have e : th'.vs = th.vs := (TermLiveProps.enter_vs h).trans hv
  show th'.vs.vWr ≤ mem.size - 1
  rw [e]; exact hw

/-- A thread step keeps `vWr` within memory. -/
theorem tstep_vlt (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, VLt (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crushVL
  all_goals first
    | exact evalOp_vlt _ _ _ _ _ _ (by assumption)
    | exact VLt.trans (projM_vlt _ _ _ _ _ (by assumption)) (injM_vlt _ _ _ _ _ _ (by assumption))
    | exact enter_vlt (by assumption) (by rfl)
    | exact rmw_vlt (by assumption) (by rfl) (by rfl) (by rfl)
    | exact rmwPair_vlt (by assumption) (by rfl) (by rfl) (by rfl)

theorem tstep_vWrLt {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hr : r ∈ tstep g mem pairs th) (hv : th.vs.vWr ≤ mem.size - 1) : r.2.2.vs.vWr ≤ r.1.size - 1 :=
  tstep_vlt g mem pairs th r hr hv

/-! ## The clauses -/

/-- (`vwrLt`) Every thread's write view is at most the last timestamp. -/
def VWrLt (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.vs.vWr ≤ c.mem.size - 1

/-- (`boxFrLt`) Every box's frontier is at most the last timestamp. -/
def BoxFrLt (Eg : GEnv) (c : Cfg) : Prop := ∀ l B, Eg.box l = some B → B.fr ≤ c.mem.size - 1

section
variable {Eg : GEnv} {c c' : Cfg} {j : Nat} {th th' : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}

theorem VWrLt_init (h : ∀ (i : Nat) (thi : TTh), c.ths[i]? = some thi → thi.vs.vWr = 0) : VWrLt c :=
  fun i thi hi => by rw [h i thi hi]; exact Nat.zero_le _

theorem VWrLt_promise (hl : VWrLt c) (hj : c.ths[j]? = some th) : VWrLt (promise c j a v w) := by
  intro i thi hi
  rw [(promise_inv (a := a) (v := v) (w := w) hj).1] at hi ⊢
  simp only [Array.size_push]
  by_cases hij : i = j
  · subst hij
    rw [arr_get_set_eq _ hj] at hi; cases hi
    exact Nat.le_trans (hl _ th hj) (Nat.sub_le_sub_right (Nat.le_succ _) 1)
  · rw [arr_get_set_ne _ _ (Ne.symm hij)] at hi
    exact Nat.le_trans (hl _ _ hi) (Nat.sub_le_sub_right (Nat.le_succ _) 1)

theorem VWrLt_thread (hl : VWrLt c) (hj' : c'.ths[j]? = some th') (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?)
    (hv : th'.vs.vWr ≤ c'.mem.size - 1) (hsz : c.mem.size ≤ c'.mem.size) : VWrLt c' := by
  intro i thi hi
  by_cases hij : i = j
  · subst hij; rw [hj'] at hi; cases hi; exact hv
  · rw [ho i hij] at hi; exact Nat.le_trans (hl _ _ hi) (Nat.sub_le_sub_right hsz 1)

theorem BoxFrLt_init (h : ∀ l, Eg.box l = none) : BoxFrLt Eg c :=
  fun l B hB => by rw [h l] at hB; cases hB

/-- `BoxFrLt` after a promise step: boxes only shrink, memory grows. -/
theorem BoxFrLt_promise {Eg' : GEnv} (hb : ∀ l B, Eg'.box l = some B → Eg.box l = some B)
    (hj : c.ths[j]? = some th) (h : BoxFrLt Eg c) : BoxFrLt Eg' (promise c j a v w) := by
  intro l B hB
  rw [(promise_inv (a := a) (v := v) (w := w) hj).1]
  simp only [Array.size_push]
  exact Nat.le_trans (h l B (hb l B hB)) (Nat.sub_le_sub_right (Nat.le_succ _) 1)

end

/-- The bridge to `TermBoxZ.BoxFrLe` at `size - 1` (T.pay's `hLn`). -/
theorem BoxFrLt.frLe {Eg : GEnv} {c : Cfg} (h : BoxFrLt Eg c) : TermBoxZ.BoxFrLe Eg (c.mem.size - 1) := h

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The stepper's new `vWr` is at most the new last timestamp. -/
theorem vWrLtT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → VWrLt c →
      r.2.2.vs.vWr ≤ c'.mem.size - 1 := by
  intro c c' Eg Tot HP HS cr db i th r X hl
  rw [X.e1]; exact tstep_vWrLt X.hr (hl i th X.hth)

/-- `VWrLt` after a thread step. -/
theorem VWrLtT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → VWrLt c → VWrLt c' := by
  intro c c' Eg Tot HP HS cr db i th r X hl
  have hsz : c.mem.size ≤ c'.mem.size := by
    rw [X.e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r X.hr).mem.size
  exact VWrLt_thread hl X.e3 X.ho (vWrLtT_of X hl) hsz

/-- `BoxFrLt` after a thread step (mirrors `TermBoxOwn.boxFrLeT_of`). -/
theorem boxFrLtT_of :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
        (cr i) (db i) δ →
      VWrLt c → BoxFrLt Eg c →
      BoxFrLt (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hl hbl
  have G := TermInterf.gfoot_of X Y Z
  have hsz : c.mem.size ≤ c'.mem.size := by
    rw [X.e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r X.hr).mem.size
  have hv := vWrLtT_of X hl
  intro l B hB
  rcases G.2.2.1 l with eb | ⟨hf, hb0, B', hB', -⟩
  · have hB0 : Eg.box l = some B := by rw [← eb]; exact hB
    exact Nat.le_trans (hbl l B hB0) (Nat.sub_le_sub_right hsz 1)
  · have hBE : E'.box l = some B := by
      simp only [EgT, TermCut.GEnv.withFp, TermCut.GEnv.post, hf, ↓reduceIte] at hB
      exact hB
    exact Nat.le_trans (TermBoxOwn.newBox_fr X Y Z l B hb0 hBE) hv

end

end TermVwrLt

#print axioms TermVwrLt.tstep_vWrLt
#print axioms TermVwrLt.VWrLt_init
#print axioms TermVwrLt.VWrLt_promise
#print axioms TermVwrLt.VWrLtT_of
#print axioms TermVwrLt.BoxFrLt_init
#print axioms TermVwrLt.BoxFrLt_promise
#print axioms TermVwrLt.boxFrLtT_of

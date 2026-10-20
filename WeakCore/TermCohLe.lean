import WeakCore.TermPlantF

/-!
# TermCohLe: the stepper's coherence at a newly shared cell, and `FlipOK` at a publish

* `ownCohLe` (N16): at a cell a thread step newly shares, the stepper's coherence is at
  most its new `vWr` (in-range offsets).  From the per-thread invariant `OwnCohInv`
  (own private cells: coherence at most `vWr`), preserved by the step itself
  (`ownCohInv_step`), and a machine fact: every message a step appends is at most its
  new `vWr` (`tstep_appAll`).
* `wp` (T5): `FlipOK` at a publish's cell, from `TermTyped.flipOK_cert` and the run
  premise `CertRunC` (scope and `NoHoldPub` along solo runs from the pre-step
  configuration), which also gives `TermPlantF.CertRunT`.
-/

namespace TermCohLe
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermTyped TermCert
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Every message a thread step appends is at most its new `vWr` -/

/-- `vWr` and memory grow, and if memory grew, its new size is at most `vWr + 1`. -/
def AppAllM (mem : Memory) (vs : VState) (mem' : Memory) (vs' : VState) : Prop :=
  vs.vWr ≤ vs'.vWr ∧ mem.size ≤ mem'.size ∧ (mem.size < mem'.size → mem'.size ≤ vs'.vWr + 1)

/-- `AppAllM` on states. -/
def AppAll (s s' : St) : Prop := AppAllM s.mem s.vs s'.mem s'.vs

theorem AppAllM.refl' (mem : Memory) (vs : VState) : AppAllM mem vs mem vs :=
  ⟨Nat.le_refl _, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem AppAllM.trans {m1 m2 m3 : Memory} {v1 v2 v3 : VState}
    (a : AppAllM m1 v1 m2 v2) (b : AppAllM m2 v2 m3 v3) : AppAllM m1 v1 m3 v3 := by
  obtain ⟨a1, a2, a3⟩ := a
  obtain ⟨b1, b2, b3⟩ := b
  refine ⟨Nat.le_trans a1 b1, Nat.le_trans a2 b2, fun h => ?_⟩
  by_cases h2 : m2.size < m3.size
  · exact b3 h2
  · have := a3 (by omega)
    simp only [WeakMem.Ts] at *
    omega

theorem AppAll.trans {s1 s2 s3 : St} (a : AppAll s1 s2) (b : AppAll s2 s3) : AppAll s1 s3 :=
  AppAllM.trans a b

theorem AppAllM.keep {mem : Memory} {vs vs' : VState} (h : vs.vWr ≤ vs'.vWr) : AppAllM mem vs mem vs' :=
  ⟨h, Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl _)⟩

theorem AppAllM.push {mem : Memory} {vs vs' : VState} (m : Msg) (h : vs.vWr ≤ vs'.vWr)
    (hs : mem.size ≤ vs'.vWr) : AppAllM mem vs (mem.push m) vs' := by
  refine ⟨h, by simp only [Array.size_push]; omega, fun _ => ?_⟩
  simp only [Array.size_push, WeakMem.Ts] at *
  omega

theorem AppAllM.push2 {mem : Memory} {vs vs' : VState} (m m' : Msg) (h : vs.vWr ≤ vs'.vWr)
    (hs : mem.size + 1 ≤ vs'.vWr) : AppAllM mem vs ((mem.push m).push m') vs' := by
  refine ⟨h, by simp only [Array.size_push]; omega, fun _ => ?_⟩
  simp only [Array.size_push, WeakMem.Ts] at *
  omega

theorem appAll_lock {arch' : Arch} {mem mem' : Memory} {vs : VState} {x : Promises.Thread}
    (h : AppAllM mem vs mem' x.vs) :
    AppAllM mem vs mem' (if arch' = .tso then Promises.stepFence x .sy else x).vs := by
  split
  · exact h
  · exact h

theorem stepStore_appAll {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg}
    {rel : Bool} (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    AppAllM mem th.vs mem' th'.vs := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact AppAllM.push _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            exact AppAllM.keep (Nat.le_max_left _ _)
          · simp at hf

theorem stepRmw_appAll_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel) :
    AppAllM mem th.vs mem' th'.vs := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, _, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    apply appAll_lock
    exact AppAllM.keep (Nat.le_refl _)
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        apply appAll_lock
        exact AppAllM.push _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          apply appAll_lock
          exact AppAllM.keep (Nat.le_max_left _ _)

theorem stepRmw_appAll {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    AppAllM mem th.vs mem' th'.vs := by
  obtain ⟨h1, h2, h3⟩ := stepRmw_appAll_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  exact ⟨by rw [TermStepper.lockFence_vWr] at h1; exact h1, h2, h3⟩

theorem stepRmwPair_appAll_at {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : WeakMem.Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    AppAllM mem th.vs mem' th'.vs := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    apply appAll_lock
    exact AppAllM.keep (Nat.le_refl _)
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      apply appAll_lock
      exact AppAllM.push2 _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    cases hm : mem[tw]? with
    | none => simp [hm] at hf
    | some pm0 =>
    cases hm1 : mem[tw + 1]? with
    | none => simp [hm, hm1] at hf
    | some pm1 =>
    simp only [hm, hm1, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨-, rfl, rfl, rfl⟩ := hf
    apply appAll_lock
    exact AppAllM.keep (Nat.le_max_left _ _)

theorem stepRmwPair_appAll {arch : Arch} {mem mem' : Memory}
    {pairs pairs' : List Ts} {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address}
    {cmp0 cmp1 : WeakMem.Val} {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    AppAllM mem th.vs mem' th'.vs := by
  obtain ⟨h1, h2, h3⟩ := stepRmwPair_appAll_at (th := if arch = .tso then Promises.stepFence th .sy else th) h
  exact ⟨by rw [TermStepper.lockFence_vWr] at h1; exact h1, h2, h3⟩

theorem loadUnits_appAll {arch' : Arch} {pw : Word} {a : Address} {acq : Bool}
    {us : List Acc} {n : Nat} {s : St} {r : St × List Word} (hr : r ∈ loadUnits arch' pw a acq us n s) :
    AppAll s r.1 := by
  obtain ⟨e1, -, -⟩ := TermFul.loadUnits_keep us n s r hr
  have e2 := TermMem.loadUnits_vWr us n s r hr
  show AppAllM s.mem s.vs r.1.mem r.1.vs
  rw [e1]
  exact AppAllM.keep (Nat.le_of_eq e2.symm)

theorem storeUnits_appAll {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      AppAll s s'
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact AppAllM.refl' _ _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact AppAllM.trans (stepStore_appAll (th := mth s pw w w) hst)
        (storeUnits_appAll us ws (i + 1) _ s' hs)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have h2 : AppAllM s.mem s.vs
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).1
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).2.2.vs := by
        simp only [Promises.stepStorePair]
        exact AppAllM.push2 _ _ (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at h2 hs
      obtain ⟨mem', pairs', th⟩ := R
      exact AppAllM.trans h2 (storeUnits_appAll us ws (i + 2) _ s' hs)
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem fenceS_appAll (s : St) (f : WeakMem.Fence) : AppAll s (fenceS s f) := by
  show AppAllM s.mem s.vs s.mem (Promises.stepFence (mth s _ _ _) f).vs
  cases f <;> exact AppAllM.keep (Nat.le_refl _)

theorem fold_appAll (s : St) (n : Nat) (f : Nat → Msg) (vs : VState)
    (hv : vs.vWr = max s.vs.vWr (s.mem.size + n - 1)) :
    AppAllM s.mem s.vs ((List.range n).foldl (fun m j => m.push (f j)) s.mem) vs := by
  refine ⟨by rw [hv]; exact Nat.le_max_left _ _, ?_, fun h => ?_⟩
  · rw [TermMem.fold_size]; exact Nat.le_add_right _ _
  · rw [TermMem.fold_size] at h ⊢
    rw [hv]
    have := Nat.le_max_right s.vs.vWr (s.mem.size + n - 1)
    simp only [WeakMem.Ts] at *
    omega

theorem allocBuf_appAll (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St) :
    AppAll s (allocBuf lbl n zero s).1 := by
  unfold allocBuf
  exact fold_appAll s n _ _ rfl

theorem alloc_appAll {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : AppAll s r.1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact AppAllM.trans (fold_appAll s _ _ _ rfl) (storeUnits_appAll us ws 0 _ s' hs)

theorem injM_appAll {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word}
    {r : St × List Word} (h : r ∈ injM g s ty j p) : AppAll s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_appAll hs
      dsimp only
      split
      · exact AppAll.trans this (fenceS_appAll _ _)
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact AppAllM.refl' _ _

theorem projM_appAll {g : G} {s : St} {ty : Ty} {ws : List Word}
    {r : St × Nat × List Word} (h : r ∈ projM g s ty ws) : AppAll s r.1 := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have d1 := loadUnits_appAll h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact AppAll.trans d1 (loadUnits_appAll h2))
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact AppAllM.refl' _ _

theorem evalOp_appAll {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : AppAll s r.1 := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact AppAllM.refl' _ _ | exact fenceS_appAll _ _ | exact allocBuf_appAll _ _ _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact loadUnits_appAll hx
         | exact storeUnits_appAll _ _ _ _ _ hx
         | exact alloc_appAll hx
         | exact stepRmw_appAll (th := mth s _ _ _) hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact AppAll.trans (projM_appAll hx) (injM_appAll hy)
         | exact AppAll.trans (loadUnits_appAll hx) (storeUnits_appAll _ _ _ _ _ hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_appAll hx
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact AppAll.trans d1 (storeUnits_appAll _ _ _ _ _ hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       have d1 := loadUnits_appAll hx
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact d1)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_appAll _ _ _ _)

/-- **A thread step appends only at or below its new `vWr`** (and `vWr` grows). -/
theorem tstep_appAll {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) :
    AppAll (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact AppAllM.refl' _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨h1, -⟩ := enter_eq he
       show AppAllM mem th.vs mem th'.vs
       rw [h1]; exact AppAllM.refl' _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨h1, -⟩ := enter_eq he
       show AppAllM mem th.vs mem th'.vs
       rw [h1]; exact AppAllM.refl' _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_appAll hx
         | exact stepRmw_appAll (th := mth _ _ _ _) hx
         | exact stepRmwPair_appAll (th := mth _ _ _ _) hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact AppAll.trans (projM_appAll hx) (injM_appAll hy))
    | (simp only [List.mem_singleton] at h; subst h; exact fenceS_appAll _ .st)

/-- Every message a thread step appends is at most its new `vWr`. -/
theorem tstep_newLe {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) {t : Nat} (h1 : mem.size ≤ t)
    (h2 : t < r.1.size) : t ≤ r.2.2.vs.vWr := by
  obtain ⟨-, -, h3⟩ := tstep_appAll h
  have h4 : r.1.size ≤ r.2.2.vs.vWr + 1 :=
    h3 (show (stOf mem pairs th).mem.size < (stOf r.1 r.2.1 r.2.2).mem.size from Nat.lt_of_le_of_lt h1 h2)
  omega

/-! ## §2 `OwnCohInv`: the stepper's coherence at its private cells -/

/-- Offset `o` lies inside a cell of type `T` (the words of any `CellOK` value list:
their number depends on `T` only, `CellOK_len`). -/
def InCell (T : Ty) (o : Nat) : Prop := ∃ (E : TEnv) (n : Nat) (vals : List Word), CellOK E n T vals ∧ o < vals.length

/-- The number of words of a `CellOK` value list depends on the type only. -/
theorem CellOK_len {E E' : TEnv} {n n' : Nat} {T : Ty} {v0 v1 : List Word}
    (h0 : CellOK E n T v0) (h1 : CellOK E' n' T v1) : v0.length = v1.length := by
  rcases h0 with ⟨hw0, -⟩ | ⟨N, e, us, hT, hus, -, hl0, -⟩
  · rcases h1 with ⟨hw1, -⟩ | ⟨N, e, us, hT, -⟩
    · rw [hw0] at hw1; exact Option.some.inj hw1
    · rw [hT] at hw0; simp [wc, accs] at hw0
  · rcases h1 with ⟨hw1, -⟩ | ⟨N', e', us', hT', hus', -, hl1, -⟩
    · rw [hT] at hw1; simp [wc, accs] at hw1
    · rw [hT] at hT'
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨rfl, rfl⟩ := hT'
      rw [hus] at hus'; cases hus'
      rw [hl0, hl1]

theorem InCell.lt {T : Ty} {o : Nat} (h : InCell T o) {E : TEnv} {n : Nat} {vals : List Word}
    (hc : CellOK E n T vals) : o < vals.length := by
  obtain ⟨E0, n0, v0, h0, hl⟩ := h
  rw [← CellOK_len h0 hc]; exact hl

/-- (NEW clause) **At every own private cell, the thread's coherence is
at most its `vWr`**, at the offsets inside the cell.  One thread's view against its
own cells: no other thread's step or promise touches it. -/
def OwnCohInv (E : TEnv) (s : St) : Prop :=
  ∀ l c, E.sto l = some c → c.owner = some E.tid → E.pfr l = none → ∀ o, InCell c.ty o →
    s.vs.coh ⟨l, o⟩ ≤ s.vs.vWr

/-- **The core step lemma** (stage A, per memory event).  After a thread step with
footprint `E → E'` (`EFoot`) whose result has the owner's invariant at `E'`
(`OwnOKPF`), at every own cell of `E'` without a frontier before the step, the
stepper's coherence is at most its new `vWr`: the coherence message is no outstanding
promise (`LatestSF` at `E'`); if the step appended it, it is below `vWr`
(`tstep_newLe`); if it is old, it is at most the old coherence (`OwnCohInv`) or, past
it, an own promise (`LatestSF` at `pfr = none`, or `FreshLP` at a fresh label) that the
step discharged, so below `vWr` (`tstep_appUp`).  `E0` is the environment of the
pre-step `MemInv` (another cut of the same global environment). -/
theorem cohLe_core {g : G} {E E0 E' : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hm0 : MemInv g E0 (stOf mem pairs th)) (hs0 : E0.sto = E.sto) (hp0 : E0.pfr = E.pfr)
    (ht0 : E0.tid = E.tid) (hinv : OwnCohInv E (stOf mem pairs th))
    (hfoot : EFoot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hpost : OwnOKPF E' r.1 r.2.1 r.2.2.vs r.2.2.promises) :
    ∀ l cl, E'.sto l = some cl → cl.owner = some E'.tid → E.pfr l = none → ∀ o, InCell cl.ty o →
      r.2.2.vs.coh ⟨l, o⟩ ≤ r.2.2.vs.vWr := by
  intro l cl hsl ho hpn o hin
  obtain ⟨vals', hcv', hlat', -⟩ := hpost l cl hsl ho
  obtain ⟨⟨m, hm, hml, -⟩, hnp, -⟩ := hlat' o _ (List.getElem?_eq_getElem (hin.lt hcv'))
  obtain ⟨u1, u2, -, u4, -⟩ := tstep_appUp hr
  by_cases hnew : mem.size ≤ r.2.2.vs.coh ⟨l, o⟩
  · exact tstep_newLe hr hnew (TermLiveProps.lt_of_get hm)
  have hlt : r.2.2.vs.coh ⟨l, o⟩ < mem.size := Nat.lt_of_not_le hnew
  have hmo : mem[r.2.2.vs.coh ⟨l, o⟩]? = some m := by
    obtain ⟨m0, hm0'⟩ : ∃ m0, mem[r.2.2.vs.coh ⟨l, o⟩]? = some m0 := ⟨_, Array.getElem?_eq_getElem hlt⟩
    have h2 : r.1[r.2.2.vs.coh ⟨l, o⟩]? = some m0 := u2 _ _ hm0'
    rw [hm] at h2; cases h2; exact hm0'
  have key : r.2.2.vs.coh ⟨l, o⟩ ∈ th.promises ∨ r.2.2.vs.coh ⟨l, o⟩ ≤ th.vs.vWr := by
    rcases hfoot.2.2.1 l with e | ⟨⟨j, hj1, -, hlj⟩, -⟩
    · have hsE : E.sto l = some cl := by rw [← e]; exact hsl
      have hown0 : cl.owner = some E0.tid := by rw [ht0, ← hfoot.2.1]; exact ho
      obtain ⟨vals0, hcv0, hlat0, -⟩ := hm0.2.1 l cl (by rw [hs0]; exact hsE) hown0
      obtain ⟨-, -, hlater⟩ := hlat0 o _ (List.getElem?_eq_getElem (hin.lt hcv0))
      by_cases hle : r.2.2.vs.coh ⟨l, o⟩ ≤ th.vs.coh ⟨l, o⟩
      · exact Or.inr (Nat.le_trans hle (hinv l cl hsE (by rw [← hfoot.2.1]; exact ho) hpn o hin))
      · rcases hlater _ m (Nat.lt_of_not_le hle) hmo hml with h | ⟨hne, -⟩
        · exact Or.inl h
        · exact absurd (by rw [hp0]; exact hpn) hne
    · obtain ⟨-, hfr, -⟩ := hm0.2.2.2.1.1 j hj1
      exact Or.inl (hfr _ m hmo (by rw [hml]; exact hlj))
  rcases key with h | h
  · exact u4 _ h hnp
  · exact Nat.le_trans h u1

/-- **`OwnCohInv` after the stepper's own step** (the stepper's preservation of the
clause): an own cell of `E'` without a frontier had none before (`EFoot`). -/
theorem ownCohInv_step {g : G} {E E0 E' : TEnv} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep g mem pairs th)
    (hm0 : MemInv g E0 (stOf mem pairs th)) (hs0 : E0.sto = E.sto) (hp0 : E0.pfr = E.pfr)
    (ht0 : E0.tid = E.tid) (hinv : OwnCohInv E (stOf mem pairs th))
    (hfoot : EFoot g E E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2))
    (hpost : OwnOKPF E' r.1 r.2.1 r.2.2.vs r.2.2.promises) : OwnCohInv E' (stOf r.1 r.2.1 r.2.2) := by
  intro l c hsl ho hpn o hin
  have hpE : E.pfr l = none := by
    rcases hfoot.2.2.2.2.2.1 l with e | ⟨h, -⟩ | ⟨-, h, -⟩
    · rw [← e]; exact hpn
    · exact h
    · exact h
  exact cohLe_core hr hm0 hs0 hp0 ht0 hinv hfoot hpost l c hsl ho hpE o hin

/-! ## §3 The fields -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (named state fact; to become a `SysInvN` clause) `OwnCohInv` for the stepper at
its cut. -/
def OwnCohInvT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    OwnCohInv (CE η) (stOf c.mem c.pairs th)

/-- `TermInterf.OwnCohLeF` narrowed to the offsets inside the cell (the only use,
`pairStepper_holds`, is there).  The TermInterf patch makes `OwnCohLeF` this. -/
def OwnCohLeN (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ l, (CE η).pfr l = none → E'.pfr l ≠ none → ∀ cl vals, E'.sto l = some cl →
      CellOK E' (E'.rc l) cl.ty vals → ∀ o, o < vals.length → r.2.2.vs.coh ⟨l, o⟩ ≤ r.2.2.vs.vWr

/-- **N16 `ownCohLe`** (narrowed) from `OwnCohInvT`: a cell the step newly shares is an
own cell (`EFoot`: a publish or a plant; a new box is outside Σ), so `cohLe_core`. -/
theorem ownCohLe_of (hinv : OwnCohInvT p k arch Sp Init MintOK c0) : OwnCohLeN p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z l hp0 hfne cl vals
    hs' hcv o hlt
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hfoot := Z.1
  have hown : cl.owner = some E'.tid := by
    rcases hfoot.2.2.2.2.2.1 l with e | ⟨-, F, hF, -, -, ⟨c1, hc1, hown1⟩, -⟩ | ⟨-, -, hn⟩
    · rw [e] at hfne; exact absurd hp0 hfne
    · rw [hfoot.2.1]
      rcases hfoot.2.2.1 l with e2 | ⟨-, T, eT, -⟩
      · rw [e2, hc1] at hs'; cases hs'; exact hown1
      · rw [eT] at hs'; cases hs'; rfl
    · rw [hn] at hs'; cases hs'
  exact cohLe_core X.hr hm0 (by rw [Y.1]; rfl) (by rw [Y.1]; rfl) (by rw [Y.1]; rfl) (hinv X Y) hfoot
    Z.2.2.1.2.1 l cl hs' hown hp0 o ⟨E', _, vals, hcv, hlt⟩

/-- **`OwnCohInv` is kept by the stepper** (the thread-step half of the future
`SysInvN` clause), at the step's witness `E'`. -/
theorem ownCohInvT_step (hinv : OwnCohInvT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    OwnCohInv E' (stOf r.1 r.2.1 r.2.2) := by
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  exact ownCohInv_step X.hr hm0 (by rw [Y.1]; rfl) (by rw [Y.1]; rfl) (by rw [Y.1]; rfl) (hinv X Y) Z.1
    Z.2.2.1.2.1

/-- (future `SysInvN` clause, the other events) `OwnCohInv` is kept when the view is
unchanged, own cells stay own cells, and frontiers only appear: an idle thread under
another thread's step, and the promiser at a promise step (a plant sets `pfr`). -/
theorem OwnCohInv_mono {E E' : TEnv} {s s' : St} (h : OwnCohInv E s)
    (hs : ∀ l c, E'.sto l = some c → c.owner = some E'.tid → E.sto l = some c) (ht : E'.tid = E.tid)
    (hp : ∀ l, E'.pfr l = none → E.pfr l = none) (hv : s'.vs = s.vs) : OwnCohInv E' s' := by
  intro l c hsl ho hpn o hin
  rw [hv]
  exact h l c (hs l c hsl ho) (by rw [← ht]; exact ho) (hp l hpn) o hin

/-- (future `SysInvN` clause, initialisation) `OwnCohInv` holds at a view whose
coherence is `0` everywhere (the initial views). -/
theorem OwnCohInv_coh0 {E : TEnv} {s : St} (h : ∀ a, s.vs.coh a = 0) : OwnCohInv E s :=
  fun l _ _ _ _ o _ => by rw [h ⟨l, o⟩]; exact Nat.zero_le _

/-! ## §4 `wp` (T5): `FlipOK` at a publish's cell -/

/-- (named run fact, replaces `certRunT`) scope and `NoHoldPub` along every solo run
of the stepper from the PRE-step configuration of a thread step. -/
def CertRunC (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r →
    ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ c1, Solo p k arch i c c1 → Certified p k arch c1 i → ScopeAt p i c1 ∧ NoHoldPubA p k arch (Cut Eg i S) (Cut Eg i S) i c1

/-- `CertRunC` gives `TermPlantF.CertRunT`: a solo run from the successor, prefixed by
the step, is one from the source. -/
theorem certRunT_of (h : CertRunC p k arch Sp Init MintOK c0) : TermPlantF.CertRunT p k arch Sp Init MintOK c0 :=
  fun X S hS => ⟨(h X S hS _ (.refl _) (TermGlob.certified_back (.thread X.hc' (.refl _)) X.cert)).1,
    fun c1 hs hc => h X S hS c1 (.thread X.hc' hs) hc⟩

/-- `FlipOK` reads only `sto`, `tid`, `pfr` and `ini`. -/
theorem flipOK_congr {E E' : TEnv} {s : St} {l : AllocLabel} (hs : E'.sto = E.sto) (ht : E'.tid = E.tid)
    (hp : E'.pfr = E.pfr) (hi : E'.ini = E.ini) (h : FlipOK E s l) : FlipOK E' s l := by
  unfold FlipOK Priv OwnL WordUnit IniW at *
  rw [hs, ht, hp, hi]
  exact h

/-- **T5 `wp`** from `CertRunC`: `TermTyped.flipOK_cert` at the stepper's cut in
`SysInvN` (stage A, the PRE-step `MemInv`), certified through the step; `FlipOK` does
not read `seen`, so it transfers to the step's cut. -/
theorem wp_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [WrIniC] (hP : ProgT p) (hrun : CertRunC p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      ∀ x a e rt ws ad, th.term = .let_ x (.publish a) e → evalAt th.env a = some (rt, ws) →
        ws.map (·.val) = [.loc ad 0] → FlipOK (CE η) (stOf c.mem c.pairs th) ad.label := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y x a e rt ws ad _ _ _
  obtain ⟨S0, hS0⟩ := X.inv.thr i th X.hth
  obtain ⟨hRE0, hTE, hmi, -⟩ := id hS0
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, -⟩ := hRE0
  have hSC : StoClo (CE η2) := by rw [hce2]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hT2 : ThInvE p (CE η2) th := by rw [hce2]; exact hTE
  have hm2 : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hmi
  have hc : Certified p k arch c i := by
    obtain ⟨c'', hs, hn⟩ := X.cert
    exact ⟨c'', .thread X.hc' hs, hn⟩
  have h := flipOK_cert (l := ad.label) hP (fun c1 h1 h2 => (hrun X S0 hS0 c1 h1 h2).1) (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc')
    (fun c1 h1 h2 => by rw [hce2]; exact (hrun X S0 hS0 c1 h1 h2).2) X.hth hT2 hm2 hc hSC X.inv.bf hPS hSub hSig
    (by rw [hce2]; exact X.inv.riniCoh _ _ _ X.hth)
    (fun l cl f hs hp => by rw [hce2] at hs hp; exact X.inv.frlt l cl f (cutSto_sub hs) hp)
  refine flipOK_congr ?_ ?_ ?_ ?_ h <;> rw [Y.1, hce2] <;> rfl

/-! ## §5 `rmw` (T8): the slot form `NoPlantRMWS` -/

/-- (T8, slot form; replaces the label-wide `NoPlantRMW`) the target of a `cas`/`fetch`
at one of the thread's own cells lies in a slot below the real count (`IniWr`). -/
def NoPlantRMWS (E : TEnv) (th : TTh) : Prop :=
  ∀ w rt pw ad, ((∃ acq rel e v x ok fail, th.term = .cas acq rel w e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w v) e)) →
    evalAt th.env w = some (rt, [pw]) → addrOf pw = some ad → OwnL E ad.label → IniWr E ad

/-- (residual of `NoPlantRMWS`) the same, through a non-`own` reference that is either a
region reference (excluded by the scope at the stepper) or a `pub` one at a label whose
readers' count exceeds its real count (by `OwnHidP`, a planted, unseen label): typing gives
such a target only below `ini`. -/
def NoPlantRMWP (E : TEnv) (cx : Cx) (th : TTh) : Prop :=
  ∀ w rt pw ad tw μ u, ((∃ acq rel e v x ok fail, th.term = .cas acq rel w e v x ok fail) ∨
      (∃ x o acq rel v e, th.term = .let_ x (.fetch o acq rel w v) e)) →
    cx.peek w = .ok tw → cellOf tw = some (μ, u) → μ ≠ .own →
    (μ ≠ .pub ∨ E.rini ad.label < E.ini ad.label) →
    evalAt th.env w = some (rt, [pw]) → addrOf pw = some ad → OwnL E ad.label → IniWr E ad

/-- A one-word unit initialised below the real count lies in a slot below it. -/
theorem iniWr_of_iniAt {E : TEnv} {c : Cell} {ad : Address} {U : Ty} (hU : accs U = some [.one])
    (hsto : E.sto ad.label = some c) (hini : IniAt E.rc c ad U) : IniWr E ad := by
  intro c' N e us hs hty hus
  rw [hsto] at hs; cases hs
  rcases hini N e hty with ⟨hU', -⟩ | ⟨us', j, o, hus', hj, hoff, hato⟩
  · rw [hty] at hU'; rw [hU'] at hU; simp [accs] at hU
  · rw [hus] at hus'; cases hus'
    have hb := AtOff_bound hato hus hU
    have h1 : nWords [Acc.one] = 1 := rfl
    rw [h1] at hb
    have h2 : (j + 1) * nWords us ≤ E.rc ad.label * nWords us := Nat.mul_le_mul_right _ hj
    rw [Nat.succ_mul] at h2
    rw [← hoff]
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hb _) h2

theorem cellOf_cases {tw u : Ty} {μ : Mode} (hc : cellOf tw = some (μ, u)) : tw = .ptr μ u ∨ tw = .loc μ u := by
  cases tw <;> simp [cellOf] at hc <;> obtain ⟨rfl, rfl⟩ := hc <;> simp

theorem cellOf_wordOf {tw : Ty} {r : Idx} {P : Proto} (h : wordOf tw = some (r, P)) :
    ∃ μ, cellOf tw = some (μ, .word r P) := by
  unfold wordOf at h
  split at h
  · cases h; exact ⟨_, rfl⟩
  · cases h; exact ⟨_, rfl⟩
  · cases h

/-- **A one-word reference's target lies below the real count**: `own` by `cell_target` at
`modeIni .own = rc`; any other mode at `modeIni = ini`, which is the real count unless
`rini < ini` (left to `hres`, as is every region reference). -/
theorem refIniWr {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {w : At} {tw u : Ty} {μ : Mode} {rt : Ty} {pw : Word} {ad : Address}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hc : cellOf tw = some (μ, u))
    (hacc : accs (cl ρ η.wit 0 0 u) = some [.one])
    (hres : μ ≠ .own → (μ ≠ .pub ∨ η.rini ad.label < η.ini ad.label) → IniWr (CE η) ad)
    (hea : evalAt env w = some (rt, [pw])) (had : addrOf pw = some ad) : IniWr (CE η) ad := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hi.2.1 hpk
  obtain ⟨ad', c, hws, hsto, -, -, hini⟩ := cell_target hc (Fd_noarr (by rw [hacc]; simp)) hv
  rw [hea] at hea'; cases hea'
  have hpw : pw.val = .loc ad' 0 := by simpa using hws
  have had' : ad = ad' := by simp only [addrOf, hpw, Option.some.injEq] at had; exact had.symm
  subst had'
  by_cases hμ : μ = .own
  · subst hμ
    exact iniWr_of_iniAt (E := CE η) hacc hsto hini
  · by_cases hlt : μ ≠ .pub ∨ η.rini ad.label < η.ini ad.label
    · exact hres hμ hlt
    · have hpub : μ = .pub := Classical.byContradiction fun h => hlt (.inl h)
      have hge : ¬ η.rini ad.label < η.ini ad.label := fun h => hlt (.inr h)
      subst hpub
      refine iniWr_of_iniAt (E := CE η) hacc hsto ?_
      intro N e he
      rcases hini N e he with h | ⟨us, j, o, h1, h2, h3, h4⟩
      · exact .inl h
      · refine .inr ⟨us, j, o, h1, ?_, h3, h4⟩
        show j < min (η.ini ad.label) (η.rini ad.label)
        simp only [modeIni] at h2
        exact Nat.lt_min.2 ⟨h2, by omega⟩

/-- A protocol-word reference (`own`/`pub` need the word to be non-ghost). -/
theorem wordRef_iniWr {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {w : At} {tw : Ty} {r : Idx} {P : Proto} {rt : Ty} {pw : Word} {ad : Address}
    (hi : FInv ρ η σs K cx env) (hpk : cx.peek w = .ok tw) (hw : wordOf tw = some (r, P))
    (hg : ∀ μ, cellOf tw = some (μ, .word r P) → (μ = .own ∨ μ = .pub) → P.ghost = false)
    (hres : ∀ μ u, cellOf tw = some (μ, u) → μ ≠ .own → (μ ≠ .pub ∨ η.rini ad.label < η.ini ad.label) →
      IniWr (CE η) ad)
    (hea : evalAt env w = some (rt, [pw])) (had : addrOf pw = some ad) : IniWr (CE η) ad := by
  obtain ⟨μ, hc⟩ := cellOf_wordOf hw
  by_cases hpo : μ = .own ∨ μ = .pub
  · have hcl : cl ρ η.wit 0 0 (.word r P) = .word (.lit (ev ρ r)) P := by simp [cl, clI_zero]
    exact refIniWr hi hpk hc (by rw [hcl]; exact accs_word (hg μ hc hpo)) (hres μ _ hc) hea had
  · exact hres μ _ hc (fun h => hpo (.inl h)) (.inl fun h => hpo (.inr h))

/-- **`NoPlantRMWS` at a typed thread** from the residual `NoPlantRMWP` (stage A: the
`MemInv` only gives an epoch counter's `pwf`). -/
theorem rmwS_core {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {K : TEnv → Nat → List Word → Res → Prop} {Rf : Res}
    (hT : Typed p cx th.term) (hi : FInvR ρ η th.σs K cx th.env Rf) (hE : EnvOK p η) (htv : TvOK cx)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hres : NoPlantRMWP (CE η) cx th) :
    NoPlantRMWS (CE η) th := by
  intro w rt pw ad hcase hea had hown
  have hT0 := hT
  have hR : ∀ tw μ u, cx.peek w = .ok tw → cellOf tw = some (μ, u) → μ ≠ .own →
      (μ ≠ .pub ∨ η.rini ad.label < η.ini ad.label) → IniWr (CE η) ad :=
    fun tw μ u hp hc hμ hl => hres w rt pw ad tw μ u hcase hp hc hμ hl hea had hown
  have hEp : ∀ {tw : Ty} {r : Idx} {P : Proto}, cx.peek w = .ok tw → P.epoch = true →
      ∀ μ, cellOf tw = some (μ, .word r P) → (μ = .own ∨ μ = .pub) → P.ghost = false :=
    fun hp hep μ hc hpo => pwf_epoch_ghost (wordRef_pwf hp (cellOf_cases hc) hpo hi.1 hE htv hm) hep
  rcases hcase with ⟨acq, rel, e, v, x, ok, fail, hterm⟩ | ⟨x, o, acq, rel, v, e, hterm⟩
  · rw [hterm] at hT0
    cases hT0 with
    | casCell hp _ hc hraw =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact refIniWr hi.1 hp hc (accs_cl_one hraw) (hR _ _ _ hp hc) hea had
      · exact hR _ _ _ hp hc (fun h => by cases h) (.inl fun h => by cases h)
    | casShare hp hw hg =>
      exact wordRef_iniWr hi.1 hp hw (fun _ _ _ => hg) (fun μ u => hR _ μ u hp) hea had
    | casTake hp hw hg =>
      exact wordRef_iniWr hi.1 hp hw (fun _ _ _ => hg) (fun μ u => hR _ μ u hp) hea had
    | casEpoch hp hw hep =>
      exact wordRef_iniWr hi.1 hp hw (hEp hp hep) (fun μ u => hR _ μ u hp) hea had
  · rw [hterm] at hT0
    cases hT0 with
    | let_ hop _ =>
    cases hop with
    | fetchCell hp _ hc =>
      rcases hc with hc | ⟨r, hc, -⟩
      · exact refIniWr hi.1 hp hc (accs_cl_one (by rfl)) (hR _ _ _ hp hc) hea had
      · exact hR _ _ _ hp hc (fun h => by cases h) (.inl fun h => by cases h)
    | fetchEpoch hp hw hep =>
      exact wordRef_iniWr hi.1 hp hw (hEp hp hep) (fun μ u => hR _ μ u hp) hea had
    | fetchShare hp hw hep hj heq hok =>
      refine wordRef_iniWr hi.1 hp hw (fun _ _ _ => ?_) (fun μ u => hR _ μ u hp) hea had
      have hok' := hok
      unfold fetchOK at hok'; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok'
      exact hok'.1.1.1.1

/-- `NoPlantRMWS` reads only `sto`, `tid`, `ini` and `rini`. -/
theorem noPlantRMWS_congr {E E' : TEnv} {th : TTh} (hs : E'.sto = E.sto) (ht : E'.tid = E.tid)
    (hi : E'.ini = E.ini) (hr : E'.rini = E.rini) (h : NoPlantRMWS E th) : NoPlantRMWS E' th := by
  unfold NoPlantRMWS OwnL IniWr TermSound.TEnv.rc at *
  rw [hs, ht, hi, hr]
  exact h

/-- (named run fact, the residual of T8) `NoPlantRMWP` at a thread step's environment. -/
def RmwPubF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    NoPlantRMWP (CE η) cx th

/-- **T8 `rmw`, slot form**, from the residual `RmwPubF`: at the stepper's cut in `SysInvN`
(stage A, the PRE-step `MemInv`), transferred to the step's cut. -/
theorem rmwS_of (hres : RmwPubF p k arch Sp Init MintOK c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      NoPlantRMWS (CE η) th := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hE2, hT2, htv2, hi2, hsum2, -⟩ := hRE0
  have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
    ⟨hce2, congrArg (fun E => E.tid) hce2, hE2, hT2, htv2, hi2, hsum2⟩
  have h2 := rmwS_core hT2.1 hi2 hE2 htv2 (by rw [hce2]; exact hm0) (hres X Y2)
  refine noPlantRMWS_congr ?_ ?_ ?_ ?_ h2 <;> rw [Y.1, hce2] <;> rfl

end

end TermCohLe

#print axioms TermCohLe.tstep_appAll
#print axioms TermCohLe.tstep_newLe
#print axioms TermCohLe.CellOK_len
#print axioms TermCohLe.cohLe_core
#print axioms TermCohLe.ownCohInv_step
#print axioms TermCohLe.ownCohLe_of
#print axioms TermCohLe.ownCohInvT_step
#print axioms TermCohLe.OwnCohInv_mono
#print axioms TermCohLe.OwnCohInv_coh0
#print axioms TermCohLe.certRunT_of
#print axioms TermCohLe.flipOK_congr
#print axioms TermCohLe.wp_of
#print axioms TermCohLe.iniWr_of_iniAt
#print axioms TermCohLe.refIniWr
#print axioms TermCohLe.wordRef_iniWr
#print axioms TermCohLe.rmwS_core
#print axioms TermCohLe.noPlantRMWS_congr
#print axioms TermCohLe.rmwS_of

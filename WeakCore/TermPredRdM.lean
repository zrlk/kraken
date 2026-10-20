import WeakCore.TermReadCls

/-! # TermPredRdM: a read's message is not hidden below its pointer's view

A read at `b` through a pointer word `pw` (dependency register `0`, `mth s pw _ _`) chooses a
message `readable` under a bound at least `pw.view` (`depBound`), so no message at `b` lies in
`(K′, pw.view]` (`RdV`), `K′` the coherence the read raises `b` to.  `tstep_rdv` for the pointer
reads `load`, `ldp`, `fetch`, `cas`, `casp`.
-/

namespace TermPredRdM

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- No message at `b` in `(K, v]`. -/
def RdV (mem : Memory) (b : Address) (K v : Ts) : Prop :=
  (∃ m, mem[K]? = some m ∧ m.loc = b) ∧ ∀ (t : Ts) (m : Msg), K < t → t ≤ v → mem[t]? = some m → m.loc ≠ b

theorem readable_rdv {mem : Memory} {a : Address} {t bound v : Ts}
    (h : WeakMem.readable mem a t bound = true) (hv : v ≤ bound) : RdV mem a t v := by
  refine ⟨TermLiveProps.loc_of_readable h, ?_⟩
  intro t' m h1 h2 hm hl
  rw [Promises.not_readable_of_later h1 (Nat.le_trans h2 hv) hm hl] at h
  cases h

theorem max_rise {x t : Nat} (h : x < max x t) : max x t = t := by
  rw [Nat.max_def] at h ⊢
  split
  · rfl
  · rename_i hn; rw [ite_eq_right hn] at h; exact absurd h (Nat.lt_irrefl _)

theorem view_le_bound (arch : Arch) (vs : VState) (pw x y : Word) (a : Address) :
    pw.view ≤ Promises.readBoundOf arch vs (Promises.depBound (regsOf pw x y) [0]) a := by
  have h1 : pw.view ≤ Promises.depView (regsOf pw x y) [0] := by
    simp [Promises.depView, regsOf]
  have h2 : Promises.depView (regsOf pw x y) [0] ≤ Promises.depBound (regsOf pw x y) [0] :=
    Nat.le_max_left _ _
  unfold Promises.readBoundOf
  refine Nat.le_trans (Nat.le_trans h1 h2) ?_
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_right _ _

theorem stepLoad_rd {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {dst : WeakMem.Reg} {a : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoad arch mem pairs th dst a deps acq) (hc : th.vs.coh a < th'.vs.coh a) :
    WeakMem.readable mem a (th'.vs.coh a) (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) a)
      = true := by
  simp only [Promises.stepLoad, List.mem_map, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨-, hr⟩, rfl⟩ := h
  simp only [ite_true] at hc ⊢
  rw [max_rise hc]; exact hr

theorem stepLoadPair_rd {arch : Arch} {mem : Memory} {pairs : List Ts} {th th' : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a b : Address} {deps : List WeakMem.Reg} {acq : Bool}
    (h : th' ∈ Promises.stepLoadPair arch mem pairs th d0 d1 a deps acq) (hb : b = a ∨ b = a.next)
    (hc : th.vs.coh b < th'.vs.coh b) :
    WeakMem.readable mem b (th'.vs.coh b) (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) b)
      = true := by
  simp only [Promises.stepLoadPair, List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_range] at h
  obtain ⟨t0, ⟨-, hr0⟩, t1, ⟨-, hr1⟩, hbody⟩ := h
  split at hbody
  · cases hbody
  · cases hbody
    have hne : a ≠ a.next := by
      intro e; have := congrArg Address.offset e; simp [WeakMem.Address.next] at this
    rcases hb with rfl | rfl
    · simp only [ite_true] at hc ⊢
      rw [max_rise hc]; exact hr0
    · simp only [ite_eq_right (Ne.symm hne), ite_true] at hc ⊢
      rw [max_rise hc]; exact hr1

#print axioms stepLoadPair_rd

/-- The leading lock fence of an RMW only raises the read bound. -/
theorem readBound_lock (arch : Arch) (th : Promises.Thread) (d : Ts) (a : Address) :
    Promises.readBoundOf arch th.vs d a ≤
      Promises.readBoundOf arch (if arch = .tso then Promises.stepFence th .sy else th).vs d a := by
  have mm : ∀ {x x' y y' : Nat}, x ≤ x' → y ≤ y' → max x y ≤ max x' y' := fun h1 h2 =>
    Nat.max_le.2 ⟨Nat.le_trans h1 (Nat.le_max_left _ _), Nat.le_trans h2 (Nat.le_max_right _ _)⟩
  split
  · exact mm (mm (mm (Nat.le_max_left _ _) (Nat.le_refl _)) (Nat.le_refl _)) (Nat.le_refl _)
  · exact Nat.le_refl _

theorem stepRmw_rd_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a cmp newv deps acq rel)
    (hc : th.vs.coh a < th'.vs.coh a) (h2 : th'.vs.coh a < mem.size) (h3 : th'.vs.coh a ∉ th.promises) :
    WeakMem.readable mem a (th'.vs.coh a) (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) a)
      = true := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t, ⟨-, hr⟩, hbody⟩ := h
  split at hbody
  · rw [List.mem_singleton] at hbody
    cases hbody
    rw [TermLiveProps.ite_fence_coh] at hc ⊢
    simp only [ite_true] at hc ⊢
    rw [max_rise hc]; exact hr
  · rw [List.mem_append] at hbody
    rcases hbody with happ | hful
    · split at happ
      · rw [List.mem_singleton] at happ
        cases happ
        rw [TermLiveProps.ite_fence_coh] at h2
        simp at h2
      · simp at happ
    · obtain ⟨tw, htw, hft⟩ := List.mem_filterMap.1 hful
      split at hft
      · cases hft
      · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
        obtain ⟨-, hft⟩ := hft
        cases hft
        rw [TermLiveProps.ite_fence_coh] at h3
        simp at h3
        exact absurd htw h3

theorem stepRmw_rd {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a cmp newv deps acq rel)
    (hc : th.vs.coh a < th'.vs.coh a) (h2 : th'.vs.coh a < mem.size) (h3 : th'.vs.coh a ∉ th.promises) :
    WeakMem.readable mem a (th'.vs.coh a) (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) a)
      = true := by
  have hx := stepRmw_rd_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [lockTh_coh]; exact hc) h2 (by rw [lockTh_prom]; exact h3)
  rw [lockTh_regs] at hx
  exact Promises.readable_antitone (readBound_lock arch th _ a) hx

#print axioms stepRmw_rd

theorem stepRmwPair_rd_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a b : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) (hb : b = a ∨ b = a.next)
    (hc : th.vs.coh b < th'.vs.coh b) (h2 : th'.vs.coh b < mem.size) (h3 : th'.vs.coh b ∉ th.promises) :
    WeakMem.readable mem b (th'.vs.coh b) (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) b)
      = true := by
  have hne : a ≠ a.next := by
    intro e; have := congrArg Address.offset e; simp [WeakMem.Address.next] at this
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, ⟨-, hr0⟩, t1, ⟨-, hr1⟩, hbody⟩ := h
  split at hbody
  · simp at hbody
  · split at hbody
    · rw [List.mem_singleton] at hbody
      cases hbody
      rw [TermLiveProps.ite_fence_coh] at hc ⊢
      rcases hb with rfl | rfl
      · simp only [ite_true] at hc ⊢
        rw [max_rise hc]; exact hr0
      · simp only [ite_eq_right (Ne.symm hne), ite_true] at hc ⊢
        rw [max_rise hc]; exact hr1
    · rw [List.mem_append] at hbody
      rcases hbody with happ | hful
      · split at happ
        · rw [List.mem_singleton] at happ
          cases happ
          rw [TermLiveProps.ite_fence_coh] at h2
          rcases hb with rfl | rfl
          · simp at h2
          · simp only [ite_eq_right (Ne.symm hne), ite_true] at h2
            exact absurd (Nat.lt_of_le_of_lt (Nat.le_succ _) h2) (Nat.lt_irrefl _)
        · simp at happ
      · obtain ⟨tw, htw, hft⟩ := List.mem_filterMap.1 hful
        split at hft
        · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
          obtain ⟨hcond, hft⟩ := hft
          cases hft
          rw [TermLiveProps.ite_fence_coh] at h3
          rcases hb with rfl | rfl
          · simp at h3
            exact absurd htw h3
          · simp [ite_eq_right (Ne.symm hne)] at h3
            simp only [Bool.and_eq_true, List.contains_iff_mem] at hcond
            exact absurd hcond.1.1.1.1.1.1.1.1.1.2 h3
        · cases hft

theorem stepRmwPair_rd {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a b : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) (hb : b = a ∨ b = a.next)
    (hc : th.vs.coh b < th'.vs.coh b) (h2 : th'.vs.coh b < mem.size) (h3 : th'.vs.coh b ∉ th.promises) :
    WeakMem.readable mem b (th'.vs.coh b) (Promises.readBoundOf arch th.vs (Promises.depBound th.regs deps) b)
      = true := by
  have hx := stepRmwPair_rd_at (th := if arch = .tso then Promises.stepFence th .sy else th) h hb (by rw [lockTh_coh]; exact hc) h2 (by rw [lockTh_prom]; exact h3)
  rw [lockTh_regs] at hx
  exact Promises.readable_antitone (readBound_lock arch th _ b) hx

#print axioms stepRmwPair_rd

theorem offs_ne {a : Address} {k j : Nat} (h : 0 < j) : offs a (k + j) ≠ offs a k := by
  intro e; have := congrArg Address.offset e; simp [offs] at this; omega

/-- **`loadUnits`**: a rise at `b` is a read under `pw.view`. -/
theorem loadUnits_rdv {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      ∀ b, s.vs.coh b < r.1.vs.coh b → RdV s.mem b (r.1.vs.coh b) pw.view
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr
      intro b hc; exact absurd hc (Nat.lt_irrefl _)
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      intro b hc
      by_cases hb : b = offs a k
      · have e := TermUnitKeepC.loadUnits_cohOff us (k + 1)
          { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] } (s', ws) hmem b
          (fun j _ e => by
            rw [hb, show k + 1 + j = k + (j + 1) by omega] at e
            exact offs_ne (Nat.succ_pos j) e.symm)
        simp only at hc e ⊢
        rw [e] at hc ⊢
        subst hb
        exact readable_rdv (stepLoad_rd hth hc) (view_le_bound _ _ _ _ _ _)
      · have e1 : th.vs.coh b = s.vs.coh b := stepLoad_cohOther hth b hb
        have := loadUnits_rdv us (k + 1)
          { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1] } (s', ws) hmem b
          (by simp only at hc ⊢; rw [e1]; exact hc)
        exact this
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, hth, ⟨s', ws⟩, hmem, rfl⟩ := hr
      intro b hc
      by_cases hb : b = offs a k ∨ b = (offs a k).next
      · have e := TermUnitKeepC.loadUnits_cohOff us (k + 2)
          { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } (s', ws) hmem b
          (fun j _ e => by
            rcases hb with hb | hb
            · rw [hb, show k + 2 + j = k + (j + 2) by omega] at e
              exact offs_ne (by omega) e.symm
            · rw [hb] at e
              have h5 : (offs a k).next.offset = (offs a (k + 2 + j)).offset := congrArg Address.offset e
              have h6 : (offs a k).next.offset = a.offset + k + 1 := rfl
              have h7 : (offs a (k + 2 + j)).offset = a.offset + (k + 2 + j) := rfl
              rw [h6, h7, Nat.add_assoc] at h5
              have h8 : k + 1 = k + 2 + j := Nat.add_left_cancel h5
              omega)
        simp only at hc e ⊢
        rw [e] at hc ⊢
        exact readable_rdv (stepLoadPair_rd hth hb hc) (view_le_bound _ _ _ _ _ _)
      · have e1 : th.vs.coh b = s.vs.coh b :=
          stepLoadPair_cohOther hth b (fun h => hb (.inl h)) (fun h => hb (.inr h))
        exact loadUnits_rdv us (k + 2)
          { s with vs := th.vs, undefs := s.undefs + countUndef [th.regs 1, th.regs 2] } (s', ws) hmem b
          (by simp only at hc ⊢; rw [e1]; exact hc)

#print axioms loadUnits_rdv

/-- The pointer-read terms, reading through `a`. -/
def PtrTerm (e : Expr) (a : At) : Prop :=
  (∃ x acq e', e = .let_ x (.load acq a) e') ∨ (∃ x acq n0 n1 e', e = .let_ x (.ldp acq a n0 n1) e') ∨
  (∃ x o acq rel v e', e = .let_ x (.fetch o acq rel a v) e') ∨
  (∃ acq rel e0 v tn ok fail, e = .cas acq rel a e0 v tn ok fail) ∨
  (∃ acq rel e0 e1 v0 v1 tn ok fail, e = .casp acq rel a e0 e1 v0 v1 tn ok fail)

theorem fetch_ev {g : G} {env : Env} {σs : List Ty} {s : St} {o : FetchOp} {acq rel : Bool} {a v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) :
    ∃ t' pw' nw b0 mem' th', evalAt env a = some (t', [pw']) ∧
      (mem', th') ∈ Promises.stepRmw g.k g.arch s.mem s.pairs (mth s pw' nw nw) 1 b0 o.kind (dataE 1 nw)
        [0] acq rel ∧ r.1.vs = th'.vs := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨⟨mem', th'⟩, hst, rfl⟩ := List.mem_map.1 h
       exact ⟨_, _, _, _, _, _, by assumption, hst, rfl⟩)

theorem fetch_rdv {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {a : At} {t : Ty} {pw : Word} {b : Address} {x : String} {o : FetchOp} {acq rel : Bool} {v : At} {e' : Expr}
    (h : r ∈ tstep g mem pairs th) (hterm : th.term = .let_ x (.fetch o acq rel a v) e')
    (hea : evalAt th.env a = some (t, [pw]))
    (h1 : th.vs.coh b < r.2.2.vs.coh b) (h2 : r.2.2.vs.coh b < mem.size) (h3 : r.2.2.vs.coh b ∉ th.promises) :
    RdV mem b (r.2.2.vs.coh b) pw.view := by
  rw [TermLocal.tstep_let_gen hterm rfl] at h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
  obtain ⟨t', pw', nw, b0, mem', th', hea', hst, hvs⟩ := fetch_ev hy
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
  obtain ⟨-, rfl⟩ := hea'
  have hvs' : (withS { th with term := e', env := (x, y.2.1, y.2.2) :: th.env } y.1).vs = th'.vs := hvs
  rw [hvs'] at h1 h2 h3 ⊢
  have e := TermReadClsM.stepRmw_rise hst h1
  subst e
  exact readable_rdv (stepRmw_rd hst h1 h2 h3) (view_le_bound _ _ _ _ _ _)

#print axioms fetch_rdv

theorem cas_ev {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {acq rel : Bool} {w e0 v : At} {tn : String} {ok fail : Expr}
    (h : r ∈ tstep g mem pairs th) (hterm : th.term = .cas acq rel w e0 v tn ok fail) :
    ∃ t' pw' x y b0 kind newv mem' th', evalAt th.env w = some (t', [pw']) ∧
      (mem', th') ∈ Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw' x y) 1 b0 kind newv
        [0] acq rel ∧ r.2.2.vs = th'.vs := by
  unfold tstep at h
  rw [hterm] at h
  simp only at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨⟨mem', th'⟩, hst, rfl⟩ := List.mem_map.1 h
       exact ⟨_, _, _, _, _, _, _, _, _, by assumption, hst, by dsimp only; split <;> rfl⟩)

theorem casp_ev {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {acq rel : Bool} {w e0 e1 v0 v1 : At} {tn : String} {ok fail : Expr}
    (h : r ∈ tstep g mem pairs th) (hterm : th.term = .casp acq rel w e0 e1 v0 v1 tn ok fail) :
    ∃ t' pw' x y b0 c0 c1 m0 m1 mem' pairs' th', evalAt th.env w = some (t', [pw']) ∧
      (mem', pairs', th') ∈ Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw' x y) 1 2 b0
        c0 c1 m0 m1 [0] acq rel ∧ r.2.2.vs = th'.vs := by
  unfold tstep at h
  rw [hterm] at h
  simp only at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (obtain ⟨⟨mem', pairs', th'⟩, hst, rfl⟩ := List.mem_map.1 h
       exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, by assumption, hst, by dsimp only; split <;> rfl⟩)

#print axioms cas_ev
#print axioms casp_ev

/-- **A pointer read's message is not hidden below the pointer's view.** -/
theorem tstep_rdv {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {a : At} {t : Ty} {pw : Word} {b : Address}
    (h : r ∈ tstep g mem pairs th) (hpt : PtrTerm th.term a) (hea : evalAt th.env a = some (t, [pw]))
    (h1 : th.vs.coh b < r.2.2.vs.coh b) (h2 : r.2.2.vs.coh b < mem.size) (h3 : r.2.2.vs.coh b ∉ th.promises) :
    RdV mem b (r.2.2.vs.coh b) pw.view := by
  rcases hpt with ⟨x, acq, e', hterm⟩ | ⟨x, acq, n0, n1, e', hterm⟩ | ⟨x, o, acq, rel, v, e', hterm⟩ |
      ⟨acq, rel, e0, v, tn, ok, fail, hterm⟩ | ⟨acq, rel, e0, e1, v0, v1, tn, ok, fail, hterm⟩
  · rw [TermLocal.tstep_let_gen hterm rfl] at h
    obtain ⟨⟨s', ty, ws⟩, hy, rfl⟩ := List.mem_map.1 h
    simp only [evalOp, hea] at hy
    split at hy
    · split at hy
      · obtain ⟨⟨s2, ws2⟩, hx, he⟩ := List.mem_map.1 hy
        cases he
        exact loadUnits_rdv _ 0 _ _ hx b h1
      · simp at hy
    · simp at hy
  · rw [TermLocal.tstep_let_gen hterm rfl] at h
    obtain ⟨⟨s', ty, ws⟩, hy, rfl⟩ := List.mem_map.1 h
    simp only [evalOp, hea] at hy
    split at hy
    · split at hy
      · obtain ⟨⟨s2, ws2⟩, hx, he⟩ := List.mem_map.1 hy
        cases he
        exact loadUnits_rdv _ 0 _ _ hx b h1
      · simp at hy
    · simp at hy
  · exact fetch_rdv h hterm hea h1 h2 h3
  · obtain ⟨t', pw', x0, y0, b0, kd, nv, mem', th', hea', hst, hvs⟩ := cas_ev h hterm
    rw [hea] at hea'
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
    obtain ⟨-, rfl⟩ := hea'
    rw [hvs] at h1 h2 h3 ⊢
    have e := TermReadClsM.stepRmw_rise hst h1
    subst e
    exact readable_rdv (stepRmw_rd hst h1 h2 h3) (view_le_bound _ _ _ _ _ _)
  · obtain ⟨t', pw', x0, y0, b0, q0, q1, m0, m1, mem', pairs', th', hea', hst, hvs⟩ := casp_ev h hterm
    rw [hea] at hea'
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea'
    obtain ⟨-, rfl⟩ := hea'
    rw [hvs] at h1 h2 h3 ⊢
    have e := TermReadClsM.stepRmwPair_rise hst h1
    exact readable_rdv (stepRmwPair_rd hst e h1 h2 h3) (view_le_bound _ _ _ _ _ _)

#print axioms tstep_rdv

end TermPredRdM

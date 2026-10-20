import WeakCore.TermPlant
import WeakCore.TermK5P
import WeakCore.TermB5

/-! # TermFootNC ((X) FootNC): `FootNCE` on the step's witness

`FootNCE E E' r` (verbatim): the pair stores of a step result at labels new
to `E'.sto` start two-word units of their cells (NC), and a message off the result's promises at the
second word of a two-word unit of a label new to `E'.sto` holds no pointer or is a pair store's
second half (NC4).

* Generic: a step whose allocation count is unchanged keeps `E.sto` (`EFoot`'s fresh disjunct is
  empty), so `FootNCE` is vacuous (`footNC_efoot`); `tstep_nalloc` gives the unchanged count off the
  allocating terms (`AllocT`: `new`, `newBuf`, `inl`, `inr`, `case`).
-/

namespace TermFootNC
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (staging) **NC ∧ NC4** at one step result. -/
def FootNCE (E E' : TEnv) (r : Memory × List Ts × TTh) : Prop :=
  (∀ q ∈ r.2.1, ∀ (m0 : Msg) (cl : Cell), r.1[q]? = some m0 → E'.sto m0.loc.label = some cl →
    E.sto m0.loc.label = none → TwoAtT cl.ty m0.loc.offset) ∧
  ∀ (v : Nat) (mv : Msg) (cl : Cell) (o : Nat), r.1[v]? = some mv → v ∉ r.2.2.promises →
    E'.sto mv.loc.label = some cl → E.sto mv.loc.label = none → mv.loc.offset = o + 1 →
    TwoAtT cl.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ r.2.1, v = q + 1

/-- `FootNCE` at a witness keeping `E.sto`. -/
theorem footNC_sto {E E' : TEnv} {r : Memory × List Ts × TTh} (h : ∀ l, E'.sto l = E.sto l) :
    FootNCE E E' r :=
  ⟨fun _ _ m0 _ _ h1 h2 => (by rw [h, h2] at h1; cases h1),
   fun _ mv _ _ _ _ h1 h2 => (by rw [h, h2] at h1; cases h1)⟩

/-- `FootNCE` at a footprint taking no fresh label. -/
theorem footNC_efoot {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} {r : Memory × List Ts × TTh}
    (hF : EFootB W g E E' s s') (hn : s'.nalloc ≤ s.nalloc) : FootNCE E E' r :=
  footNC_sto fun l => (hF.2.2.1 l).elim id fun ⟨⟨_, h1, h2, _⟩, _⟩ => absurd (Nat.lt_of_lt_of_le h2 hn)
    (Nat.not_lt.2 h1)

/-! ## The allocating terms, and the allocation count off them -/

/-- The ops that may allocate: `new`, `newBuf`, and the (re-)boxing injections. -/
def AllocOp : Op → Prop
  | .new _ => True
  | .newBuf _ _ => True
  | .inl _ _ => True
  | .inr _ _ => True
  | _ => False

/-- The terms whose step may allocate: an allocating op, or a `case` (which re-injects). -/
def AllocT : Expr → Prop
  | .let_ _ op _ => AllocOp op
  | .case _ _ _ _ _ => True
  | _ => False

theorem fenceS_nalloc (s : St) (f : WeakMem.Fence) : (fenceS s f).nalloc = s.nalloc := rfl

theorem ls_nal {arch arch' : Arch} {kn : Promises.Knobs} {pw pw' : Word} {a a' : Address} {acq rel : Bool}
    {us us' : List Acc} {k i : Nat} {s s1 s2 : St} {ws ws' : List Word}
    (h1 : (s1, ws) ∈ loadUnits arch pw a acq us k s) (h2 : s2 ∈ storeUnits kn arch' pw' a' rel us' ws' i s1) :
    s2.nalloc = s.nalloc :=
  (TermTyped.storeUnits_nallocT _ _ _ _ _ h2).trans (TermStepper.loadUnits_nalloc _ _ _ _ h1)

macro "close_nal" : tactic => `(tactic| first
    | done
    | rfl
    | exact TermStepper.loadUnits_nalloc _ _ _ _ (by assumption)
    | exact TermTyped.storeUnits_nallocT _ _ _ _ _ (by assumption)
    | exact ls_nal (by assumption) (by assumption)
    | exact (TermStepper.loadUnits_nalloc _ _ _ _ (by assumption)).trans (TermStepper.loadUnits_nalloc _ _ _ _ (by assumption)))

macro "crushN1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flat)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try close_nal)))

theorem evalOp_nalloc (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) (hA : ¬ AllocOp op) :
    ∀ r ∈ evalOp g env σs s op, r.1.nalloc = s.nalloc := by
  cases op <;> simp only [AllocOp, not_true_eq_false] at hA <;> simp only [evalOp]
  all_goals (
    intro r hin
    revert hin
    crushN1
    all_goals (try (rename_i hh; revert hh; crushN1))
    all_goals (try (rename_i hh; revert hh; crushN1)))

/-- **The allocation count off the allocating terms**: a step at a term that is not `AllocT`
keeps the thread's allocation count. -/
theorem tstep_nalloc {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} (hA : ¬ AllocT th.term) :
    ∀ r ∈ tstep g mem pairs th, r.2.2.nalloc = th.nalloc := by
  intro r h
  simp only [tstep] at h
  split at h <;> rename_i hT <;> rw [hT] at hA <;> simp only [AllocT] at hA
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (exact absurd trivial hA)
    | (simp only [List.mem_singleton] at h; subst h; rfl)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', h1, rfl⟩ := h
       first
         | exact (TermTyped.enter_nallocT h1).2
         | (obtain ⟨fr, -, hen⟩ := h1; exact (TermTyped.enter_nallocT hen).2))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_nalloc _ _ _ _ _ hA x hx
         | rfl)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       rfl)

/-! ## `new`: the allocated label's pair stores and second words -/

/-- (`new`) The allocated label `lbl` at type `T`, at a fixed promise set `P`: pair stores in bounds;
those at `lbl` start two-word units of `T`; a message off `P` at `lbl` at the second word of a
two-word unit of `T` holds no pointer or is a pair store's second half. -/
def LocNC (lbl : AllocLabel) (T : Ty) (mem : Memory) (pairs P : List Ts) : Prop :=
  (∀ q ∈ pairs, q + 1 < mem.size) ∧
  (∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc.label = lbl → TwoAtT T m0.loc.offset) ∧
  ∀ (v : Nat) (mv : Msg) (o : Nat), mem[v]? = some mv → v ∉ P → mv.loc.label = lbl → mv.loc.offset = o + 1 →
    TwoAtT T o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1

theorem getP {mem : Memory} {m : Msg} {t : Nat} :
    (mem.push m)[t]? = if t = mem.size then some m else mem[t]? := Array.getElem?_push

theorem getP_lt {mem : Memory} {m : Msg} {t : Nat} (h : t < mem.size) : (mem.push m)[t]? = mem[t]? := by
  rw [getP, ite_eq_right_iff.2 (fun h' => absurd h' (Nat.ne_of_lt h))]

theorem locNC_push {lbl : AllocLabel} {T : Ty} {mem : Memory} {pairs P : List Ts} {m : Msg}
    (h : LocNC lbl T mem pairs P)
    (hm : m.loc.label = lbl → ∀ o, m.loc.offset = o + 1 → TwoAtT T o → ∀ a g, m.val ≠ .loc a g) :
    LocNC lbl T (mem.push m) pairs P := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun q hq => ?_, fun q hq m0 h0 hl => ?_, fun v mv o hv hP hl ho hT => ?_⟩
  · exact Nat.lt_of_lt_of_le (h1 q hq) (by simp)
  · rw [getP_lt (Nat.lt_of_succ_lt (h1 q hq))] at h0; exact h2 q hq m0 h0 hl
  · rw [getP] at hv
    split at hv
    · cases hv; exact Or.inl (hm hl o ho hT)
    · exact h3 v mv o hv hP hl ho hT

theorem locNC_pushPair {lbl : AllocLabel} {T : Ty} {mem : Memory} {pairs P : List Ts} {m0 m1 : Msg}
    (h : LocNC lbl T mem pairs P)
    (h0 : m0.loc.label = lbl → TwoAtT T m0.loc.offset ∧ ∀ o, m0.loc.offset = o + 1 → ¬ TwoAtT T o) :
    LocNC lbl T ((mem.push m0).push m1) (pairs ++ [mem.size]) P := by
  obtain ⟨h1, h2, h3⟩ := h
  have hsz : ((mem.push m0).push m1).size = mem.size + 2 := by simp
  refine ⟨fun q hq => ?_, fun q hq m h0' hl => ?_, fun v mv o hv hP hl ho hT => ?_⟩
  · rw [hsz]
    rcases List.mem_append.1 hq with hq | hq
    · exact Nat.lt_of_lt_of_le (h1 q hq) (Nat.le_add_right _ _)
    · rw [List.mem_singleton] at hq; rw [hq]; exact Nat.lt_succ_self _
  · rcases List.mem_append.1 hq with hq | hq
    · have hq1 := h1 q hq
      rw [getP_lt (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hq1) (by simp)), getP_lt (Nat.lt_of_succ_lt hq1)] at h0'
      exact h2 q hq m h0' hl
    · rw [List.mem_singleton] at hq; subst hq
      rw [getP_lt (by simp), getP] at h0'
      simp only [ite_true] at h0'
      cases h0'; exact (h0 hl).1
  · rw [getP, getP] at hv
    simp only [Array.size_push] at hv
    split at hv
    · cases hv
      exact Or.inr ⟨mem.size, List.mem_append_right _ (List.mem_singleton_self _), by assumption⟩
    · split at hv
      · cases hv; exact absurd hT ((h0 hl).2 o ho)
      · rcases h3 v mv o hv hP hl ho hT with h4 | ⟨q, hq, e⟩
        · exact Or.inl h4
        · exact Or.inr ⟨q, List.mem_append_left _ hq, e⟩

theorem locNC_erase {lbl : AllocLabel} {T : Ty} {mem : Memory} {pairs P : List Ts} {t : Nat} {m : Msg}
    (h : LocNC lbl T mem pairs P) (ht : mem[t]? = some m)
    (hm : m.loc.label = lbl → ∀ o, m.loc.offset = o + 1 → ¬ TwoAtT T o) :
    LocNC lbl T mem pairs (P.erase t) := by
  refine ⟨h.1, h.2.1, fun v mv o hv hP hl ho hT => ?_⟩
  by_cases hvP : v ∈ P
  · by_cases e : v = t
    · subst e; rw [ht] at hv; cases hv; exact absurd hT (hm hl o ho)
    · exact absurd ((List.mem_erase_of_ne e).2 hvP) hP
  · exact h.2.2 v mv o hv hvP hl ho hT

/-- `stepStore`'s two outcomes, with the promise set: appended, or a promise at the address
fulfilled (and erased). -/
theorem stepStore_casesP {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {th th' : Promises.Thread}
    {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    (∃ m : Msg, mem' = mem.push m ∧ m.loc = a ∧ m.val = exprVal th e ∧ th'.promises = th.promises) ∨
    (mem' = mem ∧ ∃ t m, mem[t]? = some m ∧ m.loc = a ∧ th'.promises = th.promises.erase t) := by
  cases e with
  | const c =>
      simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
      rcases h with h | ⟨t, htp, hf⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
      · cases hm : mem[t]? with
        | none => simp [hm] at hf
        | some m =>
            simp only [hm] at hf
            split at hf
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
              exact Or.inr ⟨rfl, t, m, hm, hcond.1.1.1, rfl⟩
            · simp at hf
  | reg r =>
      simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
      rcases h with h | ⟨t, htp, hf⟩
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inl ⟨_, rfl, rfl, rfl, rfl⟩
      · cases hm : mem[t]? with
        | none => simp [hm] at hf
        | some m =>
            simp only [hm] at hf
            split at hf
            · rename_i hcond
              simp only [Option.some.injEq, Prod.mk.injEq] at hf
              obtain ⟨rfl, rfl⟩ := hf
              simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
              exact Or.inr ⟨rfl, t, m, hm, hcond.1.1.1, rfl⟩
            · simp at hf

theorem locNC_storeUnits {k : Promises.Knobs} {arch : Arch} {pw : Word} {lbl : AllocLabel} {rel : Bool}
    {T : Ty} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St),
      s' ∈ storeUnits k arch pw ⟨lbl, 0⟩ rel us ws i s →
      (∀ j, OneAt us j → ∀ o, i + j = o + 1 → ¬ TwoAtT T o) →
      (∀ j, TwoAt us j → TwoAtT T (i + j) ∧ ∀ o, i + j = o + 1 → ¬ TwoAtT T o) →
      LocNC lbl T s.mem s.pairs s.promises → LocNC lbl T s'.mem s'.pairs s'.promises
  | [], _, _, s, s', hs, _, _, hG => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hG
  | .one :: us, w :: ws, i, s, s', hs, hOne, hTwo, hG => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      refine locNC_storeUnits us ws (i + 1) _ s' hs (fun j hj o ho => ?_) (fun j hj => ?_) ?_
      · exact hOne (j + 1) (OneAt_cons .one hj) o (by first | omega | (simp only [Acc.size]; omega))
      · have := hTwo (j + 1) (TwoAt_cons .one hj)
        try simp only [Acc.size] at this
        rw [show i + (j + 1) = i + 1 + j by omega] at this; exact this
      · have h0 : ∀ o, i = o + 1 → ¬ TwoAtT T o := fun o ho => hOne 0 ⟨0, rfl, rfl⟩ o (by simp; omega)
        rcases stepStore_casesP hst with ⟨m, e, hl, -, hp⟩ | ⟨e, t, m, ht, hl, hp⟩
        · show LocNC lbl T mem' s.pairs th.promises
          rw [e, hp]
          refine locNC_push hG fun _ o ho hT => absurd hT (h0 o ?_)
          rw [hl] at ho; simpa [offs] using ho
        · show LocNC lbl T mem' s.pairs th.promises
          rw [e, hp]
          refine locNC_erase hG ht fun _ o ho => h0 o ?_
          rw [hl] at ho; simpa [offs] using ho
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hOne, hTwo, hG => by
      simp only [storeUnits] at hs
      obtain ⟨q1, q2, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs ⟨lbl, 0⟩ i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      refine locNC_storeUnits us ws (i + 2) _ s' hs (fun j hj o ho => ?_) (fun j hj => ?_) ?_
      · exact hOne (j + 2) (OneAt_cons .two hj) o (by first | omega | (simp only [Acc.size]; omega))
      · have := hTwo (j + 2) (TwoAt_cons .two hj)
        try simp only [Acc.size] at this
        rw [show i + (j + 2) = i + 2 + j by omega] at this; exact this
      · have hp : (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs ⟨lbl, 0⟩ i) (dataE 1 w0)
            (dataE 2 w1) [0] rel).2.2.promises = s.promises := rfl
        show LocNC lbl T (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs ⟨lbl, 0⟩ i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).1 (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs ⟨lbl, 0⟩ i)
          (dataE 1 w0) (dataE 2 w1) [0] rel).2.1 (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1)
          (offs ⟨lbl, 0⟩ i) (dataE 1 w0) (dataE 2 w1) [0] rel).2.2.promises
        rw [q1, q2, hp]
        obtain ⟨h2a, h2b⟩ := hTwo 0 ⟨0, rfl, rfl⟩
        refine locNC_pushPair hG fun _ => ⟨?_, fun o ho => h2b o ?_⟩
        · simpa [offs, nWords] using h2a
        · simpa [offs, nWords] using ho
  | .one :: _, [], _, _, _, hs, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, hs, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, hs, _, _, _ => by simp [storeUnits] at hs

/-- Before the allocation: the label's messages are own promises, which start no pair store. -/
theorem locNC_init {lbl : AllocLabel} {T : Ty} {s : St}
    (hfresh : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label = lbl → t ∈ s.promises) (hpo : PromOK s)
    (hlt : ∀ t, t ∈ s.pairs → t + 1 < s.mem.size) : LocNC lbl T s.mem s.pairs s.promises :=
  ⟨hlt, fun q hq m0 h0 hl => absurd hq (hpo.2.1 q (hfresh q m0 h0 hl)),
   fun v mv _ hv hP hl _ _ => absurd (hfresh v mv hv hl) hP⟩

theorem layT_of_accs {T : Ty} {us : List Acc} (hus : accs T = some us) : LayT T :=
  Or.inl (by rw [hus]; simp)

/-- **`alloc` at a label laid out as `T`** (`accs T = some us`) keeps `LocNC`. -/
theorem locNC_alloc {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {T : Ty} {s s' : St} {pw : Word} (hal : (s', pw) ∈ alloc k arch lbl us ws s) (hus : accs T = some us)
    (h0 : LocNC lbl T s.mem s.pairs s.promises) : LocNC lbl T s'.mem s'.pairs s'.promises := by
  obtain ⟨s1, hst, -, e1, e2, -, -, -, -, -, esz, eget⟩ := alloc_unf hal
  have h1 : LocNC lbl T s1.mem s1.pairs s1.promises := by
    rw [e1, e2]
    refine ⟨fun q hq => ?_, fun q hq m0 hm hl => ?_, fun v mv o hv hP hl ho hT => ?_⟩
    · rw [esz]; exact Nat.lt_of_lt_of_le (h0.1 q hq) (Nat.le_add_right _ _)
    · rw [eget] at hm
      simp only [Nat.lt_of_succ_lt (h0.1 q hq), ite_true] at hm; exact h0.2.1 q hq m0 hm hl
    · rw [eget] at hv
      split at hv
      · exact h0.2.2 v mv o hv hP hl ho hT
      · split at hv
        · cases hv; exact Or.inl (fun a g h => by cases h)
        · cases hv
  have hlay := layT_of_accs hus
  refine locNC_storeUnits us ws 0 s1 s' hst (fun j hj o ho hT => ?_) (fun j hj => ⟨?_, fun o ho hT => ?_⟩) h1
  · exact (TermPlantF.oneAt_twoAtT (AtOff.here hlay) hus (TermStepper.oneAt_ful hj) hT).2 ho
  · exact ⟨0, T, us, j, Or.inl ⟨rfl, rfl, by rw [hus]; simp⟩, hus, hj, rfl⟩
  · have := TermB5.twoAt_twoAtT (AtOff.here hlay) hus hj hT
    omega

/-- `LocNC` at the result gives `FootNCE` at `allocE`. -/
theorem footNC_ofLoc {E : TEnv} {lbl : AllocLabel} {T : Ty} {mem : Memory} {pairs : List Ts} {th' : TTh}
    (h : LocNC lbl T mem pairs th'.promises) : FootNCE E (allocE E lbl T) (mem, pairs, th') := by
  refine ⟨fun q hq m0 cl h0 hc hn => ?_, fun v mv cl o hv hP hc hn ho hT => ?_⟩
  · by_cases hl : m0.loc.label = lbl
    · rw [hl, allocE_eq] at hc; cases hc; exact h.2.1 q hq m0 h0 hl
    · rw [allocE_ne hl, hn] at hc; cases hc
  · by_cases hl : mv.loc.label = lbl
    · rw [hl, allocE_eq] at hc; cases hc; exact h.2.2 v mv o hv hP hl ho hT
    · rw [allocE_ne hl, hn] at hc; cases hc

/-- **(per-op, `new`) `FootNCE` at `alloc`'s witness** `allocE E lbl T`, `T` laid out as the stored
units (`accs T = some us`), from the old state's fresh label (its messages own promises,
`FreshLP`) and `PromOK`. -/
theorem footNC_alloc {k : Promises.Knobs} {arch : Arch} {E : TEnv} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {T : Ty} {s s' : St} {pw : Word} {th' : TTh}
    (hal : (s', pw) ∈ alloc k arch lbl us ws s) (hus : accs T = some us)
    (hfresh : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m → m.loc.label = lbl → t ∈ s.promises) (hpo : PromOK s)
    (hlt : ∀ t, t ∈ s.pairs → t + 1 < s.mem.size) (hpr : th'.promises = s'.promises) :
    FootNCE E (allocE E lbl T) (s'.mem, s'.pairs, th') :=
  footNC_ofLoc (by rw [hpr]; exact locNC_alloc hal hus (locNC_init hfresh hpo hlt))

#print axioms footNC_sto
#print axioms footNC_efoot
#print axioms fenceS_nalloc
#print axioms ls_nal
#print axioms evalOp_nalloc
#print axioms tstep_nalloc
#print axioms getP
#print axioms getP_lt
#print axioms locNC_push
#print axioms locNC_pushPair
#print axioms locNC_erase
#print axioms stepStore_casesP
#print axioms locNC_storeUnits
#print axioms locNC_init
#print axioms layT_of_accs
#print axioms locNC_alloc
#print axioms footNC_ofLoc
#print axioms footNC_alloc

end TermFootNC

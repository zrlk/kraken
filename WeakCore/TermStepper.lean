import WeakCore.TermSys

/-!
# S8b part 1: what a thread step gives the system invariant

Proof-only scratch module (stage B, S8b).  For a step of thread `j` at a
configuration satisfying `SysInvW`:

* **PromsOK bookkeeping.**  The ghost foreign promises after a promise step
  (`fpProm`: every other thread gains the new timestamp) and after a thread
  step (`fpSync`: keep only what is still outstanding), with `PromsOK`
  preserved (`PromsOK_promise`, `PromsOK_thread`), the side invariants they
  need (`PromsDisj`, `FpOwnFree`, `AllPromLt`, each preserved), and the
  stepper's own `fp` unchanged (`fpSync_self`), so `Cut_self` survives
  (`Cut_withFp`).
* **A1/A2.**  `SysInvW.fpok`/`SysInvW.fresh` (TermSys); the trivial cases
  (`fpok_nil`, `fresh_blankG`), `fpok_of` (A1 from `PromsOK` and where the
  other threads' promises lie), and the stepper's `GFreshE` (`SysInvW.gfresh`).
* **B-facts** (below).

S8b part 2:

* **Bookkeeping clauses** (`SysInvW.disj`/`fpfree`/`plt`/`vwr`/`frle`,
  TermSys): trivial cases (`*_init`), promise step (`SysInvW.book_promise`),
  thread step (`SysInvW.book_thread`, `SysInvW.frle_thread`); `vWr` stays
  within memory (`tstep_vWr`, the `VMono` framework).
* **B2, own cells**: a step writes each old address at most once
  (`tstep_once`), so every new message at an initialised offset of an own cell
  is typed (`SysInvW.newOwn_wordOK`); other threads' cells now use `frle`.
* **B3, own shared cells**: the exact missing fact (`PlantFrozen`) and what it
  gives (`gfoot_ini_shared`).
* **B5, every append**: where each appended message lands, operationally
  (`tstep_newOp`: a `storeUnits` word in its `Role`, an `stp`/`casp` pair word,
  a `fetch`/`cas` RMW) and typed (`tstep_newPos`, `NewPos`); hence within its
  cell's words and never straddling a `word2` unit (`newPos_b5`, `twoAt_word2`,
  `stepper_newPos`), discharging `hwc` (`SysInvW.newOwn_wordOK_sc`).  (F2′ step 3)
  Also at planted slots (`InitR`): `SysInvW.newOwn_wordOK_init`/`_init_sc`.
-/

namespace TermStepper

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermFul (projM_keep stepRmwPair_shape loadUnits_keep)

/-! ## Configurations: who holds a promise -/

theorem mem_allProms {c : Cfg} {t : Ts} :
    t ∈ allProms c ↔ ∃ (i : Nat) (th : TTh), c.ths[i]? = some th ∧ t ∈ th.promises := by
  unfold allProms
  simp only [List.mem_flatMap, Array.mem_toList_iff]
  constructor
  · rintro ⟨th, hth, ht⟩
    obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.1 hth
    exact ⟨i, th, hi, ht⟩
  · rintro ⟨i, th, hi, ht⟩
    exact ⟨th, Array.mem_of_getElem? hi, ht⟩

/-- Every promise of a configuration that changed only thread `j`'s state is
`j`'s new one's or another thread's old one's. -/
theorem mem_allProms_upd {c c' : Cfg} {j : Nat} {th' : TTh} (hj' : c'.ths[j]? = some th')
    (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?) {t : Ts} :
    t ∈ allProms c' ↔ t ∈ th'.promises ∨ ∃ (i : Nat) (thi : TTh), i ≠ j ∧ c.ths[i]? = some thi ∧ t ∈ thi.promises := by
  rw [mem_allProms]
  constructor
  · rintro ⟨i, thi, hi, ht⟩
    by_cases hij : i = j
    · subst hij; rw [hj'] at hi; cases hi; exact .inl ht
    · rw [ho i hij] at hi; exact .inr ⟨i, thi, hij, hi, ht⟩
  · rintro (ht | ⟨i, thi, hij, hi, ht⟩)
    · exact ⟨j, th', hj', ht⟩
    · exact ⟨i, thi, by rw [ho i hij]; exact hi, ht⟩

/-! ## The side invariants of the bookkeeping

`PromsDisj`, `FpOwnFree`, `AllPromLt` are SysInvW clauses (TermSys). -/

/-- `E_g` with its ghost foreign promises replaced. -/
def _root_.TermCut.GEnv.withFp (Eg : GEnv) (f : Nat → List Ts) : GEnv := { Eg with fpOf := f }

/-- (S8b) **After a promise of thread `j` at timestamp `n`**: every other
thread's foreign promises gain `n`. -/
def fpProm (Eg : GEnv) (j : Nat) (n : Ts) : Nat → List Ts :=
  fun i => if i = j then Eg.fpOf i else Eg.fpOf i ++ [n]

/-- (S8b) **After a thread step into `c'`**: the foreign promises that are
still outstanding (a fulfilled promise is dropped everywhere). -/
def fpSync (Eg : GEnv) (c' : Cfg) : Nat → List Ts :=
  fun i => (Eg.fpOf i).filter (fun t => decide (t ∈ allProms c'))

/-- Only `fp` changes: a cut with the same foreign promises is the same cut. -/
theorem Cut_withFp (X : GEnv) (f : Nat → List Ts) (i : Nat) (S : AllocLabel → Prop) (h : f i = X.fpOf i) :
    Cut (X.withFp f) i S = Cut X i S := by
  unfold Cut
  simp only [GEnv.withFp, h]
  rfl

/-! ## `PromsOK` across a promise step -/

theorem or_iffA {P Q A N : Prop} (e : P ∨ Q ↔ A) : (P ∨ N) ∨ Q ↔ A ∨ N := by
  constructor
  · rintro ((h | h) | h)
    · exact .inl (e.1 (.inl h))
    · exact .inr h
    · exact .inl (e.1 (.inr h))
  · rintro (h | h)
    · rcases e.2 h with h | h
      · exact .inl (.inl h)
      · exact .inr h
    · exact .inl (.inr h)

theorem or_iffB {P Q A N : Prop} (e : P ∨ Q ↔ A) : P ∨ (Q ∨ N) ↔ A ∨ N := by
  constructor
  · rintro (h | h | h)
    · exact .inl (e.1 (.inl h))
    · exact .inl (e.1 (.inr h))
    · exact .inr h
  · rintro (h | h)
    · rcases e.2 h with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · exact .inr (.inr h)

section
variable {Eg : GEnv} {c : Cfg} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}

theorem promise_other (hj : c.ths[j]? = some th) {i : Nat} (hij : i ≠ j) :
    (promise c j a v w).ths[i]? = c.ths[i]? := by
  rw [(promise_inv (a := a) (v := v) (w := w) hj).1]
  exact arr_get_set_ne _ _ (Ne.symm hij)

theorem allProms_promise (hj : c.ths[j]? = some th) {t : Ts} :
    t ∈ allProms (promise c j a v w) ↔ t ∈ allProms c ∨ t = c.mem.size := by
  rw [mem_allProms_upd (promise_inv (a := a) (v := v) (w := w) hj).2.1 (fun i hij => promise_other hj hij),
    mem_allProms_upd hj (fun _ _ => rfl)]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro ((h | h) | h)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr h)
  · rintro ((h | h) | h)
    · exact .inl (.inl h)
    · exact .inr h
    · exact .inl (.inr h)

/-- **(S8b) `PromsOK` after a promise step** of thread `j`, with every other
thread's foreign promises gaining the new timestamp (`fpProm`). -/
theorem PromsOK_promise (h : PromsOK Eg c) (hj : c.ths[j]? = some th) :
    PromsOK (Eg.withFp (fpProm Eg j c.mem.size)) (promise c j a v w) := by
  intro i thi hi t
  rw [allProms_promise hj]
  by_cases hij : i = j
  · subst hij
    rw [(promise_inv (a := a) (v := v) (w := w) hj).2.1] at hi
    cases hi
    have e := h i th hj t
    simp only [GEnv.withFp, fpProm, ↓reduceIte, List.mem_append, List.mem_singleton] at e ⊢
    exact or_iffA e
  · rw [promise_other hj hij] at hi
    have e := h i thi hi t
    simp only [GEnv.withFp, fpProm, hij, ↓reduceIte, List.mem_append, List.mem_singleton] at e ⊢
    exact or_iffB e

theorem PromsDisj_promise (hd : PromsDisj c) (hl : AllPromLt c) (hj : c.ths[j]? = some th) :
    PromsDisj (promise c j a v w) := by
  have hn : ∀ (i : Nat) (thi : TTh), c.ths[i]? = some thi → c.mem.size ∉ thi.promises := fun i thi hi ht =>
    Nat.lt_irrefl _ (hl i thi _ hi ht)
  have hupd : ∀ (i : Nat) (thi : TTh), (promise c j a v w).ths[i]? = some thi →
      (i = j ∧ thi = { th with promises := th.promises ++ [c.mem.size] }) ∨ (i ≠ j ∧ c.ths[i]? = some thi) :=
    fun i thi hi => by
      by_cases hij : i = j
      · subst hij; rw [(promise_inv (a := a) (v := v) (w := w) hj).2.1] at hi; cases hi; exact .inl ⟨rfl, rfl⟩
      · rw [promise_other hj hij] at hi; exact .inr ⟨hij, hi⟩
  intro i i' thi thi' t hii hi hi' ht ht'
  rcases hupd i thi hi with ⟨rfl, rfl⟩ | ⟨hij, hi0⟩ <;> rcases hupd i' thi' hi' with ⟨rfl, rfl⟩ | ⟨hij', hi0'⟩
  · exact hii rfl
  · simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hd _ _ _ _ t hii hj hi0' ht ht'
    · exact hn _ _ hi0' ht'
  · simp only [List.mem_append, List.mem_singleton] at ht'
    rcases ht' with ht' | rfl
    · exact hd _ _ _ _ t hii hi0 hj ht ht'
    · exact hn _ _ hi0 ht
  · exact hd _ _ _ _ t hii hi0 hi0' ht ht'

theorem AllPromLt_promise (hl : AllPromLt c) (hj : c.ths[j]? = some th) : AllPromLt (promise c j a v w) := by
  intro i thi t hi ht
  rw [(promise_inv (a := a) (v := v) (w := w) hj).1] at hi ⊢
  simp only [Array.size_push]
  by_cases hij : i = j
  · subst hij
    rw [arr_get_set_eq _ hj] at hi; cases hi
    simp only [List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact Nat.lt_succ_of_lt (hl _ _ _ hj ht)
    · exact Nat.lt_succ_self _
  · rw [arr_get_set_ne _ _ (Ne.symm hij)] at hi
    exact Nat.lt_succ_of_lt (hl _ _ _ hi ht)

theorem FpOwnFree_promise (h : PromsOK Eg c) (hf : FpOwnFree Eg c) (hl : AllPromLt c) (hj : c.ths[j]? = some th) :
    FpOwnFree (Eg.withFp (fpProm Eg j c.mem.size)) (promise c j a v w) := by
  intro i thi t hi ht ht'
  by_cases hij : i = j
  · subst hij
    rw [(promise_inv (a := a) (v := v) (w := w) hj).2.1] at hi; cases hi
    simp only [GEnv.withFp, fpProm, ↓reduceIte] at ht
    simp only [List.mem_append, List.mem_singleton] at ht'
    rcases ht' with ht' | rfl
    · exact hf _ _ _ hj ht ht'
    · obtain ⟨i', thi', hi', ht''⟩ := mem_allProms.1 ((h _ _ hj _).1 (List.mem_append_right _ ht))
      exact Nat.lt_irrefl _ (hl _ _ _ hi' ht'')
  · rw [promise_other hj hij] at hi
    simp only [GEnv.withFp, fpProm, hij, ↓reduceIte, List.mem_append, List.mem_singleton] at ht
    rcases ht with ht | rfl
    · exact hf _ _ _ hi ht ht'
    · exact Nat.lt_irrefl _ (hl _ _ _ hi ht')

end

/-! ## `PromsOK` across a thread step -/

section
variable {Eg : GEnv} {c c' : Cfg} {j : Nat} {th th' : TTh}

/-- **(S8b) `PromsOK` after a thread step** of thread `j` (its promises shrink,
`tstep_fulfil`; the others' are unchanged), the fulfilled promises dropped
from every thread's foreign promises (`fpSync`). -/
theorem PromsOK_thread (h : PromsOK Eg c) (hd : PromsDisj c) (hj : c.ths[j]? = some th)
    (hj' : c'.ths[j]? = some th') (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?)
    (hsub : ∀ t, t ∈ th'.promises → t ∈ th.promises) :
    PromsOK (Eg.withFp (fpSync Eg c')) c' := by
  have hA : ∀ t, t ∈ allProms c' → t ∈ allProms c := fun t ht => by
    rcases (mem_allProms_upd hj' ho).1 ht with ht | ⟨i, thi, -, hi, ht⟩
    · exact mem_allProms.2 ⟨j, th, hj, hsub t ht⟩
    · exact mem_allProms.2 ⟨i, thi, hi, ht⟩
  intro i thi hi t
  simp only [GEnv.withFp, fpSync, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (ht | ⟨-, ht⟩)
    · exact mem_allProms.2 ⟨i, thi, hi, ht⟩
    · exact ht
  · intro ht
    by_cases hp : t ∈ thi.promises
    · exact .inl hp
    refine .inr ⟨?_, ht⟩
    by_cases hij : i = j
    · subst hij
      rw [hj'] at hi; cases hi
      rcases (mem_allProms_upd hj' ho).1 ht with ht1 | ⟨i', thi', hi'j, hi', ht'⟩
      · exact absurd ht1 hp
      · rcases List.mem_append.1 ((h i th hj t).2 (hA t ht)) with h1 | h1
        · exact absurd h1 (hd _ _ _ _ t hi'j hi' hj ht')
        · exact h1
    · rw [ho i hij] at hi
      rcases List.mem_append.1 ((h i thi hi t).2 (hA t ht)) with h1 | h1
      · exact absurd h1 hp
      · exact h1

/-- (S8b) The stepper's own foreign promises are unchanged by its step. -/
theorem fpSync_self (h : PromsOK Eg c) (hf : FpOwnFree Eg c) (hj : c.ths[j]? = some th)
    (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?) : fpSync Eg c' j = Eg.fpOf j := by
  unfold fpSync
  refine List.filter_eq_self.2 fun t ht => ?_
  simp only [decide_eq_true_eq]
  obtain ⟨i, thi, hi, ht'⟩ := mem_allProms.1 ((h j th hj t).1 (List.mem_append_right _ ht))
  have hij : i ≠ j := fun e => by subst e; rw [hj] at hi; cases hi; exact hf _ _ _ hj ht ht'
  exact mem_allProms.2 ⟨i, thi, by rw [ho i hij]; exact hi, ht'⟩

theorem PromsDisj_thread (hd : PromsDisj c) (hj : c.ths[j]? = some th) (hj' : c'.ths[j]? = some th')
    (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?) (hsub : ∀ t, t ∈ th'.promises → t ∈ th.promises) :
    PromsDisj c' := by
  have hb : ∀ (i : Nat) (thi : TTh), c'.ths[i]? = some thi → ∃ thi0 : TTh, c.ths[i]? = some thi0 ∧
      ∀ t, t ∈ thi.promises → t ∈ thi0.promises := fun i thi hi => by
    by_cases hij : i = j
    · subst hij; rw [hj'] at hi; cases hi; exact ⟨th, hj, hsub⟩
    · rw [ho i hij] at hi; exact ⟨thi, hi, fun _ h => h⟩
  intro i i' thi thi' t hii hi hi' ht ht'
  obtain ⟨a, ha, ha'⟩ := hb i thi hi
  obtain ⟨b, hb', hb''⟩ := hb i' thi' hi'
  exact hd _ _ _ _ t hii ha hb' (ha' t ht) (hb'' t ht')

theorem AllPromLt_thread (hl : AllPromLt c) (hj : c.ths[j]? = some th) (hj' : c'.ths[j]? = some th')
    (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?) (hsub : ∀ t, t ∈ th'.promises → t ∈ th.promises)
    (hsz : c.mem.size ≤ c'.mem.size) : AllPromLt c' := by
  intro i thi t hi ht
  by_cases hij : i = j
  · subst hij; rw [hj'] at hi; cases hi; exact Nat.lt_of_lt_of_le (hl _ _ _ hj (hsub t ht)) hsz
  · rw [ho i hij] at hi; exact Nat.lt_of_lt_of_le (hl _ _ _ hi ht) hsz

theorem FpOwnFree_thread (hf : FpOwnFree Eg c) (hj : c.ths[j]? = some th) (hj' : c'.ths[j]? = some th')
    (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?) (hsub : ∀ t, t ∈ th'.promises → t ∈ th.promises) :
    FpOwnFree (Eg.withFp (fpSync Eg c')) c' := by
  intro i thi t hi ht ht'
  simp only [GEnv.withFp, fpSync, List.mem_filter] at ht
  by_cases hij : i = j
  · subst hij; rw [hj'] at hi; cases hi; exact hf _ _ _ hj ht.1 (hsub t ht')
  · rw [ho i hij] at hi; exact hf _ _ _ hi ht.1 ht'

end

/-- The thread-step shape of a machine thread step (`threadSteps`). -/
theorem threadSteps_upd {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) :
    ∃ (th : TTh) (r : Memory × List Ts × TTh), c.ths[i]? = some th ∧ r ∈ tstep (gOf p k arch c i) c.mem c.pairs th ∧ c'.mem = r.1 ∧
      c'.pairs = r.2.1 ∧ c'.ths[i]? = some r.2.2 ∧ (∀ i', i' ≠ i → c'.ths[i']? = c.ths[i']?) :=
  let ⟨th, r, hth, hr, e1, e2, e3, _⟩ := TermFul.threadSteps_inv h
  ⟨th, r, hth, hr, e1, e2, e3, fun _ hj => threadSteps_other h hj⟩

/-! ## A1 and A2: the trivial cases and the stepper's freshness -/

/-- (S8b A1) With no ghost foreign promises, `fpok` holds. -/
theorem fpok_nil {Eg : GEnv} {c : Cfg} (h : ∀ i, Eg.fpOf i = []) :
    ∀ (i : Nat) (th : TTh) (S : AllocLabel → Prop), c.ths[i]? = some th → FpOK (Cut Eg i S) (stOf c.mem c.pairs th) :=
  fun i _ S _ => ⟨fun t ht => by simp [Cut_fp, h i] at ht, fun t _ ht => by simp [Cut_fp, h i] at ht⟩

/-- (S8b A1) **`fpok` from `PromsOK`**: thread `i`'s foreign promises are
other threads' promises (`FpOwnFree`), so messages (`AllPromLt`); what remains
is that no other thread's promise lies at `i`'s private cell (`hv`). -/
theorem fpok_of {Eg : GEnv} {c : Cfg} (h : PromsOK Eg c) (hf : FpOwnFree Eg c) (hl : AllPromLt c)
    (hv : ∀ (i i' : Nat) (th th' : TTh) (t : Ts) (m : Msg) (S : AllocLabel → Prop), i ≠ i' → c.ths[i]? = some th → c.ths[i']? = some th' →
      t ∈ th'.promises → c.mem[t]? = some m → Vis (Cut Eg i S) m.loc.label) :
    ∀ (i : Nat) (th : TTh) (S : AllocLabel → Prop), c.ths[i]? = some th → FpOK (Cut Eg i S) (stOf c.mem c.pairs th) := by
  intro i th S hth
  have key : ∀ t, t ∈ Eg.fpOf i → ∃ (i' : Nat) (th' : TTh), i ≠ i' ∧ c.ths[i']? = some th' ∧ t ∈ th'.promises := fun t ht => by
    obtain ⟨i', th', hi', ht'⟩ := mem_allProms.1 ((h i th hth t).1 (List.mem_append_right _ ht))
    refine ⟨i', th', fun e => ?_, hi', ht'⟩
    subst e; rw [hth] at hi'; cases hi'; exact hf _ _ _ hth ht ht'
  refine ⟨fun t ht => ?_, fun t m ht hm => ?_⟩
  · rw [Cut_fp] at ht
    obtain ⟨i', th', -, hi', ht'⟩ := key t ht
    exact hl _ _ _ hi' ht'
  · rw [Cut_fp] at ht
    obtain ⟨i', th', hne, hi', ht'⟩ := key t ht
    exact hv i i' th th' t m S hne hth hi' ht' hm

/-- (S8b) In an `E_g` with no cells, boxes, counts or frontiers, `fresh`
holds when memory at every thread's fresh labels holds only its promises. -/
theorem fresh_blankG {Eg : GEnv} {c : Cfg} (hs : ∀ l, Eg.sto l = none) (hb : ∀ l, Eg.box l = none)
    (hi : ∀ l, Eg.ini l = 0) (hp : ∀ l, Eg.pfr l = none)
    (hm : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ∀ j, th.nalloc ≤ j → ∀ (t : Nat) (m : Msg), c.mem[t]? = some m →
      m.loc.label = freshLabel c.lbase c.n i j → t ∈ th.promises) :
    ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ∀ j, th.nalloc ≤ j → GFreshL Eg c th (freshLabel c.lbase c.n i j) :=
  fun i th hth j hj => ⟨hs _, hb _, hi _, hp _, hm i th hth j hj⟩

/-- (S8b) **The stepper's fresh labels are blank in `E_g`** (`GFreshE`, the
`hfr` of `EFoot_post`/`Cut_self`), from `fresh`. -/
theorem SysInvW.gfresh {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    (n' : Nat) : GFreshE (gOf p k arch c i) Eg th.nalloc n' := by
  rintro l ⟨j, hj, -, rfl⟩
  obtain ⟨h1, h2, -, h4, -⟩ := h.fresh i th hth j hj
  exact ⟨h1, h2, h4⟩

/-- (S8b) The memory half of `fresh`, as the stepper's `FreshLP` reads it. -/
theorem SysInvW.freshMem {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {j : Nat} (hj : th.nalloc ≤ j) {t : Nat} {m : Msg} (hm : c.mem[t]? = some m)
    (hl : m.loc.label = freshLabel (gOf p k arch c i).lbase (gOf p k arch c i).n (gOf p k arch c i).i j) :
    t ∈ th.promises :=
  (h.fresh i th hth j hj).2.2.2.2 t m hm hl

/-! ## (B1) Where a thread step writes: operationally

`NewIn s s' Q`: every message of `s'` past `s`'s memory is at a label in `Q`.
An operation writes through its address operands (`OpTgt`) or at fresh labels
(allocation); a thread step adds `cas`/`casp`'s address (`TermTgt`). -/

/-- Every message past `s`'s memory in `s'` is at a label in `Q`. -/
def NewIn (s s' : St) (Q : AllocLabel → Prop) : Prop :=
  ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → Q m.loc.label

theorem NewIn.of_eq {s s' : St} {Q : AllocLabel → Prop} (h : s'.mem = s.mem) : NewIn s s' Q :=
  fun t m ht hm => by rw [h] at hm; exact absurd (lt_of_get hm) (by omega)

theorem NewIn.mono {s s' : St} {Q Q' : AllocLabel → Prop} (h : NewIn s s' Q) (hq : ∀ L, Q L → Q' L) :
    NewIn s s' Q' := fun t m ht hm => hq _ (h t m ht hm)

theorem NewIn.left {s s1 s2 : St} {Q : AllocLabel → Prop} (he : s1.mem = s.mem) (h : NewIn s1 s2 Q) :
    NewIn s s2 Q := fun t m ht hm => h t m (by rw [he]; exact ht) hm

theorem NewIn.trans {s1 s2 s3 : St} {Q : AllocLabel → Prop} (h1 : NewIn s1 s2 Q) (h2 : NewIn s2 s3 Q)
    (he : MemExt s2.mem s3.mem) : NewIn s1 s3 Q := by
  intro t m ht hm
  cases e : s2.mem[t]? with
  | none =>
      have : s2.mem.size ≤ t := by
        apply Nat.le_of_not_lt; intro hl; rw [Array.getElem?_eq_getElem hl] at e; cases e
      exact h2 t m this hm
  | some m' =>
      have := he t m' e
      rw [this] at hm; cases hm
      exact h1 t m ht e

theorem newIn_storeUnits {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} (hs : s' ∈ storeUnits k arch pw a rel us ws i s) :
    NewIn s s' (· = a.label) :=
  fun t m ht hm => (storeUnits_growsF us ws i s s' hs).1.2.2 t m ht hm

/-- The address an atom's single word points to. -/
def AtAddr (env : Env) (a : At) (L : AllocLabel) : Prop :=
  ∃ rt pw b, evalAt env a = some (rt, [pw]) ∧ addrOf pw = some b ∧ b.label = L

/-- The address operands an operation writes through. -/
def OpTgt : Op → List At
  | .store _ a _ _ | .xchg a _ | .stp _ a _ _ _ | .fetch _ _ _ a _ => [a]
  | .stl b _ _ | .stlw b _ _ _ | .xchgAt b _ _ | .xchgAtF b _ _ _ | .bufInit b _ _ => [b]
  | _ => []

/-- The address operands a term's step writes through. -/
def TermTgt : Expr → List At
  | .let_ _ op _ => OpTgt op
  | .cas _ _ w _ _ _ _ _ => [w]
  | .casp _ _ w _ _ _ _ _ _ _ => [w]
  | _ => []

theorem tgt_of {env : Env} {a : At} {L : AllocLabel} {l : List At} {rt : Ty} {pw : Word} {b : Address}
    (hb : addrOf pw = some b) (he : evalAt env a = some (rt, [pw])) (hl : b.label = L) (hm : a ∈ l) :
    ∃ a, a ∈ l ∧ AtAddr env a L := ⟨a, hm, rt, pw, b, he, hb, hl⟩

theorem loadUnits_nalloc {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.nalloc = s.nalloc
  | [], _, s, r, hr => by simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_nalloc us (k + 1) _ (s', ws) hmem; exact this
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_nalloc us (k + 2) _ (s', ws) hmem; exact this

theorem projM_nalloc {g : G} {s : St} {ty : Ty} {ws : List Word} {r : St × Nat × List Word}
    (h : r ∈ projM g s ty ws) : r.1.nalloc = s.nalloc := by
  unfold projM at h
  split at h
  · split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        have a1 := loadUnits_nalloc _ _ _ _ h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             exact (loadUnits_nalloc _ _ _ _ h2).trans a1)
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    rfl

/-- An allocation at the next fresh label writes there only. -/
theorem newIn_alloc {g : G} {us : List Acc} {ws : List Word} {s : St} {r : St × Word} {X : AllocLabel → Prop}
    (hpl : PromLt s) (hr : r ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i s.nalloc) us ws s) :
    NewIn s r.1 (fun L => FreshIn g s.nalloc r.1.nalloc L ∨ X L) := by
  obtain ⟨hg, -, hn, -⟩ := alloc_growsP hpl r hr
  intro t m ht hm
  exact .inl ⟨s.nalloc, Nat.le_refl _, by omega, hg.2.2 t m ht hm⟩

theorem newIn_allocBuf {g : G} {n : Nat} {z : Option (List WeakMem.Val)} {s s' : St} {pw : Word}
    {X : AllocLabel → Prop} (he : allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s = (s', pw)) :
    NewIn s s' (fun L => FreshIn g s.nalloc s'.nalloc L ∨ X L) := by
  obtain ⟨hg, -, hn⟩ := allocBuf_grows (freshLabel g.lbase g.n g.i s.nalloc) n z s
  rw [he] at hg hn
  intro t m ht hm
  exact .inl ⟨s.nalloc, Nat.le_refl _, by simp only at hn; omega, hg.2.2 t m ht hm⟩

/-- A boxed injection after a projection allocates at the next fresh label. -/
theorem newIn_projInj {g : G} {s : St} {t S : Ty} {ws : List Word} {j : Nat} {p : List Word}
    {x : St × Nat × List Word} {y : St × List Word} {X : AllocLabel → Prop} (hpl : PromLt s)
    (hx : x ∈ projM g s t ws) (hy : y ∈ injM g x.1 S j p) :
    NewIn s y.1 (fun L => FreshIn g s.nalloc y.1.nalloc L ∨ X L) := by
  obtain ⟨e1, -, e3⟩ := projM_keep hx
  have e4 := projM_nalloc hx
  have hpl1 : PromLt x.1 := fun t ht => by rw [e1]; rw [e3] at ht; exact hpl t ht
  refine NewIn.left e1 ?_
  rw [← e4]
  unfold injM at hy
  split at hy
  · split at hy
    · simp only [List.mem_map] at hy
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := hy
      have h := newIn_alloc (X := X) hpl1 hs
      dsimp only
      split
      · exact h
      · exact h
    · cases hy
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at hy
    obtain ⟨_, -, rfl⟩ := hy
    exact NewIn.of_eq rfl

/-- An RMW appends at most one message, at its address. -/
theorem rmw_newAt {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {x : Memory × Promises.Thread}
    (h : x ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → x.1[t]? = some m → m.loc.label = a.label := by
  obtain ⟨mem', th'⟩ := x
  intro t m ht hm
  dsimp only at hm
  obtain ⟨_, _, _, _, _, h⟩ := stepRmw_mem h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -⟩ | ⟨_, _, _, rfl, -⟩⟩
  · exact absurd (lt_of_get hm) (by omega)
  · rw [Array.getElem?_push] at hm
    split at hm
    · cases hm; rfl
    · exact absurd (lt_of_get hm) (by omega)
  · exact absurd (lt_of_get hm) (by omega)

/-- A `casp` appends at most its two words, at its address. -/
theorem rmwPair_newAt {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc.label = a.label := by
  intro t m ht hm
  rcases stepRmwPair_shape h with ⟨rfl, -⟩ | ⟨⟨m0, m1, rfl, h0, h1⟩, -⟩
  · exact absurd (lt_of_get hm) (by omega)
  · rw [Array.getElem?_push] at hm
    split at hm
    · cases hm; rw [h1]; rfl
    · rw [Array.getElem?_push] at hm
      split at hm
      · cases hm; rw [h0]
      · exact absurd (lt_of_get hm) (by simp at *; omega)

theorem newIn_allocBuf' {g : G} {n : Nat} {z : Option (List WeakMem.Val)} {s : St} {X : AllocLabel → Prop} :
    NewIn s (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s).1
      (fun L => FreshIn g s.nalloc (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s).1.nalloc L ∨ X L) :=
  newIn_allocBuf (pw := (allocBuf (freshLabel g.lbase g.n g.i s.nalloc) n z s).2) rfl

/-- **(B1, operation)**: every message an operation appends is at one of its
fresh labels or at the address of one of its address operands. -/
theorem evalOp_new {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) :
    NewIn s r.1 (fun L => FreshIn g s.nalloc r.1.nalloc L ∨ ∃ a, a ∈ OpTgt op ∧ AtAddr env a L) := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first
         | exact NewIn.of_eq rfl
         | exact newIn_allocBuf ‹_›
         | exact newIn_allocBuf')
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact NewIn.of_eq (loadUnits_keep _ _ _ _ hx).1
         | exact (newIn_storeUnits hx).mono
             (fun L hL => Or.inr (tgt_of (by assumption) (by assumption) (by exact hL.symm) (List.mem_singleton_self _)))
         | exact newIn_alloc hpl hx
         | exact fun t m ht hm => Or.inr (tgt_of (by assumption) (by assumption) (by exact (rmw_newAt hx t m ht hm).symm) (List.mem_singleton_self _)))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact newIn_projInj hpl hx hy
         | exact NewIn.left (loadUnits_keep _ _ _ _ hx).1 ((newIn_storeUnits hy).mono
             (fun L hL => Or.inr (tgt_of (by assumption) (by assumption) (by exact hL.symm) (List.mem_singleton_self _)))))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact NewIn.left (loadUnits_keep _ _ _ _ hx).1 ((newIn_storeUnits hy).mono
           (fun L hL => Or.inr (tgt_of (by assumption) (by assumption) (by exact hL.symm) (List.mem_singleton_self _))))
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact NewIn.of_eq (loadUnits_keep _ _ _ _ hx).1)
    | (simp only [Option.toList_some, List.mem_singleton] at h; subst h; dsimp only; exact newIn_allocBuf')

/-- **(B1, thread step)**: every message a thread step appends is at one of the
thread's fresh labels (`th.nalloc ≤ j < th'.nalloc`) or at the address of one
of the term's address operands (`TermTgt`). -/
theorem tstep_new {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hpl : PromLt (stOf mem pairs th)) (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ ∃ a, a ∈ TermTgt th.term ∧ AtAddr th.env a m.loc.label := by
  intro t m ht hm
  simp only [tstep] at h
  split at h <;> rename_i hT <;> simp only [hT, TermTgt]
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only at hm; exact absurd (lt_of_get hm) (by omega))
    -- D1: `region` fences (memory unchanged)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf] at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_new hpl hx t m ht hm
         | (split <;> exact evalOp_new hpl hx t m ht hm)
         | exact Or.inr (tgt_of (by assumption) (by assumption) (by exact (rmw_newAt hx t m ht hm).symm)
             (List.mem_singleton_self _))
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact Or.inr (tgt_of (by assumption) (by assumption)
              (by exact (rmwPair_newAt hx t m ht hm).symm) (List.mem_singleton_self _))))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact (newIn_projInj (X := fun _ => False) hpl hx hy t m ht hm).imp id False.elim)

/-! ## (B1) Where a thread step writes: typing

Every address operand of a typed term is a reference (`cellOf`) or a buffer
(`bufOf`), so its address is at a label of `Σ` (`VR`). -/

/-- A reference or buffer type. -/
def IsRef (t : Ty) : Prop := (∃ x, cellOf t = some x) ∨ (∃ x, bufOf t = some x)

theorem isRef_cell {t : Ty} {x : Mode × Ty} (h : cellOf t = some x) : IsRef t := .inl ⟨x, h⟩

theorem isRef_cellOr {t u : Ty} {x : Mode × Ty} {P : Idx → Prop}
    (h : cellOf t = some x ∨ ∃ r, cellOf t = some (.rgn r, u) ∧ P r) : IsRef t := by
  rcases h with h | ⟨_, h, -⟩
  · exact .inl ⟨_, h⟩
  · exact .inl ⟨_, h⟩

theorem isRef_buf {t : Ty} {x : Mode × Idx × Ty × Idx} (h : bufOf t = some x) : IsRef t := .inr ⟨x, h⟩

theorem isRef_word {t : Ty} {x : Idx × Proto} (h : wordOf t = some x) : IsRef t := by
  unfold wordOf at h; split at h <;> first | exact .inl ⟨_, rfl⟩ | (cases h)

theorem isRef_word2 {t : Ty} {x : Idx × Proto2} (h : word2Of t = some x) : IsRef t := by
  unfold word2Of at h; split at h <;> first | exact .inl ⟨_, rfl⟩ | (cases h)

theorem isRef_epair {t : Ty} {x : Idx × ECounter} (h : epairOf t = some x) : IsRef t := by
  unfold epairOf at h; split at h <;> first | exact .inl ⟨_, rfl⟩ | (cases h)

theorem isRef_xchg {cx : Cx} {t u o : Ty} (h : XchgCell cx t u o) : IsRef t := by
  cases h with
  | own _ hc _ => exact isRef_cell hc
  | rgn _ hc _ _ _ => exact isRef_cell hc

/-- A reference's or buffer's address is at a label of `Σ`. -/
theorem vr_sto {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {pw : Word} {b : Address}
    (hv : VR ρ η t rt [pw]) (ht : IsRef t) (hb : addrOf pw = some b) : ∃ c, η.sto b.label = some c := by
  have key : ∀ a g, pw.val = .loc a g → b = a := fun a g h => by
    simp [addrOf, h] at hb; exact hb.symm
  have hloc : ∀ μ u, VR ρ η (.loc μ u) rt [pw] → ∃ c, η.sto b.label = some c := by
    intro μ u hv
    simp only [VR] at hv
    rcases hv with ⟨hws, -⟩ | ⟨a, c, U, hws, hsto, -⟩
    · have hpw : pw.val = .null := by simpa using hws
      simp [addrOf, hpw] at hb
    · have := key a 0 (by simpa using hws); subst this; exact ⟨c, hsto⟩
  rcases ht with ⟨x, hx⟩ | ⟨x, hx⟩
  · unfold cellOf at hx
    split at hx
    · simp only [VR] at hv
      obtain ⟨a, c, hws, -, hsto, -⟩ := hv
      have := key a 0 (by simpa using hws); subst this; exact ⟨c, hsto⟩
    · exact hloc _ _ hv
    · cases hx
  · unfold bufOf at hx
    split at hx
    · simp only [VR] at hv; exact hloc _ _ hv.1
    · cases hx

theorem peek_sto {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env) (hp : cx.peek a = .ok t)
    (ht : IsRef t) (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) :
    ∃ c, η.sto b.label = some c := by
  obtain ⟨rt', ws, hea', hv, -⟩ := peek_VR hvars hp
  rw [hea] at hea'
  simp only [Option.some.injEq, Prod.mk.injEq] at hea'
  obtain ⟨rfl, rfl⟩ := hea'
  exact vr_sto hv ht hb

/-- **(B1, typing)**: every address operand of a typed term (`TermTgt`) points
into a cell of `Σ`. -/
theorem termTgt_sto {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env}
    {term : Expr} {a : At} {L : AllocLabel} (hT : Typed p cx term) (hvars : VarsOK ρ η σs cx.vars env)
    (ha : a ∈ TermTgt term) (hA : AtAddr env a L) : ∃ c, η.sto L = some c := by
  obtain ⟨rt, pw, b, hea, hb, rfl⟩ := hA
  cases term <;> simp only [TermTgt, List.mem_singleton, List.not_mem_nil] at ha
  case let_ x op e =>
    cases op <;> simp only [OpTgt, List.mem_singleton, List.not_mem_nil] at ha
    all_goals subst ha
    all_goals cases hT
    all_goals rename_i hop _
    all_goals cases hop
    all_goals first
      | exact peek_sto hvars (by assumption) (by first
          | exact isRef_cell (by assumption) | exact isRef_word (by assumption)
          | exact isRef_word2 (by assumption) | exact isRef_buf (by assumption)
          | exact isRef_cellOr (by assumption) | exact isRef_xchg (by assumption)) hea hb
      | exact peek_sto hvars (use_inv (ρ := ρ) (η := η) (σs := σs) (env := env) (by assumption)).1
          (isRef_buf (by assumption)) hea hb
  all_goals subst ha
  all_goals cases hT
  all_goals first
    | exact peek_sto hvars (by assumption) (by first
        | exact isRef_cell (by assumption) | exact isRef_word (by assumption)
        | exact isRef_word2 (by assumption) | exact isRef_epair (by assumption)
        | exact isRef_cellOr (by assumption)) hea hb

/-- **(B1, thread)**: a typed thread's step appends only at its fresh labels
or at labels of its environment's `Σ`. -/
theorem tstep_writeAt {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    {r : Memory × List Ts × TTh} (hE : ThInvE p E th) (hpl : PromLt (stOf mem pairs th))
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ ∃ cl, E.sto m.loc.label = some cl := by
  obtain ⟨ρ, η, cx, rfl, -, hT, -, hi, -⟩ := hE
  intro t m ht hm
  rcases tstep_new hpl h t m ht hm with hf | ⟨a, ha, hA⟩
  · exact .inl hf
  · exact .inr (termTgt_sto (η := η) hT hi.2.1 ha hA)

/-- **(B1, system)**: under `SysInvW`, a step of thread `i` appends only at
`i`'s fresh labels (globally blank, `fresh`) or at labels of `i`'s cut. -/
theorem stepper_writeAt {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th) :
    ∃ S, ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → r.1[t]? = some m →
      FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label ∨
        ∃ cl, (Cut Eg i S).sto m.loc.label = some cl := by
  obtain ⟨S, -, hE, hm, -⟩ := h.thread hth
  exact ⟨S, tstep_writeAt hE hm.2.2.1 hr⟩

/-- A thread step adds no promise: every new message is no promise of the
result. -/
theorem tstep_newNotProm {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hlt : ∀ t, t ∈ th.promises → t < mem.size) (hpp : ∀ t, t ∈ th.promises → t ∉ pairs)
    (h : r ∈ tstep g mem pairs th) {t : Nat} (ht : mem.size ≤ t) : t ∉ r.2.2.promises := fun hp =>
  absurd (hlt t ((TermFul.tstep_fulfil hlt hpp h).1.subset hp)) (Nat.not_lt.2 ht)

/-! ## (B3) Counts at shared labels -/

/-- **(B3)**: along a global step of `g.i`, the initialised count is unchanged
at every cell that is not `g.i`'s (in particular at every shared cell of
another thread). -/
theorem gfoot_ini_other {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg' n n' v)
    (hfr : GFreshE g Eg n n') {l : AllocLabel} {cl : Cell} (hc : Eg.sto l = some cl)
    (ho : cl.owner ≠ some g.i) : Eg'.ini l = Eg.ini l := by
  rcases (hf.2.2.2.1 l).2 with e | hF | ⟨c', hc', ho'⟩
  · exact e
  · rw [(hfr l hF).1] at hc; cases hc
  · rw [hc] at hc'; cases hc'; exact absurd ho' ho

/-- **(B3)** at a box label (no cell): the count is unchanged. -/
theorem gfoot_ini_box {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg' n n' v)
    (hfr : GFreshE g Eg n n') {l : AllocLabel} {B : Box} (hb : Eg.box l = some B) (hs : Eg.sto l = none) :
    Eg'.ini l = Eg.ini l := by
  rcases (hf.2.2.2.1 l).2 with e | hF | ⟨c', hc', -⟩
  · exact e
  · rw [(hfr l hF).2.1] at hb; cases hb
  · rw [hs] at hc'; cases hc'

/-- **(B3)** at `g.i`'s own cells the count only grows (`bufInit` raises it,
also at an own planted buffer: that case is not excluded here). -/
theorem gfoot_ini_own {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg' n n' v)
    (l : AllocLabel) : Eg.ini l ≤ Eg'.ini l := (hf.2.2.2.1 l).1

/-! ## (B5) No single-word write inside a two-word unit -/

/-- **(B5)**: every single-word write (`SW`) of a typed, in-scope thread lands
in a cell of its `Σ`, at an offset of no `word2` unit of the cell's type
(`SWOne_holds` + `oneAt_word2`). -/
theorem sw_noWord2 {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {loc : Address} {val : WeakMem.Val} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (hpa : PromAbove (stOf mem pairs th)) (hsw : TermFul.SW g mem pairs th loc val) :
    ∃ cl, η.sto loc.label = some cl ∧
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → loc.offset ≠ o2 ∧ loc.offset ≠ o2 + 1 := by
  obtain ⟨cl, o, U, us, j, hcl, h1o, hus, hj, ho⟩ :=
    TermTyped.SWOne_holds p g mem pairs th ρ η cx loc val hE hT htv hi hm hsc hpa hsw
  refine ⟨cl, hcl, fun o2 r P h2 => ?_⟩
  rw [ho]
  exact TermGlob.oneAt_word2 h1o hus hj h2

/-- **(B5, cut form)**: the same at a thread's `ThInvE` environment. -/
theorem sw_noWord2E {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    {loc : Address} {val : WeakMem.Val} (hE : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th))
    (hsc : ∀ (η : TEnv) (cx : Cx), CE η = E → Typed p cx th.term → StepScope cx th.term)
    (hpa : PromAbove (stOf mem pairs th)) (hsw : TermFul.SW g mem pairs th loc val) :
    ∃ cl, E.sto loc.label = some cl ∧
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → loc.offset ≠ o2 ∧ loc.offset ≠ o2 + 1 := by
  obtain ⟨ρ, η, cx, rfl, hEo, hT, htv, hi, -⟩ := hE
  exact sw_noWord2 (η := η) hEo hT htv hi hm (hsc η cx rfl hT) hpa hsw

/-! ## (B5) Every append: where it lands, in its unit's role

Operationally (`tstep_newOp`): every message a thread step appends is at a
fresh label, or it is word `j` of a `storeUnits` call (`UnitsOp`, in the role
`storeUnits_roles` gives), word `j` of an `stp`'s pair, a `fetch`'s or `cas`'s
RMW at its address, or one of a `casp`'s two words.  Typed (`tstep_newPos`):
the word is at `o + j` of a cell of `Σ`, where `o` is a component `U` of the
cell's type and `j` has a role (`Role`) in `U`'s units.  Hence (`newPos_b5`)
it is inside the cell's words, and a message inside a `word2` unit is a word of
a two-word unit starting there (`twoAt_word2`: two-word units never straddle a
`word2` unit). -/

/-- The role of word `j` of a unit list: a one-word unit, or the first or the
second word of a two-word unit. -/
def Role (us : List Acc) (j : Nat) : Prop :=
  TermFul.OneAt us j ∨ TwoAt us j ∨ ∃ jj, j = jj + 1 ∧ TwoAt us jj

theorem oneAt_ful : ∀ {us : List Acc} {j : Nat}, TermStep.OneAt us j → TermFul.OneAt us j
  | [], _, ⟨_, h, _⟩ => by simp at h
  | u :: us, j, ⟨0, h, e⟩ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have e0 : j = 0 := by rw [e]; rfl
      subst e0; exact .here _
  | u :: us, j, ⟨i + 1, h, e⟩ => by
      simp only [List.getElem?_cons_succ] at h
      have ih := oneAt_ful (us := us) ⟨i, h, rfl⟩
      have e' : j = nWords (us.take i) + u.size := by
        rw [e]; simp only [List.take_succ_cons, nWords, List.map_cons, List.sum_cons]; omega
      rw [e']; exact .cons u ih

theorem role_lt {us : List Acc} {j : Nat} (h : Role us j) : j < nWords us := by
  rcases h with h | h | ⟨jj, rfl, h⟩
  · exact TermFul.OneAt_lt h
  · have := TwoAt_lt h; omega
  · have := TwoAt_lt h; omega

theorem role_of_newRole {us : List Acc} {a : Address} {i M0 : Nat} {s' : St} {t j : Nat}
    (h : NewRole us a i M0 s' t j) : Role us j := by
  rcases h with h | ⟨h, -⟩ | ⟨jj, -, -, rfl, h, -⟩
  · exact .inl (oneAt_ful h)
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨jj, rfl, h⟩)

theorem role_two0 : Role [.two] 0 := .inr (.inl ⟨0, rfl, rfl⟩)

theorem role_two1 : Role [.two] 1 := .inr (.inr ⟨0, rfl, ⟨0, rfl, rfl⟩⟩)

/-- (B5) Where an operation's new message at `loc` can be, operationally: word
`j` of a `storeUnits` call (`UnitsOp`) in its role; word `j` of an `stp`'s
pair; or a `fetch`'s RMW, at its address. -/
def OpNew (g : G) (env : Env) (s : St) (op : Op) (loc : Address) : Prop :=
  (∃ pw b rel us ws j, TermFul.UnitsOp g env s op pw b rel us ws ∧ Role us j ∧ loc = offs b j) ∨
  (∃ rel a v0 v1 tk t pw b j, op = .stp rel a v0 v1 tk ∧ evalAt env a = some (t, [pw]) ∧
    addrOf pw = some b ∧ Role [.two] j ∧ loc = offs b j) ∨
  (∃ o acq rel a v t pw, op = .fetch o acq rel a v ∧ evalAt env a = some (t, [pw]) ∧
    addrOf pw = some loc)

theorem units_new {k : Promises.Knobs} {arch : Arch} {g : G} {env : Env} {op : Op} {pw : Word}
    {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hm1 : s1.mem = s.mem) (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1)
    (hU : TermFul.UnitsOp g env s op pw b rel us ws) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → OpNew g env s op m.loc := by
  intro t m ht hm
  obtain ⟨-, -, h3⟩ := storeUnits_roles us ws 0 s1 s' hs
  obtain ⟨j, hl, hr⟩ := h3 t m (by rw [hm1]; exact ht) hm
  exact .inl ⟨pw, b, rel, us, ws, j, hU, role_of_newRole hr, by rw [hl, Nat.zero_add]⟩

/-- An RMW appends at most one message, exactly at its address. -/
theorem rmw_newLoc {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {x : Memory × Promises.Thread}
    (h : x ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → x.1[t]? = some m → m.loc = a := by
  obtain ⟨mem', th'⟩ := x
  intro t m ht hm
  dsimp only at hm
  obtain ⟨_, _, _, _, _, h⟩ := stepRmw_mem h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -⟩ | ⟨_, _, _, rfl, -⟩⟩
  · exact absurd (lt_of_get hm) (by omega)
  · rw [Array.getElem?_push] at hm
    split at hm
    · cases hm; rfl
    · exact absurd (lt_of_get hm) (by omega)
  · exact absurd (lt_of_get hm) (by omega)

/-- A `casp` appends at most its two words, exactly at its address and the next. -/
theorem rmwPair_newLoc {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc = a ∨ m.loc = a.next := by
  intro t m ht hm
  rcases stepRmwPair_shape h with ⟨rfl, -⟩ | ⟨⟨m0, m1, rfl, h0, h1⟩, -⟩
  · exact absurd (lt_of_get hm) (by omega)
  · rw [Array.getElem?_push] at hm
    split at hm
    · cases hm; exact .inr h1
    · rw [Array.getElem?_push] at hm
      split at hm
      · cases hm; exact .inl h0
      · exact absurd (lt_of_get hm) (by simp at *; omega)

theorem evalOp_store_new {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v : At}
    {o : Option At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.store rel a v o)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.store rel a v o) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_new rfl hs (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchg_new {g : G} {env : Env} {σs : List Ty} {s : St} {a v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchg a v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m → OpNew g env s (.xchg a v) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
       exact units_new k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchgAt_new {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchgAt bb i v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.xchgAt bb i v) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
       exact units_new k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchgAtF_new {g : G} {env : Env} {σs : List Ty} {s : St} {bb i : At} {p : List Nat}
    {v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchgAtF bb i p v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.xchgAtF bb i p v) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
       exact units_new k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_bufInit_new {g : G} {env : Env} {σs : List Ty} {s : St} {bb i x : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.bufInit bb i x)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.bufInit bb i x) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_new rfl hs (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_stl_new {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stl bb i v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m → OpNew g env s (.stl bb i v) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
         exact units_new k1 hy (by dsimp only [TermFul.UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stlw_new {g : G} {env : Env} {σs : List Ty} {s : St} {bb wi jl v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stlw bb wi jl v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.stlw bb wi jl v) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := loadUnits_keep _ _ _ _ hx
         exact units_new k1 hy (by dsimp only [TermFul.UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stp_new {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v0 v1 tk : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stp rel a v0 v1 tk)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.stp rel a v0 v1 tk) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       intro t m ht hm
       obtain ⟨-, -, h3⟩ := storeUnits_roles _ _ 0 s s' hs
       obtain ⟨j, hl, hr⟩ := h3 t m ht hm
       exact .inr (.inl ⟨_, _, _, _, _, _, _, _, j, rfl, ‹_›, ‹_›, role_of_newRole hr,
         by rw [hl, Nat.zero_add]⟩))

theorem evalOp_fetch_new {g : G} {env : Env} {σs : List Ty} {s : St} {o : FetchOp} {acq rel : Bool}
    {a v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNew g env s (.fetch o acq rel a v) m.loc := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
       intro t m ht hm
       have hl := rmw_newLoc hx t m ht hm
       exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl, ‹_›, by rw [hl]; assumption⟩))

/-- **(B5, operation)**: every message an operation appends is at one of its
fresh labels or at an `OpNew` position. -/
theorem evalOp_newOp {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      FreshIn g s.nalloc r.1.nalloc m.loc.label ∨ OpNew g env s op m.loc := by
  intro t m ht hm
  cases op
  case spawn => simp [evalOp] at h
  case store => exact .inr (evalOp_store_new h t m ht hm)
  case xchg => exact .inr (evalOp_xchg_new h t m ht hm)
  case xchgAt => exact .inr (evalOp_xchgAt_new h t m ht hm)
  case xchgAtF => exact .inr (evalOp_xchgAtF_new h t m ht hm)
  case bufInit => exact .inr (evalOp_bufInit_new h t m ht hm)
  case stl => exact .inr (evalOp_stl_new h t m ht hm)
  case stlw => exact .inr (evalOp_stlw_new h t m ht hm)
  case stp => exact .inr (evalOp_stp_new h t m ht hm)
  case fetch => exact .inr (evalOp_fetch_new h t m ht hm)
  all_goals exact (evalOp_new hpl h t m ht hm).imp id (fun ⟨_, ha, _⟩ => by simp [OpTgt] at ha)

/-- (B5) Where a thread step's new message at `loc` can be, operationally. -/
def TermNew (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (loc : Address) : Prop :=
  (∃ x op e, th.term = .let_ x op e ∧ OpNew g th.env (stOf mem pairs th) op loc) ∨
  (∃ acq rel w e v tn ok fail tw pw, th.term = .cas acq rel w e v tn ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ addrOf pw = some loc) ∨
  (∃ acq rel w e0 e1 v0 v1 tn ok fail tw pw A, th.term = .casp acq rel w e0 e1 v0 v1 tn ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ addrOf pw = some A ∧ (loc = A ∨ loc = A.next))

/-- **(B5, thread step, operational)** (`tstep_newRole`): every message a thread
step appends is at one of its fresh labels or at a `TermNew` position. -/
theorem tstep_newOp {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hpl : PromLt (stOf mem pairs th)) (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ TermNew g mem pairs th m.loc := by
  intro t m ht hm
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only at hm; exact absurd (lt_of_get hm) (by omega))
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf] at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (lt_of_get hm) (by omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact (evalOp_newOp hpl hx t m ht hm).imp id (fun h => .inl ⟨_, _, _, hT, h⟩)
         | (split <;> exact (evalOp_newOp hpl hx t m ht hm).imp id (fun h => .inl ⟨_, _, _, hT, h⟩))
         | exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, hT, ‹_›,
             by rw [rmw_newLoc hx t m ht hm]; assumption⟩))
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hT, ‹_›, ‹_›,
              rmwPair_newLoc hx t m ht hm⟩))))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact .inl ((newIn_projInj (X := fun _ => False) hpl hx hy t m ht hm).resolve_right id))

/-- (B5) A typed position for a new message: word `j`, in its role, of the unit
list `us` of a component `U` (at `o`) of its cell's type. -/
def NewPos (η : TEnv) (loc : Address) : Prop :=
  ∃ cl o U us j, η.sto loc.label = some cl ∧ AtOff cl.ty o U ∧ accs U = some us ∧ Role us j ∧
    loc.offset = o + j

theorem newPos_ua {η : TEnv} {b : Address} {us : List Acc} {j : Nat} (h : TermTyped.UnitsAt η b us)
    (hj : Role us j) : NewPos η (offs b j) :=
  let ⟨c, U, hsto, hat, hus⟩ := h; ⟨c, b.offset, U, us, j, hsto, hat, hus, hj, rfl⟩

theorem newPos_sw {η : TEnv} {loc : Address} (h : TermTyped.SWAt η loc) : NewPos η loc :=
  let ⟨cl, o, U, us, j, h1, h2, h3, h4, h5⟩ := h; ⟨cl, o, U, us, j, h1, h2, h3, .inl h4, h5⟩

theorem offs_zero (a : Address) : offs a 0 = a := by cases a; simp [offs]

theorem offs_one (a : Address) : offs a 1 = a.next := rfl

/-- A pair target: a reference or locative to a `word2` or an epoch pair. -/
theorem pair_ua {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {cx : Cx} {env : Env} {a : At} {t : Ty}
    {μ : Mode} {u rt : Ty} {pw : Word} {b : Address} (hvars : VarsOK ρ η σs cx.vars env)
    (hp : cx.peek a = .ok t) (ht : t = .ptr μ u ∨ t = .loc μ u)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hea : evalAt env a = some (rt, [pw])) (hb : addrOf pw = some b) : TermTyped.UnitsAt η b [.two] := by
  obtain ⟨c, U, hsto, hat, hFd⟩ := TermTyped.ptr_target hvars hp ht hea hb
  refine ⟨c, U, hsto, hat, (Fd_accs hFd).trans ?_⟩
  rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [cl, accs]

theorem stp_ua {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c' : Cx} {env : Env} {x : String} {rel : Bool} {a v0 v1 tk : At} {t : Ty} {pw : Word}
    {b : Address} (hop : OpT p cx x (.stp rel a v0 v1 tk) c') (hsc : OpScope cx (.stp rel a v0 v1 tk))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env a = some (t, [pw])) (hb : addrOf pw = some b) :
    TermTyped.UnitsAt η b [.two] := by
  have hp : ∃ t, cx.peek a = .ok t := by cases hop <;> exact ⟨_, ‹_›⟩
  obtain ⟨t', hp⟩ := hp
  obtain ⟨μ, r, P, ht, -⟩ := hsc t' hp
  exact pair_ua hi.2.1 hp ht (.inl ⟨r, P, rfl⟩) hea hb

theorem casp_ua {p : Prog} {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx : Cx} {env : Env} {acq rel : Bool} {w e0 e1 v0 v1 : At} {tn : String} {ok fail : Expr}
    {tw : Ty} {pw : Word} {A : Address}
    (hT : Typed p cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hsc : StepScope cx (.casp acq rel w e0 e1 v0 v1 tn ok fail))
    (hi : FInv ρ η σs K cx env) (hea : evalAt env w = some (tw, [pw])) (hb : addrOf pw = some A) :
    TermTyped.UnitsAt η A [.two] := by
  have hp : ∃ t, cx.peek w = .ok t := by cases hT <;> exact ⟨_, ‹_›⟩
  obtain ⟨t, hp⟩ := hp
  obtain ⟨μ, u, ht, -, hu⟩ := hsc t hp
  exact pair_ua hi.2.1 hp ht hu hea hb

/-- **(B5, thread step, typed)**: every message a typed, in-scope thread's step
appends is at one of its fresh labels or at a `NewPos` of its `Σ`. -/
theorem tstep_newPos {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {r : Memory × List Ts × TTh} (hE : EnvOK p η) (hT : Typed p cx th.term)
    (htv : TvOK cx) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env)
    (hm : MemInv g (CE η) (stOf mem pairs th)) (hsc : StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ NewPos η m.loc := by
  intro t m ht hmt
  refine (tstep_newOp (MemInv_promLt hm) h t m ht hmt).imp id ?_
  rintro (⟨x, op, e, hterm, hn⟩ | ⟨acq, rel, w, e, v, tn, ok, fail, tw, pw, hterm, hea, hb⟩ |
      ⟨acq, rel, w, e0, e1, v0, v1, tn, ok, fail, tw, pw, A, hterm, hea, hb, hl⟩)
  · rw [hterm] at hT hsc
    cases hT with
    | let_ hop _ =>
        rcases hn with ⟨pw, b, rel, us, ws, j, hu, hj, hl⟩ |
            ⟨rel, a, v0, v1, tk, t', pw, b, j, rfl, hea, hb, hj, hl⟩ |
            ⟨o, acq, rel, a, v, t', pw, rfl, hea, hb⟩
        · rw [hl]; exact newPos_ua (TermTyped.unitsOp_ua hop hsc hi hE htv hu) hj
        · rw [hl]; exact newPos_ua (stp_ua hop hsc hi hea hb) hj
        · exact newPos_sw (TermTyped.fetch_sw hop hsc hi hE htv hm hea hb)
  · rw [hterm] at hT hsc
    exact newPos_sw (TermTyped.cas_sw hT hsc hi hE htv hm hea hb)
  · rw [hterm] at hT hsc
    have hua := casp_ua hT hsc hi hea hb
    rcases hl with hl | hl
    · have := newPos_ua hua role_two0; rw [offs_zero] at this; rw [hl]; exact this
    · have := newPos_ua hua role_two1; rw [offs_one] at this; rw [hl]; exact this

/-- **(B5, cut form)**: the same at a thread's `ThInvE` environment. -/
theorem tstep_newPosE {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    {r : Memory × List Ts × TTh} (hE : ThInvE p E th) (hm : MemInv g E (stOf mem pairs th))
    (hsc : ∀ (η : TEnv) (cx : Cx), CE η = E → Typed p cx th.term → StepScope cx th.term)
    (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ NewPos E m.loc := by
  obtain ⟨ρ, η, cx, rfl, hEo, hT, htv, hi, -⟩ := hE
  exact tstep_newPos (η := η) hEo hT htv hi hm (hsc η cx rfl hT) h

/-- Two two-word units of one access list start at the same word or are disjoint. -/
theorem twoAt_twoAt {us : List Acc} {a b : Nat} (ha : TwoAt us a) (hb : TwoAt us b) :
    a = b ∨ a + 2 ≤ b ∨ b + 2 ≤ a := by
  obtain ⟨i, hi, rfl⟩ := ha
  obtain ⟨i', hi', rfl⟩ := hb
  rcases Nat.lt_trichotomy i i' with h | rfl | h
  · have := start_lt hi h; simp only [Acc.size] at this; omega
  · exact .inl rfl
  · have := start_lt hi' h; simp only [Acc.size] at this; omega

/-- **(B5, layout; the `TwoAt` analogue of `oneAt_word2`)**: a two-word unit
of a component `U` (at `o`) of `T` and a `word2` component of `T` (at `o2`)
start at the same word or are disjoint. -/
theorem twoAt_word2 {T U : Ty} {o o2 jj : Nat} {us : List Acc} {r : Idx} {P : Proto2}
    (h1 : AtOff T o U) (hus : accs U = some us) (hj : TwoAt us jj) (h2 : AtOff T o2 (.word2 r P)) :
    o + jj = o2 ∨ o + jj + 2 ≤ o2 ∨ o2 + 2 ≤ o + jj := by
  have hjl := TwoAt_lt hj
  have n2 : nWords [Acc.two] = 2 := rfl
  rcases AtOff_nest (Solid_word2 r P) accs_word2 h1 hus h2 with h | h | ⟨hle, h⟩
  · rw [n2] at h; omega
  · omega
  · obtain ⟨pre, post, e, hn⟩ := AtOff_embed h hus accs_word2
    have h2' : TwoAt us (o2 - o) := by
      have := TwoAt_embed (pre := pre) (post := post) (us := [Acc.two]) (j := 0) ⟨0, rfl, rfl⟩
      rw [hn, Nat.add_zero, ← e] at this; exact this
    rcases twoAt_twoAt hj h2' with h | h | h <;> omega

/-- **(B5, every append)**: a `NewPos` lies within its cell's words (`wc`), and
if it lies in a `word2` unit of the cell's type (at `o2`), it is a word of a
two-word unit (of a component at `o`) starting exactly there. -/
theorem newPos_b5 {η : TEnv} {loc : Address} (h : NewPos η loc) :
    ∃ cl, η.sto loc.label = some cl ∧ (∀ n, wc cl.ty = some n → loc.offset < n) ∧
      ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → (loc.offset = o2 ∨ loc.offset = o2 + 1) →
        ∃ o U us jj, AtOff cl.ty o U ∧ accs U = some us ∧ TwoAt us jj ∧ o + jj = o2 := by
  obtain ⟨cl, o, U, us, j, hsto, hat, hus, hj, hoff⟩ := h
  -- `Offset` is an `abbrev` for `Nat`, but `omega` only reads facts stated at `Nat`.
  obtain ⟨x, hx⟩ : ∃ x : Nat, loc.offset = x := ⟨_, rfl⟩
  have hoff' : x = o + j := hx ▸ hoff
  refine ⟨cl, hsto, fun n hn => ?_, fun o2 r P h2 hin => ?_⟩
  · suffices hx' : x < n by rw [hx]; exact hx'
    obtain ⟨L, hL, rfl⟩ := wc_some hn
    obtain ⟨pre, post, e, hpre⟩ := AtOff_embed hat hL hus
    have h1 := role_lt hj
    have h2 : nWords L = nWords pre + nWords us + nWords post := by
      rw [e]; simp only [nWords, List.map_append, List.sum_append]
    omega
  · have hin' : x = o2 ∨ x = o2 + 1 := hx ▸ hin
    clear hoff hin hx
    rcases hj with hj | hj | ⟨jj, rfl, hj⟩
    · have := TermGlob.oneAt_word2 hat hus hj h2; omega
    · exact ⟨o, U, us, j, hat, hus, hj, by rcases twoAt_word2 hat hus hj h2 with h | h | h <;> omega⟩
    · exact ⟨o, U, us, jj, hat, hus, hj, by rcases twoAt_word2 hat hus hj h2 with h | h | h <;> omega⟩

/-- **(B5, system)**: under `SysInvW` and the step's scope, every message a step
of thread `i` appends is at a fresh label of `i`, or in a cell of `i`'s cut,
within its words, and inside a `word2` unit only as a word of a two-word unit
starting there. -/
theorem stepper_newPos {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    (hsc : ∀ (η : TEnv) (cx : Cx) (S' : AllocLabel → Prop), CE η = Cut Eg i S' → Typed p cx th.term →
      StepScope cx th.term) :
    ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → r.1[t]? = some m →
      FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label ∨
        ∃ cl, cutSto Eg i m.loc.label = some cl ∧ (∀ n, wc cl.ty = some n → m.loc.offset < n) ∧
          ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → (m.loc.offset = o2 ∨ m.loc.offset = o2 + 1) →
            ∃ o U us jj, AtOff cl.ty o U ∧ accs U = some us ∧ TwoAt us jj ∧ o + jj = o2 := by
  obtain ⟨S0, -, hE0, hm0, -⟩ := h.thread hth
  intro t m ht hmt
  exact (tstep_newPosE hE0 hm0 (fun η cx he hT => hsc η cx S0 he hT) hr t m ht hmt).imp id newPos_b5

/-! ## (B2) New messages at initialised offsets of shared cells are typed -/

/-- **(B2, another thread's shared cell)**: in the post state of a step (any
`MemInv` at the new memory), a message appended by the step (`t` at or past
the old size, not a promise) at an initialised offset of another thread's
shared cell whose frontier is at most the old size (`hfb`) is `WordOK`
(`PubDefP`: an untyped message would be hidden by a later one at or below the
frontier). -/
theorem newMsg_wordOK_other {g : G} {E : TEnv} {s' : St} {n0 : Nat} {l : AllocLabel} {cl : Cell} {f : Ts}
    {o t : Nat} {m : Msg} (hm : MemInv g E s') (hsto : E.sto l = some cl) (hown : cl.owner ≠ some E.tid)
    (hf : E.pfr l = some f) (hfb : f ≤ n0) (hi : InitR E cl l o) (ht : n0 ≤ t) (hnp : t ∉ s'.promises)
    (hmt : s'.mem[t]? = some m) (hloc : m.loc = ⟨l, o⟩) : WordOK E cl.ty o (mw m) :=
  Classical.byContradiction fun hno => by
    obtain ⟨t', m', h1, h2, -, -⟩ := hm.2.2.2.2.2.2.1 l cl f hsto hown hf o hi t m hnp hmt hloc hno
    exact absurd (Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 hfb)) (Nat.not_lt.2 ht)

/-- **(B2, own cell, above coherence)**: a non-promise message of the
thread's own shared (frontier-carrying) cell above the thread's coherence at
its address is `TypedAt` (`LatestSF`), provided the cell's word list covers
the offset (`hcov`). -/
theorem newMsg_wordOK_own {g : G} {E : TEnv} {s' : St} {l : AllocLabel} {cl : Cell} {o t : Nat} {m : Msg}
    (hm : MemInv g E s') (hsto : E.sto l = some cl) (hown : cl.owner = some E.tid)
    (hcov : ∀ vals, CellOK E (E.rc l) cl.ty vals → o < vals.length)
    (hlt : s'.vs.coh ⟨l, o⟩ < t) (hnp : t ∉ s'.promises) (hmt : s'.mem[t]? = some m)
    (hloc : m.loc = ⟨l, o⟩) : WordOK E cl.ty o (mw m) := by
  obtain ⟨vals, hc, hl, -⟩ := hm.2.1 l cl hsto hown
  obtain ⟨v, hv⟩ : ∃ v, vals[o]? = some v := ⟨_, List.getElem?_eq_getElem (hcov vals hc)⟩
  rcases (hl o v hv).2.2 t m hlt hmt hloc with hp | ⟨-, hty⟩
  · exact absurd hp hnp
  · unfold TypedAt at hty; rw [hloc] at hty; exact hty

/-- (B2) A cut's typing of a `noOR` cell's word moves to `PubE`. -/
theorem wordOK_pub {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {T : Ty} (hT : noOR T = true)
    {o : Nat} {w : Word} (h : WordOK (Cut Eg i S) T o w) : WordOK (PubE Eg) T o w :=
  WordOK_transferS (InclS_cut_pub Eg i S) hT h

/-! ## (S8b) `vWr` stays within memory (`VWrLe`)

A thread step raises `vWr` only to a timestamp it writes or fulfils, so it
stays below the new memory size.  The framework mirrors `TermLiveProps.Mono`. -/

/-- A step keeps `vWr` within memory. -/
def VMono (s s' : St) : Prop := s.vs.vWr ≤ s.mem.size → s'.vs.vWr ≤ s'.mem.size

@[simp] theorem VMono.refl' (s : St) : VMono s s := id

theorem VMono.trans {s1 s2 s3 : St} (a : VMono s1 s2) (b : VMono s2 s3) : VMono s1 s3 := fun h => b (a h)

theorem stepFence_vWr (th : Promises.Thread) (f : WeakMem.Fence) :
    (Promises.stepFence th f).vs.vWr = th.vs.vWr := by
  cases f <;> rfl

theorem lockFence_vWr (arch : Arch) (x : Promises.Thread) :
    (if arch = .tso then Promises.stepFence x .sy else x).vs.vWr = x.vs.vWr := by
  split
  · exact stepFence_vWr x _
  · rfl

@[simp] theorem fenceS_vmono (s : St) (f : WeakMem.Fence) : VMono s (fenceS s f) := fun h => by
  cases f <;> exact h

theorem loadUnits_vmono (arch : Arch) (pw : Word) (a : Address) (acq : Bool) (us : List Acc) (k : Nat) (s : St)
    {s' : St} {ws : List Word} (h : (s', ws) ∈ loadUnits arch pw a acq us k s) : VMono s s' := fun hv => by
  have e1 := (loadUnits_keep us k s (s', ws) h).1
  have e2 := loadUnits_vWr us k s (s', ws) h
  simp only at e1 e2
  rw [e1, e2]; exact hv

theorem storeUnits_vmono (k : Promises.Knobs) (arch : Arch) (pw : Word) (a : Address) (rel : Bool) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s : St) {s' : St},
    s' ∈ storeUnits k arch pw a rel us ws i s → VMono s s'
  | [], ws, i, s, s', h => by
      simp only [storeUnits, List.mem_singleton] at h
      subst h; exact VMono.refl' _
  | .one :: us, [], i, s, s', h => by simp [storeUnits] at h
  | .one :: us, w :: ws, i, s, s', h => by
      simp only [storeUnits, List.mem_flatMap] at h
      obtain ⟨⟨mem', th⟩, hst, hin⟩ := h
      refine VMono.trans ?_ (storeUnits_vmono k arch pw a rel us ws _ _ hin)
      intro hv
      obtain ⟨t, hc, -, -, hw⟩ := stepStore_casesC hst
      show th.vs.vWr ≤ mem'.size
      rw [hw]
      refine Nat.max_le.2 ⟨?_, ?_⟩
      · rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
        · simp only [Array.size_push]; exact Nat.le_succ_of_le hv
        · exact hv
      · rcases hc with ⟨rfl, rfl, -⟩ | ⟨rfl, -, -, -, m, hm, -⟩
        · simp only [Array.size_push]; exact Nat.le_succ _
        · exact Nat.le_of_lt (lt_of_get hm)
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
      refine VMono.trans ?_ (storeUnits_vmono k arch pw a rel us ws _ _ h)
      intro hv
      show th.vs.vWr ≤ mem'.size
      simp only at q1 q6
      rw [q6, q1]; simp only [Array.size_push]
      exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩

theorem alloc_vmono {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s s' : St} {pw : Word} (h : (s', pw) ∈ alloc k arch lbl us ws s) : VMono s s' := by
  simp only [alloc, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨s2, hs2, rfl, rfl⟩ := h
  refine VMono.trans ?_ (storeUnits_vmono k arch _ _ false us ws 0 _ hs2)
  intro hv
  dsimp only
  rw [fold_size]
  exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩

@[simp] theorem allocBuf_vmono (lbl : AllocLabel) (n : Nat) (zero : Option (List WeakMem.Val)) (s : St) :
    VMono s (allocBuf lbl n zero s).1 := fun hv => by
  dsimp only [allocBuf]
  rw [fold_size]
  exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), by omega⟩

theorem stepRmw_vmono_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hv : th.vs.vWr ≤ mem.size) : th'.vs.vWr ≤ mem'.size := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, -, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [lockFence_vWr]; exact hv
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [lockFence_vWr]; simp only [Array.size_push]
        exact Nat.max_le.2 ⟨Nat.le_succ_of_le hv, Nat.le_succ _⟩
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨-, rfl, rfl⟩ := hf
          rw [lockFence_vWr]; exact Nat.max_le.2 ⟨hv, Nat.le_of_lt (lt_of_get hm)⟩

theorem stepRmw_vmono {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hv : th.vs.vWr ≤ mem.size) : th'.vs.vWr ≤ mem'.size := by
  exact stepRmw_vmono_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [lockFence_vWr]; exact hv)

theorem stepRmwPair_vmono_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hv : th.vs.vWr ≤ mem.size) : th'.vs.vWr ≤ mem'.size := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [lockFence_vWr]; exact hv
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rw [lockFence_vWr]; simp only [Array.size_push]
      exact Nat.max_le.2 ⟨Nat.le_trans hv (by omega), Nat.le_succ _⟩
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      rw [lockFence_vWr]; exact Nat.max_le.2 ⟨hv, Nat.le_of_lt (lt_of_get (by assumption))⟩
    · cases hf

theorem stepRmwPair_vmono {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈ Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hv : th.vs.vWr ≤ mem.size) : th'.vs.vWr ≤ mem'.size := by
  exact stepRmwPair_vmono_at (th := if arch = .tso then Promises.stepFence th .sy else th) h (by rw [lockFence_vWr]; exact hv)

theorem rmw_vmono {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs (mth s r0 r1 r2) dst a cmp newv deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : VMono s s' := fun hw => by
  rw [hm, hv]; exact stepRmw_vmono h (by rw [← hs]; exact hw)

theorem rmwPair_vmono {arch : Arch} {mem : Memory} {pairs : List Ts} {s s' : St}
    {r0 r1 r2 : Word} {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs (mth s r0 r1 r2) d0 d1 a c0 c1 n0 n1 deps acq rel)
    (hm : s'.mem = mem') (hv : s'.vs = th'.vs) (hs : s.mem = mem) : VMono s s' := fun hw => by
  rw [hm, hv]; exact stepRmwPair_vmono h (by rw [← hs]; exact hw)

macro "flatVW" : tactic => `(tactic|
  simp (config := {contextual := true}) only [ol, Option.mem_toList,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, List.mem_map, List.mem_flatMap,
    List.mem_filterMap, List.mem_singleton, List.not_mem_nil, Prod.exists,
    Prod.mk.injEq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, forall_eq',
    Option.some.injEq, Option.pure_def, Option.bind_some, reduceCtorEq, false_implies,
    implies_true, VMono.refl', fenceS_vmono, allocBuf_vmono, Option.toList_none, Option.toList_some,
    Option.bind_none, Option.map_none, Option.map_some, Option.mem_def,
    Option.bind_eq_bind, Option.map_eq_map, Option.ite_none_left_eq_some, Option.ite_none_right_eq_some])

macro "closeVW" : tactic => `(tactic| first
    | done
    | exact VMono.refl' _
    | exact fenceS_vmono _ _
    | exact allocBuf_vmono _ _ _ _
    | exact loadUnits_vmono _ _ _ _ _ _ _ (by assumption)
    | exact storeUnits_vmono _ _ _ _ _ _ _ _ _ (by assumption)
    | exact alloc_vmono (by assumption)
    | exact VMono.trans (loadUnits_vmono _ _ _ _ _ _ _ (by assumption))
        (storeUnits_vmono _ _ _ _ _ _ _ _ _ (by assumption))
    | exact VMono.trans (alloc_vmono (by assumption)) (fenceS_vmono _ _)
    | exact VMono.trans (loadUnits_vmono _ _ _ _ _ _ _ (by assumption))
        (loadUnits_vmono _ _ _ _ _ _ _ (by assumption)))

macro "crushVW1" : tactic => `(tactic| (
  repeat' split
  all_goals (try flatVW)
  all_goals (try intros)
  all_goals (try subst_vars)
  all_goals (try closeVW)))

macro "crushVW" : tactic => `(tactic| (
  intro r hin
  revert hin
  crushVW1
  all_goals (try (rename_i hh; revert hh; crushVW1))
  all_goals (try (rename_i hh; revert hh; crushVW1))))

theorem projM_vmono (g : G) (s : St) (t : Ty) (ws : List Word) :
    ∀ r ∈ projM g s t ws, VMono s r.1 := by
  unfold projM
  crushVW

theorem injM_vmono (g : G) (s : St) (t : Ty) (j : Nat) (p : List Word) :
    ∀ r ∈ injM g s t j p, VMono s r.1 := by
  unfold injM
  crushVW

theorem evalOp_vmono (g : G) (env : Env) (σs : List Ty) (s : St) (op : Op) :
    ∀ r ∈ evalOp g env σs s op, VMono s r.1 := by
  cases op <;> simp only [evalOp]
  all_goals crushVW
  all_goals first
    | exact VMono.trans (projM_vmono _ _ _ _ _ (by assumption)) (injM_vmono _ _ _ _ _ _ (by assumption))
    | exact rmw_vmono (by assumption) (by rfl) (by rfl) (by rfl)

theorem enter_vmono {g : G} {mem : Memory} {pairs : List Ts} {th th0 th' : TTh} {f : String}
    {ts : List Ty} {a : At} (h : enter g th0 f ts a = some th') (hv : th0.vs = th.vs) :
    VMono (stOf mem pairs th) (stOf mem pairs th') := fun hw => by
  have e : th'.vs = th.vs := (TermLiveProps.enter_vs h).trans hv
  show th'.vs.vWr ≤ mem.size
  rw [e]; exact hw

/-- A thread step keeps `vWr` within memory. -/
theorem tstep_vmono (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) :
    ∀ r ∈ tstep g mem pairs th, VMono (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  unfold tstep
  crushVW
  all_goals first
    | exact evalOp_vmono _ _ _ _ _ _ (by assumption)
    | exact VMono.trans (projM_vmono _ _ _ _ _ (by assumption)) (injM_vmono _ _ _ _ _ _ (by assumption))
    | exact enter_vmono (by assumption) (by rfl)
    | exact rmw_vmono (by assumption) (by rfl) (by rfl) (by rfl)
    | exact rmwPair_vmono (by assumption) (by rfl) (by rfl) (by rfl)

theorem tstep_vWr {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hr : r ∈ tstep g mem pairs th) (hv : th.vs.vWr ≤ mem.size) : r.2.2.vs.vWr ≤ r.1.size :=
  tstep_vmono g mem pairs th r hr hv

/-! ## (S8b) The bookkeeping clauses of `SysInvW`: trivial cases, promise step, thread step -/

section
variable {Eg : GEnv} {c c' : Cfg} {j : Nat} {th th' : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}

/-- (S8b) `PromsDisj` with no promises. -/
theorem PromsDisj_init (h : ∀ (i : Nat) (thi : TTh), c.ths[i]? = some thi → thi.promises = []) : PromsDisj c :=
  fun i _ thi _ _ _ hi _ ht _ => by rw [h i thi hi] at ht; cases ht

/-- (S8b) `FpOwnFree` with no promises. -/
theorem FpOwnFree_init (h : ∀ (i : Nat) (thi : TTh), c.ths[i]? = some thi → thi.promises = []) : FpOwnFree Eg c :=
  fun i thi _ hi _ ht => by rw [h i thi hi] at ht; cases ht

/-- (S8b) `AllPromLt` with no promises. -/
theorem AllPromLt_init (h : ∀ (i : Nat) (thi : TTh), c.ths[i]? = some thi → thi.promises = []) : AllPromLt c :=
  fun i thi _ hi ht => by rw [h i thi hi] at ht; cases ht

/-- (S8b) `VWrLe` when no thread has written. -/
theorem VWrLe_init (h : ∀ (i : Nat) (thi : TTh), c.ths[i]? = some thi → thi.vs.vWr = 0) : VWrLe c :=
  fun i thi hi => by rw [h i thi hi]; exact Nat.zero_le _

theorem VWrLe_promise (hl : VWrLe c) (hj : c.ths[j]? = some th) : VWrLe (promise c j a v w) := by
  intro i thi hi
  rw [(promise_inv (a := a) (v := v) (w := w) hj).1] at hi ⊢
  simp only [Array.size_push]
  by_cases hij : i = j
  · subst hij
    rw [arr_get_set_eq _ hj] at hi; cases hi
    exact Nat.le_succ_of_le (hl _ th hj)
  · rw [arr_get_set_ne _ _ (Ne.symm hij)] at hi
    exact Nat.le_succ_of_le (hl _ _ hi)

theorem VWrLe_thread (hl : VWrLe c) (hj' : c'.ths[j]? = some th') (ho : ∀ i, i ≠ j → c'.ths[i]? = c.ths[i]?)
    (hv : th'.vs.vWr ≤ c'.mem.size) (hsz : c.mem.size ≤ c'.mem.size) : VWrLe c' := by
  intro i thi hi
  by_cases hij : i = j
  · subst hij; rw [hj'] at hi; cases hi; exact hv
  · rw [ho i hij] at hi; exact Nat.le_trans (hl _ _ hi) hsz

/-- (S8b) `FrontierLe` with no frontiers. -/
theorem FrontierLe_init {n : Nat} (h : ∀ l, Eg.pfr l = none) : FrontierLe Eg n :=
  fun l _ f _ hf => by rw [h l] at hf; cases hf

theorem FrontierLe_mono {n n' : Nat} (h : FrontierLe Eg n) (hn : n ≤ n') : FrontierLe Eg n' :=
  fun l cl f hs hf => Nat.le_trans (h l cl f hs hf) hn

theorem FrontierLe_withFp {n : Nat} {f : Nat → List Ts} : FrontierLe (Eg.withFp f) n ↔ FrontierLe Eg n :=
  Iff.rfl

/-- (S8b) `FrontierLe` across a global step whose new frontier (`v`, the old
`vWr`) is within the old bound. -/
theorem FrontierLe_gfoot {g : G} {Eg' : GEnv} {n n' : Nat} {v M M' : Nat} (hf : GFoot g Eg Eg' n n' v)
    (h : FrontierLe Eg M) (hv : v ≤ M) (hM : M ≤ M') : FrontierLe Eg' M' := by
  intro l cl f hs hp
  rcases hf.2.2.2.2.1 l with e | ⟨-, f0, e, hf0, -⟩ | ⟨-, -, e⟩
  · rw [e] at hp
    rcases hf.2.1 l with e' | ⟨-, -, e', -⟩
    · rw [e'] at hs; exact Nat.le_trans (h l cl f hs hp) hM
    · rw [e'] at hp; cases hp
  · rw [e] at hp; cases hp; exact Nat.le_trans hf0 (Nat.le_trans hv hM)
  · rw [e] at hs; cases hs

/-- (frlt) **The strict frontier bound after a thread step**: an old frontier keeps its bound; the
step's new frontier (`EFootB`'s publish clause) is at most the old `vWr` or below the old size. -/
theorem FrontierLt_post {g : G} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St} {M' : Nat}
    (hf : EFoot g (Cut Eg g.i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc)
    (hvz : s.vs.vWr ≤ s.mem.size - 1) (h : FrontierLe Eg (s.mem.size - 1)) (hM : s.mem.size ≤ M') :
    FrontierLe (Eg.post g s.nalloc s'.nalloc E') (M' - 1) := by
  have G := EFoot_post hf hfr (Nat.le_trans hvz (Nat.sub_le _ _))
  have hM1 : s.mem.size - 1 ≤ M' - 1 := Nat.sub_le_sub_right hM 1
  obtain ⟨_, _, _, _, _, hpfr, -⟩ := hf
  intro l cl f hs hp
  change E'.pfr l = some f at hp
  rcases hpfr l with e | ⟨-, F, e, -, -, -, -, -, -, hlt⟩ | ⟨hF, -, e⟩
  · rw [e] at hp
    change Eg.pfr l = some f at hp
    rcases G.2.1 l with e' | ⟨-, -, hp0, -⟩
    · rw [e'] at hs; exact Nat.le_trans (h l cl f hs hp) hM1
    · rw [hp0] at hp; cases hp
  · rw [e] at hp; cases hp
    rcases hlt with hlt | hlt
    · exact Nat.le_trans hlt (Nat.le_trans hvz hM1)
    · exact Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le hlt hM)
  · rw [post_sto_fresh hF, e] at hs; cases hs

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
  {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}

/-- **(S8b) The bookkeeping clauses after a promise step** of thread `j`
(`E_g` gains `fpProm`; memory grows by one, `pfr`/`sto` unchanged). -/
theorem SysInvW.book_promise (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (hj : c.ths[j]? = some th) :
    PromsOK (Eg.withFp (fpProm Eg j c.mem.size)) (promise c j a v w) ∧ PromsDisj (promise c j a v w) ∧
      AllPromLt (promise c j a v w) ∧ FpOwnFree (Eg.withFp (fpProm Eg j c.mem.size)) (promise c j a v w) ∧
      VWrLe (promise c j a v w) ∧
      FrontierLe (Eg.withFp (fpProm Eg j c.mem.size)) (promise c j a v w).mem.size := by
  have hsz : c.mem.size ≤ (promise c j a v w).mem.size := by
    rw [(promise_inv (a := a) (v := v) (w := w) hj).1]; simp only [Array.size_push]; exact Nat.le_succ _
  exact ⟨PromsOK_promise h.proms hj, PromsDisj_promise h.disj h.plt hj, AllPromLt_promise h.plt hj,
    FpOwnFree_promise h.proms h.fpfree h.plt hj, VWrLe_promise h.vwr hj, FrontierLe_mono h.frle hsz⟩

/-- **(S8b) The bookkeeping clauses after a thread step** of thread `i`
(`E_g` gains `fpSync`; the frontier clause is `SysInvW.frle_thread`). -/
theorem SysInvW.book_thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {c' : Cfg}
    (hc' : c' ∈ threadSteps p k arch c i) :
    PromsOK (Eg.withFp (fpSync Eg c')) c' ∧ PromsDisj c' ∧ AllPromLt c' ∧
      FpOwnFree (Eg.withFp (fpSync Eg c')) c' ∧ VWrLe c' := by
  obtain ⟨th, r, hth, hr, e1, -, e3, ho⟩ := threadSteps_upd hc'
  obtain ⟨S0, -, -, hm0, -⟩ := h.thread hth
  have hsub : ∀ t, t ∈ r.2.2.promises → t ∈ th.promises := fun t ht =>
    (TermFul.tstep_fulfil (fun t ht => h.plt i th t hth ht) (MemInv_nopair hm0) hr).1.subset ht
  have hsz : c.mem.size ≤ c'.mem.size := by
    rw [e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r hr).mem.size
  have hv : r.2.2.vs.vWr ≤ c'.mem.size := by rw [e1]; exact tstep_vWr hr (h.vwr i th hth)
  exact ⟨PromsOK_thread h.proms h.disj hth e3 ho hsub, PromsDisj_thread h.disj hth e3 ho hsub,
    AllPromLt_thread h.plt hth e3 ho hsub hsz, FpOwnFree_thread h.fpfree hth e3 ho hsub,
    VWrLe_thread h.vwr e3 ho hv hsz⟩

/-- **(S8b) `FrontierLe` after a thread step** of thread `i` with S6 witness
`E'`: the one frontier the step may set is the old `vWr` (`VWrLe`). -/
theorem SysInvW.frle_thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    {S : AllocLabel → Prop} {E' : TEnv}
    (hf : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2)) :
    FrontierLe (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') r.1.size :=
  FrontierLe_gfoot (EFoot_post (g := gOf p k arch c i) hf (SysInvW.gfresh h hth r.2.2.nalloc) (h.vwr i th hth))
    h.frle (Nat.le_refl _) (TermLiveProps.tstep_ext _ _ _ _ r hr).mem.size

/-- (F2′ step 3, RiniLe) **`rini ≤ ini` after a thread step** of thread `i`
with S6 witness `E'` (`EFoot`'s transport from the cut). -/
theorem SysInvW.rle_thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {g : G}
    {S : AllocLabel → Prop} {E' : TEnv} {s s' : St} {n n' : Nat} (hf : EFoot g (Cut Eg i S) E' s s') :
    ∀ l, (Eg.post g n n' E').rini l ≤ (Eg.post g n n' E').ini l :=
  hf.2.2.2.2.2.2.2.2.2.2.1 h.rle

/-- (F2′ step 3, RiniLe) `rini ≤ ini` at a thread's cut: the plant's `hrl`. -/
theorem SysInvW.rle_cut (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (i : Nat)
    (S : AllocLabel → Prop) (l : AllocLabel) : (Cut Eg i S).rini l ≤ (Cut Eg i S).ini l :=
  h.rle l

/-- (F2′ step 3, RiniLe) A promise step's `E_g` (`withFp`) keeps `rini ≤ ini`. -/
theorem SysInvW.rle_withFp (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (f : Nat → List Ts) :
    ∀ l, (Eg.withFp f).rini l ≤ (Eg.withFp f).ini l :=
  h.rle

/-- (U3) **A box payload at a thread's cut names no label any
thread has yet to allocate**: payload labels are allocated in `E_g`
(`BoxNamed_cut`), yet-to-allocate labels are globally fresh (`SysInvW.fresh`). -/
theorem SysInvW.bnamed_cut (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    {S : AllocLabel → Prop} {l : AllocLabel} {B : Box} (hB : (Cut Eg i S).box l = some B) {w : Word}
    (hw : w ∈ B.pay) {a : Address} {g : Nat} (e : w.val = .loc a g) {i' : Nat} {th : TTh}
    (hth : c.ths[i']? = some th) {j : Nat} (hj : th.nalloc ≤ j) :
    a.label ≠ freshLabel c.lbase c.n i' j := by
  intro ha
  obtain ⟨h1, h2, -⟩ := h.fresh i' th hth j hj
  rw [← ha] at h1 h2
  rcases BoxNamed_cut h.bnamed hB hw e with ⟨c', hc⟩ | ⟨B', hB'⟩
  · rw [h1] at hc; cases hc
  · rw [h2] at hB'; cases hB'

/-- (U3) A promise step's `E_g` (`withFp`) keeps `GBoxNamed`. -/
theorem SysInvW.bnamed_withFp (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (f : Nat → List Ts) :
    GBoxNamed (Eg.withFp f) :=
  h.bnamed

/-- (S8b A1) `fpok_of` from the clauses: what remains is `hv`. -/
theorem SysInvW.fpokOf (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db)
    (hv : ∀ (i i' : Nat) (th th' : TTh) (t : Ts) (m : Msg) (S : AllocLabel → Prop), i ≠ i' → c.ths[i]? = some th →
      c.ths[i']? = some th' → t ∈ th'.promises → c.mem[t]? = some m → Vis (Cut Eg i S) m.loc.label) :
    ∀ (i : Nat) (th : TTh) (S : AllocLabel → Prop), c.ths[i]? = some th → FpOK (Cut Eg i S) (stOf c.mem c.pairs th) :=
  fpok_of h.proms h.fpfree h.plt hv

end

/-! ## (B2) Own cells: a step writes each old address at most once

`OnceIn s s' X`: two messages of `s'` past `s`'s memory at the same address
outside `X` are the same message.  A store writes distinct offsets
(`storeUnits_once`), an RMW one word, a `casp` two distinct words; an
allocation writes only at fresh labels. -/

/-- Two new messages at one address (outside `X`) are one. -/
def OnceIn (s s' : St) (X : AllocLabel → Prop) : Prop :=
  ∀ (t1 t2 : Nat) (m1 m2 : Msg), s.mem.size ≤ t1 → s.mem.size ≤ t2 → s'.mem[t1]? = some m1 →
    s'.mem[t2]? = some m2 → m1.loc = m2.loc → ¬ X m1.loc.label → t1 = t2

theorem OnceIn.of_eq {s s' : St} {X : AllocLabel → Prop} (h : s'.mem = s.mem) : OnceIn s s' X :=
  fun t1 _ m1 _ h1 _ hm1 _ _ _ => by rw [h] at hm1; exact absurd (lt_of_get hm1) (by omega)

theorem OnceIn.of_newInF {s s' : St} {X : AllocLabel → Prop} (h : NewIn s s' (fun L => X L ∨ False)) :
    OnceIn s s' X :=
  fun t1 _ m1 _ h1 _ hm1 _ _ hx => absurd ((h t1 m1 h1 hm1).resolve_right id) hx

theorem OnceIn.left {s s1 s2 : St} {X : AllocLabel → Prop} (he : s1.mem = s.mem) (h : OnceIn s1 s2 X) :
    OnceIn s s2 X := fun t1 t2 m1 m2 h1 h2 => h t1 t2 m1 m2 (by rw [he]; exact h1) (by rw [he]; exact h2)

theorem offs_inj {a : Address} {x y : Nat} (h : offs a x = offs a y) : x = y :=
  Classical.byContradiction fun hn => TermMem.offs_ne a hn h

/-- **A store writes each address at most once.** -/
theorem storeUnits_once {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ (t1 t2 : Nat) (m1 m2 : Msg), s.mem.size ≤ t1 → s.mem.size ≤ t2 → s'.mem[t1]? = some m1 →
        s'.mem[t2]? = some m2 → m1.loc = m2.loc → t1 = t2
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t1 _ m1 _ h1 _ hm1; exact absurd (lt_of_get hm1) (by omega)
  | .one :: us, [], _, _, _, hs => by simp [storeUnits] at hs
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      have IH := storeUnits_once us ws (i + 1) _ s' hs
      obtain ⟨-, g2, g3⟩ := storeUnits_roles us ws (i + 1) _ s' hs
      obtain ⟨t, hc, -⟩ := stepStore_casesC hst
      have hsz : mem'.size ≤ s.mem.size + 1 := by
        rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
        · simp only [Array.size_push]; exact Nat.le_refl _
        · exact Nat.le_succ _
      have key : ∀ (t' : Nat) (m : Msg), s.mem.size ≤ t' → s'.mem[t']? = some m →
          (t' < mem'.size ∧ m.loc = offs a (i + (t' - s.mem.size))) ∨
          (mem'.size ≤ t' ∧ ∃ j, m.loc = offs a (i + 1 + j)) := by
        intro t' m ht hm
        by_cases hlt : t' < mem'.size
        · refine .inl ⟨hlt, ?_⟩
          have e := g2 t' hlt
          rw [hm] at e
          dsimp only at e
          rcases hc with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
          · simp only [Array.size_push] at hlt
            obtain rfl : t' = s.mem.size := by omega
            rw [Array.getElem?_push_size] at e
            cases e
            simp
          · omega
        · obtain ⟨j, hj, -⟩ := g3 t' m (by show mem'.size ≤ t'; omega) hm
          exact .inr ⟨by omega, j, hj⟩
      intro t1 t2 m1 m2 h1 h2 hm1 hm2 hl
      rcases key t1 m1 h1 hm1 with ⟨a1, b1⟩ | ⟨a1, j1, b1⟩ <;>
        rcases key t2 m2 h2 hm2 with ⟨a2, b2⟩ | ⟨a2, j2, b2⟩
      · have := offs_inj (b1.symm.trans (hl.trans b2)); omega
      · have := offs_inj (b1.symm.trans (hl.trans b2)); omega
      · have := offs_inj (b1.symm.trans (hl.trans b2)); omega
      · exact IH t1 t2 m1 m2 a1 a2 hm1 hm2 hl
  | .two :: us, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: us, [_], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      obtain ⟨-, ⟨x0, x1, q1, hx0, hx1⟩, -⟩ := TermFul.stepStorePair_shape s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      unfold storeUnits at hs
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel = q at hs q1
      obtain ⟨mem', pairs', th⟩ := q
      simp only at q1
      subst q1
      have IH := storeUnits_once us ws (i + 2) _ s' hs
      obtain ⟨-, g2, g3⟩ := storeUnits_roles us ws (i + 2) _ s' hs
      have key : ∀ (t' : Nat) (m : Msg), s.mem.size ≤ t' → s'.mem[t']? = some m →
          (t' < s.mem.size + 2 ∧ m.loc = offs a (i + (t' - s.mem.size))) ∨
          (s.mem.size + 2 ≤ t' ∧ ∃ j, m.loc = offs a (i + 2 + j)) := by
        intro t' m ht hm
        by_cases hlt : t' < s.mem.size + 2
        · refine .inl ⟨hlt, ?_⟩
          have e := g2 t' (by simp only [Array.size_push]; omega)
          rw [hm] at e
          dsimp only at e
          rcases Nat.lt_or_ge t' (s.mem.size + 1) with h0 | h0
          · obtain rfl : t' = s.mem.size := by omega
            rw [TermLiveProps.push2_fst] at e
            cases e
            rw [hx0]; simp
          · obtain rfl : t' = s.mem.size + 1 := by omega
            rw [TermLiveProps.push2_snd] at e
            cases e
            rw [hx1, offs_next]; simp
        · obtain ⟨j, hj, -⟩ := g3 t' m (by simp only [Array.size_push]; omega) hm
          exact .inr ⟨by omega, j, hj⟩
      intro t1 t2 m1 m2 h1 h2 hm1 hm2 hl
      rcases key t1 m1 h1 hm1 with ⟨a1, b1⟩ | ⟨a1, j1, b1⟩ <;>
        rcases key t2 m2 h2 hm2 with ⟨a2, b2⟩ | ⟨a2, j2, b2⟩
      · have := offs_inj (b1.symm.trans (hl.trans b2)); omega
      · have := offs_inj (b1.symm.trans (hl.trans b2)); omega
      · have := offs_inj (b1.symm.trans (hl.trans b2)); omega
      · exact IH t1 t2 m1 m2 (by simp only [Array.size_push]; omega) (by simp only [Array.size_push]; omega)
          hm1 hm2 hl

theorem storeUnits_onceIn {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} {X : AllocLabel → Prop}
    (hs : s' ∈ storeUnits k arch pw a rel us ws i s) : OnceIn s s' X :=
  fun t1 t2 m1 m2 h1 h2 hm1 hm2 hl _ => storeUnits_once us ws i s s' hs t1 t2 m1 m2 h1 h2 hm1 hm2 hl

/-- An RMW appends at most one message. -/
theorem rmw_once {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {x : Memory × Promises.Thread}
    (h : x ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) :
    ∀ (t1 t2 : Nat) (m1 m2 : Msg), mem.size ≤ t1 → mem.size ≤ t2 → x.1[t1]? = some m1 → x.1[t2]? = some m2 →
      t1 = t2 := by
  obtain ⟨mem', th'⟩ := x
  intro t1 t2 m1 m2 h1 h2 hm1 hm2
  dsimp only at hm1 hm2
  have hs : mem'.size ≤ mem.size + 1 := by
    obtain ⟨_, _, _, _, _, h⟩ := stepRmw_mem h
    rcases h with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -⟩ | ⟨_, _, _, rfl, -⟩⟩
    · exact Nat.le_succ _
    · simp only [Array.size_push]; exact Nat.le_refl _
    · exact Nat.le_succ _
  have := lt_of_get hm1
  have := lt_of_get hm2
  omega

/-- A `casp` appends at most two messages, at distinct addresses. -/
theorem rmwPair_once {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    ∀ (t1 t2 : Nat) (m1 m2 : Msg), mem.size ≤ t1 → mem.size ≤ t2 → mem'[t1]? = some m1 → mem'[t2]? = some m2 →
      m1.loc = m2.loc → t1 = t2 := by
  intro t1 t2 m1 m2 h1 h2 hm1 hm2 hl
  rcases stepRmwPair_shape h with ⟨rfl, -⟩ | ⟨⟨x0, x1, rfl, h0, h1'⟩, -⟩
  · exact absurd (lt_of_get hm1) (by omega)
  · have k : ∀ (t : Nat) (m : Msg), mem.size ≤ t → ((mem.push x0).push x1)[t]? = some m →
        (t = mem.size ∧ m.loc = a) ∨ (t = mem.size + 1 ∧ m.loc = a.next) := by
      intro t m ht hm
      have hlt := lt_of_get hm
      simp only [Array.size_push] at hlt
      rcases Nat.lt_or_ge t (mem.size + 1) with h | h
      · obtain rfl : t = mem.size := by omega
        rw [TermLiveProps.push2_fst] at hm; cases hm; exact .inl ⟨rfl, h0⟩
      · obtain rfl : t = mem.size + 1 := by omega
        rw [TermLiveProps.push2_snd] at hm; cases hm; exact .inr ⟨rfl, h1'⟩
    rcases k t1 m1 h1 hm1 with ⟨e1, l1⟩ | ⟨e1, l1⟩ <;> rcases k t2 m2 h2 hm2 with ⟨e2, l2⟩ | ⟨e2, l2⟩
    · omega
    · exact absurd (l2.symm.trans (hl.symm.trans l1)) (next_ne a)
    · exact absurd (l1.symm.trans (hl.trans l2)) (next_ne a)
    · omega

/-- **(B2, operation)**: an operation writes each address outside its fresh
labels at most once. -/
theorem evalOp_once {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) : OnceIn s r.1 (FreshIn g s.nalloc r.1.nalloc) := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first
         | exact OnceIn.of_eq rfl
         | exact OnceIn.of_newInF (newIn_allocBuf ‹_›)
         | exact OnceIn.of_newInF newIn_allocBuf')
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact OnceIn.of_eq (loadUnits_keep _ _ _ _ hx).1
         | exact storeUnits_onceIn hx
         | exact OnceIn.of_newInF (newIn_alloc hpl hx)
         | exact fun t1 t2 m1 m2 h1 h2 hm1 hm2 _ _ => rmw_once hx t1 t2 m1 m2 h1 h2 hm1 hm2)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact OnceIn.of_newInF (newIn_projInj hpl hx hy)
         | exact OnceIn.left (loadUnits_keep _ _ _ _ hx).1 (storeUnits_onceIn hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact OnceIn.left (loadUnits_keep _ _ _ _ hx).1 (storeUnits_onceIn hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact OnceIn.of_eq (loadUnits_keep _ _ _ _ hx).1)
    | (simp only [Option.toList_some, List.mem_singleton] at h; subst h; dsimp only
       exact OnceIn.of_newInF newIn_allocBuf')

/-- **(B2, thread step)**: a thread step writes each address outside its fresh
labels at most once. -/
theorem tstep_once {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hpl : PromLt (stOf mem pairs th)) (h : r ∈ tstep g mem pairs th) :
    ∀ (t1 t2 : Nat) (m1 m2 : Msg), mem.size ≤ t1 → mem.size ≤ t2 → r.1[t1]? = some m1 → r.1[t2]? = some m2 →
      m1.loc = m2.loc → ¬ FreshIn g th.nalloc r.2.2.nalloc m1.loc.label → t1 = t2 := by
  intro t1 t2 m1 m2 h1 h2 hm1 hm2 hl hX
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only at hm1; exact absurd (lt_of_get hm1) (by omega))
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf] at hm1
       exact absurd (lt_of_get hm1) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm1
       exact absurd (lt_of_get hm1) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm1
       exact absurd (lt_of_get hm1) (by omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_once hpl hx t1 t2 m1 m2 h1 h2 hm1 hm2 hl hX
         | (revert hX; split <;> intro hX <;> exact evalOp_once hpl hx t1 t2 m1 m2 h1 h2 hm1 hm2 hl hX)
         | exact rmw_once hx t1 t2 m1 m2 h1 h2 hm1 hm2
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact rmwPair_once hx t1 t2 m1 m2 h1 h2 hm1 hm2 hl))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact absurd ((newIn_projInj (X := fun _ => False) hpl hx hy t1 m1 h1 hm1).resolve_right id) hX)

/-! ## (B2) Own cells: every new message at an initialised offset is typed -/

/-- (B2) A word of a cell's words (`CellOK` at count `n`) at an offset below
slot `n` is `WordOK`. -/
theorem cellOK_wordOK {η : TEnv} {cl : Cell} {n o : Nat} {vals : List Word} {v : Word}
    (hc : CellOK η n cl.ty vals)
    (hi : ∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → o < n * nWords us)
    (hv : vals[o]? = some v) :
    WordOK η cl.ty o v := by
  rcases hc with ⟨hwc, hval⟩ | ⟨N, e, us, hT, hus, hn, hlen, hsl⟩
  · obtain ⟨L, hL, -⟩ := Option.map_eq_some_iff.1 (show (accs cl.ty).map nWords = some vals.length from hwc)
    exact WordOK_whole ⟨hval, ShapeC_of_wc hwc rfl⟩ (by rw [hL]; exact Option.some_ne_none _) hv
  · have hc : CellOK η n cl.ty vals := .inr ⟨N, e, us, hT, hus, hn, hlen, hsl⟩
    have ho : o < n * nWords us := hi N e us hT hus
    have hj : o / nWords us < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact ho)
    have hpos : 0 < nWords us :=
      Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at ho; exact Nat.not_lt_zero _ ho
    have hm : o % nWords us < nWords us := Nat.mod_lt _ hpos
    have hdm : o / nWords us * nWords us + o % nWords us = o := by
      rw [Nat.mul_comm]; exact Nat.div_add_mod o _
    have hseg : SegOf cl.ty (o / nWords us * nWords us) e :=
      .inr ⟨N, us, o / nWords us, hT, hus, Nat.lt_of_lt_of_le hj hn, rfl⟩
    obtain ⟨hval, -⟩ := CellOK_seg hc hseg hus fun N' e' hT' => by
      rw [hT] at hT'; simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨rfl, rfl⟩ := hT'
      exact ⟨us, o / nWords us, hus, hj, rfl⟩
    refine ⟨_, e, _, o % nWords us, v, hseg, hval, ?_, WLe1_refl v, hdm⟩
    rw [List.getElem?_take_of_lt hm, List.getElem?_drop, hdm]; exact hv

/-- (B2) An offset below slot `n` within the cell's word count is covered by its
words (`CellOK` at count `n`). -/
theorem cellOK_cover {η : TEnv} {cl : Cell} {n o : Nat} {vals : List Word}
    (hc : CellOK η n cl.ty vals)
    (hi : ∀ N e us, cl.ty = .array (.lit N) e → accs e = some us → o < n * nWords us) (hwc : ∀ n, wc cl.ty = some n → o < n) :
    o < vals.length := by
  rcases hc with ⟨h, -⟩ | ⟨N, e, us, hT, hus, hn, hlen, -⟩
  · exact hwc _ h
  · rw [hlen]
    exact Nat.lt_of_lt_of_le (hi N e us hT hus) (Nat.mul_le_mul_right _ hn)

/-- **(B2, own cell, any timestamp)**: in a post state, a non-promise message
at or past `n0` at an in-range offset below the real count (`InitRr`; a
planted slot's words are not recorded by `OwnOKPF`) of the thread's own cell is
`WordOK`, provided no other message at or past `n0` is at that address
(`honce`, from `tstep_once`).  Above coherence: `LatestSF`; at coherence: the
cell's word (`cellOK_wordOK`); below: a second new write, excluded. -/
theorem newMsg_wordOK_ownAll {g : G} {E : TEnv} {s' : St} {n0 : Nat} {l : AllocLabel} {cl : Cell} {o t : Nat}
    {m : Msg} (hm : MemInv g E s') (hsto : E.sto l = some cl) (hown : cl.owner = some E.tid)
    (hi : InitRr E cl l o) (hwc : ∀ n, wc cl.ty = some n → o < n) (ht : n0 ≤ t) (hnp : t ∉ s'.promises)
    (hmt : s'.mem[t]? = some m) (hloc : m.loc = ⟨l, o⟩)
    (honce : ∀ (t' : Nat) (m' : Msg), n0 ≤ t' → s'.mem[t']? = some m' → m'.loc = ⟨l, o⟩ → t' = t) :
    WordOK E cl.ty o (mw m) := by
  obtain ⟨vals, hc, hl, -⟩ := hm.2.1 l cl hsto hown
  obtain ⟨v, hv⟩ : ∃ v, vals[o]? = some v := ⟨_, List.getElem?_eq_getElem (cellOK_cover hc hi hwc)⟩
  have hL := hl o v hv
  rcases Nat.lt_trichotomy (s'.vs.coh ⟨l, o⟩) t with hlt | heq | hgt
  · rcases hL.2.2 t m hlt hmt hloc with hp | ⟨-, hty⟩
    · exact absurd hp hnp
    · unfold TypedAt at hty; rw [hloc] at hty; exact hty
  · obtain ⟨m', hm', hl', hor⟩ := hL.1
    rw [heq, hmt] at hm'; cases hm'
    rcases hor with ⟨hval, hview⟩ | ⟨-, hty⟩
    · obtain ⟨b, S, ws, o', w0, h1, h2, h3, h4, h5⟩ := cellOK_wordOK hc hi hv
      exact ⟨b, S, ws, o', w0, h1, h2, h3, WLe1_trans h4 ⟨hval.symm, fun x g hx => hview x g hx⟩, h5⟩
    · unfold TypedAt at hty; rw [hloc] at hty; exact hty
  · obtain ⟨m', hm', hl', -⟩ := hL.1
    have := honce _ m' (Nat.le_trans ht (Nat.le_of_lt hgt)) hm' hl'
    omega

/-- **(B2, own cell, system)**: under `SysInvW`, a message appended by a step of
thread `i` at an in-range offset below the real count (`InitRr`) of an own cell of `i` is
`WordOK` in the step's witness `E'`, and, if the cell is shared, in `PubE E_g'`
(every timestamp: `newMsg_wordOK_ownAll` with `tstep_once`). -/
theorem SysInvW.newOwn_wordOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    {S : AllocLabel → Prop} {E' : TEnv}
    (hf : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hm' : MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)) (hce : CE E' = E')
    {t : Nat} {m : Msg} {l : AllocLabel} {o : Nat} {cl : Cell} (ht : c.mem.size ≤ t) (hmt : r.1[t]? = some m)
    (hloc : m.loc = ⟨l, o⟩) (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hi : InitRr E' cl l o)
    (hwc : ∀ n, wc cl.ty = some n → o < n) :
    WordOK E' cl.ty o (mw m) ∧
      (Eg.Shared l → WordOK (PubE (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E')) cl.ty o (mw m)) := by
  obtain ⟨S0, -, -, hm0, -⟩ := h.thread hth
  have hfr := SysInvW.gfresh h hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
    rw [(hfr l hF).1] at hsto; cases hsto
  have hsto' : E'.sto l = some cl := by
    rcases hf.2.2.1 l with e | ⟨hF, -⟩
    · rw [e]; exact cutSto_own hsto hown
    · exact absurd hF hnF
  have htid : E'.tid = i := hf.2.1
  have hnp : t ∉ (stOf r.1 r.2.1 r.2.2).promises :=
    tstep_newNotProm (MemInv_promLt hm0) (MemInv_nopair hm0) hr ht
  have hw : WordOK E' cl.ty o (mw m) :=
    newMsg_wordOK_ownAll hm' hsto' (by rw [htid]; exact hown) hi hwc ht hnp hmt hloc
      fun t' m' ht' hm'' hl' => tstep_once hm0.2.2.1 hr t' t m' m ht' ht hm'' hmt (hl'.trans hloc.symm)
        (by rw [hl']; exact hnF)
  refine ⟨hw, fun hsh => ?_⟩
  have hcut := Cut_self (g := gOf p k arch c i) hf hfr
  rw [hce] at hcut
  rw [hcut] at hw
  exact wordOK_pub (h.shty l cl hsh hsto) hw

/-- **(B2, own cell, system, B5 form)**: `SysInvW.newOwn_wordOK` with its
in-range hypothesis `hwc` discharged by B5 (`tstep_newPosE`, `newPos_b5`),
under the step's scope `hsc`. -/
theorem SysInvW.newOwn_wordOK_sc {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    (hsc : ∀ (η : TEnv) (cx : Cx) (S' : AllocLabel → Prop), CE η = Cut Eg i S' → Typed p cx th.term →
      StepScope cx th.term)
    {S : AllocLabel → Prop} {E' : TEnv}
    (hf : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hm' : MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)) (hce : CE E' = E')
    {t : Nat} {m : Msg} {l : AllocLabel} {o : Nat} {cl : Cell} (ht : c.mem.size ≤ t) (hmt : r.1[t]? = some m)
    (hloc : m.loc = ⟨l, o⟩) (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hi : InitRr E' cl l o) :
    WordOK E' cl.ty o (mw m) ∧
      (Eg.Shared l → WordOK (PubE (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E')) cl.ty o (mw m)) := by
  refine SysInvW.newOwn_wordOK h hth hr hf hm' hce ht hmt hloc hsto hown hi ?_
  have hfr := SysInvW.gfresh h hth r.2.2.nalloc
  rcases stepper_newPos h hth hr hsc t m ht hmt with hF | ⟨cl', hsto', hwc, -⟩
  · rw [hloc] at hF; rw [(hfr l hF).1] at hsto; cases hsto
  · have e2 : cutSto Eg i m.loc.label = some cl := by rw [hloc]; exact cutSto_own hsto hown
    rw [e2] at hsto'; cases hsto'
    intro n hn; have := hwc n hn; rw [hloc] at this; exact this

/-- **(B2, own cell, planted slot)** (F2′ step 3, S3.6): in a post state, a
non-promise message at an offset initialised at the reader-visible count but
not at the real one (`InitR`, `¬ InitRr`: the cell is planted) of the thread's
own cell is `WordOK`, provided the cell's frontier is at most its timestamp.
`OwnHidP` part 2 hides a `¬ WordOK` one below the frontier, by a later message. -/
theorem newMsg_wordOK_ownPlanted {g : G} {E : TEnv} {s' : St} {l : AllocLabel} {cl : Cell} {o t : Nat}
    {m : Msg} (hm : MemInv g E s') (hsto : E.sto l = some cl) (hown : cl.owner = some E.tid)
    (hi : InitR E cl l o) (hnr : ¬ InitRr E cl l o) (hnp : t ∉ s'.promises)
    (hmt : s'.mem[t]? = some m) (hloc : m.loc = ⟨l, o⟩) (hft : ∀ f, E.pfr l = some f → f ≤ t) :
    WordOK E cl.ty o (mw m) := by
  have hrc : E.rc l < E.ini l := Nat.lt_of_not_le fun hle => hnr fun N e us h1 h2 =>
    Nat.lt_of_lt_of_le (hi N e us h1 h2) (Nat.mul_le_mul_right _ hle)
  obtain ⟨f, hf, -, hH⟩ := hm.2.2.2.2.2.1.2 l cl hsto hown hrc
  refine Classical.byContradiction fun hno => ?_
  obtain ⟨t', m', h1, h2, -, -⟩ := hH o hi t m hnp hmt hloc hno
  exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le h1 (Nat.le_trans h2 (hft f hf)))

/-- **(B2, own cell, any initialised offset)**: `newMsg_wordOK_ownAll` at the
reader-visible count (`InitR`): at the real count as there, at a planted slot by
`newMsg_wordOK_ownPlanted`. -/
theorem newMsg_wordOK_ownInit {g : G} {E : TEnv} {s' : St} {n0 : Nat} {l : AllocLabel} {cl : Cell} {o t : Nat}
    {m : Msg} (hm : MemInv g E s') (hsto : E.sto l = some cl) (hown : cl.owner = some E.tid)
    (hi : InitR E cl l o) (hwc : ∀ n, wc cl.ty = some n → o < n) (ht : n0 ≤ t) (hnp : t ∉ s'.promises)
    (hmt : s'.mem[t]? = some m) (hloc : m.loc = ⟨l, o⟩)
    (honce : ∀ (t' : Nat) (m' : Msg), n0 ≤ t' → s'.mem[t']? = some m' → m'.loc = ⟨l, o⟩ → t' = t)
    (hft : ∀ f, E.pfr l = some f → f ≤ t) :
    WordOK E cl.ty o (mw m) := by
  by_cases hr : InitRr E cl l o
  · exact newMsg_wordOK_ownAll hm hsto hown hr hwc ht hnp hmt hloc honce
  · exact newMsg_wordOK_ownPlanted hm hsto hown hi hr hnp hmt hloc hft

/-- **(B2, own cell, system, any initialised offset)** (F2′ step 3, S3.6):
`SysInvW.newOwn_wordOK` at the reader-visible count (`InitR`), covering the
planted slots.  The cell's frontier in `E'` is at most the old memory size:
an old frontier by `SysInvW.frle`, a frontier planted by the step at the old
`vWr` by `SysInvW.vwr`. -/
theorem SysInvW.newOwn_wordOK_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    {S : AllocLabel → Prop} {E' : TEnv}
    (hf : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hm' : MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)) (hce : CE E' = E')
    {t : Nat} {m : Msg} {l : AllocLabel} {o : Nat} {cl : Cell} (ht : c.mem.size ≤ t) (hmt : r.1[t]? = some m)
    (hloc : m.loc = ⟨l, o⟩) (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hi : InitR E' cl l o)
    (hwc : ∀ n, wc cl.ty = some n → o < n) :
    WordOK E' cl.ty o (mw m) ∧
      (Eg.Shared l → WordOK (PubE (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E')) cl.ty o (mw m)) := by
  obtain ⟨S0, -, -, hm0, -⟩ := h.thread hth
  have hfr := SysInvW.gfresh h hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
    rw [(hfr l hF).1] at hsto; cases hsto
  have hsto' : E'.sto l = some cl := by
    rcases hf.2.2.1 l with e | ⟨hF, -⟩
    · rw [e]; exact cutSto_own hsto hown
    · exact absurd hF hnF
  have htid : E'.tid = i := hf.2.1
  have hnp : t ∉ (stOf r.1 r.2.1 r.2.2).promises :=
    tstep_newNotProm (MemInv_promLt hm0) (MemInv_nopair hm0) hr ht
  have hft : ∀ f, E'.pfr l = some f → f ≤ t := fun f hpf' => by
    rcases hf.2.2.2.2.2.1 l with e | ⟨-, F, e, -, hF2, -⟩ | ⟨hF, -, -⟩
    · rw [e] at hpf'
      exact Nat.le_trans (h.frle l cl f hsto hpf') ht
    · rw [e] at hpf'
      obtain rfl := Option.some.inj hpf'
      exact Nat.le_trans hF2 (Nat.le_trans (Nat.max_le.2 ⟨h.vwr i th hth, Nat.le_refl _⟩) ht)
    · exact absurd hF hnF
  have hw : WordOK E' cl.ty o (mw m) :=
    newMsg_wordOK_ownInit hm' hsto' (by rw [htid]; exact hown) hi hwc ht hnp hmt hloc
      (fun t' m' ht' hm'' hl' => tstep_once hm0.2.2.1 hr t' t m' m ht' ht hm'' hmt (hl'.trans hloc.symm)
        (by rw [hl']; exact hnF)) hft
  refine ⟨hw, fun hsh => ?_⟩
  have hcut := Cut_self (g := gOf p k arch c i) hf hfr
  rw [hce] at hcut
  rw [hcut] at hw
  exact wordOK_pub (h.shty l cl hsh hsto) hw

/-- **(B2, own cell, system, any initialised offset, B5 form)**:
`SysInvW.newOwn_wordOK_init` with `hwc` discharged by B5, under the step's
scope `hsc` (as `SysInvW.newOwn_wordOK_sc`). -/
theorem SysInvW.newOwn_wordOK_init_sc {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    (hsc : ∀ (η : TEnv) (cx : Cx) (S' : AllocLabel → Prop), CE η = Cut Eg i S' → Typed p cx th.term →
      StepScope cx th.term)
    {S : AllocLabel → Prop} {E' : TEnv}
    (hf : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hm' : MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)) (hce : CE E' = E')
    {t : Nat} {m : Msg} {l : AllocLabel} {o : Nat} {cl : Cell} (ht : c.mem.size ≤ t) (hmt : r.1[t]? = some m)
    (hloc : m.loc = ⟨l, o⟩) (hsto : Eg.sto l = some cl) (hown : cl.owner = some i) (hi : InitR E' cl l o) :
    WordOK E' cl.ty o (mw m) ∧
      (Eg.Shared l → WordOK (PubE (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E')) cl.ty o (mw m)) := by
  refine SysInvW.newOwn_wordOK_init h hth hr hf hm' hce ht hmt hloc hsto hown hi ?_
  have hfr := SysInvW.gfresh h hth r.2.2.nalloc
  rcases stepper_newPos h hth hr hsc t m ht hmt with hF | ⟨cl', hsto', hwc, -⟩
  · rw [hloc] at hF; rw [(hfr l hF).1] at hsto; cases hsto
  · have e2 : cutSto Eg i m.loc.label = some cl := by rw [hloc]; exact cutSto_own hsto hown
    rw [e2] at hsto'; cases hsto'
    intro n hn; have := hwc n hn; rw [hloc] at this; exact this

/-! ## (B3) The stepper's own planted buffers

`gfoot_ini_other` covers every cell not of `g.i`.  At `g.i`'s own *shared*
cells a step may raise the count (`bufInit` on a planted buffer): `ModeOK .own`
constrains only the owner, and a plain `bufInit` store's message view
(`max vRelSt dv`) does not include `vWr`, so nothing in the certification
freezes the count there without a typed certifying run (b4 `FrBound`, later).
The exact missing fact is `PlantFrozen`. -/

/-- (B3, hypothesis) A step of `g.i` leaves the count of each of its own shared
cells unchanged. -/
def PlantFrozen (i : Nat) (Eg Eg' : GEnv) : Prop :=
  ∀ l, Eg.OwnAt i l → Eg.Shared l → Eg'.ini l = Eg.ini l

/-- **(B3, every shared label)**: given `PlantFrozen`, a global step of `g.i`
leaves the count of every shared label unchanged. -/
theorem gfoot_ini_shared {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg' n n' v)
    (hfr : GFreshE g Eg n n') (hpf : PlantFrozen g.i Eg Eg') {l : AllocLabel} (hsh : Eg.Shared l) :
    Eg'.ini l = Eg.ini l := by
  rcases (hf.2.2.2.1 l).2 with e | hF | ho
  · exact e
  · obtain ⟨f, hf'⟩ := hsh; rw [(hfr l hF).2.2] at hf'; cases hf'
  · exact hpf l ho hsh

/-! ## The bundle: `stepper_facts` -/

theorem PubE_withFp (X : GEnv) (f : Nat → List Ts) : PubE (X.withFp f) = PubE X := rfl
theorem ini_withFp (X : GEnv) (f : Nat → List Ts) : (X.withFp f).ini = X.ini := rfl

/-- **(S8b B1–B3, B5) What a thread step does to shared memory**, under
`SysInvW`, for a step `r` of thread `i` whose S6 witness is `E'` (footprint
`hf` on `i`'s cut, post `MemInv` `hm'`, `CE`-shaped `hce`), with
`E_g' = E_g.post g n n' E'` (`withFp` changes neither `ini` nor `PubE`):

* (B1) every appended message is at a fresh label of `i` or at a label of
  `i`'s cut;
* (B2) an appended message at an initialised offset of another thread's
  shared cell is `WordOK` in `E'` and in `PubE E_g'` (the frontier is at most
  the old memory size by `SysInvW.frle`);
* (B3) the initialised count is unchanged at every cell that is not `i`'s;
* (B5) (under the step's scope `hsc` and `PromAbove` `hpa`) every
  single-word write is in a cell of `i`'s cut, outside every `word2` unit. -/
theorem stepper_facts {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh} (hth : c.ths[i]? = some th)
    {r : Memory × List Ts × TTh} (hr : r ∈ tstep (gOf p k arch c i) c.mem c.pairs th)
    {S : AllocLabel → Prop} {E' : TEnv}
    (hf : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hm' : MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)) (hce : CE E' = E') :
    -- (B1)
    (∀ (t : Nat) (m : Msg), c.mem.size ≤ t → r.1[t]? = some m →
      FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label ∨
        ∃ cl, cutSto Eg i m.loc.label = some cl) ∧
    -- (B2)
    (∀ (t : Nat) (m : Msg) (l : AllocLabel) (o : Nat) (cl : Cell) (f : Ts), c.mem.size ≤ t →
      r.1[t]? = some m → m.loc = ⟨l, o⟩ → Eg.sto l = some cl → cl.owner ≠ some i → Eg.pfr l = some f →
      InitR E' cl l o →
      WordOK E' cl.ty o (mw m) ∧
        WordOK (PubE (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E')) cl.ty o (mw m)) ∧
    -- (B3)
    (∀ (l : AllocLabel) (cl : Cell), Eg.sto l = some cl → cl.owner ≠ some i →
      (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l = Eg.ini l) ∧
    -- (B5)
    (∀ (loc : Address) (val : WeakMem.Val),
      (∀ (η : TEnv) (cx : Cx) (S' : AllocLabel → Prop), CE η = Cut Eg i S' → Typed p cx th.term →
        StepScope cx th.term) →
      PromAbove (stOf c.mem c.pairs th) → TermFul.SW (gOf p k arch c i) c.mem c.pairs th loc val →
      ∃ cl, cutSto Eg i loc.label = some cl ∧
        ∀ o2 r P, AtOff cl.ty o2 (.word2 r P) → loc.offset ≠ o2 ∧ loc.offset ≠ o2 + 1) := by
  obtain ⟨S0, -, hE0, hm0, -⟩ := h.thread hth
  have hfr := SysInvW.gfresh h hth r.2.2.nalloc
  have hgf := EFoot_post (g := gOf p k arch c i) hf hfr (h.vwr i th hth)
  refine ⟨fun t m ht hmt => tstep_writeAt hE0 hm0.2.2.1 hr t m ht hmt, ?_, ?_, ?_⟩
  · intro t m l o cl f ht hmt hloc hsto hown hpf hi
    have hfb : f ≤ c.mem.size := h.frle l cl f hsto hpf
    have hsh : Eg.Shared l := ⟨f, hpf⟩
    have hsto' : E'.sto l = some cl := by
      rcases hf.2.2.1 l with e | ⟨hF, -⟩
      · rw [e]; exact cutSto_shared hsto hsh
      · rw [(hfr l hF).1] at hsto; cases hsto
    have hpf' : E'.pfr l = some f := by
      rcases hf.2.2.2.2.2.1 l with e | ⟨e, -⟩ | ⟨-, e, -⟩
      · rw [e]; exact hpf
      · have e2 : Eg.pfr l = none := e; rw [e2] at hpf; cases hpf
      · have e2 : Eg.pfr l = none := e; rw [e2] at hpf; cases hpf
    have htid : E'.tid = i := hf.2.1
    have hnp : t ∉ (stOf r.1 r.2.1 r.2.2).promises :=
      tstep_newNotProm (MemInv_promLt hm0) (MemInv_nopair hm0) hr ht
    have hw : WordOK E' cl.ty o (mw m) :=
      newMsg_wordOK_other hm' hsto' (by rw [htid]; exact hown) hpf' hfb hi ht hnp hmt hloc
    refine ⟨hw, ?_⟩
    have hcut := Cut_self (g := gOf p k arch c i) hf hfr
    rw [hce] at hcut
    rw [hcut] at hw
    exact wordOK_pub (h.shty l cl hsh hsto) hw
  · intro l cl hsto hown
    exact gfoot_ini_other hgf hfr hsto hown
  · intro loc val hsc hpa hsw
    exact sw_noWord2E hE0 hm0 (fun η cx he hT => hsc η cx S0 he hT) hpa hsw

#print axioms mem_allProms
#print axioms mem_allProms_upd
#print axioms Cut_withFp
#print axioms promise_other
#print axioms allProms_promise
#print axioms PromsOK_promise
#print axioms PromsDisj_promise
#print axioms AllPromLt_promise
#print axioms FpOwnFree_promise
#print axioms PromsOK_thread
#print axioms fpSync_self
#print axioms PromsDisj_thread
#print axioms AllPromLt_thread
#print axioms FpOwnFree_thread
#print axioms threadSteps_upd
#print axioms fpok_nil
#print axioms fpok_of
#print axioms fresh_blankG
#print axioms SysInvW.gfresh
#print axioms SysInvW.freshMem
#print axioms or_iffA
#print axioms or_iffB
#print axioms NewIn.of_eq
#print axioms NewIn.mono
#print axioms NewIn.left
#print axioms NewIn.trans
#print axioms newIn_storeUnits
#print axioms tgt_of
#print axioms loadUnits_nalloc
#print axioms projM_nalloc
#print axioms newIn_alloc
#print axioms newIn_allocBuf
#print axioms newIn_projInj
#print axioms rmw_newAt
#print axioms rmwPair_newAt
#print axioms newIn_allocBuf'
#print axioms evalOp_new
#print axioms tstep_new
#print axioms isRef_cell
#print axioms isRef_cellOr
#print axioms isRef_buf
#print axioms isRef_word
#print axioms isRef_word2
#print axioms isRef_epair
#print axioms isRef_xchg
#print axioms vr_sto
#print axioms peek_sto
#print axioms termTgt_sto
#print axioms tstep_writeAt
#print axioms stepper_writeAt
#print axioms tstep_newNotProm
#print axioms gfoot_ini_other
#print axioms gfoot_ini_box
#print axioms gfoot_ini_own
#print axioms sw_noWord2
#print axioms sw_noWord2E
#print axioms newMsg_wordOK_other
#print axioms newMsg_wordOK_own
#print axioms wordOK_pub
#print axioms PubE_withFp
#print axioms ini_withFp
#print axioms stepper_facts
#print axioms VMono.refl'
#print axioms VMono.trans
#print axioms stepFence_vWr
#print axioms lockFence_vWr
#print axioms fenceS_vmono
#print axioms loadUnits_vmono
#print axioms storeUnits_vmono
#print axioms alloc_vmono
#print axioms allocBuf_vmono
#print axioms stepRmw_vmono
#print axioms stepRmwPair_vmono
#print axioms rmw_vmono
#print axioms rmwPair_vmono
#print axioms projM_vmono
#print axioms injM_vmono
#print axioms evalOp_vmono
#print axioms enter_vmono
#print axioms tstep_vmono
#print axioms tstep_vWr
#print axioms PromsDisj_init
#print axioms FpOwnFree_init
#print axioms AllPromLt_init
#print axioms VWrLe_init
#print axioms VWrLe_promise
#print axioms VWrLe_thread
#print axioms FrontierLe_init
#print axioms FrontierLe_mono
#print axioms FrontierLe_withFp
#print axioms FrontierLe_gfoot
#print axioms SysInvW.book_promise
#print axioms SysInvW.book_thread
#print axioms SysInvW.frle_thread
#print axioms SysInvW.rle_thread
#print axioms SysInvW.rle_cut
#print axioms SysInvW.rle_withFp
#print axioms SysInvW.bnamed_cut
#print axioms SysInvW.bnamed_withFp
#print axioms SysInvW.fpokOf
#print axioms OnceIn.of_eq
#print axioms OnceIn.of_newInF
#print axioms OnceIn.left
#print axioms offs_inj
#print axioms storeUnits_once
#print axioms storeUnits_onceIn
#print axioms rmw_once
#print axioms rmwPair_once
#print axioms evalOp_once
#print axioms tstep_once
#print axioms cellOK_wordOK
#print axioms cellOK_cover
#print axioms newMsg_wordOK_ownAll
#print axioms SysInvW.newOwn_wordOK
#print axioms gfoot_ini_shared
#print axioms oneAt_ful
#print axioms role_lt
#print axioms role_of_newRole
#print axioms role_two0
#print axioms role_two1
#print axioms units_new
#print axioms rmw_newLoc
#print axioms rmwPair_newLoc
#print axioms evalOp_store_new
#print axioms evalOp_xchg_new
#print axioms evalOp_xchgAt_new
#print axioms evalOp_xchgAtF_new
#print axioms evalOp_bufInit_new
#print axioms evalOp_stl_new
#print axioms evalOp_stlw_new
#print axioms evalOp_stp_new
#print axioms evalOp_fetch_new
#print axioms evalOp_newOp
#print axioms tstep_newOp
#print axioms newPos_ua
#print axioms newPos_sw
#print axioms offs_zero
#print axioms offs_one
#print axioms pair_ua
#print axioms stp_ua
#print axioms casp_ua
#print axioms tstep_newPos
#print axioms tstep_newPosE
#print axioms twoAt_twoAt
#print axioms twoAt_word2
#print axioms newPos_b5
#print axioms stepper_newPos
#print axioms SysInvW.newOwn_wordOK_sc
#print axioms newMsg_wordOK_ownPlanted
#print axioms newMsg_wordOK_ownInit
#print axioms SysInvW.newOwn_wordOK_init
#print axioms SysInvW.newOwn_wordOK_init_sc

end TermStepper

namespace TermStepper
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## (F2′ P2) The publish step under the system invariant

`SysInvW.own_thread` supplies `publish_ownZero`'s bound `Tot i (own x) +
(HP i + HS) (own x) ≤ 1`, and `SysInvW.thInvMC` its thread invariant. -/

/-- (F2′ P2) **Under `SysInvW`, publishing through an own handle to `x`
leaves no `own x`** in thread `i`'s frame or its holding at the certified
successor. -/
theorem SysInvW.publish_ownZero {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (hP : ProgT p) {i : Nat} {c' : Cfg}
    (hs : c' ∈ threadSteps p k arch c i) (hc' : Certified p k arch c' i)
    {th : TTh} (hth : c.ths[i]? = some th) {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e)
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g'])
    (hside : TermTyped.OwnSide p (gOf p k arch c i) c.mem c.pairs th) (hPS : PwSkel)
    (hRc : RecFresh (gOf p k arch c i) i th.nalloc)
    (hTyE : ∀ S, TyOKE (gOf p k arch c i) (Cut Eg i S)) :
    TermTyped.OwnZeroAt p k arch i ad.label c' := by
  obtain ⟨S, hT, -, hm, hHP, hHS, hC⟩ := h.thread hth
  have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hHP hHS
  exact TermTyped.publish_ownZero hP hs hc' hth hterm hea hws rfl hT hm hH hC
    (h.own_thread (arr_lt hth) ad.label) hside hPS (hTyE S) hRc

/-- (F2′ P2) **Under `SysInvW`, after publishing `x`'s own handle no own-mode
use reaches `x` along the certifying run** (`TermTyped.publish_noOwnUse`). -/
-- (C) restricted to certificate runs with no boxed current(), the pre-C coverage; the finals use the anchored X-chain
theorem SysInvW.publish_noOwnUse {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) {i : Nat} {c1 : Cfg}
    (hs : c1 ∈ threadSteps p k arch c i)
    {th : TTh} (hth : c.ths[i]? = some th) {y : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ y (.publish a) e)
    {rt : Ty} {ws : List Word} {ad : Address} {g' : Nat} (hea : evalAt th.env a = some (rt, ws))
    (hws : ws.map (·.val) = [.loc ad g'])
    (hside0 : TermTyped.OwnSide p (gOf p k arch c i) c.mem c.pairs th)
    (hn : 0 < (gOf p k arch c i).n) (hbf : (gOf p k arch c i).boxFence = true)
    (hside : ∀ c0 th, Solo p k arch i c1 c0 → Certified p k arch c0 i → c0.ths[i]? = some th →
      TermTyped.OwnSide p (gOf p k arch c0 i) c0.mem c0.pairs th)
    (hprom : ∀ c0 th a v w, Solo p k arch i c1 c0 → w < c0.mem.size → Certified p k arch (promise c0 i a v w) i →
      c0.ths[i]? = some th → TermTyped.PromSide p (gOf p k arch c0 i) c0.mem c0.pairs th a v w)
    {c2 : Cfg} (h12 : Solo p k arch i c1 c2) (hc2 : Certified p k arch c2 i) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hnb : TermTyped.NoBoxedCur p k arch i c1)
    (hRc : RecFresh (gOf p k arch c i) i th.nalloc)
    (hTyE : ∀ S, TyOKE (gOf p k arch c i) (Cut Eg i S)) :
    ∃ th, c2.ths[i]? = some th ∧ ∃ ρ η cx Rf Rs, EnvOK p η ∧ Typed p cx th.term ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧
      ∀ a t c₁ rt ws ad' g, cx.use a = .ok (t, c₁) →
        ((∃ u, cellOf t = some (.own, u)) ∨ ∃ n u k, bufOf t = some (.own, n, u, k)) →
        evalAt th.env a = some (rt, ws) → ws.map (·.val) = [.loc ad' g] → ad'.label ≠ ad.label := by
  obtain ⟨S, hT, -, hm, hHP, hHS, hC⟩ := h.thread hth
  have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hHP hHS
  exact TermTyped.publish_noOwnUse hP hs hth hterm hea hws rfl hT hm hH hC
    (h.own_thread (arr_lt hth) ad.label) hside0 hn hbf hside hprom h12 hc2 hPS hSub hSig hnb (hTyE S) hRc

#print axioms SysInvW.publish_ownZero
#print axioms SysInvW.publish_noOwnUse

end TermStepper

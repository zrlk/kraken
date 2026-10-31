import WeakCore.TermUndefLowDefs
import WeakCore.TermB5

/-!
# TermUndefLow: preservation of `UndefLowG`

* §1 Layout: a single-word unit of a laid-out cell (`OneU`) is never a word of a two-word unit of a
  component (`two_not_oneU`); a single-word unit of a solid piece is one of the cell
  (`onePc_oneU`, the bridge to `TermFreeQW`'s `hUL`).
-/

namespace TermUndefLow
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermCert
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## §1 Layout -/

theorem fulOneAt_step {us : List Acc} {j : Nat} (h : TermFul.OneAt us j) : TermStep.OneAt us j := by
  induction h with
  | here us => exact ⟨0, rfl, by simp [nWords]⟩
  | cons u _ ih => exact OneAt_cons u ih

/-- A unit of `us` holding exactly one offset is a single-word unit. -/
theorem inAcc_single_oneAt {us : List Acc} {i x : Nat} (h : InAcc us i x)
    (hs : ∀ o2, InAcc us i o2 → o2 = x) : TermFul.OneAt us x := by
  obtain ⟨h1, h2⟩ := h
  cases hu : us[i]? with
  | none =>
      have hl : us.length ≤ i := List.getElem?_eq_none_iff.1 hu
      rw [List.take_of_length_le hl, List.take_of_length_le (by omega)] at *
      omega
  | some u =>
      have e : nWords (us.take (i + 1)) = nWords (us.take i) + u.size := by
        rw [List.take_add_one, hu]; simp [nWords]
      cases u with
      | one =>
          simp only [Acc.size] at e
          exact oneAt_ful ⟨i, hu, by omega⟩
      | two =>
          simp only [Acc.size] at e
          have a1 := hs (nWords (us.take i)) ⟨Nat.le_refl _, by omega⟩
          have a2 := hs (nWords (us.take i) + 1) ⟨by omega, by omega⟩
          omega

/-- **Layout**: a single-word unit of a laid-out cell type is no word of a two-word unit of a
component. -/
theorem two_not_oneU {T U : Ty} {b jj o : Nat} {us : List Acc} (h1 : AtOff T b U) (hus : accs U = some us)
    (hj : TwoAt us jj) (ho : OneU T o) (he : o = b + jj ∨ o = b + jj + 1) : False := by
  rcases ho with ⟨L, hL, hone⟩ | ⟨N, e, L, j, o', hT, hL, hjN, ho', hone⟩
  · obtain ⟨pre, post, e, hn⟩ := AtOff_embed h1 hL hus
    have h2 : TwoAt L (b + jj) := by rw [e, ← hn]; exact TwoAt_embed hj
    have h3 := fulOneAt_step hone
    rcases he with rfl | rfl
    · exact TwoAt_not_OneAt h2 h3
    · exact TwoAt_not_OneAt_succ h2 h3
  · subst hT
    rcases AtOff_arr_elem h1 rfl with hU | ⟨us', j2, o2, hus', hj2, hb, hat⟩
    · subst hU; simp [accs] at hus
    · rw [hL] at hus'; cases hus'
      obtain ⟨pre, post, e2, hn⟩ := AtOff_embed hat hL hus
      have h2 : TwoAt L (o2 + jj) := by rw [e2, ← hn]; exact TwoAt_embed hj
      have hlt := TwoAt_lt h2
      have hlt1 := TermFul.OneAt_lt hone
      rcases Nat.lt_trichotomy j2 j with hl | rfl | hg
      · have hm : (j2 + 1) * nWords L ≤ j * nWords L := Nat.mul_le_mul_right _ hl
        rw [Nat.succ_mul] at hm
        omega
      · have h3 := fulOneAt_step hone
        rcases he with he | he
        · have : o' = o2 + jj := by omega
          subst this; exact TwoAt_not_OneAt h2 h3
        · have : o' = o2 + jj + 1 := by omega
          subst this; exact TwoAt_not_OneAt_succ h2 h3
      · have hm : (j + 1) * nWords L ≤ j2 * nWords L := Nat.mul_le_mul_right _ hg
        rw [Nat.succ_mul] at hm
        omega

/-- **The bridge to `hUL`**: a single-word unit of a solid piece of a laid-out cell type is a
single-word unit of the cell. -/
theorem onePc_oneU {T : Ty} {o : Nat} (hlay : LayT T) (h : OnePc T o) : OneU T o := by
  obtain ⟨b, U, us, i, hP, hus, hb, hi, hsing⟩ := h
  have hone := inAcc_single_oneAt hi hsing
  by_cases harr : ∃ N e, T = .array (.lit N) e
  · obtain ⟨N, e, rfl⟩ := harr
    rcases AtOff_arr_elem hP.1 rfl with hU | ⟨us', j2, o2, hus', hj2, hb2, hat⟩
    · exact absurd hU (hP.2.1.2.1 _ _)
    · obtain ⟨pre, post, e2, hn⟩ := AtOff_embed hat hus' hus
      refine .inr ⟨N, e, us', j2, o2 + (o - b), rfl, hus', hj2, by omega, ?_⟩
      rw [e2, ← hn, List.append_assoc]
      exact TermPlantF.oneAtF_prepend pre (TermPlantF.oneAtF_append post hone)
  · rcases hlay with hacc | ⟨N, e, hTe, -⟩
    · obtain ⟨L, hL⟩ := Option.ne_none_iff_exists'.1 hacc
      obtain ⟨pre, post, e2, hn⟩ := AtOff_embed hP.1 hL hus
      refine .inl ⟨L, hL, ?_⟩
      have h3 := TermPlantF.oneAtF_prepend pre (TermPlantF.oneAtF_append post hone)
      rw [hn, show b + (o - b) = o by omega, ← List.append_assoc, ← e2] at h3
      exact h3
    · exact absurd ⟨N, e, hTe⟩ harr

#print axioms inAcc_single_oneAt
#print axioms two_not_oneU
#print axioms onePc_oneU

/-! ## §2 New messages: a defined one is never followed by another new one at its address

`NewOrdM mem mem'`: of two messages of `mem'` past `mem` at one address, the earlier is `undef`
(an allocation's placeholder).  Every thread step has it. -/

def NewOrdM (mem mem' : Memory) : Prop :=
  ∀ (t1 t2 : Nat) (m1 m2 : Msg), mem.size ≤ t1 → t1 < t2 → mem'[t1]? = some m1 → mem'[t2]? = some m2 →
    m1.loc = m2.loc → m1.val = .undef

theorem newOrd_eq {mem mem' : Memory} (h : mem' = mem) : NewOrdM mem mem' := by
  intro t1 t2 m1 m2 h1 _ hm1; subst h; exact absurd (TermMem.lt_of_get hm1) (by omega)

theorem newOrd_left {mem mem1 mem2 : Memory} (he : mem1 = mem) (h : NewOrdM mem1 mem2) : NewOrdM mem mem2 := by
  subst he; exact h

/-- A store writes each address at most once. -/
theorem storeUnits_newInj {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ (t1 t2 : Nat) (m1 m2 : Msg), s.mem.size ≤ t1 → t1 < t2 → s'.mem[t1]? = some m1 →
        s'.mem[t2]? = some m2 → m1.loc ≠ m2.loc
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t1 t2 m1 m2 h1 _ hm1; exact absurd (TermMem.lt_of_get hm1) (by omega)
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      have ih := storeUnits_newInj us ws (i + 1) _ s' hs
      obtain ⟨-, g2, g3⟩ := storeUnits_roles us ws (i + 1) _ s' hs
      have g2' : ∀ t, t < mem'.size → s'.mem[t]? = mem'[t]? := g2
      have g3' : ∀ (t : Nat) (m : Msg), mem'.size ≤ t → s'.mem[t]? = some m →
          ∃ j, m.loc = offs a (i + 1 + j) ∧ NewRole us a (i + 1) mem'.size s' t j := g3
      have ih' : ∀ (t1 t2 : Nat) (m1 m2 : Msg), mem'.size ≤ t1 → t1 < t2 → s'.mem[t1]? = some m1 →
          s'.mem[t2]? = some m2 → m1.loc ≠ m2.loc := ih
      obtain ⟨t0, hcase, _⟩ := stepStore_cases hst
      intro t1 t2 m1 m2 h1 h12 hm1 hm2
      rcases hcase with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
      · by_cases hb : s.mem.size + 1 ≤ t1
        · exact ih' t1 t2 m1 m2 (by simp; omega) h12 hm1 hm2
        · have e1 : t1 = s.mem.size := by omega
          subst e1
          rw [g2' _ (by simp)] at hm1
          simp at hm1
          obtain ⟨j, hj, -⟩ := g3' t2 m2 (by simp; omega) hm2
          rw [← hm1, hj]
          exact offs_ne a (by omega)
      · exact ih' t1 t2 m1 m2 h1 h12 hm1 hm2
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have ih := storeUnits_newInj us ws (i + 2) _ s' hs
      obtain ⟨-, g2, g3⟩ := storeUnits_roles us ws (i + 2) _ s' hs
      obtain ⟨q1, -, -, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at ih g2 g3 q1
      have g2' : ∀ t, t < R.1.size → s'.mem[t]? = R.1[t]? := g2
      have g3' : ∀ (t : Nat) (m : Msg), R.1.size ≤ t → s'.mem[t]? = some m →
          ∃ j, m.loc = offs a (i + 2 + j) ∧ NewRole us a (i + 2) R.1.size s' t j := g3
      have ih' : ∀ (t1 t2 : Nat) (m1 m2 : Msg), R.1.size ≤ t1 → t1 < t2 → s'.mem[t1]? = some m1 →
          s'.mem[t2]? = some m2 → m1.loc ≠ m2.loc := ih
      have hsz : R.1.size = s.mem.size + 2 := by rw [q1]; simp
      have h0 : ∀ m, R.1[s.mem.size]? = some m → m.loc = offs a i := by
        intro m hm; rw [q1, push_lt (by simp)] at hm; simp at hm; rw [← hm]
      have h1' : ∀ m, R.1[s.mem.size + 1]? = some m → m.loc = offs a (i + 1) := by
        intro m hm; rw [q1, Array.getElem?_push, ite_eq_left (by simp)] at hm; rw [← Option.some.inj hm]
        simp [offs, WeakMem.Address.next, Nat.add_assoc]
      intro t1 t2 m1 m2 h1 h12 hm1 hm2
      by_cases hb : R.1.size ≤ t1
      · exact ih' t1 t2 m1 m2 hb h12 hm1 hm2
      · rw [g2' t1 (by omega)] at hm1
        have hl1 : m1.loc = offs a i ∨ m1.loc = offs a (i + 1) := by
          by_cases e : t1 = s.mem.size
          · subst e; exact .inl (h0 m1 hm1)
          · have e' : t1 = s.mem.size + 1 := by omega
            subst e'; exact .inr (h1' m1 hm1)
        by_cases hb2 : R.1.size ≤ t2
        · obtain ⟨j, hj, -⟩ := g3' t2 m2 hb2 hm2
          rw [hj]
          rcases hl1 with e | e <;> rw [e] <;> exact offs_ne a (by omega)
        · rw [g2' t2 (by omega)] at hm2
          have e1 : t1 = s.mem.size := by omega
          have e2 : t2 = s.mem.size + 1 := by omega
          subst e1; subst e2
          rw [h0 m1 hm1, h1' m2 hm2]
          exact offs_ne a (by omega)
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem newOrd_storeUnits {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} (hs : s' ∈ storeUnits k arch pw a rel us ws i s) :
    NewOrdM s.mem s'.mem :=
  fun t1 t2 m1 m2 h1 h12 hm1 hm2 hl => absurd hl (storeUnits_newInj us ws i s s' hs t1 t2 m1 m2 h1 h12 hm1 hm2)

theorem newOrd_alloc {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc} {ws : List Word}
    {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : NewOrdM s.mem r.1.mem := by
  obtain ⟨s1, hs, -, -, -, -, -, -, -, -, hsz, hget⟩ := alloc_unf hr
  obtain ⟨-, g2, -⟩ := storeUnits_roles us ws 0 s1 r.1 hs
  intro t1 t2 m1 m2 h1 h12 hm1 hm2 hl
  by_cases hb : s1.mem.size ≤ t1
  · exact absurd hl (storeUnits_newInj us ws 0 s1 r.1 hs t1 t2 m1 m2 hb h12 hm1 hm2)
  · rw [g2 t1 (by omega), hget, ite_eq_right (by omega), ite_eq_left (by omega)] at hm1
    rw [← Option.some.inj hm1]

theorem newOrd_allocBuf {lbl : AllocLabel} {n : Nat} {z : Option (List WeakMem.Val)} {s : St} :
    NewOrdM s.mem (allocBuf lbl n z s).1.mem := by
  intro t1 t2 m1 m2 h1 h12 hm1 hm2 hl
  simp only [allocBuf] at hm1 hm2
  rw [TermMem.fold_get, ite_eq_right (by omega)] at hm1 hm2
  split at hm1
  · split at hm2
    · rw [← Option.some.inj hm1, ← Option.some.inj hm2] at hl
      simp only [offs] at hl
      have h3 : t1 - s.mem.size = t2 - s.mem.size := by
        have := congrArg WeakMem.Address.offset hl
        simpa using this
      omega
    · cases hm2
  · cases hm1

theorem newOrd_allocBufE {lbl : AllocLabel} {n : Nat} {z : Option (List WeakMem.Val)} {s s' : St} {pw : Word}
    (he : allocBuf lbl n z s = (s', pw)) : NewOrdM s.mem s'.mem := by
  have h := newOrd_allocBuf (lbl := lbl) (n := n) (z := z) (s := s)
  rw [he] at h; exact h

theorem newOrd_rmw {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {x : Memory × Promises.Thread}
    (h : x ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel) : NewOrdM mem x.1 := by
  obtain ⟨mem', th'⟩ := x
  obtain ⟨_, _, _, _, _, h⟩ := stepRmw_mem h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -⟩ | ⟨_, _, _, rfl, -⟩⟩
  · exact newOrd_eq rfl
  · intro t1 t2 m1 m2 h1 h12 _ hm2
    have := TermMem.lt_of_get hm2
    simp at this; omega
  · exact newOrd_eq rfl

theorem newOrd_rmwPair {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    NewOrdM mem mem' := by
  rcases TermFul.stepRmwPair_shape h with ⟨rfl, -⟩ | ⟨⟨m0, m1, rfl, h0, h1⟩, -⟩
  · exact newOrd_eq rfl
  · intro t1 t2 n1 n2 ht1 h12 hn1 hn2 hl
    have hlt := TermMem.lt_of_get hn2
    simp only [Array.size_push] at hlt
    have e1 : t1 = mem.size := by omega
    have e2 : t2 = mem.size + 1 := by omega
    subst e1; subst e2
    rw [push_lt (by simp), Array.getElem?_push_size] at hn1
    rw [show mem.size + 1 = (mem.push m0).size from (Array.size_push _).symm, Array.getElem?_push_size] at hn2
    cases hn1; cases hn2
    rw [h0, h1] at hl
    exact absurd hl.symm (next_ne a)

theorem newOrd_projInj {g : G} {s : St} {t S : Ty} {ws : List Word} {j : Nat} {p : List Word}
    {x : St × Nat × List Word} {y : St × List Word}
    (hx : x ∈ projM g s t ws) (hy : y ∈ injM g x.1 S j p) : NewOrdM s.mem y.1.mem := by
  obtain ⟨e1, -, -⟩ := TermFul.projM_keep hx
  refine newOrd_left e1 ?_
  unfold injM at hy
  split at hy
  · split at hy
    · simp only [List.mem_map] at hy
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := hy
      have h := newOrd_alloc hs
      dsimp only
      split
      · exact h
      · exact h
    · cases hy
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at hy
    obtain ⟨_, -, rfl⟩ := hy
    exact newOrd_eq rfl

#print axioms storeUnits_newInj
#print axioms newOrd_alloc
#print axioms newOrd_allocBuf
#print axioms newOrd_rmw
#print axioms newOrd_rmwPair
#print axioms newOrd_projInj

/-- **(operation)** `NewOrdM` for every operation. -/
theorem evalOp_newOrd {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (h : r ∈ evalOp g env σs s op) : NewOrdM s.mem r.1.mem := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first
         | exact newOrd_eq rfl
         | exact newOrd_allocBufE ‹_›
         | exact newOrd_allocBuf)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact newOrd_eq (TermFul.loadUnits_keep _ _ _ _ hx).1
         | exact newOrd_storeUnits hx
         | exact newOrd_alloc hx
         | exact newOrd_rmw hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact newOrd_projInj hx hy
         | exact newOrd_left (TermFul.loadUnits_keep _ _ _ _ hx).1 (newOrd_storeUnits hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact newOrd_left (TermFul.loadUnits_keep _ _ _ _ hx).1 (newOrd_storeUnits hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact newOrd_eq (TermFul.loadUnits_keep _ _ _ _ hx).1)
    | (simp only [Option.toList_some, List.mem_singleton] at h; subst h; dsimp only; exact newOrd_allocBuf)

/-- **(thread step)** `NewOrdM` for every thread step. -/
theorem tstep_newOrd {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (h : r ∈ tstep g mem pairs th) : NewOrdM mem r.1 := by
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact newOrd_eq rfl)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf]; exact newOrd_eq rfl)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact newOrd_eq rfl)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact newOrd_eq rfl)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_newOrd hx
         | exact newOrd_rmw hx
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact newOrd_rmwPair hx))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact newOrd_projInj hx hy)
    | (simp only [List.mem_map] at h  -- new arm: record write
       obtain ⟨x, hx, rfl⟩ := h
       try dsimp only
       split
       all_goals
         first
           | exact evalOp_newOrd hx
           | exact newOrd_rmw hx
           | (obtain ⟨mem', pairs', th'⟩ := x
              exact newOrd_rmwPair hx))

#print axioms evalOp_newOrd
#print axioms tstep_newOrd

/-! ## §3 New messages with their values

`RoleV us ws j v`: word `j` of a store of units `us` and data `ws` holds `v`: at a single-word unit
`v` is the data word's value; otherwise the word is in a two-word unit. -/

def RoleV (us : List Acc) (ws : List Word) (j : Nat) (v : WeakMem.Val) : Prop :=
  (TermFul.OneAt us j ∧ ∃ w, ws[j]? = some w ∧ v = w.val) ∨ TwoAt us j ∨ ∃ jj, j = jj + 1 ∧ TwoAt us jj

theorem roleV_cons1 {us : List Acc} {ws : List Word} {w : Word} {j : Nat} {v : WeakMem.Val}
    (h : RoleV us ws j v) : RoleV (.one :: us) (w :: ws) (j + 1) v := by
  rcases h with ⟨h1, x, h2, h3⟩ | h | ⟨jj, rfl, h⟩
  · exact .inl ⟨TermFul.OneAt.cons .one h1, x, by simpa using h2, h3⟩
  · exact .inr (.inl (TwoAt_cons .one h))
  · exact .inr (.inr ⟨jj + 1, by omega, TwoAt_cons .one h⟩)

theorem roleV_cons2 {us : List Acc} {ws : List Word} {w0 w1 : Word} {j : Nat} {v : WeakMem.Val}
    (h : RoleV us ws j v) : RoleV (.two :: us) (w0 :: w1 :: ws) (j + 2) v := by
  rcases h with ⟨h1, x, h2, h3⟩ | h | ⟨jj, rfl, h⟩
  · exact .inl ⟨TermFul.OneAt.cons .two h1, x, by simpa using h2, h3⟩
  · exact .inr (.inl (TwoAt_cons .two h))
  · exact .inr (.inr ⟨jj + 2, by omega, TwoAt_cons .two h⟩)

/-- **Where and what a store's new messages are.** -/
theorem storeUnits_newV {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m →
        ∃ j, m.loc = offs a (i + j) ∧ RoleV us ws j m.val
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      intro t m ht hm; exact absurd (TermMem.lt_of_get hm) (by omega)
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      have ih := storeUnits_newV us ws (i + 1) _ s' hs
      obtain ⟨-, g2, -⟩ := storeUnits_roles us ws (i + 1) _ s' hs
      have g2' : ∀ t, t < mem'.size → s'.mem[t]? = mem'[t]? := g2
      have ih' : ∀ (t : Nat) (m : Msg), mem'.size ≤ t → s'.mem[t]? = some m →
          ∃ j, m.loc = offs a (i + 1 + j) ∧ RoleV us ws j m.val := ih
      obtain ⟨t0, hcase, _⟩ := stepStore_cases hst
      intro t m ht hm
      rcases hcase with ⟨rfl, -, -⟩ | ⟨rfl, -⟩
      · by_cases hb : s.mem.size + 1 ≤ t
        · obtain ⟨j, hj, hr⟩ := ih' t m (by simp; omega) hm
          exact ⟨j + 1, by rw [hj, show i + 1 + j = i + (j + 1) by omega], roleV_cons1 hr⟩
        · have e1 : t = s.mem.size := by omega
          subst e1
          rw [g2' _ (by simp)] at hm
          simp at hm
          refine ⟨0, by rw [← hm]; rfl, .inl ⟨.here _, w, rfl, ?_⟩⟩
          rw [← hm]; exact TermFul.exprVal_dataE s pw w
      · obtain ⟨j, hj, hr⟩ := ih' t m ht hm
        exact ⟨j + 1, by rw [hj, show i + 1 + j = i + (j + 1) by omega], roleV_cons1 hr⟩
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have ih := storeUnits_newV us ws (i + 2) _ s' hs
      obtain ⟨-, g2, -⟩ := storeUnits_roles us ws (i + 2) _ s' hs
      obtain ⟨q1, -, -, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at ih g2 q1
      have g2' : ∀ t, t < R.1.size → s'.mem[t]? = R.1[t]? := g2
      have ih' : ∀ (t : Nat) (m : Msg), R.1.size ≤ t → s'.mem[t]? = some m →
          ∃ j, m.loc = offs a (i + 2 + j) ∧ RoleV us ws j m.val := ih
      have hsz : R.1.size = s.mem.size + 2 := by rw [q1]; simp
      have h0 : ∀ m, R.1[s.mem.size]? = some m → m.loc = offs a i := by
        intro m hm; rw [q1, push_lt (by simp)] at hm; simp at hm; rw [← hm]
      have h1' : ∀ m, R.1[s.mem.size + 1]? = some m → m.loc = offs a (i + 1) := by
        intro m hm; rw [q1, Array.getElem?_push, ite_eq_left (by simp)] at hm; rw [← Option.some.inj hm]
        simp [offs, WeakMem.Address.next, Nat.add_assoc]
      have hT0 : TwoAt (.two :: us) 0 := ⟨0, rfl, by simp [nWords]⟩
      intro t m ht hm
      by_cases hb : R.1.size ≤ t
      · obtain ⟨j, hj, hr⟩ := ih' t m hb hm
        exact ⟨j + 2, by rw [hj, show i + 2 + j = i + (j + 2) by omega], roleV_cons2 hr⟩
      · rw [g2' t (by omega)] at hm
        by_cases e : t = s.mem.size
        · subst e; exact ⟨0, by rw [h0 m hm]; rfl, .inr (.inl hT0)⟩
        · have e' : t = s.mem.size + 1 := by omega
          subst e'; exact ⟨1, h1' m hm, .inr (.inr ⟨0, rfl, hT0⟩)⟩
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

#print axioms storeUnits_newV

/-- (§3) An operation's new message at `loc` holding `v`: a word of a `storeUnits` call
(`UnitsOp`) in its role, a word of an `stp`'s pair, or a `fetch`'s RMW at its address. -/
def OpNewV (g : G) (env : Env) (s : St) (op : Op) (loc : Address) (v : WeakMem.Val) : Prop :=
  (∃ pw b rel us ws j, TermFul.UnitsOp g env s op pw b rel us ws ∧ loc = offs b j ∧ RoleV us ws j v) ∨
  (∃ rel a v0 v1 tk t pw b ws j, op = .stp rel a v0 v1 tk ∧ evalAt env a = some (t, [pw]) ∧
    addrOf pw = some b ∧ loc = offs b j ∧ RoleV [.two] ws j v) ∨
  (∃ o acq rel a v' t pw, op = .fetch o acq rel a v' ∧ evalAt env a = some (t, [pw]) ∧
    addrOf pw = some loc)

theorem units_newV {k : Promises.Knobs} {arch : Arch} {g : G} {env : Env} {op : Op} {pw : Word}
    {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hm1 : s1.mem = s.mem) (hs : s' ∈ storeUnits k arch pw b rel us ws 0 s1)
    (hU : TermFul.UnitsOp g env s op pw b rel us ws) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → OpNewV g env s op m.loc m.val := by
  intro t m ht hm
  obtain ⟨j, hl, hr⟩ := storeUnits_newV us ws 0 s1 s' hs t m (by rw [hm1]; exact ht) hm
  exact .inl ⟨pw, b, rel, us, ws, j, hU, by rw [hl, Nat.zero_add], hr⟩

theorem evalOp_store_newV {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v : At}
    {o : Option At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.store rel a v o)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.store rel a v o) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_newV rfl hs (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchg_newV {g : G} {env : Env} {σs : List Ty} {s : St} {a v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchg a v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.xchg a v) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := TermFul.loadUnits_keep _ _ _ _ hx
       exact units_newV k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchgAt_newV {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchgAt bb i v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.xchgAt bb i v) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := TermFul.loadUnits_keep _ _ _ _ hx
       exact units_newV k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_xchgAtF_newV {g : G} {env : Env} {σs : List Ty} {s : St} {bb i : At} {p : List Nat}
    {v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.xchgAtF bb i p v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.xchgAtF bb i p v) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, -⟩ := TermFul.loadUnits_keep _ _ _ _ hx
       exact units_newV k1 hy (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_bufInit_newV {g : G} {env : Env} {σs : List Ty} {s : St} {bb i x : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.bufInit bb i x)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.bufInit bb i x) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_newV rfl hs (by dsimp only [TermFul.UnitsOp]; fillx))

theorem evalOp_stl_newV {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stl bb i v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.stl bb i v) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := TermFul.loadUnits_keep _ _ _ _ hx
         exact units_newV k1 hy (by dsimp only [TermFul.UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stlw_newV {g : G} {env : Env} {σs : List Ty} {s : St} {bb wi jl v : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stlw bb wi jl v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.stlw bb wi jl v) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, -⟩ := TermFul.loadUnits_keep _ _ _ _ hx
         exact units_newV k1 hy (by dsimp only [TermFul.UnitsOp]; fillx)
       · simp at h)


theorem evalOp_stp_newV {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v0 v1 tk : At}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.stp rel a v0 v1 tk)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.stp rel a v0 v1 tk) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       intro t m ht hm
       obtain ⟨j, hl, hr⟩ := storeUnits_newV _ _ 0 s s' hs t m ht hm
       exact .inr (.inl ⟨_, _, _, _, _, _, _, _, _, j, rfl, ‹_›, ‹_›, by rw [hl, Nat.zero_add], hr⟩))

theorem evalOp_fetch_newV {g : G} {env : Env} {σs : List Ty} {s : St} {o : FetchOp} {acq rel : Bool}
    {a v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      OpNewV g env s (.fetch o acq rel a v) m.loc m.val := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
       intro t m ht hm
       have hl := rmw_newLoc hx t m ht hm
       exact .inr (.inr ⟨_, _, _, _, _, _, _, rfl, ‹_›, by rw [hl]; assumption⟩))

/-- **(§3, operation)**: every message an operation appends is at one of its fresh labels or an
`OpNewV` word. -/
theorem evalOp_newV {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hpl : PromLt s) (h : r ∈ evalOp g env σs s op) :
    ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → r.1.mem[t]? = some m →
      FreshIn g s.nalloc r.1.nalloc m.loc.label ∨ OpNewV g env s op m.loc m.val := by
  intro t m ht hm
  cases op
  case spawn => simp [evalOp] at h
  case store => exact .inr (evalOp_store_newV h t m ht hm)
  case xchg => exact .inr (evalOp_xchg_newV h t m ht hm)
  case xchgAt => exact .inr (evalOp_xchgAt_newV h t m ht hm)
  case xchgAtF => exact .inr (evalOp_xchgAtF_newV h t m ht hm)
  case bufInit => exact .inr (evalOp_bufInit_newV h t m ht hm)
  case stl => exact .inr (evalOp_stl_newV h t m ht hm)
  case stlw => exact .inr (evalOp_stlw_newV h t m ht hm)
  case stp => exact .inr (evalOp_stp_newV h t m ht hm)
  case fetch => exact .inr (evalOp_fetch_newV h t m ht hm)
  all_goals exact (evalOp_new hpl h t m ht hm).imp id (fun ⟨_, ha, _⟩ => by simp [OpTgt] at ha)

/-- A `cas` appends at most its new value, at its address. -/
theorem rmw_casNew {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts} {s : St}
    {pw nw : Word} {b : Address} {ev : WeakMem.Val} {acq rel : Bool} {x : Memory × Promises.Thread}
    (h : x ∈ Promises.stepRmw k arch mem pairs (mth s pw nw nw) 1 b (.cas ev) (dataE 1 nw) [0] acq rel) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → x.1[t]? = some m → m.loc = b ∧ m.val = nw.val := by
  obtain ⟨mem', th'⟩ := x
  intro t m ht hm
  dsimp only at hm
  obtain ⟨_, _, _, _, _, h⟩ := stepRmw_mem h
  rcases h with ⟨-, rfl, -⟩ | ⟨-, ⟨mv, rfl, -⟩ | ⟨_, _, _, rfl, -⟩⟩
  · exact absurd (TermMem.lt_of_get hm) (by omega)
  · rw [Array.getElem?_push] at hm
    split at hm
    · cases hm
      exact ⟨rfl, by simp only [WeakMem.RmwKind.apply]; exact TermFul.rmwNewVal_dataE s pw nw⟩
    · exact absurd (TermMem.lt_of_get hm) (by omega)
  · exact absurd (TermMem.lt_of_get hm) (by omega)

/-- (§3) Where and what a thread step's new message is. -/
def TermNewV (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (loc : Address) (v : WeakMem.Val) : Prop :=
  (∃ x op e, th.term = .let_ x op e ∧ OpNewV g th.env (stOf mem pairs th) op loc v) ∨
  (∃ acq rel w e v' tn ok fail tw pw te ew tv nw, th.term = .cas acq rel w e v' tn ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ evalAt th.env e = some (te, [ew]) ∧
    evalAt th.env v' = some (tv, [nw]) ∧ addrOf pw = some loc ∧ v = nw.val) ∨
  (∃ acq rel w e0 e1 v0 v1 tn ok fail tw pw A, th.term = .casp acq rel w e0 e1 v0 v1 tn ok fail ∧
    evalAt th.env w = some (tw, [pw]) ∧ addrOf pw = some A ∧ (loc = A ∨ loc = A.next))

/-- **(§3, thread step)**: every message a thread step appends is at one of its fresh labels or a
`TermNewV` word. -/
theorem tstep_newV {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hpl : PromLt (stOf mem pairs th)) (h : r ∈ tstep g mem pairs th) :
    ∀ (t : Nat) (m : Msg), mem.size ≤ t → r.1[t]? = some m →
      FreshIn g th.nalloc r.2.2.nalloc m.loc.label ∨ TermNewV g mem pairs th m.loc m.val := by
  intro t m ht hm
  simp only [tstep] at h
  split at h <;> rename_i hT
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; dsimp only at hm; exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [List.mem_singleton] at h; subst h; dsimp only [fenceS, stOf] at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       dsimp only at hm
       exact absurd (TermMem.lt_of_get hm) (by omega))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact (evalOp_newV hpl hx t m ht hm).imp id (fun h => .inl ⟨_, _, _, hT, h⟩)
         | (obtain ⟨hl, hv⟩ := rmw_casNew hx t m ht hm
            exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hT, ‹_›, ‹_›, ‹_›,
              by rw [hl]; assumption, hv⟩)))
         | (obtain ⟨mem', pairs', th'⟩ := x
            exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hT, ‹_›, ‹_›,
              rmwPair_newLoc hx t m ht hm⟩))))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact .inl ((newIn_projInj (X := fun _ => False) hpl hx hy t m ht hm).resolve_right id))
    | (simp only [List.mem_map] at h  -- new arm: record write
       obtain ⟨x, hx, rfl⟩ := h
       try dsimp only
       split
       all_goals
         first
           | exact (evalOp_newV hpl hx t m ht hm).imp id (fun h => .inl ⟨_, _, _, hT, h⟩)
           | (obtain ⟨hl, hv⟩ := rmw_casNew hx t m ht hm
              exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hT, ‹_›, ‹_›, ‹_›,
                by rw [hl]; assumption, hv⟩)))
           | (obtain ⟨mem', pairs', th'⟩ := x
              exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hT, ‹_›, ‹_›,
                rmwPair_newLoc hx t m ht hm⟩))))

#print axioms evalOp_newV
#print axioms tstep_newV

end TermUndefLow

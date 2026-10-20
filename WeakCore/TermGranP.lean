import WeakCore.TermGranW
import WeakCore.TermPlantF

/-! # TermGranP: `GranuleWP` across memory-level writes (shape-independent helpers)

`GranuleWP sto mem pairs P` (own promises `P` exempt from clause 2) across one push, a pair push,
a typed store by units, a store by units at a label with no pair store at or past the written
offsets (a fresh label), and the allocation placeholders.  `GranuleWP … []` is `GranuleW`.
Also the layout fact `AtOff` + a two-word unit of the component ⇒ `TwoAtT` (on a laid-out cell). -/

namespace TermGranP
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermGranW
open WeakMem (Msg Memory Address Ts Arch AllocLabel)

/-! ## Layout -/

/-- A two-word unit of a component of a laid-out cell type starts a two-word unit of the cell. -/
theorem twoAtT_of_atOff {T U : Ty} {o j : Nat} {us : List Acc} (hlay : LayT T) (h : AtOff T o U)
    (hus : accs U = some us) (hj : TwoAt us j) : TwoAtT T (o + j) := by
  rcases hlay with hacc | ⟨N, e, hTe, -⟩
  · obtain ⟨L, hL⟩ : ∃ L, accs T = some L := by
      cases e : accs T with
      | none => exact absurd e hacc
      | some L => exact ⟨L, rfl⟩
    obtain ⟨pre, post, hLe, hn⟩ := AtOff_embed h hL hus
    refine ⟨0, T, L, o + j, Or.inl ⟨rfl, rfl, hacc⟩, hL, ?_, by omega⟩
    rw [hLe, ← hn]; exact TwoAt_embed hj
  · rcases AtOff_arr_elem h hTe with hU | ⟨us', j', o', hus', hj', ho, hat⟩
    · subst hU; rw [hTe] at hus; simp [accs] at hus
    · obtain ⟨pre, post, hLe, hn⟩ := AtOff_embed hat hus' hus
      refine ⟨j' * nWords us', e, us', o' + j, Or.inr ⟨N, us', j', hTe, hus', hj', rfl⟩, hus', ?_, by omega⟩
      rw [hLe, ← hn]; exact TwoAt_embed hj

/-- A one-word unit of a component starts no two-word unit of the cell. -/
theorem notTwoAtT_of_oneAt {T U : Ty} {o j : Nat} {us : List Acc} (h : AtOff T o U)
    (hus : accs U = some us) (hj : TermFul.OneAt us j) : ¬ TwoAtT T (o + j) :=
  fun h2 => (TermPlantF.oneAt_twoAtT h hus hj h2).1 rfl

/-! ## `GranuleWP` and `GranuleW` -/

theorem granuleW_of_nil {sto : Sto} {mem : Memory} {pairs : List Ts} (hG : GranuleWP sto mem pairs []) :
    GranuleW sto mem pairs :=
  ⟨hG.1, fun q hq v m0 mv h0 hv hl hqv => hG.2.1 q hq v m0 mv h0 hv hl hqv (List.not_mem_nil), hG.2.2.1,
    fun v mv cl o hv hc ho hT => hG.2.2.2 v mv cl o hv List.not_mem_nil hc ho hT⟩

theorem granuleWP_nil_iff {sto : Sto} {mem : Memory} {pairs : List Ts} :
    GranuleWP sto mem pairs [] ↔ GranuleW sto mem pairs :=
  ⟨granuleW_of_nil, granuleWP_of []⟩

theorem granuleWP_sto {sto sto2 : Sto} {mem : Memory} {pairs P : List Ts} (hG : GranuleWP sto mem pairs P)
    (h : ∀ l c, sto2 l = some c → sto l = some c ∨
      (∀ q ∈ pairs, ∀ m0, mem[q]? = some m0 → m0.loc.label ≠ l) ∧
      ∀ (v : Nat) (mv : Msg) (o : Nat), mem[v]? = some mv → v ∉ P → mv.loc.label = l → mv.loc.offset = o + 1 →
        TwoAtT c.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1) :
    GranuleWP sto2 mem pairs P := by
  refine ⟨hG.1, hG.2.1, fun q hq m0 cl h0 hc => ?_, fun v mv cl o hv hP hc ho hT => ?_⟩
  · rcases h _ _ hc with h1 | h1
    · exact hG.2.2.1 q hq m0 cl h0 h1
    · exact absurd rfl (h1.1 q hq m0 h0)
  · rcases h _ _ hc with h1 | h1
    · exact hG.2.2.2 v mv cl o hv hP h1 ho hT
    · exact h1.2 v mv o hv hP rfl ho hT

/-! ## Pushes -/

theorem pairs_lt {sto : Sto} {mem : Memory} {pairs P : List Ts} (hG : GranuleWP sto mem pairs P) :
    ∀ q : Nat, q ∈ pairs → q + 1 < mem.size := fun q hq => by
  obtain ⟨_, _, _, h1, _⟩ := hG.1 q hq
  exact (Array.getElem?_eq_some_iff.1 h1).1

/-- **One push** at a word where no pair store starts. -/
theorem granuleWP_pushOne {sto : Sto} {mem : Memory} {pairs P : List Ts} {m : Msg}
    (hG : GranuleWP sto mem pairs P)
    (hn : ∀ q ∈ pairs, ∀ m0, mem[q]? = some m0 → m0.loc ≠ m.loc) (h4 : SndNL sto m) :
    GranuleWP sto (mem.push m) pairs P := by
  have hlt := pairs_lt hG
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have hold : ∀ q, q < mem.size → (mem.push m)[q]? = mem[q]? := fun q hq => push_get_lt hq
  refine ⟨fun q hq => ?_, fun q hq v m0 mv h0 hv hl hqv hP => ?_, fun q hq m0 cl h0 hc => ?_,
    fun v mv cl o hv hP hc ho hT => ?_⟩
  · obtain ⟨a0, a1, h0, h1, hl⟩ := g1 q hq
    have := hlt q hq
    exact ⟨a0, a1, by rw [hold q (by omega)]; exact h0, by rw [hold (q + 1) this]; exact h1, hl⟩
  · have hq1 := hlt q hq
    rw [hold q (by omega)] at h0
    by_cases hvs : v < mem.size
    · rw [hold v hvs] at hv
      exact g2 q hq v m0 mv h0 hv hl hqv hP
    · have hv2 : v = mem.size := by
        have := (Array.getElem?_eq_some_iff.1 hv).1; simp at this; omega
      subst hv2
      rw [push_get_eq] at hv; cases hv
      exact absurd hl.symm (hn q hq m0 h0)
  · have hq1 := hlt q hq
    rw [hold q (by omega)] at h0
    exact g3 q hq m0 cl h0 hc
  · by_cases hvs : v < mem.size
    · rw [hold v hvs] at hv
      exact g4 v mv cl o hv hP hc ho hT
    · have hv2 : v = mem.size := by
        have := (Array.getElem?_eq_some_iff.1 hv).1; simp at this; omega
      subst hv2
      rw [push_get_eq] at hv; cases hv
      exact .inl (h4 cl o hc ho hT)

/-- A push at a word of a cell of `sto` that neither starts nor ends a two-word unit. -/
theorem granuleWP_pushOne_notTwo {sto : Sto} {mem : Memory} {pairs P : List Ts} {m : Msg} {cl : Cell}
    (hG : GranuleWP sto mem pairs P) (hc : sto m.loc.label = some cl) (hn : ¬ TwoAtT cl.ty m.loc.offset)
    (hs : ∀ o, m.loc.offset = o + 1 → ¬ TwoAtT cl.ty o) :
    GranuleWP sto (mem.push m) pairs P :=
  granuleWP_pushOne hG (fun q hq m0 h0 e => hn (by rw [← e]; exact hG.2.2.1 q hq m0 cl h0 (by rw [e]; exact hc)))
    fun cl2 o hc2 ho hT => by rw [hc] at hc2; cases hc2; exact absurd hT (hs o ho)

/-- A push at a label where no pair store is. -/
theorem granuleWP_push_fresh {sto : Sto} {mem : Memory} {pairs P : List Ts} {m : Msg}
    (hG : GranuleWP sto mem pairs P)
    (hf : ∀ q ∈ pairs, ∀ m0, mem[q]? = some m0 → m0.loc.label ≠ m.loc.label) (h4 : SndNL sto m) :
    GranuleWP sto (mem.push m) pairs P :=
  granuleWP_pushOne hG (fun q hq m0 h0 e => hf q hq m0 h0 (by rw [e])) h4

/-- **A pair push** at `a`, `a.next`. -/
theorem granuleWP_pushPair {sto : Sto} {mem : Memory} {pairs P : List Ts} {m0 m1 : Msg}
    (hG : GranuleWP sto mem pairs P) (hl : m1.loc = m0.loc.next)
    (hn : ∀ q ∈ pairs, ∀ x, mem[q]? = some x → x.loc ≠ m1.loc)
    (hT : ∀ cl, sto m0.loc.label = some cl → TwoAtT cl.ty m0.loc.offset) :
    GranuleWP sto ((mem.push m0).push m1) (pairs ++ [mem.size]) P := by
  have hlt := pairs_lt hG
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have hold : ∀ q, q < mem.size → ((mem.push m0).push m1)[q]? = mem[q]? := fun q hq => by
    rw [push_get_lt (by simp; omega), push_get_lt hq]
  have e0 : ((mem.push m0).push m1)[mem.size]? = some m0 := by
    rw [push_get_lt (by simp), push_get_eq]
  have e1 : ((mem.push m0).push m1)[mem.size + 1]? = some m1 := by
    have : mem.size + 1 = (mem.push m0).size := by simp
    rw [this, push_get_eq]
  have hsz : ∀ v (x : Msg), ((mem.push m0).push m1)[v]? = some x →
      (v < mem.size ∧ mem[v]? = some x) ∨ (v = mem.size ∧ x = m0) ∨ (v = mem.size + 1 ∧ x = m1) := by
    intro v x hv
    rcases Nat.lt_or_ge v mem.size with h | h
    · exact .inl ⟨h, by rw [← hold v h]; exact hv⟩
    · have hvl := (Array.getElem?_eq_some_iff.1 hv).1
      simp at hvl
      rcases (show v = mem.size ∨ v = mem.size + 1 by omega) with rfl | rfl
      · rw [e0] at hv; cases hv; exact .inr (.inl ⟨rfl, rfl⟩)
      · rw [e1] at hv; cases hv; exact .inr (.inr ⟨rfl, rfl⟩)
  refine ⟨fun q hq => ?_, fun q hq v x0 xv h0 hv hlq hqv hP => ?_, fun q hq x0 cl h0 hc => ?_,
    fun v xv cl o hv hP hc ho hTo => ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨a0, a1, h0, h1, hl⟩ := g1 q hq
      have := hlt q hq
      exact ⟨a0, a1, by rw [hold q (by omega)]; exact h0, by rw [hold (q + 1) this]; exact h1, hl⟩
    · simp at hq; subst hq
      exact ⟨m0, m1, e0, e1, hl⟩
  · rcases List.mem_append.1 hq with hq | hq
    · have hq1 := hlt q hq
      rw [hold q (by omega)] at h0
      rcases hsz v xv hv with ⟨hvs, hv2⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact List.mem_append_left _ (g2 q hq v x0 xv h0 hv2 hlq hqv hP)
      · exact List.mem_append_right _ (by simp)
      · exact absurd hlq.symm (hn q hq x0 h0)
    · simp at hq; subst hq
      rw [e0] at h0; cases h0
      have hqv2 : mem.size < v := hqv
      rcases hsz v xv hv with ⟨hvs, -⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · omega
      · omega
      · exact absurd (hl.symm.trans hlq) (next_ne _)
  · rcases List.mem_append.1 hq with hq | hq
    · have hq1 := hlt q hq
      rw [hold q (by omega)] at h0
      exact g3 q hq x0 cl h0 hc
    · simp at hq; subst hq
      rw [e0] at h0; cases h0
      exact hT cl hc
  · rcases hsz v xv hv with ⟨hvs, hv2⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases g4 v xv cl o hv2 hP hc ho hTo with h | ⟨q, hq, e⟩
      · exact .inl h
      · exact .inr ⟨q, List.mem_append_left _ hq, e⟩
    · exact absurd (by rw [← ho]; exact hT cl hc) (TwoAtT_not_succ hTo)
    · exact .inr ⟨mem.size, List.mem_append_right _ (by simp), rfl⟩

/-! ## Stores by units -/

/-- **A store by units** at a cell `cl` of `sto` (`GranuleWP` form of `granuleW_storeUnits`). -/
theorem granuleWP_storeUnits {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {sto : Sto} {cl : Cell} {P : List Ts} (hc : sto a.label = some cl) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      (∀ j, OneAt us j → ¬ TwoAtT cl.ty (a.offset + i + j)) →
      (∀ j, OneAt us j → ∀ o, a.offset + i + j = o + 1 → ¬ TwoAtT cl.ty o) →
      (∀ j, TwoAt us j → TwoAtT cl.ty (a.offset + i + j)) →
      GranuleWP sto s.mem s.pairs P → GranuleWP sto s'.mem s'.pairs P
  | [], _, _, s, s', hs, _, _, _, hG => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hG
  | .one :: us, w :: ws, i, s, s', hs, hOne, hOne2, hTwo, hG => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      refine granuleWP_storeUnits hc us ws (i + 1) _ s' hs (fun j hj => ?_) (fun j hj o ho => ?_)
        (fun j hj => ?_) ?_
      · have := hOne (j + 1) (OneAt_cons .one hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 1) = x + (i + 1) + j)) a.offset] at this; exact this
      · exact hOne2 (j + 1) (OneAt_cons _ hj) o ((fun x y : Nat => (by omega : x + (i + 1) + j = y + 1 → x + i + (j + 1) = y + 1)) a.offset o ho)
      · have := hTwo (j + 1) (TwoAt_cons .one hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 1) = x + (i + 1) + j)) a.offset] at this; exact this
      · obtain ⟨t, hcase, -⟩ := stepStore_cases hst
        rcases hcase with ⟨e, -, -⟩ | ⟨e, -⟩
        · show GranuleWP sto mem' s.pairs P
          rw [e]
          refine granuleWP_pushOne_notTwo hG (cl := cl) (by simp only [offs_label]; exact hc) ?_ ?_
          · simp only [offs_offset]
            have := hOne 0 ⟨0, rfl, rfl⟩
            simpa using this
          · intro o ho
            simp only [offs_offset] at ho
            exact hOne2 0 ⟨0, rfl, rfl⟩ o (by omega)
        · show GranuleWP sto mem' s.pairs P
          rw [e]; exact hG
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hOne, hOne2, hTwo, hG => by
      simp only [storeUnits] at hs
      obtain ⟨q1, q2, -, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      refine granuleWP_storeUnits hc us ws (i + 2) _ s' hs (fun j hj => ?_) (fun j hj o ho => ?_)
        (fun j hj => ?_) ?_
      · have := hOne (j + 2) (OneAt_cons .two hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 2) = x + (i + 2) + j)) a.offset] at this; exact this
      · exact hOne2 (j + 2) (OneAt_cons _ hj) o ((fun x y : Nat => (by omega : x + (i + 2) + j = y + 1 → x + i + (j + 2) = y + 1)) a.offset o ho)
      · have := hTwo (j + 2) (TwoAt_cons .two hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 2) = x + (i + 2) + j)) a.offset] at this; exact this
      · show GranuleWP sto (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).1 (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).2.1 P
        rw [q1, q2]
        have h2 : TwoAtT cl.ty (a.offset + i) := by
          have := hTwo 0 ⟨0, rfl, rfl⟩; simpa using this
        refine granuleWP_pushPair hG rfl (fun q hq x hx e => ?_) (fun cl2 hc2 => ?_)
        · have hc2 : sto x.loc.label = some cl := by rw [e]; exact hc
          have := hG.2.2.1 q hq x cl hx hc2
          rw [e] at this
          exact TwoAtT_not_succ h2 this
        · simp only [offs_label] at hc2
          rw [hc] at hc2; cases hc2
          simpa only [offs_offset] using h2
  | .one :: _, [], _, _, s', hs, _, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _, _, _, _ => by simp [storeUnits] at hs

theorem lt_add_mono {o b i k : Nat} (h : o < b + i) : o < b + (i + k) := by omega

theorem lt_add_ne {o b i k : Nat} (h : o < b + i) (e : o = b + i + k) : False := by omega

/-- Every pair store at label `l` lies below offset `n` (both its words). -/
def PairsBelow (mem : Memory) (pairs : List Ts) (l : AllocLabel) (n : Nat) : Prop :=
  ∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc.label = l → m0.loc.offset < n

/-- **A store by units at an untyped label whose pair stores lie below the written offsets** (a
fresh label). -/
theorem granuleWP_storeUnitsF {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {sto : Sto} {P : List Ts} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      sto a.label = none →
      PairsBelow s.mem s.pairs a.label (a.offset + i) →
      GranuleWP sto s.mem s.pairs P → GranuleWP sto s'.mem s'.pairs P
  | [], _, _, s, s', hs, _, _, hG => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hG
  | .one :: us, w :: ws, i, s, s', hs, hTwo, hB, hG => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      have hlt := pairs_lt hG
      obtain ⟨t, hcase, -⟩ := stepStore_cases hst
      have hB2 : PairsBelow mem' s.pairs a.label (a.offset + (i + 1)) := by
        intro q hq m0 h0 hl
        rcases hcase with ⟨e, -, -⟩ | ⟨e, -⟩
        · rw [e] at h0
          rw [push_get_lt (by have := hlt q hq; omega)] at h0
          exact lt_add_mono (hB q hq m0 h0 hl)
        · rw [e] at h0
          exact lt_add_mono (hB q hq m0 h0 hl)
      refine granuleWP_storeUnitsF us ws (i + 1) _ s' hs hTwo hB2 ?_
      · rcases hcase with ⟨e, -, -⟩ | ⟨e, -⟩
        · show GranuleWP sto mem' s.pairs P
          rw [e]
          refine granuleWP_pushOne hG (fun q hq m0 h0 hl => ?_) (fun cl o hc => ?_)
          · have hl1 : m0.loc.label = a.label := by rw [hl]; rfl
            have h2 : m0.loc.offset = a.offset + i + 0 := by rw [hl]; rfl
            exact lt_add_ne (hB q hq m0 h0 hl1) h2
          · simp only [offs_label] at hc; rw [hTwo] at hc; cases hc
        · show GranuleWP sto mem' s.pairs P
          rw [e]; exact hG
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hTwo, hB, hG => by
      simp only [storeUnits] at hs
      obtain ⟨q1, q2, -, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      have hlt := pairs_lt hG
      refine granuleWP_storeUnitsF us ws (i + 2) _ s' hs hTwo ?_ ?_
      · show PairsBelow (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).1 (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).2.1 a.label (a.offset + (i + 2))
        rw [q1, q2]
        intro q hq m0 h0 hl
        rcases List.mem_append.1 hq with hq | hq
        · have := hlt q hq
          rw [push_get_lt (by rw [Array.size_push]; omega), push_get_lt (by omega)] at h0
          exact lt_add_mono (hB q hq m0 h0 hl)
        · simp at hq; subst hq
          rw [push_get_lt (by simp), push_get_eq] at h0; cases h0
          simp only [offs_offset]; exact Nat.add_lt_add_left (by omega) _
      · show GranuleWP sto (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).1 (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).2.1 P
        rw [q1, q2]
        refine granuleWP_pushPair hG rfl (fun q hq x hx e => ?_) (fun cl2 hc2 => ?_)
        · have hl1 : x.loc.label = a.label := by rw [e]; rfl
          have h2 : x.loc.offset = a.offset + i + 1 := by rw [e]; rfl
          exact lt_add_ne (hB q hq x hx hl1) h2
        · simp only [offs_label] at hc2; rw [hTwo] at hc2; cases hc2
  | .one :: _, [], _, _, s', hs, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs, _, _, _ => by simp [storeUnits] at hs

/-! ## Allocation -/

/-- No pair store at label `l`. -/
def NoPairAt (mem : Memory) (pairs : List Ts) (l : AllocLabel) : Prop :=
  ∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc.label ≠ l

/-- Placeholder pushes at a label with no pair store. -/
theorem granuleWP_foldPush {sto : Sto} {pairs P : List Ts} (f : Nat → Msg) (l : AllocLabel)
    (hf : ∀ j, (f j).loc.label = l) (hnone : sto l = none) :
    ∀ (js : List Nat) (mem : Memory), GranuleWP sto mem pairs P → NoPairAt mem pairs l →
      GranuleWP sto (js.foldl (fun m j => m.push (f j)) mem) pairs P ∧
        NoPairAt (js.foldl (fun m j => m.push (f j)) mem) pairs l
  | [], mem, hG, hN => ⟨hG, hN⟩
  | j :: js, mem, hG, hN => by
      simp only [List.foldl_cons]
      refine granuleWP_foldPush f l hf hnone js _ (granuleWP_push_fresh hG (fun q hq m0 h0 => by
        rw [hf j]; exact hN q hq m0 h0) fun cl o hc => by rw [hf j, hnone] at hc; cases hc) fun q hq m0 h0 => ?_
      have := pairs_lt hG q hq
      rw [push_get_lt (by omega)] at h0
      exact hN q hq m0 h0

theorem pairsBelow_of_noPair {mem : Memory} {pairs : List Ts} {l : AllocLabel} {n : Nat}
    (h : NoPairAt mem pairs l) : PairsBelow mem pairs l n :=
  fun q hq m0 h0 hl => absurd hl (h q hq m0 h0)

/-- **`alloc`** at an untyped label with no pair store. -/
theorem granuleWP_alloc {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} {sto : Sto} {P : List Ts}
    (hr : r ∈ alloc k arch lbl us ws s) (hG : GranuleWP sto s.mem s.pairs P) (hN : NoPairAt s.mem s.pairs lbl)
    (hnone : sto lbl = none) :
    GranuleWP sto r.1.mem r.1.pairs P := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s2, hs2, rfl⟩ := hr
  obtain ⟨hG1, hN1⟩ := granuleWP_foldPush (fun j => (⟨offs ⟨lbl, 0⟩ j, .undef, 0⟩ : Msg)) lbl (fun _ => rfl)
    hnone (List.range (nWords us)) s.mem hG hN
  exact granuleWP_storeUnitsF us ws 0 _ s2 hs2 hnone (pairsBelow_of_noPair hN1) hG1

/-- **`allocBuf`** at an untyped label with no pair store. -/
theorem granuleWP_allocBuf {lbl : AllocLabel} {n : Nat} {z : Option (List WeakMem.Val)} {s : St} {sto : Sto}
    {P : List Ts} (hG : GranuleWP sto s.mem s.pairs P) (hN : NoPairAt s.mem s.pairs lbl) (hnone : sto lbl = none) :
    GranuleWP sto (allocBuf lbl n z s).1.mem (allocBuf lbl n z s).1.pairs P := by
  unfold allocBuf
  exact (granuleWP_foldPush _ lbl (fun _ => rfl) hnone (List.range n) s.mem hG hN).1

/-! ## Read-modify-writes -/

/-- **A single RMW** at `a`, where no pair store starts, and which ends no two-word unit. -/
theorem granuleWP_stepRmw {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {sto : Sto} {P : List Ts}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hG : GranuleWP sto mem pairs P) (hn : ∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc ≠ a)
    (hs : ∀ cl o, sto a.label = some cl → a.offset = o + 1 → ¬ TwoAtT cl.ty o) :
    GranuleWP sto mem' pairs P := by
  obtain ⟨_, _, _, _, _, hc⟩ := TermStep.stepRmw_mem h
  rcases hc with ⟨-, e, -⟩ | ⟨-, ⟨mv, e, -⟩ | ⟨-, -, -, e, -⟩⟩
  · rw [e]; exact hG
  · rw [e]; exact granuleWP_pushOne hG hn fun cl o hc ho hT => absurd hT (hs cl o hc ho)
  · rw [e]; exact hG

/-- **A pair RMW** at `a`, `a.next`. -/
theorem granuleWP_stepRmwPair {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool} {sto : Sto} {P : List Ts}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel)
    (hG : GranuleWP sto mem pairs P) (hn : ∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc ≠ a.next)
    (hT : ∀ cl, sto a.label = some cl → TwoAtT cl.ty a.offset) :
    GranuleWP sto mem' pairs' P := by
  rcases TermFul.stepRmwPair_shape h with ⟨rfl, rfl⟩ | ⟨⟨m0, m1, rfl, h0, h1⟩, rfl, -⟩
  · exact hG
  · refine granuleWP_pushPair hG (by rw [h0, h1]) (fun q hq x hx => by rw [h1]; exact hn q hq x hx) ?_
    rw [h0]; exact hT

/-! ## Growing the store typing -/

/-- **New cells**: a cell of `sto2` not in `sto` has every pair store at its label starting a two-word
unit of it, and every non-`P` message at the second word of a two-word unit of it holding no pointer
or ending a pair store. -/
theorem granuleWP_lift {sto sto2 : Sto} {mem : Memory} {pairs P : List Ts} (hG : GranuleWP sto mem pairs P)
    (h : ∀ l c, sto2 l = some c → sto l = some c ∨
      (∀ q ∈ pairs, ∀ m0 : Msg, mem[q]? = some m0 → m0.loc.label = l → TwoAtT c.ty m0.loc.offset) ∧
      ∀ (v : Nat) (mv : Msg) (o : Nat), mem[v]? = some mv → v ∉ P → mv.loc.label = l → mv.loc.offset = o + 1 →
        TwoAtT c.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1) :
    GranuleWP sto2 mem pairs P := by
  refine ⟨hG.1, hG.2.1, fun q hq m0 cl h0 hc => ?_, fun v mv cl o hv hP hc ho hT => ?_⟩
  · rcases h _ _ hc with h1 | h1
    · exact hG.2.2.1 q hq m0 cl h0 h1
    · exact h1.1 q hq m0 h0 rfl
  · rcases h _ _ hc with h1 | h1
    · exact hG.2.2.2 v mv cl o hv hP h1 ho hT
    · exact h1.2 v mv o hv hP rfl ho hT

end TermGranP

#print axioms TermGranP.twoAtT_of_atOff
#print axioms TermGranP.notTwoAtT_of_oneAt
#print axioms TermGranP.granuleWP_nil_iff
#print axioms TermGranP.granuleWP_sto
#print axioms TermGranP.granuleWP_pushOne
#print axioms TermGranP.granuleWP_pushOne_notTwo
#print axioms TermGranP.granuleWP_push_fresh
#print axioms TermGranP.granuleWP_pushPair
#print axioms TermGranP.granuleWP_storeUnits
#print axioms TermGranP.granuleWP_storeUnitsF
#print axioms TermGranP.granuleWP_foldPush
#print axioms TermGranP.granuleWP_alloc
#print axioms TermGranP.granuleWP_allocBuf
#print axioms TermGranP.granuleWP_stepRmw
#print axioms TermGranP.granuleWP_stepRmwPair
#print axioms TermGranP.granuleWP_lift

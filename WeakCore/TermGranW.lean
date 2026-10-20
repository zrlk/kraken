import WeakCore.TermPtrRts

/-!
# TermGranW: granules are written whole (`granW`)

`TermPtrRts.GranuleW sto mem pairs`: a pair store's messages are at consecutive words; once a pair is
written at a word, every later message there is a pair store's first; a pair store at a cell of
`sto` starts a two-word unit of the cell.

* `granuleW_init` — the empty memory.
* `granuleW_partner` — **the load lemma**: a two-word read not straddling a pair, whose second word
  is a pair store's second half, read that pair store's first half.
* `granuleW_pushOne`, `granuleW_pushPair` — memory-only preservation by one push / a pair push.
* `granuleW_push_fresh`, `granuleW_pushOne_notTwo` — the side conditions from a fresh label or from
  a target that does not start a two-word unit.
* `granuleW_storeUnits` — a typed store at a component of a segment.
* `granuleW_sto` — growing the store typing by labels with no pair store.
* `granuleWP_*` (B′) — `GranuleWP` (own promises exempt): from `GranuleW`, the load lemma, a raw
  promise, a change of `P`, a fulfil at a word starting no two-word unit.
-/

namespace TermGranW
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts
open WeakMem (Msg Memory Address Ts Arch AllocLabel)

theorem granuleW_init (sto : Sto) : GranuleW sto #[] [] :=
  ⟨fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, fun _ _ _ _ h => by simp at h⟩

/-- (v3c, clause 4 at one message) A message `m` at the second word of a two-word unit of a cell of
`sto` holds no pointer. -/
def SndNL (sto : Sto) (m : Msg) : Prop :=
  ∀ (cl : Cell) (o : Nat), sto m.loc.label = some cl → m.loc.offset = o + 1 → TwoAtT cl.ty o →
    ∀ a g, m.val ≠ .loc a g

theorem next_inj {a b : Address} (h : a.next = b.next) : a = b := by
  cases a; cases b
  simp only [Address.next, Address.mk.injEq] at h ⊢
  exact ⟨h.1, Nat.add_right_cancel h.2⟩

theorem next_ne (a : Address) : a.next ≠ a := by
  intro h
  have := congrArg Address.offset h
  simp [Address.next] at this

theorem push_get (mem : Memory) (m : Msg) (i : Nat) :
    (mem.push m)[i]? = if i = mem.size then some m else mem[i]? := Array.getElem?_push

theorem push_get_lt {mem : Memory} {m : Msg} {i : Nat} (h : i < mem.size) : (mem.push m)[i]? = mem[i]? := by
  rw [push_get]; simp [Nat.ne_of_lt h]

theorem push_get_eq (mem : Memory) (m : Msg) : (mem.push m)[mem.size]? = some m := by
  rw [push_get]; simp

/-- **The load lemma**: a two-word read at `a0` not straddling a pair, whose second word `q + 1` is
a pair store's second half, read the pair store's first half (`t0 = q`): the reader's first word is
the actual partner. -/
theorem granuleW_partner {sto : Sto} {mem : Memory} {pairs : List Ts} (hG : GranuleW sto mem pairs)
    {a0 : Address} {t0 q : Nat} {m0 m1 : Msg} (h0 : mem[t0]? = some m0) (hl0 : m0.loc = a0)
    (hq : q ∈ pairs) (h1 : mem[q + 1]? = some m1) (hl1 : m1.loc = a0.next)
    (hs : WeakMem.pairStraddles mem pairs a0 t0 (q + 1) = false) : t0 = q := by
  obtain ⟨g1, g2, -⟩ := hG
  obtain ⟨p0, p1, hp0, hp1, hpl⟩ := g1 q hq
  rw [h1] at hp1; cases hp1
  have hq0 : p0.loc = a0 := next_inj (hpl.symm.trans hl1)
  have e1 := (noStraddle_at hs hq hp0 hq0 h1 hl1).2 (Nat.le_refl _)
  rcases Nat.lt_or_ge q t0 with hlt | hge
  · exfalso
    have ht0 : t0 ∈ pairs := g2 q hq t0 p0 m0 hp0 h0 (hl0.trans hq0.symm) hlt
    obtain ⟨r0, r1, hr0, hr1, hrl⟩ := g1 t0 ht0
    rw [h0] at hr0; cases hr0
    have e2 := (noStraddle_at hs ht0 h0 hl0 hr1 (by rw [hrl, hl0])).1 (Nat.le_refl _)
    omega
  · omega

/-- A two-word unit start is not followed by another (used by `granuleW_pushPair`). -/
theorem TwoAtT_not_succ0 {T : Ty} {o : Nat} (h : TwoAtT T o) : ¬ TwoAtT T (o + 1) := by
  rintro ⟨b2, S2, us2, o2, hs2, hL2, ht2, he2⟩
  obtain ⟨b, S, us, o1, hs, hL, ht, rfl⟩ := h
  have hlt := TwoAt_lt ht
  have hlt2 := TwoAt_lt ht2
  obtain ⟨rfl, rfl⟩ := SegOf_unique2 hs hL (show o1 + 1 < nWords us by omega) hs2 hL2
    (show o2 < nWords us2 by omega) (by omega)
  rw [hL] at hL2; cases hL2
  have : o2 = o1 + 1 := by omega
  subst this
  exact TwoAt_not_TwoAt_succ ht ht2

/-- **One push** at a word where no pair store starts. -/
theorem granuleW_pushOne {sto : Sto} {mem : Memory} {pairs : List Ts} {m : Msg} (hG : GranuleW sto mem pairs)
    (hn : ∀ q ∈ pairs, ∀ m0, mem[q]? = some m0 → m0.loc ≠ m.loc) (h4 : SndNL sto m) :
    GranuleW sto (mem.push m) pairs := by
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have hold : ∀ q, q < mem.size → (mem.push m)[q]? = mem[q]? := fun q hq => by
    exact push_get_lt hq
  have hlt : ∀ q : Nat, q ∈ pairs → q + 1 < mem.size := fun q hq => by
    obtain ⟨_, _, _, h1, _⟩ := g1 q hq
    exact (Array.getElem?_eq_some_iff.1 h1).1
  refine ⟨fun q hq => ?_, fun q hq v m0 mv h0 hv hl hqv => ?_, fun q hq m0 cl h0 hc => ?_,
    fun v mv cl o hv hc ho hT => ?_⟩
  · obtain ⟨a0, a1, h0, h1, hl⟩ := g1 q hq
    have := hlt q hq
    exact ⟨a0, a1, by rw [hold q (by omega)]; exact h0, by rw [hold (q + 1) this]; exact h1, hl⟩
  · have hq1 := hlt q hq
    rw [hold q (by omega)] at h0
    by_cases hvs : v < mem.size
    · rw [hold v hvs] at hv
      exact g2 q hq v m0 mv h0 hv hl hqv
    · have hv' : v = mem.size := by
        have := (Array.getElem?_eq_some_iff.1 hv).1; simp at this; omega
      subst hv'
      rw [push_get_eq] at hv; cases hv
      exact absurd hl.symm (hn q hq m0 h0)
  · have hq1 := hlt q hq
    rw [hold q (by omega)] at h0
    exact g3 q hq m0 cl h0 hc
  · by_cases hvs : v < mem.size
    · rw [hold v hvs] at hv
      exact g4 v mv cl o hv hc ho hT
    · have hv' : v = mem.size := by
        have := (Array.getElem?_eq_some_iff.1 hv).1; simp at this; omega
      subst hv'
      rw [push_get_eq] at hv; cases hv
      exact .inl (h4 cl o hc ho hT)

/-- **A pair push** at `a`, `a.next`: `a.next` starts no pair store, and `a` starts a two-word unit
of its cell. -/
theorem granuleW_pushPair {sto : Sto} {mem : Memory} {pairs : List Ts} {m0 m1 : Msg}
    (hG : GranuleW sto mem pairs) (hl : m1.loc = m0.loc.next)
    (hn : ∀ q ∈ pairs, ∀ x, mem[q]? = some x → x.loc ≠ m1.loc)
    (hT : ∀ cl, sto m0.loc.label = some cl → TwoAtT cl.ty m0.loc.offset) :
    GranuleW sto ((mem.push m0).push m1) (pairs ++ [mem.size]) := by
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have hlt : ∀ q : Nat, q ∈ pairs → q + 1 < mem.size := fun q hq => by
    obtain ⟨_, _, _, h1, _⟩ := g1 q hq
    exact (Array.getElem?_eq_some_iff.1 h1).1
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
  refine ⟨fun q hq => ?_, fun q hq v x0 xv h0 hv hlq hqv => ?_, fun q hq x0 cl h0 hc => ?_,
    fun v xv cl o hv hc ho hT2 => ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨a0, a1, h0, h1, hl⟩ := g1 q hq
      have := hlt q hq
      exact ⟨a0, a1, by rw [hold q (by omega)]; exact h0, by rw [hold (q + 1) this]; exact h1, hl⟩
    · simp at hq; subst hq
      exact ⟨m0, m1, e0, e1, hl⟩
  · rcases List.mem_append.1 hq with hq | hq
    · have hq1 := hlt q hq
      rw [hold q (by omega)] at h0
      rcases hsz v xv hv with ⟨hvs, hv'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact List.mem_append_left _ (g2 q hq v x0 xv h0 hv' hlq hqv)
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
  · rcases hsz v xv hv with ⟨hvs, hv'⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases g4 v xv cl o hv' hc ho hT2 with h | ⟨q, hq, e⟩
      · exact .inl h
      · exact .inr ⟨q, List.mem_append_left _ hq, e⟩
    · exfalso
      have h2 := hT cl hc
      rw [ho] at h2
      exact TwoAtT_not_succ0 hT2 h2
    · exact .inr ⟨mem.size, List.mem_append_right _ (List.mem_singleton.2 rfl), rfl⟩

/-- A push at a label where no pair store is. -/
theorem granuleW_push_fresh {sto : Sto} {mem : Memory} {pairs : List Ts} {m : Msg} (hG : GranuleW sto mem pairs)
    (hf : ∀ q ∈ pairs, ∀ m0, mem[q]? = some m0 → m0.loc.label ≠ m.loc.label) (h4 : SndNL sto m) :
    GranuleW sto (mem.push m) pairs :=
  granuleW_pushOne hG (fun q hq m0 h0 e => hf q hq m0 h0 (by rw [e])) h4

/-- A push at a word of a cell of `sto` that neither starts nor ends a two-word unit. -/
theorem granuleW_pushOne_notTwo {sto : Sto} {mem : Memory} {pairs : List Ts} {m : Msg} {cl : Cell}
    (hG : GranuleW sto mem pairs) (hc : sto m.loc.label = some cl) (hn : ¬ TwoAtT cl.ty m.loc.offset)
    (hs : ∀ o, m.loc.offset = o + 1 → ¬ TwoAtT cl.ty o) :
    GranuleW sto (mem.push m) pairs :=
  granuleW_pushOne hG (fun q hq m0 h0 e => hn (by rw [← e]; exact hG.2.2.1 q hq m0 cl h0 (by rw [e]; exact hc)))
    fun cl2 o hc2 ho hT => by rw [hc] at hc2; cases hc2; exact absurd hT (hs o ho)

/-- Growing the store typing by labels where no pair store is. -/
theorem granuleW_sto {sto sto2 : Sto} {mem : Memory} {pairs : List Ts} (hG : GranuleW sto mem pairs)
    (h : ∀ l c, sto2 l = some c → sto l = some c ∨
      (∀ q ∈ pairs, ∀ m0, mem[q]? = some m0 → m0.loc.label ≠ l) ∧
      ∀ (v : Nat) (mv : Msg) (o : Nat), mem[v]? = some mv → mv.loc.label = l → mv.loc.offset = o + 1 →
        TwoAtT c.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1) :
    GranuleW sto2 mem pairs := by
  refine ⟨hG.1, hG.2.1, fun q hq m0 cl h0 hc => ?_, fun v mv cl o hv hc ho hT => ?_⟩
  · rcases h _ _ hc with h1 | h1
    · exact hG.2.2.1 q hq m0 cl h0 h1
    · exact absurd rfl (h1.1 q hq m0 h0)
  · rcases h _ _ hc with h1 | h1
    · exact hG.2.2.2 v mv cl o hv h1 ho hT
    · exact h1.2 v mv o hv rfl ho hT

/-! ## Typed stores -/

/-- A two-word unit start is not followed by another. -/
theorem TwoAtT_not_succ {T : Ty} {o : Nat} (h : TwoAtT T o) : ¬ TwoAtT T (o + 1) :=
  TwoAtT_not_succ0 h

/-- A one-word unit of a segment starts no two-word unit of the cell. -/
theorem OneAt_not_TwoAtT {T S : Ty} {b o : Nat} {L : List Acc} (hs : SegOf T b S) (hL : accs S = some L)
    (h : OneAt L o) : ¬ TwoAtT T (b + o) := by
  rintro ⟨b2, S2, us2, o2, hs2, hL2, ht2, he2⟩
  have hlt := OneAt_lt h
  have hlt2 := TwoAt_lt ht2
  obtain ⟨rfl, rfl⟩ := SegOf_unique2 hs hL (show o < nWords L by omega) hs2 hL2
    (show o2 < nWords us2 by omega) he2
  rw [hL] at hL2; cases hL2
  have : o2 = o := by omega
  subst this
  exact TwoAt_not_OneAt ht2 h

/-- A one-word unit of a segment is not the second word of a two-word unit of the cell. -/
theorem OneAt_not_snd {T S : Ty} {b o : Nat} {L : List Acc} (hs : SegOf T b S) (hL : accs S = some L)
    (h : OneAt L o) {o' : Nat} (he : b + o = o' + 1) : ¬ TwoAtT T o' := by
  rintro ⟨b2, S2, us2, o2, hs2, hL2, ht2, he2⟩
  have hlt := OneAt_lt h
  have hlt2 := TwoAt_lt ht2
  obtain ⟨rfl, rfl⟩ := SegOf_unique2 hs hL (show o < nWords L by omega) hs2 hL2
    (show o2 + 1 < nWords us2 by omega) (by omega)
  rw [hL] at hL2; cases hL2
  have : o = o2 + 1 := by omega
  subst this
  exact TwoAt_not_OneAt_succ ht2 h

/-- The second word of a two-word unit of a segment starts no two-word unit of the cell. -/
theorem TwoAt_succ_not_TwoAtT {T S : Ty} {b o : Nat} {L : List Acc} (hs : SegOf T b S) (hL : accs S = some L)
    (h : TwoAt L o) : ¬ TwoAtT T (b + o + 1) :=
  TwoAtT_not_succ ⟨b, S, L, o, hs, hL, h, rfl⟩

theorem offs_label (a : Address) (k : Nat) : (offs a k).label = a.label := rfl

theorem offs_offset (a : Address) (k : Nat) : (offs a k).offset = a.offset + k := rfl

/-- **A store by units** at a cell `cl` of `sto` whose one-word units start no two-word unit of the
cell and whose two-word units start two-word units of it. -/
theorem granuleW_storeUnits {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {sto : Sto} {cl : Cell} (hc : sto a.label = some cl) :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      (∀ j, OneAt us j → ¬ TwoAtT cl.ty (a.offset + i + j)) →
      (∀ j, OneAt us j → ∀ o, a.offset + i + j = o + 1 → ¬ TwoAtT cl.ty o) →
      (∀ j, TwoAt us j → TwoAtT cl.ty (a.offset + i + j)) →
      GranuleW sto s.mem s.pairs → GranuleW sto s'.mem s'.pairs
  | [], _, _, s, s', hs, _, _, _, hG => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact hG
  | .one :: us, w :: ws, i, s, s', hs, hOne, hOne2, hTwo, hG => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      refine granuleW_storeUnits hc us ws (i + 1) _ s' hs (fun j hj => ?_) (fun j hj o ho => ?_)
        (fun j hj => ?_) ?_
      · have := hOne (j + 1) (OneAt_cons .one hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 1) = x + (i + 1) + j)) a.offset] at this; exact this
      · exact hOne2 (j + 1) (OneAt_cons .one hj) o
          ((fun (x i j o : Nat) (h : x + (i + 1) + j = o + 1) => (by omega : x + i + (j + 1) = o + 1)) _ _ _ _ ho)
      · have := hTwo (j + 1) (TwoAt_cons .one hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 1) = x + (i + 1) + j)) a.offset] at this; exact this
      · obtain ⟨t, hcase, -⟩ := stepStore_cases hst
        rcases hcase with ⟨e, -, -⟩ | ⟨e, -⟩
        · show GranuleW sto mem' s.pairs
          rw [e]
          refine granuleW_pushOne_notTwo hG (cl := cl) (by simp only [offs_label]; exact hc) ?_ ?_
          · simp only [offs_offset]
            have := hOne 0 ⟨0, rfl, rfl⟩
            simpa using this
          · intro o ho
            simp only [offs_offset] at ho
            exact hOne2 0 ⟨0, rfl, rfl⟩ o (by omega)
        · show GranuleW sto mem' s.pairs
          rw [e]; exact hG
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, hOne, hOne2, hTwo, hG => by
      simp only [storeUnits] at hs
      obtain ⟨q1, q2, -, -, -⟩ := stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel
      refine granuleW_storeUnits hc us ws (i + 2) _ s' hs (fun j hj => ?_) (fun j hj o ho => ?_)
        (fun j hj => ?_) ?_
      · have := hOne (j + 2) (OneAt_cons .two hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 2) = x + (i + 2) + j)) a.offset] at this; exact this
      · exact hOne2 (j + 2) (OneAt_cons .two hj) o
          ((fun (x i j o : Nat) (h : x + (i + 2) + j = o + 1) => (by omega : x + i + (j + 2) = o + 1)) _ _ _ _ ho)
      · have := hTwo (j + 2) (TwoAt_cons .two hj)
        rw [(fun x : Nat => (by omega : x + i + (j + 2) = x + (i + 2) + j)) a.offset] at this; exact this
      · show GranuleW sto (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).1 (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
          (dataE 2 w1) [0] rel).2.1
        rw [q1, q2]
        have h2 : TwoAtT cl.ty (a.offset + i) := by
          have := hTwo 0 ⟨0, rfl, rfl⟩; simpa using this
        refine granuleW_pushPair hG rfl (fun q hq x hx e => ?_) (fun cl2 hc2 => ?_)
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

/-- **A typed store at a component of a segment** (`PubInv_storeAt`'s layout hypotheses): the store's
units are the segment's units `pre ++ us ++ post` at the component. -/
theorem granuleW_storeAt {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {sto : Sto} {c : Cell} {b oS : Nat} {S : Ty} {L pre us post : List Acc} {ws : List Word} {s s' : St}
    (hsto : sto a.label = some c) (hseg : SegOf c.ty b S) (hL : accs S = some L) (hbo : b + oS = a.offset)
    (hLe : L = pre ++ us ++ post) (hpre : nWords pre = oS) (hs : s' ∈ storeUnits k arch pw a rel us ws 0 s)
    (hG : GranuleW sto s.mem s.pairs) : GranuleW sto s'.mem s'.pairs := by
  refine granuleW_storeUnits hsto us ws 0 s s' hs (fun j hj => ?_) (fun j hj o ho => ?_) (fun j hj => ?_) hG
  · have h1 : OneAt L (nWords pre + j) := by rw [hLe]; exact OneAt_embed hj
    have := OneAt_not_TwoAtT hseg hL h1
    rw [show b + (nWords pre + j) = a.offset + 0 + j by omega] at this; exact this
  · have h1 : OneAt L (nWords pre + j) := by rw [hLe]; exact OneAt_embed hj
    exact OneAt_not_snd (o' := o) hseg hL h1
      ((fun (b oS x n j o : Nat) (h1 : b + oS = x) (h2 : n = oS) (h3 : x + 0 + j = o + 1) =>
        (by omega : b + (n + j) = o + 1)) _ _ _ _ _ _ hbo hpre ho)
  · have h1 : TwoAt L (nWords pre + j) := by rw [hLe]; exact TwoAt_embed hj
    exact ⟨b, S, L, nWords pre + j, hseg, hL, h1, by omega⟩

theorem granuleWP_of {sto : Sto} {mem : Memory} {pairs : List Ts} (P : List Ts) (hG : GranuleW sto mem pairs) :
    GranuleWP sto mem pairs P :=
  ⟨hG.1, fun q hq v m0 mv h0 hv hl hqv _ => hG.2.1 q hq v m0 mv h0 hv hl hqv, hG.2.2.1,
    fun v mv cl o hv _ hc ho hT => hG.2.2.2 v mv cl o hv hc ho hT⟩

/-- **The load lemma** under `GranuleWP`: the first word read is not an own outstanding promise. -/
theorem granuleWP_partner {sto : Sto} {mem : Memory} {pairs P : List Ts} (hG : GranuleWP sto mem pairs P)
    {a0 : Address} {t0 q : Nat} {m0 m1 : Msg} (h0 : mem[t0]? = some m0) (hl0 : m0.loc = a0) (hP : t0 ∉ P)
    (hq : q ∈ pairs) (h1 : mem[q + 1]? = some m1) (hl1 : m1.loc = a0.next)
    (hs : WeakMem.pairStraddles mem pairs a0 t0 (q + 1) = false) : t0 = q := by
  obtain ⟨g1, g2, -⟩ := hG
  obtain ⟨p0, p1, hp0, hp1, hpl⟩ := g1 q hq
  rw [h1] at hp1; cases hp1
  have hq0 : p0.loc = a0 := next_inj (hpl.symm.trans hl1)
  have e1 := (noStraddle_at hs hq hp0 hq0 h1 hl1).2 (Nat.le_refl _)
  rcases Nat.lt_or_ge q t0 with hlt | hge
  · exfalso
    have ht0 : t0 ∈ pairs := g2 q hq t0 p0 m0 hp0 h0 (hl0.trans hq0.symm) hlt hP
    obtain ⟨r0, r1, hr0, hr1, hrl⟩ := g1 t0 ht0
    rw [h0] at hr0; cases hr0
    have e2 := (noStraddle_at hs ht0 h0 hl0 hr1 (by rw [hrl, hl0])).1 (Nat.le_refl _)
    omega
  · omega

/-- **Changing `P`**: a message leaving `P` is at no pair store's first word (for a later index). -/
theorem granuleWP_setP {sto : Sto} {mem : Memory} {pairs P P2 : List Ts} (hG : GranuleWP sto mem pairs P)
    (h : ∀ v ∈ P, v ∉ P2 → ∀ q ∈ pairs, ∀ m0 mv, mem[q]? = some m0 → mem[v]? = some mv → q < v →
      mv.loc ≠ m0.loc)
    (h4 : ∀ v ∈ P, v ∉ P2 → ∀ (mv : Msg) (cl : Cell) (o : Nat), mem[v]? = some mv → sto mv.loc.label = some cl →
      mv.loc.offset = o + 1 → TwoAtT cl.ty o → (∀ a g, mv.val ≠ .loc a g) ∨ ∃ q ∈ pairs, v = q + 1) :
    GranuleWP sto mem pairs P2 := by
  refine ⟨hG.1, fun q hq v m0 mv h0 hv hl hqv hP2 => ?_, hG.2.2.1, fun v mv cl o hv hP2 hc ho hT => ?_⟩
  · by_cases hP : v ∈ P
    · exact absurd hl (h v hP hP2 q hq m0 mv h0 hv hqv)
    · exact hG.2.1 q hq v m0 mv h0 hv hl hqv hP
  · by_cases hP : v ∈ P
    · exact h4 v hP hP2 mv cl o hv hc ho hT
    · exact hG.2.2.2 v mv cl o hv hP hc ho hT

/-- **A fulfil** of an own promise by a single store at a word starting no two-word unit. -/
theorem granuleWP_fulfil_notTwo {sto : Sto} {mem : Memory} {pairs P P2 : List Ts} {t : Nat} {m : Msg} {cl : Cell}
    (hG : GranuleWP sto mem pairs P) (hPt : ∀ v ∈ P, v ∉ P2 → v = t) (ht : mem[t]? = some m)
    (hc : sto m.loc.label = some cl) (hn : ¬ TwoAtT cl.ty m.loc.offset)
    (hs : ∀ o, m.loc.offset = o + 1 → ¬ TwoAtT cl.ty o) : GranuleWP sto mem pairs P2 :=
  granuleWP_setP hG (fun v hv hv2 q hq m0 mv h0 hmv _ e => by
    have := hPt v hv hv2; subst this
    rw [ht] at hmv; cases hmv
    exact hn (by rw [e]; exact hG.2.2.1 q hq m0 cl h0 (by rw [← e]; exact hc)))
    fun v hv hv2 mv cl2 o hmv hc2 ho hT => by
      have := hPt v hv hv2; subst this
      rw [ht] at hmv; cases hmv
      rw [hc] at hc2; cases hc2
      exact absurd hT (hs o ho)

/-- **A raw promise**: one push, recorded in `P`. -/
theorem granuleWP_promise {sto : Sto} {mem : Memory} {pairs P : List Ts} {m : Msg}
    (hG : GranuleWP sto mem pairs P) : GranuleWP sto (mem.push m) pairs (P ++ [mem.size]) := by
  obtain ⟨g1, g2, g3, g4⟩ := hG
  have hlt : ∀ q : Nat, q ∈ pairs → q + 1 < mem.size := fun q hq => by
    obtain ⟨_, _, _, h1, _⟩ := g1 q hq
    exact (Array.getElem?_eq_some_iff.1 h1).1
  refine ⟨fun q hq => ?_, fun q hq v m0 mv h0 hv hl hqv hP => ?_, fun q hq m0 cl h0 hc => ?_,
    fun v mv cl o hv hP hc ho hT => ?_⟩
  · obtain ⟨a0, a1, h0, h1, hl⟩ := g1 q hq
    have := hlt q hq
    exact ⟨a0, a1, by rw [push_get_lt (by omega)]; exact h0, by rw [push_get_lt this]; exact h1, hl⟩
  · have hq1 := hlt q hq
    rw [push_get_lt (by omega)] at h0
    by_cases hvs : v < mem.size
    · rw [push_get_lt hvs] at hv
      exact g2 q hq v m0 mv h0 hv hl hqv (fun h => hP (List.mem_append_left _ h))
    · have hv' : v = mem.size := by
        have := (Array.getElem?_eq_some_iff.1 hv).1; simp at this; omega
      exact absurd (List.mem_append_right _ (List.mem_singleton.2 hv')) hP
  · have hq1 := hlt q hq
    rw [push_get_lt (by omega)] at h0
    exact g3 q hq m0 cl h0 hc
  · by_cases hvs : v < mem.size
    · rw [push_get_lt hvs] at hv
      exact g4 v mv cl o hv (fun h => hP (List.mem_append_left _ h)) hc ho hT
    · have hv' : v = mem.size := by
        have := (Array.getElem?_eq_some_iff.1 hv).1; simp at this; omega
      exact absurd (List.mem_append_right _ (List.mem_singleton.2 hv')) hP


end TermGranW

#print axioms TermGranW.granuleW_init
#print axioms TermGranW.granuleW_partner
#print axioms TermGranW.granuleW_pushOne
#print axioms TermGranW.granuleW_pushPair
#print axioms TermGranW.granuleW_push_fresh
#print axioms TermGranW.granuleW_pushOne_notTwo
#print axioms TermGranW.granuleW_sto
#print axioms TermGranW.TwoAtT_not_succ
#print axioms TermGranW.OneAt_not_TwoAtT
#print axioms TermGranW.OneAt_not_snd
#print axioms TermGranW.TwoAt_succ_not_TwoAtT
#print axioms TermGranW.granuleW_storeUnits
#print axioms TermGranW.granuleW_storeAt
#print axioms TermGranW.granuleWP_of
#print axioms TermGranW.granuleWP_partner
#print axioms TermGranW.granuleWP_setP
#print axioms TermGranW.granuleWP_fulfil_notTwo
#print axioms TermGranW.granuleWP_promise

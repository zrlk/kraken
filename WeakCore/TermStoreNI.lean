import WeakCore.TermDwf

/-!
# TermStoreNI: `storeNI` from a per-store hiding fact

`Obligations.storeNI` (T3c) says that at a plain store, no outstanding own
promise at a stored protocol-word unit `b` *initialises* it (`InitAt`: every
predecessor is the `.undef` placeholder).  The machine half is proved here:

* **the store's bound is below every own promise at `b`** (`storeNI_bound`):
  with `B := max (obLow vs) (max (coh b) (dep pw))` (`dep pw` is the pointer's
  read timestamp under `storeDepRts`, else its view), the store either
  fulfils such a promise `t` (`B ≤ storeOb < t`), or appends (then `coh' b`
  passes `t`, and the certificate at `c'` is broken), or fulfils another
  promise `t2` (`B < t2 ≤ coh' b < t` by the certificate);
* **a hidden placeholder is no predecessor** (`initAt_hid`): if every `.undef`
  message at `b` is followed at `b` by a message at or below `V`, and some
  message at `b` lies at or below `V`, no `t > V` initialises `b`.

The remaining fact, `SeenHid` (the hiding at the store's bound), is a named
per-store hypothesis of `storeNI_of`.  It has the shape of `PubDefP` /
`OwnHidP` (`HiddenP`) at the reference's frontier (`pubPtr_view`: `f ≤
pw.view`) and of `OwnOKSF` at `coh b`.
-/

namespace TermStoreNI
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep TermCut TermSys TermMain TermCert TermFul TermLiveProps
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The store's bound -/

/-- The part of a store's `storeOb` the pointer word contributes. -/
def dep (k : Promises.Knobs) (pw : Word) : Ts := if k.storeDepRts then pw.rts else pw.view

/-- A lower bound of every `storeOb` a store through `pw` computes at `b` from views `vs`. -/
def Bnd (k : Promises.Knobs) (arch : Arch) (pw : Word) (vs : VState) (b : Address) : Ts :=
  max (obLow k arch vs) (max (vs.coh b) (dep k pw))

theorem Bnd_le_storeOb (k : Promises.Knobs) (arch : Arch) (s : St) (pw w : Word) (b : Address) :
    Bnd k arch pw s.vs b ≤ Promises.storeOb k arch (mth s pw w w) b (dataE 1 w) [0] := by
  have h1 := obLow_le_storeOb k arch (mth s pw w w) b (dataE 1 w) [0]
  have h2 : (mth s pw w w).vs.coh b ≤ Promises.storeOb k arch (mth s pw w w) b (dataE 1 w) [0] :=
    coh_le_storeOb
  have e0 : (mth s pw w w).regs 0 = pw := by simp [mth, regsOf]
  have h3 : dep k pw ≤ Promises.storeOb k arch (mth s pw w w) b (dataE 1 w) [0] := by
    generalize dataE 1 w = e
    cases e <;>
    · unfold Promises.storeOb dep Promises.depRts Promises.depView
      simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil, e0]
      cases k.storeDepRts <;> cases (decide (arch = Arch.tso) && k.tsoStoreOrder) <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;> tomega
  exact Nat.max_le.2 ⟨h1, Nat.max_le.2 ⟨h2, h3⟩⟩

theorem Bnd_mono {k : Promises.Knobs} {arch : Arch} {pw : Word} {v w : VState} {b : Address}
    (h : VLe v w) (hc : w.coh b = v.coh b) : Bnd k arch pw v b ≤ Bnd k arch pw w b := by
  unfold Bnd; rw [hc]
  exact Nat.max_le.2 ⟨Nat.le_trans (obLow_mono h) (Nat.le_max_left _ _), Nat.le_max_right _ _⟩

/-! ## One-word and two-word store steps -/

/-- A one-word store moves `coh` at `a` only, keeps the monotone views, and
either appends (at the top, promises unchanged) or fulfils a promise `T`
above its `storeOb`. -/
theorem stepStore_info {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) :
    ∃ T, th'.vs.coh = (fun b => if b = a then T else th.vs.coh b) ∧ VLe th.vs th'.vs ∧
      ((T = mem.size ∧ th'.promises = th.promises) ∨
       (th'.promises = th.promises.erase T ∧ Promises.storeOb k arch th a e deps < T)) := by
  cases e <;>
  · simp only [Promises.stepStore, List.mem_append, List.mem_singleton, List.mem_filterMap] at h
    rcases h with h | ⟨tw, _, hf⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨mem.size, rfl, by vle, Or.inl ⟨rfl, rfl⟩⟩
    · cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm] at hf
          split at hf
          · rename_i hcond
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
            exact ⟨tw, rfl, by vle, Or.inr ⟨rfl, hcond.2⟩⟩
          · simp at hf

theorem stepStorePair_info (mem : Memory) (pairs : List Ts) (th : Promises.Thread) (a : Address)
    (e0 e1 : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    let th' := (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.2
    th'.promises = th.promises ∧ VLe th.vs th'.vs ∧ th'.vs.coh a = mem.size ∧
      th'.vs.coh a.next = mem.size + 1 ∧ ∀ b, b ≠ a → b ≠ a.next → th'.vs.coh b = th.vs.coh b := by
  obtain ⟨-, -, q3, q4, -⟩ := TermMem.stepStorePair_eq mem pairs th a e0 e1 deps rel
  obtain ⟨-, -, -, h4, h5⟩ := stepStorePair_shape mem pairs th a e0 e1 deps rel
  refine ⟨q4, ?_, h4, h5, fun b hb hb1 => ?_⟩
  · simp only [Promises.stepStorePair]; vle
  · rw [q3]; simp [hb, hb1]

/-! ## `storeUnits`: frame and bound -/

theorem offs_ne {a : Address} {i j : Nat} (h : i ≠ j) : offs a i ≠ offs a j := by
  intro e
  have : a.offset + i = a.offset + j := congrArg Address.offset e
  exact h (Nat.add_left_cancel this)

theorem offs_next (a : Address) (i : Nat) : (offs a i).next = offs a (i + 1) := by
  simp only [offs, Address.next]; congr 1

/-- Units outside the store's range keep their `coh`; the monotone views grow. -/
theorem storeUnits_frame {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      VLe s.vs s'.vs ∧ ∀ b, (∀ j, j < nWords us → b ≠ offs a (i + j)) → s'.vs.coh b = s.vs.coh b
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs
      exact ⟨VLe.rfl' _, fun _ _ => rfl⟩
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨T, hcoh, hv, -⟩ := stepStore_info hst
      obtain ⟨hv2, hc2⟩ := storeUnits_frame us ws (i + 1) _ s' hs
      refine ⟨hv.trans hv2, fun b hb => ?_⟩
      have hb0 : b ≠ offs a i := by
        have := hb 0 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega); simpa using this
      rw [hc2 b fun j hj => by
        have := hb (j + 1) (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this]
      show th.vs.coh b = s.vs.coh b
      rw [hcoh]; simp only [hb0, ↓reduceIte]; rfl
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨-, hv, -, -, hoth⟩ := stepStorePair_info s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      obtain ⟨hv2, hc2⟩ := storeUnits_frame us ws (i + 2) _ s' hs
      refine ⟨hv.trans hv2, fun b hb => ?_⟩
      have hb0 : b ≠ offs a i := by
        have := hb 0 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega); simpa using this
      have hb1 : b ≠ (offs a i).next := by
        rw [offs_next]; exact hb 1 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
      rw [hc2 b fun j hj => by
        have := hb (j + 2) (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega)
        rwa [show i + (j + 2) = i + 2 + j by omega] at this]
      exact hoth b hb0 hb1
  | .one :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, hs => by simp [storeUnits] at hs

/-- A promise at an address the store does not write survives it. -/
theorem storeUnits_keepAt {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {i : Nat} {s s' : St} (hs : s' ∈ storeUnits k arch pw a rel us ws i s)
    {t : Ts} {m : Msg} (ht : t ∈ s.promises) (hm : s.mem[t]? = some m)
    (hn : ∀ j, j < nWords us → m.loc ≠ offs a (i + j)) : t ∈ s'.promises := by
  refine Classical.byContradiction fun hx => ?_
  obtain ⟨-, -, rem⟩ := storeUnits_ful us ws i s s' hs
  obtain ⟨j, -, s0, m', hj, -, he, -, hm', hl, -⟩ := rem t ht hx
  rw [he t m hm] at hm'
  cases hm'
  exact hn j (OneAt_lt hj) hl

/-- A promise at an address other than a one-word store's survives it. -/
theorem stepStore_keepAt {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory}
    {th th' : Promises.Thread} {a : Address} {e : WeakMem.Expr} {deps : List WeakMem.Reg} {rel : Bool}
    (h : (mem', th') ∈ Promises.stepStore k arch mem th a e deps rel) {t : Ts} {m : Msg}
    (ht : t ∈ th.promises) (hm : mem[t]? = some m) (hn : m.loc ≠ a) : t ∈ th'.promises := by
  refine Classical.byContradiction fun hx => ?_
  obtain ⟨-, -, rem⟩ := stepStore_ful h
  obtain ⟨-, m', hm', hl, -⟩ := rem t ht hx
  rw [hm] at hm'
  cases hm'
  exact hn hl

/-- **The store's bound at a written unit `b` against an own promise `t` at
`b`**: the bound is below `t`, or `t` survives with `coh' b` above `t` or
above the bound. -/
theorem storeUnits_bound {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ (t j : Nat) (m : Msg), t ∈ s.promises → s.mem[t]? = some m → m.loc = offs a (i + j) →
        j < nWords us →
        Bnd k arch pw s.vs m.loc < t ∨
        (t ∈ s'.promises ∧ (t < s'.vs.coh m.loc ∨ Bnd k arch pw s.vs m.loc < s'.vs.coh m.loc))
  | [], _, _, _, _, _, _, _, _, _, _, _, hj => absurd hj (by simp [nWords])
  | .one :: us, w :: ws, i, s, s', hs, t, j, m, ht, hm, hl, hj => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      obtain ⟨T, hcoh, hv, hcase⟩ := stepStore_info hst
      obtain ⟨he1, -, -⟩ := stepStore_ful hst
      have hlt : t < s.mem.size := TermMem.lt_of_get hm
      cases j with
      | zero =>
          rw [Nat.add_zero] at hl
          rw [hl]
          have hob := Bnd_le_storeOb k arch s pw w (offs a i)
          have hfr := (storeUnits_frame us ws (i + 1) _ s' hs).2 (offs a i) fun j _ =>
            offs_ne (by omega)
          have hT : th.vs.coh (offs a i) = T := by rw [hcoh]; simp
          have hm1 : (mem' : Memory)[t]? = some m := he1 t m hm
          have hkeep : t ∈ th.promises → t ∈ s'.promises := fun htm =>
            storeUnits_keepAt hs htm hm1 fun j' _ => by rw [hl]; exact offs_ne (by omega)
          rcases hcase with ⟨rfl, hp⟩ | ⟨hp, hlt2⟩
          · refine Or.inr ⟨hkeep (by rw [hp]; exact ht), Or.inl ?_⟩
            rw [hfr]; show t < th.vs.coh (offs a i); rw [hT]; exact hlt
          · by_cases e : t = T
            · subst e; exact Or.inl (Nat.lt_of_le_of_lt hob hlt2)
            · refine Or.inr ⟨hkeep (by rw [hp]; exact (List.mem_erase_of_ne e).2 ht), Or.inr ?_⟩
              rw [hfr]; show _ < th.vs.coh (offs a i); rw [hT]; exact Nat.lt_of_le_of_lt hob hlt2
      | succ j =>
          have hj' : j < nWords us := by
            simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega
          have hne : m.loc ≠ offs a i := by rw [hl]; exact offs_ne (by omega)
          have hc : th.vs.coh m.loc = s.vs.coh m.loc := by rw [hcoh]; simp [hne, mth]
          have htm : t ∈ th.promises := stepStore_keepAt hst ht hm hne
          have hl' : m.loc = offs a (i + 1 + j) := by rw [hl]; congr 1; omega
          have ih := storeUnits_bound us ws (i + 1) _ s' hs t j m htm (he1 t m hm) hl' hj'
          have hB : Bnd k arch pw s.vs m.loc ≤ Bnd k arch pw th.vs m.loc := Bnd_mono hv hc
          rcases ih with h | ⟨h1, h2 | h2⟩
          · exact Or.inl (Nat.lt_of_le_of_lt hB h)
          · exact Or.inr ⟨h1, Or.inl h2⟩
          · exact Or.inr ⟨h1, Or.inr (Nat.lt_of_le_of_lt hB h2)⟩
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs, t, j, m, ht, hm, hl, hj => by
      simp only [storeUnits] at hs
      obtain ⟨hp, hv, hc0, hc1, hoth⟩ := stepStorePair_info s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      obtain ⟨q1, -⟩ := TermMem.stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      have hlt : t < s.mem.size := TermMem.lt_of_get hm
      have he1 : ∀ (t : Nat) (m : Msg), s.mem[t]? = some m →
          (Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1)
            [0] rel).1[t]? = some m := by
        obtain ⟨⟨m0, m1, hq, -, -⟩, -⟩ := (stepStorePair_shape s.mem s.pairs (mth s pw w0 w1) (offs a i)
          (dataE 1 w0) (dataE 2 w1) [0] rel).2
        intro t m h; rw [hq]; exact (MemExt.push _ _).trans (MemExt.push _ _) t m h
      have htm : t ∈ (mth s pw w0 w1).promises := ht
      rw [← hp] at htm
      by_cases hj2 : j < 2
      · -- one of the two words written here: `coh` passes `t`
        have hfr := (storeUnits_frame us ws (i + 2) _ s' hs).2 m.loc fun j' _ => by
          rw [hl]; exact offs_ne (by omega)
        refine Or.inr ⟨storeUnits_keepAt hs htm (he1 t m hm) fun j' _ => by rw [hl]; exact offs_ne (by omega),
          Or.inl ?_⟩
        rw [hfr]
        rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
        · rw [Nat.add_zero] at hl; rw [hl, hc0]; exact hlt
        · rw [hl, ← offs_next, hc1]; omega
      · have hj' : j - 2 < nWords us := by
          simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega
        have hne0 : m.loc ≠ offs a i := by rw [hl]; exact offs_ne (by omega)
        have hne1 : m.loc ≠ (offs a i).next := by rw [hl, offs_next]; exact offs_ne (by omega)
        have hc := hoth m.loc hne0 hne1
        have hl' : m.loc = offs a (i + 2 + (j - 2)) := by rw [hl]; congr 1; omega
        have ih := storeUnits_bound us ws (i + 2) _ s' hs t (j - 2) m htm (he1 t m hm) hl' hj'
        have hB : Bnd k arch pw s.vs m.loc ≤ Bnd k arch pw _ m.loc := Bnd_mono hv hc
        rcases ih with h | ⟨h1, h2 | h2⟩
        · exact Or.inl (Nat.lt_of_le_of_lt hB h)
        · exact Or.inr ⟨h1, Or.inl h2⟩
        · exact Or.inr ⟨h1, Or.inr (Nat.lt_of_le_of_lt hB h2)⟩
  | .one :: _, [], _, _, _, hs, _, _, _, _, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [], _, _, _, hs, _, _, _, _, _, _, _ => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, _, hs, _, _, _, _, _, _, _ => by simp [storeUnits] at hs

/-! ## Hidden placeholders are no predecessors -/

/-- (storeNI) Every `.undef` message at `b` is followed at `b` by a message at
or below `V`, and some message at `b` lies at or below `V`: a reader bounded
by `V` sees past the placeholders at `b`. -/
def HidBy (mem : Memory) (b : Address) (V : Nat) : Prop :=
  (∃ (h : Nat) (m : Msg), h ≤ V ∧ mem[h]? = some m ∧ m.loc = b) ∧
    ∀ (t0 : Nat) (m0 : Msg), mem[t0]? = some m0 → m0.loc = b → m0.val = .undef →
      ∃ (t' : Nat) (m' : Msg), t0 < t' ∧ t' ≤ V ∧ mem[t']? = some m' ∧ m'.loc = b

/-- The latest message at `b` below `h + 1 + n`, given one at `h`. -/
theorem latest_below {mem : Memory} {b : Address} {h : Nat} {m0 : Msg} (h0 : mem[h]? = some m0)
    (hl : m0.loc = b) : ∀ n : Nat, ∃ (t0 : Nat) (m : Msg), h ≤ t0 ∧ t0 < h + 1 + n ∧ mem[t0]? = some m ∧
      m.loc = b ∧ ∀ (t' : Nat) (m' : Msg), t0 < t' → t' < h + 1 + n → mem[t']? = some m' → m'.loc ≠ b
  | 0 => ⟨h, m0, Nat.le_refl _, by omega, h0, hl, fun t' _ h1 h2 _ => absurd h2 (by omega)⟩
  | n + 1 => by
      by_cases hx : ∃ m, mem[h + 1 + n]? = some m ∧ m.loc = b
      · obtain ⟨m, hm, hml⟩ := hx
        exact ⟨h + 1 + n, m, by omega, by omega, hm, hml, fun t' _ h1 h2 _ => absurd h2 (by omega)⟩
      · obtain ⟨t0, m, h1, h2, h3, h4, h5⟩ := latest_below h0 hl n
        refine ⟨t0, m, h1, by omega, h3, h4, fun t' m' a1 a2 a3 => ?_⟩
        by_cases e : t' = h + 1 + n
        · subst e; exact fun hb => hx ⟨m', a3, hb⟩
        · exact h5 t' m' a1 (by omega) a3

/-- **A unit hidden at `V` is initialised by no timestamp above `V`.** -/
theorem initAt_hid {mem : Memory} {b : Address} {V t : Nat} (hh : HidBy mem b V) (hv : V < t)
    (hi : InitAt mem b t) : False := by
  obtain ⟨⟨h, m0, hle, h0, hl⟩, hund⟩ := hh
  obtain ⟨t0, m, -, h2, h3, h4, h5⟩ := latest_below h0 hl (t - h - 1)
  have ht : h + 1 + (t - h - 1) = t := by omega
  rw [ht] at h2 h5
  have hu : m.val = .undef := hi (mw m) ⟨t0, m, h2, h3, h4, rfl, h5⟩
  obtain ⟨t', m', a1, a2, a3, a4⟩ := hund t0 m h3 h4 hu
  exact h5 t' m' a1 (by omega) a3 a4

/-! ## `storeNI` -/

/-- (storeNI, the named per-store fact) At a plain store, every protocol-word
unit it writes, and (H) every designated start of a predicted unit
(`PredU ∧ DStart`, `NoInitF`'s other disjunct), is hidden (`HidBy`) at the
store's bound `Bnd`: the bound
reaches past the unit's allocation placeholders.  The shape of `PubDefP` /
`OwnHidP` at the reference's frontier and of `OwnOKSF` at `coh`. -/
def SeenHid (k : Promises.Knobs) (arch : Arch) (E : TEnv) (mem : Memory) (th : TTh) : Prop :=
  ∀ x rel a v tok e, th.term = .let_ x (.store rel a v tok) e →
    ∀ rt pw ad μ ru us j, evalAt th.env a = some (rt, [pw]) → addrOf pw = some ad →
      cellOf rt = some (μ, ru) → accs ru = some us → j < nWords us →
        ((∃ n P, WordAt E (offs ad j) n P) ∨ (PredU E (offs ad j) ∧ DStart E (offs ad j))) →
        HidBy mem (offs ad j) (Bnd k arch pw th.vs (offs ad j))

/-- **The store's bound is below every own promise at a stored unit**, by the
certificate after the step. -/
theorem storeNI_bound {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    {x : String} {rel : Bool} {a v : At} {tok : Option At} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e)
    {rt : Ty} {pw : Word} {ad : Address} {μ : Mode} {ru : Ty} {us : List Acc} {j : Nat}
    (hev : evalAt th.env a = some (rt, [pw])) (had : addrOf pw = some ad) (hc : cellOf rt = some (μ, ru))
    (hus : accs ru = some us) (hj : j < nWords us)
    {t : Ts} {m : Msg} (ht : t ∈ th.promises) (hm : c.mem[t]? = some m) (hloc : m.loc = offs ad j) :
    Bnd k arch pw th.vs m.loc < t := by
  have hr := X.hr
  simp only [tstep, hterm, evalOp] at hr
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hin, hr⟩ := hr
  split at hin
  · rename_i rt1 pw1 tv ws hea _
    rw [hev] at hea
    simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hea
    obtain ⟨rfl, rfl⟩ := hea
    split at hin
    · rename_i μ1 u b hc1 hb
      rw [hc] at hc1; rw [had] at hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hc1 hb
      obtain ⟨rfl, rfl⟩ := hc1
      subst hb
      split at hin
      · rename_i us1 hus1
        rw [hus] at hus1
        simp only [Option.some.injEq] at hus1
        subst hus1
        rw [List.mem_map] at hin
        obtain ⟨s'', hs'', he⟩ := hin
        injection he with e1 e2
        subst e1
        have hloc0 : m.loc = offs ad (0 + j) := by rw [Nat.zero_add]; exact hloc
        rcases storeUnits_bound us ws 0 (stOf c.mem c.pairs th) s'' hs'' t j m ht hm hloc0 hj with
          h | ⟨h1, h2⟩
        · exact h
        · obtain ⟨hme, -, -⟩ := storeUnits_ful us ws 0 _ s'' hs''
          have hth' : c'.ths[i]? = some (withS { th with term := e, env := (x, t', ws') :: th.env } s'') := by
            rw [X.e3, ← hr]
          have hm' : c'.mem[t]? = some m := by rw [X.e1, ← hr]; exact hme t m hm
          have hab := certified_promAbove X.cert hth' h1 hm'
          change s''.vs.coh m.loc < t at hab
          rcases h2 with h2 | h2
          · exact absurd (Nat.lt_trans h2 hab) (Nat.lt_irrefl _)
          · exact Nat.lt_trans h2 hab
      · simp at hin
    · simp at hin
  · simp at hin

/-- **`storeNI` from `SeenHid`** (one store context). -/
theorem storeNI_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {η : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (hseen : SeenHid k arch (CE η) c.mem th) :
    StoreNI (CE η) (stOf c.mem c.pairs th) th := by
  intro x rel a v tok e hterm rt pw ad μ ru us j hev had hc hus hj t m ht hm hloc hword hinit
  have hb := storeNI_bound X hterm hev had hc hus hj ht hm hloc
  rw [hloc] at hb
  exact initAt_hid (hseen x rel a v tok e hterm rt pw ad μ ru us j hev had hc hus hj hword) hb hinit

/-- **`Obligations.storeNI`, in the field's form**, from the per-store fact
`SeenHid` in the same form. -/
theorem storeNI_field {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg}
    (hseen : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      SeenHid k arch (CE η) c.mem th) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res},
      TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
      StoreNI (CE η) (stOf c.mem c.pairs th) th :=
  fun X Y => storeNI_of X (hseen X Y)

#print axioms Bnd_le_storeOb
#print axioms stepStore_info
#print axioms storeUnits_frame
#print axioms storeUnits_bound
#print axioms latest_below
#print axioms initAt_hid
#print axioms storeNI_bound
#print axioms storeNI_of
#print axioms storeNI_field

end TermStoreNI

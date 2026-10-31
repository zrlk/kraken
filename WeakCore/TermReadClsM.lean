import WeakCore.TermReadClsDefs
import WeakCore.TermUnitKeepC

/-! # TermReadClsM: where a thread step can raise coherence to an old non-promise message

`tstep_rd`: at a thread step, if the stepper's coherence at `b` rises to an old message
(`< mem.size`) that is none of its promises, then the step is a read of `b`: a load-family op
whose footprint holds `b` (`RdOp`), a `fetch`/`cas` at `b`, a `casp` at `b` or the word before, or
a boxed `inl`/`inr`/`case` reading its box (`b`'s label is the box's), or an allocation (`b`'s
label is the fresh one).  Stores and the `xchg` family end each written unit at a new message or
an own promise (`storeUnits_cohW`); fences and control steps keep coherence.
-/

namespace TermReadClsM

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## State primitives -/

theorem loadUnits_rise {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {us : List Acc} {k : Nat}
    {s : St} {r : St × List Word} (hr : r ∈ loadUnits arch pw a acq us k s) {b : Address}
    (h : s.vs.coh b < r.1.vs.coh b) : ∃ j, j < nWords us ∧ b = offs a (k + j) := by
  by_cases hx : ∃ j, j < nWords us ∧ b = offs a (k + j)
  · exact hx
  · have e := TermUnitKeepC.loadUnits_cohOff us k s r hr b (fun j hj e => hx ⟨j, hj, e⟩)
    rw [e] at h
    exact absurd h (Nat.lt_irrefl _)

theorem loadUnits_na {arch : Arch} {pw : Word} {a : Address} {acq : Bool} :
    ∀ (us : List Acc) (k : Nat) (s : St) (r : St × List Word), r ∈ loadUnits arch pw a acq us k s →
      r.1.nalloc = s.nalloc
  | [], _, s, r, hr => by
      simp only [loadUnits, List.mem_singleton] at hr; subst hr; rfl
  | .one :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_na us (k + 1) _ (s', ws) hmem; exact this
  | .two :: us, k, s, r, hr => by
      simp only [loadUnits, List.mem_flatMap, List.mem_map] at hr
      obtain ⟨th, -, ⟨s', ws⟩, hmem, rfl⟩ := hr
      have := loadUnits_na us (k + 2) _ (s', ws) hmem; exact this

/-- `storeUnits` leaves coherence alone off the words it writes (bounded form). -/
theorem storeUnits_cohOffB {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      ∀ b, (∀ j, j < nWords us → b ≠ offs a (i + j)) → s'.vs.coh b = s.vs.coh b
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; intros; rfl
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      intro b hb
      rw [storeUnits_cohOffB us ws (i + 1) _ s' hs b
        (fun j hj => by
          have := hb (1 + j) (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega)
          rw [show i + 1 + j = i + (1 + j) by omega]; exact this)]
      obtain ⟨t0, -, hc, -, -⟩ := stepStore_casesC hst
      show th.vs.coh b = s.vs.coh b
      rw [hc]
      have h0 : b ≠ offs a i := by
        have := hb 0 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
        simpa using this
      simp [h0, mth]
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨-, -, q3, -, -⟩ := TermMem.stepStorePair_eq s.mem s.pairs (mth s pw w0 w1) (offs a i)
        (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at q3 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q3
      intro b hb
      rw [storeUnits_cohOffB us ws (i + 2) _ s' hs b
        (fun j hj => by
          have := hb (2 + j) (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size] at hj ⊢; omega)
          rw [show i + 2 + j = i + (2 + j) by omega]; exact this)]
      show th.vs.coh b = s.vs.coh b
      have h0 : b ≠ offs a i := by
        have := hb 0 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
        simpa using this
      have h1 : b ≠ (offs a i).next := by
        have := hb 1 (by simp only [nWords, List.map_cons, List.sum_cons, Acc.size]; omega)
        have e : (offs a i).next = offs a (i + 1) := by
          simp only [offs, Address.next, Nat.add_assoc]
        rw [e]; exact this
      rw [q3]; simp [h0, h1, mth]
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

/-- A read-then-store (`LS`) raises no coherence to an old non-promise message. -/
theorem LS_noRise {s s' : St} (h : TermUnitKeepC.LS s s') (hlt : PromLt s) {b : Address}
    (h1 : s.vs.coh b < s'.vs.coh b) (h2 : s'.vs.coh b < s.mem.size) (h3 : s'.vs.coh b ∉ s.promises) :
    False := by
  obtain ⟨k, arch, pw, a, rel, us, ws, s1, e1, e2, hc1, hs⟩ := h
  have hlt1 : PromLt s1 := by
    intro t ht; rw [e1]; rw [e2] at ht; exact hlt t ht
  by_cases hb : ∃ j, j < nWords us ∧ b = offs a (0 + j)
  · obtain ⟨j, hj, rfl⟩ := hb
    rcases storeUnits_cohW us ws 0 s1 s' hs hlt1 j hj with hc | ⟨u, hu, m, -, -, hc⟩
    · rw [e1] at hc; exact absurd h2 (Nat.not_lt.2 hc)
    · rw [e2] at hu; rw [hc] at h3; exact h3 hu
  · have hoff : ∀ j, j < nWords us → b ≠ offs a (0 + j) := fun j hj e => hb ⟨j, hj, e⟩
    rw [storeUnits_cohOffB us ws 0 s1 s' hs b hoff, hc1 b hoff] at h1
    exact absurd h1 (Nat.lt_irrefl _)

theorem stepRmw_cohOff_at {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a cmp newv deps acq rel) :
    ∀ b, b ≠ a → th'.vs.coh b = th.vs.coh b := by
  intro b hb
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t, -, hbody⟩ := h
  split at hbody
  · rw [List.mem_singleton] at hbody
    cases hbody
    rw [TermLiveProps.ite_fence_coh]
    simp [hb]
  · rw [List.mem_append] at hbody
    rcases hbody with happ | hful
    · split at happ
      · rw [List.mem_singleton] at happ
        cases happ
        rw [TermLiveProps.ite_fence_coh]
        simp [hb]
      · simp at happ
    · obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
      split at hft
      · cases hft
      · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
        obtain ⟨-, hft⟩ := hft
        cases hft
        rw [TermLiveProps.ite_fence_coh]
        simp [hb]

theorem stepRmw_cohOff {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a cmp newv deps acq rel) :
    ∀ b, b ≠ a → th'.vs.coh b = th.vs.coh b := by
  intro b hb
  rw [stepRmw_cohOff_at (th := if arch = .tso then Promises.stepFence th .sy else th) h b hb, lockTh_coh]

theorem stepRmwPair_cohOff_at {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    ∀ b, b ≠ a → b ≠ a.next → th'.vs.coh b = th.vs.coh b := by
  intro b hb hb1
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, -, t1, -, hbody⟩ := h
  split at hbody
  · simp at hbody
  · split at hbody
    · rw [List.mem_singleton] at hbody
      cases hbody
      rw [TermLiveProps.ite_fence_coh]
      simp [hb, hb1]
    · rw [List.mem_append] at hbody
      rcases hbody with happ | hful
      · split at happ
        · rw [List.mem_singleton] at happ
          cases happ
          rw [TermLiveProps.ite_fence_coh]
          simp [hb, hb1]
        · simp at happ
      · obtain ⟨tw, _, hft⟩ := List.mem_filterMap.1 hful
        split at hft
        · simp only [Option.ite_none_right_eq_some, Option.some.injEq] at hft
          obtain ⟨-, hft⟩ := hft
          cases hft
          rw [TermLiveProps.ite_fence_coh]
          simp [hb, hb1]
        · cases hft

theorem stepRmwPair_cohOff {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) :
    ∀ b, b ≠ a → b ≠ a.next → th'.vs.coh b = th.vs.coh b := by
  intro b hb hb1
  rw [stepRmwPair_cohOff_at (th := if arch = .tso then Promises.stepFence th .sy else th) h b hb hb1, lockTh_coh]

theorem stepRmw_rise {k : Promises.Knobs} {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {cmp : WeakMem.RmwKind} {newv : WeakMem.Expr}
    {deps : List WeakMem.Reg} {acq rel : Bool} {mem' : Memory} {th' : Promises.Thread}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a cmp newv deps acq rel) {b : Address}
    (hc : th.vs.coh b < th'.vs.coh b) : b = a := by
  by_cases e : b = a
  · exact e
  · rw [stepRmw_cohOff h b e] at hc; exact absurd hc (Nat.lt_irrefl _)

theorem stepRmwPair_rise {arch : Arch} {mem : Memory} {pairs : List Ts} {th : Promises.Thread}
    {d0 d1 : WeakMem.Reg} {a : Address} {c0 c1 : WeakMem.Val} {n0 n1 : WeakMem.Expr} {deps : List WeakMem.Reg}
    {acq rel : Bool} {mem' : Memory} {pairs' : List Ts} {th' : Promises.Thread}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPair arch mem pairs th d0 d1 a c0 c1 n0 n1 deps acq rel) {b : Address}
    (hc : th.vs.coh b < th'.vs.coh b) : b = a ∨ b = a.next := by
  by_cases e : b = a
  · exact .inl e
  · by_cases e1 : b = a.next
    · exact .inr e1
    · rw [stepRmwPair_cohOff h b e e1] at hc; exact absurd hc (Nat.lt_irrefl _)

theorem fenceS_coh (s : St) (f : WeakMem.Fence) : (fenceS s f).vs.coh = s.vs.coh :=
  TermLiveProps.stepFence_coh _ f

theorem alloc_cohOff {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) :
    ∀ b : Address, b.label ≠ lbl → r.1.vs.coh b = s.vs.coh b := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  intro b hb
  rw [storeUnits_cohOff us ws 0 _ s' hs b (fun j e => hb (by rw [e]; rfl))]
  simp [hb]

theorem allocBuf_cohOff (lbl : AllocLabel) (n : Nat) (z : Option (List WeakMem.Val)) (s : St) :
    ∀ b : Address, b.label ≠ lbl → (allocBuf lbl n z s).1.vs.coh b = s.vs.coh b := by
  intro b hb
  unfold allocBuf
  simp [hb]

theorem injM_cohOff {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word}
    {r : St × List Word} (h : r ∈ injM g s ty j p) :
    ∀ b : Address, b.label ≠ freshLabel g.lbase g.n g.i s.nalloc → r.1.vs.coh b = s.vs.coh b := by
  intro b hb
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_cohOff hs b hb
      dsimp only
      split
      · rw [fenceS_coh]; exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    rfl

theorem projM_rise {g : G} {s : St} {ty : Ty} {ws : List Word} {r : St × Nat × List Word}
    (h : r ∈ projM g s ty ws) :
    r.1.mem = s.mem ∧ r.1.promises = s.promises ∧ r.1.nalloc = s.nalloc ∧
      ∀ b : Address, s.vs.coh b < r.1.vs.coh b →
        ∃ pw b0, ws = [pw] ∧ isBoxed ty = true ∧ addrOf pw = some b0 ∧ b.label = b0.label := by
  unfold projM at h
  split at h
  · rename_i hbx
    split at h
    · rename_i pw
      split at h
      · rename_i b0 hb0
        simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, h1, h⟩ := h
        obtain ⟨k1, -, k3⟩ := TermFul.loadUnits_keep _ _ _ _ h1
        have n1 := loadUnits_na _ _ _ _ h1
        have c1 := loadUnits_cohF _ _ _ _ h1
        repeat' split at h
        all_goals first
          | (simp at h; done)
          | (simp only [List.mem_map] at h
             obtain ⟨⟨s2, p⟩, h2, rfl⟩ := h
             obtain ⟨k1', -, k3'⟩ := TermFul.loadUnits_keep _ _ _ _ h2
             have n2 := loadUnits_na _ _ _ _ h2
             have c2 := loadUnits_cohF _ _ _ _ h2
             refine ⟨k1'.trans k1, k3'.trans k3, n2.trans n1, fun b hb => ?_⟩
             refine ⟨pw, b0, rfl, hbx, hb0, ?_⟩
             by_cases e : b.label = b0.label
             · exact e
             · exfalso
               rw [c2 b e, c1 b e] at hb
               exact absurd hb (Nat.lt_irrefl _))
      · cases h
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, fun b hb => absurd hb (Nat.lt_irrefl _)⟩

/-! ## The read classification of an op -/

/-- A boxed operand's box (`b`'s label is the box reference's), or the fresh label. -/
def BoxRd (g : G) (env : Env) (s : St) (a : At) (b : Address) : Prop :=
  (∃ t pw b0, evalAt env a = some (t, [pw]) ∧ isBoxed t = true ∧ addrOf pw = some b0 ∧ b.label = b0.label) ∨
    b.label = freshLabel g.lbase g.n g.i s.nalloc

/-- **What an op reads at `b`** (the ops whose coherence can rise to an old non-promise message). -/
def RdOp (g : G) (env : Env) (s : St) : Op → Address → Prop
  | .load _ a, b => ∃ t pw μ u b0 us j, evalAt env a = some (t, [pw]) ∧ cellOf t = some (μ, u) ∧
      addrOf pw = some b0 ∧ accs u = some us ∧ j < nWords us ∧ b = offs b0 (0 + j)
  | .ldp _ a _ _, b => ∃ t pw b0 j, evalAt env a = some (t, [pw]) ∧ pairRef t = true ∧
      addrOf pw = some b0 ∧ j < nWords [Acc.two] ∧ b = offs b0 (0 + j)
  | .loadAt bb i, b => ∃ t pw ti iws μ u jj a0 us j, evalAt env bb = some (t, [pw]) ∧
      evalAt env i = some (ti, iws) ∧ bufElem t = some (μ, u) ∧ numOf iws = some jj ∧ addrOf pw = some a0 ∧
      accs u = some us ∧ j < nWords us ∧ b = offs (offs a0 (jj * nWords us)) (0 + j)
  | .loadAtF bb i q, b => ∃ t pw ti iws μ u jj a0 us c o cs j, evalAt env bb = some (t, [pw]) ∧
      evalAt env i = some (ti, iws) ∧ bufElem t = some (μ, u) ∧ numOf iws = some jj ∧ addrOf pw = some a0 ∧
      accs u = some us ∧ compOff u q = some (c, o) ∧ accs c = some cs ∧ j < nWords cs ∧
      b = offs (offs a0 (jj * nWords us + o)) (0 + j)
  | .ldl bb i, b => ∃ t pw ti iws μ u jj a0 sg w j, evalAt env bb = some (t, [pw]) ∧
      evalAt env i = some (ti, iws) ∧ bufElem t = some (μ, u) ∧ numOf iws = some jj ∧ addrOf pw = some a0 ∧
      lanesOf u = some (sg, w) ∧ j < nWords [Acc.one] ∧ b = offs (offs a0 (jj / w.lanes)) (0 + j)
  | .ldlw bb wi jl, b => ∃ t pw t1 iws t2 jws μ u ii jj a0 sg w j, evalAt env bb = some (t, [pw]) ∧
      evalAt env wi = some (t1, iws) ∧ evalAt env jl = some (t2, jws) ∧ bufElem t = some (μ, u) ∧
      numOf iws = some ii ∧ numOf jws = some jj ∧ addrOf pw = some a0 ∧ lanesOf u = some (sg, w) ∧
      j < nWords [Acc.one] ∧ b = offs (offs a0 ii) (0 + j)
  | .fetch _ _ _ a v, b => ∃ t pw tv nw, evalAt env a = some (t, [pw]) ∧ evalAt env v = some (tv, [nw]) ∧
      addrOf pw = some b
  | .inl _ a, b => BoxRd g env s a b
  | .inr _ a, b => BoxRd g env s a b
  | .new _ _, b => b.label = freshLabel g.lbase g.n g.i s.nalloc
  | .newBuf _ _, b => b.label = freshLabel g.lbase g.n g.i s.nalloc
  | _, _ => False

theorem box_rd {g : G} {env : Env} {s s1 s2 : St} {a : At} {t S : Ty} {ws p q : List Word} {j j' : Nat}
    {b : Address} (hea : evalAt env a = some (t, ws)) (h1 : (s1, j, p) ∈ projM g s t ws)
    (h2 : (s2, q) ∈ injM g s1 S j' p) (hc : s.vs.coh b < s2.vs.coh b) : BoxRd g env s a b := by
  obtain ⟨-, -, n1, hr⟩ := projM_rise h1
  by_cases hf : b.label = freshLabel g.lbase g.n g.i s.nalloc
  · exact .inr hf
  · have e := injM_cohOff h2 b (by rw [n1]; exact hf)
    rw [e] at hc
    obtain ⟨pw, b0, rfl, hbx, hb0, hl⟩ := hr b hc
    exact .inl ⟨t, pw, b0, hea, hbx, hb0, hl⟩

/-- **The op-level classification.** -/
theorem evalOp_rd {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (h : r ∈ evalOp g env σs s op) (hlt : PromLt s) {b : Address}
    (h1 : s.vs.coh b < r.1.vs.coh b) (h2 : r.1.vs.coh b < s.mem.size) (h3 : r.1.vs.coh b ∉ s.promises) :
    RdOp g env s op b := by
  have nr : ∀ s' : St, s'.vs.coh = s.vs.coh → r.1 = s' → False := fun s' e he => by
    rw [he, e] at h1; exact Nat.lt_irrefl _ h1
  cases op
  case spawn => simp [evalOp] at h
  case inl τ a =>
    simp only [evalOp] at h
    split at h
    · rename_i t ws hea
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨s1, j, p⟩, hp, ⟨s2, q⟩, hq, rfl⟩ := h
      exact box_rd hea hp hq h1
    · simp at h
  case inr τ a =>
    simp only [evalOp] at h
    split at h
    · rename_i t ws hea
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨s1, j, p⟩, hp, ⟨s2, q⟩, hq, rfl⟩ := h
      exact box_rd hea hp hq h1
    · simp at h
  case new a _ =>
    simp only [evalOp] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [List.mem_map] at h
         obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
         show b.label = _
         by_cases hf : b.label = freshLabel g.lbase g.n g.i s.nalloc
         · exact hf
         · exfalso
           have e := alloc_cohOff hs b hf
           simp only at h1
           rw [e] at h1
           exact Nat.lt_irrefl _ h1)
  case fetch o acq rel a v =>
    simp only [evalOp] at h
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (simp only [List.mem_map] at h
         obtain ⟨⟨mem', th'⟩, hst, rfl⟩ := h
         have e := stepRmw_rise hst h1
         subst e; dsimp only [RdOp]; fillx)
  all_goals simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first
         | exact (nr _ rfl rfl).elim
         | exact (nr _ (fenceS_coh _ _) rfl).elim)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       show b.label = _
       by_cases hf : b.label = freshLabel g.lbase g.n g.i s.nalloc
       · exact hf
       · exfalso
         simp only at h1
         rw [allocBuf_cohOff _ _ _ s b hf] at h1
         exact Nat.lt_irrefl _ h1)
    | (simp only [List.mem_singleton] at h
       subst h
       first
         | exact (nr _ rfl rfl).elim
         | exact (nr _ (fenceS_coh _ _) rfl).elim)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact (LS_noRise (TermUnitKeepC.LS_store hx) hlt h1 h2 h3).elim
         | (obtain ⟨j, hj, hb⟩ := loadUnits_rise hx h1
            dsimp only [RdOp]; fillx))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact (LS_noRise (TermUnitKeepC.LS_rmw hx hy) hlt h1 h2 h3).elim)
    | (obtain ⟨⟨s1, old⟩, hx, h⟩ := List.mem_flatMap.1 h
       simp only at h
       split at h
       · obtain ⟨y, hy, he⟩ := List.mem_map.1 h
         cases he
         exact (LS_noRise (TermUnitKeepC.LS_rmw hx hy) hlt h1 h2 h3).elim
       · simp at h)
    | (obtain ⟨⟨s1, old⟩, hx, h⟩ := List.mem_filterMap.1 h
       simp only at h
       split at h
       · cases h
         obtain ⟨j, hj, hb⟩ := loadUnits_rise hx h1
         dsimp only [RdOp]; fillx
       · cases h)

#print axioms evalOp_rd

/-- **What a thread step reads at `b`.** -/
def TRd (g : G) (s : St) (th : TTh) (b : Address) : Prop :=
  (∃ x op e, th.term = .let_ x op e ∧ RdOp g th.env s op b) ∨
  (∃ a x e1 y e2, th.term = .case a x e1 y e2 ∧ BoxRd g th.env s a b) ∨
  (∃ acq rel w e v tn ok fail t pw, th.term = .cas acq rel w e v tn ok fail ∧
      evalAt th.env w = some (t, [pw]) ∧ addrOf pw = some b) ∨
  (∃ acq rel w e0 e1 v0 v1 tn ok fail t pw b0, th.term = .casp acq rel w e0 e1 v0 v1 tn ok fail ∧
      evalAt th.env w = some (t, [pw]) ∧ addrOf pw = some b0 ∧ (b = b0 ∨ b = b0.next))

/-- **The step-level classification**: a thread step raising the stepper's coherence at `b` to an
old message that is none of its promises reads `b` (`TRd`). -/
theorem tstep_rd {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (h : r ∈ tstep g mem pairs th) (hlt : PromLt (stOf mem pairs th)) {b : Address}
    (h1 : th.vs.coh b < r.2.2.vs.coh b) (h2 : r.2.2.vs.coh b < mem.size) (h3 : r.2.2.vs.coh b ∉ th.promises) :
    TRd g (stOf mem pairs th) th b := by
  have nr : r.2.2.vs.coh = th.vs.coh → False := fun e => by
    rw [e] at h1; exact Nat.lt_irrefl _ h1
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h
       first
         | exact (nr rfl).elim
         | exact (nr (fenceS_coh _ _)).elim)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       obtain ⟨e1, -⟩ := TermCert.enter_eq he
       exact (nr (by rw [← e1])).elim)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       obtain ⟨e1, -⟩ := TermCert.enter_eq he
       exact (nr (by show th'.vs.coh = th.vs.coh; rw [e1])).elim)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨s', t, ws⟩, hx, rfl⟩ := h
       first
         | exact .inl ⟨_, _, _, by assumption, evalOp_rd hx hlt h1 h2 h3⟩
         | (revert h1 h2 h3 nr
            split <;> intro h1 h2 h3 nr <;> exact .inl ⟨_, _, _, by assumption, evalOp_rd hx hlt h1 h2 h3⟩))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨⟨s1, j, p⟩, hp, ⟨s2, q⟩, hq, rfl⟩ := h
       exact .inr (.inl ⟨_, _, _, _, _, by assumption, box_rd (by assumption) hp hq h1⟩))
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hst, rfl⟩ := h
       have e := stepRmw_rise hst h1
       subst e
       exact .inr (.inr (.inl ⟨_, _, _, _, _, _, _, _, _, _, by assumption, by assumption, by assumption⟩)))
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', pairs', th'⟩, hst, rfl⟩ := h
       have e := stepRmwPair_rise hst h1
       exact .inr (.inr (.inr ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, by assumption, by assumption,
         by assumption, e⟩)))

#print axioms tstep_rd

end TermReadClsM

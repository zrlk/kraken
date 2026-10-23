import WeakCore.TermSpawnDefs

/-! # TermPairLayout: the pair layout in every reachable configuration

`Cfg.pairs` lists the memory indices at which a pair (two-word, 16-byte) write
starts.  This file proves, along every run of the machine (`TermRun.Step`, and
runs that also spawn threads), that each listed index `q` is laid out as one
pair write:

* `mem[q]` and `mem[q+1]` exist, at addresses `a` and `a.next`, with one shared
  message view (`PairInv`, first conjunct);
* no memory index belongs to two pairs (`PairInv`, second conjunct);
* no word of a pair is ever an outstanding promise (`PairInv`, third conjunct),
  so a pair's words are never supplied by a promise and its later fulfilment.

**One atomic write.**  A step never changes an existing message and only
appends to `pairs` (`PairStep`).  For each pair `q` a step adds, `q` and `q+1`
are the two consecutive messages appended by a single application of
`Promises.stepStorePair` or `Promises.stepRmwPair` (`PairApp`), the only two
rules that extend `pairs`.  So a pair location receives its two words only
from one atomic pair write.

Main results: `pairInv_runG` / `pairInv_runS` (the invariant along runs),
`pairStep_step` / `pairStep_runG` (the one-write clause), and the start
corollaries `pairInv_reach_init`, `pairInv_reach_initOK`, `pairInv_spawnS`,
`pairInv_reach_spawn`. -/

namespace TermPairLayout
open CoreLang CoreTerm TermRun TermCert TermFul TermSpawnStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The one-write witness -/

/-- **One pair write.**  Index `q` is where one application of
`Promises.stepStorePair` or `Promises.stepRmwPair`, to a memory `M` of size `q`,
registered a pair; `mem'` extends that application's memory (so `mem'[q]` and
`mem'[q+1]` are the two messages it appended). -/
def PairApp (q : Ts) (mem' : Memory) : Prop :=
  (∃ (M : Memory) (ps : List Ts) (th : Promises.Thread) (a : Address) (e0 e1 : WeakMem.Expr)
      (deps : List WeakMem.Reg) (rel : Bool),
      M.size = q ∧ (Promises.stepStorePair M ps th a e0 e1 deps rel).2.1 = ps ++ [q] ∧
      MemExt (Promises.stepStorePair M ps th a e0 e1 deps rel).1 mem') ∨
  (∃ (arch : Arch) (M : Memory) (ps : List Ts) (th : Promises.Thread) (d0 d1 : WeakMem.Reg)
      (a : Address) (cmp0 cmp1 : Val) (n0 n1 : WeakMem.Expr) (deps : List WeakMem.Reg)
      (acq rel : Bool) (x : Memory × List Ts × Promises.Thread),
      x ∈ Promises.stepRmwPair arch M ps th d0 d1 a cmp0 cmp1 n0 n1 deps acq rel ∧
      M.size = q ∧ x.2.1 = ps ++ [q] ∧ MemExt x.1 mem')

theorem PairApp.ext {q : Ts} {m m' : Memory} (h : PairApp q m) (he : MemExt m m') : PairApp q m' := by
  rcases h with ⟨M, ps, th, a, e0, e1, deps, rel, h1, h2, h3⟩ |
    ⟨arch, M, ps, th, d0, d1, a, c0, c1, n0, n1, deps, acq, rel, x, h0, h1, h2, h3⟩
  · exact Or.inl ⟨M, ps, th, a, e0, e1, deps, rel, h1, h2, h3.trans he⟩
  · exact Or.inr ⟨arch, M, ps, th, d0, d1, a, c0, c1, n0, n1, deps, acq, rel, x, h0, h1, h2, h3.trans he⟩

/-- The layout of one pair entry `q` in `mem`. -/
def Lay (mem : Memory) (q : Ts) : Prop :=
  ∃ m0 m1, mem[q]? = some m0 ∧ mem[q + 1]? = some m1 ∧ m1.loc = m0.loc.next ∧ m1.view = m0.view

theorem Lay.ext {mem mem' : Memory} {q : Ts} (h : Lay mem q) (he : MemExt mem mem') : Lay mem' q := by
  obtain ⟨m0, m1, h0, h1, h2, h3⟩ := h
  exact ⟨m0, m1, he _ _ h0, he _ _ h1, h2, h3⟩

theorem Lay.lt {mem : Memory} {q : Ts} (h : Lay mem q) : q + 1 < mem.size := by
  obtain ⟨-, m1, -, h1, -⟩ := h
  exact (Array.getElem?_eq_some_iff.1 h1).1

/-! ## Growth of `(mem, pairs)` by pair writes -/

/-- New pair entries `ns`, as written into `mem'` by a step from a memory `mem`. -/
def NewPairs (mem mem' : Memory) (ns : List Ts) : Prop :=
  (∀ q ∈ ns, mem.size ≤ q ∧ Lay mem' q ∧ PairApp q mem') ∧ ns.Pairwise (fun q q' => q + 2 ≤ q')

/-- `GrowM` with the new pair entries laid out and witnessed: memory only grows,
and `pairs` only gains entries `ns` at the end, each one pair write. -/
def PG (mem : Memory) (pairs : List Ts) (mem' : Memory) (pairs' : List Ts) : Prop :=
  MemExt mem mem' ∧ ∃ ns, pairs' = pairs ++ ns ∧ NewPairs mem mem' ns

abbrev PGs (s s' : St) : Prop := PG s.mem s.pairs s'.mem s'.pairs

theorem PG.refl (mem : Memory) (pairs : List Ts) : PG mem pairs mem pairs :=
  ⟨MemExt.rfl' _, [], by simp, by simp, List.Pairwise.nil⟩

theorem pg_mem {mem mem' : Memory} {pairs : List Ts} (h : MemExt mem mem') : PG mem pairs mem' pairs :=
  ⟨h, [], by simp, by simp, List.Pairwise.nil⟩

theorem pg_eq {mem mem' : Memory} {pairs pairs' : List Ts} (h1 : mem' = mem) (h2 : pairs' = pairs) :
    PG mem pairs mem' pairs' := by
  subst h1; subst h2; exact PG.refl _ _

theorem PG.trans {m1 m2 m3 : Memory} {p1 p2 p3 : List Ts} (h1 : PG m1 p1 m2 p2) (h2 : PG m2 p2 m3 p3) :
    PG m1 p1 m3 p3 := by
  obtain ⟨e1, ns1, rfl, n1, w1⟩ := h1
  obtain ⟨e2, ns2, rfl, n2, w2⟩ := h2
  have s1 := memExt_size e1
  refine ⟨e1.trans e2, ns1 ++ ns2, by simp, fun q hq => ?_, ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨a, b, c⟩ := n1 q hq
      exact ⟨a, b.ext e2, c.ext e2⟩
    · obtain ⟨a, b, c⟩ := n2 q hq
      exact ⟨Nat.le_trans s1 a, b, c⟩
  · refine List.pairwise_append.2 ⟨w1, w2, fun a ha b hb => ?_⟩
    have ha' := Lay.lt (n1 a ha).2.1
    have hb' := (n2 b hb).1
    show a + 2 ≤ b
    exact Nat.le_trans (Nat.succ_le_of_lt ha') hb'

/-- Appending one pair write. -/
theorem pg_app {mem mem' : Memory} {pairs : List Ts} (hL : Lay mem' mem.size) (hA : PairApp mem.size mem')
    (he : MemExt mem mem') : PG mem pairs mem' (pairs ++ [mem.size]) :=
  ⟨he, [mem.size], rfl, fun q hq => by
    rw [List.mem_singleton] at hq; subst hq; exact ⟨Nat.le_refl _, hL, hA⟩, List.pairwise_singleton _ _⟩

theorem lay_push2 (mem : Memory) (m0 m1 : Msg) (hl : m1.loc = m0.loc.next) (hv : m1.view = m0.view) :
    Lay ((mem.push m0).push m1) mem.size := by
  refine ⟨m0, m1, ?_, ?_, hl, hv⟩
  · simp [Array.getElem?_push]
  · simp only [Array.getElem?_push, Array.size_push, ↓reduceIte]

theorem memExt_push2 (mem : Memory) (m0 m1 : Msg) : MemExt mem ((mem.push m0).push m1) :=
  (MemExt.push _ _).trans (MemExt.push _ _)

/-! ## The two pair rules -/

theorem stepStorePair_pg (mem : Memory) (pairs : List Ts) (th : Promises.Thread) (a : Address)
    (e0 e1 : WeakMem.Expr) (deps : List WeakMem.Reg) (rel : Bool) :
    PG mem pairs (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1
      (Promises.stepStorePair mem pairs th a e0 e1 deps rel).2.1 := by
  have hA : PairApp mem.size (Promises.stepStorePair mem pairs th a e0 e1 deps rel).1 :=
    Or.inl ⟨mem, pairs, th, a, e0, e1, deps, rel, rfl, (TermMem.stepStorePair_eq mem pairs th a e0 e1 deps rel).2.1,
      MemExt.rfl' _⟩
  obtain ⟨q1, q2, -⟩ := TermMem.stepStorePair_eq mem pairs th a e0 e1 deps rel
  rw [q2]
  rw [q1] at hA ⊢
  exact pg_app (lay_push2 _ _ _ rfl rfl) hA (memExt_push2 _ _ _)

theorem stepRmwPairAt_lay {arch : Arch} {mem mem' : Memory} {pairs pairs' : List Ts}
    {th th' : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', pairs', th') ∈
      Promises.stepRmwPairAt arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    (mem' = mem ∧ pairs' = pairs) ∨
    ((∃ m0 m1, mem' = (mem.push m0).push m1 ∧ m1.loc = m0.loc.next ∧ m1.view = m0.view) ∧
      pairs' = pairs ++ [mem.size]) := by
  simp only [Promises.stepRmwPairAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨t0, _, t1, _, h⟩ := h
  split at h
  · simp at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  simp only [List.mem_append] at h
  rcases h with h | h
  · split at h
    · simp only [List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact Or.inr ⟨⟨_, _, rfl, rfl, rfl⟩, rfl⟩
    · cases h
  · simp only [List.mem_filterMap] at h
    obtain ⟨tw, _, hf⟩ := h
    split at hf
    · simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨-, rfl, rfl, rfl⟩ := hf
      exact Or.inl ⟨rfl, rfl⟩
    · cases hf

theorem stepRmwPair_pg {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    {x : Memory × List Ts × Promises.Thread}
    (h : x ∈ Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    PG mem pairs x.1 x.2.1 := by
  rcases stepRmwPairAt_lay (mem' := x.1) (pairs' := x.2.1) (th' := x.2.2)
      (th := if arch = .tso then Promises.stepFence th .sy else th) h with ⟨h1, h2⟩ |
    ⟨⟨m0, m1, h1, hl, hv⟩, h2⟩
  · exact pg_eq h1 h2
  · rw [h2]
    have hA : PairApp mem.size x.1 :=
      Or.inr ⟨arch, mem, pairs, th, dst0, dst1, a, cmp0, cmp1, new0, new1, deps, acq, rel, x, h, rfl, h2,
        MemExt.rfl' _⟩
    rw [h1] at hA ⊢
    exact pg_app (lay_push2 _ _ _ hl hv) hA (memExt_push2 _ _ _)

/-! ## Sub-steps of `tstep`

The proofs follow `TermFul.storeUnits_grow` … `TermFul.tstep_grow` case for case, with `PG`
for `GrowM` and the two pair rules' layouts (`stepStorePair_pg`, `stepRmwPair_pg`). -/

theorem storeUnits_pg {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      PGs s s'
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact PG.refl _ _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, hst, hs⟩ := hs
      exact (pg_mem (stepStore_ful hst).1).trans (storeUnits_pg us ws (i + 1) _ s' hs)
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      have hp := stepStorePair_pg s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at hp hs
      obtain ⟨mem', pairs', th⟩ := R
      exact PG.trans hp (storeUnits_pg us ws (i + 2) _ s' hs)
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem alloc_pg {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : PGs s r.1 := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  exact (pg_mem (memExt_fold _ _ _)).trans (storeUnits_pg _ _ _ _ s' hs)

theorem allocBuf_pg {lbl : AllocLabel} {n : Nat} {zero : Option (List Val)} {s : St} :
    PGs s (allocBuf lbl n zero s).1 := by
  unfold allocBuf
  exact pg_mem (memExt_fold _ _ _)

theorem injM_pg {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (h : r ∈ injM g s ty j p) : PGs s r.1 := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_pg hs
      dsimp only
      split
      · exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact PG.refl _ _

theorem pg_load {s s' : St} (h : s'.mem = s.mem ∧ s'.pairs = s.pairs ∧ s'.promises = s.promises) :
    PGs s s' := pg_eq h.1 h.2.1

theorem evalOp_pg {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : PGs s r.1 := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact PG.refl _ _ | exact allocBuf_pg)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact pg_load (loadUnits_keep _ _ _ _ hx)
         | exact storeUnits_pg _ _ _ _ _ hx
         | exact alloc_pg hx
         | exact pg_mem (stepRmw_memExt hx))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact (pg_load (projM_keep hx)).trans (injM_pg hy)
         | exact (pg_load (loadUnits_keep _ _ _ _ hx)).trans (storeUnits_pg _ _ _ _ _ hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact (pg_load (loadUnits_keep _ _ _ _ hx)).trans (storeUnits_pg _ _ _ _ _ hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact pg_load (loadUnits_keep _ _ _ _ hx))
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_pg)

theorem tstep_pg {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) : PG mem pairs r.1 r.2.1 := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact PG.refl _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact PG.refl _ _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact PG.refl _ _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_pg hx
         | exact pg_mem (stepRmw_memExt hx)
         | exact stepRmwPair_pg hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact (pg_load (projM_keep hx)).trans (injM_pg hy))

/-! ## The invariant and the step clause -/

/-- **Pair layout.**  (1) Every pair start `q` has messages at `q` and `q+1`, at
`a` and `a.next`, with one shared view.  (2) Pair entries are at least two
apart, so no index belongs to two pairs.  (3) Every outstanding promise is a
message and is neither word of any pair. -/
def PairInv (c : Cfg) : Prop :=
  (∀ q ∈ c.pairs, ∃ m0 m1, c.mem[q]? = some m0 ∧ c.mem[q + 1]? = some m1 ∧
      m1.loc = m0.loc.next ∧ m1.view = m0.view) ∧
  c.pairs.Pairwise (fun q q' => q + 2 ≤ q') ∧
  (∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ∀ t ∈ th.promises, t < c.mem.size ∧ ∀ q ∈ c.pairs, t ≠ q ∧ t ≠ q + 1)

/-- **One atomic write, per step.**  The step keeps every existing message,
only appends to `pairs`, and each appended pair `q` is two fresh messages
`q`, `q+1` of the step, at `a` and `a.next` with one view, appended by a single
application of `Promises.stepStorePair` or `Promises.stepRmwPair` (`PairApp`). -/
def PairStep (c c' : Cfg) : Prop :=
  (∀ (t : Nat) (m : Msg), c.mem[t]? = some m → c'.mem[t]? = some m) ∧
  ∃ ns, c'.pairs = c.pairs ++ ns ∧ ∀ q ∈ ns, c.mem.size ≤ q ∧
    (∃ m0 m1, c'.mem[q]? = some m0 ∧ c'.mem[q + 1]? = some m1 ∧ m1.loc = m0.loc.next ∧
      m1.view = m0.view) ∧ PairApp q c'.mem

theorem pairStep_of_pg {c c' : Cfg} (h : PG c.mem c.pairs c'.mem c'.pairs) : PairStep c c' := by
  obtain ⟨he, ns, hp, hn, -⟩ := h
  exact ⟨he, ns, hp, fun q hq => hn q hq⟩

theorem pairStep_refl (c : Cfg) : PairStep c c :=
  ⟨fun _ _ h => h, [], by simp, by simp⟩

/-- `PairStep` composes along a run. -/
theorem PairStep.trans {c1 c2 c3 : Cfg} (h1 : PairStep c1 c2) (h2 : PairStep c2 c3) : PairStep c1 c3 := by
  obtain ⟨e1, ns1, p1, n1⟩ := h1
  obtain ⟨e2, ns2, p2, n2⟩ := h2
  have s1 := memExt_size e1
  refine ⟨fun t m h => e2 t m (e1 t m h), ns1 ++ ns2, by rw [p2, p1, List.append_assoc], fun q hq => ?_⟩
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨a, ⟨m0, m1, h0, h1, hl, hv⟩, c⟩ := n1 q hq
    exact ⟨a, ⟨m0, m1, e2 _ _ h0, e2 _ _ h1, hl, hv⟩, c.ext e2⟩
  · obtain ⟨a, b, c⟩ := n2 q hq
    exact ⟨Nat.le_trans s1 a, b, c⟩

/-- The memory/pairs half of `PairInv` survives a `PG` step. -/
theorem lay_pg {mem mem' : Memory} {pairs pairs' : List Ts} (h : PG mem pairs mem' pairs')
    (h1 : ∀ q ∈ pairs, Lay mem q) (h2 : pairs.Pairwise (fun q q' => q + 2 ≤ q')) :
    (∀ q ∈ pairs', Lay mem' q) ∧ pairs'.Pairwise (fun q q' => q + 2 ≤ q') := by
  obtain ⟨he, ns, rfl, hn, hw⟩ := h
  refine ⟨fun q hq => ?_, List.pairwise_append.2 ⟨h2, hw, fun a ha b hb => ?_⟩⟩
  · rcases List.mem_append.1 hq with hq | hq
    · exact (h1 q hq).ext he
    · exact (hn q hq).2.1
  · have ha' := Lay.lt (h1 a ha)
    have hb' := (hn b hb).1
    show a + 2 ≤ b
    exact Nat.le_trans (Nat.succ_le_of_lt ha') hb'

theorem promise_pairInv {c : Cfg} {i : Nat} {a : Address} {v : Val} {w : Ts} (hi : i < c.ths.size)
    (h : PairInv c) : PairInv (promise c i a v w) ∧ PairStep c (promise c i a v w) := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨th, hth⟩ : ∃ th, c.ths[i]? = some th := ⟨c.ths[i], by simp [hi]⟩
  have e1 : (promise c i a v w).mem = c.mem.push ⟨a, v, w⟩ := by simp [promise, hth]
  have e2 : (promise c i a v w).pairs = c.pairs := by simp [promise, hth]
  have e3 : (promise c i a v w).ths = c.ths.set! i { th with promises := th.promises ++ [c.mem.size] } := by
    simp [promise, hth]
  have hext : MemExt c.mem (promise c i a v w).mem := by rw [e1]; exact MemExt.push _ _
  have hs := memExt_size hext
  have hsz : (promise c i a v w).mem.size = c.mem.size + 1 := by rw [e1]; simp
  refine ⟨⟨fun q hq => ?_, by rw [e2]; exact h2, fun j thj hj t ht => ?_⟩, ?_⟩
  · rw [e2] at hq; exact Lay.ext (h1 q hq) hext
  · rw [e2]
    by_cases hji : j = i
    · subst hji
      rw [e3, arr_set hth] at hj
      cases hj
      rcases List.mem_append.1 ht with ht | ht
      · obtain ⟨l, hq⟩ := h3 j th hth t ht
        exact ⟨Nat.lt_of_lt_of_le l hs, hq⟩
      · rw [List.mem_singleton] at ht; subst ht
        refine ⟨by rw [hsz]; exact Nat.lt_succ_self _, fun q hq => ?_⟩
        have hq1 := Lay.lt (h1 q hq)
        exact ⟨Nat.ne_of_gt (Nat.lt_of_succ_lt hq1), Nat.ne_of_gt hq1⟩
    · rw [e3, set_other hji] at hj
      obtain ⟨l, hq⟩ := h3 j thj hj t ht
      exact ⟨Nat.lt_of_lt_of_le l hs, hq⟩
  · exact pairStep_of_pg (by rw [e2]; exact pg_mem hext)

theorem threadSteps_pairInv {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hs : c' ∈ threadSteps p k arch c i) (h : PairInv c) : PairInv c' ∧ PairStep c c' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨th, r, hth, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  have hg : PG c.mem c.pairs c'.mem c'.pairs := by rw [e1, e2]; exact tstep_pg hr
  have hsz := memExt_size hg.1
  have hlt : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => (h3 i th hth t ht).1
  have hpp : ∀ t, t ∈ th.promises → t ∉ c.pairs := fun t ht hq => ((h3 i th hth t ht).2 t hq).1 rfl
  have hsub := (tstep_ful hlt hpp hr).1
  obtain ⟨l1, l2⟩ := lay_pg hg h1 h2
  obtain ⟨-, ns, hpe, hn, -⟩ := id hg
  -- an old promise stays off every pair: old pairs by `h3`, new ones lie above `c.mem.size`
  have keep : ∀ t, t < c.mem.size → (∀ q ∈ c.pairs, t ≠ q ∧ t ≠ q + 1) →
      t < c'.mem.size ∧ ∀ q ∈ c'.pairs, t ≠ q ∧ t ≠ q + 1 := by
    intro t ht hq
    refine ⟨Nat.lt_of_lt_of_le ht hsz, fun q hq' => ?_⟩
    rw [hpe] at hq'
    rcases List.mem_append.1 hq' with hq' | hq'
    · exact hq q hq'
    · have := (hn q hq').1; omega
  refine ⟨⟨l1, l2, fun j thj hj t ht => ?_⟩, pairStep_of_pg hg⟩
  by_cases hji : j = i
  · subst hji
    rw [e3] at hj; cases hj
    have ht0 : t ∈ th.promises := hsub.subset ht
    exact keep t (h3 j th hth t ht0).1 (h3 j th hth t ht0).2
  · have hj' : c.ths[j]? = some thj := by
      simp only [threadSteps, hth, List.mem_map] at hs
      obtain ⟨_, _, rfl⟩ := hs
      rwa [set_other hji] at hj
    exact keep t (h3 j thj hj' t ht).1 (h3 j thj hj' t ht).2

theorem spawn_ths {c : Cfg} {i : Nat} {th : TTh} {x : String} {e : Expr} {f : String} {ts : List Ty}
    {T : Ty} {ws : List Word} {j : Nat} {th' : TTh}
    (h : (spawnCfg c i th x e f ts T ws).ths[j]? = some th') :
    th' = spawnPar c i th x e ∨ th' = spawnKid c i th f ts T ws ∨ c.ths[j]? = some th' := by
  simp only [spawnCfg, spawnT, Array.getElem?_push] at h
  split at h
  · exact Or.inr (Or.inl (Option.some.inj h).symm)
  · by_cases hji : j = i
    · subst hji
      unfold Array.set! Array.setIfInBounds at h
      split at h
      · rw [Array.getElem?_set] at h
        simp at h
        first | exact Or.inl h.symm | exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rw [set_other hji] at h; exact Or.inr (Or.inr h)

theorem spawn_pairInv {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (hs : Spawn p k arch cap c c') (h : PairInv c) : PairInv c' ∧ PairStep c c' := by
  cases hs with
  | mk i x f a T ts e th rt ws hth _ hp _ _ =>
      obtain ⟨h1, h2, h3⟩ := h
      refine ⟨⟨h1, h2, fun j thj hj t ht => ?_⟩, pairStep_refl c⟩
      rcases spawn_ths hj with rfl | rfl | hj'
      · simp [spawnPar, withS, spawnS, fenceS, stOf, hp] at ht
      · simp [spawnKid] at ht
      · exact h3 j thj hj' t ht

/-! ## Runs -/

/-- **The step clause.**  Every machine or spawn step from a `PairInv`
configuration keeps `PairInv` and is a `PairStep`: existing messages are kept,
and each new pair is one atomic pair write of that step. -/
theorem pairStep_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : PairInv c) (hs : Step p k arch c c' ∨ Spawn p k arch cap c c') : PairInv c' ∧ PairStep c c' := by
  rcases hs with hs | hs
  · cases hs with
    | thread i hs _ => exact threadSteps_pairInv hs h
    | prom i a v w hi _ _ => exact promise_pairInv hi h
  · exact spawn_pairInv hs h

/-- `PairInv` along every run of machine and spawn steps. -/
theorem pairInv_runG {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (h0 : PairInv c0) (hr : StepsG p k arch (Spawn p k arch cap) c0 c) : PairInv c := by
  induction hr with
  | refl => exact h0
  | step hs _ ih => exact ih (pairStep_step h0 hs).1

/-- The one-write clause from the start of a run to any configuration on it. -/
theorem pairStep_runG {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (h0 : PairInv c0) (hr : StepsG p k arch (Spawn p k arch cap) c0 c) : PairStep c0 c := by
  induction hr with
  | refl => exact pairStep_refl _
  | step hs _ ih =>
      have := pairStep_step h0 hs
      exact this.2.trans (ih this.1)

theorem stepsG_of_steps {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop}
    {c0 c : Cfg} (hr : TermStep.Steps p k arch c0 c) : StepsG p k arch Sp c0 c := by
  induction hr with
  | refl => exact .refl _
  | step hs _ ih => exact .step (.inl hs) ih

/-- `PairInv` along every run of machine steps (`TermStep.Steps`). -/
theorem pairInv_runS {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c : Cfg}
    (h0 : PairInv c0) (hr : TermStep.Steps p k arch c0 c) : PairInv c :=
  pairInv_runG (cap := 0) h0 (stepsG_of_steps hr)

theorem pairStep_runS {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c : Cfg}
    (h0 : PairInv c0) (hr : TermStep.Steps p k arch c0 c) : PairStep c0 c :=
  pairStep_runG (cap := 0) h0 (stepsG_of_steps hr)

/-! ## Starts -/

theorem pairInv_nil {c : Cfg} (hp : c.pairs = []) (hn : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []) :
    PairInv c := by
  refine ⟨by simp [hp], by simp [hp], fun i th hth t ht => ?_⟩
  rw [hn i th hth] at ht; cases ht

/-- **Init start (`InitShape`).** -/
theorem pairInv_of_initShape {p : Prog} {c0 : Cfg} (hs : TermInit.InitShape p c0) : PairInv c0 :=
  pairInv_nil hs.pairs fun i th h => (hs.thr i th h).1

/-- **Runs from an `InitShape` start.** -/
theorem pairInv_reach_init {p : Prog} {k : Promises.Knobs} {arch : Arch} {c0 c : Cfg}
    (hs : TermInit.InitShape p c0) (hr : TermStep.Steps p k arch c0 c) : PairInv c ∧ PairStep c0 c :=
  ⟨pairInv_runS (pairInv_of_initShape hs) hr, pairStep_runS (pairInv_of_initShape hs) hr⟩

/-- **Init start (`InitOK`).**  `InitOK` fixes `c0.mem = #[]` and no promises,
and each thread's memory invariant puts every pair start below `c0.mem.size`,
so `c0.pairs = []`.  With no thread at all, `InitOK` says nothing about
`c0.pairs` (and no step can be taken), hence `hn`. -/
theorem pairInv_of_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {MintOK : TermSound.Res → Prop}
    {c0 : Cfg} (h0 : TermMain.InitOK p k arch Init MintOK c0) (hn : 0 < c0.ths.size) : PairInv c0 := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hmem, -⟩, hnp, -⟩ := id h0
  rcases TermMain.pwf0_of_initOK h0 with hz | hw
  · omega
  · refine pairInv_nil ?_ hnp
    cases hq : c0.pairs with
    | nil => rfl
    | cons q _ =>
        have := (hw 0).1 q (by rw [hq]; exact List.mem_cons_self ..)
        rw [hmem] at this; simp at this

/-- **Runs from an `InitOK` start** (with at least one thread, see `pairInv_of_initOK`). -/
theorem pairInv_reach_initOK {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res}
    {MintOK : TermSound.Res → Prop} {c0 c : Cfg} (h0 : TermMain.InitOK p k arch Init MintOK c0) (hn : 0 < c0.ths.size)
    (hr : StepsG p k arch (Spawn p k arch c0.cap) c0 c) : PairInv c ∧ PairStep c0 c :=
  ⟨pairInv_runG (pairInv_of_initOK h0 hn) hr, pairStep_runG (pairInv_of_initOK h0 hn) hr⟩

/-- **Spawn start.**  The barrier spawn (`TermSpawn.spawnS`) keeps memory and
`pairs` and starts every kid with no promises. -/
theorem pairInv_spawnS {cs : Cfg} {res : List Word} {kids : List TermSpawn.Kid} (h : PairInv cs) :
    PairInv (TermSpawn.spawnS cs res kids) := by
  unfold TermSpawn.spawnS
  split
  · exact h
  · obtain ⟨h1, h2, -⟩ := h
    refine ⟨h1, h2, fun i th hth t ht => ?_⟩
    simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hth
    obtain ⟨kd, -, rfl⟩ := hth
    simp [TermSpawn.kidTh] at ht

/-- **Runs from a spawn start** (`StartOKX` starts carry `PairInv` as a hypothesis;
`pairInv_spawnS` supplies it at the barrier spawn). -/
theorem pairInv_reach_spawn {p : Prog} {k : Promises.Knobs} {arch : Arch} {cs c : Cfg} {res : List Word}
    {kids : List TermSpawn.Kid} (h : PairInv cs)
    (hr : StepsG p k arch (Spawn p k arch (TermSpawn.spawnS cs res kids).cap) (TermSpawn.spawnS cs res kids) c) :
    PairInv c ∧ PairStep (TermSpawn.spawnS cs res kids) c :=
  ⟨pairInv_runG (pairInv_spawnS h) hr, pairStep_runG (pairInv_spawnS h) hr⟩

/-! ## The layout, as promised -/

/-- **Pair layout in every reachable configuration**: for each pair start `n`,
`mem[n].loc = a` and `mem[n+1].loc = a.next` for some address `a`. -/
theorem pair_layout {c : Cfg} (h : PairInv c) {n : Nat} (hn : n ∈ c.pairs) :
    ∃ (a : Address) (m0 m1 : Msg), c.mem[n]? = some m0 ∧ c.mem[n + 1]? = some m1 ∧
      m0.loc = a ∧ m1.loc = a.next := by
  obtain ⟨m0, m1, h0, h1, hl, -⟩ := h.1 n hn
  exact ⟨m0.loc, m0, m1, h0, h1, rfl, hl⟩

#print axioms pairInv_runG
#print axioms pairStep_runG
#print axioms pairInv_reach_init
#print axioms pairInv_reach_initOK
#print axioms pairInv_reach_spawn
#print axioms pair_layout
#print axioms pairStep_step
#print axioms pairInv_runS
#print axioms pairStep_runS
#print axioms pairInv_of_initOK
#print axioms pairInv_spawnS

end TermPairLayout

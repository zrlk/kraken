import WeakCore.TermPtrRts

/-!
# TermNoFul: K-3(i), a thread step of the owner does not fulfil `tmin`

A fulfil of `t` writes the fulfilled message's value from a data word `w`
(`storeUnits_ful`, `stepRmw_ful`), below the store's bound (`storeOb < t`).
Under `storeDepRts`, a pointer-valued data word is a register dependency of the
write, so `w.rts ≤ storeOb < t`.  The data word comes from an environment entry
(`WriteFrom`); that entry's runtime type is shallow-pub (staging `FulSNo`, to be discharged by
the PubOnly typing lemmas), so the word counts (`pubWords_of_sNo`) and (R) gives `t ≤ w.rts`: a
contradiction.
A fetch-op writes no pointer.
-/

namespace TermNoFul
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermCert TermFul TermPtrRts
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-! ## The data word's rts is below the write's bound -/

theorem storeOb_rts (k : Promises.Knobs) (arch : Arch) (s : St) (pw w : Word) (b : Address)
    (hk : k.storeDepRts = true) {a' : Address} {n : Nat} (hw : w.val = .loc a' n) :
    w.rts ≤ Promises.storeOb k arch (mth s pw w w) b (dataE 1 w) [0] := by
  have e1 : dataE 1 w = .reg 1 := by simp only [dataE, hw]
  have e0 : (mth s pw w w).regs 1 = w := by simp [mth, regsOf]
  rw [e1]
  unfold Promises.storeOb Promises.depRts
  simp only [List.cons_append, List.nil_append, List.foldl_cons, List.foldl_nil, e0, hk, ↓reduceIte]
  maxle

theorem rts_le_depRts (s : St) (pw w : Word) {a' : Address} {n : Nat} (hw : w.val = .loc a' n) :
    w.rts ≤ Promises.depRts (mth s pw w w).regs ((dataE 1 w).writeDeps [0]) := by
  have e1 : dataE 1 w = .reg 1 := by simp only [dataE, hw]
  have e0 : (mth s pw w w).regs 1 = w := by simp [mth, regsOf]
  rw [e1]
  simp only [WeakMem.Expr.writeDeps, Promises.depRts, List.cons_append, List.nil_append, List.foldl_cons,
    List.foldl_nil, e0]
  exact Nat.le_max_right _ _

/-- **`stepRmw`'s bound**: under `storeDepRts`, a fulfilled `t` is above the write's register
dependencies' read timestamps. -/
theorem stepRmw_ob_at {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmwAt k arch mem pairs th dst a kind newv deps acq rel)
    (hk : k.storeDepRts = true) :
    ∀ t, t ∈ th.promises → t ∉ th'.promises → Promises.depRts th.regs (newv.writeDeps deps) < t := by
  simp only [Promises.stepRmwAt, List.mem_flatMap, List.mem_filter, List.mem_range] at h
  obtain ⟨tr, -, h⟩ := h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro t ht hn; rw [lockFence_prom] at hn; exact absurd ht hn
  · simp only [List.mem_append] at h
    rcases h with h | h
    · split at h
      · simp only [List.mem_singleton, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        intro t ht hn; rw [lockFence_prom] at hn; exact absurd ht hn
      · cases h
    · simp only [List.mem_filterMap] at h
      obtain ⟨tw, _, hf⟩ := h
      cases hm : mem[tw]? with
      | none => simp [hm] at hf
      | some pm =>
          simp only [hm, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨hcond, rfl, rfl⟩ := hf
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          obtain ⟨⟨⟨⟨-, -⟩, -⟩, hlt⟩, -⟩ := hcond
          intro t ht hn
          rw [lockFence_prom] at hn
          have e := not_mem_erase ht hn
          subst e
          refine Nat.lt_of_le_of_lt ?_ hlt
          maxle

theorem stepRmw_ob {k : Promises.Knobs} {arch : Arch} {mem mem' : Memory} {pairs : List Ts}
    {th th' : Promises.Thread} {dst : WeakMem.Reg} {a : Address} {kind : WeakMem.RmwKind}
    {newv : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    (h : (mem', th') ∈ Promises.stepRmw k arch mem pairs th dst a kind newv deps acq rel)
    (hk : k.storeDepRts = true) :
    ∀ t, t ∈ th.promises → t ∉ th'.promises → Promises.depRts th.regs (newv.writeDeps deps) < t := by
  intro t ht hn
  have hx := stepRmw_ob_at (th := if arch = .tso then Promises.stepFence th .sy else th) h hk t (by rw [lockFence_prom]; exact ht) hn
  rwa [TermCert.lockF_regs] at hx

/-! ## Fulfils with the fulfilled index -/

/-- Promises shrink, and each removed promise `t` (message `m`) satisfies `W m.loc m.val t`. -/
def FulT (s s' : St) (W : Address → WeakMem.Val → Ts → Prop) : Prop :=
  s'.promises.Sublist s.promises ∧
    ∀ t, t ∈ s.promises → t ∉ s'.promises → ∃ m, s.mem[t]? = some m ∧ W m.loc m.val t

theorem fulT_of_keep {s s' : St} {W : Address → WeakMem.Val → Ts → Prop}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (h : KeepR s s') : FulT s s' W :=
  ⟨h.2.1, fun t ht hn => absurd (h.2.2 t ht (hlt t ht)) hn⟩

theorem fulT_mono {s s' : St} {W W2 : Address → WeakMem.Val → Ts → Prop} (h : FulT s s' W)
    (hW : ∀ l v t, W l v t → W2 l v t) : FulT s s' W2 :=
  ⟨h.1, fun t ht hn => let ⟨m, hm, hw⟩ := h.2 t ht hn; ⟨m, hm, hW _ _ _ hw⟩⟩

/-- The single-word write of an operation, with its data word's rts bound; or a fetch-op's. -/
def OpWT (g : G) (env : Env) (s : St) (op : Op) (loc : Address) (val : WeakMem.Val) (t : Ts) : Prop :=
  (∃ pw b rel us ws j w, UnitsOp g env s op pw b rel us ws ∧ OneAt us j ∧ ws[j]? = some w ∧
    loc = offs b j ∧ val = w.val ∧ (g.k.storeDepRts = true → ∀ a' n, w.val = .loc a' n → w.rts < t)) ∨
  (∃ o acq rel a v, op = .fetch o acq rel a v ∧ ∃ mr nw : WeakMem.Val, val = o.kind.apply mr nw)

theorem units_fulT {g : G} {env : Env} {op : Op} {pw : Word}
    {b : Address} {rel : Bool} {us : List Acc} {ws : List Word} {s s1 s' : St}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (hm1 : s1.mem = s.mem) (hp1 : s1.promises = s.promises)
    (hs : s' ∈ storeUnits g.k g.arch pw b rel us ws 0 s1) (hU : UnitsOp g env s op pw b rel us ws) :
    FulT s s' (OpWT g env s op) := by
  obtain ⟨-, sub, rem⟩ := storeUnits_ful _ _ _ _ _ hs
  refine ⟨hp1 ▸ sub, fun t ht hn => ?_⟩
  obtain ⟨j, w, s0, m, hj, hw, he, -, hm0, hl, hv, -, hob⟩ := rem t (hp1 ▸ ht) hn
  refine ⟨m, memExt_back (hm1 ▸ he) (hlt t ht) hm0, Or.inl ⟨pw, b, rel, us, ws, j, w, hU, hj, hw,
    by rw [hl, Nat.zero_add], hv, fun hk a' n hwv => ?_⟩⟩
  exact Nat.lt_of_le_of_lt (storeOb_rts g.k g.arch s0 pw w _ hk hwv) hob

theorem evalOp_store_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {rel : Bool} {a v : At}
    {o : Option At} {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.store rel a v o)) : FulT s r.1 (OpWT g env s (.store rel a v o)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_fulT hlt rfl rfl hs (by dsimp only [UnitsOp]; fillx))

theorem evalOp_xchg_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {a v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchg a v)) : FulT s r.1 (OpWT g env s (.xchg a v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_fulT hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx))

theorem evalOp_xchgAt_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchgAt bb i v)) : FulT s r.1 (OpWT g env s (.xchgAt bb i v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_fulT hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx))

theorem evalOp_xchgAtF_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {bb i : At} {p : List Nat}
    {v : At} {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.xchgAtF bb i p v)) :
    FulT s r.1 (OpWT g env s (.xchgAtF bb i p v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
       exact units_fulT hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx))

theorem evalOp_bufInit_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {bb i x : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.bufInit bb i x)) : FulT s r.1 (OpWT g env s (.bufInit bb i x)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨s', hs, rfl⟩ := h
       exact units_fulT hlt rfl rfl hs (by dsimp only [UnitsOp]; fillx))

theorem evalOp_stl_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {bb i v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.stl bb i v)) : FulT s r.1 (OpWT g env s (.stl bb i v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact units_fulT hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx)
       · simp at h)

theorem evalOp_stlw_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {bb wi jl v : At}
    {r : St × Ty × List Word} (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (h : r ∈ evalOp g env σs s (.stlw bb wi jl v)) : FulT s r.1 (OpWT g env s (.stlw bb wi jl v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         obtain ⟨k1, -, k3⟩ := loadUnits_keep _ _ _ _ hx
         exact units_fulT hlt k1 k3 hy (by dsimp only [UnitsOp]; fillx)
       · simp at h)

theorem evalOp_fetch_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {o : FetchOp} {acq rel : Bool}
    {a v : At} {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s (.fetch o acq rel a v)) :
    FulT s r.1 (OpWT g env s (.fetch o acq rel a v)) := by
  simp only [evalOp] at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_map] at h
       obtain ⟨⟨mem', th'⟩, hx, rfl⟩ := h
       obtain ⟨-, sub, rem⟩ := stepRmw_ful hx
       refine ⟨sub, fun t ht hn => ?_⟩
       obtain ⟨-, m, tr, mr, hm, -, -, -, hv, -⟩ := rem t ht hn
       exact ⟨m, hm, Or.inr ⟨o, acq, rel, a, v, rfl, _, _, hv⟩⟩)

/-- **An operation's fulfils**, with the data word's rts bound. -/
theorem evalOp_fulT {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op} {r : St × Ty × List Word}
    (hlt : ∀ t, t ∈ s.promises → t < s.mem.size) (h : r ∈ evalOp g env σs s op) :
    FulT s r.1 (OpWT g env s op) := by
  cases op
  case spawn => simp [evalOp] at h
  case store => exact evalOp_store_fulT hlt h
  case xchg => exact evalOp_xchg_fulT hlt h
  case xchgAt => exact evalOp_xchgAt_fulT hlt h
  case xchgAtF => exact evalOp_xchgAtF_fulT hlt h
  case bufInit => exact evalOp_bufInit_fulT hlt h
  case stl => exact evalOp_stl_fulT hlt h
  case stlw => exact evalOp_stlw_fulT hlt h
  case fetch => exact evalOp_fetch_fulT h
  all_goals
    obtain ⟨sub, rem⟩ := evalOp_ful hlt h
    refine ⟨sub, fun t ht hn => ?_⟩
    obtain ⟨m, -, hw⟩ := rem t ht hn
    exfalso
    rcases hw with ⟨_, _, _, _, _, _, _, hU, -⟩ | ⟨_, _, _, _, _, _, _, _, _, _, _, he, -⟩
    · simp only [UnitsOp] at hU
    · cases he

/-- The single-word writes of a thread step, with the fulfilled index: an operation's
(`OpWT`), or a `cas`'s, whose data word `nw` has rts below `t` under `storeDepRts`. -/
def SWT (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (loc : Address) (val : WeakMem.Val) (t : Ts) : Prop :=
  (∃ x op e, th.term = .let_ x op e ∧ OpWT g th.env (stOf mem pairs th) op loc val t) ∨
  (∃ acq rel w e v tn ok fail t1 t2 t3 pw ew nw, th.term = .cas acq rel w e v tn ok fail ∧
    evalAt th.env w = some (t1, [pw]) ∧ evalAt th.env e = some (t2, [ew]) ∧
    evalAt th.env v = some (t3, [nw]) ∧ addrOf pw = some loc ∧ val = nw.val ∧
    (g.k.storeDepRts = true → ∀ a' n, nw.val = .loc a' n → nw.rts < t))

theorem cas_fulT {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {acq rel : Bool} {w e v : At}
    {tn : String} {ok fail : Expr} {t1 t2 t3 : Ty} {pw ew nw : Word} {b : Address}
    {x : Memory × Promises.Thread}
    (hterm : th.term = .cas acq rel w e v tn ok fail) (h1 : evalAt th.env w = some (t1, [pw]))
    (h2 : evalAt th.env e = some (t2, [ew])) (h3 : evalAt th.env v = some (t3, [nw]))
    (hb : addrOf pw = some b)
    (hx : x ∈ Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 b
      (.cas ew.val) (dataE 1 nw) [0] acq rel) (s2 : St) (hs : s2.promises = x.2.promises) :
    FulT (stOf mem pairs th) s2 (SWT g mem pairs th) := by
  obtain ⟨-, sub, rem⟩ := stepRmw_ful (mem' := x.1) (th' := x.2) hx
  refine ⟨by rw [hs]; exact sub, fun t ht hn => ?_⟩
  rw [hs] at hn
  obtain ⟨-, m, tr, mr, hm, -, -, hl, hv, -⟩ := rem t ht hn
  rw [rmwNewVal_dataE] at hv
  refine ⟨m, hm, Or.inr ⟨acq, rel, w, e, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, hterm, h1, h2, h3,
    by rw [hl]; exact hb, hv, fun hk a' n hnw => ?_⟩⟩
  exact Nat.lt_of_le_of_lt (rts_le_depRts _ pw nw hnw) (stepRmw_ob (mem' := x.1) (th' := x.2) hx hk t ht hn)

/-- **A thread step's fulfils, with the fulfilled index** (the `tstep_ful` analysis, keeping
the bound `storeOb < t` as the data word's `rts < t`). -/
theorem tstep_fulT {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hlt : ∀ t, t ∈ th.promises → t < mem.size) (hpp : ∀ t, t ∈ th.promises → t ∉ pairs)
    (h : r ∈ tstep g mem pairs th) :
    FulT (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) (SWT g mem pairs th) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact fulT_of_keep hlt (keepR_eq rfl rfl))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       have := enter_eqM he
       exact fulT_of_keep hlt (keepR_eq rfl this))
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       have := enter_eqM he
       exact fulT_of_keep hlt (keepR_eq rfl this))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact fulT_mono (evalOp_fulT hlt hx) (fun l v t hw => Or.inl ⟨_, _, _, ‹_›, hw⟩)
         | exact cas_fulT ‹_› ‹_› ‹_› ‹_› ‹_› hx _ rfl
         | exact fulT_of_keep hlt (keepR_of (stepRmwPair_grow (x := x) hx).1
             (stepRmwPair_prom (mem' := x.1) (pairs' := x.2.1) (th' := x.2.2) hx hpp)))
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact fulT_of_keep hlt ((keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy)))
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       dsimp only
       split <;> exact fulT_mono (evalOp_fulT hlt hx) (fun l v t hw => Or.inl ⟨_, _, _, ‹_›, hw⟩))

/-! ## The data word comes from the environment -/

/-- The data atom of a storing operation is the variable `x`. -/
def DataVar : Op → String → Prop
  | .store _ _ v _, x => v = .var x
  | .xchg _ v, x => v = .var x
  | .xchgAt _ _ v, x => v = .var x
  | .xchgAtF _ _ _ v, x => v = .var x
  | .bufInit _ _ v, x => v = .var x
  | _, _ => False

theorem lookupE_mem {env : Env} {x : String} {rt : Ty} {ws : List Word}
    (h : lookupE env x = some (rt, ws)) : (x, rt, ws) ∈ env := by
  unfold lookupE at h
  cases hf : env.find? (·.1 == x) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    have hm := List.mem_of_find?_eq_some hf
    have hx := List.find?_some hf
    obtain ⟨e1, e2⟩ := e
    simp only [beq_iff_eq] at hx
    simp only [Option.map, Option.some.injEq] at h
    subst hx; subst h; exact hm

/-- A word naming a label, in an atom's value, makes the atom a variable. -/
theorem evalAt_names {env : Env} {v : At} {rt : Ty} {ws : List Word} {w : Word} {a : AllocLabel}
    (h : evalAt env v = some (rt, ws)) (hw : w ∈ ws) (hn : Names a w) :
    ∃ x, v = .var x ∧ lookupE env x = some (rt, ws) := by
  cases v with
  | var x => exact ⟨x, rfl, h⟩
  | lit n =>
    simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rw [List.mem_singleton] at hw
    subst hw
    obtain ⟨a', g, hv, -⟩ := hn
    simp [cst, Promises.TVal.mk0] at hv
  | unit =>
    simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    cases hw

theorem unitsOp_var {g : G} {env : Env} {s : St} {op : Op} {pw : Word} {b : Address} {rel : Bool}
    {us : List Acc} {ws : List Word} {w : Word} {a : AllocLabel}
    (hU : UnitsOp g env s op pw b rel us ws) (hw : w ∈ ws) (hn : Names a w) :
    ∃ x rt, DataVar op x ∧ lookupE env x = some (rt, ws) := by
  cases op <;> simp only [UnitsOp] at hU
  case store =>
    obtain ⟨-, _, t2, _, _, -, hv, -⟩ := hU
    obtain ⟨x, rfl, hx⟩ := evalAt_names hv hw hn
    exact ⟨x, t2, rfl, hx⟩
  case xchg =>
    obtain ⟨-, _, t2, _, _, -, hv, -⟩ := hU
    obtain ⟨x, rfl, hx⟩ := evalAt_names hv hw hn
    exact ⟨x, t2, rfl, hx⟩
  case xchgAt =>
    obtain ⟨-, _, _, t2, _, _, _, _, _, -, -, hv, -⟩ := hU
    obtain ⟨x, rfl, hx⟩ := evalAt_names hv hw hn
    exact ⟨x, t2, rfl, hx⟩
  case xchgAtF =>
    obtain ⟨-, _, _, t2, _, _, _, _, _, _, _, _, -, -, hv, -⟩ := hU
    obtain ⟨x, rfl, hx⟩ := evalAt_names hv hw hn
    exact ⟨x, t2, rfl, hx⟩
  case bufInit =>
    obtain ⟨-, _, _, t2, _, _, _, _, _, _, _, _, _, -, -, hv, -⟩ := hU
    obtain ⟨x, rfl, hx⟩ := evalAt_names hv hw hn
    exact ⟨x, t2, rfl, hx⟩
  case stl =>
    obtain ⟨-, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, hws⟩ := hU
    subst hws
    rw [List.mem_singleton] at hw
    subst hw
    obtain ⟨a', g, hv, -⟩ := hn
    simp [cst, Promises.TVal.mk0] at hv
  case stlw =>
    obtain ⟨-, -, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hws⟩ := hU
    subst hws
    rw [List.mem_singleton] at hw
    subst hw
    obtain ⟨a', g, hv, -⟩ := hn
    simp [cst, Promises.TVal.mk0] at hv

/-! ## K-3(i) -/

/-- The step's data word `w`, written at `loc`, comes from the environment entry `x : rt = ws`
(the operand of a storing operation, or a `cas`'s new value). -/
def WriteFrom (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (x : String) (rt : Ty) (ws : List Word)
    (w : Word) (loc : Address) : Prop :=
  lookupE th.env x = some (rt, ws) ∧ w ∈ ws ∧
  ((∃ y op e pw b rel us j, th.term = .let_ y op e ∧ DataVar op x ∧
      UnitsOp g th.env (stOf mem pairs th) op pw b rel us ws ∧ OneAt us j ∧ ws[j]? = some w ∧ loc = offs b j) ∨
   (∃ acq rel wa e tn ok fail t1 t2 pw ew, th.term = .cas acq rel wa e (.var x) tn ok fail ∧ ws = [w] ∧
      evalAt th.env wa = some (t1, [pw]) ∧ evalAt th.env e = some (t2, [ew]) ∧ addrOf pw = some loc))

/-- **Staging (PubOnly; never in a final theorem)**: the environment entry a typed thread's data
word naming a label comes from, when written into a noOwn, rgnFree cell, has a shallow-pub runtime type (so all
its words count, `pubWords_of_sNo`). -/
def FulSNo (p : Prog) : Prop :=
  ∀ (E : TEnv) (sto : Sto) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (x : String) (rt : Ty)
    (ws : List Word) (w : Word) (loc : Address) (a : AllocLabel),
    (∀ l c, E.sto l = some c → sto l = some c) → ThInvE p E th → TermStep.MemInv g E (stOf mem pairs th) →
    WriteFrom g mem pairs th x rt ws w loc → Names a w →
    (∃ ca, sto loc.label = some ca ∧ Ty.noOwnIn [] ca.ty = true ∧ rgnFree ca.ty = true) →
    sNo rt = true

theorem fetch_notLoc (o : FetchOp) (mr nw : WeakMem.Val) (a' : Address) (n : Nat) :
    o.kind.apply mr nw ≠ .loc a' n := by
  cases o <;> cases mr <;> cases nw <;> simp [FetchOp.kind, WeakMem.RmwKind.apply]

/-- **K-3(i)**: from the staging `FulSNo`, an owner thread step keeps `tmin` outstanding. -/
theorem noFul_step (p : Prog) (hF : FulSNo p) : NoFulStep p := by
  intro E sto g mem pairs th a t r hk hsto hT hM hR htm hr _
  have hlt := TermStep.MemInv_promLt hM
  have hpp := TermStep.MemInv_nopair hM
  obtain ⟨htp, m, hm, hpe⟩ := tminOf_spec htm
  obtain ⟨⟨ca, hca, hno, hrf⟩, a', n, hv, ha'⟩ := hpe
  have hRts := (hR t htm).2
  refine (Classical.em _).elim id fun hn => (?_ : False).elim
  obtain ⟨-, rem⟩ := tstep_fulT hlt hpp hr
  obtain ⟨m2, hm2, hw⟩ := rem t htp hn
  have e : m2 = m := Option.some.inj (hm2.symm.trans hm)
  subst e
  rcases hw with ⟨y, op, e, hterm, hW | hW⟩ |
      ⟨acq, rel, wa, ee, v, tn, ok, fail, t1, t2, t3, pw, ew, nw, hterm, h1, h2, h3, hb, hval, hrts⟩
  · obtain ⟨pw, b, rel, us, ws, j, w, hU, hj, hwj, hl, hval, hrts⟩ := hW
    have hwv : w.val = .loc a' n := by rw [← hval]; exact hv
    have hnames : Names a w := ⟨a', n, hwv, ha'⟩
    have hwm : w ∈ ws := List.mem_of_getElem? hwj
    obtain ⟨x, rt, hdv, hx⟩ := unitsOp_var hU hwm hnames
    have hs := hF E sto g mem pairs th x rt ws w m2.loc a hsto hT hM
      ⟨hx, hwm, Or.inl ⟨y, op, e, pw, b, rel, us, j, hterm, hdv, hU, hj, hwj, hl⟩⟩ hnames ⟨ca, hca, hno, hrf⟩
    have hle := hRts.1 x rt ws (lookupE_mem hx) w (by rw [pubWords_of_sNo hs]; exact hwm) hnames
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (hrts hk a' n hwv))
  · obtain ⟨o, -, -, -, -, -, mr, nw, hval⟩ := hW
    rw [hval] at hv
    exact fetch_notLoc o mr nw a' n hv
  · have hnv : nw.val = .loc a' n := by rw [← hval]; exact hv
    have hnames : Names a nw := ⟨a', n, hnv, ha'⟩
    obtain ⟨x, rfl, hx⟩ := evalAt_names h3 (List.mem_singleton_self nw) hnames
    have hs := hF E sto g mem pairs th x t3 [nw] nw m2.loc a hsto hT hM
      ⟨hx, List.mem_singleton_self nw, Or.inr ⟨acq, rel, wa, ee, tn, ok, fail, t1, t2, pw, ew, hterm, rfl, h1,
        h2, hb⟩⟩ hnames ⟨ca, hca, hno, hrf⟩
    have hle := hRts.1 x t3 [nw] (lookupE_mem hx) nw
      (by rw [pubWords_of_sNo hs]; exact List.mem_singleton_self nw) hnames
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hle (hrts hk a' n hnv))

end TermNoFul

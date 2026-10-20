/-
**Stage 3: promise-free instruction steps of four tree
shapes.** A thread with no outstanding promise and its views at most `|M|`
(`Thread.Bnd`) runs an instruction whose event tree is

- `done s` (a register-only instruction or a branch),
- `load k false l (fun v => done (f v))` (one plain/acquire load),
- `store k false l v (fun _ => done s)` (one plain/release store),
- `rmw k false l (fun old => some (g old)) (fun v => done (f v))` (one RMW
  that always writes, e.g. `LDADDA`).

For each shape: every outcome (`stepOne_out` and the `run_*` lemmas) and the
existence of an outcome (`stepOne_of_run` and the `run_*_exists` lemmas). The
outcomes carry no promise: a write "promises now" and fulfils at once, and
there is no older promise to fulfil.

The memory facts at the end: `finalVal` after an append, and the converse of
`Memory.atomic_of_forall`.
-/
import Kraken.Promising.ReleasePrefixNT
import Kraken.Promising.ReachCore
import Kraken.Promising.LiveTrace
import Kraken.Promising.SLR.StepRunCommon

namespace Kraken.Promising.Live.TicketStep

open Kraken.Promising

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Memory facts -/

/-- The final value of a location after an append. -/
theorem finalVal_append (m : Memory) (w : Msg) (l : Loc) :
    (m.append w).1.finalVal l = if w.loc = l then w.val else m.finalVal l := by
  unfold Memory.finalVal; simp only [Memory.append]
  by_cases hl : w.loc = l
  · rw [Array.findRev?_push_of_pos (by simpa using hl), ite_eq_left hl]
  · rw [Array.findRev?_push_of_neg (by simpa using hl), ite_eq_right hl]
    rfl

/-- A read of an appended memory at an old timestamp. -/
theorem read?_append_of_le (m : Memory) (w : Msg) (l : Loc) {t : Time} (ht : t ≤ m.last) :
    (m.append w).1.read? l t = m.read? l t := by
  unfold Memory.read?
  rw [Memory.get?_append_of_le m w t ht]
  rfl

/-- A read of an appended memory: an old one or the new message. -/
theorem read?_append_eq_some (m : Memory) (w : Msg) {l : Loc} {t : Time} {v : Val}
    (h : (m.append w).1.read? l t = some v) :
    m.read? l t = some v ∨ (t = m.last + 1 ∧ w.loc = l ∧ v = w.val) := by
  by_cases ht : t ≤ m.last
  · left; rwa [read?_append_of_le m w l ht] at h
  · right
    rcases (m.append w).1.read?_eq_some h with ⟨rfl, -⟩ | ⟨w', hw', hl, rfl⟩
    · exact absurd (Nat.zero_le _) ht
    · rcases m.get?_append_eq_some w hw' with ⟨h1, -⟩ | ⟨h1, rfl⟩
      · exact absurd h1 ht
      · exact ⟨h1, hl, rfl⟩

/-- An atomicity check up to `|M| + 1` is unchanged by an append when the
read is old (`tr ≤ |M|`). ISA-neutral original of the `atomic_append_last`
copies in `LiveTicketInvP`, `LiveX64SemInv` and `LiveX64Sem2Inv`. -/
theorem atomic_append_of_le (mem : Memory) (w : Msg) (l : Loc) (tid : Nat) {tr : Time} (htr : tr ≤ mem.last) :
    (mem.append w).1.atomic l tid tr (mem.last + 1) = mem.atomic l tid tr (mem.last + 1) := by
  unfold Memory.atomic
  rw [read?_append_of_le mem w l htr]
  cases hr : mem.read? l tr with
  | none => rfl
  | some _ =>
    simp only
    rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall_congr' fun i => imp_congr_right fun hi => ?_
    rw [List.mem_range] at hi
    rw [Memory.get?_append_of_le mem w _ (by simp only [Time] at *; omega)]

/-- **The converse of `atomic_of_forall`**: an atomic pair whose read is of
`l` has no write to `l` by another thread strictly between. -/
theorem forall_of_atomic (m : Memory) (l : Loc) (tid : Nat) (tr tw : Time) {v : Val}
    (hr : m.read? l tr = some v) (h : m.atomic l tid tr tw = true) :
    ∀ (t : Nat) w, tr < t → t < tw → m.get? t = some w → w.loc = l → w.tid = tid := by
  intro t w h1 h2 hw hl
  unfold Memory.atomic at h
  rw [hr] at h
  simp only [List.all_eq_true, List.mem_range] at h
  have := h (t - tr - 1) (by omega_t)
  have e : tr + (t - tr - 1) + 1 = t := by omega_t
  rw [e, hw] at this
  simpa [hl] using this

/-- An RMW's read, atomic with a write at `|M| + 1`, by a thread with no
write to `l` in memory, reads the last write to `l`. -/
theorem atomic_lastWrite (m : Memory) (l : Loc) (tid : Nat) {tr : Time} {v : Val}
    (hr : m.read? l tr = some v) (h : m.atomic l tid tr (m.last + 1) = true)
    (hown : ∀ t w, m.get? t = some w → w.loc = l → w.tid ≠ tid) :
    tr = m.lastWrite l ∧ v = m.finalVal l := by
  have hlw := m.read?_lastWrite l
  have htr : tr = m.lastWrite l := by
    rcases Nat.lt_trichotomy tr (m.lastWrite l) with hlt | heq | hgt
    · obtain ⟨w, hw, hl⟩ := m.get?_lastWriteBelow l m.last (by unfold Memory.lastWrite at hlt; omega_t)
      exact absurd (forall_of_atomic m l tid tr _ hr h _ w hlt
        (Nat.lt_succ_of_le (m.lastWrite_le l)) hw hl) (hown _ w hw hl)
    · exact heq
    · rcases m.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw, hl, -⟩
      · exact absurd hgt (Nat.not_lt_zero _)
      · exact absurd hl (m.not_write_of_lastWrite_lt l hgt hw)
  subst htr
  rw [hlw] at hr
  exact ⟨rfl, (Option.some.inj hr).symm⟩

/-- A read whose coherence bound is at or past the last write to `l` reads
the last write. -/
theorem read_lastWrite_of_coh (m : Memory) (l : Loc) {t bound : Time} {v : Val} (ht : t ≤ m.last)
    (hr : m.read? l t = some v) (hw : m.writeIn l t bound = false) (hb : m.lastWrite l ≤ bound) :
    t = m.lastWrite l ∧ v = m.finalVal l := by
  have htr : t = m.lastWrite l := by
    rcases Nat.lt_trichotomy t (m.lastWrite l) with hlt | heq | hgt
    · rw [m.writeIn_of_lt_lastWrite l hlt hb] at hw; cases hw
    · exact heq
    · rcases m.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw', hl, -⟩
      · exact absurd hgt (Nat.not_lt_zero _)
      · exact absurd hl (m.not_write_of_lastWrite_lt l hgt hw')
  subst htr
  rw [m.read?_lastWrite l] at hr
  exact ⟨rfl, (Option.some.inj hr).symm⟩

/-! ## `stepOne` through `runTree` -/

section Step

variable (A : Arch) (tid : Nat)

/-- The context `stepOne` starts the tree from. -/
abbrev ctx0 (t : Thread I) (mem : Memory) : Ctx :=
  { views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] }

/-- **Every outcome of `stepOne` is a run of the tree**, finished. -/
theorem stepOne_out {t : Thread I} {mem : Memory} {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    {outs : List (Except String (Outcome I))} (hs : stepOne A t tid mem = some outs) {o : Outcome I}
    (ho : .ok o ∈ outs) :
    ∃ st c', .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree ∧
      o.mem = c'.mem ∧ o.thread.st = st ∧ o.thread.prom = c'.prom ∧ o.thread.views.coh = c'.views.coh ∧
      o.log = c'.log := by
  obtain ⟨tree', c', hex', hr, hp, hv, hm, hl⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree' = tree := Option.some.inj (hex'.symm.trans hex)
  exact ⟨_, c', hr, hm, rfl, hp, by have := congrArg Views.coh hv; exact this, hl⟩

theorem finishInstr_ne_nil (t : Thread I) (d : InstrDeps I.RegId) (iv : InstrViews) (st : I.State) (c : Ctx) :
    finishInstr t d iv st c ≠ [] := by
  unfold finishInstr
  simp only
  split <;> simp

/-- **Every run of the tree is an outcome of `stepOne`.** -/
theorem stepOne_of_run {t : Thread I} {mem : Memory} {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    {st : I.State} {c' : Ctx} (hr : .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.mem = c'.mem ∧ o.thread.st = st ∧
      o.thread.prom = c'.prom := by
  obtain ⟨th, hth⟩ := List.exists_mem_of_ne_nil _
    (finishInstr_ne_nil t (I.deps t.st) (instrViews t (I.deps t.st)) st c')
  refine ⟨_, ⟨th, c'.mem, c'.promisedNow, c'.log⟩, by unfold stepOne; rw [hex]; rfl, ?_, rfl,
    finishInstr_st hth, (finishInstr_relKey hth).1⟩
  rw [List.mem_flatMap]
  exact ⟨_, hr, List.mem_map.mpr ⟨th, hth, rfl⟩⟩

end Step

/-! ## The four tree shapes -/

section Shapes

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem run_done {σ : Type} {c c' : Ctx} {s st : σ} (h : .ok (st, c') ∈ runTree A tid iv c (.done s)) :
    st = s ∧ c' = c := by
  simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  exact h

theorem run_done_exists {σ : Type} (c : Ctx) (s : σ) : .ok (s, c) ∈ runTree A tid iv c (.done s) := by
  simp [runTree]

/-- A load: the timestamp and value read, with the read's conditions. -/
theorem run_load {σ : Type} {c c' : Ctx} {k : LoadKind} {l : Loc} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.load k false l fun v => .done (f v))) :
    ∃ ts v, st = f v ∧ ts ≤ c.mem.last ∧ c.mem.read? l ts = some v ∧
      c.mem.writeIn l ts (max (readPre A iv c k) (c.views.getCoh l)) = false ∧
      c'.mem = c.mem ∧ c'.prom = c.prom ∧ (∃ ν, TraceEv.read l ts v ν ∈ c'.log) := by
  simp only [runTree, List.mem_flatMap] at h
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := h
  obtain ⟨hst, rfl⟩ := run_done A tid iv h
  obtain ⟨ts', v', hx', hle, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨h1, h2, h3⟩ := hx'
  subst h1 h2 h3
  exact ⟨_, _, hst, hle, hr, hw, rfl, rfl,
    max (readPre A iv c k) (readView A (A.loadKind k) (c.views.getFwd l) ts), by simp [readNext]⟩

/-- A load can read the last write. -/
theorem run_load_exists {σ : Type} {c : Ctx} (hp : c.prom = []) (k : LoadKind) (l : Loc) (f : Val → σ) :
    ∃ c', .ok (f (c.mem.finalVal l), c') ∈ runTree A tid iv c (.load k false l fun v => .done (f v)) := by
  refine ⟨readNext A iv c k false l false (c.mem.lastWrite l) (c.mem.finalVal l), ?_⟩
  simp only [runTree, List.mem_flatMap]
  refine ⟨(c.mem.lastWrite l, c.mem.finalVal l, readNext A iv c k false l false (c.mem.lastWrite l)
    (c.mem.finalVal l)), ?_, run_done_exists A tid iv _ _⟩
  rw [mem_readSuccs]
  refine ⟨_, _, rfl, c.mem.lastWrite_le l, c.mem.read?_lastWrite l, c.mem.writeIn_lastWrite l _, ?_⟩
  rw [hp]; rfl

/-- A promise-free non-exclusive write: it appends, and promises nothing. -/
theorem writeSuccs_nil {xr : View} {c c' : Ctx} (hp : c.prom = []) {k : StoreKind} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (h : c' ∈ writeSuccs A tid iv c k true l v tr extra xr ∨ c' ∈ writeSuccs A tid iv c k false l v tr extra xr) :
    c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧ c'.prom = [] ∧
      (∀ t0, tr = some t0 → t0 < c.mem.last + 1 ∧ c.mem.atomic l tid t0 (c.mem.last + 1) = true) := by
  have key : ∀ xcl, c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr →
      c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧ c'.prom = [] ∧
      (∀ t0, tr = some t0 → t0 < c.mem.last + 1 ∧ c.mem.atomic l tid t0 (c.mem.last + 1) = true) := by
    intro xcl h
    simp only [writeSuccs, hp, List.filterMap_nil, List.nil_append, List.mem_ite_nil_right,
      List.mem_singleton] at h
    obtain ⟨hok, rfl⟩ := h
    refine ⟨rfl, by simp [afterWrite, Memory.append], fun t0 ht0 => ?_⟩
    subst ht0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    exact hok.2
  rcases h with h | h
  · exact key true h
  · exact key false h

/-- A non-exclusive store: it appends its message. -/
theorem run_store {σ : Type} {c c' : Ctx} (hp : c.prom = []) {k : StoreKind} {l : Loc} {v : Val} {s st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.store k false l v fun _ => .done s)) :
    st = s ∧ c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧ c'.prom = [] := by
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at h
  obtain ⟨c1, h1, h⟩ := h
  obtain ⟨rfl, rfl⟩ := run_done A tid iv h
  obtain ⟨hm, hpr, -⟩ := writeSuccs_nil A tid _ hp (.inr h1)
  exact ⟨rfl, hm, hpr⟩

/-- A non-exclusive store can append its message. -/
theorem run_store_exists {σ : Type} {c : Ctx} (hp : c.prom = []) (hv : c.views.Le c.mem.last)
    (hiv : iv.Le c.mem.last) (k : StoreKind) (l : Loc) (v : Val) (s : σ) :
    ∃ c', .ok (s, c') ∈ runTree A tid iv c (.store k false l v fun _ => .done s) := by
  have hiv' := hiv.forStore c.stores
  have h1 := hiv'.addrW; have h2 := hiv'.dataW; have h3 := hiv'.condW
  have h4 := hv.vwNew; have h5 := hv.vCAP; have h6 := hv.coh l
  have h7 := hv.vrOld; have h8 := hv.vrOldNR; have h9 := hv.vwOld
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap, writeSuccs, hp, List.filterMap_nil, List.nil_append, Memory.append_time]
  refine ⟨_, _, List.mem_ite_nil_right.mpr ⟨?_, List.mem_singleton_self _⟩, run_done_exists A tid iv _ _⟩
  simp only [Bool.and_true]
  apply decide_eq_true
  split <;> (try split) <;> omega_t

theorem readNext_prom (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time) (v : Val) :
    (readNext A iv c k xcl l noRet t v).prom = c.prom := rfl

theorem readNext_mem (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time) (v : Val) :
    (readNext A iv c k xcl l noRet t v).mem = c.mem := rfl

/-- The context after an RMW's write: its memory and promises are the write's. -/
private theorem rmwPost_mem_prom (b : Bool) (c : Ctx) (l : Loc) :
    (if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }).mem = c.mem ∧
    (if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }).prom = c.prom := by
  cases b <;> exact ⟨rfl, rfl⟩

/-- An RMW that always writes: it reads some `old` at `tr`, atomic with its
write of `g old` appended at `|M| + 1`. -/
theorem run_rmw {σ : Type} (hA : A.rmwFence = false) {c c' : Ctx} (hp : c.prom = []) {k : RmwKind} {l : Loc}
    {g : Val → Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ tr old, st = f old ∧ c.mem.read? l tr = some old ∧ c.mem.atomic l tid tr (c.mem.last + 1) = true ∧
      c'.mem = (c.mem.append { loc := l, val := g old, tid }).1 ∧ c'.prom = [] := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_singleton,
    Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨tr, old, c1⟩, hx, c2, h2, hst, hc⟩ := h
  obtain ⟨tr', old', hx', -, hr, -, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  obtain ⟨hm, hpr, hat⟩ := writeSuccs_nil A tid iv (by rw [readNext_prom]; exact hp) (.inl h2)
  rw [readNext_mem] at hm hat
  obtain ⟨-, ha2⟩ := hat _ rfl
  subst hc
  obtain ⟨hm', hp'⟩ := rmwPost_mem_prom (A.rmwKind k == RmwKind.acqRel && !false) c2 l
  exact ⟨_, _, hst, hr, ha2, hm'.trans hm, hp'.trans hpr⟩

/-- An RMW that always writes can read the last write and append. -/
theorem run_rmw_exists {σ : Type} (hA : A.rmwFence = false) {c : Ctx} (hp : c.prom = []) (hb : c.Bnd)
    (hiv : iv.Le c.mem.last) (k : RmwKind) (l : Loc) (g : Val → Val) (f : Val → σ) :
    ∃ c', .ok (f (c.mem.finalVal l), c') ∈
      runTree A tid iv c (.rmw k false l (fun old => some (g old)) fun v => .done (f v)) := by
  let kl := if false = true then LoadKind.plain else (A.rmwKind k).loadKind
  let c1 := readNext A iv c kl false l false (c.mem.lastWrite l) (c.mem.finalVal l)
  have hx : (c.mem.lastWrite l, c.mem.finalVal l, c1) ∈ readSuccs A iv c kl false l false := by
    rw [mem_readSuccs]
    refine ⟨_, _, rfl, c.mem.lastWrite_le l, c.mem.read?_lastWrite l, c.mem.writeIn_lastWrite l _, ?_⟩
    rw [hp]; rfl
  obtain ⟨hb1, -, hm1⟩ := readSuccs_bnd A iv hb hiv hx
  have hm1 : c1.mem = c.mem := hm1
  have hp1 : c1.prom = [] := by simp [c1, readNext, hp]
  have hνr : c1.loadViews.getLastD 0 ≤ c.mem.last := by
    rw [← hm1]
    cases hlv : c1.loadViews.getLast? with
    | none => simp [List.getLastD_eq_getLast?, hlv]
    | some ν =>
      rw [List.getLastD_eq_getLast?, hlv]
      exact hb1.loadViews ν (List.mem_of_getLast? hlv)
  have hv := hb1.views.le
  rw [hm1] at hv
  have h1 := hiv.addrW; have h2 := hiv.dataW; have h3 := hiv.condW
  have h4 := hv.vwNew; have h5 := hv.vCAP; have h6 := hv.coh l
  have h7 := hv.vrOld; have h8 := hv.vrOldNR; have h9 := hv.vwOld
  have hat : c.mem.atomic l tid (c.mem.lastWrite l) (c.mem.last + 1) = true :=
    c.mem.atomic_of_forall l tid _ _ fun t w h1 _ hw hl => absurd hl (c.mem.not_write_of_lastWrite_lt l h1 hw)
  have hlw := c.mem.lastWrite_le l
  obtain ⟨c2, hw⟩ : ∃ c2, c2 ∈ writeSuccs A tid iv c1 (A.rmwKind k).storeKind true l
      (g (c.mem.finalVal l)) (some (c.mem.lastWrite l)) (c1.loadViews.getLastD 0) := by
    simp only [writeSuccs, hp1, List.filterMap_nil, List.nil_append, Memory.append_time, hm1]
    refine ⟨_, List.mem_ite_nil_right.mpr ⟨?_, List.mem_singleton_self _⟩⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, by omega_t, hat⟩
    split <;> (try split) <;> omega_t
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_singleton]
  exact ⟨_, _, hx, c2, hw, rfl⟩

end Shapes

/-! ## Instruction steps by shape -/

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- A `done` instruction: memory, promises and coherence views unchanged. -/
theorem spec_done {s : I.State} (hex : I.exec t.st = some (.done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    o.mem = mem ∧ o.thread.st = s ∧ o.thread.prom = t.prom ∧ o.thread.views.coh = t.views.coh := by
  obtain ⟨st, c', hr, hm, hst, hp, hc, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨rfl, rfl⟩ := run_done A tid _ hr
  exact ⟨hm, hst, hp, hc⟩

/-- **A load reads a timestamp that is not one of the thread's outstanding
promises** (`readSuccs` never offers them; moved from
`LiveTicketLoopCert`, same full name; `spec_load` is an instance). -/
theorem _root_.Kraken.Promising.Live.TicketLoopCert.spec_load_np {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧ ts ∉ t.prom ∧
      (mem.lastWrite l ≤ t.views.getCoh l → v = mem.finalVal l) ∧ o.mem = mem ∧ o.thread.prom = t.prom ∧
      ∃ ν, TraceEv.read l ts v ν ∈ o.log := by
  obtain ⟨st, c', hr, hm, hst, hp, -, hlog⟩ := stepOne_out A tid hex hs ho
  simp only [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  obtain ⟨rfl, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
  obtain ⟨ts', v', hx', hle, hrd, hw, hc⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  refine ⟨ts, v, hst, hrd, fun hin => ?_, fun hc' => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc' (Nat.le_max_right _ _))).2, hm, hp,
    max (readPre A (instrViews t (I.deps t.st)) (ctx0 tid t mem) k)
      (readView A (A.loadKind k) ((ctx0 tid t mem).views.getFwd l) ts), ?_⟩
  · have : (t.prom.contains ts) = true := List.elem_iff.mpr hin
    exact absurd hc (by simp only [this]; decide)
  · rw [hlog]; simp [readNext]

/-- A load: it reads a value of the location from memory; the last write's,
if the coherence view is at or past it. -/
theorem spec_load {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧
      (mem.lastWrite l ≤ t.views.getCoh l → v = mem.finalVal l) ∧
      o.mem = mem ∧ o.thread.prom = t.prom ∧ ∃ ν, TraceEv.read l ts v ν ∈ o.log := by
  obtain ⟨ts, v, hst, hrd, -, hc, hm, hp, hl⟩ := TicketLoopCert.spec_load_np A tid hex hs ho
  exact ⟨ts, v, hst, hrd, hc, hm, hp, hl⟩

/-- A store by a promise-free thread appends its message. -/
theorem spec_store {k : StoreKind} {l : Loc} {v : Val} {s : I.State} (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    o.mem = (mem.append { loc := l, val := v, tid }).1 ∧ o.thread.st = s ∧ o.thread.prom = [] := by
  obtain ⟨st, c', hr, hm, hst, hp, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨rfl, hm', hp'⟩ := run_store A tid _ hp0 hr
  exact ⟨hm.trans hm', hst, hp.trans hp'⟩

/-- An always-writing RMW by a promise-free thread: an atomic read and an
appended write. -/
theorem spec_rmw (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧ mem.atomic l tid tr (mem.last + 1) = true ∧
      o.mem = (mem.append { loc := l, val := g old, tid }).1 ∧ o.thread.prom = [] := by
  obtain ⟨st, c', hr, hm, hst, hp, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨tr, old, rfl, hrd, hat, hm', hp'⟩ := run_rmw A tid _ hA hp0 hr
  exact ⟨tr, old, hst, hrd, hat, hm.trans hm', hp.trans hp'⟩

theorem en_done {s : I.State} (hex : I.exec t.st = some (.done s)) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = t.prom := by
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex (run_done_exists A tid _ (ctx0 tid t mem) s)
  exact ⟨outs, o, h1, h2, h3⟩

theorem en_load {k : LoadKind} {l : Loc} {f : Val → I.State} (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨c', hr⟩ := run_load_exists A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem) hp0 k l f
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex hr
  obtain ⟨-, -, -, -, -, -, -, hp', -⟩ := run_load A tid _ hr
  exact ⟨outs, o, h1, h2, h3.trans (hp'.trans hp0)⟩

theorem en_store {k : StoreKind} {l : Loc} {v : Val} {s : I.State} (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨c', hr⟩ := run_store_exists A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem) hp0 hb.views.le
    (instrViews_le hb.regs _) k l v s
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex hr
  exact ⟨outs, o, h1, h2, h3.trans (run_store A tid _ hp0 hr).2.2⟩

theorem en_rmw (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨c', hr⟩ := run_rmw_exists A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem) hA hp0
    ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ (instrViews_le hb.regs _) k l g f
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex hr
  obtain ⟨-, -, -, -, -, -, hp'⟩ := run_rmw A tid _ hA hp0 hr
  exact ⟨outs, o, h1, h2, h3.trans hp'⟩

/-- **A promise-free outcome makes the thread instruction-enabled.** -/
theorem instrEnabled_of {fuel : Nat} {c : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)
    (hs : stepOne A t tid c.mem = some outs) (ho : .ok o ∈ outs) (hp : o.thread.prom = []) :
    InstrEnabled A fuel tid c :=
  ⟨_, reach_mem_succs A fuel (by simp [stepThread, ht, hs]) ho (by simp [hp]), _, _, _, ht, hs, ho, rfl⟩

end Spec

end Kraken.Promising.Live.TicketStep

/-
**Stage 3: stores and RMWs with outstanding
promises, and replay against a larger memory** (ISA-neutral; the four tree
shapes of `LiveTicketStep`).

- `mem_writeSuccs`: a write either appends ("promise now", which leaves the
  older promises alone and raises `vwOld` past the new timestamp unless it is
  non-temporal) or fulfils an outstanding promise of the same message, above
  the thread's `coh` of the location, and, for a release write, above
  `vwOld`. `spec_store_p`/`spec_rmw_p`: the same for a whole instruction.
- `vwOld` never decreases (`spec_done_vw`, `spec_load_vw`, and the store
  lemmas).
- `stepOne_replay`: an outcome of one of the four shapes that does not append
  to memory is also an outcome against any larger memory (`Memory.Prefix`),
  for a thread whose views are at most the smaller memory's `|M|`: reads and
  fulfilments only look at timestamps up to `|M|`, and `finishInstr` ignores
  memory. `threadNPn_replay`: a whole run of such steps.
-/
import Kraken.Promising.LiveTicketStep
import Kraken.Promising.LiveWfInstr
import Kraken.Promising.LiveSpinSwpStep

namespace Kraken.Promising.Live.SemShape

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- Erasing a fresh timestamp just appended. -/
theorem erase_fresh {p : List Time} {n : Time} (h : ∀ ts ∈ p, ts ≤ n) : (p ++ [n + 1]).erase (n + 1) = p := by
  rw [List.erase_append_right _ (fun hm => by have := h _ hm; omega_t)]
  simp

theorem append_ne (m : Memory) (w : Msg) : (m.append w).1 ≠ m := by
  intro h
  have := congrArg Memory.last h
  rw [Memory.last_append] at this
  omega_t

theorem msg_eq_of_beq {w : Msg} {l : Loc} {v : Val} {tid : Nat}
    (h : (w.loc == l && w.val == v && w.tid == tid) = true) : w = { loc := l, val := v, tid } := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  cases w; simp_all

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A write, with any promise set**, with the coherence view of the written
location after it. -/
theorem _root_.Kraken.Promising.Live.SpinSemShape.mem_writeSuccs_c {xr : View} {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    (c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧
      c'.prom = (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) ∧
      ((A.storeKind k == .nt) = false → c.mem.last + 1 ≤ c'.views.vwOld) ∧ c.views.vwOld ≤ c'.views.vwOld ∧
      c.mem.last + 1 ≤ c'.views.getCoh l ∧
      (∀ t0, tr = some t0 → t0 < c.mem.last + 1 ∧ c.mem.atomic l tid t0 (c.mem.last + 1) = true)) ∨
    (∃ ts ∈ c.prom, c.mem.get? ts = some { loc := l, val := v, tid } ∧ c.views.getCoh l < ts ∧
      ((A.storeKind k == .rel) = true → c.views.vwOld < ts) ∧ c'.mem = c.mem ∧ c'.prom = c.prom.erase ts ∧
      c.views.vwOld ≤ c'.views.vwOld ∧ ts ≤ c'.views.getCoh l ∧
      (∀ t0, tr = some t0 → t0 < ts ∧ c.mem.atomic l tid t0 ts = true)) := by
  unfold writeSuccs at h
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, ht, h⟩ | h
  · right
    cases hg : c.mem.get? t with
    | none => simp [hg] at h
    | some w =>
      simp only [hg] at h
      rw [Option.ite_none_right_eq_some] at h
      obtain ⟨hc, h⟩ := h
      obtain rfl := Option.some.inj h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hw, hb, htr⟩ := hc
      have hw' := msg_eq_of_beq (by simp only [Bool.and_eq_true]; exact hw)
      subst hw'
      simp only [decide_eq_true_eq] at hb
      refine ⟨t, ht, hg, ?_, ?_, rfl, rfl, ?_, SpinSwpStep.coh_setCoh_self _ _ _, ?_⟩
      · omega_t
      · intro hk
        simp only [hk, ↓reduceIte] at hb
        omega_t
      · show c.views.vwOld ≤ (if A.storeKind k == .nt then c.views.vwOld else max c.views.vwOld t)
        split <;> omega_t
      · intro t0 ht0; subst ht0
        simp only [Bool.and_eq_true, decide_eq_true_eq] at htr
        exact htr
  · left
    generalize hap : c.mem.append { loc := l, val := v, tid } = ap at h
    obtain ⟨mem', t⟩ := ap
    have e1 : mem' = (c.mem.append { loc := l, val := v, tid }).1 := by rw [hap]
    have e2 : t = c.mem.last + 1 := by rw [← Memory.append_time c.mem { loc := l, val := v, tid }, hap]
    subst e1 e2
    simp only at h
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨hok, rfl⟩ := h
    simp only [Bool.and_eq_true] at hok
    obtain ⟨-, htr⟩ := hok
    refine ⟨rfl, rfl, fun hk => ?_, ?_, SpinSwpStep.coh_setCoh_self _ _ _, fun t0 ht0 => ?_⟩
    · show c.mem.last + 1 ≤ (if A.storeKind k == .nt then c.views.vwOld else max c.views.vwOld (c.mem.last + 1))
      simp only [hk, Bool.false_eq_true, ↓reduceIte]; omega_t
    · show c.views.vwOld ≤ (if A.storeKind k == .nt then c.views.vwOld else max c.views.vwOld (c.mem.last + 1))
      split <;> omega_t
    · subst ht0
      simp only [Bool.and_eq_true, decide_eq_true_eq] at htr
      exact htr

/-- **A write, with any promise set**: an append, or a fulfilment (from
`SpinSemShape.mem_writeSuccs_c`). -/
theorem mem_writeSuccs {xr : View} {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr) :
    (c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧
      c'.prom = (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) ∧
      ((A.storeKind k == .nt) = false → c.mem.last + 1 ≤ c'.views.vwOld) ∧ c.views.vwOld ≤ c'.views.vwOld ∧
      (∀ t0, tr = some t0 → t0 < c.mem.last + 1 ∧ c.mem.atomic l tid t0 (c.mem.last + 1) = true)) ∨
    (∃ ts ∈ c.prom, c.mem.get? ts = some { loc := l, val := v, tid } ∧ c.views.getCoh l < ts ∧
      ((A.storeKind k == .rel) = true → c.views.vwOld < ts) ∧ c'.mem = c.mem ∧ c'.prom = c.prom.erase ts ∧
      c.views.vwOld ≤ c'.views.vwOld ∧ (∀ t0, tr = some t0 → t0 < ts ∧ c.mem.atomic l tid t0 ts = true)) := by
  rcases SpinSemShape.mem_writeSuccs_c A tid iv h with
    ⟨e1, e2, e3, e4, -, e6⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, -, e8⟩
  · exact .inl ⟨e1, e2, e3, e4, e6⟩
  · exact .inr ⟨ts, hts, e1, e2, e3, e4, e5, e6, e8⟩

/-- **A fulfilment replays against a larger memory.** -/
theorem writeSuccs_replay {xr : View} {c c' : Ctx} {mem : Memory} (hp : c.mem.Prefix mem) {k : StoreKind} {xcl : Bool}
    {l : Loc} {v : Val} {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr)
    (hm : c'.mem = c.mem) : { c' with mem := mem } ∈ writeSuccs A tid iv { c with mem := mem } k xcl l v tr extra xr := by
  unfold writeSuccs at h ⊢
  rw [List.mem_append, List.mem_filterMap] at h
  rcases h with ⟨t, ht, h⟩ | h
  · rw [List.mem_append, List.mem_filterMap]
    left
    refine ⟨t, ht, ?_⟩
    cases hg : c.mem.get? t with
    | none => simp [hg] at h
    | some w =>
      simp only [hg] at h
      rw [Option.ite_none_right_eq_some] at h
      obtain ⟨hc, h⟩ := h
      obtain rfl := Option.some.inj h
      have htl := c.mem.last_le_of_get?_eq_some hg
      simp only
      rw [hp.get? htl]
      simp only [hg]
      rw [Option.ite_none_right_eq_some]
      refine ⟨?_, rfl⟩
      cases tr with
      | none => exact hc
      | some t0 =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc ⊢
        obtain ⟨h1, h2, h3, h4⟩ := hc
        refine ⟨h1, h2, h3, ?_⟩
        rw [hp.atomic_eq h3 htl]; exact h4
  · exfalso
    generalize hap : c.mem.append { loc := l, val := v, tid } = ap at h
    obtain ⟨mem', t⟩ := ap
    have e1 : mem' = (c.mem.append { loc := l, val := v, tid }).1 := by rw [hap]
    subst e1
    simp only at h
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    exact append_ne c.mem _ hm

/-- **A read replays against a larger memory**, if its bound is within the
smaller one. -/
theorem readSuccs_replay {c : Ctx} {mem : Memory} (hp : c.mem.Prefix mem) {k : LoadKind} {xcl : Bool} {l : Loc}
    {noRet : Bool} {x : Time × Val × Ctx} (hx : x ∈ readSuccs A iv c k xcl l noRet)
    (hb : max (readPre A iv c k) (c.views.getCoh l) ≤ c.mem.last) :
    (x.1, x.2.1, { x.2.2 with mem := mem }) ∈ readSuccs A iv { c with mem := mem } k xcl l noRet := by
  obtain ⟨t, v, rfl, hle, hr, hw, hpr⟩ := (mem_readSuccs A).mp hx
  rw [mem_readSuccs]
  refine ⟨t, v, rfl, Nat.le_trans hle hp.last_le, ?_, ?_, hpr⟩
  · show mem.read? l t = some v
    rw [hp.read? hle]; exact hr
  · show mem.writeIn l t (max (readPre A iv c k) (c.views.getCoh l)) = false
    rw [hp.writeIn_eq hb]; exact hw

end Rules

/-! ## Conditional RMWs with promises

`SpinSemShape.run_rmwo_p`/`spec_rmwo_p`/`replay_rmwo` and
`SpinSemShape.mem_writeSuccs_c` were proved in `LiveSpinSemShape.lean`; they are
now here (same full names) so that
`mem_writeSuccs`, `spec_rmw_p` and `replay_rmw` are their instances. -/

section Run

variable (A : Arch) (tid : Nat) (iv : InstrViews)

private theorem rmwPost_eqC (b : Bool) (c : Ctx) (l : Loc) :
    let c' := if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }
    c'.mem = c.mem ∧ c'.prom = c.prom ∧ c'.views.vwOld = c.views.vwOld ∧ c'.views.coh = c.views.coh := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem _root_.Kraken.Promising.Live.SpinSemShape.readNext_vwOld (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc)
    (noRet : Bool)
    (t : Time) (v : Val) :
    (readNext A iv c k xcl l noRet t v).views.vwOld = c.views.vwOld := rfl

/-- **An RMW with an arbitrary operation, with any promise set** (run level). -/
theorem _root_.Kraken.Promising.Live.SpinSemShape.run_rmwo_p {σ : Type} (hA : A.rmwFence = false) {c c' : Ctx}
    {k : RmwKind} {l : Loc} {op : Val → Option Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v))) :
    ∃ tr old, st = f old ∧ tr ≤ c.mem.last ∧ c.mem.read? l tr = some old ∧
      c.mem.writeIn l tr (max (readPre A iv c (A.rmwKind k).loadKind) (c.views.getCoh l)) = false ∧
      ((op old = none ∧ c'.mem = c.mem ∧ c'.prom = c.prom ∧ c'.views.vwOld = c.views.vwOld) ∨
       (∃ new, op old = some new ∧
        ((c'.mem = (c.mem.append { loc := l, val := new, tid }).1 ∧
          c'.prom = (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) ∧
          ((A.storeKind (A.rmwKind k).storeKind == .nt) = false → c.mem.last + 1 ≤ c'.views.vwOld) ∧
          c.views.vwOld ≤ c'.views.vwOld ∧ c.mem.last + 1 ≤ c'.views.getCoh l ∧
          c.mem.atomic l tid tr (c.mem.last + 1) = true) ∨
         (∃ ts ∈ c.prom, c.mem.get? ts = some { loc := l, val := new, tid } ∧ c.views.getCoh l < ts ∧
          c'.mem = c.mem ∧ c'.prom = c.prom.erase ts ∧ c.views.vwOld ≤ c'.views.vwOld ∧
          ts ≤ c'.views.getCoh l ∧ tr < ts ∧ c.mem.atomic l tid tr ts = true)))) := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at h
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := h
  have hd := readSuccs_dord A _ hx
  obtain ⟨tr', old', hx', hle, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  refine ⟨tr, old, ?_⟩
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨rfl, rfl⟩ := run_done A tid iv h
    exact ⟨rfl, hle, hr, hw, .inl ⟨rfl, readNext_mem _ _ _ _ _ _ _ _ _, readNext_prom _ _ _ _ _ _ _ _ _,
      SpinSemShape.readNext_vwOld _ _ _ _ _ _ _ _ _⟩⟩
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨rfl, hc⟩ := run_done A tid iv h
    obtain ⟨q1, q2, q3, q4⟩ := rmwPost_eqC (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    rw [← hc] at q1 q2 q3 q4
    have qc : c'.views.getCoh l = c2.views.getCoh l := SpinSwpStep.getCoh_congr q4 l
    refine ⟨rfl, hle, hr, hw, .inr ⟨new, rfl, ?_⟩⟩
    rcases SpinSemShape.mem_writeSuccs_c A tid _ h2 with
      ⟨e1, e2, e3, e4, e5, e6⟩ | ⟨ts, hts, e1, e2, -, e4, e5, e6, e7, e8⟩
    · simp only [readNext_mem, readNext_prom, SpinSemShape.readNext_vwOld] at e1 e2 e3 e4 e5 e6
      obtain ⟨-, ha⟩ := e6 _ rfl
      exact .inl ⟨q1.trans e1, q2.trans e2, fun hk => q3 ▸ e3 hk, q3 ▸ e4, qc ▸ e5, ha⟩
    · simp only [readNext_mem, readNext_prom, SpinSemShape.readNext_vwOld] at hts e1 e4 e5 e6 e8
      obtain ⟨a1, a2⟩ := e8 _ rfl
      exact .inr ⟨ts, hts, e1, Nat.lt_of_le_of_lt (hd.coh l) e2, q1.trans e4, q2.trans e5, q3 ▸ e6, qc ▸ e7,
        a1, a2⟩

end Run

-- moved here from section `MemFacts` of `SpinSemSwpSolo` below (same
-- full name and type), for `SpinSemShape.spec_rmwo_pw`.
theorem _root_.Kraken.Promising.Live.SpinSemSwpSolo.writeIn_le {l : Loc} {mem : Memory} {lo b b' : Time}
    (h : mem.writeIn l lo b' = false) (hb : b ≤ b') : mem.writeIn l lo b = false := by
  rw [Bool.eq_false_iff] at h ⊢
  intro h'
  obtain ⟨t, w, h1, h2, h3, h4⟩ := (mem.writeIn_iff l lo b).mp h'
  exact h ((mem.writeIn_iff l lo b').mpr ⟨t, w, h1, Nat.le_trans h2 hb, h3, h4⟩)

/-! ## Instruction-level facts -/

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- `stepOne_out` with the views (but `vCAP`). -/
theorem stepOne_outV {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ c', .ok (o.thread.st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree ∧
      o.mem = c'.mem ∧ o.thread.prom = c'.prom ∧ o.thread.views.vwOld = c'.views.vwOld := by
  obtain ⟨tree', c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree' = tree := Option.some.inj (hex'.symm.trans hex)
  exact ⟨c', hr, hm, hp, by have := congrArg Views.vwOld hv; exact this⟩

theorem spec_done_vw {s : I.State} (hex : I.exec t.st = some (.done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.views.vwOld = t.views.vwOld := by
  obtain ⟨c', hr, -, -, hv⟩ := stepOne_outV A tid hex hs ho
  obtain ⟨-, rfl⟩ := run_done A tid _ hr
  exact hv

theorem spec_load_vw {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.views.vwOld = t.views.vwOld := by
  obtain ⟨c', hr, -, -, hv⟩ := stepOne_outV A tid hex hs ho
  simp only [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
  obtain ⟨ts', v', hx', -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  exact hv

/-- **A store, with any promise set, with the coherence view after it**: an
append or a fulfilment (moved from `LiveTicketLoopCert`, same full
name; `spec_store_p` is an instance). -/
theorem _root_.Kraken.Promising.Live.TicketLoopCert.spec_store_c {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.st = s ∧
    ((o.mem = (mem.append { loc := l, val := v, tid }).1 ∧
      o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
      ((A.storeKind k == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld) ∧
      t.views.vwOld ≤ o.thread.views.vwOld ∧ mem.last + 1 ≤ o.thread.views.getCoh l) ∨
    (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := v, tid } ∧ t.views.getCoh l < ts ∧
      ((A.storeKind k == .rel) = true → t.views.vwOld < ts) ∧ o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧
      t.views.vwOld ≤ o.thread.views.vwOld ∧ ts ≤ o.thread.views.getCoh l)) := by
  obtain ⟨tree, c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  have hvw : o.thread.views.vwOld = c'.views.vwOld := by have := congrArg Views.vwOld hv; exact this
  have hco : o.thread.views.getCoh l = c'.views.getCoh l :=
    SpinSwpStep.getCoh_congr (by have := congrArg Views.coh hv; exact this) l
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at hr
  obtain ⟨c1, h1, h⟩ := hr
  simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hst, rfl⟩ := h
  refine ⟨hst, ?_⟩
  rcases SpinSemShape.mem_writeSuccs_c A tid _ h1 with
    ⟨e1, e2, e3, e4, e5, -⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, e7, -⟩
  · exact .inl ⟨hm.trans e1, hp.trans e2, fun hk => hvw ▸ e3 hk, hvw ▸ e4, hco ▸ e5⟩
  · exact .inr ⟨ts, hts, e1, e2, e3, hm.trans e4, hp.trans e5, hvw ▸ e6, hco ▸ e7⟩

/-- **A store, with any promise set**: an append or a fulfilment. -/
theorem spec_store_p {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.st = s ∧
    ((o.mem = (mem.append { loc := l, val := v, tid }).1 ∧
      o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
      ((A.storeKind k == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld)) ∨
    (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := v, tid } ∧ t.views.getCoh l < ts ∧
      ((A.storeKind k == .rel) = true → t.views.vwOld < ts) ∧ o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧
      t.views.vwOld ≤ o.thread.views.vwOld)) := by
  obtain ⟨hst, ⟨e1, e2, e3, -, -⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, -⟩⟩ :=
    TicketLoopCert.spec_store_c A tid hex hs ho
  · exact ⟨hst, .inl ⟨e1, e2, e3⟩⟩
  · exact ⟨hst, .inr ⟨ts, hts, e1, e2, e3, e4, e5, e6⟩⟩

private theorem rmwPost_eq (b : Bool) (c : Ctx) (l : Loc) :
    let c' := if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }
    c'.mem = c.mem ∧ c'.prom = c.prom ∧ c'.views.vwOld = c.views.vwOld := by
  cases b <;> exact ⟨rfl, rfl, rfl⟩

/-- **An RMW with an arbitrary operation, with any promise set**, with the
read's write-free window up to the coherence view (shared by
`SpinSemShape.spec_rmwo_p` and `TicketLoopCert.spec_rmw_w`): it reads `old`
at `tr` (the last write's value, if the coherence view is at or past it), with
no write to `l` after `tr` up to the coherence view; then no write (memory,
promises and `vwOld` unchanged), or an atomic append (coherence view of `l`
raised to it, `vwOld` past it unless non-temporal), or the atomic fulfilment
of an outstanding promise above the coherence view (coherence view raised to
it). -/
theorem _root_.Kraken.Promising.Live.SpinSemShape.spec_rmwo_pw (hA : A.rmwFence = false) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State} (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧
      (mem.lastWrite l ≤ t.views.getCoh l → old = mem.finalVal l) ∧ mem.writeIn l tr (t.views.getCoh l) = false ∧
      ((op old = none ∧ o.mem = mem ∧ o.thread.prom = t.prom ∧ o.thread.views.vwOld = t.views.vwOld) ∨
       (∃ new, op old = some new ∧
        ((o.mem = (mem.append { loc := l, val := new, tid }).1 ∧
          o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
          ((A.storeKind (A.rmwKind k).storeKind == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld) ∧
          t.views.vwOld ≤ o.thread.views.vwOld ∧ mem.last + 1 ≤ o.thread.views.getCoh l ∧
          mem.atomic l tid tr (mem.last + 1) = true) ∨
         (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := new, tid } ∧ t.views.getCoh l < ts ∧
          o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
          ts ≤ o.thread.views.getCoh l ∧ tr < ts ∧ mem.atomic l tid tr ts = true)))) := by
  obtain ⟨tree, c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  have hvw : o.thread.views.vwOld = c'.views.vwOld := by have := congrArg Views.vwOld hv; exact this
  have hco : o.thread.views.getCoh l = c'.views.getCoh l :=
    SpinSwpStep.getCoh_congr (by have := congrArg Views.coh hv; exact this) l
  obtain ⟨tr, old, hst, hle, hrd, hw, hcase⟩ := SpinSemShape.run_rmwo_p A tid _ hA hr
  refine ⟨tr, old, hst, hrd, fun hc' => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc' (Nat.le_max_right _ _))).2, SpinSemSwpSolo.writeIn_le hw (Nat.le_max_right _ _), ?_⟩
  rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨new, h1, ⟨e1, e2, e3, e4, e5, e6⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, e7, e8⟩⟩
  · exact .inl ⟨h1, hm.trans h2, hp.trans h3, hvw.trans h4⟩
  · exact .inr ⟨new, h1, .inl ⟨hm.trans e1, hp.trans e2, fun hk => hvw ▸ e3 hk, hvw ▸ e4, hco ▸ e5, e6⟩⟩
  · exact .inr ⟨new, h1, .inr ⟨ts, hts, e1, e2, hm.trans e3, hp.trans e4, hvw ▸ e5, hco ▸ e6, e7, e8⟩⟩

/-- **An RMW with an arbitrary operation, with any promise set**: it reads
`old` at `tr` (the last write's value, if the coherence view is at or past
it); then no write (memory, promises and `vwOld` unchanged), or an atomic
append (coherence view of `l` raised to it, `vwOld` past it unless
non-temporal), or the atomic fulfilment of an outstanding promise above the
coherence view (coherence view raised to it). -/
theorem _root_.Kraken.Promising.Live.SpinSemShape.spec_rmwo_p (hA : A.rmwFence = false) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State} (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧
      (mem.lastWrite l ≤ t.views.getCoh l → old = mem.finalVal l) ∧
      ((op old = none ∧ o.mem = mem ∧ o.thread.prom = t.prom ∧ o.thread.views.vwOld = t.views.vwOld) ∨
       (∃ new, op old = some new ∧
        ((o.mem = (mem.append { loc := l, val := new, tid }).1 ∧
          o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
          ((A.storeKind (A.rmwKind k).storeKind == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld) ∧
          t.views.vwOld ≤ o.thread.views.vwOld ∧ mem.last + 1 ≤ o.thread.views.getCoh l ∧
          mem.atomic l tid tr (mem.last + 1) = true) ∨
         (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := new, tid } ∧ t.views.getCoh l < ts ∧
          o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
          ts ≤ o.thread.views.getCoh l ∧ tr < ts ∧ mem.atomic l tid tr ts = true)))) := by
  obtain ⟨tr, old, hst, hrd, hlw, -, hcase⟩ := SpinSemShape.spec_rmwo_pw A tid hA hex hs ho
  exact ⟨tr, old, hst, hrd, hlw, hcase⟩

/-- **An always-writing RMW, with any promise set**: an atomic read, then an
append or a fulfilment (`SpinSemShape.spec_rmwo_p` at an always-writing
operation). -/
theorem spec_rmw_p (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧
    ((o.mem = (mem.append { loc := l, val := g old, tid }).1 ∧
      o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
      ((A.storeKind (A.rmwKind k).storeKind == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld) ∧
      mem.atomic l tid tr (mem.last + 1) = true) ∨
    (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := g old, tid } ∧ t.views.getCoh l < ts ∧
      o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
      tr < ts ∧ mem.atomic l tid tr ts = true)) := by
  obtain ⟨tr, old, hst, hrd, -, hcase⟩ := SpinSemShape.spec_rmwo_p A tid hA hex hs ho
  refine ⟨tr, old, hst, hrd, ?_⟩
  rcases hcase with ⟨h1, -⟩ | ⟨new, h1, ⟨e1, e2, e3, -, -, e6⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, -, e7, e8⟩⟩
  · exact absurd h1 (by simp)
  · cases Option.some.inj h1; exact .inl ⟨e1, e2, e3, e6⟩
  · cases Option.some.inj h1; exact .inr ⟨ts, hts, e1, e2, e3, e4, e5, e7, e8⟩

end Spec

/-! ## Replay against a larger memory -/

section Replay

variable (A : Arch) (tid : Nat) {t : Thread I} {mem0 mem : Memory}

/-- An outcome whose tree run replays against `mem` (with the same final
context but its memory) is an outcome against `mem`. -/
theorem stepOne_replay_of_run {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    {outs : List (Except String (Outcome I))} {o : Outcome I} (hs : stepOne A t tid mem0 = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem = mem0)
    (hrun : ∀ st c0', .ok (st, c0') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem0) tree →
      c0'.mem = mem0 → .ok (st, { c0' with mem := mem }) ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  unfold stepOne at hs ⊢
  rw [hex] at hs ⊢
  have hs' : _ = outs := Option.some.inj hs
  subst hs'
  rw [List.mem_flatMap] at ho
  obtain ⟨r, hr, ho⟩ := ho
  cases r with
  | error m => simp at ho
  | ok p =>
    obtain ⟨st, c0'⟩ := p
    simp only [List.mem_map, Except.ok.injEq] at ho
    obtain ⟨th, hth, rfl⟩ := ho
    refine ⟨_, ⟨th, mem, c0'.promisedNow, c0'.log⟩, rfl, ?_, rfl, rfl⟩
    rw [List.mem_flatMap]
    refine ⟨_, hrun st c0' hr hm, ?_⟩
    simp only [List.mem_map]
    exact ⟨th, hth, rfl⟩

variable {outs : List (Except String (Outcome I))} {o : Outcome I}
  (hp : mem0.Prefix mem) (hb : t.Bnd mem0.last) (hs : stepOne A t tid mem0 = some outs) (ho : .ok o ∈ outs)
  (hm : o.mem = mem0)

include hp hb hs ho hm

theorem replay_done {s : I.State} (hex : I.exec t.st = some (.done s)) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr _ => ?_
  obtain ⟨rfl, rfl⟩ := run_done A tid _ hr
  exact run_done_exists A tid _ _ _

theorem replay_load {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr _ => ?_
  have hiv := instrViews_le hb.regs (I.deps t.st)
  have hv := hb.views.le
  have hbd : max (readPre A (instrViews t (I.deps t.st)) (ctx0 tid t mem0) k) ((ctx0 tid t mem0).views.getCoh l) ≤
      (ctx0 tid t mem0).mem.last := by
    have := hiv.addrR; have := hv.vrNew; have := hv.vRel; have := hv.coh l
    simp only [readPre]; split <;> omega_t
  rw [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hx' := readSuccs_replay A _ hp hx hbd
  rw [runTree, List.mem_flatMap]
  refine ⟨(ts, v, { c1 with mem := mem }), hx', ?_⟩
  show Except.ok (st, { c0' with mem := mem }) ∈ runTree A tid _ { c1 with mem := mem } (.done (f v))
  rw [runTree, List.mem_singleton, h1, h2]

theorem replay_store {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr hm' => ?_
  rw [runTree] at hr
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap] at hr
  obtain ⟨c1, h1, h⟩ := hr
  rw [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h2, h3⟩ := h
  have h1' := writeSuccs_replay A tid _ hp h1 (h3 ▸ hm')
  rw [runTree]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap]
  refine ⟨{ c1 with mem := mem }, h1', ?_⟩
  rw [runTree, List.mem_singleton, h2, h3]

/-- **An RMW outcome with an arbitrary operation that does not append
replays against a larger memory** (`SemShape.replay_rmw` for any `op`). -/
theorem _root_.Kraken.Promising.Live.SpinSemShape.replay_rmwo (hA : A.rmwFence = false) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State} (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr hm' => ?_
  have hiv := instrViews_le hb.regs (I.deps t.st)
  have hv := hb.views.le
  have hbd : ∀ kl, max (readPre A (instrViews t (I.deps t.st)) (ctx0 tid t mem0) kl)
      ((ctx0 tid t mem0).views.getCoh l) ≤ (ctx0 tid t mem0).mem.last := by
    intro kl
    have := hiv.addrR; have := hv.vrNew; have := hv.vRel; have := hv.coh l
    simp only [readPre]; split <;> omega_t
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at hr ⊢
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  have hx' := readSuccs_replay A _ hp hx (hbd _)
  have hc1 : c1.mem = mem0 := by
    obtain ⟨tr', old', hxe, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨-, -, rfl⟩ := hxe
    rfl
  refine ⟨(tr, old, { c1 with mem := mem }), hx', ?_⟩
  dsimp only at h ⊢
  cases hop : op old with
  | none =>
    simp only [hop] at h ⊢
    obtain ⟨rfl, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    exact run_done_exists A tid (instrViews t (I.deps t.st)) _ _
  | some new =>
    simp only [hop, List.mem_flatMap] at h ⊢
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨hst, hc⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    obtain ⟨q1, -, -, -⟩ := rmwPost_eqC (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    have hm2 : c2.mem = c1.mem := by rw [hc1, ← q1, ← hc]; exact hm'
    have h2' := writeSuccs_replay A tid _ (hc1 ▸ hp) h2 hm2
    refine ⟨{ c2 with mem := mem }, h2', ?_⟩
    rw [hst, hc]
    cases (A.rmwKind k == RmwKind.acqRel && !false) <;> exact run_done_exists A tid (instrViews t (I.deps t.st)) _ _

/-- `SpinSemShape.replay_rmwo` at an always-writing operation. -/
theorem replay_rmw (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem :=
  SpinSemShape.replay_rmwo A tid hp hb hs ho hm hA hex

end Replay

end Kraken.Promising.Live.SemShape

/-! # Zeros, gaps and swaps with promises

Moved here (same full names, ISA-neutral) from `LiveSpinSemSwpSolo`, which
imports this module: `ZeroAt`/`ZNot`/`Gap`/`TopZ` (+ `mono`), `read_le`,
`val_zero`, `read_zero`, `read_zero_gap`, `writeIn_le`, `run_swp_p`,
`spec_swp_p`, `spec_load_w`; this file also has the layout-free `zeroAt_back` etc.
and `SpinSemSwpInv.get_new`/`get_none`. -/

namespace Kraken.Promising.Live.SpinSemSwpSolo

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Zeros and gaps of a location -/

section Mem

variable (l : Loc) (mem : Memory)

/-- `z` is a zero of `l`: the initial write (timestamp `0`) of value `0`, or
a write of `0` to `l`. -/
def ZeroAt (z : Time) : Prop := (z = 0 ∧ mem.initVal l = 0) ∨ ∃ w, mem.get? z = some w ∧ w.loc = l ∧ w.val = 0

/-- The write at `z`, if any, is not by `tid`. -/
def ZNot (z : Time) (tid : Nat) : Prop := z = 0 ∨ ∃ w, mem.get? z = some w ∧ w.tid ≠ tid

/-- No write to `l` strictly between `z` and `m`. -/
def Gap (z m : Time) : Prop := ∀ ts w, z < ts → ts < m → mem.get? ts = some w → w.loc ≠ l

/-- No zero of `l` above `z`. -/
def TopZ (z : Time) : Prop := ∀ ts w, z < ts → mem.get? ts = some w → w.loc = l → w.val ≠ 0

end Mem

section MemFacts

variable {l : Loc} {mem mem' : Memory}

theorem ZeroAt.mono {z : Time} (hp : mem.Prefix mem') (h : ZeroAt l mem z) : ZeroAt l mem' z := by
  rcases h with ⟨rfl, h⟩ | ⟨w, hw, h⟩
  · exact .inl ⟨rfl, by rw [hp.initVal]; exact h⟩
  · exact .inr ⟨w, by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw, h⟩

theorem ZNot.mono {z : Time} {tid : Nat} (hp : mem.Prefix mem') (h : ZNot mem z tid) : ZNot mem' z tid := by
  rcases h with h | ⟨w, hw, h⟩
  · exact .inl h
  · exact .inr ⟨w, by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw, h⟩

theorem Gap.mono {z m : Time} (hp : mem.Prefix mem') (hm : m ≤ mem.last + 1) (h : Gap l mem z m) :
    Gap l mem' z m :=
  fun ts w h1 h2 hw => h ts w h1 h2 (by rw [← hp.get? (by omega_t)]; exact hw)

/-! Smaller memories (layout-free; `ZeroAt.back` etc. of
`LiveSpinSemSwpSolo` and `SpinX64SemXchgSolo.zeroAt_back` etc. are instances). -/

theorem zeroAt_back {z : Time} (hp : mem.Prefix mem') (hz : z ≤ mem.last) (h : ZeroAt l mem' z) :
    ZeroAt l mem z := by
  rcases h with ⟨rfl, h⟩ | ⟨w, hw, h⟩
  · exact .inl ⟨rfl, by rw [← hp.initVal l]; exact h⟩
  · exact .inr ⟨w, by rw [← hp.get? hz]; exact hw, h⟩

theorem zNot_back {z : Time} {tid : Nat} (hp : mem.Prefix mem') (hz : z ≤ mem.last) (h : ZNot mem' z tid) :
    ZNot mem z tid := by
  rcases h with h | ⟨w, hw, h⟩
  · exact .inl h
  · exact .inr ⟨w, by rw [← hp.get? hz]; exact hw, h⟩

theorem topZ_back {z : Time} (hp : mem.Prefix mem') (h : TopZ l mem' z) : TopZ l mem z :=
  fun ts w h1 hw => h ts w h1 (by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw)

theorem gap_back {z m : Time} (hp : mem.Prefix mem') (h : Gap l mem' z m) : Gap l mem z m :=
  fun ts w h1 h2 hw => h ts w h1 h2 (by rw [hp.get? (mem.last_le_of_get?_eq_some hw)]; exact hw)

/-! Appends (moved from `LiveSpinSemSwpInv`, same full names). -/

theorem _root_.Kraken.Promising.Live.SpinSemSwpInv.get_new {w w' : Msg} {m : Time}
    (h : (mem.append w).1.get? m = some w') (hm : ¬ m ≤ mem.last) : m = mem.last + 1 ∧ w' = w := by
  rcases Memory.get?_append_eq_some _ _ h with ⟨h1, -⟩ | h2
  · exact absurd h1 hm
  · exact h2

theorem _root_.Kraken.Promising.Live.SpinSemSwpInv.get_none {w : Msg} {m : Time} (h : mem.get? m = some w)
    (hm : ¬ m ≤ mem.last) : False :=
  hm (mem.last_le_of_get?_eq_some h)

theorem read_le {tr : Time} {v : Val} (hr : mem.read? l tr = some v) : tr ≤ mem.last := by
  rcases mem.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw, -⟩
  · exact Nat.zero_le _
  · exact mem.last_le_of_get?_eq_some hw

/-- A read of `l` at `tr ≥ z`, a zero, with the write at `tr` (if above `z`)
of value `0`, reads `0`. -/
theorem val_zero {tr z : Time} {v : Val} (hr : mem.read? l tr = some v) (hz : ZeroAt l mem z) (hle : z ≤ tr)
    (h : ∀ w, z < tr → mem.get? tr = some w → w.loc = l → w.val = 0) : v = 0 := by
  rcases mem.read?_eq_some hr with ⟨rfl, rfl⟩ | ⟨w, hw, hl, rfl⟩
  · rcases hz with ⟨-, h0⟩ | ⟨w, hw, -⟩
    · exact h0
    · obtain rfl : z = 0 := by omega_t
      rw [mem.get?_zero] at hw; cases hw
  · rcases Nat.lt_or_ge z tr with hlt | hge
    · exact h w hlt hw hl
    · obtain rfl : tr = z := by omega_t
      rcases hz with ⟨rfl, -⟩ | ⟨w', hw', -, h0⟩
      · rw [mem.get?_zero] at hw; cases hw
      · rw [hw] at hw'; cases hw'; exact h0

/-- **A read whose coherence bound is at or past a zero `z`, with every write
to `l` above `z` of value `0`, reads `0`.** -/
theorem read_zero {tr b z : Time} {v : Val} (hr : mem.read? l tr = some v) (hw : mem.writeIn l tr b = false)
    (hz : ZeroAt l mem z) (hzb : z ≤ b) (habove : ∀ ts w, z < ts → mem.get? ts = some w → w.loc = l → w.val = 0) :
    v = 0 := by
  refine val_zero hr hz (Nat.le_of_not_lt fun hlt => ?_) fun w h1 h2 h3 => habove _ w h1 h2 h3
  rcases hz with ⟨rfl, -⟩ | ⟨w, hwz, hl, -⟩
  · exact Nat.not_lt_zero _ hlt
  · rw [(mem.writeIn_iff l tr b).mpr ⟨z, w, hlt, hzb, hwz, hl⟩] at hw; cases hw

/-- **An atomic read paired with a write at `m`, with a zero `z < m` not
written by the thread and no write to `l` strictly between, reads `0`.** -/
theorem read_zero_gap {tr z m : Time} {tid : Nat} {v : Val} (hr : mem.read? l tr = some v)
    (ha : mem.atomic l tid tr m = true) (htr : tr < m) (hz : ZeroAt l mem z) (hzn : ZNot mem z tid) (hzm : z < m)
    (hg : Gap l mem z m) : v = 0 := by
  refine val_zero hr hz (Nat.le_of_not_lt fun hlt => ?_) fun w h1 h2 h3 => absurd h3 (hg tr w h1 htr h2)
  rcases hz with ⟨rfl, -⟩ | ⟨w, hwz, hl, -⟩
  · exact Nat.not_lt_zero _ hlt
  · rcases hzn with rfl | ⟨w', hw', hne⟩
    · exact Nat.not_lt_zero _ hlt
    · rw [hwz] at hw'; cases hw'
      exact hne (forall_of_atomic mem l tid tr m hr ha z w hlt hzm hwz hl)

end MemFacts

/-! ## Swaps and loads with promises -/

section Swap

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A swap (an RMW always writing `v`), with any promise set** (run level):
`SpinSemShape.run_rmwo_p` at `fun _ => some v`, keeping the release
fulfilment's `vwOld` bound (candidate). -/
theorem run_swp_p (hA : A.rmwFence = false) {σ : Type} {c c' : Ctx} {k : RmwKind} {l : Loc} {v : Val}
    {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l (fun _ => some v) fun x => .done (f x))) :
    ∃ tr old, st = f old ∧ c.mem.read? l tr = some old ∧ c.mem.writeIn l tr (c.views.getCoh l) = false ∧
      ((c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧
        c'.prom = (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) ∧
        c.mem.last + 1 ≤ c'.views.getCoh l ∧ c.mem.atomic l tid tr (c.mem.last + 1) = true) ∨
       (∃ ts ∈ c.prom, c.mem.get? ts = some { loc := l, val := v, tid } ∧ c.views.getCoh l < ts ∧
        ((A.storeKind (A.rmwKind k).storeKind == .rel) = true → c.views.vwOld < ts) ∧ c'.mem = c.mem ∧
        c'.prom = c.prom.erase ts ∧ c.views.vwOld ≤ c'.views.vwOld ∧ ts ≤ c'.views.getCoh l ∧ tr < ts ∧
        c.mem.atomic l tid tr ts = true)) := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at h
  obtain ⟨⟨tr, old, c1⟩, hx, c2, h2, h⟩ := h
  have hd := readSuccs_dord A _ hx
  obtain ⟨tr', old', hx', -, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  obtain ⟨rfl, hc⟩ := run_done A tid iv h
  obtain ⟨q1, q2, q3, q4⟩ := rmwPost_eqC (A.rmwKind k == RmwKind.acqRel && !false) c2 l
  rw [← hc] at q1 q2 q3 q4
  have qc : c'.views.getCoh l = c2.views.getCoh l := SpinSwpStep.getCoh_congr q4 l
  refine ⟨tr, old, rfl, hr, writeIn_le hw (Nat.le_max_right _ _), ?_⟩
  rcases SpinSemShape.mem_writeSuccs_c A tid _ h2 with ⟨e1, e2, -, -, e5, e6⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, e7, e8⟩
  · simp only [readNext_mem, readNext_prom] at e1 e2 e5 e6
    obtain ⟨-, ha⟩ := e6 _ rfl
    exact .inl ⟨q1.trans e1, q2.trans e2, qc ▸ e5, ha⟩
  · simp only [readNext_mem, readNext_prom, SpinSemShape.readNext_vwOld] at hts e1 e3 e4 e5 e6 e8
    obtain ⟨a1, a2⟩ := e8 _ rfl
    exact .inr ⟨ts, hts, e1, Nat.lt_of_le_of_lt (hd.coh l) e2, e3, q1.trans e4, q2.trans e5, q3 ▸ e6, qc ▸ e7,
      a1, a2⟩

variable {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))} {o : Outcome I}

/-- **A swap, with any promise set**: an atomic read below the coherence
bound, then an atomic append or the atomic fulfilment of an outstanding
promise above the coherence view (raised to the written timestamp). -/
theorem spec_swp_p (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {v : Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun _ => some v) fun x => .done (f x)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧ mem.writeIn l tr (t.views.getCoh l) = false ∧
      ((o.mem = (mem.append { loc := l, val := v, tid }).1 ∧
        o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
        mem.last + 1 ≤ o.thread.views.getCoh l ∧ mem.atomic l tid tr (mem.last + 1) = true) ∨
       (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := v, tid } ∧ t.views.getCoh l < ts ∧
        ((A.storeKind (A.rmwKind k).storeKind == .rel) = true → t.views.vwOld < ts) ∧ o.mem = mem ∧
        o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧ ts ≤ o.thread.views.getCoh l ∧
        tr < ts ∧ mem.atomic l tid tr ts = true)) := by
  obtain ⟨tree, c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  have hvw : o.thread.views.vwOld = c'.views.vwOld := by have := congrArg Views.vwOld hv; exact this
  have hco : o.thread.views.getCoh l = c'.views.getCoh l :=
    SpinSwpStep.getCoh_congr (by have := congrArg Views.coh hv; exact this) l
  obtain ⟨tr, old, hst, hrd, hw, ⟨e1, e2, e3, e4⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, e7, e8, e9⟩⟩ :=
    run_swp_p A tid _ hA hr
  · exact ⟨tr, old, hst, hrd, hw, .inl ⟨hm.trans e1, hp.trans e2, hco ▸ e3, e4⟩⟩
  · exact ⟨tr, old, hst, hrd, hw, .inr ⟨ts, hts, e1, e2, e3, hm.trans e4, hp.trans e5, hvw ▸ e6, hco ▸ e7, e8, e9⟩⟩

/-- A load reads below its coherence bound. -/
theorem spec_load_w {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧ mem.writeIn l ts (t.views.getCoh l) = false := by
  obtain ⟨st, c', hr, -, hst, -, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨ts, v, rfl, -, hrd, hw, -⟩ := run_load A tid _ hr
  exact ⟨ts, v, hst, hrd, writeIn_le hw (Nat.le_max_right _ _)⟩

end Swap

end Kraken.Promising.Live.SpinSemSwpSolo

/-! # Least and greatest witnesses (moved from `LiveSpinSemSwpLive`,
same full names; `SpinX64SemXchgLive`'s are instances) -/

namespace Kraken.Promising.Live.SpinSemSwpLive

/-- A least witness, without `Nat.find`. -/
theorem exists_least {p : Nat → Prop} : ∀ N n, n ≤ N → p n → ∃ m, p m ∧ ∀ k, k < m → ¬ p k
  | 0, n, hn, h => ⟨n, h, fun k hk => absurd hk (by omega)⟩
  | N + 1, n, hn, h => by
    by_cases e : ∃ k, k < n ∧ p k
    · obtain ⟨k, hk, hpk⟩ := e
      exact exists_least N k (by omega) hpk
    · exact ⟨n, h, fun k hk hpk => e ⟨k, hk, hpk⟩⟩

/-- A greatest witness up to a bound, without `Nat.findGreatest`. -/
theorem exists_greatest {p : Nat → Prop} (h0 : p 0) : ∀ N, ∃ m, m ≤ N ∧ p m ∧ ∀ k, m < k → k ≤ N → ¬ p k
  | 0 => ⟨0, Nat.le_refl _, h0, fun k h1 h2 => absurd h1 (by omega)⟩
  | N + 1 => by
    by_cases e : p (N + 1)
    · exact ⟨N + 1, Nat.le_refl _, e, fun k h1 h2 => absurd h1 (by omega)⟩
    · obtain ⟨m, hm, hp, hk⟩ := exists_greatest h0 N
      refine ⟨m, by omega, hp, fun k h1 h2 => ?_⟩
      rcases Nat.lt_or_ge N k with h | h
      · obtain rfl : k = N + 1 := by omega
        exact e
      · exact hk k h1 h

end Kraken.Promising.Live.SpinSemSwpLive

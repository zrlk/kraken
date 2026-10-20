/-
**The three model facts behind F3** (ISA-neutral,
program-independent; Promising-ARM views of `Thread.lean`).

The holder argument of `LiveTicketLoopHolder.lean` (F3 of KNOWN_GAPS,
"Liveness: repeated acquisition (LOOP)") rests on three facts about the
views of one instruction:

1. **A release write's pre-view takes `vwOld`** (`mem_writeSuccs_rel`,
   `spec_store_rel`): a release store fulfils only promises above the thread's
   `vwOld`, and it raises `vRel` to the timestamp it writes. With fact 3 of
   `SemShape.mem_writeSuccs` (a non-`nt` write raises `vwOld` past its
   timestamp), a fresh write kills every older promise to the release's
   location.
2. **An acquire read's pre-view takes `vRel`** (`readNext_acq_vRel`): so
   after a release write at `t`, every later acquire read has post-view at
   least `t`.
3. **An acquire read raises `vwNew`** to its post-view (`readNext_acq_vwNew`),
   so every later write lies above it; with fact 2, an acquire RMW after a
   release at `t` fulfils no promise at or below `t` and leaves `vwNew ≥ t`
   (`spec_rmw_acq`).

Also: a `done` instruction leaves `vRel` alone (`spec_done_vRel`), and a
promise at or below the thread's `vwNew`, or its `coh` of the promise's
location, stays outstanding forever (`DeadW`, `deadW_step`: the `vwNew` and
`coh` thirds of `Thread.hasDeadPromise`).
-/
import Kraken.Promising.LiveSemShape
import Kraken.Promising.LiveWfProm

namespace Kraken.Promising.Live.LoopFacts

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Fact 2 and fact 3: acquire reads -/

section Read

variable (A : Arch) (iv : InstrViews)

/-- **Fact 2: an acquire read's pre-view takes `vRel`**: its post-view, and so
the new `vrNew`, is at least the thread's `vRel`. -/
theorem readNext_acq_vRel {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val}
    (hk : A.loadKind k = .acq) : c.views.vRel ≤ (readNext A iv c k xcl l noRet t v).views.vrNew := by
  have hb : (LoadKind.acq == LoadKind.acq) = true := by decide
  simp only [readNext, readPre, hk, LoadKind.isAcquire, hb, ↓reduceIte, Views.setCoh]
  omega_t

/-- **Fact 3: an acquire read raises `vwNew`** to its post-view, which is at
least its pre-view (and so, by fact 2, the thread's `vRel`). -/
theorem readNext_acq_vwNew {c : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {noRet : Bool} {t : Time} {v : Val}
    (hk : A.loadKind k = .acq) : c.views.vRel ≤ (readNext A iv c k xcl l noRet t v).views.vwNew := by
  have hb : (LoadKind.acq == LoadKind.acq) = true := by decide
  simp only [readNext, readPre, hk, LoadKind.isAcquire, hb, ↓reduceIte, Views.setCoh]
  omega_t

end Read

/-! ## Fact 1: release writes -/

section Write

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **Fact 1: a release write's pre-view takes `vwOld`**: a write of a release
kind either appends at `|M| + 1` (raising `vRel` to it) or fulfils an
outstanding promise of the same message above `vwOld` (raising `vRel` to
it). -/
theorem mem_writeSuccs_rel {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} (hk : A.storeKind k = .rel) (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) :
    (c'.mem = (c.mem.append { loc := l, val := v, tid }).1 ∧
      c'.prom = (c.prom ++ [c.mem.last + 1]).erase (c.mem.last + 1) ∧ c.mem.last + 1 ≤ c'.views.vRel) ∨
    (∃ ts ∈ c.prom, c.mem.get? ts = some { loc := l, val := v, tid } ∧ c.views.vwOld < ts ∧
      c'.mem = c.mem ∧ c'.prom = c.prom.erase ts ∧ ts ≤ c'.views.vRel) := by
  have hrr : (StoreKind.rel == StoreKind.rel) = true := by decide
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
      obtain ⟨hw, hb, -⟩ := hc
      have hw' := msg_eq_of_beq (by simp only [Bool.and_eq_true]; exact hw)
      subst hw'
      simp only [decide_eq_true_eq, hk, hrr, ↓reduceIte] at hb
      refine ⟨t, ht, hg, by omega_t, rfl, rfl, ?_⟩
      simp only [afterWrite, hk, hrr, ↓reduceIte]
      omega_t
  · left
    generalize hap : c.mem.append { loc := l, val := v, tid } = ap at h
    obtain ⟨mem', t⟩ := ap
    have e1 : mem' = (c.mem.append { loc := l, val := v, tid }).1 := by rw [hap]
    have e2 : t = c.mem.last + 1 := by rw [← Memory.append_time c.mem { loc := l, val := v, tid }, hap]
    subst e1 e2
    simp only at h
    rw [List.mem_ite_nil_right, List.mem_singleton] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨rfl, rfl, ?_⟩
    simp only [afterWrite, hk, hrr, ↓reduceIte]
    omega_t

end Write

/-! ## Instruction-level forms -/

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- The resulting thread's `vRel` is the tree run's (`finishInstr` changes only
`vCAP`). -/
theorem stepOne_vRel {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ c', .ok (o.thread.st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree ∧
      o.mem = c'.mem ∧ o.thread.prom = c'.prom ∧ o.thread.views.vRel = c'.views.vRel ∧
      o.thread.views.vwNew = c'.views.vwNew ∧ o.thread.views.vwOld = c'.views.vwOld := by
  obtain ⟨tree', c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree' = tree := Option.some.inj (hex'.symm.trans hex)
  exact ⟨c', hr, hm, hp, by have := congrArg Views.vRel hv; exact this,
    by have := congrArg Views.vwNew hv; exact this, by have := congrArg Views.vwOld hv; exact this⟩

/-- A `done` instruction leaves `vRel` alone. -/
theorem spec_done_vRel {s : I.State} (hex : I.exec t.st = some (.done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.views.vRel = t.views.vRel := by
  obtain ⟨c', hr, -, -, hv, -⟩ := stepOne_vRel A tid hex hs ho
  obtain ⟨-, rfl⟩ := run_done A tid _ hr
  exact hv

/-- **Fact 1, instruction level: a release store**: an append at `|M| + 1`
(raising `vRel` to it), or the fulfilment of a promise above `vwOld` (raising
`vRel` to it). -/
theorem spec_store_rel {k : StoreKind} {l : Loc} {v : Val} {s : I.State} (hk : A.storeKind k = .rel)
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.st = s ∧
    ((o.mem = (mem.append { loc := l, val := v, tid }).1 ∧
      o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧ mem.last + 1 ≤ o.thread.views.vRel) ∨
    (∃ ts ∈ t.prom, mem.get? ts = some { loc := l, val := v, tid } ∧ t.views.vwOld < ts ∧
      o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ ts ≤ o.thread.views.vRel)) := by
  obtain ⟨c', hr, hm, hp, hv, -⟩ := stepOne_vRel A tid hex hs ho
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at hr
  obtain ⟨c1, h1, h⟩ := hr
  simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hst, rfl⟩ := h
  refine ⟨hst, ?_⟩
  rcases mem_writeSuccs_rel A tid _ hk h1 with ⟨e1, e2, e3⟩ | ⟨ts, hts, e1, e2, e3, e4, e5⟩
  · exact .inl ⟨hm.trans e1, hp.trans e2, hv ▸ e3⟩
  · exact .inr ⟨ts, hts, e1, e2, hm.trans e3, hp.trans e4, hv ▸ e5⟩

/-- **Facts 2 and 3, instruction level: an acquire RMW** (no fence around it)
fulfils no promise at or below the thread's `vRel`, and leaves `vwNew` at
least `vRel`. -/
theorem spec_rmw_acq (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hk : A.loadKind (A.rmwKind k).loadKind = .acq)
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    t.views.vRel ≤ o.thread.views.vwNew ∧ ∀ ts ∈ t.prom, ts ∉ o.thread.prom → t.views.vRel < ts := by
  obtain ⟨c', hr, -, hp, -, hv, -⟩ := stepOne_vRel A tid hex hs ho
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  obtain ⟨tr', old', hx', -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  have h1 : t.views.vRel ≤ (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) (A.rmwKind k).loadKind false l
      false tr old).views.vwNew := readNext_acq_vwNew (c := ctx0 tid t mem) A _ hk
  have hw : (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) (A.rmwKind k).loadKind false l false tr
      old).WOrd c' := by
    simp only at h
    split at h
    · simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact .refl _
    · rw [List.mem_flatMap] at h
      obtain ⟨c3, hc3, h⟩ := h
      simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact (writeSuccs_word A tid _ hc3).trans (Ctx.WOrd.rmwPost A c3 k false l)
  refine ⟨hv ▸ Nat.le_trans h1 hw.vwNew, fun ts hts hn => ?_⟩
  rw [hp] at hn
  exact Nat.lt_of_le_of_lt h1 (hw.prom ts (by rw [readNext_prom]; exact hts) hn)

end Spec

/-! ## Dead promises stay dead -/

/-- Promise `p` of `t` is dead against `mem` through `vwNew` or through its
location's `coh` (two thirds of `Thread.hasDeadPromise`). -/
def DeadW (t : Thread I) (mem : Memory) (p : Time) : Prop :=
  p ∈ t.prom ∧ (p ≤ t.views.vwNew ∨ ∃ w, mem.get? p = some w ∧ p ≤ t.views.getCoh w.loc)

/-- **A dead promise stays dead** across any instruction step. -/
theorem deadW_step (A : Arch) {t : Thread I} {tid : Nat} {mem : Memory} {outs : List (Except String (Outcome I))}
    {o : Outcome I} (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) {p : Time}
    (h : DeadW t mem p) : DeadW o.thread o.mem p := by
  obtain ⟨hp, hd⟩ := h
  obtain ⟨-, hcoh, hpre, hful⟩ := stepOne_dord A hs ho
  obtain ⟨hvw, hwful⟩ := stepOne_word A hs ho
  have hin : p ∈ o.thread.prom := by
    refine Classical.byContradiction fun hn => ?_
    rcases hd with hd | ⟨w, hw, hd⟩
    · exact absurd (hwful p hp hn) (by omega_t)
    · exact absurd ((hful p hp hn).2 w hw) (by omega_t)
  refine ⟨hin, ?_⟩
  rcases hd with hd | ⟨w, hw, hd⟩
  · exact .inl (Nat.le_trans hd hvw)
  · exact .inr ⟨w, by rw [hpre.get? (mem.last_le_of_get?_eq_some hw)]; exact hw, Nat.le_trans hd (hcoh _)⟩

/-- A thread with a dead promise never empties its promise set. -/
theorem deadW_run {A : Arch} {tid : Nat} : ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q →
    ∀ ts, DeadW p.1 p.2 ts → q.1.prom ≠ [] := by
  intro n p q h
  induction h with
  | refl => intro ts hd he; have := hd.1; rw [he] at this; exact absurd this (by simp)
  | step hs _ ih =>
    intro ts hd
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    exact ih ts (deadW_step A hs ho hd)

end Kraken.Promising.Live.LoopFacts

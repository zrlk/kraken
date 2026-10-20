/-
**Stage 3: a load-then-store with outstanding
promises, and its replay against a larger memory** (ISA-neutral; the tree
`load k false l fun v => store k' false l (g v) fun _ => done (f v)`, e.g. an
unlocked x86 `incl (sym)`). Generic beside `LiveSemShape`; the
promise-free shape is `Ticket2X64Step.spec_ldst`.

- `spec_ldst_p`: every outcome reads some `v` at `ts`, at or after every
  message of `l` the thread's coherence view covers (`writeIn`), and then
  appends `g v` or fulfils an outstanding promise of `⟨l, g v, tid⟩` above
  the coherence view; for a thread without a forwarding entry of `l` that
  promise also lies above `ts` (the read raises the view to `ts`).
- `replay_ldst`: an outcome that does not append replays against any larger
  memory, for a thread whose views are at most the smaller memory's `|M|`.
-/
import Kraken.Promising.LiveSemShape

namespace Kraken.Promising.Live.X64Sem2Shape

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-- A read at `ts` with no write to `l` in `(ts, b]` is at or after every
message of `l` (or the initial value) up to `b`. -/
theorem le_of_writeIn {mem : Memory} {l : Loc} {ts b : Time} (hw : mem.writeIn l ts b = false) {tsr : Time}
    {r : Val} (hb : tsr ≤ b) (hr : mem.read? l tsr = some r) : tsr ≤ ts := by
  apply Classical.byContradiction
  intro hlt
  rcases mem.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw', hl, -⟩
  · omega_t
  · have : mem.writeIn l ts b = true := (mem.writeIn_iff l ts b).mpr ⟨tsr, w, by omega_t, hb, hw', hl⟩
    rw [hw] at this; cases this

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A load-then-store, with any promise set**: a read at `ts`, at or after
every message of `l` within the coherence view, then an append or the
fulfilment of a promise above the view (and above `ts` without a forwarding
entry of `l`). -/
theorem spec_ldst_p {k : LoadKind} {k' : StoreKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .store k' false l (g v) fun _ => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧
      (∀ tsr r, tsr ≤ t.views.getCoh l → mem.read? l tsr = some r → tsr ≤ ts) ∧
      ((o.mem = (mem.append { loc := l, val := g v, tid }).1 ∧
        o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1) ∧
        ((A.storeKind k' == .nt) = false → mem.last + 1 ≤ o.thread.views.vwOld)) ∨
      (∃ tsp ∈ t.prom, mem.get? tsp = some { loc := l, val := g v, tid } ∧
        (t.views.getFwd l = none → ts < tsp) ∧ t.views.getCoh l < tsp ∧
        ((A.storeKind k' == .rel) = true → t.views.vwOld < tsp) ∧ o.mem = mem ∧
        o.thread.prom = t.prom.erase tsp ∧ t.views.vwOld ≤ o.thread.views.vwOld)) := by
  obtain ⟨c', hr, hm, hp, hv⟩ := stepOne_outV A tid hex hs ho
  rw [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  obtain ⟨ts', v', hx', hle, hrd, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at h
  obtain ⟨c2, h2, h⟩ := h
  simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hst, rfl⟩ := h
  refine ⟨ts, v, hst, hrd, fun tsr r hb hr => le_of_writeIn hw (Nat.le_trans hb (Nat.le_max_right _ _)) hr, ?_⟩
  have hcoh1 : t.views.getCoh l ≤
      (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) k false l false ts v).views.getCoh l :=
    Views.getCoh_le_setCoh _ _ _ _
  have hts1 : t.views.getFwd l = none →
      ts ≤ (readNext A (instrViews t (I.deps t.st)) (ctx0 tid t mem) k false l false ts v).views.getCoh l := by
    intro hn
    show ts ≤ (t.views.setCoh l _).getCoh l
    rw [Views.getCoh_setCoh, ite_eq_left rfl]
    have : readView A (A.loadKind k) (t.views.getFwd l) ts = ts := by rw [hn]; rfl
    show ts ≤ max (t.views.getCoh l) (max (readPre A _ _ k) (readView A (A.loadKind k) (t.views.getFwd l) ts))
    rw [this]; omega_t
  rcases SemShape.mem_writeSuccs A tid _ h2 with ⟨e1, e2, e3, -, -⟩ | ⟨tsp, htsp, e1, e2, e3, e4, e5, e6, -⟩
  · exact .inl ⟨hm.trans e1, hp.trans e2, fun hk => hv ▸ e3 hk⟩
  · exact .inr ⟨tsp, htsp, e1, fun hn => Nat.lt_of_le_of_lt (hts1 hn) e2, Nat.lt_of_le_of_lt hcoh1 e2, e3,
      hm.trans e4, hp.trans e5, hv ▸ e6⟩

end Spec

/-! ## Replay against a larger memory -/

section Replay

variable (A : Arch) (tid : Nat) {t : Thread I} {mem0 mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A load-then-store outcome that does not append replays against a larger
memory.** -/
theorem replay_ldst (hp : mem0.Prefix mem) (hb : t.Bnd mem0.last) (hs : stepOne A t tid mem0 = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem = mem0) {k : LoadKind} {k' : StoreKind} {l : Loc} {g : Val → Val}
    {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .store k' false l (g v) fun _ => .done (f v))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr hm' => ?_
  have hiv := instrViews_le hb.regs (I.deps t.st)
  have hv := hb.views.le
  have hbd : max (readPre A (instrViews t (I.deps t.st)) (ctx0 tid t mem0) k) ((ctx0 tid t mem0).views.getCoh l) ≤
      (ctx0 tid t mem0).mem.last := by
    have := hiv.addrR; have := hv.vrNew; have := hv.vRel; have := hv.coh l
    simp only [readPre]; split <;> omega_t
  rw [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  have hc1 : c1.mem = mem0 := by
    obtain ⟨ts', v', hxe, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨-, -, rfl⟩ := hxe
    rfl
  dsimp only at h
  rw [runTree] at h
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap] at h
  obtain ⟨c2, h2, h⟩ := h
  rw [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h3, h4⟩ := h
  have hx' := readSuccs_replay A _ hp hx hbd
  have h2' := writeSuccs_replay A tid _ (hc1 ▸ hp) h2 (by rw [hc1, ← h4]; exact hm')
  rw [runTree, List.mem_flatMap]
  refine ⟨(ts, v, { c1 with mem := mem }), hx', ?_⟩
  show Except.ok (st, { c0' with mem := mem }) ∈ runTree A tid _ { c1 with mem := mem } (.store k' false l (g v) _)
  rw [runTree]
  simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap]
  refine ⟨{ c2 with mem := mem }, h2', ?_⟩
  rw [runTree, List.mem_singleton, h3, h4]

end Replay

end Kraken.Promising.Live.X64Sem2Shape

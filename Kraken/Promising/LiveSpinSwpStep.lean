/-
**Stage 3: promise-free write steps with their
coherence views, and "a swap reads the last write".** ISA-neutral.
`atomic_lastWrite_own` is `LiveTsoRmw.rmw_reads_last` at coherence bound
`b`, and `spec_store_coh` is `TsoRmw.spec_store_coh` (the same statement;
both names are kept, so with both namespaces open write
`TsoRmw.spec_store_coh`). The RMW lemmas here are for `A.rmwFence = false`;
`LiveTsoRmw`'s are their `rmwFence = true` twins (the `runTree` shapes
differ by the fences).

A failing `SWPA` still writes, so the SWP spinlock proofs need every swap to
read the *last* write of the lock. RMW atomicity (`Memory.atomic`) excludes
other threads' writes between the read and the write; the read's coherence
condition (`writeIn … (getCoh l) = false`) excludes the thread's own writes,
provided they are all at or below its coherence view (`OwnLe`). A write
raises the writer's coherence view of its location to the new timestamp, so
`OwnLe` is kept.

- `writeSuccs_coh`, `spec_store_coh`: a promise-free write sets the
  coherence view of its location to at least `|M| + 1` and lowers none.
- `OwnLe` and its preservation under appends (`OwnLe.append_other`,
  `OwnLe.append_self`).
- `atomic_lastWrite_own`: an atomic read with no own write above the
  coherence bound reads the last write.
- `spec_swp`: an always-writing RMW by a promise-free thread with `OwnLe`
  reads the final value, appends, and raises its coherence views.
-/
import Kraken.Promising.LiveTsoRmw

namespace Kraken.Promising.Live.SpinSwpStep

open Kraken.Promising Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Own writes at or below a bound -/

/-- Every write of thread `tid` to `l` in `mem` is at or below `b`. -/
def OwnLe (mem : Memory) (tid : Nat) (l : Loc) (b : Time) : Prop :=
  ∀ ts w, mem.get? ts = some w → w.loc = l → w.tid = tid → ts ≤ b

theorem OwnLe.mono {mem : Memory} {tid : Nat} {l : Loc} {b b' : Time} (h : OwnLe mem tid l b) (hb : b ≤ b') :
    OwnLe mem tid l b' :=
  fun ts w hw hl ht => Nat.le_trans (h ts w hw hl ht) hb

/-- An append of another location's or another thread's message keeps `OwnLe`. -/
theorem OwnLe.append_other {mem : Memory} {tid : Nat} {l : Loc} {b : Time} (h : OwnLe mem tid l b) {w : Msg}
    (hw : w.loc ≠ l ∨ w.tid ≠ tid) : OwnLe (mem.append w).1 tid l b := by
  intro ts w' h' hl ht
  rcases mem.get?_append_eq_some w h' with ⟨-, h'⟩ | ⟨-, rfl⟩
  · exact h ts w' h' hl ht
  · rcases hw with hw | hw
    · exact absurd hl hw
    · exact absurd ht hw

/-- An own append with the bound raised to the new timestamp keeps `OwnLe`. -/
theorem OwnLe.append_self {mem : Memory} {tid : Nat} {l : Loc} {b b' : Time} (h : OwnLe mem tid l b)
    (hb : b ≤ b') (hl : mem.last + 1 ≤ b') (w : Msg) : OwnLe (mem.append w).1 tid l b' := by
  intro ts w' h' hl' ht
  rcases mem.get?_append_eq_some w h' with ⟨-, h'⟩ | ⟨e, -⟩
  · exact Nat.le_trans (h ts w' h' hl' ht) hb
  · omega_t

/-- **An atomic read with no own write above the coherence bound reads the
last write.** -/
theorem atomic_lastWrite_own (m : Memory) (l : Loc) (tid : Nat) {tr b : Time} {v : Val}
    (hr : m.read? l tr = some v) (h : m.atomic l tid tr (m.last + 1) = true) (hw : m.writeIn l tr b = false)
    (hown : OwnLe m tid l b) : tr = m.lastWrite l ∧ v = m.finalVal l :=
  TsoRmw.rmw_reads_last m l tid hr hw (Nat.le_refl b) hown h

/-! ## Writes and coherence views -/

section Shapes

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem getCoh_congr {v v' : Views} (h : v'.coh = v.coh) (l : Loc) : v'.getCoh l = v.getCoh l := by
  unfold Views.getCoh; rw [h]

/-- A promise-free write's coherence views: those of `setCoh l (|M| + 1)`. -/
theorem writeSuccs_coh {c c' : Ctx} (hp : c.prom = []) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) (l' : Loc) :
    c'.views.getCoh l' = (c.views.setCoh l (c.mem.last + 1)).getCoh l' := by
  simp only [writeSuccs, hp, List.filterMap_nil, List.nil_append, List.mem_ite_nil_right,
    List.mem_singleton] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem coh_setCoh_le (v : Views) (l : Loc) (t : View) (l' : Loc) : v.getCoh l' ≤ (v.setCoh l t).getCoh l' :=
  Views.getCoh_le_setCoh v l l' t

theorem coh_setCoh_self (v : Views) (l : Loc) (t : View) : t ≤ (v.setCoh l t).getCoh l := by
  rw [Views.getCoh_setCoh, ite_eq_left rfl]; exact Nat.le_max_right _ _

/-- A non-exclusive store raises the coherence view of its location to the
new timestamp and lowers none. -/
theorem run_store_coh {σ : Type} {c c' : Ctx} (hp : c.prom = []) {k : StoreKind} {l : Loc} {v : Val} {s st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.store k false l v fun _ => .done s)) :
    (∀ l', c.views.getCoh l' ≤ c'.views.getCoh l') ∧ c.mem.last + 1 ≤ c'.views.getCoh l := by
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at h
  obtain ⟨c1, h1, h⟩ := h
  obtain ⟨-, rfl⟩ := run_done A tid iv h
  have hc := writeSuccs_coh A tid _ hp h1
  exact ⟨fun l' => by rw [hc]; exact coh_setCoh_le _ _ _ _, by rw [hc]; exact coh_setCoh_self _ _ _⟩

/-- An always-writing RMW: the read's conditions, the atomic append, and the
coherence views (raised at `l` to the new timestamp, none lowered). -/
theorem run_rmw_coh {σ : Type} (hA : A.rmwFence = false) {c c' : Ctx} (hp : c.prom = []) {k : RmwKind}
    {l : Loc} {g : Val → Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ tr old, st = f old ∧ c.mem.read? l tr = some old ∧
      c.mem.writeIn l tr (max (readPre A iv c (A.rmwKind k).loadKind) (c.views.getCoh l)) = false ∧
      c.mem.atomic l tid tr (c.mem.last + 1) = true ∧
      c'.mem = (c.mem.append { loc := l, val := g old, tid }).1 ∧ c'.prom = [] ∧
      (∀ l', c.views.getCoh l' ≤ c'.views.getCoh l') ∧ c.mem.last + 1 ≤ c'.views.getCoh l := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap, List.mem_singleton,
    Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨tr, old, c1⟩, hx, c2, h2, hst, hc⟩ := h
  obtain ⟨tr', old', hx', -, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  obtain ⟨hm, hpr, hat⟩ := writeSuccs_nil A tid iv (by rw [readNext_prom]; exact hp) (.inl h2)
  have hco := writeSuccs_coh A tid iv (by rw [readNext_prom]; exact hp) h2
  rw [readNext_mem] at hm hat hco
  obtain ⟨-, ha2⟩ := hat _ rfl
  have key : ∀ l', c'.views.getCoh l' = c2.views.getCoh l' ∧ c'.mem = c2.mem ∧ c'.prom = c2.prom := by
    intro l'
    subst hc
    cases (A.rmwKind k == RmwKind.acqRel && !false) <;> exact ⟨rfl, rfl, rfl⟩
  refine ⟨tr, old, by rw [← hst], hr, hw, ha2, (key l).2.1.trans hm, (key l).2.2.trans hpr, fun l' => ?_, ?_⟩
  · rw [(key l').1, hco]
    exact Nat.le_trans (readNext_getCoh A iv _ _ _ _ _ _ _ l') (coh_setCoh_le _ _ _ _)
  · rw [(key l).1, hco]; exact coh_setCoh_self _ _ _

end Shapes

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A store by a promise-free thread**: the coherence view of its location
reaches the new timestamp, and none drops. -/
theorem spec_store_coh {k : StoreKind} {l : Loc} {v : Val} {s : I.State} (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    (∀ l', t.views.getCoh l' ≤ o.thread.views.getCoh l') ∧ mem.last + 1 ≤ o.thread.views.getCoh l :=
  TsoRmw.spec_store_coh A tid hp0 hex hs ho

/-- **An always-writing RMW by a promise-free thread whose own writes to `l`
are at or below its coherence view reads the final value of `l`**, appends
its write, and raises its coherence views. -/
theorem spec_swp (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) (hown : OwnLe mem tid l (t.views.getCoh l)) :
    o.thread.st = f (mem.finalVal l) ∧ o.mem = (mem.append { loc := l, val := g (mem.finalVal l), tid }).1 ∧
      o.thread.prom = [] ∧ (∀ l', t.views.getCoh l' ≤ o.thread.views.getCoh l') ∧
      mem.last + 1 ≤ o.thread.views.getCoh l := by
  obtain ⟨st, c', hr, hm, hst, hp, hc, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨tr, old, rfl, hrd, hw, hat, hm', hp', h1, h2⟩ := run_rmw_coh A tid _ hA hp0 hr
  obtain ⟨-, rfl⟩ := atomic_lastWrite_own mem l tid hrd hat hw (hown.mono (Nat.le_max_right _ _))
  exact ⟨hst, hm.trans hm', hp.trans hp', fun l' => by rw [getCoh_congr hc]; exact h1 l',
    by rw [getCoh_congr hc]; exact h2⟩

end Spec

end Kraken.Promising.Live.SpinSwpStep

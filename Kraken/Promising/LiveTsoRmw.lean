/-
**Stage 3: promise-free steps of a fencing RMW**
(`A.rmwFence = true`, `Arch.tso`: x86's `lock`-prefixed instructions and
`xchg`). ISA-neutral and lock-agnostic.

`runTree` wraps an RMW in `fence .sy` before its read and after its write
(or after its read, when the operation does not write). The fences change
views only (`vrNew`/`vwNew`), not memory, promises or coherence views, so
the outcome facts of `LiveTicketStep.run_rmw`/`LiveSpinStep.run_rmwo` (which
assume `A.rmwFence = false`) hold unchanged; this file proves them for
`rmwFence = true`:

- `run_rmw_tso`/`run_rmw_tso_exists`/`spec_rmw_tso`/`en_rmw_tso`: an RMW that
  always writes (`op = some ∘ g`: `lock xadd`, `xchg`);
- `run_rmwo_tso`/`run_rmwo_tso_exists`/`spec_rmwo_tso`/`en_rmwo_tso`: an RMW
  with an arbitrary operation `op : Val → Option Val` (`none`: no write, a
  failing `lock cmpxchg`).

The `rmwo` lemmas also give what liveness proofs need beyond the outcome:
the read is in the step's log (`ReadsAt`, for `MemFair`), coherence views
never drop, and a write's timestamp `|M| + 1` is in the writer's coherence
view of the location (so a thread's own messages stay at or below its view,
whence an RMW reads the last write: `rmw_reads_last`).

Also generic coherence facts for plain stores (`writeSuccs_coh`,
`spec_store_coh`), used with the same "own messages below the view"
invariant.
-/
import Kraken.Promising.LiveSpinStep

namespace Kraken.Promising.Live.TsoRmw

open Kraken.Promising Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SpinStep

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## Fences and writes: what they keep -/

theorem fence_mem (c : Ctx) (k : FenceKind) : (fenceStep c k).mem = c.mem := by
  cases k <;> rfl

theorem fence_prom (c : Ctx) (k : FenceKind) : (fenceStep c k).prom = c.prom := by
  cases k <;> rfl

theorem fence_getCoh (c : Ctx) (k : FenceKind) (l : Loc) :
    (fenceStep c k).views.getCoh l = c.views.getCoh l := by
  cases k <;> rfl

theorem fence_log (c : Ctx) (k : FenceKind) : c.log ⊆ (fenceStep c k).log := by
  cases k <;> exact fun _ h => List.mem_append_left _ h

/-- The context after an RMW's write (`rmwWrote`, and the acquire-release
view raise): memory, promises, coherence views and log unchanged. -/
theorem rmwPost_keeps (b : Bool) (c : Ctx) (l : Loc) :
    let c' : Ctx := if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }
    c'.mem = c.mem ∧ c'.prom = c.prom ∧ (∀ l', c'.views.getCoh l' = c.views.getCoh l') ∧ c'.log = c.log := by
  cases b <;> exact ⟨rfl, rfl, fun _ => rfl, rfl⟩

section Shapes

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A promise-free write's coherence views**: none drops, and the write's
location is at least the appended timestamp `|M| + 1`. -/
theorem writeSuccs_coh {c c' : Ctx} (hp : c.prom = []) {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val}
    {tr : Option Time} {extra : View} (h : c' ∈ writeSuccs A tid iv c k xcl l v tr extra) :
    (∀ l', c.views.getCoh l' ≤ c'.views.getCoh l') ∧ c.mem.last + 1 ≤ c'.views.getCoh l ∧ c.log ⊆ c'.log := by
  simp only [writeSuccs, hp, List.filterMap_nil, List.nil_append, List.mem_ite_nil_right,
    List.mem_singleton] at h
  obtain ⟨-, rfl⟩ := h
  refine ⟨fun l' => Views.getCoh_le_setCoh _ _ _ _, ?_, fun _ h => List.mem_append_left _ h⟩
  show c.mem.last + 1 ≤ (c.views.setCoh l _).getCoh l
  rw [Views.getCoh_setCoh, ite_eq_left rfl, Memory.append_time]
  omega_t

/-- **An RMW with an arbitrary operation under `rmwFence`**: it reads some
`old` at `tr` (with the read's conditions, the pre-view taken after the
leading `fence .sy`; the read is logged); coherence views never drop; then
`op old = none` (memory unchanged) or `op old = some new` (an atomic write of
`new` appended at `|M| + 1`, which the coherence view of `l` then covers). -/
theorem run_rmwo_tso {σ : Type} (hA : A.rmwFence = true) {c c' : Ctx} (hp : c.prom = []) {k : RmwKind}
    {l : Loc} {op : Val → Option Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v))) :
    ∃ tr old, st = f old ∧ tr ≤ c.mem.last ∧ c.mem.read? l tr = some old ∧
      c.mem.writeIn l tr (max (readPre A iv (fenceStep c .sy) (A.rmwKind k).loadKind) (c.views.getCoh l)) = false ∧
      c'.prom = [] ∧ (∃ ν, TraceEv.read l tr old ν ∈ c'.log) ∧
      (∀ l', c.views.getCoh l' ≤ c'.views.getCoh l') ∧
      ((op old = none ∧ c'.mem = c.mem) ∨
       (∃ new, op old = some new ∧ c.mem.atomic l tid tr (c.mem.last + 1) = true ∧
         c'.mem = (c.mem.append { loc := l, val := new, tid }).1 ∧ c.mem.last + 1 ≤ c'.views.getCoh l)) := by
  simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap] at h
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := h
  obtain ⟨tr', old', hx', hle, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  rw [fence_mem] at hle hr hw
  rw [fence_getCoh] at hw
  have hp0 : (fenceStep c .sy).prom = [] := by rw [fence_prom]; exact hp
  have hcoh1 : ∀ l', c.views.getCoh l' ≤
      (readNext A iv (fenceStep c .sy) (A.rmwKind k).loadKind false l false tr old).views.getCoh l' :=
    fun l' => by rw [← fence_getCoh c .sy l']; exact readNext_getCoh A iv _ _ _ _ _ _ _ l'
  have hlog1 : ∃ ν, TraceEv.read l tr old ν ∈
      (readNext A iv (fenceStep c .sy) (A.rmwKind k).loadKind false l false tr old).log :=
    ⟨_, List.mem_append_right _ (List.mem_singleton_self _)⟩
  refine ⟨tr, old, ?_⟩
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨rfl, rfl⟩ := run_done A tid iv h
    obtain ⟨ν, hν⟩ := hlog1
    refine ⟨rfl, hle, hr, hw, by rw [fence_prom]; simp [readNext, hp0], ⟨ν, fence_log _ _ hν⟩, fun l' => by rw [fence_getCoh]; exact hcoh1 l',
      .inl ⟨rfl, by rw [fence_mem, readNext_mem, fence_mem]⟩⟩
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨rfl, hc⟩ := run_done A tid iv h
    obtain ⟨hm, hpr, hat⟩ := writeSuccs_nil A tid iv (by rw [readNext_prom]; exact hp0) (.inl h2)
    obtain ⟨hco, hlast, hlg⟩ := writeSuccs_coh A tid iv (by rw [readNext_prom]; exact hp0) h2
    rw [readNext_mem, fence_mem] at hm hat hlast
    obtain ⟨-, ha2⟩ := hat _ rfl
    subst hc
    obtain ⟨hm', hp', hc', hl'⟩ := rmwPost_keeps (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    obtain ⟨ν, hν⟩ := hlog1
    refine ⟨rfl, hle, hr, hw, by rw [fence_prom]; exact hp'.trans hpr, ⟨ν, ?_⟩,
      fun l' => ?_, .inr ⟨new, rfl, ha2, by rw [fence_mem]; exact hm'.trans hm, ?_⟩⟩
    · apply fence_log; rw [hl']; exact hlg hν
    · rw [fence_getCoh, hc']; exact Nat.le_trans (hcoh1 l') (hco l')
    · rw [fence_getCoh, hc']; exact hlast

/-- An RMW under `rmwFence` can read the last write (and write, if its
operation does). -/
theorem run_rmwo_tso_exists {σ : Type} (hA : A.rmwFence = true) {c : Ctx} (hp : c.prom = []) (hb : c.Bnd)
    (hiv : iv.Le c.mem.last) (k : RmwKind) (l : Loc) (op : Val → Option Val) (f : Val → σ) :
    ∃ c', .ok (f (c.mem.finalVal l), c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v)) := by
  let c0 := fenceStep c .sy
  have hb0 : c0.Bnd := fenceStep_bnd hb .sy
  have hm0 : c0.mem = c.mem := fence_mem c .sy
  have hp0 : c0.prom = [] := by rw [fence_prom]; exact hp
  rw [← hm0] at hiv ⊢
  let kl := (A.rmwKind k).loadKind
  let c1 := readNext A iv c0 kl false l false (c0.mem.lastWrite l) (c0.mem.finalVal l)
  have hx : (c0.mem.lastWrite l, c0.mem.finalVal l, c1) ∈ readSuccs A iv c0 kl false l false := by
    rw [mem_readSuccs]
    refine ⟨_, _, rfl, c0.mem.lastWrite_le l, c0.mem.read?_lastWrite l, c0.mem.writeIn_lastWrite l _, ?_⟩
    rw [hp0]; rfl
  cases hop : op (c0.mem.finalVal l) with
  | none =>
    refine ⟨fenceStep c1 .sy, ?_⟩
    simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap]
    exact ⟨_, hx, by simp only [hop]; exact run_done_exists A tid iv _ _⟩
  | some new =>
    obtain ⟨c2, hw⟩ := readLast_writeSuccs_exists A tid iv hp0 hb0 hiv k l new
    simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap]
    exact ⟨_, _, hx, by simp only [hop, List.mem_flatMap]; exact ⟨c2, hw, run_done_exists A tid iv _ _⟩⟩

/-- An always-writing RMW under `rmwFence`: it reads some `old` at `tr`,
atomic with its write of `g old` appended at `|M| + 1` (the TSO twin of
`LiveTicketStep.run_rmw`). -/
theorem run_rmw_tso {σ : Type} (hA : A.rmwFence = true) {c c' : Ctx} (hp : c.prom = []) {k : RmwKind} {l : Loc}
    {g : Val → Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ tr old, st = f old ∧ c.mem.read? l tr = some old ∧ c.mem.atomic l tid tr (c.mem.last + 1) = true ∧
      c'.mem = (c.mem.append { loc := l, val := g old, tid }).1 ∧ c'.prom = [] := by
  obtain ⟨tr, old, hst, -, hr, -, hp', -, -, hcase⟩ := run_rmwo_tso A tid iv hA hp h
  rcases hcase with ⟨h1, -⟩ | ⟨new, h1, h2, h3, -⟩
  · cases h1
  · cases h1; exact ⟨tr, old, hst, hr, h2, h3, hp'⟩

/-- An always-writing RMW under `rmwFence` can read the last write and
append. -/
theorem run_rmw_tso_exists {σ : Type} (hA : A.rmwFence = true) {c : Ctx} (hp : c.prom = []) (hb : c.Bnd)
    (hiv : iv.Le c.mem.last) (k : RmwKind) (l : Loc) (g : Val → Val) (f : Val → σ) :
    ∃ c', .ok (f (c.mem.finalVal l), c') ∈
      runTree A tid iv c (.rmw k false l (fun old => some (g old)) fun v => .done (f v)) :=
  run_rmwo_tso_exists A tid iv hA hp hb hiv k l _ f

end Shapes

/-! ## Reading the last write -/

/-- **An atomic RMW reads the last write** when the thread's own messages to
`l` are at or below its coherence view (which bounds the read): a later own
write would be skipped by the read's coherence bound, a later write of
another thread by atomicity. -/
theorem rmw_reads_last (m : Memory) (l : Loc) (tid : Nat) {tr bound coh : Time} {v : Val}
    (hr : m.read? l tr = some v) (hw : m.writeIn l tr bound = false) (hcb : coh ≤ bound)
    (hown : ∀ ts w, m.get? ts = some w → w.loc = l → w.tid = tid → ts ≤ coh)
    (hat : m.atomic l tid tr (m.last + 1) = true) :
    tr = m.lastWrite l ∧ v = m.finalVal l := by
  have hlw := m.read?_lastWrite l
  have htr : tr = m.lastWrite l := by
    rcases Nat.lt_trichotomy tr (m.lastWrite l) with hlt | heq | hgt
    · obtain ⟨w, hw', hl⟩ := m.get?_lastWriteBelow l m.last (by unfold Memory.lastWrite at hlt; omega_t)
      by_cases hb : m.lastWrite l ≤ bound
      · rw [m.writeIn_of_lt_lastWrite l hlt hb] at hw; cases hw
      · have hne : w.tid ≠ tid := fun e => hb (Nat.le_trans (hown _ w hw' hl e) hcb)
        exact absurd (forall_of_atomic m l tid tr _ hr hat _ w hlt
          (Nat.lt_succ_of_le (m.lastWrite_le l)) hw' hl) hne
    · exact heq
    · rcases m.read?_eq_some hr with ⟨rfl, -⟩ | ⟨w, hw', hl, -⟩
      · exact absurd hgt (Nat.not_lt_zero _)
      · exact absurd hl (m.not_write_of_lastWrite_lt l hgt hw')
  subst htr
  rw [hlw] at hr
  exact ⟨rfl, (Option.some.inj hr).symm⟩

/-! ## Instruction steps -/

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **An RMW with an arbitrary operation under `rmwFence`** by a
promise-free thread: it reads a value of the location (the last write's, if
the coherence view is at or past it, or if the operation writes and the
thread's own messages to `l` are at or below its coherence view); the read is
logged; coherence views never drop; no write, or an atomic write appended,
whose timestamp the coherence view of `l` then covers. -/
theorem spec_rmwo_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧
      (mem.lastWrite l ≤ t.views.getCoh l → old = mem.finalVal l) ∧ o.thread.prom = [] ∧
      (∃ ν, TraceEv.read l tr old ν ∈ o.log) ∧ (∀ l', t.views.getCoh l' ≤ o.thread.views.getCoh l') ∧
      ((op old = none ∧ o.mem = mem) ∨
       (∃ new, op old = some new ∧ mem.atomic l tid tr (mem.last + 1) = true ∧
         o.mem = (mem.append { loc := l, val := new, tid }).1 ∧ mem.last + 1 ≤ o.thread.views.getCoh l ∧
         ((∀ ts w, mem.get? ts = some w → w.loc = l → w.tid = tid → ts ≤ t.views.getCoh l) →
           old = mem.finalVal l))) := by
  obtain ⟨st, c', hr, hm, hst, hp, hc, hlog⟩ := stepOne_out A tid hex hs ho
  obtain ⟨tr, old, rfl, hle, hrd, hw, hp', hl, hco, hcase⟩ := run_rmwo_tso A tid _ hA hp0 hr
  have hc' : ∀ l', o.thread.views.getCoh l' = c'.views.getCoh l' := fun l' => by unfold Views.getCoh; rw [hc]
  refine ⟨tr, old, hst, hrd, fun hc' => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc' (Nat.le_max_right _ _))).2, hp.trans hp', hlog ▸ hl, fun l' => (hc' l') ▸ hco l', ?_⟩
  rcases hcase with ⟨h1, h2⟩ | ⟨new, h1, h2, h3, h4⟩
  · exact .inl ⟨h1, hm.trans h2⟩
  · exact .inr ⟨new, h1, h2, hm.trans h3, (hc' l) ▸ h4, fun hown =>
      (rmw_reads_last mem l tid hrd hw (Nat.le_max_right _ _) hown h2).2⟩

theorem en_rmwo_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨c', hr⟩ := run_rmwo_tso_exists A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem) hA hp0
    ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ (instrViews_le hb.regs _) k l op f
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex hr
  obtain ⟨-, -, -, -, -, -, hp', -⟩ := run_rmwo_tso A tid _ hA hp0 hr
  exact ⟨outs, o, h1, h2, h3.trans hp'⟩

/-- An always-writing RMW under `rmwFence` by a promise-free thread (the TSO
twin of `LiveTicketStep.spec_rmw`). -/
theorem spec_rmw_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧ mem.atomic l tid tr (mem.last + 1) = true ∧
      o.mem = (mem.append { loc := l, val := g old, tid }).1 ∧ o.thread.prom = [] := by
  obtain ⟨st, c', hr, hm, hst, hp, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨tr, old, rfl, hrd, hat, hm', hp'⟩ := run_rmw_tso A tid _ hA hp0 hr
  exact ⟨tr, old, hst, hrd, hat, hm.trans hm', hp.trans hp'⟩

theorem en_rmw_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] :=
  en_rmwo_tso A tid hA hp0 hb hex

/-- **A store's coherence views** (any architecture): none drops, and the
stored location's covers the appended timestamp `|M| + 1`. -/
theorem spec_store_coh {k : StoreKind} {l : Loc} {v : Val} {s : I.State} (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    (∀ l', t.views.getCoh l' ≤ o.thread.views.getCoh l') ∧ mem.last + 1 ≤ o.thread.views.getCoh l := by
  obtain ⟨st, c', hr, -, -, -, hc, -⟩ := stepOne_out A tid hex hs ho
  have hc' : ∀ l', o.thread.views.getCoh l' = c'.views.getCoh l' := fun l' => by unfold Views.getCoh; rw [hc]
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at hr
  obtain ⟨c1, h1, h⟩ := hr
  simp only [List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨hco, hl, -⟩ := writeSuccs_coh A tid _ hp0 h1
  exact ⟨fun l' => (hc' l') ▸ hco l', (hc' l) ▸ hl⟩

end Spec

end Kraken.Promising.Live.TsoRmw

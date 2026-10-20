/-
**Stage 3: promise-free instruction steps for the
unlocked `incl` release, and forwarding.** ISA-neutral (generic beside
`LiveTicketStep`, `LiveSpinStep`, `LiveTsoRmw`).

- A *load-then-store* instruction to one location (the tree
  `load k false l fun v => store k' false l (g v) fun _ => done (f v)`, e.g.
  an unlocked x86 `incl (sym)`): every outcome reads some `v` (the last
  write's, if the coherence view is at or past it) and appends `g v`
  (`run_ldst`, `spec_ldst`), and some outcome exists (`run_ldst_exists`,
  `en_ldst`). Nothing is atomic: another thread's write may come between
  the read message and the appended one.
- Forwarding (`Views.getFwd`): a register-only step, a load, a store to
  another location and (under `rmwFence`) an RMW of another location keep a
  thread's forwarding entry of `l` (`spec_*_fwd`). A load whose location has
  no forwarding entry raises the coherence view of that location to the
  timestamp read (`spec_load_fwd`): so a thread that never wrote `l` and read
  the last write of `l` has a coherence view of `l` at that write.
-/
import Kraken.Promising.LiveTsoRmw
import Kraken.Promising.LiveSpinStep
import Kraken.Promising.SLR.EnvG.TicketX2Reach

namespace Kraken.Promising.Live.Ticket2X64Step

open Kraken.Promising Kraken.Promising.Live.TicketStep Kraken.Promising.Live.TsoRmw
open Kraken.Promising.SLR.EnvG.TicketX2 (writeSuccs_spec getFwd_of_fwdb vle_of_key fenceStep_fwdb)

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

section Shapes

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- **A load-then-store to one location**: it reads some `v` at `ts` (with
the read's conditions) and appends `g v`. -/
theorem run_ldst {σ : Type} {c c' : Ctx} (hp : c.prom = []) {k : LoadKind} {k' : StoreKind} {l : Loc}
    {g : Val → Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.load k false l fun v => .store k' false l (g v) fun _ => .done (f v))) :
    ∃ ts v, st = f v ∧ ts ≤ c.mem.last ∧ c.mem.read? l ts = some v ∧
      c.mem.writeIn l ts (max (readPre A iv c k) (c.views.getCoh l)) = false ∧
      c'.mem = (c.mem.append { loc := l, val := g v, tid }).1 ∧ c'.prom = [] := by
  simp only [runTree, List.mem_flatMap] at h
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := h
  obtain ⟨ts', v', hx', hle, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  have hp1 : (readNext A iv c k false l false ts v).prom = [] := by rw [readNext_prom]; exact hp
  have h' : .ok (st, c') ∈ runTree A tid iv (readNext A iv c k false l false ts v)
      (.store k' false l (g v) fun _ => .done (f v)) := by
    simp only [runTree]; exact h
  obtain ⟨rfl, hm, hpr⟩ := run_store A tid iv hp1 h'
  exact ⟨ts, v, rfl, hle, hr, hw, by rw [hm, readNext_mem], hpr⟩

/-- A load-then-store can read the last write and append. -/
theorem run_ldst_exists {σ : Type} {c : Ctx} (hp : c.prom = []) (hb : c.Bnd) (hiv : iv.Le c.mem.last)
    (k : LoadKind) (k' : StoreKind) (l : Loc) (g : Val → Val) (f : Val → σ) :
    ∃ c', .ok (f (c.mem.finalVal l), c') ∈
      runTree A tid iv c (.load k false l fun v => .store k' false l (g v) fun _ => .done (f v)) := by
  let c1 := readNext A iv c k false l false (c.mem.lastWrite l) (c.mem.finalVal l)
  have hx : (c.mem.lastWrite l, c.mem.finalVal l, c1) ∈ readSuccs A iv c k false l false := by
    rw [mem_readSuccs]
    refine ⟨_, _, rfl, c.mem.lastWrite_le l, c.mem.read?_lastWrite l, c.mem.writeIn_lastWrite l _, ?_⟩
    rw [hp]; rfl
  obtain ⟨hb1, -, hm1⟩ := readSuccs_bnd A iv hb hiv hx
  have hm1 : c1.mem = c.mem := hm1
  have hp1 : c1.prom = [] := by simp [c1, readNext, hp]
  obtain ⟨c2, h2⟩ := run_store_exists A tid iv hp1 (by rw [hm1]; exact hb1.views.le) (by rw [hm1]; exact hiv)
    k' l (g (c.mem.finalVal l)) (f (c.mem.finalVal l))
  refine ⟨c2, ?_⟩
  simp only [runTree, List.mem_flatMap]
  exact ⟨_, hx, by simpa only [runTree, List.mem_flatMap] using h2⟩

end Shapes

/-! ## Instruction steps -/

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **Every outcome of `stepOne` is a run of the tree**, with its coherence
views and forwarding entries (`stepOne_out` with `getFwd`). -/
theorem stepOne_out' {tree : EvTree I.State} (hex : I.exec t.st = some tree) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ st c', .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree ∧
      o.mem = c'.mem ∧ o.thread.st = st ∧ o.thread.prom = c'.prom ∧
      (∀ l, o.thread.views.getCoh l = c'.views.getCoh l) ∧ (∀ l, o.thread.views.getFwd l = c'.views.getFwd l) ∧
      o.log = c'.log := by
  obtain ⟨tree', c', hex', hr, hp, hv, hm, hl⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree' = tree := Option.some.inj (hex'.symm.trans hex)
  have hc := congrArg Views.coh hv
  simp only at hc
  exact ⟨_, c', hr, hm, rfl, hp, fun l => by unfold Views.getCoh; rw [hc], (vle_of_key hv).2, hl⟩

/-- A register-only step keeps the forwarding entries. -/
theorem spec_done_fwd {s : I.State} (hex : I.exec t.st = some (.done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) (l : Loc) : o.thread.views.getFwd l = t.views.getFwd l := by
  obtain ⟨st, c', hr, -, -, -, -, hf, -⟩ := stepOne_out' A tid hex hs ho
  obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) hr
  exact hf l

/-- **A load, with forwarding**: as `spec_load`; besides, no coherence view
drops, the forwarding entries are kept, and without a forwarding entry of
`l` the coherence view of `l` reaches the timestamp read. -/
theorem spec_load_fwd {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧
      (mem.lastWrite l ≤ t.views.getCoh l → v = mem.finalVal l) ∧
      (t.views.getFwd l = none → ts ≤ o.thread.views.getCoh l) ∧
      (∀ l', t.views.getCoh l' ≤ o.thread.views.getCoh l') ∧
      (∀ l', o.thread.views.getFwd l' = t.views.getFwd l') ∧
      o.mem = mem ∧ o.thread.prom = t.prom ∧ ∃ ν, TraceEv.read l ts v ν ∈ o.log := by
  obtain ⟨st, c', hr, hm, hst, hp, hc, hf, hlog⟩ := stepOne_out' A tid hex hs ho
  simp only [runTree, List.mem_flatMap] at hr
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := hr
  obtain ⟨ts', v', hx', hle, hrd, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  obtain ⟨rfl, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
  refine ⟨ts, v, hst, hrd, fun hc' => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc' (Nat.le_max_right _ _))).2, fun hn => ?_, fun l' => ?_, fun l' => ?_, hm, hp,
    _, by rw [hlog]; exact List.mem_append_right _ (List.mem_singleton_self _)⟩
  · rw [hc]
    show ts ≤ (t.views.setCoh l _).getCoh l
    rw [Views.getCoh_setCoh, ite_eq_left rfl]
    have : readView A (A.loadKind k) (t.views.getFwd l) ts = ts := by rw [hn]; rfl
    show ts ≤ max (t.views.getCoh l) (max (readPre A _ _ k) (readView A (A.loadKind k) (t.views.getFwd l) ts))
    rw [this]; omega_t
  · rw [hc]; exact Views.getCoh_le_setCoh _ _ _ _
  · rw [hf]; rfl

/-- A store keeps the forwarding entries of the other locations. -/
theorem spec_store_fwd {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) {l' : Loc} (hl : l' ≠ l) : o.thread.views.getFwd l' = t.views.getFwd l' := by
  obtain ⟨st, c', hr, -, -, -, -, hf, -⟩ := stepOne_out' A tid hex hs ho
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil,
    List.mem_flatMap] at hr
  obtain ⟨c1, h1, h⟩ := hr
  obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfw⟩ := writeSuccs_spec A tid _ h1
  rw [hf, hfw l' hl]

/-- An always-writing RMW under `rmwFence` keeps the forwarding entries of
the other locations. -/
theorem spec_rmw_tso_fwd (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l (fun old => some (g old)) fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) {l' : Loc} (hl : l' ≠ l) :
    o.thread.views.getFwd l' = t.views.getFwd l' := by
  obtain ⟨st, c', hr, -, -, -, -, hf, -⟩ := stepOne_out' A tid hex hs ho
  simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  obtain ⟨tr', old', hx', -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  obtain ⟨c2, h2, h⟩ := h
  obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hfw⟩ := writeSuccs_spec A tid _ h2
  have e2 : ∀ c : Ctx, (fenceStep c .sy).views.getFwd l' = c.views.getFwd l' :=
    fun c => getFwd_of_fwdb (fenceStep_fwdb _ _) _
  rw [hf, e2]
  split <;> exact (hfw l' hl).trans (e2 (ctx0 tid t mem))

/-- **A load-then-store** by a promise-free thread: it reads some `v` (the
last write's, if the coherence view is at or past it) and appends `g v`. -/
theorem spec_ldst {k : LoadKind} {k' : StoreKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.load k false l fun v => .store k' false l (g v) fun _ => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ ts v, o.thread.st = f v ∧ mem.read? l ts = some v ∧
      (mem.lastWrite l ≤ t.views.getCoh l → v = mem.finalVal l) ∧
      o.mem = (mem.append { loc := l, val := g v, tid }).1 ∧ o.thread.prom = [] := by
  obtain ⟨st, c', hr, hm, hst, hp, -, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨ts, v, rfl, hle, hrd, hw, hm', hp'⟩ := run_ldst A tid _ hp0 hr
  exact ⟨ts, v, hst, hrd, fun hc => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc (Nat.le_max_right _ _))).2, hm.trans hm', hp.trans hp'⟩

theorem en_ldst {k : LoadKind} {k' : StoreKind} {l : Loc} {g : Val → Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.load k false l fun v => .store k' false l (g v) fun _ => .done (f v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨c', hr⟩ := run_ldst_exists A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem) hp0
    ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ (instrViews_le hb.regs _) k k' l g f
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex hr
  obtain ⟨-, -, -, -, -, -, -, hp'⟩ := run_ldst A tid _ hp0 hr
  exact ⟨outs, o, h1, h2, h3.trans hp'⟩

end Spec

end Kraken.Promising.Live.Ticket2X64Step

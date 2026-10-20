/-
**Stage 3: promise-free instruction steps beyond
`LiveTicketStep`'s four shapes.** ISA-neutral.

- `spec_load_coh`/`spec_done_coh`: a load or a register-only step never
  lowers a coherence view (`getCoh`), so a view caught up by memory fairness
  stays caught up.
- An RMW with an arbitrary operation `op : Val → Option Val` (`none`: no
  write, e.g. a failing `CAS`; `some new`: write `new`): every outcome
  (`run_rmwo`, `spec_rmwo`) and the existence of an outcome (`run_rmwo_exists`,
  `en_rmwo`). `LiveTicketStep.spec_rmw` is the case `op = some ∘ g`.
- `readLast_writeSuccs_exists`: the write half of an RMW reading the last
  write, at any architecture (also used by `LiveTsoRmw`).
-/
import Kraken.Promising.LiveTicketStep

namespace Kraken.Promising.Live.SpinStep

open Kraken.Promising Kraken.Promising.Live.TicketStep

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

section Shapes

variable (A : Arch) (tid : Nat) (iv : InstrViews)

theorem readNext_getCoh (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool) (t : Time) (v : Val)
    (l' : Loc) : c.views.getCoh l' ≤ (readNext A iv c k xcl l noRet t v).views.getCoh l' :=
  Views.getCoh_le_setCoh _ _ _ _

/-- A load never lowers a coherence view. -/
theorem run_load_coh {σ : Type} {c c' : Ctx} {k : LoadKind} {l : Loc} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.load k false l fun v => .done (f v))) (l' : Loc) :
    c.views.getCoh l' ≤ c'.views.getCoh l' := by
  simp only [runTree, List.mem_flatMap] at h
  obtain ⟨⟨ts, v, c1⟩, hx, h⟩ := h
  obtain ⟨-, rfl⟩ := run_done A tid iv h
  obtain ⟨ts', v', hx', -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  exact readNext_getCoh A iv _ _ _ _ _ _ _ l'

/-- **An RMW with an arbitrary operation**: it reads some `old` at `tr` (with
the read's conditions); then `op old = none` (no write: memory and promises
unchanged, coherence views not lowered) or `op old = some new` (an atomic
write of `new` appended at `|M| + 1`). -/
theorem run_rmwo {σ : Type} (hA : A.rmwFence = false) {c c' : Ctx} (hp : c.prom = []) {k : RmwKind}
    {l : Loc} {op : Val → Option Val} {f : Val → σ} {st : σ}
    (h : .ok (st, c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v))) :
    ∃ tr old, st = f old ∧ tr ≤ c.mem.last ∧ c.mem.read? l tr = some old ∧
      c.mem.writeIn l tr (max (readPre A iv c (A.rmwKind k).loadKind) (c.views.getCoh l)) = false ∧
      c'.prom = [] ∧
      ((op old = none ∧ c'.mem = c.mem ∧ ∀ l', c.views.getCoh l' ≤ c'.views.getCoh l') ∨
       (∃ new, op old = some new ∧ c.mem.atomic l tid tr (c.mem.last + 1) = true ∧
         c'.mem = (c.mem.append { loc := l, val := new, tid }).1)) := by
  simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap] at h
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := h
  obtain ⟨tr', old', hx', hle, hr, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  refine ⟨tr, old, ?_⟩
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨rfl, rfl⟩ := run_done A tid iv h
    exact ⟨rfl, hle, hr, hw, by simp [readNext, hp], .inl ⟨rfl, rfl, readNext_getCoh A iv _ _ _ _ _ _ _⟩⟩
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨rfl, hc⟩ := run_done A tid iv h
    obtain ⟨hm, hpr, hat⟩ := writeSuccs_nil A tid iv (by rw [readNext_prom]; exact hp) (.inl h2)
    rw [readNext_mem] at hm hat
    obtain ⟨-, ha2⟩ := hat _ rfl
    subst hc
    refine ⟨rfl, hle, hr, hw, ?_, .inr ⟨new, rfl, ha2, ?_⟩⟩ <;>
      cases (A.rmwKind k == RmwKind.acqRel && !false) <;> simp [hpr, hm]

/-- **The write half of an RMW that reads the last write**: in a
promise-free, bounded context, after the read of the last write of `l`
(`readNext` at `lastWrite l`), an exclusive write of any value has a
successor. Architecture-generic (shared by `run_rmwo_exists` and
`TsoRmw.run_rmwo_tso_exists`, which applies it after the leading fence). -/
theorem readLast_writeSuccs_exists {c : Ctx} (hp : c.prom = []) (hb : c.Bnd) (hiv : iv.Le c.mem.last)
    (k : RmwKind) (l : Loc) (new : Val) :
    let c1 := readNext A iv c (A.rmwKind k).loadKind false l false (c.mem.lastWrite l) (c.mem.finalVal l)
    ∃ c2, c2 ∈ writeSuccs A tid iv c1 (A.rmwKind k).storeKind true l new (some (c.mem.lastWrite l))
      (c1.loadViews.getLastD 0) := by
  intro c1
  have hx : (c.mem.lastWrite l, c.mem.finalVal l, c1) ∈ readSuccs A iv c (A.rmwKind k).loadKind false l false := by
    rw [mem_readSuccs]
    refine ⟨_, _, rfl, c.mem.lastWrite_le l, c.mem.read?_lastWrite l, c.mem.writeIn_lastWrite l _, ?_⟩
    rw [hp]; rfl
  obtain ⟨hb1, -, hm1⟩ := readSuccs_bnd A iv hb hiv hx
  have hm1 : c1.mem = c.mem := hm1
  have hp1 : c1.prom = [] := by simp [c1, readNext, hp]
  have hv := hb1.views.le
  rw [hm1] at hv
  have h1 := hiv.addrW; have h2 := hiv.dataW; have h3 := hiv.condW
  have h4 := hv.vwNew; have h5 := hv.vCAP; have h6 := hv.coh l
  have h7 := hv.vrOld; have h8 := hv.vrOldNR; have h9 := hv.vwOld
  have hνr : c1.loadViews.getLastD 0 ≤ c.mem.last := by
    rw [← hm1]
    cases hlv : c1.loadViews.getLast? with
    | none => simp [List.getLastD_eq_getLast?, hlv]
    | some ν =>
      rw [List.getLastD_eq_getLast?, hlv]
      exact hb1.loadViews ν (List.mem_of_getLast? hlv)
  have hat : c.mem.atomic l tid (c.mem.lastWrite l) (c.mem.last + 1) = true :=
    c.mem.atomic_of_forall l tid _ _ fun t w h1 _ hw hl => absurd hl (c.mem.not_write_of_lastWrite_lt l h1 hw)
  have hlw := c.mem.lastWrite_le l
  simp only [writeSuccs, hp1, List.filterMap_nil, List.nil_append, Memory.append_time, hm1]
  refine ⟨_, List.mem_ite_nil_right.mpr ⟨?_, List.mem_singleton_self _⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, by omega_t, hat⟩
  split <;> (try split) <;> omega_t

/-- An RMW can read the last write (and write, if its operation does). -/
theorem run_rmwo_exists {σ : Type} (hA : A.rmwFence = false) {c : Ctx} (hp : c.prom = []) (hb : c.Bnd)
    (hiv : iv.Le c.mem.last) (k : RmwKind) (l : Loc) (op : Val → Option Val) (f : Val → σ) :
    ∃ c', .ok (f (c.mem.finalVal l), c') ∈ runTree A tid iv c (.rmw k false l op fun v => .done (f v)) := by
  let kl := if false = true then LoadKind.plain else (A.rmwKind k).loadKind
  let c1 := readNext A iv c kl false l false (c.mem.lastWrite l) (c.mem.finalVal l)
  have hx : (c.mem.lastWrite l, c.mem.finalVal l, c1) ∈ readSuccs A iv c kl false l false := by
    rw [mem_readSuccs]
    refine ⟨_, _, rfl, c.mem.lastWrite_le l, c.mem.read?_lastWrite l, c.mem.writeIn_lastWrite l _, ?_⟩
    rw [hp]; rfl
  cases hop : op (c.mem.finalVal l) with
  | none =>
    refine ⟨c1, ?_⟩
    simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
    exact ⟨_, hx, by simp only [hop]; exact run_done_exists A tid iv _ _⟩
  | some new =>
    obtain ⟨c2, hw⟩ := readLast_writeSuccs_exists A tid iv hp hb hiv k l new
    simp only [runTree, hA, Bool.false_eq_true, ↓reduceIte, List.mem_flatMap]
    exact ⟨_, _, hx, by simp only [hop, List.mem_flatMap]; exact ⟨c2, hw, run_done_exists A tid iv _ _⟩⟩

end Shapes

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- A register-only step keeps the coherence views. -/
theorem spec_done_coh {s : I.State} (hex : I.exec t.st = some (.done s)) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) (l : Loc) : o.thread.views.getCoh l = t.views.getCoh l := by
  obtain ⟨-, -, -, hc⟩ := spec_done A tid hex hs ho
  unfold Views.getCoh; rw [hc]

/-- A load never lowers a coherence view. -/
theorem spec_load_coh {k : LoadKind} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k false l fun v => .done (f v))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) (l' : Loc) : t.views.getCoh l' ≤ o.thread.views.getCoh l' := by
  obtain ⟨st, c', hr, -, -, -, hc, -⟩ := stepOne_out A tid hex hs ho
  have := run_load_coh A tid _ hr l'
  unfold Views.getCoh at this ⊢; rw [hc]; exact this

/-- **An RMW with an arbitrary operation** by a promise-free thread: it reads
a value of the location (the last write's, if the coherence view is at or
past it); no write and the coherence views not lowered, or an atomic write
appended. -/
theorem spec_rmwo (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hp0 : t.prom = [])
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
    (hs : stepOne A t tid mem = some outs) (ho : .ok o ∈ outs) :
    ∃ tr old, o.thread.st = f old ∧ mem.read? l tr = some old ∧
      (mem.lastWrite l ≤ t.views.getCoh l → old = mem.finalVal l) ∧ o.thread.prom = [] ∧
      ((op old = none ∧ o.mem = mem ∧ ∀ l', t.views.getCoh l' ≤ o.thread.views.getCoh l') ∨
       (∃ new, op old = some new ∧ mem.atomic l tid tr (mem.last + 1) = true ∧
         o.mem = (mem.append { loc := l, val := new, tid }).1)) := by
  obtain ⟨st, c', hr, hm, hst, hp, hc, -⟩ := stepOne_out A tid hex hs ho
  obtain ⟨tr, old, rfl, hle, hrd, hw, hp', hcase⟩ := run_rmwo A tid _ hA hp0 hr
  refine ⟨tr, old, hst, hrd, fun hc' => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc' (Nat.le_max_right _ _))).2, hp.trans hp', ?_⟩
  rcases hcase with ⟨h1, h2, h3⟩ | ⟨new, h1, h2, h3⟩
  · refine .inl ⟨h1, hm.trans h2, fun l' => ?_⟩
    have := h3 l'
    unfold Views.getCoh at this ⊢; rw [hc]; exact this
  · exact .inr ⟨new, h1, h2, hm.trans h3⟩

theorem en_rmwo (hA : A.rmwFence = false) {k : RmwKind} {l : Loc} {op : Val → Option Val} {f : Val → I.State}
    (hp0 : t.prom = []) (hb : t.Bnd mem.last)
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) :
    ∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread.prom = [] := by
  obtain ⟨c', hr⟩ := run_rmwo_exists A tid (instrViews t (I.deps t.st)) (c := ctx0 tid t mem) hA hp0
    ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ (instrViews_le hb.regs _) k l op f
  obtain ⟨outs, o, h1, h2, -, -, h3⟩ := stepOne_of_run A tid hex hr
  obtain ⟨-, -, -, -, -, -, hp', -⟩ := run_rmwo A tid _ hA hp0 hr
  exact ⟨outs, o, h1, h2, h3.trans hp'⟩

end Spec

/-! ## Configuration and memory frames

ISA-generic and instance-free. `LiveTicketInv.{wt_get, wt_tid, wt_ne,
mem_frame, loc_ne}` (which carry that file's `ValidLayout (layout tkWorker)`
section instance) are proved from these. -/

theorem wt_get {cfg : Config I} {tid j : Nat} {t t' u : Thread I} {mem' : Memory}
    (ht : cfg.threads[tid]? = some t) (h : (cfg.withThread tid t' mem').threads[j]? = some u) :
    (j = tid ∧ u = t') ∨ (j ≠ tid ∧ cfg.threads[j]? = some u) := by
  rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht)] at h
  split at h
  · cases h; left; exact ⟨by omega, rfl⟩
  · right; exact ⟨by omega, h⟩

theorem wt_tid {cfg : Config I} {tid : Nat} {t t' : Thread I} {mem' : Memory}
    (ht : cfg.threads[tid]? = some t) : (cfg.withThread tid t' mem').threads[tid]? = some t' := by
  rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht), ite_eq_left rfl]

theorem wt_ne {cfg : Config I} {tid j : Nat} {t t' : Thread I} {mem' : Memory}
    (ht : cfg.threads[tid]? = some t) (hj : j ≠ tid) :
    (cfg.withThread tid t' mem').threads[j]? = cfg.threads[j]? := by
  rw [Config.withThread_get? _ _ _ (lt_size_of_get? ht), ite_eq_right (Ne.symm hj)]

/-- An append to another location: the memory facts about `l'` unchanged. -/
theorem mem_frame (mem : Memory) (w : Msg) {l' : Loc} (hl : w.loc ≠ l') :
    (mem.append w).1.finalVal l' = mem.finalVal l' ∧ (mem.append w).1.lastWrite l' = mem.lastWrite l' ∧
    (∀ ts v, (mem.append w).1.read? l' ts = some v → mem.read? l' ts = some v) ∧
    (∀ ts w', (mem.append w).1.get? ts = some w' → w'.loc = l' → mem.get? ts = some w') := by
  refine ⟨by rw [finalVal_append, ite_eq_right hl], by rw [Memory.lastWrite_append, ite_eq_right hl],
    fun ts v h => ?_, fun ts w' h hl' => ?_⟩
  · rcases read?_append_eq_some mem w h with h | ⟨-, h, -⟩
    · exact h
    · exact absurd h hl
  · rcases mem.get?_append_eq_some w h with ⟨-, h⟩ | ⟨-, rfl⟩
    · exact h
    · exact absurd hl' hl

theorem loc_ne {a b : BitVec 64} (h : Decls.overlaps a 4 b 4 = false) : (⟨a, 4⟩ : Loc) ≠ ⟨b, 4⟩ := by
  intro e; cases e; simp [Decls.overlaps] at h

end Kraken.Promising.Live.SpinStep

/-
**Stage 3: a fencing conditional RMW with
outstanding promises, and the TSO no-fresh-write certification lemma**
(ISA-neutral; candidates for `LiveX64SemShape` / `LiveSemShape`).

- `spec_rmwo_p_tso`: an RMW with an arbitrary operation under `rmwFence`
  (x86's `lock cmpxchg`), with any promise set: an atomic read, then no write,
  an append, or the fulfilment of an outstanding promise. Unlike
  `X64SemShape.spec_rmw_p_tso` the fulfilment keeps the release condition
  `vwOld < ts`, which the no-fresh-write argument below needs.
- `spec_choose_vw`: a register-only choice keeps `vwOld`.
- `replay_rmwo_tso`: an outcome that does not append replays against any
  larger memory (the conditional twin of `X64SemShape.replay_rmw_tso`).
- `TsoW`, `nacert_of_tsoW`: **on TSO a thread with outstanding promises
  certifies without fresh writes.** Every store is a release (`Arch.tso`:
  plain stores are `.rel`, locked RMWs `acqRel`), so a fresh write raises
  `vwOld` past `|M|`, hence past every outstanding promise, and every
  fulfilment needs `vwOld < ts`; `vwOld` never drops. So after a fresh write
  the thread can never empty its promise set. `TsoW` is this per-step
  property (proved per instruction shape: `tsoW_done`, `tsoW_load`,
  `tsoW_store`, `tsoW_rmwo`; non-temporal stores are excluded by the shape
  lemmas' hypotheses), and `nacert_of_tsoW` turns any certification of a
  thread with promises into one without fresh writes, for any program whose
  every step satisfies `TsoW` under a step invariant.
-/
import Kraken.Promising.LiveX64SemShape
import Kraken.Promising.LiveSem
import Kraken.Promising.LiveSpinX64Step

namespace Kraken.Promising.Live.SpinX64SemShape

set_option linter.unusedSectionVars false

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.TicketStep Kraken.Promising.Live.SemShape
open Kraken.Promising.Live.TsoRmw Kraken.Promising.Live.X64SemShape

variable {I : ISA}

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

private theorem rmwPost_vw (b : Bool) (c : Ctx) (l : Loc) :
    (if b then ({ c with rmwWrote := true, views := { c.views with
        vrNew := max c.views.vrNew (c.views.getCoh l), vwNew := max c.views.vwNew (c.views.getCoh l) } } : Ctx)
      else { c with rmwWrote := true }).views.vwOld = c.views.vwOld := by
  cases b <;> rfl

section Spec

variable (A : Arch) (tid : Nat) {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A fencing RMW with an arbitrary operation, with any promise set**: it
reads `old` at `tr` (the last write's value, if the coherence view is at or
past it); then no write (memory, promises and `vwOld` unchanged), or an
atomic append (`vwOld` past it unless non-temporal), or the atomic fulfilment
of an outstanding promise above the coherence view (and above `vwOld` for a
release). A hoist candidate. -/
theorem spec_rmwo_p_tso (hA : A.rmwFence = true) {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v)))
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
          ((A.storeKind (A.rmwKind k).storeKind == .rel) = true → t.views.vwOld < ts) ∧
          o.mem = mem ∧ o.thread.prom = t.prom.erase ts ∧ t.views.vwOld ≤ o.thread.views.vwOld ∧
          ts ≤ o.thread.views.getCoh l ∧ tr < ts ∧ mem.atomic l tid tr ts = true)))) := by
  obtain ⟨tree, c', hex', hr, hp, hv, hm, -⟩ := SLR.stepOne_runK A hs ho
  obtain rfl : tree = _ := Option.some.inj (hex'.symm.trans hex)
  have hvw : o.thread.views.vwOld = c'.views.vwOld := by have := congrArg Views.vwOld hv; exact this
  have hco : ∀ l', o.thread.views.getCoh l' = c'.views.getCoh l' := fun l' =>
    SpinSwpStep.getCoh_congr (by have := congrArg Views.coh hv; exact this) l'
  simp only [runTree, hA, ↓reduceIte, Bool.false_eq_true, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  have hd := readSuccs_dord A _ hx
  obtain ⟨tr', old', hx', hle, hrd, hw, -⟩ := (mem_readSuccs A).mp hx
  simp only [Prod.mk.injEq] at hx'
  obtain ⟨rfl, rfl, rfl⟩ := hx'
  rw [fence_mem] at hle hrd hw
  rw [fence_getCoh] at hw
  have hc0 : (fenceStep ({ views := t.views, prom := t.prom, mem, log := [.instr tid (I.showInstr t.st)] } : Ctx)
      .sy).views.getCoh l = t.views.getCoh l := fence_getCoh _ _ _
  refine ⟨tr, old, ?_, hrd, fun hc' => (read_lastWrite_of_coh mem l hle hrd hw
    (Nat.le_trans hc' (Nat.le_max_right _ _))).2, ?_⟩
  · cases hop : op old with
    | none => simp only [hop] at h; exact (run_done A tid (instrViews t (I.deps t.st)) h).1
    | some new =>
      simp only [hop, List.mem_flatMap] at h
      obtain ⟨c2, -, h⟩ := h
      exact (run_done A tid (instrViews t (I.deps t.st)) h).1
  cases hop : op old with
  | none =>
    simp only [hop] at h
    obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    refine .inl ⟨rfl, ?_, ?_, ?_⟩
    · rw [hm, fence_mem, readNext_mem, fence_mem]
    · rw [hp, fence_prom, readNext_prom, fence_prom]
    · rw [hvw, fence_vwOld, SpinSemShape.readNext_vwOld, fence_vwOld]
  | some new =>
    simp only [hop, List.mem_flatMap] at h
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨-, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    obtain ⟨q1, q2, q3, -⟩ := rmwPost_keeps (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    have q4 := rmwPost_vw (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    refine .inr ⟨new, rfl, ?_⟩
    rcases SpinSemShape.mem_writeSuccs_c A tid _ h2 with
      ⟨e1, e2, e3, e4, e5, e6⟩ | ⟨ts, hts, e1, e2, e3, e4, e5, e6, e7, e8⟩
    · simp only [readNext_mem, readNext_prom, SpinSemShape.readNext_vwOld, fence_mem, fence_prom,
        fence_vwOld] at e1 e2 e3 e4 e5 e6
      obtain ⟨-, ha⟩ := e6 _ rfl
      refine .inl ⟨by rw [hm, fence_mem, q1, e1], by rw [hp, fence_prom, q2, e2], fun hk => ?_, ?_, ?_, ha⟩
      · rw [hvw, fence_vwOld, q4]; exact e3 hk
      · rw [hvw, fence_vwOld, q4]; exact e4
      · rw [hco, fence_getCoh, q3]; exact e5
    · simp only [readNext_mem, readNext_prom, SpinSemShape.readNext_vwOld, fence_mem, fence_prom,
        fence_vwOld] at hts e1 e3 e4 e5 e6 e8
      obtain ⟨a1, a2⟩ := e8 _ rfl
      refine .inr ⟨ts, hts, e1, ?_, e3, by rw [hm, fence_mem, q1, e4], by rw [hp, fence_prom, q2, e5], ?_, ?_,
        a1, a2⟩
      · rw [← hc0]; exact Nat.lt_of_le_of_lt (hd.coh l) e2
      · rw [hvw, fence_vwOld, q4]; exact e6
      · rw [hco, fence_getCoh, q3]; exact e7

/-- A choice of register-only outcomes keeps `vwOld` (the `vwOld` part missing
from `SpinX64Step.spec_choose`). A hoist candidate. -/
theorem spec_choose_vw {n : Nat} {f : Fin n → I.State}
    (hex : I.exec t.st = some (.choose n fun i => .done (f i))) (hs : stepOne A t tid mem = some outs)
    (ho : .ok o ∈ outs) : o.thread.views.vwOld = t.views.vwOld := by
  obtain ⟨c', hr, -, -, hv⟩ := stepOne_outV A tid hex hs ho
  obtain ⟨-, rfl⟩ := SpinX64Step.run_choose A tid _ hr
  exact hv

end Spec

/-! ## Replay against a larger memory -/

section Replay

variable (A : Arch) (tid : Nat) {t : Thread I} {mem0 mem : Memory} {outs : List (Except String (Outcome I))}
  {o : Outcome I}

/-- **A choice of register-only outcomes replays against a larger memory**
(the `.choose` twin of `SemShape.replay_done`; the generic form of
`SpinX64SemXchgSolo.replay_choose`/`SpinX64SemCmpxSolo.replay_choose`). -/
theorem replay_choose (hs : stepOne A t tid mem0 = some outs) (ho : .ok o ∈ outs) (hm : o.mem = mem0) {n : Nat}
    {f : Fin n → I.State} (hex : I.exec t.st = some (.choose n fun i => .done (f i))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr _ => ?_
  obtain ⟨⟨i, rfl⟩, rfl⟩ := SpinX64Step.run_choose A tid _ hr
  exact SpinX64Step.run_choose_exists A tid _ _ f i

/-- **A fencing RMW outcome with an arbitrary operation that does not append
replays against a larger memory** (`X64SemShape.replay_rmw_tso` for any
`op`). A hoist candidate. -/
theorem replay_rmwo_tso (hp : mem0.Prefix mem) (hb : t.Bnd mem0.last) (hs : stepOne A t tid mem0 = some outs)
    (ho : .ok o ∈ outs) (hm : o.mem = mem0) (hA : A.rmwFence = true) {k : RmwKind} {l : Loc}
    {op : Val → Option Val} {f : Val → I.State}
    (hex : I.exec t.st = some (.rmw k false l op fun v => .done (f v))) :
    ∃ outs' o', stepOne A t tid mem = some outs' ∧ .ok o' ∈ outs' ∧ o'.thread = o.thread ∧ o'.mem = mem := by
  refine stepOne_replay_of_run A tid hex hs ho hm fun st c0' hr hm' => ?_
  have hiv := instrViews_le hb.regs (I.deps t.st)
  have hcb : (fenceStep (ctx0 tid t mem0) .sy).Bnd :=
    fenceStep_bnd ⟨hb.views, fun _ h => absurd h List.not_mem_nil, Nat.zero_le _⟩ .sy
  have hv := hcb.views.le
  have hbd : ∀ kl, max (readPre A (instrViews t (I.deps t.st)) (fenceStep (ctx0 tid t mem0) .sy) kl)
      ((fenceStep (ctx0 tid t mem0) .sy).views.getCoh l) ≤ (fenceStep (ctx0 tid t mem0) .sy).mem.last := by
    intro kl
    have := hiv.addrR; have := hv.vrNew; have := hv.vRel; have := hv.coh l
    have hfm : (fenceStep (ctx0 tid t mem0) .sy).mem.last = mem0.last := by rw [fence_mem]
    simp only [readPre]; split <;> omega_t
  rw [runTree] at hr
  simp only [hA, ↓reduceIte, List.mem_flatMap] at hr
  obtain ⟨⟨tr, old, c1⟩, hx, h⟩ := hr
  have hp' : (fenceStep (ctx0 tid t mem0) .sy).mem.Prefix mem := by rw [fence_mem]; exact hp
  have hx' := readSuccs_replay A _ hp' hx (hbd _)
  have hc1 : c1.mem = mem0 := by
    obtain ⟨tr', old', hxe, -⟩ := (mem_readSuccs A).mp hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨-, -, rfl⟩ := hxe
    rw [readNext_mem, fence_mem]
  have e : fenceStep (ctx0 tid t mem) .sy = { fenceStep (ctx0 tid t mem0) .sy with mem := mem } :=
    fence_eq_mem (ctx0 tid t mem0) mem .sy
  rw [runTree]
  simp only [hA, ↓reduceIte, List.mem_flatMap]
  refine ⟨(tr, old, { c1 with mem := mem }), by rw [e]; exact hx', ?_⟩
  dsimp only at h ⊢
  cases hop : op old with
  | none =>
    simp only [hop] at h ⊢
    obtain ⟨rfl, rfl⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    have : fenceStep { c1 with mem := mem } .sy = { fenceStep c1 .sy with mem := mem } := fence_eq_mem c1 mem .sy
    rw [this]
    exact run_done_exists A tid _ _ _
  | some new =>
    simp only [hop, List.mem_flatMap] at h ⊢
    obtain ⟨c2, h2, h⟩ := h
    obtain ⟨rfl, hc⟩ := run_done A tid (instrViews t (I.deps t.st)) h
    obtain ⟨q1, -, -, -⟩ := rmwPost_keeps (A.rmwKind k == RmwKind.acqRel && !false) c2 l
    have hm2 : c2.mem = c1.mem := by
      rw [hc1, ← q1, ← fence_mem _ .sy, ← hc]; exact hm'
    have h2' := writeSuccs_replay A tid _ (hc1 ▸ hp) h2 hm2
    refine ⟨{ c2 with mem := mem }, h2', ?_⟩
    rw [hc]
    cases (A.rmwKind k == RmwKind.acqRel && !false) <;> exact run_done_exists A tid _ _ _

end Replay

/-! ## TSO: certification without fresh writes -/

/-- **The TSO write discipline of one instruction step**: `vwOld`
does not drop in a step that keeps memory; a dropped promise lies above `vwOld` (a release fulfilment); a
fresh write raises `vwOld` past `|M|` and keeps the promise set; promises
stay messages of the memory. -/
structure TsoW (t : Thread I) (mem : Memory) (o : Outcome I) : Prop where
  vw : o.mem = mem → t.views.vwOld ≤ o.thread.views.vwOld
  drop : ∀ ts ∈ t.prom, ts ∉ o.thread.prom → t.views.vwOld < ts
  fresh : o.mem ≠ mem → mem.last + 1 ≤ o.thread.views.vwOld ∧ o.thread.prom = t.prom
  le : ∀ ts ∈ o.thread.prom, ts ≤ o.mem.last

section W

variable {t : Thread I} {mem : Memory} {o : Outcome I}

/-- A step that changes neither memory, promises nor `vwOld`. -/
theorem tsoW_same (hle : ∀ ts ∈ t.prom, ts ≤ mem.last) (hm : o.mem = mem) (hp : o.thread.prom = t.prom)
    (hv : o.thread.views.vwOld = t.views.vwOld) : TsoW t mem o :=
  ⟨fun _ => Nat.le_of_eq hv.symm, fun ts h hn => absurd (hp ▸ h) hn, fun h => absurd hm h,
    fun ts h => by rw [hm]; exact hle ts (hp ▸ h)⟩

/-- A fresh (non-temporal-free) write. -/
theorem tsoW_fresh {w : Msg} (hle : ∀ ts ∈ t.prom, ts ≤ mem.last) (hm : o.mem = (mem.append w).1)
    (hp : o.thread.prom = (t.prom ++ [mem.last + 1]).erase (mem.last + 1))
    (hv1 : mem.last + 1 ≤ o.thread.views.vwOld) : TsoW t mem o := by
  have hp' : o.thread.prom = t.prom := hp.trans (erase_fresh hle)
  refine ⟨fun h => absurd (hm.symm.trans h) (append_ne _ _), fun ts h hn => absurd (hp' ▸ h) hn, fun _ => ⟨hv1, hp'⟩, fun ts h => ?_⟩
  rw [hm, Memory.last_append]; exact Nat.le_succ_of_le (hle ts (hp' ▸ h))

/-- A release fulfilment. -/
theorem tsoW_ful {ts : Time} (hle : ∀ ts ∈ t.prom, ts ≤ mem.last) (hm : o.mem = mem)
    (hp : o.thread.prom = t.prom.erase ts) (hvt : t.views.vwOld < ts) (hv : t.views.vwOld ≤ o.thread.views.vwOld) :
    TsoW t mem o := by
  refine ⟨fun _ => hv, fun ts' h hn => ?_, fun h => absurd hm h, fun ts' h => ?_⟩
  · by_cases e : ts' = ts
    · exact e ▸ hvt
    · rw [hp] at hn; exact absurd ((List.mem_erase_of_ne e).mpr h) hn
  · rw [hm]; rw [hp] at h; exact hle ts' (List.mem_of_mem_erase h)

end W

section Run

variable {A : Arch} {tid : Nat} (Inv : I.State → Prop)
  (hstep : ∀ {t : Thread I} {mem : Memory} {outs : List (Except String (Outcome I))} {oc : Outcome I},
    Inv t.st → (∀ ts ∈ t.prom, ts ≤ mem.last) → stepOne A t tid mem = some outs → .ok oc ∈ outs →
    Inv oc.thread.st ∧ TsoW t mem oc)

include hstep

/-- Under `TsoW`, a promise at or below `vwOld` is never fulfilled. -/
theorem stuck_of_tsoW : ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → Inv p.1.st →
    (∀ ts ∈ p.1.prom, ts ≤ p.2.last) → ∀ ts0 ∈ p.1.prom, ts0 ≤ p.1.views.vwOld → ts0 ∈ q.1.prom := by
  intro n p q h
  induction h with
  | refl => intro _ _ ts0 h _; exact h
  | @step n p q r hs _ ih =>
    intro hI hle ts0 h0 hv0
    obtain ⟨outs, oc, hs, ho, rfl⟩ := hs
    obtain ⟨hI', W⟩ := hstep hI hle hs ho
    have hin : ts0 ∈ oc.thread.prom := Classical.byContradiction fun hn =>
      absurd (W.drop ts0 h0 hn) (Nat.not_lt.mpr hv0)
    refine ih hI' W.le ts0 hin ?_
    by_cases hm : oc.mem = p.2
    · exact Nat.le_trans hv0 (W.vw hm)
    · exact Nat.le_trans (Nat.le_succ_of_le (hle ts0 h0)) (W.fresh hm).1

/-- **On TSO a thread with promises certifies without fresh writes**:
a run that empties the promise set gives one of the same length against the
same memory (stopping once the promise set is empty). -/
theorem nacert_of_tsoW : ∀ {n : Nat} {p q : Thread I × Memory}, ThreadNPn A tid n p q → q.1.prom = [] →
    Inv p.1.st → (∀ ts ∈ p.1.prom, ts ≤ p.2.last) → ∃ t', ThreadNPn A tid n p (t', p.2) ∧ t'.prom = [] := by
  intro n p q h
  induction h with
  | refl n p => intro hq _ _; exact ⟨p.1, .refl _ _, hq⟩
  | @step n p q r hs h ih =>
    intro hq hI hle
    by_cases hp0 : p.1.prom = []
    · exact ⟨p.1, .refl _ _, hp0⟩
    obtain ⟨outs, oc, hs', ho, rfl⟩ := hs
    obtain ⟨hI', W⟩ := hstep hI hle hs' ho
    by_cases hm : oc.mem = p.2
    · obtain ⟨t', h', ht'⟩ := ih hq hI' W.le
      refine ⟨t', .step ⟨outs, oc, hs', ho, rfl⟩ ?_, ht'⟩
      rw [← hm]; exact h'
    · obtain ⟨ts, hts⟩ := List.exists_mem_of_ne_nil _ hp0
      obtain ⟨hv1, hpe⟩ := W.fresh hm
      have := stuck_of_tsoW Inv hstep h hI' W.le ts (hpe ▸ hts) (Nat.le_trans (Nat.le_succ_of_le (hle ts hts)) hv1)
      rw [hq] at this; cases this

/-- `nacert_of_tsoW` for a certification (`Sem.NACertG`). -/
theorem nacertG_of_tsoW {fuel : Nat} {t : Thread I} {mem : Memory} (h : CertOkN A tid t mem fuel) (hI : Inv t.st)
    (hle : ∀ ts ∈ t.prom, ts ≤ mem.last) : Sem.NACertG A fuel tid t mem :=
  let ⟨_, _, hr, hp⟩ := h; nacert_of_tsoW Inv hstep hr hp hI hle

end Run

end Kraken.Promising.Live.SpinX64SemShape

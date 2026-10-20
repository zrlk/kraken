/-
**One instruction step = one memory event, on the
fuel-free machine** (ISA-neutral, architecture-neutral).

The lowering is planned as a backward simulation over shared promise memory
with one memory event per micro-step. This file states, in Kraken's own event
vocabulary (`EvTree`: `done`/`load`/`store`/`rmw`/`fence`, plus `choose`),
what one instruction step of the fuel-free semantic machine
(`Live.Inf.InstrSemInf`, `LiveSemInf.lean`) is, as an **iff**, for a thread
whose next instruction has a tree of each single-event shape. The
per-instruction half (which instruction has which tree) is ISA-specific:
`Lower/EventsA64.lean` for AArch64 `isaLSE2`.

## Contents

- `RunOut A tid t mem tree th mem'`: the thread rules' outcomes of one
  instruction with tree `tree` (a run of `runTree` from `stepOne`'s context
  `ctx0`, finished by `finishInstr`). `instrSemInf_iff_of_exec`: an
  `InstrSemInf` step of a thread whose `exec` is `some tree` is exactly a
  `RunOut` outcome that is `CertOk`, installed by `Config.withThread`.
- The rules in closed form: `mem_readSuccs` (from `ReleasePrefixNT.lean`:
  read = `readNext` at a readable timestamp) and `mem_writeSuccs_iff` (new:
  write = fulfil an outstanding promise, or promise-now at `|M| + 1`, with
  `afterWrite`; `writePre`/`writeFwd`/`writeOk` name the pieces of
  `writeSuccs`).
- Run level, one lemma per shape, each an iff: `run_done_iff`,
  `run_load_iff`, `run_store_iff` (non-exclusive store), `run_fence_iff`,
  `run_rmw_iff` (any `Arch`: `rmwFenceOpt` is TSO's surrounding `fence .sy`,
  `rmwBump` the acquire-release bump), `run_choose_iff`.
- Machine level (`InstrSemInf`), one lemma per shape, each an iff:
  `instrSemInf_done_iff`, `instrSemInf_load_iff`, `instrSemInf_store_iff`,
  `instrSemInf_fence_iff`, `instrSemInf_rmw_iff`.
- **No-event steps (source stutter):** `instrSemInf_done_stutter`: a step at
  a `.done s` tree leaves the memory and the promise set unchanged, sets the
  state to `s`, and changes the thread's views at most in `vCAP` (raised by
  the condition registers' view, for a conditional branch); only the register
  views (`rview`/`wview`) change otherwise.

The per-instruction lemmas compose with these: `exec t.st = some tree` from
`EventsA64`, then the shape lemma here.
-/
import Kraken.Promising.LiveSemInf
import Kraken.Promising.LiveSemShape
import Kraken.Promising.LiveCertCut

namespace Kraken.Promising.Lower

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

variable {I : ISA}

/-! ## The write rule in closed form -/

section Write

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- The pre-view of a write of kind `k` (`νpre` of `writeSuccs`; `k` is the
effective kind, `A.storeKind` already applied). -/
def writePre (c : Ctx) (k : StoreKind) (extra : View) : View :=
  max (max iv.addrW (max iv.dataW (max iv.condW extra))) (max (max c.views.vwNew c.views.vCAP)
    (if k == .rel then max (max c.views.vrOld c.views.vrOldNR) c.views.vwOld
     else if k == .nt then max c.views.vrOld c.views.vrOldNR else 0))

/-- The forwarding view of a write (`νfwd` of `writeSuccs`). -/
def writeFwd (extra : View) : View := max iv.addrR (max iv.dataR extra)

/-- The timestamp condition of a write at `t` (`ok` of `writeSuccs`): above
the pre-view and the coherence view, and, for an exclusive or RMW write
paired with a read at `tr`, above `tr` and atomic. -/
def writeOk (c : Ctx) (k : StoreKind) (l : Loc) (tr : Option Time) (extra : View) (t : Time) : Bool :=
  max (writePre iv c k extra) (c.views.getCoh l) < t &&
    (match tr with | some tr => tr < t && c.mem.atomic l tid tr t | none => true)

/-- The context of a promise-now write before `afterWrite`: the message
appended, its timestamp promised, and recorded in `promisedNow`. -/
def promiseNowCtx (c : Ctx) (k : StoreKind) (l : Loc) (v : Val) (extra : View) : Ctx :=
  { c with mem := (c.mem.append { loc := l, val := v, tid }).1, prom := c.prom ++ [c.mem.last + 1],
           promisedNow := c.promisedNow ++
             [({ loc := l, val := v, tid }, max (writePre iv c k extra) (c.views.getCoh l))] }

private theorem msg_beq_iff {w : Msg} {l : Loc} {v : Val} :
    (w.loc == l && w.val == v && w.tid == tid) = true ↔ w = { loc := l, val := v, tid } := by
  refine ⟨SemShape.msg_eq_of_beq, fun h => ?_⟩
  subst h; simp

/-- **The write rule in closed form** (`writeSuccs`, both directions): fulfil
an outstanding promise `t` of the same message, or promise now at `|M| + 1`;
either way under `writeOk`, and the context after is `afterWrite`. -/
theorem mem_writeSuccs_iff {xr : View} {c c' : Ctx} {k : StoreKind} {xcl : Bool} {l : Loc} {v : Val} {tr : Option Time}
    {extra : View} :
    c' ∈ writeSuccs A tid iv c k xcl l v tr extra xr ↔
      (∃ t ∈ c.prom, c.mem.get? t = some { loc := l, val := v, tid } ∧
        writeOk tid iv c (A.storeKind k) l tr extra t = true ∧
        c' = afterWrite A iv c (A.storeKind k) xcl l v t (writeFwd iv extra) true xr) ∨
      (writeOk tid iv c (A.storeKind k) l tr extra (c.mem.last + 1) = true ∧
        c' = afterWrite A iv (promiseNowCtx tid iv c (A.storeKind k) l v extra) (A.storeKind k) xcl l v
          (c.mem.last + 1) (writeFwd iv extra) false xr) := by
  unfold writeSuccs writeOk writePre promiseNowCtx writeFwd
  rw [List.mem_append, List.mem_filterMap]
  apply or_congr
  · constructor
    · rintro ⟨t, ht, h⟩
      cases hg : c.mem.get? t with
      | none => simp [hg] at h
      | some w =>
        simp only [hg] at h
        rw [Option.ite_none_right_eq_some] at h
        obtain ⟨hc, h⟩ := h
        obtain rfl := Option.some.inj h
        rw [Bool.and_eq_true] at hc
        obtain ⟨hw, hok⟩ := hc
        have hw' := (msg_beq_iff tid).mp hw
        subst hw'
        exact ⟨t, ht, hg, hok, rfl⟩
    · rintro ⟨t, ht, hg, hok, rfl⟩
      refine ⟨t, ht, ?_⟩
      simp only [hg]
      rw [Option.ite_none_right_eq_some]
      refine ⟨?_, rfl⟩
      rw [Bool.and_eq_true]
      exact ⟨(msg_beq_iff tid).mpr rfl, hok⟩
  · cases tr <;> simp [writePre, Memory.append, Memory.last, List.mem_ite_nil_right] <;> intros <;>
      exact decide_eq_decide.mpr Iff.rfl

end Write

/-! ## Run level: one lemma per tree shape -/

section Run

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- TSO's `fence .sy` around an RMW (`Arch.rmwFence`); the identity on ARM. -/
def rmwFenceOpt (c : Ctx) : Ctx := if A.rmwFence then fenceStep c .sy else c

/-- The acquire-release bump after an RMW's write (`k` effective): an
acquire-release RMW that returns its value orders everything after it after
its write. -/
def rmwBump (k : RmwKind) (noRet : Bool) (l : Loc) (c : Ctx) : Ctx :=
  if k == .acqRel && !noRet then
    { c with views := { c.views with vrNew := max c.views.vrNew (c.views.getCoh l),
                                     vwNew := max c.views.vwNew (c.views.getCoh l) } }
  else c

theorem run_done_iff {σ : Type} {c c' : Ctx} {s st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.done s) ↔ st = s ∧ c' = c := by
  simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]

/-- **A load**: one read (`readSuccs`, closed form `mem_readSuccs`). -/
theorem run_load_iff {σ : Type} {c c' : Ctx} {k : LoadKind} {xcl : Bool} {l : Loc} {f : Val → σ} {st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.load k xcl l fun v => .done (f v)) ↔
      ∃ ts v, (ts, v, c') ∈ readSuccs A iv c k xcl l ∧ st = f v := by
  simp only [runTree, List.mem_flatMap, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨ts, v, c1⟩, hx, rfl, rfl⟩; exact ⟨ts, v, hx, rfl⟩
  · rintro ⟨ts, v, hx, rfl⟩; exact ⟨(ts, v, c'), hx, rfl, rfl⟩

/-- **A non-exclusive store**: one write (`writeSuccs`, closed form
`mem_writeSuccs_iff`), with the store's own data views. -/
theorem run_store_iff {σ : Type} {c c' : Ctx} {k : StoreKind} {l : Loc} {v : Val} {s st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.store k false l v fun _ => .done s) ↔
      st = s ∧ c' ∈ writeSuccs A tid (iv.forStore c.stores) c k false l v none := by
  simp only [runTree, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.mem_flatMap,
    List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨c1, h1, rfl, rfl⟩; exact ⟨rfl, h1⟩
  · rintro ⟨rfl, h1⟩; exact ⟨c', h1, rfl, rfl⟩

/-- **A fence**: `fenceStep`, no memory access. -/
theorem run_fence_iff {σ : Type} {c c' : Ctx} {k : FenceKind} {s st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.fence k fun _ => .done s) ↔ st = s ∧ c' = fenceStep c k := by
  simp only [runTree, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq]

/-- **An RMW** (any `Arch`, any operation, `noRet` either way): one atomic
read; then no write (`op old = none`, a failed compare), or one exclusive
write paired with the read (`writeSuccs … true l new (some tr)`), its data
view joined with the read's post-view. -/
theorem run_rmw_iff {σ : Type} {c c' : Ctx} {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val}
    {f : Val → σ} {st : σ} :
    .ok (st, c') ∈ runTree A tid iv c (.rmw k noRet l op fun v => .done (f v)) ↔
      ∃ tr old c1, (tr, old, c1) ∈ readSuccs A iv (rmwFenceOpt A c)
          (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet ∧ st = f old ∧
        ((op old = none ∧ c' = rmwFenceOpt A c1) ∨
         (∃ new c2, op old = some new ∧
            c2 ∈ writeSuccs A tid iv c1 (A.rmwKind k).storeKind true l new (some tr) (c1.loadViews.getLastD 0) ∧
            c' = rmwFenceOpt A (rmwBump (A.rmwKind k) noRet l { c2 with rmwWrote := true }))) := by
  simp only [runTree, List.mem_flatMap]
  constructor
  · rintro ⟨⟨tr, old, c1⟩, hx, h⟩
    refine ⟨tr, old, c1, hx, ?_⟩
    dsimp only at h
    cases hop : op old with
    | none =>
      simp only [hop, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.1, .inl ⟨rfl, h.2⟩⟩
    | some new =>
      simp only [hop, List.mem_flatMap, List.mem_singleton, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨c2, h2, rfl, rfl⟩ := h
      exact ⟨rfl, .inr ⟨new, c2, rfl, h2, rfl⟩⟩
  · rintro ⟨tr, old, c1, hx, rfl, h⟩
    refine ⟨(tr, old, c1), hx, ?_⟩
    dsimp only
    rcases h with ⟨hop, rfl⟩ | ⟨new, c2, hop, h2, rfl⟩
    · simp only [hop, List.mem_singleton]; rfl
    · simp only [hop, List.mem_flatMap, List.mem_singleton]
      exact ⟨c2, h2, rfl⟩

/-- **A finite choice** (`choose n k`): a run of one branch. -/
theorem run_choose_iff {σ : Type} {c : Ctx} {n : Nat} {k : Fin n → EvTree σ} {x : Except String (σ × Ctx)} :
    x ∈ runTree A tid iv c (.choose n k) ↔ ∃ i, x ∈ runTree A tid iv c (k i) := by
  simp only [runTree, List.mem_flatMap, List.mem_finRange, true_and]

end Run

/-! ## Machine level: `InstrSemInf` -/

section Machine

variable (A : Arch) (tid : Nat)

/-- **The thread rules' outcomes of one instruction** whose tree is `tree`:
a run of the tree from `stepOne`'s context, finished by `finishInstr` (the
register views of the destinations and, for a branch, `vCAP`), with the
memory the run leaves. -/
def RunOut (t : Thread I) (mem : Memory) (tree : EvTree I.State) (th : Thread I) (mem' : Memory) : Prop :=
  ∃ st c', .ok (st, c') ∈ runTree A tid (instrViews t (I.deps t.st)) (ctx0 tid t mem) tree ∧
    th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) st c' ∧ mem' = c'.mem

/-- **`stepOne`'s successful outcomes are the `RunOut` outcomes.** -/
theorem stepOne_ok_iff {t : Thread I} {mem : Memory} {tree : EvTree I.State} (hex : I.exec t.st = some tree)
    {th : Thread I} {mem' : Memory} :
    (∃ outs o, stepOne A t tid mem = some outs ∧ .ok o ∈ outs ∧ o.thread = th ∧ o.mem = mem') ↔
      RunOut A tid t mem tree th mem' := by
  constructor
  · rintro ⟨outs, o, hs, ho, rfl, rfl⟩
    unfold stepOne at hs
    rw [hex] at hs
    have hs' : _ = outs := Option.some.inj hs
    subst hs'
    rw [List.mem_flatMap] at ho
    obtain ⟨r, hr, ho⟩ := ho
    cases r with
    | error m => simp at ho
    | ok p =>
      obtain ⟨st, c'⟩ := p
      simp only [List.mem_map, Except.ok.injEq] at ho
      obtain ⟨th, hth, rfl⟩ := ho
      exact ⟨st, c', hr, hth, rfl⟩
  · rintro ⟨st, c', hr, hth, rfl⟩
    refine ⟨_, ⟨th, c'.mem, c'.promisedNow, c'.log⟩, by unfold stepOne; rw [hex]; rfl, ?_, rfl, rfl⟩
    rw [List.mem_flatMap]
    exact ⟨_, hr, List.mem_map.mpr ⟨th, hth, rfl⟩⟩

/-- **An instruction step on the fuel-free machine, at a thread whose next
instruction has tree `tree`**: a `RunOut` outcome, certifiable
(`CertOk`), installed in the configuration. -/
theorem instrSemInf_iff_of_exec {c c' : Config I} {t : Thread I} {tree : EvTree I.State}
    (ht : c.threads[tid]? = some t) (hex : I.exec t.st = some tree) :
    InstrSemInf A tid c c' ↔ ∃ th mem', RunOut A tid t c.mem tree th mem' ∧ CertOk A tid th mem' ∧
      c' = c.withThread tid th mem' := by
  constructor
  · rintro ⟨t', outs, o, ht', hs, ho, hc, rfl⟩
    obtain rfl : t' = t := Option.some.inj (ht'.symm.trans ht)
    exact ⟨o.thread, o.mem, (stepOne_ok_iff A tid hex).mp ⟨outs, o, hs, ho, rfl, rfl⟩, hc, rfl⟩
  · rintro ⟨th, mem', hr, hc, rfl⟩
    obtain ⟨outs, o, hs, ho, rfl, rfl⟩ := (stepOne_ok_iff A tid hex).mpr hr
    exact ⟨t, outs, o, ht, hs, ho, hc, rfl⟩

variable {c c' : Config I} {t : Thread I} (ht : c.threads[tid]? = some t)

include ht

/-- **A no-event instruction** (`exec = some (.done s)`): the outcome is
`finishInstr` at the thread's own context; memory unchanged. -/
theorem instrSemInf_done_iff {s : I.State} (hex : I.exec t.st = some (.done s)) :
    InstrSemInf A tid c c' ↔ ∃ th, th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s
        (ctx0 tid t c.mem) ∧ CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  rw [instrSemInf_iff_of_exec A tid ht hex]
  constructor
  · rintro ⟨th, mem', ⟨st, c1, hr, hth, rfl⟩, hc, rfl⟩
    obtain ⟨rfl, rfl⟩ := (run_done_iff A tid _).mp hr
    exact ⟨th, hth, hc, rfl⟩
  · rintro ⟨th, hth, hc, rfl⟩
    exact ⟨th, c.mem, ⟨s, _, (run_done_iff A tid _).mpr ⟨rfl, rfl⟩, hth, rfl⟩, hc, rfl⟩

/-- **The source-stutter case**: a step at a `.done s` tree changes only the
thread's local state. The memory and the promise set are unchanged, the
state becomes `s`, and the views are the thread's own, but for `vCAP`, which
a branch raises by its condition registers' view; only the register views
(`rview`/`wview`) change otherwise. -/
theorem instrSemInf_done_stutter {s : I.State} (hex : I.exec t.st = some (.done s))
    (h : InstrSemInf A tid c c') :
    ∃ th, c' = c.withThread tid th c.mem ∧ th.st = s ∧ th.prom = t.prom ∧
      (th.views = t.views ∨
        th.views = { t.views with vCAP := max t.views.vCAP (instrViews t (I.deps t.st)).condW }) ∧
      CertOk A tid th c.mem := by
  obtain ⟨th, hth, hc, rfl⟩ := (instrSemInf_done_iff A tid ht hex).mp h
  exact ⟨th, rfl, finishInstr_st hth, (finishInstr_relKey hth).1, CertCut.finishInstr_views hth, hc⟩

/-- **A load instruction** (`exec = some (.load k xcl l fun v => .done (f v))`):
one read of `l` (`mem_readSuccs`: at a readable timestamp `ts`, the context
`readNext`); memory and promises unchanged. -/
theorem instrSemInf_load_iff {k : LoadKind} {xcl : Bool} {l : Loc} {f : Val → I.State}
    (hex : I.exec t.st = some (.load k xcl l fun v => .done (f v))) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (instrViews t (I.deps t.st)) (ctx0 tid t c.mem) k xcl l ∧
      th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) (f v) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem := by
  rw [instrSemInf_iff_of_exec A tid ht hex]
  constructor
  · rintro ⟨th, mem', ⟨st, c1, hr, hth, rfl⟩, hc, rfl⟩
    obtain ⟨ts, v, hx, rfl⟩ := (run_load_iff A tid _).mp hr
    exact ⟨ts, v, c1, th, hx, hth, hc, rfl⟩
  · rintro ⟨ts, v, c1, th, hx, hth, hc, rfl⟩
    exact ⟨th, c1.mem, ⟨f v, c1, (run_load_iff A tid _).mpr ⟨ts, v, hx, rfl⟩, hth, rfl⟩, hc, rfl⟩

/-- **A non-exclusive store instruction**: one write of `l := v`
(`mem_writeSuccs_iff`: fulfil or promise now). -/
theorem instrSemInf_store_iff {k : StoreKind} {l : Loc} {v : Val} {s : I.State}
    (hex : I.exec t.st = some (.store k false l v fun _ => .done s)) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((instrViews t (I.deps t.st)).forStore 0) (ctx0 tid t c.mem) k false l v none ∧
      th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem := by
  rw [instrSemInf_iff_of_exec A tid ht hex]
  constructor
  · rintro ⟨th, mem', ⟨st, c1, hr, hth, rfl⟩, hc, rfl⟩
    obtain ⟨rfl, hw⟩ := (run_store_iff A tid _).mp hr
    exact ⟨c1, th, hw, hth, hc, rfl⟩
  · rintro ⟨c1, th, hw, hth, hc, rfl⟩
    exact ⟨th, c1.mem, ⟨s, c1, (run_store_iff A tid _).mpr ⟨rfl, hw⟩, hth, rfl⟩, hc, rfl⟩

/-- **A fence instruction**: `fenceStep`; memory and promises unchanged. -/
theorem instrSemInf_fence_iff {k : FenceKind} {s : I.State}
    (hex : I.exec t.st = some (.fence k fun _ => .done s)) :
    InstrSemInf A tid c c' ↔ ∃ th,
      th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) s (fenceStep (ctx0 tid t c.mem) k) ∧
      CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem := by
  rw [instrSemInf_iff_of_exec A tid ht hex]
  have hm : (fenceStep (ctx0 tid t c.mem) k).mem = c.mem := (SLR.fenceStep_mem_prom _ k).1
  constructor
  · rintro ⟨th, mem', ⟨st, c1, hr, hth, rfl⟩, hc, rfl⟩
    obtain ⟨rfl, rfl⟩ := (run_fence_iff A tid _).mp hr
    exact ⟨th, hth, hm ▸ hc, by rw [hm]⟩
  · rintro ⟨th, hth, hc, rfl⟩
    exact ⟨th, c.mem, ⟨s, _, (run_fence_iff A tid _).mpr ⟨rfl, rfl⟩, hth, hm.symm⟩, hc, rfl⟩

/-- **An RMW instruction** (any `Arch`): one atomic read, then no write or
one paired write (`run_rmw_iff`). -/
theorem instrSemInf_rmw_iff {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val}
    {f : Val → I.State} (hex : I.exec t.st = some (.rmw k noRet l op fun v => .done (f v))) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (instrViews t (I.deps t.st)) (rmwFenceOpt A (ctx0 tid t c.mem))
          (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet ∧
      ((op old = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, op old = some new ∧
          c2 ∈ writeSuccs A tid (instrViews t (I.deps t.st)) c1 (A.rmwKind k).storeKind true l new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) noRet l { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (I.deps t.st) (instrViews t (I.deps t.st)) (f old) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem := by
  rw [instrSemInf_iff_of_exec A tid ht hex]
  constructor
  · rintro ⟨th, mem', ⟨st, cf, hr, hth, rfl⟩, hc, rfl⟩
    obtain ⟨tr, old, c1, hx, rfl, h⟩ := (run_rmw_iff A tid _).mp hr
    exact ⟨tr, old, c1, cf, th, hx, h, hth, hc, rfl⟩
  · rintro ⟨tr, old, c1, cf, th, hx, h, hth, hc, rfl⟩
    exact ⟨th, cf.mem, ⟨f old, cf, (run_rmw_iff A tid _).mpr ⟨tr, old, c1, hx, rfl, h⟩, hth, rfl⟩, hc, rfl⟩

end Machine

end Kraken.Promising.Lower

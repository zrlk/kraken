/-
The interface of the `EnvG` environment's steps. ISA-neutral.

Two layers, one per access kind:

- **Outcomes** (`LoadOut`, `StoreOut`, `RmwOut`, `FenceOut`): exactly the
  outcomes `EnvG`'s `step` offers (`EnvG/Env.lean` defines `step` as these).
  Each runs the access with the machine's own rule (`readSuccs`,
  `writeSuccs`, `fenceStep`) on `envCtx` at an admissible re-anchor
  (`AnchorOk`), with `iv0`. The link produces these from the per-node
  simulation lemmas.
- **Facts** (`LoadFacts`, `StoreFacts`, `RmwFacts`, `FenceFacts`): what a
  step exposes to a program proof, without raw `readSuccs`/`writeSuccs`:
  the value read and its read window, view lower bounds, the resource and
  ghost effect, `seen`, the fence bits. `EnvG/Env.lean` proves
  `step_loadFacts` etc.: every outcome satisfies its facts.

The resource after a write is
`∃ P, (σ.cl → P) ∧ σ'.r = Plan.after(Rmw) … P σ.r` (a release split's
knowledge is fixed at its prepay, see `EnvG/State.lean` §Release splits),
and a successful RMW exposes that the message it read is unclaimed at the
anchor ghost (`¬ σ'.g.Claimed (l, tr)`, the claim fix).

`Anchor` (re-anchoring without an access) is in `EnvG/State.lean`.

Exclusive stores are refused (LL/SC is deferred); `noRet` RMWs are not
offered (live RMWs only, §1c: `TreeJ.live` in `EnvG/Live.lean`). Phase 1:
single-access trees only.
-/
import Kraken.Promising.SLR.EnvG.State

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## View vocabulary -/

/-- Pointwise order on the view components a program proof reasons about
(coherence and the scalar views; not `fwdb`/`xclb`). -/
structure VLe (a b : Views) : Prop where
  coh : ∀ l, a.getCoh l ≤ b.getCoh l
  vrNew : a.vrNew ≤ b.vrNew
  vrOld : a.vrOld ≤ b.vrOld
  vrOldNR : a.vrOldNR ≤ b.vrOldNR
  vwNew : a.vwNew ≤ b.vwNew
  vwOld : a.vwOld ≤ b.vwOld
  vwOldNT : a.vwOldNT ≤ b.vwOldNT
  vCAP : a.vCAP ≤ b.vCAP
  vRel : a.vRel ≤ b.vRel

theorem VLe.refl (a : Views) : VLe a a :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
    Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem VLe.trans {a b c : Views} (h₁ : VLe a b) (h₂ : VLe b c) : VLe a c :=
  ⟨fun l => Nat.le_trans (h₁.coh l) (h₂.coh l), Nat.le_trans h₁.vrNew h₂.vrNew, Nat.le_trans h₁.vrOld h₂.vrOld,
    Nat.le_trans h₁.vrOldNR h₂.vrOldNR, Nat.le_trans h₁.vwNew h₂.vwNew, Nat.le_trans h₁.vwOld h₂.vwOld,
    Nat.le_trans h₁.vwOldNT h₂.vwOldNT, Nat.le_trans h₁.vCAP h₂.vCAP, Nat.le_trans h₁.vRel h₂.vRel⟩

/-- The read lower bound of a load of kind `k` (as `readSuccs` applies
`A.loadKind`) of `l` from views `vs`, with no instruction views: a load may
read `tr` only if no write to `l` lies in `(tr, readBound]`. -/
def readBound (A : Arch) (vs : Views) (k : LoadKind) (l : Loc) : View :=
  max (max vs.vrNew (if A.loadKind k == .acq then vs.vRel else 0)) (vs.getCoh l)

/-- The forwarding buffer of `l` holds the timestamp `tr` (the thread's own
write): such a read may take the forwarding view instead of `tr`. -/
def Fwded (vs : Views) (l : Loc) (tr : Time) : Prop := ∃ f, vs.getFwd l = some f ∧ f.time = tr

/-- The views an RMW reads from: the full fence first if the architecture's
RMWs are fences (TSO). -/
def rmwReadViews (A : Arch) (vs : Views) : Views := if A.rmwFence then fenceViews vs .sy else vs

/-! ## Outcomes: what `step` is -/

/-- **A load outcome**: at an admissible re-anchor `(σ'.snap, σ'.g)`, a
`readSuccs` outcome on `envCtx` with value `v`; the env's views become the
outcome's, the resource is unchanged, `cl` gains the clean erasure at the
anchor, `seen` records an acquire-type read, and `fencedR` clears. -/
def LoadOut (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (xcl : Bool) (l : Loc) (v : Val) : Prop :=
  AnchorOk tid σ σ'.snap σ'.g ∧ σ'.r = σ.r ∧ σ'.cl = (σ.cl ∧ ClAt tid σ.r σ'.g σ'.snap) ∧
    ∃ tr cx', (tr, v, cx') ∈ readSuccs A iv0 (envCtx tid σ.vs σ'.snap) k xcl l ∧ σ'.vs = cx'.views ∧
      σ'.seen = seenAfter A k σ σ'.g l tr ∧ σ'.fencedR = false ∧ σ'.fencedW = σ.fencedW

/-- **A store outcome** (non-exclusive): at an admissible re-anchor
`(c, σ'.g)`, a `writeSuccs` outcome `cx'` on `envCtx` at `tw` that overtakes
no own promise; a planned release is fresh or fulfils a pending promise (a
release fulfilling an old non-pending promise is not offered: the link rules
it out by the impurity `ok` asks for). The snapshot becomes the post-write
configuration, the views `cx'`'s, the resource `Plan.after`; `fencedW` clears. -/
def StoreOut (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : StoreKind) (xcl : Bool) (l : Loc)
    (v : Val) (b : Bool) : Prop :=
  xcl = false ∧ b = true ∧ ∃ (c : Config I) (cx' : Ctx) (tw : Time), AnchorOk tid σ c σ'.g ∧
    cx' ∈ writeSuccs A tid iv0 (envCtx tid σ.vs c) k false l v none ∧
    WriteEv tid (envCtx tid σ.vs c) cx' l v none tw ∧ ¬ cx'.Overtaken ∧
    (pl.rel l v = true → tw ∉ ownProm tid c ∨ tw ∈ σ'.g.pend) ∧
    σ'.snap = snapAfter tid c cx' ∧ σ'.vs = cx'.views ∧ (∃ P : Prop, (σ.cl → P) ∧ σ'.r = pl.after l v tw P σ.r) ∧ σ'.cl = σ.cl ∧
    σ'.seen = σ.seen ∧ σ'.fencedR = σ.fencedR ∧ σ'.fencedW = false

/-- **An RMW outcome** (live: `noRet = false`): at an admissible re-anchor
`(c, σ'.g)`, a `readSuccs` outcome `x` of the RMW's read on
`fenceOptCtx A (envCtx …)` with value `old`; then either the operation fails
(the read's context, after the optional fence) or a `writeSuccs` outcome `cx'`
at `tw` that overtakes no own promise, with the virtual resource
`Plan.afterRmw` (claimed update slots at the anchor ghost), the message read
not yet claimed at the anchor ghost (`Erase.not_claimed`). Both fence bits
clear; `seen` records an acquire-type read. -/
def RmwOut (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ (c : Config I) (x : Time × Val × Ctx), AnchorOk tid σ c σ'.g ∧
    x ∈ readSuccs A iv0 (fenceOptCtx A (envCtx tid σ.vs c)) (A.rmwKind k).loadKind false l false ∧ x.2.1 = old ∧
    σ'.cl = σ.cl ∧ σ'.seen = seenAfter A (A.rmwKind k).loadKind σ σ'.g l x.1 ∧
    σ'.fencedR = false ∧ σ'.fencedW = false ∧
    ((op old = none ∧ σ'.snap = c ∧ σ'.vs = (fenceOptCtx A x.2.2).views ∧ σ'.r = σ.r) ∨
     (∃ (new : Val) (cx' : Ctx) (tw : Time), op old = some new ∧
       cx' ∈ writeSuccs A tid iv0 x.2.2 (A.rmwKind k).storeKind true l new (some x.1) (x.2.2.loadViews.getLastD 0) ∧
       WriteEv tid x.2.2 cx' l new (some x.1) tw ∧ ¬ cx'.Overtaken ∧
       (pl.rel l new = true → tw ∉ ownProm tid c ∨ tw ∈ σ'.g.pend) ∧
       σ'.snap = snapAfter tid c cx' ∧ σ'.vs = (rmwAfter A k false l cx').views ∧
       (∃ P : Prop, (σ.cl → P) ∧ σ'.r = pl.afterRmw l new x.1 tw σ'.g P σ.r) ∧ ¬ σ'.g.Claimed (l, x.1)))

/-- **A fence outcome** (deterministic, no re-anchor): `fenceStep` on the
views, the bits set per §3 (`.sy` both, `.st`/`.stAll` `fencedW`, `.ld` and
`.isb` neither). -/
def FenceOut (σ σ' : State I) (k : FenceKind) : Prop :=
  σ' = { σ with vs := fenceViews σ.vs k, fencedR := fenceSetsR k || σ.fencedR,
                fencedW := fenceSetsW k || σ.fencedW }

/-! ## Facts: what a step exposes -/

/-- **The read** of `v` from `(l, tr)` at anchor `c` with views `vs`: the
message's value, not an own outstanding promise, inside the read window (the
three hypotheses of `read_max_gen`/`read_max_slot`, with `B = readBound`). -/
structure ReadAt (A : Arch) (tid : Nat) (vs : Views) (c : Config I) (k : LoadKind) (l : Loc) (tr : Time)
    (v : Val) : Prop where
  val : c.mem.read? l tr = some v
  notOwn : (ownProm tid c).contains tr = false
  window : c.mem.writeIn l tr (readBound A vs k l) = false

/-- **The views after a load** of kind `k` reading `(l, tr)`, from `vs` to
`vs'`: they only grow; `vwOld`, `vRel` and the forwarding buffers are
unchanged; unless the read is forwarded from an own write at `tr`, `coh l`
and `vrOld` reach `tr`, and for an acquire-type load `vrNew` and `vwNew` too. -/
structure LoadViews (A : Arch) (vs vs' : Views) (k : LoadKind) (l : Loc) (tr : Time) : Prop where
  mono : VLe vs vs'
  vwOld : vs'.vwOld = vs.vwOld
  vRel : vs'.vRel = vs.vRel
  fwdb : vs'.fwdb = vs.fwdb
  coh : ¬ Fwded vs l tr → tr ≤ vs'.getCoh l
  vrOld : ¬ Fwded vs l tr → tr ≤ vs'.vrOld
  acq : (A.loadKind k).isAcquire = true → ¬ Fwded vs l tr → tr ≤ vs'.vrNew ∧ tr ≤ vs'.vwNew

/-- **Where a write lands**: from anchor `c` to snapshot `c'`, a write of `v`
to `l` at `tw` by thread `tid` either fulfils an own outstanding promise (the
memory is unchanged) or appends (`tw = |M| + 1`); the thread's promise list
loses `tw`, other threads are unchanged. -/
structure WriteSnap (tid : Nat) (c c' : Config I) (l : Loc) (v : Val) (tw : Time) : Prop where
  mem : (c'.mem = c.mem ∧ c.mem.get? tw = some ⟨l, v, tid⟩ ∧ tw ∈ ownProm tid c) ∨
    (c'.mem = (c.mem.append ⟨l, v, tid⟩).1 ∧ tw = c.mem.last + 1)
  threads : c'.threads = c.threads.modify tid (fun t => { t with prom := (ownProm tid c).erase tw })

/-- **The bound a write at `tw` clears** (the `bound < t` of `writeSuccs`,
with no instruction views): above `vwNew`, `vCAP` and `coh l`, and for a
release store (`A.storeKind k = .rel`) above `vrOld`, `vrOldNR`, `vwOld`.
(A fence-release has no extra bound here: after the fence, `FenceFacts`
gives `vwNew` above the old views.) -/
structure WriteBound (A : Arch) (vs : Views) (k : StoreKind) (l : Loc) (tw : Time) : Prop where
  vwNew : vs.vwNew < tw
  vCAP : vs.vCAP < tw
  coh : vs.getCoh l < tw
  rel : A.storeKind k = .rel → max (max vs.vrOld vs.vrOldNR) vs.vwOld < tw

/-- **The views after a write** at `tw` (store kind `k`): they only grow;
`coh l` reaches `tw`, and (unless non-temporal) `vwOld`; the forwarding
buffer of `l` holds `tw`, the others are unchanged. -/
structure WriteViews (A : Arch) (vs vs' : Views) (k : StoreKind) (l : Loc) (tw : Time) : Prop where
  mono : VLe vs vs'
  coh : tw ≤ vs'.getCoh l
  vwOld : A.storeKind k ≠ .nt → tw ≤ vs'.vwOld
  fwd : ∃ f, vs'.getFwd l = some f ∧ f.time = tw
  fwdOther : ∀ l', l' ≠ l → vs'.getFwd l' = vs.getFwd l'

/-- **What a load exposes** (`step_loadFacts`). -/
def LoadFacts (A : Arch) (tid : Nat) (σ σ' : State I) (k : LoadKind) (l : Loc) (v : Val) : Prop :=
  AnchorOk tid σ σ'.snap σ'.g ∧ σ'.r = σ.r ∧ σ'.cl = (σ.cl ∧ ClAt tid σ.r σ'.g σ'.snap) ∧
    ∃ tr, ReadAt A tid σ.vs σ'.snap k l tr v ∧ LoadViews A σ.vs σ'.vs k l tr ∧
      σ'.seen = seenAfter A k σ σ'.g l tr ∧ σ'.fencedR = false ∧ σ'.fencedW = σ.fencedW

/-- **What a store exposes** (`step_storeFacts`): the write's anchor and
landing, its bound and views, the resource `Plan.after` (the same for a
fresh and a pending write), a planned release is fresh or pending, `cl` and
`seen` are unchanged, `fencedW` clears. -/
def StoreFacts (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : StoreKind) (l : Loc) (v : Val) :
    Prop :=
  ∃ (c : Config I) (tw : Time), AnchorOk tid σ c σ'.g ∧ WriteSnap tid c σ'.snap l v tw ∧
    WriteBound A σ.vs k l tw ∧ WriteViews A σ.vs σ'.vs k l tw ∧
    (pl.rel l v = true → tw = c.mem.last + 1 ∨ tw ∈ σ'.g.pend) ∧
    (∃ P : Prop, (σ.cl → P) ∧ σ'.r = pl.after l v tw P σ.r) ∧ σ'.cl = σ.cl ∧ σ'.seen = σ.seen ∧
    σ'.fencedR = σ.fencedR ∧ σ'.fencedW = false

/-- **What an RMW exposes** (`step_rmwFacts`): the read (from the RMW's read
views) as for a load; on failure the resource is unchanged and the snapshot
is the anchor; on success the write as for a store, after the read
(`tr < tw`, atomic), with resource `Plan.afterRmw` and `(l, tr)` unclaimed at
the anchor ghost. Both fence bits clear. -/
def RmwFacts (A : Arch) (tid : Nat) (pl : Plan) (σ σ' : State I) (k : RmwKind) (l : Loc)
    (op : Val → Option Val) (old : Val) : Prop :=
  ∃ (c : Config I) (tr : Time), AnchorOk tid σ c σ'.g ∧
    ReadAt A tid (rmwReadViews A σ.vs) c (A.rmwKind k).loadKind l tr old ∧
    VLe σ.vs σ'.vs ∧ σ'.cl = σ.cl ∧ σ'.seen = seenAfter A (A.rmwKind k).loadKind σ σ'.g l tr ∧
    σ'.fencedR = false ∧ σ'.fencedW = false ∧
    ((A.loadKind (A.rmwKind k).loadKind).isAcquire = true → ¬ Fwded σ.vs l tr →
      tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew) ∧
    ((op old = none ∧ σ'.snap = c ∧ σ'.r = σ.r) ∨
     (∃ (new : Val) (tw : Time), op old = some new ∧ tr < tw ∧ c.mem.atomic l tid tr tw = true ∧
       WriteSnap tid c σ'.snap l new tw ∧ WriteBound A σ.vs (A.rmwKind k).storeKind l tw ∧
       tw ≤ σ'.vs.getCoh l ∧ (A.storeKind (A.rmwKind k).storeKind ≠ .nt → tw ≤ σ'.vs.vwOld) ∧
       (pl.rel l new = true → tw = c.mem.last + 1 ∨ tw ∈ σ'.g.pend) ∧
       (∃ P : Prop, (σ.cl → P) ∧ σ'.r = pl.afterRmw l new tr tw σ'.g P σ.r) ∧ ¬ σ'.g.Claimed (l, tr)))

/-- **What a fence exposes** (`step_fenceFacts`): the outcome itself (it is
deterministic). -/
def FenceFacts (σ σ' : State I) (k : FenceKind) : Prop := FenceOut σ σ' k

/-! ## `WriteSnap` messages -/

/-- A `WriteSnap` keeps the old messages (from `EnvG/TicketLockVC.lean`). -/
theorem WriteSnap.get?_old' {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) {ts : Time} {w : Msg} (hw : c.mem.get? ts = some w) : c'.mem.get? ts = some w := by
  rcases h.mem with ⟨hm, -⟩ | ⟨hm, -⟩
  · rw [hm]; exact hw
  · rw [hm]; exact Memory.get?_of_prefix (by simp [Memory.append, Array.toList_push]) hw

/-- A `WriteSnap`'s message is at its timestamp (from
`EnvG/TicketLockVC.lean`). -/
theorem WriteSnap.get?_new' {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) : c'.mem.get? tw = some ⟨l, v, tid⟩ := by
  rcases h.mem with ⟨hm, hg, -⟩ | ⟨hm, rfl⟩
  · rw [hm]; exact hg
  · rw [hm]; exact Memory.get?_append_last _ _

end Kraken.Promising.SLR.EnvG

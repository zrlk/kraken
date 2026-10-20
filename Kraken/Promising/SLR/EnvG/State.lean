/-
The whole-thread SLR environment `EnvG`: the environment **state** and the static vocabulary shared by the
facts (`EnvG/Facts.lean`), the environment (`EnvG/Env.lean`), the plan
(`EnvG/Plan.lean`) and the link. ISA-neutral.

## The state

`EnvG.State I` is a *lower bound* on the actual thread and world, re-extended
at every access (§1a):

- `snap`: a configuration the actual one extends (`SnapLe`), the anchor of the
  last access;
- `vs`: lower bounds of the thread's views (no register views, §1b);
- `r`: the thread's **virtual** resource (the actual one plus the resources of
  its pending prepaid releases, §1d);
- `g`: a ghost state the actual one extends (`Ghost.Le`: release predicates,
  acquire table, update ids);
- `cl`: accumulated knowledge under the clean (`T = ⊥`) erasure, the `cl` of
  `ThreadRuleRX`;
- `seen`: messages read by an acquire-type access, with the acquire ids the
  thread held then (§2.2, read side only);
- `fencedR`, `fencedW`: the fence ghost bits (§3).

## Re-anchoring

The anchor relation is `SnapLe`, not `EnvExt`: the thread's own entry in the
snapshot is the thread *at the last access*, and the thread's state (pc,
registers, views) changes at every instruction, so only its promise list is
tracked (it grows by own promises above the snapshot's memory). Memory grows
by a prefix, as in `EnvExt`; other threads are unconstrained, as in `EnvExt`.

`AnchorOk tid σ c g` is the admissibility of a re-anchor `(c, g)` of `σ`,
which every `ok`/`step` quantifies over.

Phase 1 covers single-access event trees only (§1b caveat): the instruction
views of every access are `iv0` and the instruction-local `Ctx` fields are
reset at every access (`envCtx`).

## Release splits (F1)

A plan entry may carry a `Plan.Split`: what its release gives away and keeps
as functions of `(cl, r)`, with the laws `op_eq` (exact) and `pos` (a positive
share of the written location stays) as fields, so `Plan.Valid` stays
decidable. Without a split (`split := none`, the default) the entry gives its
`gives` locations whole, as before splits. A lock release paying SLR's `Bad`
disjunct with part of its own lock share, by an amount depending on whether
the thread is clean, is a split (generic library: `EnvG/Split.lean`).

**The `cl` of a split is fixed at the prepay.** Between a prepay and its
fulfilling write `σ.cl` only gets stronger, so the env cannot re-read it at
the write. `Inflight` (`EnvG/NodeRel.lean`) records the prepay's knowledge
`P` with `cl → P`, and `StoreOut`/`StoreFacts`/`RmwOut`/`RmwFacts` expose
`∃ P, (σ.cl → P) ∧ σ'.r = Plan.after(Rmw) … P σ.r`: in clean mode the program
gets the exact split, in unclean mode *some* split (both keep a positive
share). `StoreOk`/`RmwOk`/`PrepayGeneric(Rmw)` use `σ.cl`. For whole entries
the `P` is irrelevant (`exists_imp_prop`, `EnvG/Simp.lean`).

**Phase-1 limit:** splits only on store releases. A release RMW's entry must
be whole (`Plan.Whole`, a conjunct of `RmwOk`).
-/
import Kraken.Promising.SLR.RuleShapes
import Kraken.Promising.SLR.ThreadRuleX

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-! ## The state -/

/-- **The `EnvG` state**, ISA-neutral. -/
structure State (I : ISA) where
  /-- The anchor: a configuration the actual one extends (`SnapLe`). -/
  snap : Config I
  /-- Lower bounds of the thread's views. -/
  vs : Views
  /-- The thread's virtual resource (actual plus in-flight prepaid releases). -/
  r : Res
  /-- A ghost state the actual one extends (`Ghost.Le`). -/
  g : Ghost
  /-- Accumulated knowledge under the clean erasure. -/
  cl : Prop
  /-- Messages read by acquire-type accesses, with the acquire ids held. -/
  seen : List (Key × PredId) := []
  /-- A full fence (`.sy`) since the last load or RMW. -/
  fencedR : Bool := false
  /-- A store fence (`.sy`, `.st`, `.stAll`) since the last store or RMW. -/
  fencedW : Bool := false

/-! ## Instruction views and contexts of an access -/

/-- The instruction views of every environment access: none (§1b; forgets
dependencies, which gives weaker conclusions, never none). -/
def iv0 : InstrViews := { addrR := 0, addrW := 0, dataR := 0, dataW := 0, condW := 0 }

@[simp] theorem iv0_forStore (i : Nat) : iv0.forStore i = iv0 := rfl

/-- The promise list of thread `tid` in `c` (`[]` if there is no such thread). -/
def ownProm (tid : Nat) (c : Config I) : List Time := ((c.threads[tid]?).map (·.prom)).getD []

/-- The context an environment access runs on: the env's views, the thread's
promises and the memory of the anchor `c`, instruction-local fields at their
defaults. -/
def envCtx (tid : Nat) (vs : Views) (c : Config I) : Ctx := { views := vs, prom := ownProm tid c, mem := c.mem }

@[simp] theorem envCtx_views (tid : Nat) (vs : Views) (c : Config I) : (envCtx tid vs c).views = vs := rfl
@[simp] theorem envCtx_mem (tid : Nat) (vs : Views) (c : Config I) : (envCtx tid vs c).mem = c.mem := rfl
@[simp] theorem envCtx_prom (tid : Nat) (vs : Views) (c : Config I) :
    (envCtx tid vs c).prom = ownProm tid c := rfl

/-- The snapshot after a write of thread `tid` from anchor `c` to the context
`cx'`: the memory of `cx'`, the thread's promise list that of `cx'`. -/
def snapAfter (tid : Nat) (c : Config I) (cx' : Ctx) : Config I :=
  { threads := c.threads.modify tid (fun t => { t with prom := cx'.prom }), mem := cx'.mem }

/-- The views of `fenceStep` (which changes only views and the log). -/
def fenceViews (vs : Views) (k : FenceKind) : Views :=
  (fenceStep { views := vs, prom := [], mem := default } k).views

theorem fenceStep_views (cx : Ctx) (k : FenceKind) : (fenceStep cx k).views = fenceViews cx.views k := by
  cases k <;> rfl

/-! ## Anchors -/

/-- **The anchor order** `c ⊑ c'` for thread `tid`: the memory grows by a
prefix, and the thread's promise list grows by promises above `c`'s memory.
The thread's other fields and the other threads are unconstrained (§1a; the
difference to `EnvExt` is the thread's non-promise fields). -/
structure SnapLe (tid : Nat) (c c' : Config I) : Prop where
  init : c'.mem.init = c.mem.init
  msgs : c.mem.msgs.toList <+: c'.mem.msgs.toList
  prom : ∀ t, c.threads[tid]? = some t → ∃ t', c'.threads[tid]? = some t' ∧
    ∃ ps : List Time, t'.prom = t.prom ++ ps ∧ ∀ p ∈ ps, c.mem.last < p

/-- **An admissible re-anchor** `(c, g)` of `σ` (§1a): `c` extends the
snapshot, `g` the ghost; validity-free erasure holds at `(c, g)` for some
resource assignment, `c` satisfies the machine invariants, and thread `tid`
exists in `c`. -/
structure AnchorOk (tid : Nat) (σ : State I) (c : Config I) (g : Ghost) : Prop where
  snap : SnapLe tid σ.snap c
  ghost : σ.g.Le g
  erase : ∃ rF, Erase rF g (fun _ => True) c
  mach : c.MachInv
  lt : tid < c.threads.size

/-- **Re-anchoring without an access**: the anchor grows, views, resource,
knowledge, `seen` and fence bits are unchanged. -/
structure Anchor (tid : Nat) (σ σ' : State I) : Prop where
  snap : SnapLe tid σ.snap σ'.snap
  ghost : σ.g.Le σ'.g
  vs : σ'.vs = σ.vs
  r : σ'.r = σ.r
  cl : σ'.cl = σ.cl
  seen : σ'.seen = σ.seen
  fencedR : σ'.fencedR = σ.fencedR
  fencedW : σ'.fencedW = σ.fencedW

/-- The clean-erasure knowledge an access at anchor `(c, g)` adds to `cl`
(the `Erase … (fun _ => False) c` conjunct of `ThreadRuleRX.wp`'s new `cl`),
with the thread holding `r`. -/
def ClAt (tid : Nat) (r : Res) (g : Ghost) (c : Config I) : Prop :=
  ∃ rF, Erase (setRes rF tid r) g (fun _ => False) c

/-! ## Plans (v2) -/

/-- **A resource-dependent release split** at the location `l` written
(F1): what the release gives away and what the thread keeps, as
functions of the thread's clean-erasure knowledge `cl` (the `State.cl` at
the release) and its resource `r`. The split is exact (`op_eq`) and keeps a
positive share of `l` (`pos`), the two laws `Plan.keep_op_give` and
`Plan.keep_q_pos` need. A lock release that gives part of its own lock
share (SLR's `Bad` disjunct) is a split, not a list of whole locations. -/
structure Plan.Split (l : Loc) where
  give : Prop → Res → Res
  keep : Prop → Res → Res
  op_eq : ∀ cl r, (keep cl r).op (give cl r) = r
  pos : ∀ cl r, 0 < (r.wr l).q → 0 < ((keep cl r).wr l).q

/-- One release of a plan: a store or RMW writing `val` (`none`: any value)
to `loc` is a release, and its message carries the thread's whole permission
(fraction, write set and acquire ids) for each location in `gives`, or, with
a `split`, the split's given part (F1; `gives` is then ignored). -/
structure Plan.Entry where
  loc : Loc
  val : Option Val := none
  gives : List Loc
  split : Option (Plan.Split loc) := none

/-- **The ghost plan, v2** (§1d, §3): the angelic choices of SLR's write rules,
as finite data, so that `Plan.Valid` is decidable. The first matching entry
counts. (`EnvSpike.Plan` is v1 and is kept.) -/
structure Plan where
  entries : List Plan.Entry

namespace Plan

/-- The entry for a write of `v` to `l`, if any. -/
def find? (pl : Plan) (l : Loc) (v : Val) : Option Plan.Entry :=
  pl.entries.find? fun e => decide (e.loc = l) && (match e.val with | some w => decide (w = v) | none => true)

/-- A write of `v` to `l` is a planned release. -/
def rel (pl : Plan) (l : Loc) (v : Val) : Bool := (pl.find? l v).isSome

/-- The locations a planned release of `v` to `l` gives away. -/
def gives (pl : Plan) (l : Loc) (v : Val) : List Loc := ((pl.find? l v).map (·.gives)).getD []

end Plan

/-- The part of `r` at the locations `L`. -/
def Res.only (L : List Loc) (r : Res) : Res :=
  ⟨fun x => if x ∈ L then r.wr x else Perm.unit, fun x ι => if x ∈ L then r.acq x ι else 0⟩

/-- The part of `r` outside the locations `L`. -/
def Res.drop (L : List Loc) (r : Res) : Res :=
  ⟨fun x => if x ∈ L then Perm.unit else r.wr x, fun x ι => if x ∈ L then 0 else r.acq x ι⟩

/-- What an entry's release gives away from `r` with knowledge `cl`. -/
def Plan.Entry.give (e : Plan.Entry) (cl : Prop) (r : Res) : Res :=
  match e.split with
  | some s => s.give cl r
  | none => Res.only e.gives r

/-- What an entry's release keeps of `r` with knowledge `cl`. -/
def Plan.Entry.keep (e : Plan.Entry) (cl : Prop) (r : Res) : Res :=
  match e.split with
  | some s => s.keep cl r
  | none => Res.drop e.gives r

namespace Plan

/-- What a planned release of `v` to `l` gives away from `r` (the resource its
slots carry), with clean-erasure knowledge `cl`. -/
def give (pl : Plan) (l : Loc) (v : Val) (cl : Prop) (r : Res) : Res :=
  match pl.find? l v with
  | some e => e.give cl r
  | none => Res.only [] r

/-- What a planned release of `v` to `l` keeps of `r`, with knowledge `cl`. -/
def keep (pl : Plan) (l : Loc) (v : Val) (cl : Prop) (r : Res) : Res :=
  match pl.find? l v with
  | some e => e.keep cl r
  | none => Res.drop [] r

/-- **The virtual resource after a store** of `v` to `l` at `tw`, with
knowledge `cl`: the write set gains the message; a planned release also
gives its part away. The same in the fresh and the pending branch (§1d: the
virtual resource counts a pending release as performed). -/
def after (pl : Plan) (l : Loc) (v : Val) (tw : Time) (cl : Prop) (r : Res) : Res :=
  if pl.rel l v then (pl.keep l v cl r).addW l (v, tw) else r.addW l (v, tw)

/-- **The virtual resource after a successful RMW** reading `(l, tr)` and
writing `v` at `tw`, at ghost `g`, with knowledge `cl`: the claimed update
slots join, then as `after`. -/
def afterRmw (pl : Plan) (l : Loc) (v : Val) (tr tw : Time) (g : Ghost) (cl : Prop) (r : Res) : Res :=
  pl.after l v tw cl (r.op (Res.prod ((claimedSlots g l tr).map (·.res))))

end Plan

/-! ## Fence bits and effective release -/

/-- A fence of kind `k` sets `fencedR`: only the full fence (`.ld` does not
fold `vrOldNR`, §3). -/
def fenceSetsR : FenceKind → Bool
  | .sy => true
  | _ => false

/-- A fence of kind `k` sets `fencedW`: `.sy`, `.st`, `.stAll`. -/
def fenceSetsW : FenceKind → Bool
  | .sy | .st | .stAll => true
  | _ => false

/-- **The effective release kind** of a store of kind `k` in state `σ` (§3):
a release store, or any store after a full fence with no access in between. -/
def effRel (A : Arch) (σ : State I) (k : StoreKind) : Prop :=
  A.storeKind k = .rel ∨ (σ.fencedR = true ∧ σ.fencedW = true)

instance (A : Arch) (σ : State I) (k : StoreKind) : Decidable (effRel A σ k) := by
  unfold effRel; infer_instance

/-- The effective release kind of an RMW of kind `k`: its store kind is a
release (conservative: the RMW's own read is not ordered by an earlier fence
before its write, so the fence bits do not count). -/
def effRelRmw (A : Arch) (k : RmwKind) : Prop := A.storeKind (A.rmwKind k).storeKind = .rel

instance (A : Arch) (k : RmwKind) : Decidable (effRelRmw A k) := by
  unfold effRelRmw; infer_instance

/-! ## `seen` -/

/-- **`seen` after a load** of kind `k` (as `readSuccs` applies `A.loadKind`)
reading `(l, tr)`, at ghost `g`: an acquire-type load records the message with
every acquire id of `l` the thread holds (§2.2). -/
def seenAfter (A : Arch) (k : LoadKind) (σ : State I) (g : Ghost) (l : Loc) (tr : Time) : List (Key × PredId) :=
  if (A.loadKind k).isAcquire then σ.seen ++ (g.acqIds σ.r.acq l).map (fun ι => ((l, tr), ι)) else σ.seen

end Kraken.Promising.SLR.EnvG

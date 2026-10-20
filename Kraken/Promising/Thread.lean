/-
Promising-ARM/RISC-V for Kraken: thread state and the thread-local rules.

Follows Fig. 5 of Pulte et al. (PLDI 2019). The rules are written as an
executable successor enumerator over an instruction's event tree; the
relational presentation lives in `Kraken.Promising.Rel`.

A thread executes one *instruction* per step. The instruction's event tree
(`EvTree`) may contain several memory events (an `LDP`, a `CAS`), each
interpreted by the read/fulfil rules with the instruction's address and data
views, which come from the register views of the instruction's syntactic
dependencies (`InstrDeps`). When the tree is `done`, the register views of
the instruction's destinations are updated.
-/
import Kraken.Promising.Basic

namespace Kraken.Promising

/-! ## Thread state -/

/-- `fwdb(l)`: the last write of this thread to `l`, for store forwarding.
`xclRead` is, for a successful store exclusive, its paired load exclusive's
post-view, which an acquire load forwarding from the write also takes
(`readView`); `0` for every other write. -/
structure FwdItem where
  time : Time
  view : View
  xcl : Bool
  xclRead : View := 0
  deriving Repr, BEq, Hashable, Inhabited

/-- The view components of a thread (`TState` without `prom` and `regs`). -/
structure Views where
  coh : List (Loc × View) := []
  vrNew : View := 0
  vrOld : View := 0
  /-- `vrOld` for herd's `NoRet` reads (an RMW whose value read is discarded):
  folded in by `fence .sy` and by a release write's pre-view, not by
  `fence .ld` (see `readSuccs`). -/
  vrOldNR : View := 0
  vwNew : View := 0
  vwOld : View := 0
  /-- `vwOld` for non-temporal writes (`StoreKind.nt`, x86's `movnti`): folded
  in by `fence .sy`, `.st` and `.stAll` (and so by a TSO locked RMW), not by a
  release write's pre-view, which on TSO is every ordinary store's (SDM vol. 3A
  §8.2.2: NT stores are not ordered with other stores). Always `0` on ARM. -/
  vwOldNT : View := 0
  vCAP : View := 0
  vRel : View := 0
  fwdb : List (Loc × FwdItem) := []
  /-- The last load exclusive: its timestamp, post-view and location. -/
  xclb : Option (Time × View × Loc) := none
  deriving Repr, BEq, Hashable, Inhabited

namespace Views

/-- Insert into an association list sorted by location, replacing an existing
entry, so that equal maps are equal lists. (Not private: `Conservative.lean`
proves its `find?` characterisation.) -/
def setSorted {β} (xs : List (Loc × β)) (l : Loc) (b : β) : List (Loc × β) :=
  match xs with
  | [] => [(l, b)]
  | (l', b') :: rest =>
    match compare l l' with
    | .lt => (l, b) :: (l', b') :: rest
    | .eq => (l, b) :: rest
    | .gt => (l', b') :: setSorted rest l b

def getCoh (v : Views) (l : Loc) : View :=
  ((v.coh.find? (·.1 == l)).map (·.2)).getD 0

def setCoh (v : Views) (l : Loc) (t : View) : Views :=
  { v with coh := setSorted v.coh l (max (v.getCoh l) t) }

def getFwd (v : Views) (l : Loc) : Option FwdItem :=
  (v.fwdb.find? (·.1 == l)).map (·.2)

def setFwd (v : Views) (l : Loc) (f : FwdItem) : Views :=
  { v with fwdb := setSorted v.fwdb l f }

end Views

/-- A thread: the ISA state, two views per register, the view components,
and the outstanding promises (sorted).

A register carries a *read-ordering* view `rview` and a *write-ordering*
view `wview`, with `rview ≤ wview`. For an ordinary data dependency they
are equal. A pick dependency (Arm's `CSEL` family: the condition selects
the result) orders only later writes, so it joins into `wview` alone; a
load whose address has a pick dependency is not ordered, a store is. -/
structure Thread (I : ISA) where
  st : I.State
  rview : Array View
  wview : Array View
  views : Views := {}
  prom : List Time := []

namespace Thread

variable {I : ISA}

def beq (a b : Thread I) : Bool :=
  I.beqState a.st b.st && a.rview == b.rview && a.wview == b.wview && a.views == b.views && a.prom == b.prom

def hash (a : Thread I) : UInt64 :=
  mixHash (I.hashState a.st) (mixHash (Hashable.hash a.rview)
    (mixHash (Hashable.hash a.wview) (mixHash (Hashable.hash a.views) (Hashable.hash a.prom))))

instance : BEq (Thread I) := ⟨beq⟩
instance : Hashable (Thread I) := ⟨hash⟩

def init (st : I.State) : Thread I :=
  { st, rview := Array.replicate I.numRegs 0, wview := Array.replicate I.numRegs 0 }

/-- Some outstanding promise can no longer be fulfilled: `fulfil` needs the
promise's timestamp above `coh l`, `vwNew` and `vCAP` (part of every
write's pre-view), and these views only grow. A thread in this state can
never empty its promise set, so it is dead for certification and for
reaching a final configuration. -/
def hasDeadPromise (t : Thread I) (mem : Memory) : Bool :=
  t.prom.any fun p => match mem.get? p with
    | some w => p ≤ max (t.views.getCoh w.loc) (max t.views.vwNew t.views.vCAP)
    | none => false

def rviewOf (t : Thread I) (r : I.RegId) : View := t.rview[(I.regIndex r).val]!
def wviewOf (t : Thread I) (r : I.RegId) : View := t.wview[(I.regIndex r).val]!

/-- The joins of the read- and write-ordering views of a list of registers. -/
def joinViews (t : Thread I) (rs : List I.RegId) : View × View :=
  rs.foldl (fun (r, w) x => (max r (t.rviewOf x), max w (t.wviewOf x))) (0, 0)

def setRegView (t : Thread I) (r : I.RegId) (rv wv : View) : Thread I :=
  { t with rview := t.rview.set! (I.regIndex r).val rv, wview := t.wview.set! (I.regIndex r).val wv }

/-- The thread has halted: nothing to execute at its pc. -/
def halted (t : Thread I) : Bool := (I.exec t.st).isNone

end Thread

/-! ## Interpreting one instruction

`Ctx` threads the pieces of state a rule touches through the event tree:
the thread's views and promises, the memory (a fulfil may append to it),
and, per instruction, the post-views of its loads (for `loadDefs`) and of
its exclusive store (for `statusDefs`).
-/

/-- One step of a witness trace: what a rule did. Locations and values are
printed by the front-end, which knows their names. -/
inductive TraceEv
  | instr (tid : Nat) (text : String)
  | read (loc : Loc) (t : Time) (v : Val) (νpost : View)
  | write (loc : Loc) (t : Time) (v : Val) (fulfilled : Bool)
  | xclFail (loc : Loc)
  | fence (k : FenceKind)
  | promise (tid : Nat) (loc : Loc) (v : Val) (t : Time)
  deriving Repr, Inhabited

/-- The state threaded through an instruction's event tree. -/
structure Ctx where
  views : Views
  prom : List Time
  mem : Memory
  /-- Post-views of the loads executed so far by this instruction, in order. -/
  loadViews : List View := []
  /-- View for the success register of a store exclusive. -/
  succView : View := 0
  /-- An RMW performed its write (a compare-and-swap succeeded). -/
  rmwWrote : Bool := false
  /-- Writes performed so far by this instruction: the index of the next
  store's data view in `InstrViews.dataPer`. -/
  stores : Nat := 0
  /-- Did a step append to memory ("promise now")? For certification: the
  write's pre-view and coherence view, when it did. -/
  promisedNow : List (Msg × View) := []
  /-- What happened, for witness traces. -/
  log : List TraceEv := []

/-- Per-instruction views, from the register views of its dependencies:
read- and write-ordering views of the address and data registers, and the
write-ordering view of the condition registers. `dataPer` holds the read-
and write-ordering views of each store's own data registers, for an
instruction with several stores (`InstrDeps.dataRegsPer`); empty, every
store uses `dataR`/`dataW`. -/
structure InstrViews where
  addrR : View
  addrW : View
  dataR : View
  dataW : View
  condW : View
  dataPer : List (View × View) := []

/-- The views of an instruction's store number `i` (from `0`): its own data
views from `dataPer` if there are any, else the instruction's. -/
def InstrViews.forStore (iv : InstrViews) (i : Nat) : InstrViews :=
  match iv.dataPer[i]? with
  | some (r, w) => { iv with dataR := r, dataW := w }
  | none => iv

section Rules

variable (A : Arch) (tid : Nat) (iv : InstrViews)

/-- `read-view(a, rk, f, t)`: reading the thread's own last write to the
location (timestamp `t`) takes that write's forwarding view instead of `t`.

On ARM any load kind may forward from an exclusive write (an RMW's write or
a successful store exclusive): herd's `aob` orders only the exclusive pair's
*read* before a later acquire that reads the write locally
(`[Exp & M]; rmw; lrs; [A | Q]` in `aarch64hwreqs.cat`). An RMW's forwarding
view already carries its read's post-view (its write depends on its read);
a store exclusive's does not (a plain load forwarding from it is not ordered
after the load exclusive), so a non-plain load also takes `f.xclRead`
(which is below the write's timestamp `t`; the `min` with `t` only makes that
evident, so that a bound on `t` bounds the result).
Pulte et al.'s Fig. 5 lets only plain loads forward from an exclusive write
(`a = ARM ∧ rk ⊑ pln`), which is herd's earlier `[range(rmw)]; lrs; [A | Q]`;
`Arch.fwdXclOnlyPlain` keeps that restriction (TSO: every load is an
acquire, so a locked RMW's write never forwards). -/
def readView (k : LoadKind) (f : Option FwdItem) (t : Time) : View :=
  match f with
  | some f => if f.time = t && (!f.xcl || (!A.fwdXclOnlyPlain || k == .plain)) then
      (if f.xcl && k != .plain then max f.view (min f.xclRead t) else f.view) else t
  | none => t

/-- The `read` rule: every timestamp this thread may read `l` from, with the
value read and the context after the read.

A thread's own outstanding promise is never offered: reading it would raise
`coh l` to its timestamp, after which `fulfil` (which needs `coh l < t`) is
impossible, so no such state can reach an empty promise set — neither a
final configuration nor a certification. Pruning it is sound and keeps
promise-free certification runs from wandering into dead loops (e.g. an
enqueuer "helping" with its own not-yet-performed link).

A read raises `vrOld`, not `vwOld` (Fig. 5 of the paper): `DMB ST` and
`DSB ST` order earlier writes only, so they must not see earlier reads
(LB+dmb.st+dmb.st is allowed by herd; `corpus/aarch64-views/`).

A `noRet` read (the read of an AArch64 atomic whose destination is the zero
register, herd's `NoRet`) raises `vrOldNR` instead of `vrOld`. herd orders an
explicit read `R` before later accesses by `DMB LD`/`DSB LD` only when
`R ∉ NoRet` (`[(Exp & R) \ NoRet]; po; [dmb.ld]` in `bob`, the same for
`dsb.ld` in `DSB-ob`), but by `DMB SY`/`DSB SY` (`[Exp & M]; po; [dmb.full]`)
and by a later release write (`[Exp & M]; po; [Exp & W & L]`) whatever it is.
In Pulte et al.'s style that is one more view class next to `vrOld` and
`vwOld`: `fence .sy` and the release pre-view fold all three, `fence .ld`
only `vrOld`, `fence .st`/`.stAll` only `vwOld`. (When the RMW writes, its
write's timestamp is above the read's post-view and raises `vwOld`, but a
failing `CAS` writes nothing, so the read needs its own view.) `runTree`
also gives a `noRet` read the plain kind: herd replaces its `A` annotation. -/
def readSuccs (c : Ctx) (k : LoadKind) (xcl : Bool) (l : Loc) (noRet : Bool := false) :
    List (Time × Val × Ctx) :=
  let k := A.loadKind k
  let vs := c.views
  let νpre := max iv.addrR (max vs.vrNew (if k == .acq then vs.vRel else 0))
  let bound := max νpre (vs.getCoh l)
  (List.range (c.mem.last + 1)).filterMap fun t =>
    match c.mem.read? l t with
    | none => none
    | some v =>
      if c.mem.writeIn l t bound || c.prom.contains t then none else
      let νpost := max νpre (readView A k (vs.getFwd l) t)
      let acq := k.isAcquire
      let vs' : Views :=
        { (vs.setCoh l νpost) with
          vrOld := if noRet then vs.vrOld else max vs.vrOld νpost
          vrOldNR := if noRet then max vs.vrOldNR νpost else vs.vrOldNR
          vrNew := if acq then max vs.vrNew νpost else vs.vrNew
          vwNew := if acq then max vs.vwNew νpost else vs.vwNew
          vCAP := max vs.vCAP iv.addrW
          xclb := if xcl then some (t, νpost, l) else vs.xclb }
      some (t, v, { c with views := vs', loadViews := c.loadViews ++ [νpost],
                           log := c.log ++ [.read l t v νpost] })

/-- The state after a write of `l := v` at timestamp `t` with pre-view `νpre`
and forwarding view `νfwd` (and `xclRead`, see `FwdItem`). (Not private:
`Conservative.lean` reasons about it.) -/
def afterWrite (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val) (t : Time) (νfwd : View)
    (fulfilled : Bool) (xclRead : View := 0) : Ctx :=
  let vs := c.views
  let vs' : Views :=
    { (vs.setCoh l t) with
      vwOld := if k == .nt then vs.vwOld else max vs.vwOld t
      vwOldNT := if k == .nt then max vs.vwOldNT t else vs.vwOldNT
      vCAP := max vs.vCAP iv.addrW
      vRel := if k == .rel then max vs.vRel t else vs.vRel
      fwdb := (vs.setFwd l { time := t, view := νfwd, xcl, xclRead }).fwdb
      xclb := if xcl then none else vs.xclb }
  { c with views := vs', prom := c.prom.erase t, stores := c.stores + 1,
           succView := if A.succViewBot then 0 else t,
           log := c.log ++ [.write l t v fulfilled] }

/-- The `fulfil` rule, with "promise now" as the choice of a fresh timestamp
`|M| + 1`: every way this thread may perform the write `l := v`. For an
exclusive write, `tr` is the timestamp the paired read read from (from
`xclb`, or the RMW's own read); the `atomic` condition applies. `extraData`
joins into the data view (an RMW's write depends on its read).

A release write's pre-view also takes every earlier read and write
(`vrOld`, `vrOldNR`, `vwOld`), but not the non-temporal writes (`vwOldNT`).
A non-temporal write (`.nt`, only on TSO: x86's `movnti`) takes the earlier
reads (the SDM orders writes after older reads, with no exception for NT
stores) but no earlier write, and raises `vwOldNT` instead of `vwOld`, so that
neither earlier nor later ordinary stores are ordered with it; `sfence`,
`mfence` and locked RMWs are (`fenceStep`). Per-location coherence (`coh`)
orders it with every access to its own location.

The pre-view takes the write-ordering views of address, data and condition
registers (a pick or compare-and-swap dependency orders the write); the
forwarding view, which a later local read inherits, takes the read-ordering
views of address and data only (`(addr | data); lmrs` in `aarch64hwreqs.cat`).
A store exclusive passes its paired load exclusive's post-view as `xclRead`
(`FwdItem`, `readView`). -/
def writeSuccs (c : Ctx) (k : StoreKind) (xcl : Bool) (l : Loc) (v : Val)
    (tr : Option Time) (extraData : View := 0) (xclRead : View := 0) : List Ctx :=
  let k := A.storeKind k
  let vs := c.views
  let νpre := max (max iv.addrW (max iv.dataW (max iv.condW extraData))) (max (max vs.vwNew vs.vCAP)
    (if k == .rel then max (max vs.vrOld vs.vrOldNR) vs.vwOld
     else if k == .nt then max vs.vrOld vs.vrOldNR else 0))
  let bound := max νpre (vs.getCoh l)
  let νfwd := max iv.addrR (max iv.dataR extraData)
  let ok (t : Time) : Bool :=
    bound < t && (match tr with | some tr => tr < t && c.mem.atomic l tid tr t | none => true)
  -- fulfil an existing promise
  let fulfils := c.prom.filterMap fun t =>
    match c.mem.get? t with
    | some w => if w.loc == l && w.val == v && w.tid == tid && ok t
                then some (afterWrite A iv c k xcl l v t νfwd true xclRead) else none
    | none => none
  -- promise now
  let now :=
    let (mem', t) := c.mem.append { loc := l, val := v, tid }
    if ok t then
      [afterWrite A iv { c with mem := mem', prom := c.prom ++ [t],
                                 promisedNow := c.promisedNow ++ [({ loc := l, val := v, tid }, bound)] }
         k xcl l v t νfwd false xclRead]
    else []
  fulfils ++ now

/-- The `fence` rule, `fence_{K1,K2}`: `dmb.sy = RW,RW`, `dmb.ld = R,RW`,
`dmb.st = W,W`; `isb` folds `vCAP` into `vrNew`. `stAll` (`DSB ST`, not in the
paper) is `W,RW`: herd's `DSB-ob` orders earlier explicit writes before every
later explicit access (`aarch64hwreqs.cat`). The `R` of `dmb.sy` includes the
`noRet` reads (`vrOldNR`), the `R` of `dmb.ld` does not (see `readSuccs`). The
`W` of `sy`, `st` and `stAll` includes the non-temporal writes (`vwOldNT`):
x86's `mfence` and `sfence` (`.st`) order them before later stores. -/
def fenceStep (c : Ctx) (k : FenceKind) : Ctx :=
  let vs := c.views
  let c := { c with log := c.log ++ [TraceEv.fence k] }
  match k with
  | .sy => let ν := max (max vs.vrOld vs.vrOldNR) (max vs.vwOld vs.vwOldNT)
           { c with views := { vs with vrNew := max vs.vrNew ν, vwNew := max vs.vwNew ν } }
  | .ld => let ν := vs.vrOld
           { c with views := { vs with vrNew := max vs.vrNew ν, vwNew := max vs.vwNew ν } }
  | .st => { c with views := { vs with vwNew := max vs.vwNew (max vs.vwOld vs.vwOldNT) } }
  | .stAll => let ν := max vs.vwOld vs.vwOldNT
              { c with views := { vs with vrNew := max vs.vrNew ν, vwNew := max vs.vwNew ν } }
  | .isb => { c with views := { vs with vrNew := max vs.vrNew vs.vCAP } }

/-- Run an event tree: every (final machine state, context) pair. -/
def runTree {σ : Type} (c : Ctx) : EvTree σ → List (Except String (σ × Ctx))
  | .done s => [.ok (s, c)]
  | .fault m => [.error m]
  | .choose n k => (List.finRange n).flatMap fun i => runTree c (k i)
  | .load k xcl l ret =>
    (readSuccs A iv c k xcl l).flatMap fun (_, v, c') => runTree c' (ret v)
  | .store k xcl l v ret =>
    -- the store's own data views (`STP`: per-access data dependencies)
    let succ := (writeSuccs A tid (iv.forStore c.stores) c k xcl l v
        (if xcl then c.views.xclb.map (·.1) else none)
        (xclRead := if xcl then (c.views.xclb.map (·.2.1)).getD 0 else 0)).flatMap
      fun c' => runTree c' (ret true)
    let fail := if xcl then
        runTree { c with views := { c.views with xclb := none }, succView := 0,
                         log := c.log ++ [.xclFail l] } (ret false)
      else []
    -- an exclusive store needs a pairing load exclusive to the same location
    -- to succeed (herd's default; the paper lets a different location pair)
    let paired := match c.views.xclb with
      | some (_, _, l') => l' == l
      | none => false
    (if xcl && !paired then [] else succ) ++ fail
  | .fence k ret => runTree (fenceStep c k) (ret ())
  | .rmw k noRet l op ret =>
    let k := A.rmwKind k
    let c := if A.rmwFence then fenceStep c .sy else c
    -- a `noRet` read is plain whatever `k` says (herd: `NoRet` replaces `A`);
    -- the write keeps `k`'s release
    (readSuccs A iv c (if noRet then .plain else k.loadKind) false l noRet).flatMap fun (tr, old, c') =>
      let νr := c'.loadViews.getLastD 0
      match op old with
      | none => runTree (if A.rmwFence then fenceStep c' .sy else c') (ret old)
      | some new =>
        (writeSuccs A tid iv c' k.storeKind true l new (some tr) νr).flatMap fun c'' =>
          let c'' := { c'' with rmwWrote := true }
          -- an acquire-release atomic orders everything after it after its write
          -- (`[range([R & A]; amo; [W & L])]; po; [M]` in `aarch64hwreqs.cat`);
          -- not a `noRet` one, whose read is not `A`
          let c'' := if k == .acqRel && !noRet then
              let t := c''.views.getCoh l
              { c'' with views := { c''.views with vrNew := max c''.views.vrNew t, vwNew := max c''.views.vwNew t } }
            else c''
          runTree (if A.rmwFence then fenceStep c'' .sy else c'') (ret old)

end Rules

end Kraken.Promising

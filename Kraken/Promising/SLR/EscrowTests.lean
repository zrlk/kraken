/-
Explorer sanity checks for fallback (iii), the **prepaid release**
(`Kraken.Promising.SLR.Escrow`): promised releases whose release store is not
the instruction's last memory event.

Toy has only single-event instructions, so this file defines **Toy2**, a
small ISA with the shapes (iii) is about:

- `stp k₁ l₁ v₁ k₂ l₂ v₂`: two stores in one instruction, `[l₁] := v₁` (kind
  `k₁`) then `[l₂] := v₂` (kind `k₂`). With `k₁ = .rel` it is the "release
  first" shape (x64 `movups`/`vmovdqu` low half, `STLXP`-like); with
  `k₂ = .rel` the ordinary "release last" one;
- `casp`: AArch64 `CASP`, the Promising translation `AArch64.caspTree` (both
  orders of the halves are explored, so each half is first in some run);
- `ld`, `st`, `cas` and `beq` as in Toy.

The shadow of `Erase` is ErasureTests' (`eraseFails`), restated for an
arbitrary ISA (ErasureTests' copy is typed at Toy's `Config isa`); the
resource algebra, predicates and `CanAcq` saturation (`SRes`, `SPred`,
`sepList`, `canAcqB`, `mayWriteB`) are ErasureTests' own.

For each program and outline, at **every** reachable configuration `c`
(promises included):

- the (iii) virtual advance (`advancePre`): every thread with an outstanding
  release-mode promise runs, memory-silently and without promising, up to the
  instruction `F` that fulfils it (*pre-F*), not through it. The pending set
  is the advanced-over promises plus **every** outstanding release-mode
  promise (all prepaid at promise time, `Erase.prepay`; the RMW law
  `Erase.prepayRmw` is retired, `Erase.claimFulf`).
  Erasure is checked at `c` and at the virtual configuration `v` (there with
  the still-outstanding prepaid releases pending);
- negative control, nothing pending at `c`: fails wherever a release is
  promised (`relSettled`);
- negative control, (ii) only (`advanceStrict`, ErasureTests' `advanceTo`):
  the advance must run *through* `F` memory-silently, which is impossible
  when `F`'s other write is not itself promised (`noAdvance`);
- negative control, escrow outside `u`: an outline in which the escrowed
  resource moves into the release slot only once `F` has run (S2a's sketch)
  fails at pre-F (`slotsDom`: a reader holds an acquire id of an outstanding
  release message with no slot; `valid`: a reader that has acquired from the
  outstanding message duplicates the resource).
-/
import Kraken.Promising.SLR.ErasureTests
import Kraken.Promising.SLR.EscrowCasp

namespace Kraken.Promising.Toy2

open Kraken.Promising.Toy (SRes SPred SSlot sepList canAcqB mayWriteB loc decls locIdx)

abbrev Reg := Fin 4

/-! ## Toy2 -/

inductive Instr
  /-- `dst := load [l]` -/
  | ld (k : LoadKind) (dst : Reg) (l : Nat)
  /-- `[l] := v` -/
  | st (k : StoreKind) (l : Nat) (v : Nat)
  /-- Two stores in one instruction: `[l₁] := v₁` (kind `k₁`), then
  `[l₂] := v₂` (kind `k₂`). -/
  | stp (k₁ : StoreKind) (l₁ v₁ : Nat) (k₂ : StoreKind) (l₂ v₂ : Nat)
  /-- `CAS`: `dst := old; if old = cmp then [l] := new`. -/
  | cas (k : RmwKind) (dst : Reg) (l : Nat) (cmp new : Nat)
  /-- `CASP` on the pair `(l, l + 1)` (`AArch64.caspTree`): `dst := old₁`. -/
  | casp (k : RmwKind) (dst : Reg) (l : Nat) (cmp₁ cmp₂ new₁ new₂ : Nat)
  /-- `if r = v then goto target` -/
  | beq (r : Reg) (v : Nat) (target : Nat)
  deriving BEq, Hashable

structure State where
  prog : Array Instr
  pc : Nat := 0
  regs : Array (BitVec 64) := #[0, 0, 0, 0]

def State.set (s : State) (r : Reg) (v : BitVec 64) : State := { s with regs := s.regs.set! r.val v }
def State.next (s : State) : State := { s with pc := s.pc + 1 }

def exec (s : State) : Option (EvTree State) := do
  let i ← s.prog[s.pc]?
  return match i with
  | .ld k dst l => .load k false (loc l) fun v => .done ((s.set dst (v.setWidth 64)).next)
  | .st k l v => .store k false (loc l) (BitVec.ofNat 128 v) fun _ => .done s.next
  | .stp k₁ l₁ v₁ k₂ l₂ v₂ =>
    .store k₁ false (loc l₁) (BitVec.ofNat 128 v₁) fun _ =>
      .store k₂ false (loc l₂) (BitVec.ofNat 128 v₂) fun _ => .done s.next
  | .cas k dst l cmp new => .rmw k false (loc l)
      (fun old => if old.setWidth 64 == BitVec.ofNat 64 cmp then some (BitVec.ofNat 128 new) else none)
      fun old => .done ((s.set dst (old.setWidth 64)).next)
  | .casp k dst l c₁ c₂ n₁ n₂ =>
    AArch64.caspTree (w := .W64) decls k (loc l).addr (BitVec.ofNat 64 c₁) (BitVec.ofNat 64 c₂)
      (BitVec.ofNat 64 n₁) (BitVec.ofNat 64 n₂) fun o₁ _ => .done ((s.set dst o₁).next)
  | .beq r v target => .done (if s.regs[r.val]! == BitVec.ofNat 64 v then { s with pc := target } else s.next)

def deps (s : State) : InstrDeps Reg :=
  match s.prog[s.pc]? with
  | none => {}
  | some i => match i with
    | .ld _ dst _ => { loadDefs := [dst] }
    | .st .. | .stp .. => {}
    | .cas _ dst .. | .casp _ dst .. => { loadDefs := [dst] }
    | .beq r _ _ => { condRegs := [r], isBranch := true }

def isa : ISA where
  State := State
  RegId := Reg
  numRegs := 4
  regIndex := id
  exec := exec
  deps := deps
  beqState a b := a.pc == b.pc && a.regs == b.regs && a.prog == b.prog
  hashState s := mixHash (hash s.pc) (mixHash (hash s.regs) (hash s.prog))

def initOf (progs : List (List Instr)) : Config isa :=
  Config.init (progs.map fun p => ({ prog := p.toArray } : State)) []

/-- Every configuration reachable from `c0`, promises included
(PFCompleteDRFTests' `reachAll`). -/
partial def reachAll (A : Arch) (c0 : Config isa) : Array (Config isa) :=
  let rec go (vis : Std.HashSet (Config isa)) (cache : CertCache isa) (acc : Array (Config isa))
      (front : List (Config isa)) : Array (Config isa) :=
    match front with
    | [] => acc
    | c :: rest =>
      if vis.contains c then go vis cache acc rest else
      let (next, _, _, cache) := succsL A cache c 64 none
      go (vis.insert c) cache (acc.push c) (next.map (·.1) ++ rest)
  go {} {} #[] [c0]

/-- Final values of locations `0..n-1`, sorted (sanity check of the semantics). -/
def runMem (A : Arch) (progs : List (List Instr)) (n : Nat) : List (List Nat) :=
  let r := explore (I := isa) A (initOf progs) (fun c => (List.range n).map fun i => (c.mem.finalVal (loc i)).toNat)
  r.finals.mergeSort (fun a b => decide (a.toString ≤ b.toString))

/-- Final registers of every thread, sorted. -/
def run (A : Arch) (progs : List (List Instr)) : List (List (List Nat)) :=
  let r := explore (I := isa) A (initOf progs)
    (fun c => c.threads.toList.map fun t => t.st.regs.toList.map (·.toNat))
  r.finals.mergeSort (fun a b => decide (a.map (·.toString) ≤ b.map (·.toString)))

open Kraken.Promising.Toy2.Instr

-- `stp` writes both locations; `casp` both halves (on a match) or none.
/-- info: [[0, 1, 2]] -/
#guard_msgs in #eval runMem .armv8 [[stp .rel 1 1 .plain 2 2]] 3
/-- info: [[0, 1, 2]] -/
#guard_msgs in #eval runMem .armv8 [[casp .rel 0 1 0 0 1 2]] 3
/-- info: [[0, 0, 0]] -/
#guard_msgs in #eval runMem .armv8 [[casp .rel 0 1 0 5 1 2]] 3
-- MP through the release half of `stp`/`casp`: forbidden.
/-- info: false -/
#guard_msgs in #eval (run .armv8 [[st .plain 0 1, stp .rel 1 1 .plain 2 1], [ld .acq 0 1, ld .plain 1 0]]).any
  fun fin => fin[1]! == [1, 0, 0, 0]
/-- info: false -/
#guard_msgs in #eval (run .armv8 [[st .plain 0 1, casp .rel 0 1 0 0 1 1], [ld .acq 0 1, ld .plain 1 0]]).any
  fun fin => fin[1]! == [1, 0, 0, 0]

/-! ## The shadow of `Erase`, for an arbitrary ISA

ErasureTests' `SSpec`/`eraseFails` and helpers, verbatim up to the ISA. -/

section Shadow

variable {I : ISA}

structure SSpec (I : ISA) where
  rel : Nat → SPred
  acqTab : List SPred
  relMode : Msg → Bool
  assign : Config I → List SRes × List SSlot
  dom : List SRes
  initRel : Nat → Bool := fun _ => false
  upd : Nat → List Nat := fun _ => []
  rmwMsg : Msg → Bool := fun _ => false

def outstandingB (c : Config I) (ts : Nat) : Bool := c.threads.any (·.prom.contains ts)

def promsOf (c : Config I) (i : Nat) : List Time := (c.threads[i]?.map (·.prom)).getD []

def msgs (c : Config I) : List (Nat × Msg) :=
  (List.range (c.mem.last + 1)).filterMap fun ts => (c.mem.get? ts).map (ts, ·)

def settledB (c : Config I) (pend : List Nat) (ts : Nat) : Bool := !outstandingB c ts || pend.contains ts

def fulfOf (c : Config I) (pend : List Nat) : Toy.SFulf := fun x =>
  ((c.mem.initVal (loc x)).toNat, 0) ::
    ((msgs c).filter (fun (ts, w) => ts != 0 && locIdx w.loc == x && settledB c pend ts)).map
      fun (ts, w) => (w.val.toNat, ts)

def claimsWith (rmwMsg : Msg → Bool) (c : Config I) (pend : List Nat) : List ((Nat × Nat) × Nat) :=
  let ms := msgs c
  (ms.filter fun (ts, w) => ts != 0 && rmwMsg w && settledB c pend ts).map fun (ts, w) =>
    let tr := (ms.filter fun (ts', w') => ts' < ts && w'.loc == w.loc).foldl (fun a (ts', _) => max a ts') 0
    ((locIdx w.loc, tr), ts)

/-- The clauses of `Erase rF g ∅ c` that fail (ErasureTests' `eraseFails`). -/
def eraseFails (S : SSpec I) (c : Config I) (assignAt : Config I) (pend : List Nat) : List String :=
  let (rF, slots) := S.assign assignAt
  let tot := (rF ++ slots.map (·.2.2.2)).foldl SRes.op SRes.unit
  let f := fulfOf c pend
  let ms := msgs c
  let initMsgs := (List.range 4).map fun x => (x, 0, (c.mem.initVal (loc x)).toNat)
  let relKeys := ((List.range 4).filter S.initRel).map (·, 0) ++
    (ms.filter fun (ts, w) => ts != 0 && S.relMode w).map fun (ts, w) => (locIdx w.loc, ts)
  let claims := claimsWith S.rmwMsg c pend
  let claimed (k : Nat × Nat) : Bool := claims.any (·.1 == k)
  let valAt (x ts : Nat) : Option Nat :=
    if ts == 0 then some (c.mem.initVal (loc x)).toNat else (ms.find? (·.1 == ts)).map (·.2.val.toNat)
  let check (name : String) (b : Bool) : List String := if b then [] else [name]
  check "valid" ((List.range 4).all (tot.q · ≤ SRes.one) && tot.acq.all fun (x, ι) => tot.acqCount x ι ≤ 1) ++
  check "slotIds" (slots.all fun (_, _, ι, _) => ι < S.acqTab.length) ++
  check "acqIds" (tot.acq.all fun (_, ι) => ι < S.acqTab.length) ++
  check "relAcq" ((List.range 4).all fun x => (List.range 3).all fun v => S.dom.all fun r =>
    !S.rel x f v r ||
      sepList S.dom f (((tot.acq.filter (·.1 == x)).map (·.2) ++ S.upd x).map fun ι =>
        S.acqTab.getD ι fun _ _ _ => false) v r) ++
  check "writes" ((List.range 4).all fun x =>
    let tracked := tot.q x > 0 || ms.any fun (ts, w) => ts != 0 && locIdx w.loc == x && settledB c pend ts
    !tracked || tot.q x > 0) ++
  let nonInit : List (Nat × Nat × Nat) :=
    (ms.filter fun (p : Nat × Msg) => p.1 != 0).map fun (ts, w) => (locIdx w.loc, ts, w.val.toNat)
  check "pure" ((initMsgs ++ nonInit).all fun (x, ts, v) => relKeys.contains (x, ts) || S.rel x f v SRes.unit) ++
  check "slotsNodup" ((slots.map fun (x, ts, ι, _) => (x, ts, ι)).eraseDups.length == slots.length) ++
  check "slotsDom" ((slots.all fun (x, ts, ι, _) => relKeys.contains (x, ts) &&
      (tot.acqCount x ι == 1 || ((S.upd x).contains ι && !claimed (x, ts)))) &&
    relKeys.all fun (x, ts) =>
      let ids := (tot.acq.filter (·.1 == x)).map (·.2) ++ (if claimed (x, ts) then [] else S.upd x)
      ids.all fun ι => slots.any fun (x', ts', ι', _) => x' == x && ts' == ts && ι' == ι) ++
  check "slotsPred" (slots.all fun (x, ts, ι, r) =>
    match valAt x ts with
    | some v => (S.acqTab.getD ι fun _ _ _ => false) f v r
    | none => false) ++
  check "promWf" ((List.range c.threads.size).all fun i => (promsOf c i).all fun ts =>
    match c.mem.get? ts with
    | some w => w.tid == i
    | none => false) ++
  check "promValid" ((List.range c.threads.size).all fun i => (promsOf c i).all fun ts =>
    pend.contains ts || match c.mem.get? ts with
    | some w => mayWriteB slots (rF.getD i SRes.unit) (locIdx w.loc) S.upd
    | none => true) ++
  check "pend" (pend.all fun ts => outstandingB c ts && (c.mem.get? ts).isSome) ++
  check "updIds" ((List.range 4).all fun x => (S.upd x).all fun ι => ι < S.acqTab.length && tot.acqCount x ι == 0) ++
  check "relSettled" (relKeys.all fun (_, ts) => ts == 0 || settledB c pend ts) ++
  check "claimsNodup" ((claims.map (·.1)).eraseDups.length == claims.length) ++
  check "claimsAt" (claims.all fun ((x, tr), tw) => match c.mem.get? tw with
    | some w => tr < tw && (ms.all fun (ts, w') => !(tr < ts && ts < tw && locIdx w'.loc == x) || w'.tid == w.tid)
    | none => false)

end Shadow

/-! ## Virtual advances -/

/-- One instruction of thread `i` from `t` on `mem`, memory-silent: its
successor threads. -/
def silentSteps (A : Arch) (i : Nat) (mem : Memory) (t : Thread isa) : List (Thread isa) :=
  match stepOne A t i mem with
  | none => []
  | some outs => outs.filterMap fun
    | .ok o => if o.mem.last == mem.last then some o.thread else none
    | .error _ => none

/-- (ii): run thread `i` memory-silently **through** the instructions that
fulfil `targets` (ErasureTests' `advanceTo`). -/
partial def advanceStrict (A : Arch) (i : Nat) (mem : Memory) (targets : List Time) (t : Thread isa) (d : Nat) :
    Option (Thread isa) :=
  if targets.all (fun p => !t.prom.contains p) then some t
  else if d == 0 then none
  else (silentSteps A i mem t).findSome? fun t' => advanceStrict A i mem targets t' (d - 1)

/-- (iii): run thread `i` memory-silently **up to** (*pre-F*) the first
instruction some step of which fulfils a promise in `targets`. -/
partial def advancePre (A : Arch) (i : Nat) (mem : Memory) (targets : List Time) (t : Thread isa) (d : Nat) :
    Option (Thread isa) :=
  let fulfils := match stepOne A t i mem with
    | none => false
    | some outs => outs.any fun
      | .ok o => targets.any fun p => t.prom.contains p && !o.thread.prom.contains p
      | .error _ => false
  if targets.all (fun p => !t.prom.contains p) || fulfils then some t
  else if d == 0 then none
  else (silentSteps A i mem t).findSome? fun t' => advancePre A i mem targets t' (d - 1)

/-- The virtual configuration of `c` under the advance `adv` (`none`: some
thread with an outstanding release promise does not advance). -/
def virtualWith (adv : Nat → Memory → List Time → Thread isa → Nat → Option (Thread isa))
    (S : SSpec isa) (c : Config isa) : Option (Config isa) :=
  (List.range c.threads.size).foldlM (init := c) fun v i =>
    match c.threads[i]? with
    | none => some v
    | some t =>
      let targets := t.prom.filter fun ts => match c.mem.get? ts with
        | some w => S.relMode w
        | none => false
      if targets.isEmpty then some v else
      (adv i c.mem targets t 12).map fun t' => { v with threads := v.threads.set! i t' }

/-- Is `ts` a release-mode message of `c`? -/
def relAt (S : SSpec isa) (c : Config isa) (ts : Nat) : Bool :=
  match c.mem.get? ts with
  | some w => S.relMode w
  | none => false

/-- `(#configurations, #with an outstanding release promise, #without a (iii)
advance, #failing erasure at c with the (iii) pending set, #failing at the
virtual configuration, #failing at c with nothing pending, #without a (ii)
advance, the clauses failing at c with the (iii) pending set, and at c with
nothing pending, deduplicated)`. -/
def escrowCheck (A : Arch) (progs : List (List Instr)) (S : SSpec isa) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × List String × List String :=
  let all := reachAll A (initOf progs)
  all.foldl (init := (all.size, 0, 0, 0, 0, 0, 0, [], [])) fun (n, rp, noAdv, fc, fv, f0, noStrict, why, why0) c =>
    let hasRel := (msgs c).any fun (ts, w) => S.relMode w && outstandingB c ts
    let rp := if hasRel then rp + 1 else rp
    let noStrict := if (virtualWith (advanceStrict A) S c).isNone then noStrict + 1 else noStrict
    match virtualWith (advancePre A) S c with
    | none => (n, rp, noAdv + 1, fc, fv, f0, noStrict, why, why0)
    | some v =>
      let pend := (List.range (c.mem.last + 1)).filter fun ts =>
        outstandingB c ts && (!outstandingB v ts || relAt S c ts)
      let ec := eraseFails S c v pend
      let ev := eraseFails S v v (pend.filter (outstandingB v))
      let e0 := eraseFails S c v []
      (n, rp, noAdv, if ec.isEmpty then fc else fc + 1, if ev.isEmpty then fv else fv + 1,
        if e0.isEmpty then f0 else f0 + 1, noStrict, (why ++ ec).eraseDups, (why0 ++ e0).eraseDups)

/-! ## MP through a release that is not the last write

`x := 1; F ∥ r0 :=acq y; r1 := x`, where `F` publishes the flag `y = 1`
together with a second write to `z`: `stp.rel` (flag first, `z := 1` after
it: (iii)), `stp` with the flag last (the ordinary (ii) shape, as a
comparison), or `CASP.rel` on `(y, z)` (both orders of the halves).
Locations: `x = 0`, `y = 1`, `z = 2`.

The outline is ErasureTests' `mpSpec` (thread 0 owns `W¹(x)`, `W¹(y)`,
`W¹(z)`, thread 1 the acquire id `ι₀` of `y`, `W.rel y = W.acq ι₀ = λ v r.
v = 1 → r = W¹(x) ∧ 1 ∈ Fulf(x)`), except **when** `W¹(x)` moves into the
slot of the flag message: as soon as the message **exists** (outstanding or
not), `escrow := true`. This is the prepaid release: the slot is in `u` from
promise time (`prepayGhost`). With `escrow := false` it moves only when `F`
has run (thread 0 past `F`), the escrow-outside-`u` negative control. -/

open Kraken.Promising.Toy (unitPred mpAcq mpAcq')

def mpProgs (f : Instr) : List (List Instr) := [[st .plain 0 1, f], [ld .acq 0 1, ld .plain 1 0]]

def mpEscrowSpec (escrow : Bool) (rmw : Bool := false) : SSpec isa where
  rel y := if y == 1 then mpAcq else unitPred
  acqTab := [mpAcq, mpAcq']
  relMode w := (locIdx w.loc == 1 || (rmw && locIdx w.loc == 2)) && w.val.toNat == 1
  rmwMsg w := rmw && (locIdx w.loc == 1 || locIdx w.loc == 2) && w.val.toNat == 1
  assign v :=
    match v.threads[0]?, v.threads[1]? with
    | some t0, some t1 =>
      let flag := (msgs v).find? fun (ts, w) => ts != 0 && locIdx w.loc == 1 && w.val.toNat == 1
      let given := if escrow then flag.isSome else t0.st.pc ≥ 2
      let rest := (SRes.full 1).op (SRes.full 2)
      let r0 : SRes := if given then rest else (SRes.full 0).op rest
      let acquired := t1.st.pc ≥ 1 && t1.st.regs[0]! == 1
      (match flag with
      | some (ts, _) =>
        if acquired then ([r0, (SRes.full 0).op { acq := [(1, 1)] }], [(1, ts, 1, SRes.unit)])
        else if given then ([r0, { acq := [(1, 0)] }], [(1, ts, 0, SRes.full 0)])
        else ([r0, { acq := [(1, 0)] }], [])
      | none => ([r0, { acq := [(1, 0)] }], []))
    | _, _ => ([], [])
  dom := [SRes.unit, SRes.full 0, SRes.full 1, (SRes.full 0).op (SRes.full 1)]

-- `stp.rel`, flag first. Erasure with escrow holds at every configuration,
-- at `c` with every release promise pending and at pre-F; nothing pending
-- fails wherever the flag is promised (`relSettled`, and `slotsPred`/
-- `promValid` where `x := 1` is promised too). The (ii) advance through `F`
-- fails wherever `z := 1` is not promised with the flag.
/-- info: (96, 48, 0, 0, 0, 48, 12, [], ["slotsPred", "promValid", "relSettled"]) -/
#guard_msgs in #eval escrowCheck .armv8 (mpProgs (stp .rel 1 1 .plain 2 1)) (mpEscrowSpec true)
-- Escrow outside `u`: fails at every configuration with the flag promised.
/-- info: (96, 48, 0, 48, 48, 48, 12, ["slotsDom", "valid"], ["slotsDom", "relSettled", "valid"]) -/
#guard_msgs in #eval escrowCheck .armv8 (mpProgs (stp .rel 1 1 .plain 2 1)) (mpEscrowSpec false)
-- `stp`, flag last: the ordinary shape, where the (ii) advance succeeds
-- everywhere too; (iii) applies uniformly.
/-- info: (66, 24, 0, 0, 0, 24, 0, [], ["slotsPred", "promValid", "relSettled"]) -/
#guard_msgs in #eval escrowCheck .armv8 (mpProgs (stp .plain 2 1 .rel 1 1)) (mpEscrowSpec true)
-- `CASP.rel` on `(y, z)`, both halves release-mode RMW writes (claims of
-- the initial messages). The (ii) advance fails in the 20 configurations
-- where one half is promised without the other.
/-- info: (67, 44, 0, 0, 0, 44, 20, [], ["relSettled", "slotsPred", "promValid"]) -/
#guard_msgs in #eval escrowCheck .armv8 (mpProgs (casp .rel 0 1 0 0 1 1)) (mpEscrowSpec true (rmw := true))
-- Escrow outside `u`: fails wherever the flag half is promised and `F` has
-- not run.
/-- info: (67, 44, 0, 36, 36, 44, 20, ["slotsDom", "valid"], ["relSettled", "slotsDom", "valid"]) -/
#guard_msgs in #eval escrowCheck .armv8 (mpProgs (casp .rel 0 1 0 0 1 1)) (mpEscrowSpec false (rmw := true))

/-! ## A CAS spinlock whose unlock is the first write of `stp.rel`

ErasureTests' spinlock (`spinSpec`: update id `0` on `lock`, `φ(0) =
W¹(counter)`, half of `W(lock)` per thread), two threads running `CAS.acqRel
lock 0 → 1; retry if it read 1; counter := 1; stp.rel (lock := 0) (z := 1)`.
Locations: `lock = 0`, `counter = 1`, `z = 2` (a third of `W(z)` per
thread, unshared otherwise). The update slot with `W¹(counter)` hangs off every
unclaimed release message `lock = 0`, outstanding unlock promises included
(`escrow := true`): a thread at pre-F of its own promised unlock no longer
holds `W¹(counter)`. With `escrow := false` the thread keeps it until `F`
has run and outstanding unlocks carry no slot. -/

def spinStp : List Instr := [cas .acqRel 0 0 0 1, beq 0 1 0, st .plain 1 1, stp .rel 0 0 .plain 2 1]

def lockMsg (w : Msg) : Bool := locIdx w.loc == 0 && w.val.toNat == 0

def spinEscrowSpec (escrow : Bool) : SSpec isa where
  rel x := if x == 0 then Toy.lockPred else unitPred
  acqTab := [Toy.lockPred]
  relMode := lockMsg
  initRel x := x == 0
  upd x := if x == 0 then [0] else []
  rmwMsg := Toy.lockRmw
  assign v :=
    let unlockPromised (t : Thread isa) : Bool := t.prom.any fun ts => match v.mem.get? ts with
      | some w => lockMsg w
      | none => false
    let rF := (List.range v.threads.size).map fun i =>
      let cs := match v.threads[i]? with
        | some t => (t.st.pc == 1 && t.st.regs[0]! == 0) || t.st.pc == 2 ||
            (t.st.pc == 3 && !(escrow && unlockPromised t))
        | none => false
      ((SRes.frac 0 3).op (SRes.frac 2 3)).op (if cs then SRes.full 1 else SRes.unit)
    let cl := claimsWith Toy.lockRmw v []
    let relKeys := 0 :: ((msgs v).filter fun (ts, w) => ts != 0 && lockMsg w && (escrow || !outstandingB v ts)).map (·.1)
    (rF, (relKeys.filter fun ts => !cl.any (·.1 == (0, ts))).map fun ts => (0, ts, 0, SRes.full 1))
  dom := [SRes.unit, SRes.full 1]

-- Erasure with escrow holds at every configuration (with every promised
-- unlock pending, and at pre-F); nothing pending fails wherever an unlock is
-- promised; the (ii) advance fails in 1096 configurations (an unlock promised
-- without its `z := 1`). No `promValid` (R3) failure arises: the CAS is
-- `acqRel`, as in ErasureTests' `spinAcqRel`.
/-- info: (5241, 4632, 0, 0, 0, 4632, 1096, [], ["slotsDom", "relSettled", "promValid"]) -/
#guard_msgs in #eval escrowCheck .armv8 [spinStp, spinStp] (spinEscrowSpec true)
-- Escrow outside `u`: fails wherever an unlock is promised (the counter is
-- held by the unlocking thread and by the other thread once it acquires the
-- outstanding `lock = 0`: `valid`; or no update slot on it: `slotsDom`).
/-- info: (5241, 4632, 0, 4632, 4632, 4632, 1096, ["slotsDom", "valid", "promValid"],
  ["slotsDom", "relSettled", "valid", "promValid"]) -/
#guard_msgs in #eval escrowCheck .armv8 [spinStp, spinStp] (spinEscrowSpec false)

end Kraken.Promising.Toy2

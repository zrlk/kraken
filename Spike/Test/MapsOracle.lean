import Scc.Cert.MapsCompute

/-!
# The tables before the structural sort: an oracle for `Scc.Cert.Maps.compute` (untrusted test)

`Scc.Cert.Maps.leaders` and `Scc.Cert.Maps.compute` sort with `sortStable` (a structural stable
insertion sort the kernel reduces) where they sorted with `List.mergeSort`. The definitions below
are the forms before that change, kept verbatim except for the names (`fnMaps` and `fnSuccs` call
the old `leaders`; every other helper is unchanged and shared), except that a call's map lists
its `scc_stackmap` slots alone (the callee's argument registers it listed are gone), and that a
tail jump (a `jmp` out of the body) to a tagged function's symbol is succeeded by that function,
by name (`Succs.tail`; it had no successors). Since then `compute` follows the
label-keyed rules; the old tables are transformed by them (`computeTransformed`, below; the old
`outSuccs` is kept as `outSuccsOracle`) before the comparison. The tests
`Spike/Test/MapsOracleX64Test.lean`, `Spike/Test/MapsOracleA64Test.lean`,
`Spike/Test/MapsX64Test.lean` and `Spike/Test/MapsA64Test.lean` compare both on real texts.
-/

namespace Scc.Cert.MapsOracle
open Scc.Cert.Maps

/-- `leaders`, sorting with `List.mergeSort` (the old form). -/
def leadersOracle (body : List Item) : List Nat :=
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let tg := (is.toList.filterMap fun (_, _, i) => match i.flow with
    | .jmp l | .jcc l => lix.lookup l | _ => none).filter (· < n)
  let after := ((List.range n).filter fun k => match (is[k]!).2.2.flow with
    | .fall => false | _ => true).map (· + 1) |>.filter (· < n)
  ((if n = 0 then [] else [0]) ++ tg ++ after).eraseDups.mergeSort (· ≤ ·)

/-- `fnMaps` over `leadersOracle` (the old form). -/
def fnMapsOracle (t : FnTags) (items : List Item) : Except String (List RootMap) := do
  let pre ← t.paramPts.mapM fun l => match labelAddr items l with
    | some a => pure { pt := ⟨.blockEntry, a⟩, roots := t.params }
    | none => throw s!"{t.bodyStart}: no label {l}"
  let body := bodyOf t items
  let is := insOf body
  let live := liveSlots body
  let ls := leadersOracle body
  let grow ← match t.growStub with
    | none => pure none
    | some l => match growCall items l with
      | some c => pure (some c)
      | none => throw s!"{t.bodyStart}: no call after the grow stub {l}"
  let calls := is.toList.filterMap (fun (a, z, i) => match i.flow with
    | .call _ => some (a + z) | _ => none) ++ (grow.map fun (a, z, _) => a + z).toList
  for (ra, _) in t.stackmap do
    unless calls.contains ra do throw s!"{t.bodyStart}: scc_stackmap entry at {ra} is no call's return address"
  let ms ← (List.range is.size).mapM fun k => do
    let (a, z, i) := is[k]!
    let entry : List RootMap :=
      if ls.contains k then [{ pt := ⟨.blockEntry, a⟩, roots := liveRoots t (live[k]!) }] else []
    let own : List RootMap ← match i.flow with
      | .call _ => do
        let sl ← callRoots t (a + z)
        pure [{ pt := ⟨.call, a⟩, roots := sl }]
      | .ret => pure [{ pt := ⟨.ret, a⟩, roots := t.result }]
      | _ => pure []
    pure (entry ++ own)
  let gm ← match grow with
    | some (a, z, _) => do
      let sl ← callRoots t (a + z)
      pure [{ pt := ⟨.call, a⟩, roots := sl : RootMap }]
    | none => pure []
  pure (pre ++ ms.flatten ++ gm)

/-- `fnSuccs` over `leadersOracle` (the old form), plus the tail-jump rule `compute` follows since:
a `jmp` out of the body is succeeded by its target, by name (`Succs.tail`; `_fns` is unused, the
checkers decide that the target is a function). -/
def fnSuccsOracle (_fns : List FnTags) (t : FnTags) (items : List Item) : List Succs :=
  let body := bodyOf t items
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let ls := leadersOracle body
  let addrOf (j : Nat) : Nat := (is[j]!).1
  let rec walk : Nat → Nat → List Nat × List String
    | 0, _ => ([], [])
    | f + 1, k =>
      if k ≥ n then ([], []) else
      let (a, _, i) := is[k]!
      match i.flow with
      | .call _ | .ret => ([a], [])
      | .stop => ([], [])
      | .jcc _ => ((succIdx lix n k i).map addrOf, [])
      | .jmp l => match succIdx lix n k i with
        | [] => ([], [l])
        | js => (js.map addrOf, [])
      | .fall => if ls.contains (k + 1) then (if k + 1 < n then ([addrOf (k + 1)], []) else ([], []))
          else walk f (k + 1)
  ls.map fun k => let (nx, tl) := walk (n + 1) k; ⟨addrOf k, nx, tl⟩

/-- `compute`, sorting with `List.mergeSort` (the old form). -/
def computeOracle (fns : List FnTags) (items : List Item) : Except String Tables := do
  let ms ← fns.mapM fun t => fnMapsOracle t items
  let os ← (fns.zip ms).mapM fun (t, m) => outSuccs t items (m.map (·.pt.addr))
  pure { maps := ms.flatten.mergeSort (fun a b => a.pt.addr ≤ b.pt.addr),
         succs := (fns.flatMap (fun t => fnSuccsOracle fns t items) ++ os.flatten).mergeSort
           (fun a b => a.addr ≤ b.addr) }

/-! ## The label-keyed rules as a transformation of the old tables

`compute` now follows the label-keyed rules: a `jcc; jmp` pair is one
terminator, a leader after a `jmp`, a `ret` or a block end must be a branch target, a call's map
is keyed at its return address, and both it and the block-entry map there add the call's result
registers (`FnTags.callRes`, the `k`th entry for the `k`th call of the body). The oracle computes the tables by the old rules (`fnMapsOracle`,
`fnSuccsOracle`, `outSuccsOracle`: the forms before that change, kept verbatim) and transforms
them by the same rules, stated on the old tables (`transformFn`); `agrees` compares the result
with `compute`. -/

/-- `outSuccs` before the label-keyed rules (the old form): the grow call's return address
follows the call's successors (its call map was at the call instruction). -/
def outSuccsOracle (t : FnTags) (items : List Item) (pts : List Nat) : Except String (List Succs) := do
  let is := insOf items
  let n := is.size
  let lix := labelIdx items
  let rec walk : Nat → Nat → List Nat
    | 0, _ => []
    | f + 1, k =>
      if k ≥ n then [] else
      let (a, _, i) := is[k]!
      if pts.contains a then [a] else
      match i.flow with
      | .stop | .ret => []
      | .fall | .call _ => walk f (k + 1)
      | .jmp l => match lix.lookup l with | some j => walk f j | none => []
      | .jcc l => (match lix.lookup l with | some j => walk f j | none => []) ++ walk f (k + 1)
  -- the successors of the instruction at index `k`, not counting `k` itself
  let nexts (k : Nat) : List Nat :=
    if k ≥ n then [] else
    let (_, _, i) := is[k]!
    let nx := walk n (k + 1)
    let tg (l : String) := match lix.lookup l with | some j => walk n j | none => []
    (match i.flow with
      | .stop | .ret => []
      | .fall | .call _ => nx
      | .jmp l => tg l
      | .jcc l => tg l ++ nx).eraseDups
  let pre ← t.paramPts.mapM fun l => match lix.lookup l, labelAddr items l with
    | some k, some a => pure ({ addr := a, next := nexts k } : Succs)
    | _, _ => throw s!"{t.bodyStart}: no label {l}"
  let grow : List Succs := match t.growStub.bind (growCall items ·) with
    | some (a, z, _) => match (List.range n).find? (fun k => (is[k]!).1 == a) with
      | some k => [{ addr := a + z, next := nexts k }]
      | none => []
    | none => []
  pure (pre ++ grow)

/-- The calls of a text: the call instruction's address, its return address and the callee. -/
def callsOf (items : List Item) : List (Nat × Nat × String) :=
  items.filterMap fun
    | .ins a z i => match i.flow with | .call g => some (a, a + z, g) | _ => none
    | _ => none

/-- The old leaders the new rules drop (addresses): an instruction after a `jmp`, a `ret`, a
block end, or after a conditional branch that it completes as a `jmp`, unless it is a branch
target. -/
def droppedOf (body : List Item) : List Nat :=
  let is := insOf body
  let n := is.size
  let lix := labelIdx body
  let tg := (is.toList.filterMap fun (_, _, i) => match i.flow with
    | .jmp l | .jcc l => lix.lookup l | _ => none).filter (· < n)
  let isJmp (j : Nat) : Bool := match (is[j]!).2.2.flow with | .jmp _ => true | _ => false
  ((List.range n).filter fun k => k + 1 < n && !tg.contains (k + 1) &&
    match (is[k]!).2.2.flow with
    | .jmp _ | .ret | .stop => true
    | .jcc _ => isJmp (k + 1)
    | _ => false).map fun k => (is[k + 1]!).1

/-- **The rules, applied to one function's old tables** (`ms` its maps, `bs` its body successors,
`os` its successors outside the body):
* a call map moves to its return address (before the block-entry map there); both append and
  prepend, respectively, the call's result registers (the `k`th call of the body, the `k`th entry
  of `FnTags.callRes`; none for the grow stub's call, outside the body);
* the dropped leaders lose their block-entry maps and successor entries, and a successor list
  naming one names its successors instead (the `jmp` of a `jcc; jmp` terminator: its target);
* a successor that named a call instruction for the call (in the body: the block's own call, or
  one that is no leader; outside it: one that is no block entry) names its return address;
* the function's entry (the first of `paramPts`) and its `ret`s are frameless
  (`RootMap.frameless`). -/
def transformFn (t : FnTags) (items : List Item) (ms : List RootMap) (bs os : List Succs) :
    List RootMap × List Succs :=
  let cs := callsOf items
  let ra (x : Nat) : Option Nat := (cs.find? (·.1 == x)).map (·.2.1)
  -- the result registers of the body's calls, by return address
  let res := (callsOf (bodyOf t items)).map (·.2.1) |>.zip t.callRes
  let resAt (r : Nat) : List (Loc × Tag) := (res.lookup r).getD []
  let dropped := droppedOf (bodyOf t items)
  let leaders := bs.map (·.addr)
  let entries := ms.filterMap fun m => if m.pt.kind == .blockEntry then some m.pt.addr else none
  -- the function's entry (the first of `paramPts`): frameless, as the `ret`s
  let entry := t.paramPts.head?.bind (labelAddr items ·)
  let ms' := ms.filterMap fun m =>
    if m.pt.kind == .blockEntry && dropped.contains m.pt.addr then none else
    match m.pt.kind with
    | .call =>
      let r := (ra m.pt.addr).getD m.pt.addr
      some { pt := ⟨.call, r⟩, roots := m.roots ++ resAt r }
    | .blockEntry => some { m with roots := resAt m.pt.addr ++ m.roots,
                                   frameless := entry == some m.pt.addr }
    | .ret => some { m with frameless := true }
    | _ => some m
  let bodyNext (s : Succs) : List Nat := s.next.map fun x =>
    match ra x with
    | some r => if x == s.addr || !leaders.contains x then r else x
    | none => x
  let bs1 := bs.map fun s => (s.addr, bodyNext s)
  let subst (l : List Nat) : List Nat := l.flatMap fun x =>
    if dropped.contains x then ((bs1.lookup x).getD []) else [x]
  -- a tail name stays with its block (no dropped leader is a tail jump's block)
  let bs' := (bs.filter fun s => !dropped.contains s.addr).map fun s =>
    ({ addr := s.addr, next := subst (bodyNext s), tail := s.tail } : Succs)
  let os' := os.map fun s => ({ addr := s.addr, next := (subst (s.next.map fun x =>
    match ra x with
    | some r => if entries.contains x then x else r
    | none => x)).eraseDups } : Succs)
  (ms', bs' ++ os')

/-- The old tables, transformed by the label-keyed rules (`transformFn`), sorted by address (a
call map before the block-entry map at its return address). -/
def computeTransformed (fns : List FnTags) (items : List Item) : Except String Tables := do
  let ms ← fns.mapM fun t => fnMapsOracle t items
  let os ← (fns.zip ms).mapM fun (t, m) => outSuccsOracle t items (m.map (·.pt.addr))
  let rs := ((fns.zip ms).zip os).map fun ((t, m), o) => transformFn t items m (fnSuccsOracle fns t items) o
  let rank (m : RootMap) : Nat := if m.pt.kind == .call then 0 else 1
  pure { maps := (rs.flatMap (·.1)).mergeSort
           (fun a b => a.pt.addr < b.pt.addr || (a.pt.addr == b.pt.addr && rank a ≤ rank b)),
         succs := (rs.flatMap (·.2)).mergeSort (fun a b => a.addr ≤ b.addr) }

/-- Both computations succeed and agree (maps, successors and the `rseq` table), or both fail:
`compute` against the old tables transformed by the label-keyed rules (`computeTransformed`),
and the leaders against the old ones (`leadersOracle`) without the dropped ones. -/
def agrees (fns : List FnTags) (items : List Item) : Bool :=
  match compute fns items, computeTransformed fns items with
  | .ok t, .ok o => t.maps == o.maps && t.succs == o.succs && t.rseq == o.rseq &&
      fns.all fun f =>
        let body := bodyOf f items
        let is := insOf body
        let d := droppedOf body
        leaders body == (leadersOracle body).filter fun k => !d.contains (is[k]!).1
  | .error _, .error _ => true
  | _, _ => false

/-- How many old leaders the new rules drop, over all functions (so that a test can tell the
rules were exercised). -/
def droppedCount (fns : List FnTags) (items : List Item) : Nat :=
  fns.foldl (fun n f => n + (droppedOf (bodyOf f items)).length) 0

end Scc.Cert.MapsOracle

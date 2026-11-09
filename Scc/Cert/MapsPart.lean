import Scc.Cert.MapsCompute
import Lean.ToExpr

/-!
# The tables of a text, one function at a time (untrusted)

The statement a certificate makes about the tables (`tables_ok`, `Scc/Cert/Gen.lean`).
Neither the checker on the whole text (`checkW`) nor the computation of the runtime routines'
tables fits in a certificate's kernel run. So the statement is made per function, on the function's
own items: its **slice** of the text (`Scc.Cert.MapsX64.sliceFn`, `Scc.Cert.MapsA64.sliceFn`),
with its tags, **rebased** to its entry label (`rebaseI`, `rebaseFT`: every address minus the
entry's), so that a runtime routine's slice, tables and witness are the same in every program
whose text has the same routine.

For each function `i` the certificate gives a liveness witness `w` and the function's tables `t`
(rebased, as literals), and `fnOk` checks them on the slice: the slice computes, `w` is a
post-fixpoint of slot liveness on the body (`liveOk`), and `t` is the tables `computeW` builds
from it and has the format's shape (`Tables.g1Ok`). A jump out of the slice's body names its
target (`Succs.tail`), whatever the target is, and the check requires it to be one of the
program's function symbols `names` (`Tables.tailsIn`; the same list for every function, and the
one scc's whole-text checker uses, `fnNames`): a jump out of the body to anything else fails
`fnOk`. A name needs no rebasing, so the per-function tables merged in address order are the whole text's by
construction, tail successors included. `fnsOkFrom` chains the functions, in the order of
the IR, so that a certificate checks each in a kernel run of its own and the whole by
`fnsOkFrom_cons` (`fnsOkFrom_spec`: what the chain says of each function).

A function's check is itself split in three (`fnOk_of`): the slice (`sliceFn … = .ok …`, on
literals), the witness (`liveOk`) and the tables (`computeW`, `g1Ok`), each on the slice's literal,
so that the kernel holds one part's terms at a time.

What this does not say: that the per-function tables, put back at their entries and merged in
address order, are the tables of the whole text (the merge is `sortStable` of the concatenation,
as `compute`; scc checks it, W1), nor that `w` is the least fixpoint (scc checks the tables
against `compute`, W1; `liveSlots_le`: any post-fixpoint lists every slot the least one does).

The `Lean.ToExpr` instances of the tables' types are here, for the certificate's literals
(`scc_lit%`, `Scc/Cert/OutLit.lean`).
-/

namespace Scc.Cert.Maps

-- In the namespace: the derived instances' names (`instToExprItem`, …) would clash at the root
-- with other modules' (`Scc/Cert/OutStageX64.lean`'s `Scc.Emit.X64.Item`).
deriving instance Lean.ToExpr for Loc
deriving instance Lean.ToExpr for Tag
deriving instance Lean.ToExpr for Derived
deriving instance Lean.ToExpr for Kind
deriving instance Lean.ToExpr for SafePt
deriving instance Lean.ToExpr for RootMap
deriving instance Lean.ToExpr for Succs
deriving instance Lean.ToExpr for Rseq
deriving instance Lean.ToExpr for Tables
deriving instance Lean.ToExpr for Flow
deriving instance Lean.ToExpr for Ins
deriving instance Lean.ToExpr for Item
deriving instance Lean.ToExpr for FnTags

/-- `items` with every address less `d` (a slice rebased to its entry at `d`). -/
def rebaseI (d : Nat) : List Item → List Item
  | [] => []
  | .label a l :: r => .label (a - d) l :: rebaseI d r
  | .ins a z i :: r => .ins (a - d) z i :: rebaseI d r

/-- Tags with their `scc_stackmap` return addresses less `d` (the only addresses of `FnTags`). -/
def rebaseFT (d : Nat) (t : FnTags) : FnTags :=
  { t with stackmap := t.stackmap.map fun (a, st, hp) => (a - d, st, hp) }

/-- **Function check**, a tail jump entering one of `names`: the function's rebased slice `r`
(entry address, items, tags) computes, the witness `w` is a post-fixpoint on its body, and `t` is
the tables built from `w`, of the format's shape, its tail names among `names` (`checkWWith` on
the one function). -/
def fnOk (names : List String) (r : Except String (Nat × List Item × FnTags)) (w : Array (List Int))
    (t : Tables) : Bool :=
  match r with
  | .ok (_, items, ft) => checkWWith names [ft] items [w] t
  | .error _ => false

/-- `fnOk` from its parts: the slice, the witness, the tables (computed, of the format's shape,
their tail names among `names`). -/
theorem fnOk_of {names : List String} {r : Except String (Nat × List Item × FnTags)} {e : Nat}
    {items : List Item} {ft : FnTags} {w : Array (List Int)} {t : Tables}
    (hs : r = .ok (e, items, ft)) (hw : liveOk (bodyOf ft items) w = true)
    (hc : computeW [ft] items [w] = .ok t) (hg : t.g1Ok = true)
    (hn : t.tailsIn names = true) : fnOk names r w t = true := by
  subst hs
  simp [fnOk, checkWWith, hw, hc, hg, hn]

/-- `fnOk_of` with the slice as one triple `s` (a certificate's literal: `sliceFn … = .ok s`,
then the witness and the tables on `s`'s items and tags) and the names as a literal `ns` (`hns`:
`names = ns`). -/
theorem fnOk_of_lit {names ns : List String} {r : Except String (Nat × List Item × FnTags)}
    {s : Nat × List Item × FnTags} {w : Array (List Int)} {t : Tables} (hns : names = ns)
    (hs : r = .ok s) (hw : liveOk (bodyOf s.2.2 s.2.1) w = true)
    (hc : computeW [s.2.2] s.2.1 [w] = .ok t) (hg : t.g1Ok = true)
    (hn : t.tailsIn ns = true) : fnOk names r w t = true := by
  subst hns
  exact fnOk_of hs hw hc hg hn

/-- **What `fnOk` says**: the slice computes, the witness is a post-fixpoint on its body, and the
tables are the ones built from it, of the format's shape, their tail names among `names`. -/
theorem fnOk_spec {names : List String} {r : Except String (Nat × List Item × FnTags)}
    {w : Array (List Int)} {t : Tables} (h : fnOk names r w t = true) :
    ∃ e items ft, r = .ok (e, items, ft) ∧ liveOk (bodyOf ft items) w = true ∧
      computeW [ft] items [w] = .ok t ∧ t.g1Ok = true ∧ t.tailsIn names = true := by
  unfold fnOk at h
  split at h
  · rename_i e items ft
    obtain ⟨hl, hc, hg, hn⟩ := checkWWith_sound h
    exact ⟨e, items, ft, rfl, hl (ft, w) (by simp), hc, hg, hn⟩
  · simp at h

/-- **The functions from `i` on**: function `i + k` (its slice `sl (i + k)`) passes `fnOk names`
with the `k`th witness and tables of `ws`. -/
def fnsOkFrom (names : List String) (sl : Nat → Except String (Nat × List Item × FnTags)) :
    Nat → List (Array (List Int) × Tables) → Bool
  | _, [] => true
  | i, (w, t) :: r => fnOk names (sl i) w t && fnsOkFrom names sl (i + 1) r

theorem fnsOkFrom_cons {names : List String} {sl : Nat → Except String (Nat × List Item × FnTags)}
    {i : Nat} {w : Array (List Int)} {t : Tables} {r : List (Array (List Int) × Tables)}
    (h : fnOk names (sl i) w t = true) (hr : fnsOkFrom names sl (i + 1) r = true) :
    fnsOkFrom names sl i ((w, t) :: r) = true := by
  simp [fnsOkFrom, h, hr]

/-- **What the chain says**: every function `i + k` with an entry `k` of `ws` passes `fnOk`. -/
theorem fnsOkFrom_spec {names : List String} {sl : Nat → Except String (Nat × List Item × FnTags)} :
    ∀ {i : Nat} {ws : List (Array (List Int) × Tables)}, fnsOkFrom names sl i ws = true →
      ∀ k (hk : k < ws.length), fnOk names (sl (i + k)) ws[k].1 ws[k].2 = true
  | _, [], _, k, hk => absurd hk (by simp)
  | i, (w, t) :: r, h, k, hk => by
    simp only [fnsOkFrom, Bool.and_eq_true] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := fnsOkFrom_spec h.2 k (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- **The tables of functions `0` to `n - 1`**, a tail jump entering one of `names`: each
function's rebased slice computes and has a witness and tables that pass `fnOk names`. A
certificate states it of `n` the number of functions of its IR and `names` their symbols
(`tables_ok`, `Scc/Cert/Gen.lean`): the statement names no literal, so it is the same whichever
module the witnesses and tables come from. The certificate's `names` (the IR functions' names,
`funcs.map (·.name)`) and the whole-text checker's (`fnNames` of the front ends' tags) are equal,
in order, by construction: the front ends' `tagsOf` give each IR function `paramPts` headed by its
name (`MapsX64.tagsOf`, `MapsA64.tagsOf`), and the tags are mapped over the IR's functions. So
the parts' tables merged are the whole text's. -/
def FnsOk (names : List String) (sl : Nat → Except String (Nat × List Item × FnTags)) (n : Nat) :
    Prop :=
  ∀ i < n, ∃ w t, fnOk names (sl i) w t = true

/-- `FnsOk` from a chain from 0 as long as `n`. -/
theorem fnsOk_of_from {names : List String} {sl : Nat → Except String (Nat × List Item × FnTags)}
    {ws : List (Array (List Int) × Tables)} {n : Nat} (h : fnsOkFrom names sl 0 ws = true)
    (hn : ws.length = n) : FnsOk names sl n := by
  intro i hi
  have := fnsOkFrom_spec h i (hn ▸ hi)
  exact ⟨_, _, by simpa using this⟩

/-! ## Tests -/

-- The toy function of `MapsCompute`, rebased by 0 and its tables built from scc's witness, passes
-- `fnOk`; with a dropped live slot it does not; a slice that fails does not.
#guard (match compute [toyTags] toyItems with
  | .ok t => fnOk (fnNames [toyTags]) (.ok (0, toyItems, toyTags)) (liveSlots (bodyOf toyTags toyItems)) t
  | .error _ => false)
#guard (match compute [toyTags] toyItems with
  | .ok t => !fnOk (fnNames [toyTags]) (.ok (0, toyItems, toyTags)) #[[], [-8], [-8], [], [], []] t
  | .error _ => false)
#guard !fnOk [] (.error "no slice") #[] { maps := [], succs := [] }
-- A tail jump's target is in the tables by name whatever it is; only names that list it pass
-- `fnOk`. A jump out of the body to a label that is not a function (`e.stub`, a local stub
-- outside the body) fails it as well.
#guard (let its := toyJItems.take 5 ++ [.ins 12 4 { flow := .jmp "t" }] ++ toyJItems.drop 6
  let e : FnTags := { toyJTags with paramPts := ["e"] }
  match compute [e] its with
  | .ok t => t.succs.any (·.tail == ["t"]) && t.tailsIn ["e", "t"] && !t.tailsIn ["e"] &&
      !fnOk (fnNames [e]) (.ok (0, its, e)) (liveSlots (bodyOf e its)) t
  | .error _ => false)
#guard (let its := toyJItems.take 5 ++ [.ins 12 4 { flow := .jmp "e.stub" }] ++ toyJItems.drop 6
  let e : FnTags := { toyJTags with paramPts := ["e"] }
  match compute [e] its with
  | .ok t => t.succs.any (·.tail == ["e.stub"]) &&
      !fnOk (fnNames [e]) (.ok (0, its, e)) (liveSlots (bodyOf e its)) t
  | .error _ => false)
-- Rebasing moves every address, and the `scc_stackmap` return addresses with them.
#guard rebaseI 8 [.label 8 "f", .ins 8 4 {}, .label 12 "f.b"] == [.label 0 "f", .ins 0 4 {}, .label 4 "f.b"]
#guard (rebaseFT 8 toyTags).stackmap == [(12, [], [-8])]

/-- info: 'Scc.Cert.Maps.fnsOkFrom_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnsOkFrom_spec

-- A chain of one function, decided as a certificate decides it (`fnsOk_of_from`).
example : FnsOk (fnNames [toyTags]) (fun _ => .ok (0, toyItems, toyTags)) 1 :=
  fnsOk_of_from (ws := [(liveSlots (bodyOf toyTags toyItems),
    ((compute [toyTags] toyItems).toOption.getD default))]) (by decide +kernel) rfl

/-- info: 'Scc.Cert.Maps.fnsOk_of_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms fnsOk_of_from

end Scc.Cert.Maps

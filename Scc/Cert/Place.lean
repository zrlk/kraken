import Scc.Lower.Program
import Scc.Cert.Blocks

/-!
# Placement data (`scc --blocks`, AArch64)

The data the proof library's node invariants need (`Spike/Lib/Form.lean`:
at a node, `c.term = t ∧ EnvRep lbl (opdVal rs σ.slot) ρ c.env`), per
compiled function, from the lowering's placement trace
(`Scc.Lower.lowerDeclMarks`) and the emitter's frame (`FnPlace`, given by
the ISA's module, `Scc/Cert/PlaceA64.lean`):

* `<fn>Node`, the function's nodes: one constructor per block start (named
  `b` and the assembler label's local part, e.g. `b0_entry` for
  `.L18_wc_rodata.0_entry`) and per call return point (its safepoint label's,
  e.g. `sp0` for `.L18_wc_rodata.sp0`), and `<fn>_label`, their assembler
  labels;
* `<fn>_rs`, each IR register's frame slot: its offset from the base of the
  function's stack region in the block data (`block_spec`'s `σ.slot k`);
* `<fn>_env n x`, the shape type and the IR operands (one per word) of source
  variable `x` at node `n`, `none` where the lowering has none (the innermost
  binding of `x`: the lowering's `Env` read as a lookup);
* `<fn>_term n`, the term that remains at node `n`, as `<fn>_t<j>`, the
  distinct terms (smallest first, each written with the earlier ones it
  contains, so they share structure).

What the source point of a node is (`Scc.Lower.lowerExpr`): at a block the
term opens (`entry`, an `if`'s branches) its variables and the term there; at
the return point of the call of a code block, `let x = f(a); e`, the
variables with `x`, whose IR registers the emitter stores from the result
registers right after the label, and `e`; at any other node inside the
lowering of `let x = op; e` (the return of a runtime call, a block of `op`'s
own), the variables before it and `let x = op; e` itself.

The file is a self-contained Lean module (`namespace SccPlace`); it is
written next to the block data, and the Lean check of the test programs'
block data checks it (`Scc/Test/blocks.sh --check`). This module imports no
ISA.
-/

namespace Scc.Cert.Place

open CoreLang CoreTerm Scc.Lower
open Scc.Cert.Blocks (ident fnId)

/-- What the emitter fixes of one function: its IR registers' slots (offsets
from the region base of the block data) and its nodes' assembler labels. -/
structure FnPlace where
  name : IR.Sym
  slots : List (IR.Reg × Int)
  labels : List (Node × String)

/-- `x` as a Lean term in argument position (its derived `Repr`). -/
def arg {α} [Repr α] (x : α) : String := (reprArg x).pretty 1000000

/-- A term as Lean source, its subterms in `named` (by their full text)
written as the names given. -/
partial def term (named : List (String × String)) (e : Expr) : String :=
  match named.lookup (arg e) with
  | some n => n
  | none =>
    let go := term named
    let c (s : String) := s!"(CoreTerm.Expr.{s})"
    match e with
    | .let_ x op e => c s!"let_ {arg x} {arg op} {go e}"
    | .split a x y e => c s!"split {arg a} {arg x} {arg y} {go e}"
    | .unpack a i x e => c s!"unpack {arg a} {arg i} {arg x} {go e}"
    | .unpackT a α x e => c s!"unpackT {arg a} {arg α} {arg x} {go e}"
    | .region a r p t e => c s!"region {arg a} {arg r} {arg p} {arg t} {go e}"
    | .openPub a r p k e => c s!"openPub {arg a} {arg r} {arg p} {arg k} {go e}"
    | .case a x e₁ y e₂ => c s!"case {arg a} {arg x} {go e₁} {arg y} {go e₂}"
    | .ifnull a e₁ x e₂ => c s!"ifnull {arg a} {go e₁} {arg x} {go e₂}"
    | .parity a k e₁ e₂ => c s!"parity {arg a} {arg k} {go e₁} {go e₂}"
    | .ifeq a b e₁ e₂ => c s!"ifeq {arg a} {arg b} {go e₁} {go e₂}"
    | .cas acq rel w x v t e₁ e₂ =>
        c s!"cas {arg acq} {arg rel} {arg w} {arg x} {arg v} {arg t} {go e₁} {go e₂}"
    | .casp acq rel w e0 e1 v0 v1 t e₁ e₂ =>
        c s!"casp {arg acq} {arg rel} {arg w} {arg e0} {arg e1} {arg v0} {arg v1} {arg t} {go e₁} {go e₂}"
    | .ret a => c s!"ret {arg a}"
    | .tail f is a ts => c s!"tail {arg f} {arg is} {arg a} {arg ts}"

/-- The constructor of a node: `b` and its block label's local part, or its
safepoint label's (the part after the function's label prefix,
`.L<k>_<fn>.`). -/
def ctor (n : Node) (lab : String) : String :=
  let loc := ".".intercalate ((lab.splitOn ".").drop 2)
  match n with
  | .block _ => "b" ++ ident loc
  | .ret .. => ident loc

/-- A string as a Lean pattern. -/
def str (s : String) : String := arg s

/-- The placement data of one function (see the module docstring). -/
def renderFn (fp : FnPlace) (marks : Array (Node × Point)) : Except String String := do
  let f := fnId fp.name
  let ty := s!"{f}Node"
  -- the nodes with an assembler label, in code order
  let mut nodes : Array (String × String × Node × Point) := #[]
  for (n, lab) in fp.labels do
    if let some (_, p) := marks.find? (·.1 == n) then
      nodes := nodes.push (ctor n lab, lab, n, p)
  for (n, _) in marks do
    unless fp.labels.any (·.1 == n) do
      throw s!"{fp.name}: no assembler label for the node {repr n}"
  if nodes.isEmpty then throw s!"{fp.name}: no nodes"
  let mut out : Array String := #[]
  let what : Node → String
    | .block l => s!"the start of IR block `{l}`"
    | .ret l i => s!"the return point of the call, instruction {i} of IR block `{l}`"
  out := out.push s!"/-! ## `{fp.name}` -/

/-- The nodes of `{fp.name}`. -/
inductive {ty} where
{"\n".intercalate (nodes.toList.map fun (c, lab, n, _) => s!"  /-- `{lab}`: {what n}. -/\n  | {c}")}
  deriving DecidableEq, Repr

/-- The assembler label of each node of `{fp.name}`. -/
def {f}_label : {ty} → String
{"\n".intercalate (nodes.toList.map fun (c, lab, _, _) => s!"  | .{c} => {str lab}")}

/-- The frame slot of each IR register of `{fp.name}`: its offset from the
base of the function's stack region in the block data (`σ.slot k`). -/
def {f}_rs : Scc.IR.Reg → Option Int
{"\n".intercalate (fp.slots.map fun (r, k) => s!"  | {str r} => some ({k})")}
  | _ => none
"
  -- the distinct terms, smallest first, each with the earlier ones named
  let terms := (nodes.toList.map (fun (_, _, _, p) => p.2)).foldl
    (fun acc e => if acc.any (arg · == arg e) then acc else acc ++ [e]) []
  let terms := (terms.toArray.qsort fun a b => (arg a).length < (arg b).length).toList
  let mut named : List (String × String) := []
  for (e, j) in terms.zipIdx do
    let nm := s!"{f}_t{j}"
    out := out.push s!"def {nm} : CoreTerm.Expr :=\n  {term named e}\n"
    named := named ++ [(arg e, nm)]
  out := out.push s!"/-- The term that remains at each node of `{fp.name}`. -/
def {f}_term : {ty} → CoreTerm.Expr
{"\n".intercalate (nodes.toList.map fun (c, _, _, p) => s!"  | .{c} => {(named.lookup (arg p.2)).getD "default"}")}
"
  -- the variables: the innermost binding of each name
  let envOf (env : List (String × Ty × List IR.Operand)) : List String :=
    let names := env.foldl (fun acc (x, _, _) => if acc.contains x then acc else acc ++ [x]) []
    names.filterMap fun x => (env.lookup x).map fun (t, ws) =>
      s!"    | {str x} => some ({arg t}, {arg ws})"
  out := out.push s!"/-- The shape type and IR operands of each source variable at each node of
`{fp.name}`. -/
def {f}_env : {ty} → String → Option (CoreLang.Ty × List Scc.IR.Operand)
{"\n".intercalate (nodes.toList.map fun (c, _, _, p) =>
    s!"  | .{c} => fun\n" ++ "\n".intercalate (envOf p.1 ++ ["    | _ => none"]))}
"
  return "\n".intercalate out.toList

/-! ## The immediate table (`scc --code`) -/

/-- The immediate entries of a program's placement traces: for each node,
each source variable (its innermost binding) and each of its words that the
lowering keeps as an immediate, `(term, variable, word, constant)`, the term
the one that remains at the node. -/
def immEntries (marks : List (IR.Sym × Array (Node × Point))) : List (Expr × String × Nat × Nat) :=
  marks.flatMap fun (_, ms) => ms.toList.flatMap fun (_, (env, e)) =>
    let names := env.foldl (fun acc (x, _, _) => if acc.contains x then acc else acc ++ [x]) []
    names.flatMap fun x => match env.lookup x with
      | some (_, ws) => ws.zipIdx.filterMap fun
          | (.imm c, k) => some (e, x, k, c.toNat)
          | _ => none
      | none => []

/-- **The immediate table** of a program (`scc --code`, both ISAs), for
`Scc.Sem.Layout.imms`: `{pfx}Imms e x k` is the constant of word `k` of
source variable `x` wherever the term `e` remains at a node whose lowering
keeps it as an immediate (`immEntries`), `none` elsewhere. The terms are
compared by propositional equality (`CoreTerm.Expr` has no decidable
equality), so the table is noncomputable when not empty. Two entries with
the same key and different constants are an error: the table is a function.
-/
def renderImms (pfx : String) (marks : List (IR.Sym × Array (Node × Point))) : Except String String := do
  -- the entries by term (in first-seen order), then by variable and word
  let mut byTerm : Array (Expr × Array (String × Nat × Nat)) := #[]
  for (e, x, k, c) in immEntries marks do
    match byTerm.findIdx? (arg ·.1 == arg e) with
    | some i =>
      let es : Array (String × Nat × Nat) := (byTerm[i]?.map (·.2)).getD #[]
      match es.find? fun (x', k', _) => x' == x && k' == k with
      | some (_, _, c') =>
        if c' != c then
          throw s!"the variable {x}'s word {k} is the immediate {c'} and {c} at the same term: \
            the immediate table would not be a function"
      | none => byTerm := byTerm.set! i (e, es.push (x, k, c))
    | none => byTerm := byTerm.push (e, #[(x, k, c)])
  if byTerm.isEmpty then
    return s!"/-- The immediate table (`Scc.Sem.Layout.imms`): no immediates. -/
def {pfx}Imms : CoreTerm.Expr → String → Nat → Option Nat := fun _ _ _ => none
"
  -- the terms, smallest first, each written with the earlier ones it contains
  let terms := (byTerm.map (·.1)).qsort fun a b => (arg a).length < (arg b).length
  let mut out : Array String := #[]
  let mut named : List (String × String) := []
  for (e, j) in terms.toList.zipIdx do
    let nm := s!"{pfx}Imm_t{j}"
    out := out.push s!"/-- A term at which the lowering keeps an immediate. -/\ndef {nm} : CoreTerm.Expr :=\n  {term named e}\n"
    named := named ++ [(arg e, nm)]
  let branch (g : Expr × Array (String × Nat × Nat)) : String :=
    let cases := g.2.toList.map fun (x, k, c) => s!"      | {str x}, {k} => some {c}"
    s!"if e = {(named.lookup (arg g.1)).getD "default"} then\n    match x, k with\n" ++
      "\n".intercalate (cases ++ ["      | _, _ => none"])
  out := out.push s!"open Classical in
/-- **The immediate table** (`Scc.Sem.Layout.imms`): the constant of word `k`
of source variable `x` where the term `e` remains at a node whose lowering
keeps it as an immediate (`Scc.Cert.Place.renderImms`). -/
noncomputable def {pfx}Imms : CoreTerm.Expr → String → Nat → Option Nat := fun e x k =>
  {"\n  else ".intercalate (byTerm.toList.map branch)}
  else none
"
  return "\n".intercalate out.toList

/-- **The placement data file** of a program (`scc --blocks`): for each
compiled function with a trace in `marks`, its `renderFn`, in code order. -/
def render (name : String) (fps : List FnPlace) (marks : List (IR.Sym × Array (Node × Point))) :
    Except String String := do
  let mut parts : Array String := #[]
  for fp in fps do
    if let some ms := marks.lookup fp.name then
      parts := parts.push (← renderFn fp ms)
  return s!"import WeakCore.CoreTerm
import Scc.IR.Core

/-!
# Placement data of `{name}`

Generated by `scc --blocks` (`Scc/Cert/Place.lean`): per compiled function,
its nodes (block starts and call return points, by assembler label), its IR
registers' frame slots (offsets from the base of its stack region in the
block data), and at each node the source variables' shape types and IR
operands and the term that remains.
-/

namespace SccPlace

{"\n".intercalate parts.toList}
end SccPlace
"

end Scc.Cert.Place

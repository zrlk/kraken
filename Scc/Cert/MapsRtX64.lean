import Scc.Cert.MapsRt
import Scc.Cert.MapsX64

/-!
# The runtime routines' tables on x64 (untrusted)

The tables of the constant runtime routines (`Scc.Cert.Maps.constRoutine`) of an x64 text,
computed (`rtTablesOf`) and keyed by routine-relative keys (`rtRelOf`, `Scc.Cert.Maps.RKey`): the
source of the constants of `Scc.Cert.MapsRtConstX64`, and what the tests compare them against.
-/

namespace Scc.Cert.MapsX64
open Maps

/-- The constant runtime routines of `p`. -/
def rtFuncs (p : IR.Program) : List IR.Func := p.funcs.filter (constRoutine ·.name)

/-- **The tables of `p`'s constant runtime routines** on the text `its` with instruction sizes
`sizes` (`compute` restricted to them). -/
def rtTablesOf (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String Tables := do
  let items ← itemsOf its sizes
  let tbl ← stackTable its items
  let fns ← (rtFuncs p).mapM (tagsOf p items tbl)
  compute fns items

/-- **`rtTablesOf`, keyed by routine-relative keys.** -/
def rtRelOf (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String RTables := do
  let items ← itemsOf its sizes
  relTables endL items ((rtFuncs p).map (·.name)) (← rtTablesOf p its sizes)

/-! ## The non-constant functions' tables on two text ranges

**The ranges** (`splitRuns`): the maximal runs of consecutive non-constant functions of
`p.funcs` (the order of the text), each from the entry label of its first function up to the
entry label of the next function of `p.funcs` (a constant routine), or of `scc_rt_morestack`
after the last function (under `Program.growth`), or the end of `.text`. Today two:
`scc_rt_main`, and `scc_rt_thr_worker` (if any) with the user functions `wc_*`.

**Chosen for the kernel's cost**: it compares each label with one name (the next boundary), and
takes the call maps from the emitter's safepoints (`Scc.Emit.X64.emitItemsMaps`), not from the
`.quad` lines. Peak anonymous memory of a `decide +kernel` of `computeSplit` on the
non-constant functions (lowering and emission included, `LEAN_NUM_THREADS=1`, cap 2.5 GB): on
AArch64 1658 MB (`hello1.w`) and 2105 MB (`wake.w`, of which lowering and emission take
1531 MB), on x64 (sizes all 1) 994 and 1327 MB; the per-function slices cost more
(`computeSlicedByLabel`: 2074 MB on `hello1.w` and over the cap on `wake.w`, AArch64). The
tests check `computeSplit` against them and the full text's tables, and that the ranges hold
exactly the non-constant functions' entry labels.

**Soundness does not rest on the split**: scc recomputes the full tables and refuses on a
mismatch, so a wrong split shows up as a refusal, not as a wrong table. -/

/-- **The runs of consecutive non-constant functions of `p`**, each with the label that ends its
range (`none`: the end of `.text`). -/
def splitRuns (p : IR.Program) : List (List IR.Func × Option String) :=
  let tailL : Option String := if p.growth.isSome then some IR.StackMap.morestackSym else none
  let rec go : List IR.Func → List IR.Func → List (List IR.Func × Option String) →
      List (List IR.Func × Option String)
    | [], cur, acc => (if cur.isEmpty then acc else (cur.reverse, tailL) :: acc).reverse
    | f :: fs, cur, acc =>
      if constRoutine f.name then
        go fs [] (if cur.isEmpty then acc else (cur.reverse, some f.name) :: acc)
      else go fs (f :: cur) acc
  go p.funcs [] []

/-- **The range of the text from label `start` up to label `stop`** (or the end of `.text`):
its start address, its items and the sizes of its instructions. `none` if `start` is not in the
text. -/
def splitRange (start : String) (stop : Option String) (its : List Scc.Emit.X64.Item)
    (sizes : List Nat) : Option (Nat × List Scc.Emit.X64.Item × List Nat) :=
  let rec take : List Scc.Emit.X64.Item → List Nat → List Scc.Emit.X64.Item → List Nat →
      List Scc.Emit.X64.Item × List Nat
    | [], _, is, zs => (is.reverse, zs.reverse)
    | .dir s :: rest, ss, is, zs =>
      if endsText s then (is.reverse, zs.reverse) else take rest ss (.dir s :: is) zs
    | .d (.label l) :: rest, ss, is, zs =>
      if some l == stop then (is.reverse, zs.reverse) else take rest ss (.d (.label l) :: is) zs
    | .d d :: rest, z :: ss, is, zs => take rest ss (.d d :: is) (z :: zs)
    | it :: rest, ss, is, zs => take rest ss (it :: is) zs
  let rec skip : List Scc.Emit.X64.Item → List Nat → Nat →
      Option (Nat × List Scc.Emit.X64.Item × List Nat)
    | [], _, _ => none
    | .dir s :: rest, ss, a => if endsText s then none else skip rest ss a
    | .d (.label l) :: rest, ss, a =>
      if l == start then
        let (is, zs) := take rest ss [.d (.label l)] []
        some (a, is, zs)
      else skip rest ss a
    | .d _ :: rest, z :: ss, a => skip rest ss (a + z)
    | _ :: rest, ss, a => skip rest ss a
  skip its sizes 0

/-- **The tables of the non-constant functions of `p` on their ranges** (`splitRuns`,
`splitRange`; see above), the call maps from the emitter's safepoints `ms` whose labels are in
the range; merged in address order as `compute`. -/
def computeSplit (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) (sizes : List Nat) : Except String Tables := do
  let rs ← (splitRuns p).mapM fun (fs, stop) => do
    let some f := fs.head? | throw "computeSplit: empty run"
    let some (a, is, zs) := splitRange f.name stop its sizes
      | throw s!"computeSplit: no label {f.name}"
    let (items, _) ← itemsExitsFrom a is zs
    let tbl := ms.filterMap fun (l, st, hp) => (labelAddr items l).map (·, st, hp)
    pure (items, ← fs.mapM (tagsOf p items tbl))
  -- a tail jump into another range names its target, as in the whole text
  let ts ← rs.mapM fun (items, fts) => compute fts items
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) (ts.flatMap (·.maps)),
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (ts.flatMap (·.succs)) }

end Scc.Cert.MapsX64

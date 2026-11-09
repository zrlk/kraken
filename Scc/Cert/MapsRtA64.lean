import Scc.Cert.MapsRt
import Scc.Cert.MapsA64

/-!
# The runtime routines' tables on AArch64 (untrusted)

The AArch64 twin of `Scc.Cert.MapsRtX64`: the tables of the constant runtime routines
(`Scc.Cert.Maps.constRoutine`) of an AArch64 text, computed (`rtTablesOf`) and keyed by
routine-relative keys (`rtRelOf`): the source of the constants of `Scc.Cert.MapsRtConstA64`.
-/

namespace Scc.Cert.MapsA64
open Maps

/-- The constant runtime routines of `p`, with their indices in `p.funcs`. -/
def rtFuncs (p : IR.Program) : List (IR.Func × Nat) :=
  p.funcs.zipIdx.filter (constRoutine ·.1.name)

/-- **The tables of `p`'s constant runtime routines** on the text `its` (`compute` restricted
to them). -/
def rtTablesOf (p : IR.Program) (its : List Scc.Emit.A64.Item) : Except String Tables := do
  let areas ← Scc.Emit.A64.emitPre p
  let items ← itemsOf its
  let tbl ← stackTable its items
  let fns ← (rtFuncs p).mapM (tagsOf p areas items tbl)
  compute fns items

/-- **`rtTablesOf`, keyed by routine-relative keys.** -/
def rtRelOf (p : IR.Program) (its : List Scc.Emit.A64.Item) : Except String RTables := do
  let items ← itemsOf its
  relTables endL items ((rtFuncs p).map (·.1.name)) (← rtTablesOf p its)

/-! ## The non-constant functions' tables on two text ranges

The AArch64 twin of `Scc.Cert.MapsX64.computeSplit`. **The ranges** (`splitRuns`): the maximal
runs of consecutive non-constant functions of `p.funcs` (the order of the text), each from the
entry label of its first function (with the assembler lines just before it, its `.p2align 2`
and `.type f, %function`, which `itemsExitsFrom` needs for the end label `endL f`) up to the
entry label of the next function of `p.funcs` (a constant routine), or of `scc_rt_morestack`
after the last function (under `Program.growth`), or the end of `.text`. Today two:
`scc_rt_main`, and `scc_rt_thr_worker` (if any) with the user functions `wc_*`. The next
routine's `.p2align`/`.type` lines end the range as in the whole text (its `.type` line puts the
last function's `endL` where the whole text does).

**Chosen for the kernel's cost**: it compares each label with one name (the next boundary), and
takes the call maps from the emitter's safepoints (`Scc.Emit.A64.emitItemsMaps`), not from the
`.quad` lines. Peak anonymous memory of a `decide +kernel` of `computeSplit` on the
non-constant functions (lowering and emission included, `LEAN_NUM_THREADS=1`, cap 2.5 GB): 1658 MB
(`hello1.w`) and 2105 MB (`wake.w`, of which lowering and emission take 1531 MB); the
per-function slices cost more (`computeSlicedByLabel`: 2074 MB on `hello1.w`, over the cap on
`wake.w`). The tests check `computeSplit` against them and the full
text's tables, and that the ranges hold exactly the non-constant functions' entry labels.

**Soundness does not rest on the split**: scc recomputes the full tables and refuses on a
mismatch, so a wrong split shows up as a refusal, not as a wrong table. -/

/-- **The runs of consecutive non-constant functions of `p`** (with their indices in
`p.funcs`), each with the label that ends its range (`none`: the end of `.text`). -/
def splitRuns (p : IR.Program) : List (List (IR.Func × Nat) × Option String) :=
  let tailL : Option String := if p.growth.isSome then some IR.StackMap.morestackSym else none
  let rec go : List (IR.Func × Nat) → List (IR.Func × Nat) →
      List (List (IR.Func × Nat) × Option String) → List (List (IR.Func × Nat) × Option String)
    | [], cur, acc => (if cur.isEmpty then acc else (cur.reverse, tailL) :: acc).reverse
    | x :: xs, cur, acc =>
      if constRoutine x.1.name then
        go xs [] (if cur.isEmpty then acc else (cur.reverse, some x.1.name) :: acc)
      else go xs (x :: cur) acc
  go p.funcs.zipIdx [] []

/-- **The range of the text from label `start` (with the assembler lines just before it) up to
label `stop`** (or the end of `.text`): its start address and its items. `none` if `start` is
not in the text. -/
def splitRange (start : String) (stop : Option String) (its : List Scc.Emit.A64.Item) :
    Option (Nat × List Scc.Emit.A64.Item) :=
  let rec take : List Scc.Emit.A64.Item → List Scc.Emit.A64.Item → List Scc.Emit.A64.Item
    | [], is => is.reverse
    | .raw s :: rest, is => if endsText s then is.reverse else take rest (.raw s :: is)
    | .d (.label l) :: rest, is =>
      if some l == stop then is.reverse else take rest (.d (.label l) :: is)
    | it :: rest, is => take rest (it :: is)
  -- `a`: the address after the last instruction, before the pending assembler lines `pend`
  -- (reversed), whose `.p2align` `itemsExitsFrom` applies again.
  let rec skip : List Scc.Emit.A64.Item → Nat → List Scc.Emit.A64.Item →
      Option (Nat × List Scc.Emit.A64.Item)
    | [], _, _ => none
    | .raw s :: rest, a, pend => skip rest a (.raw s :: pend)
    | .d (.label l) :: rest, a, pend =>
      if l == start then some (a, take rest (.d (.label l) :: pend)) else skip rest a []
    | .d _ :: rest, a, _ => skip rest (a + 4) []
    | _ :: rest, a, _ => skip rest a []
  skip its 0 []

/-- **The tables of the non-constant functions of `p` on their ranges** (`splitRuns`,
`splitRange`; see above), the call maps from the emitter's safepoints `ms` whose labels are in
the range; merged in address order as `compute`. -/
def computeSplit (p : IR.Program) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) : Except String Tables := do
  let areas ← Scc.Emit.A64.emitPre p
  let rs ← (splitRuns p).mapM fun (fs, stop) => do
    let some x := fs.head? | throw "computeSplit: empty run"
    let some (a, is) := splitRange x.1.name stop its | throw s!"computeSplit: no label {x.1.name}"
    let (items, _) ← itemsExitsFrom a is
    let tbl := ms.filterMap fun (l, st, hp) => (labelAddr items l).map (·, st, hp)
    pure (items, ← fs.mapM (tagsOf p areas items tbl))
  -- a tail jump into another range names its target, as in the whole text
  let ts ← rs.mapM fun (items, fts) => compute fts items
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) (ts.flatMap (·.maps)),
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (ts.flatMap (·.succs)) }

end Scc.Cert.MapsA64

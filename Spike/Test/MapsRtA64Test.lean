import Scc.Cert.MapsRtConstA64
import Scc.Cert.MapsRtA64
import Scc.Emit.A64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# The constant runtime routines' tables and the per-function slices on AArch64 (untrusted test)

The AArch64 twin of `Spike/Test/MapsRtX64Test.lean`, on the AArch64 texts of `hello.w`,
`hello1.w`, `ret0.w`, `call1.w` and `wake.w`:

* **The constants** (`Scc.Cert.MapsRtA64.rtConstA64`, generated) resolve to the tables `compute`
  gives the constant runtime routines (`Scc.Cert.MapsA64.rtTablesOf`), every key to a distinct
  address; the routines are the program's constant routines.
* **No tail call crosses between the constant routines and the rest** (IR `Term.tail`, and the
  text's `b`/`b.cond`/`cbz`/`cbnz` to another function's symbol).
* **The per-function slices** (`Scc.Cert.MapsA64.computeSliced`) give the full text's tables,
  for every function and for the non-constant ones; no successor edge of the full tables leaves
  its function but a tail jump's to the target's entry (`Scc.Cert.Maps.entryTail`).
* **The slices cut at entry labels** (`Scc.Cert.MapsA64.computeSlicedByLabel`, with the
  emitter's safepoints): the safepoints are the parsed `scc_stackmap` entries, and the tables are
  `computeSliced`'s and the full text's (`byLabelOk`).
* **The call maps are local to the caller** (`raOk`): a call map's machine registers are the
  call's result registers tagged by the caller's destinations (`FnTags.callRes`), none else.
* **The two text ranges** (`Scc.Cert.MapsA64.computeSplit`) give the tables of the slices cut at
  entry labels and the full text's, on the non-constant functions; the ranges' entry labels are
  exactly the non-constant functions' (`splitOk`).

**Memory** (peak anonymous resident memory of `lake env lean` on a `decide +kernel` of the
tables of the non-constant functions, `LEAN_NUM_THREADS=1`, cap 2.5 GB), measured before the
slices: on the whole text, `itemsOf` alone takes 2090 MB (`ret0.w`) and the user functions with
`scc_rt_main` and `scc_rt_thr_worker` exceed the cap (`hello1.w`); on two text ranges
(`scc_rt_main`; the user functions and `scc_rt_thr_worker`), 1626 MB (`hello1.w`) and 2048 MB
(`wake.w`): a margin of about 0.5 GB that shrinks as user code grows. The per-function slices
(`computeSliced` of the non-constant functions) exceed the cap on `ret0.w`, `hello1.w` and
`wake.w` (2687 to 2761 MB when stopped): on `ret0.w`, lowering and emission take 1266 MB,
`slices` 1856 MB and `stackEntries` 1942 MB, before any `compute`. So `computeSliced` is checked
here in the evaluator only; it is not yet a kernel-run form. The slices cut at entry labels
with the emitter's safepoints (`computeSlicedByLabel` of the non-constant functions): 1868 MB
(`ret0.w`), 2074 MB (`hello1.w`), and over the cap on `wake.w` (stopped at 2571 MB; lowering and
emission alone take 1531 MB); on x64 (sizes all 1) 998, 1157 and 1499 MB. So it too is checked
here in the evaluator only (`byLabelOk`, against the parsed table, `computeSliced` and the full
text's tables). The two text ranges (`computeSplit`, the form chosen for the certificates):
1658 MB (`hello1.w`) and 2105 MB (`wake.w`); on x64 994 and 1327 MB.
-/

namespace Scc.Cert.MapsRtA64Test
open Scc.Cert.Maps Scc.Cert.MapsA64 Scc.Cert.MapsRtA64

/-- The AArch64 IR and items of a WeakCore source. -/
def compileW (src : String) : Except String (IR.Program × List Scc.Emit.A64.Item) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .arm } c
  pure (ir, ← Scc.Emit.A64.emitItems ir)

/-- **The constants on a text** (see the module docstring). -/
def constOk (p : IR.Program) (its : List Scc.Emit.A64.Item) : Bool :=
  match itemsOf its, rtTablesOf p its with
  | .ok items, .ok t =>
    let addrs := rtConstA64.keys.map (·.resolve endL items)
    rtConstA64.resolve endL items == some t &&
    addrs.all Option.isSome && (addrs.filterMap id).eraseDups.length == addrs.length &&
    rtConstA64.routines == (rtFuncs p).map (·.1.name) &&
    !t.maps.isEmpty && !t.succs.isEmpty
  | _, _ => false

/-- The IR tail calls of `p` (caller, callee). -/
def irTails (p : IR.Program) : List (String × String) :=
  p.funcs.flatMap fun f => f.blocks.filterMap fun b => match b.term with
    | .tail g _ => some (f.name, g)
    | _ => none

/-- The text's jumps to another function's symbol (from function, to function), per slice. -/
def textTails (its : List Scc.Emit.A64.Item) : List (String × String) :=
  let sl := slices its
  let names := sl.map (·.name)
  sl.flatMap fun s => (s.its.filterMap fun
    | .d (.instr ⟨_, .B (.label l)⟩) => some l
    | .d (.instr ⟨_, .B_cond _ (.label l)⟩) => some l
    | .d (.instr ⟨_, .CBZ _ (.label l)⟩) => some l
    | .d (.instr ⟨_, .CBNZ _ (.label l)⟩) => some l
    | _ => none).filter (fun l => names.contains l && l != s.name) |>.map (s.name, ·)

/-- No tail call crosses between the constant routines and the rest (IR and text), other than
from a routine that is no IR function (`scc_rt_morestack`). -/
def tailsOk (p : IR.Program) (its : List Scc.Emit.A64.Item) : Bool :=
  (irTails p ++ textTails its).all fun (f, g) =>
    constRoutine f == constRoutine g || !p.funcs.any (·.name == f)

/-- **The slices give the full text's tables** (see the module docstring). -/
def slicedOk (p : IR.Program) (its : List Scc.Emit.A64.Item) : Bool :=
  let user (f : IR.Func) : Bool := !constRoutine f.name
  let r : Except String Bool := do
    let areas ← Scc.Emit.A64.emitPre p
    let items ← itemsOf its
    let tbl ← stackTable its items
    let full ← compute (← p.funcs.zipIdx.mapM (tagsOf p areas items tbl)) items
    let ufull ← compute (← (p.funcs.zipIdx.filter (user ·.1)).mapM (tagsOf p areas items tbl)) items
    let rs := p.funcs.filterMap fun f =>
      (labelAddr items f.name).bind fun s => (labelAddr items (endL f.name)).map (s, ·)
    let fnOf (a : Nat) : Option (Nat × Nat) := rs.find? fun (s, e) => s ≤ a && a < e
    pure ((computeSliced p its (fun _ => true)).toOption == some full &&
      (computeSliced p its user).toOption == some ufull &&
      full.succs.all (fun s => s.next.all fun n => fnOf n == fnOf s.addr || rs.any (·.1 == n)) &&
      (items.any fun | .ins _ _ i => (match i.flow with
        | .call g => p.funcs.any (·.name == g) | _ => false) | _ => false))
  r.toOption == some true

/-- **The slices cut at entry labels give the same tables** (`computeSlicedByLabel`, with the
emitter's safepoints `ms`): the safepoints are the parsed `scc_stackmap` entries, and the tables
are `computeSliced`'s and the full text's, for every function and for the non-constant ones. -/
def byLabelOk (p : IR.Program) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) : Bool :=
  let user (f : IR.Func) : Bool := !constRoutine f.name
  let r : Except String Bool := do
    let areas ← Scc.Emit.A64.emitPre p
    let items ← itemsOf its
    let tbl ← stackTable its items
    let full ← compute (← p.funcs.zipIdx.mapM (tagsOf p areas items tbl)) items
    let ufull ← compute (← (p.funcs.zipIdx.filter (user ·.1)).mapM (tagsOf p areas items tbl)) items
    pure ((stackEntries its).toOption == some ms &&
      (computeSlicedByLabel p its ms (fun _ => true)).toOption == some full &&
      (computeSliced p its (fun _ => true)).toOption == some full &&
      (computeSlicedByLabel p its ms user).toOption == some ufull &&
      (computeSliced p its user).toOption == some ufull)
  r.toOption == some true

/-- The entry labels of `entryLabels p` in the items `is`. -/
def entriesIn (p : IR.Program) (is : List Scc.Emit.A64.Item) : List String :=
  is.filterMap fun
    | .d (.label l) => if (entryLabels p).contains l then some l else none
    | _ => none

/-- **The two text ranges give the same tables** (`computeSplit`): those of the slices cut at
entry labels and the full text's, on the non-constant functions; and the ranges' entry labels
are exactly the non-constant functions', in order (no constant routine inside a range). -/
def splitOk (p : IR.Program) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) : Bool :=
  let user (f : IR.Func) : Bool := !constRoutine f.name
  let r : Except String Bool := do
    let areas ← Scc.Emit.A64.emitPre p
    let items ← itemsOf its
    let tbl ← stackTable its items
    let ufull ← compute (← (p.funcs.zipIdx.filter (user ·.1)).mapM (tagsOf p areas items tbl)) items
    let ents := (splitRuns p).flatMap fun (fs, stop) => match fs.head? with
      | some x => ((splitRange x.1.name stop its).map fun (_, is) => entriesIn p is).getD []
      | none => []
    pure ((computeSplit p its ms).toOption == some ufull &&
      (computeSlicedByLabel p its ms user).toOption == some ufull &&
      ents == (p.funcs.filter user).map (·.name) &&
      !ents.any constRoutine)
  r.toOption == some true

/-- **No call map lists a register the caller does not receive from that call**: every machine
register of a call map (keyed at the return address) is a result register of that call, tagged
by the caller's destination (`FnTags.callRes`, by `siteRes`); the grow stubs' call maps list
none. In particular no argument register of the callee and no register the caller kept across
the call (there is none: every live IR register is spilled). Not vacuous: some call map lists a
register. -/
def raOk (p : IR.Program) (its : List Scc.Emit.A64.Item) : Bool :=
  let r : Except String Bool := do
    let areas ← Scc.Emit.A64.emitPre p
    let items ← itemsOf its
    let tbl ← stackTable its items
    let fns ← p.funcs.zipIdx.mapM (tagsOf p areas items tbl)
    let full ← compute fns items
    let rs := (← fns.mapM fun t => siteRes t (insOf (bodyOf t items))).flatten
    let isReg : Loc → Bool := fun | .reg _ => true | _ => false
    let calls := full.maps.filter (·.pt.kind == .call)
    pure (calls.all (fun m => m.roots.all fun (l, _) =>
        !isReg l || ((rs.lookup m.pt.addr).getD []).any (·.1 == l)) &&
      calls.any (fun m => m.roots.any (isReg ·.1)))
  r.toOption == some true

/-- All six checks on a source. -/
def okW (src : String) : Bool :=
  match compileW src with
  | .ok (p, its) => constOk p its && tailsOk p its && slicedOk p its && raOk p its &&
    match Scc.Emit.A64.emitItemsMaps p with
    | .ok (_, ms) => byLabelOk p its ms && splitOk p its ms
    | .error _ => false
  | .error _ => false

-- The ranges on `wake.w`: `scc_rt_main`, then `scc_rt_thr_worker` with the user functions.
#guard (match compileW (w_src% "Scc/Test/wake.w") with
  | .ok (p, _) => (splitRuns p).map (fun (fs, stop) => (fs.map (·.1.name), stop)) ==
      [(["scc_rt_main"], some "scc_rt_alloc"),
       (["scc_rt_thr_worker", "wc_worker", "wc_waitLoop", "wc_main"], some "scc_rt_morestack")]
  | .error _ => false)

#guard okW (w_src% "Scc/Test/hello.w")
#guard okW (w_src% "Scc/Test/hello1.w")
#guard okW (w_src% "Scc/Test/ret0.w")
#guard okW (w_src% "Scc/Test/call1.w")
#guard okW (w_src% "Scc/Test/wake.w")

-- `scc_rt_abort` tail-jumps to the `scc_rt_abort_*` routines, all constant; the only other
-- jump between functions is the user's tail call (`_start`'s branch is before every slice).
#guard (match compileW (w_src% "Scc/Test/wake.w") with
  | .ok (_, its) =>
    let ts := textTails its
    ((ts.filter (·.1 == "scc_rt_abort")).map (·.2)) ==
      ["scc_rt_abort_overflow", "scc_rt_abort_heap", "scc_rt_abort_stack", "scc_rt_abort_write",
       "scc_rt_abort_threads"] &&
    (ts.filter fun (f, _) => !constRoutine f) == [("wc_main", "wc_waitLoop")]
  | .error _ => false)

-- The constants are for the default configuration only.
#guard (consts? { arch := .arm }).isSome && (consts? { arch := .arm, host := .raw }).isNone

end Scc.Cert.MapsRtA64Test

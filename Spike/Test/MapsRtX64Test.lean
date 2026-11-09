import Spike.Test.Cert.X64Hello1Cert
import Scc.Cert.MapsRtConstX64
import Scc.Cert.MapsRtX64
import Scc.Emit.X64
import Scc.Frontend
import Scc.Lower.Program
import Scc.Test.Src

/-!
# The constant runtime routines' tables and the per-function slices on x64 (untrusted test)

On the x86-64 texts of `hello.w`, `hello1.w`, `ret0.w`, `call1.w` and `wake.w` (frontend,
`Scc.Lower.lowerProgram`, `Scc.Emit.X64.emitItems`; instruction sizes all 1, and the real sizes
of the `hello1.w` certificate):

* **The constants** (`Scc.Cert.MapsRtX64.rtConstX64`, generated) resolve to the tables `compute`
  gives the constant runtime routines (`Scc.Cert.MapsX64.rtTablesOf`), maps and successors; every
  key resolves, to a distinct address; the routines are the program's constant routines.
* **No tail call crosses between the constant routines and the rest**: in the IR (`Term.tail`)
  and in the text (a `jmp`/`jcc` to another function's symbol), a constant routine jumps only to
  constant routines (`scc_rt_abort` to the `scc_rt_abort_*` routines), and no other function to
  a constant routine.
* **The per-function slices** (`Scc.Cert.MapsX64.computeSliced`) give the full text's tables
  (`compute` on all of `itemsOf`), for every function and for the non-constant ones; the full
  tables have no successor edge from one function into another but a tail jump's to the target's
  entry (`Scc.Cert.Maps.entryTail`), and the call maps of calls to
  other functions (cross-slice call targets) are among those compared.
* **The slices cut at entry labels** (`Scc.Cert.MapsX64.computeSlicedByLabel`, with the
  emitter's safepoints from `Scc.Emit.X64.emitItemsMaps`): the safepoints are the parsed
  `scc_stackmap` entries (`stackEntries`), and the tables are `computeSliced`'s and the full
  text's, for every function and for the non-constant ones (`byLabelOk`).
* **The call maps are local to the caller** (`raOk`): a call map's machine registers are the
  call's result registers tagged by the caller's destinations (`FnTags.callRes`), none else.
* **The two text ranges** (`Scc.Cert.MapsX64.computeSplit`) give the tables of the slices cut at
  entry labels and the full text's, on the non-constant functions; the ranges' entry labels are
  exactly the non-constant functions' (`splitOk`).

Memory (the kernel's peak on the tables of the non-constant functions, on two text ranges and
on per-function slices): recorded in `Spike/Test/MapsRtA64Test.lean`.
-/

namespace Scc.Cert.MapsRtX64Test
open Scc.Cert.Maps Scc.Cert.MapsX64 Scc.Cert.MapsRtX64

/-- The x64 IR and items of a WeakCore source. -/
def compileW (src : String) : Except String (IR.Program × List Scc.Emit.X64.Item) := do
  let c ← match Frontend.run src with
    | .ok c => pure c
    | .error ds => throw (String.intercalate "\n" (ds.map (·.render "input")))
  let ir ← Lower.lowerProgram { arch := .x64 } c
  pure (ir, ← Scc.Emit.X64.emitItems ir)

/-- The number of instructions of the text (up to the first section switch). -/
def insCount : List Scc.Emit.X64.Item → Nat
  | [] => 0
  | .dir s :: rest => if endsText s then 0 else insCount rest
  | .d (.label _) :: rest => insCount rest
  | .d _ :: rest => insCount rest + 1
  | _ :: rest => insCount rest

/-- **The constants on a text**: they resolve to the computed tables of the constant routines,
every key to a distinct address, and the routines are the program's constant routines. -/
def constOk (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) : Bool :=
  match itemsOf its sizes, rtTablesOf p its sizes with
  | .ok items, .ok t =>
    let addrs := rtConstX64.keys.map (·.resolve endL items)
    rtConstX64.resolve endL items == some t &&
    addrs.all Option.isSome && (addrs.filterMap id).eraseDups.length == addrs.length &&
    rtConstX64.routines == (rtFuncs p).map (·.name) &&
    -- the constants are not empty
    !t.maps.isEmpty && !t.succs.isEmpty
  | _, _ => false

/-- The IR tail calls of `p` (caller, callee). -/
def irTails (p : IR.Program) : List (String × String) :=
  p.funcs.flatMap fun f => f.blocks.filterMap fun b => match b.term with
    | .tail g _ => some (f.name, g)
    | _ => none

/-- The text's jumps to another function's symbol (from function, to function), per slice. -/
def textTails (its : List Scc.Emit.X64.Item) (sizes : List Nat) : List (String × String) :=
  let sl := slices its sizes
  let names := sl.map (·.name)
  sl.flatMap fun s => (s.its.filterMap fun
    | .d (.instr (.regular _ _ (.jmp t))) => relLabel t
    | .d (.instr (.regular _ _ (.jcc _ l))) => some l
    | _ => none).filter (fun l => names.contains l && l != s.name) |>.map (s.name, ·)

/-- No tail call crosses between the constant routines and the rest (IR and text). -/
def tailsOk (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) : Bool :=
  (irTails p ++ textTails its sizes).all fun (f, g) =>
    constRoutine f == constRoutine g || !p.funcs.any (·.name == f)

/-- **The slices give the full text's tables**: for every function, and for the non-constant
ones; no successor edge of the full tables leaves its function's range but to a function's
entry (a tail jump's); some call map is of a
call to another function. -/
def slicedOk (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) : Bool :=
  let user (f : IR.Func) : Bool := !constRoutine f.name
  let r : Except String Bool := do
    let items ← itemsOf its sizes
    let tbl ← stackTable its items
    let full ← compute (← p.funcs.mapM (tagsOf p items tbl)) items
    let ufull ← compute (← (p.funcs.filter user).mapM (tagsOf p items tbl)) items
    let rs := p.funcs.filterMap fun f =>
      (labelAddr items f.name).bind fun s => (labelAddr items (endL f.name)).map (s, ·)
    let fnOf (a : Nat) : Option (Nat × Nat) := rs.find? fun (s, e) => s ≤ a && a < e
    pure ((computeSliced p its sizes (fun _ => true)).toOption == some full &&
      (computeSliced p its sizes user).toOption == some ufull &&
      full.succs.all (fun s => s.next.all fun n => fnOf n == fnOf s.addr || rs.any (·.1 == n)) &&
      (items.any fun | .ins _ _ i => (match i.flow with
        | .call g => p.funcs.any (·.name == g) | _ => false) | _ => false))
  r.toOption == some true

/-- **The slices cut at entry labels give the same tables** (`computeSlicedByLabel`, with the
emitter's safepoints `ms`): the safepoints are the parsed `scc_stackmap` entries, and the tables
are `computeSliced`'s and the full text's, for every function and for the non-constant ones. -/
def byLabelOk (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) (sizes : List Nat) : Bool :=
  let user (f : IR.Func) : Bool := !constRoutine f.name
  let r : Except String Bool := do
    let items ← itemsOf its sizes
    let tbl ← stackTable its items
    let full ← compute (← p.funcs.mapM (tagsOf p items tbl)) items
    let ufull ← compute (← (p.funcs.filter user).mapM (tagsOf p items tbl)) items
    pure ((stackEntries its).toOption == some ms &&
      (computeSlicedByLabel p its ms sizes (fun _ => true)).toOption == some full &&
      (computeSliced p its sizes (fun _ => true)).toOption == some full &&
      (computeSlicedByLabel p its ms sizes user).toOption == some ufull &&
      (computeSliced p its sizes user).toOption == some ufull)
  r.toOption == some true

/-- The entry labels of `entryLabels p` in the items `is`. -/
def entriesIn (p : IR.Program) (is : List Scc.Emit.X64.Item) : List String :=
  is.filterMap fun
    | .d (.label l) => if (entryLabels p).contains l then some l else none
    | _ => none

/-- **The two text ranges give the same tables** (`computeSplit`): those of the slices cut at
entry labels and the full text's, on the non-constant functions; and the ranges' entry labels
are exactly the non-constant functions', in order (no constant routine inside a range). -/
def splitOk (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) (sizes : List Nat) : Bool :=
  let user (f : IR.Func) : Bool := !constRoutine f.name
  let r : Except String Bool := do
    let items ← itemsOf its sizes
    let tbl ← stackTable its items
    let ufull ← compute (← (p.funcs.filter user).mapM (tagsOf p items tbl)) items
    let ents := (splitRuns p).flatMap fun (fs, stop) => match fs.head? with
      | some f => ((splitRange f.name stop its sizes).map fun (_, is, _) => entriesIn p is).getD []
      | none => []
    pure ((computeSplit p its ms sizes).toOption == some ufull &&
      (computeSlicedByLabel p its ms sizes user).toOption == some ufull &&
      ents == (p.funcs.filter user).map (·.name) &&
      !ents.any constRoutine)
  r.toOption == some true

/-- **No call map lists a register the caller does not receive from that call**: every machine
register of a call map (keyed at the return address) is a result register of that call, tagged
by the caller's destination (`FnTags.callRes`, by `siteRes`); the grow stubs' call maps list
none. In particular no argument register of the callee and no register the caller kept across
the call (there is none: every live IR register is spilled). Not vacuous: some call map lists a
register. -/
def raOk (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) : Bool :=
  let r : Except String Bool := do
    let items ← itemsOf its sizes
    let tbl ← stackTable its items
    let fns ← p.funcs.mapM (tagsOf p items tbl)
    let full ← compute fns items
    let rs := (← fns.mapM fun t => siteRes t (insOf (bodyOf t items))).flatten
    let isReg : Loc → Bool := fun | .reg _ => true | _ => false
    let calls := full.maps.filter (·.pt.kind == .call)
    pure (calls.all (fun m => m.roots.all fun (l, _) =>
        !isReg l || ((rs.lookup m.pt.addr).getD []).any (·.1 == l)) &&
      calls.any (fun m => m.roots.any (isReg ·.1)))
  r.toOption == some true

/-- All six checks on a source, sizes all 1. -/
def okW (src : String) : Bool :=
  match compileW src with
  | .ok (p, its) =>
    let sizes := List.replicate (insCount its) 1
    constOk p its sizes && tailsOk p its sizes && slicedOk p its sizes && raOk p its sizes &&
    match Scc.Emit.X64.emitItemsMaps p with
    | .ok (_, ms) => byLabelOk p its ms sizes && splitOk p its ms sizes
    | .error _ => false
  | .error _ => false

-- The ranges on `wake.w`: `scc_rt_main`, then `scc_rt_thr_worker` with the user functions.
#guard (match compileW (w_src% "Scc/Test/wake.w") with
  | .ok (p, _) => (splitRuns p).map (fun (fs, stop) => (fs.map (·.name), stop)) ==
      [(["scc_rt_main"], some "scc_rt_alloc"),
       (["scc_rt_thr_worker", "wc_worker", "wc_waitLoop", "wc_main"], some "scc_rt_morestack")]
  | .error _ => false)

#guard okW (w_src% "Scc/Test/hello.w")
#guard okW (w_src% "Scc/Test/hello1.w")
#guard okW (w_src% "Scc/Test/ret0.w")
#guard okW (w_src% "Scc/Test/call1.w")
#guard okW (w_src% "Scc/Test/wake.w")

-- With the real instruction sizes of the `hello1.w` certificate.
#guard constOk SccCertificate.loweredLit.1 SccCertificate.emittedLit.1 SccCertificate.sizes
#guard slicedOk SccCertificate.loweredLit.1 SccCertificate.emittedLit.1 SccCertificate.sizes
#guard byLabelOk SccCertificate.loweredLit.1 SccCertificate.emittedLit.1 SccCertificate.emittedLit.2
  SccCertificate.sizes
#guard splitOk SccCertificate.loweredLit.1 SccCertificate.emittedLit.1 SccCertificate.emittedLit.2
  SccCertificate.sizes

-- `scc_rt_abort` tail-jumps to the `scc_rt_abort_*` routines, all constant.
#guard (match compileW (w_src% "Scc/Test/wake.w") with
  | .ok (_, its) =>
    let ts := textTails its (List.replicate (insCount its) 1)
    ((ts.filter (·.1 == "scc_rt_abort")).map (·.2)) ==
      ["scc_rt_abort_overflow", "scc_rt_abort_heap", "scc_rt_abort_stack", "scc_rt_abort_write",
       "scc_rt_abort_threads"] &&
    ts.all fun (f, g) => constRoutine f == constRoutine g
  | .error _ => false)

-- The constants are for the default configuration only.
#guard (consts? {}).isSome && (consts? { layout := { maxThreads := 7 } }).isNone

end Scc.Cert.MapsRtX64Test

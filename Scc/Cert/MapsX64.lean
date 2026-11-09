import Scc.Emit.X64Func
import Scc.Cert.MapsCompute

/-!
# Certificate tables from x64 text (front end of `Scc.Cert.MapsCompute`)

x86-64: the inputs of `Scc.Cert.Maps.compute` from an emitted program
(`Scc.Emit.X64.Item`s, with the instruction sizes of the certificates' `sizes`) and its IR.

* **Items** (`itemsOf`): the `.text` part of the emitted items (up to the first `.data`, `.bss`
  or `.section` line), a label at the offset of the next instruction, each instruction at its
  offset with its size, classified (`classify`): a 64-bit `mov` to `d(%rbp)` writes slot `d`, a
  `mov` from `d(%rbp)` (or a narrower one to it) reads it, `lea d(%rbp)` takes its address;
  `call`, `jmp` to a label, `jcc`, `ret` and `ud2` give the control flow. A call after
  `xorl %ebp, %ebp` in the same label-free run (`switchTo`, the child stubs) never returns and
  is not a safe point: it is classified as leaving the function, and listed by `exemptions`. Any other instruction that mentions `(%rbp` fails the
  classification (the emitter writes none). Each `.size f, .-f` line adds the synthetic label
  `endL f` (not in the text) at the end of `f`.
* **Tags** (`tagsOf`), from the IR function (see the module docstring of `MapsCompute`: **tags
  trusted from the IR, tied to the text only via the certificates' `reproduces` guard; option B
  must discharge this**): the parameter and result registers by the calling convention
  (`Scc.Emit.X64.argRegs`, `retRegs`; registers numbered in encoding order, `regNum`), tagged by
  `Func.heapRegs` / `Func.stackRegs`; the result registers of each call (`FnTags.callRes`) by the
  caller's own destination registers of that call (nothing from the callee); the slots `-8(k+1)(%rbp)` of `Scc.Emit.X64.frameOf`. The prologue's block entries are the
  function's symbol and, with a stack check under `Program.growth`, `.L{f}.chk`; the body runs
  from the first block's label to the first stub (`.L{f}.ovf`, the child stubs, `.L{f}.stk`) or
  the end of the function. The grow stub (`.L{f}.stk` under `Program.growth`) is
  `FnTags.growStub`: its call of `scc_rt_morestack` gets the map of its `scc_stackmap` entry
  (the words `-8(i+1)(%rbp)` where the stub pushed the tagged parameter registers live on
  entry; stack parameters in place, `Scc.Emit.X64.inArgOff`).
* **Call maps** (`stackTable`): the `scc_stackmap` table of the text (its `.quad` lines), each
  entry's label resolved to its address in the text.

Exemptions (`exemptions`, computed from the text): the routines of the text that are no IR
function (`_start`, `scc_rt_morestack`), the `scc_stackmap` entries outside every body other
than the grow stubs' (none today), and the calls after a zeroed frame pointer. The tests pin the
three lists per fixture.

Untrusted, like `MapsCompute`.
-/

namespace Scc.Cert.MapsX64
open Scc.Cert.Maps
open Scc.Emit.X64 (labelOf childL cloneEntries frameOf argRegs retRegs)

/-- The ISA number of a register (encoding order, `Scc.Cert.Maps.Loc.reg`). -/
def regNum : Reg64 → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14 | .r15 => 15

/-- The synthetic label at the end of function `f` (from its `.size` line; not in the text). -/
def endL (f : String) : String := s!".Lscc_end.{f}"

/-! ## Items -/

/-- The frame slot `d(%rbp)` an address designates. -/
def rbpOff (a : AddrExpr) : Option Int :=
  match a.base, a.idx, a.disp with
  | some (.reg .rbp), none, .int64 d => some d.toInt
  | _, _, _ => none

/-- A direct jump or call target. -/
def relLabel : RelRegOrMem → Option String
  | .rel (.sub (.label l) .after_current_instruction) => some l
  | _ => none

/-- `xorl %ebp, %ebp` (or any width): the frame-record chain ends here. -/
def zeroesFp {w : _root_.Width} : Operation w → Bool
  | .xor (.reg (.low .rbp _)) (.regOrMem (.reg (.low .rbp _))) => true
  | _ => false

/-- **The classification of one operation** (see the module docstring); `fpZero`: the frame
pointer was zeroed since the last call. `none` for an unclassified frame access. -/
def classifyOp (fpZero : Bool) {w : _root_.Width} (op : Operation w) : Option Ins :=
  let other : Option Ins :=
    match Scc.Emit.X64.ppOp op with
    | some s => if containsK s "(%rbp" then none else some {}
    | none => none
  match op with
  | .mov (.mem a) _ => match rbpOff a with
    | some o => some (if w == .W64 then { writes := [o] } else { reads := [o] })
    | none => other
  | .mov (.reg _) (.regOrMem (.mem a)) => match rbpOff a with
    | some o => some { reads := [o] }
    | none => other
  | .lea _ a => match rbpOff a with
    | some o => some { takes := [o] }
    | none => other
  | .call t => match relLabel t with
    | some g => some { flow := if fpZero then .stop else .call g }
    | none => none
  | .jmp t => match relLabel t with
    | some l => some { flow := .jmp l }
    | none => none
  | .jcc _ l => some { flow := .jcc l }
  | .ret => some { flow := .ret }
  | .ud2 => some { flow := .stop }
  | _ => other

/-- The classification of a directive (an instruction; see `classifyOp`). -/
def classify (fpZero : Bool) : Directive → Option Ins
  | .instr (.regular _ _ op) => classifyOp fpZero op
  | _ => none

/-- Whether a directive zeroes the frame pointer (`zeroesFp`). -/
def dirZeroesFp : Directive → Bool
  | .instr (.regular _ _ op) => zeroesFp op
  | _ => false

/-- The section switches that end `.text`. -/
def endsText (s : String) : Bool :=
  s == ".data" || s == ".bss" || startsK s ".section"

/-- The function a `.size f, .-f` line closes: the text before the first `,` is `.size f` with no
space in `f`. On the UTF-8 bytes (`,` and space are single bytes, so the cut is at character
boundaries and `f` decodes): reading every directive line as characters is costly in the kernel. -/
def sizeOf? (s : String) : Option String :=
  let h := s.toUTF8.data.toList.takeWhile (· != 44)
  let p := ".size ".toUTF8.data.toList
  if p.isPrefixOf h && !(h.drop p.length).contains 32 then
    String.fromUTF8? (ByteArray.mk (h.drop p.length).toArray)
  else none

/-- `--host raw`: whether the text after label `l` is in the kernel routine trampolines
(`[Tcb.kabiStartSym, Tcb.kabiEndSym)`), `kb` whether the text before it is. -/
def kabiAfter (kb : Bool) (l : String) : Bool :=
  if l == IR.Tcb.kabiStartSym then true else if l == IR.Tcb.kabiEndSym then false else kb

/-- The classification of a directive in the text (`classify`); in the kernel routine
trampolines (`kb`, `kabiAfter`), a jump through memory (`jmp *8n(%r11)`,
`Scc.Emit.X64.emitKabi`) leaves the unit (`.stop`). Anywhere else, in a function body in
particular, it stays unclassified, so the tables refuse it. -/
def classifyIn (kb fpZero : Bool) (d : Directive) : Option Ins :=
  match kb, d with
  | true, .instr (.regular _ _ (.jmp (.mem _))) => some { flow := .stop }
  | _, _ => classify fpZero d

/-- **The items of the text** (see the module docstring), with the sizes of its instructions in
order, and the calls classified as leaving the function because the frame pointer was zeroed
before them (`(address, callee)`; listed by `exemptions`). The zeroing must be in the same
label-free run as the call: a label resets it. An error if the sizes do not match the
instructions, or an instruction is unclassified. The text starts at address `a0`
(`itemsExits`: 0; a slice of the text, `Scc.Cert.MapsX64.slices`, at its own). -/
def itemsExitsFrom (a0 : Nat) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String (List Maps.Item × List (Nat × String)) :=
  let rec go : List Scc.Emit.X64.Item → List Nat → Nat → Bool → Bool → List Maps.Item →
      List (Nat × String) → Except String (List Maps.Item × List (Nat × String))
    | [], [], _, _, _, acc, ex => .ok (acc.reverse, ex.reverse)
    | [], _ :: _, _, _, _, _, _ => .error "itemsOf: more sizes than instructions"
    | .dir s :: rest, zs, a, fz, kb, acc, ex =>
      if endsText s then
        if zs.isEmpty then .ok (acc.reverse, ex.reverse)
        else .error "itemsOf: more sizes than instructions"
      else match sizeOf? s with
        | some f => go rest zs a false kb (.label a (endL f) :: acc) ex
        | none => go rest zs a fz kb acc ex
    | .d (.label l) :: rest, zs, a, _, kb, acc, ex =>
      go rest zs a false (kabiAfter kb l) (.label a l :: acc) ex
    | .d d :: rest, zs, a, fz, kb, acc, ex => match zs with
      | [] => .error "itemsOf: fewer sizes than instructions"
      | z :: zt => match classifyIn kb fz d with
        | some i =>
          let fz' := match i.flow with | .call _ | .stop => false | _ => fz || dirZeroesFp d
          let ex' := match d with
            | .instr (.regular _ _ (.call t)) =>
              if fz then (a, (relLabel t).getD "?") :: ex else ex
            | _ => ex
          go rest zt (a + z) fz' kb (.ins a z i :: acc) ex'
        | none => .error s!"itemsOf: unclassified instruction at {a}: {(Scc.Emit.X64.ppDirective d).getD "?"}"
    | .raw s :: _, _, a, _, _, _, _ => .error s!"itemsOf: raw line at {a}: {s}"
    | _ :: rest, zs, a, fz, kb, acc, ex => go rest zs a fz kb acc ex
  go its sizes a0 false false [] []

/-- **The items of the text** from address 0 (`itemsExitsFrom`). -/
def itemsExits (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String (List Maps.Item × List (Nat × String)) :=
  itemsExitsFrom 0 its sizes

/-- The items of the text (`itemsExits`). -/
def itemsOf (its : List Scc.Emit.X64.Item) (sizes : List Nat) : Except String (List Maps.Item) :=
  (·.1) <$> itemsExits its sizes

/-! ## The `scc_stackmap` table -/

/-- The operands of a `.quad` line. -/
def quadArgs (s : String) : Option (List String) :=
  match splitK s ".quad " with
  | ["", rest] => some (splitK rest ", ")
  | _ => none

/-- **The entries of the `scc_stackmap` table** of the text, keyed by their labels: label, then
for each a check of the label (`chk`, run before the entry's counts are read), stack slots, heap
slots. -/
def stackEntriesWith {α : Type} (its : List Scc.Emit.X64.Item) (chk : String → Except String α) :
    Except String (List (α × List Int × List Int)) := do
  let rest := its.dropWhile fun | .d (.label l) => l != IR.StackMap.tableSym | _ => true
  if rest.isEmpty then throw s!"no {IR.StackMap.tableSym}"
  let qs := ((rest.drop 1).takeWhile fun | .dir s => (quadArgs s).isSome | _ => false).filterMap
    fun | .dir s => quadArgs s | _ => none
  let n ← match qs.head? with
    | some [m] => match toNatK? m with | some n => pure n | none => throw s!"bad count {m}"
    | _ => throw s!"{IR.StackMap.tableSym}: no count"
  let offs ← (qs.drop (1 + n)).mapM fun
    | [o] => match toIntK? o with | some v => pure v | none => throw s!"bad offset {o}"
    | q => throw s!"bad offset line {q}"
  ((qs.drop 1).take n).mapM fun
    | [w, ns, nh, fs] => do
      -- the return address word `L - scc_text_start` (relative to the text's start)
      let l ← match splitK w s!" - {IR.StackMap.textStartSym}" with
        | [l, ""] => pure l
        | _ => throw s!"{IR.StackMap.tableSym}: entry {w} is not relative to {IR.StackMap.textStartSym}"
      let a ← chk l
      let some ns := toNatK? ns | throw s!"bad count {ns}"
      let some nh := toNatK? nh | throw s!"bad count {nh}"
      let some fs := toNatK? fs | throw s!"bad index {fs}"
      if fs + ns + nh > offs.length then throw s!"{IR.StackMap.tableSym}: entry {l} out of range"
      pure (a, (offs.drop fs).take ns, (offs.drop (fs + ns)).take nh)
    | q => throw s!"bad entry line {q}"

/-- **The entries of the `scc_stackmap` table** of the text: return address (the address of
the entry's label in `items`), stack slots, heap slots. -/
def stackTable (its : List Scc.Emit.X64.Item) (items : List Maps.Item) :
    Except String (List (Nat × List Int × List Int)) :=
  stackEntriesWith its fun l => match labelAddr items l with
    | some a => pure a
    | none => throw s!"{IR.StackMap.tableSym}: no label {l}"

/-! ## Tags -/

/-- The tag of an IR register of `f` (`Func.heapRegs`, `Func.stackRegs`), if any. -/
def tagOf (f : IR.Func) (r : IR.Reg) : Option Tag :=
  if f.heapRegs.contains r then some .heap else if f.stackRegs.contains r then some .stack else none

/-- The tagged machine registers that receive the operands `vs`, in order, in `regs`. -/
def regTags (f : IR.Func) (regs : List Reg64) (vs : List IR.Operand) : List (Loc × Tag) :=
  (vs.zip regs).filterMap fun
    | (.reg v, m) => (tagOf f v).map ((.reg (regNum m)), ·)
    | (.imm _, _) => none

/-- The tagged parameter registers of `f`. -/
def paramTags (f : IR.Func) : List (Loc × Tag) := regTags f argRegs (f.params.map .reg)

/-- The tagged result registers of `f`: those of its first `ret` (`tagsOf` checks that its `ret`s
agree). -/
def resultTags (f : IR.Func) : List (Loc × Tag) :=
  (f.blocks.findSome? fun b => match b.term with | .ret vs => some (regTags f retRegs vs) | _ => none).getD []

/-- The labels from which on `f`'s code is stubs, in emission order (`Scc.Emit.X64.emitFunc`),
then the end of `f`. -/
def stubLabels (f : IR.Func) : List String :=
  (if f.blocks.any (·.insts.any fun | .addChk .. => true | _ => false) then [labelOf f.name "ovf"]
   else []) ++ (cloneEntries f).map (childL f.name) ++
  (if f.checkStack then [labelOf f.name "stk"] else []) ++ [endL f.name]

/-- The body of `f` as an address range `[start, end)` of the text. -/
def bodyRange (f : IR.Func) (items : List Maps.Item) : Except String (Nat × Nat) := do
  let some b := f.blocks.head? | throw s!"{f.name}: no blocks"
  let some s := labelAddr items (labelOf f.name b.label) | throw s!"{f.name}: no body label"
  let some e := labelAddr items ((stubLabels f).headD (endL f.name)) | throw s!"{f.name}: no end"
  pure (s, e)

/-- **The tags of IR function `f` of `p`** (see the module docstring), with its entries of the
`scc_stackmap` table `tbl` (those inside its body, and its grow stub's). An error if its `ret`s
disagree on the tags of their results. -/
def tagsOf (p : IR.Program) (items : List Maps.Item) (tbl : List (Nat × List Int × List Int))
    (f : IR.Func) : Except String FnTags := do
  let some b := f.blocks.head? | throw s!"{f.name}: no blocks"
  let (s, e) ← bodyRange f items
  let rets := f.blocks.filterMap fun b => match b.term with
    | .ret vs => some (regTags f retRegs vs) | _ => none
  let result := rets.headD []
  unless rets.all (· == result) do throw s!"{f.name}: its rets disagree on the result tags"
  let fr := frameOf [] f
  let growRa := if f.checkStack && p.growth.isSome then
      (growCall items (labelOf f.name "stk")).map fun (a, z, _) => a + z
    else none
  pure {
    paramPts := [f.name] ++ (if f.checkStack && p.growth.isSome then [labelOf f.name "chk"] else [])
    bodyStart := labelOf f.name b.label
    bodyEnd := some ((stubLabels f).headD (endL f.name))
    growStub := if f.checkStack && p.growth.isSome then some (labelOf f.name "stk") else none
    params := paramTags f
    result
    slots := fr.slots.filterMap fun (r, k) => (tagOf f r).map (-(8 * ((k : Int) + 1)), ·)
    -- per call, in emission order: the caller's own tags of its destination registers
    callRes := f.blocks.flatMap fun b => b.insts.filterMap fun
      | .call ds _ _ => some (regTags f retRegs (ds.map .reg)) | _ => none
    stackmap := tbl.filter fun (a, _, _) => (s ≤ a && a < e) || some a == growRa }

/-! ## The tables -/

/-- **The tables of an emitted x64 program** (`Scc.Cert.Maps.compute`): its IR `p`, its items
`its` and the sizes of its instructions. -/
def computeX64 (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String Tables := do
  let items ← itemsOf its sizes
  let tbl ← stackTable its items
  let fns ← p.funcs.mapM (tagsOf p items tbl)
  compute fns items

/-- The items and the per-function tags `computeX64` computes from (for the checker with
witnesses, `Scc.Cert.Maps.checkW`). -/
def fnTagsX64 (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String (List Item × List FnTags) := do
  let items ← itemsOf its sizes
  let tbl ← stackTable its items
  pure (items, ← p.funcs.mapM (tagsOf p items tbl))

/-- **The exemptions** (see the module docstring), all computed from the text: the routines of
the text (`.type f, @function`) that are no IR function, the return addresses of the
`scc_stackmap` entries outside every function body other than the grow stubs' (whose calls have
maps, `FnTags.growStub`), and the calls after a zeroed frame pointer
(`itemsExits`: address, callee), which are no safe points. A test pins all three per fixture, so
that no ordinary call is exempted unnoticed. -/
def exemptions (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String (List String × List Nat × List (Nat × String)) := do
  let (items, exits) ← itemsExits its sizes
  let tbl ← stackTable its items
  let rs ← p.funcs.mapM (bodyRange · items)
  let grows := p.funcs.filterMap fun f =>
    if f.checkStack && p.growth.isSome then
      (growCall items (labelOf f.name "stk")).map fun (a, z, _) => a + z
    else none
  let fns := its.filterMap fun
    | .dir s => match splitK s ", " with
      | [h, "@function"] => match splitK h " " with | [".type", f] => some f | _ => none
      | _ => none
    | _ => none
  pure (fns.filter fun f => !p.funcs.any (·.name == f),
    (tbl.filter fun (a, _, _) => !grows.contains a && !rs.any fun (s, e) => s ≤ a && a < e).map
      (·.1), exits)

/-! ## Per-function slices

A certificate's kernel run cannot afford the items of the whole text (`itemsOf` alone takes most
of the memory it has), so the tables of a set of functions are computed on **slices**: each
function's part of the text, from its `.type f, @function` line up to the next such line (or the
end of `.text`), read from the function's start address with its share of the sizes
(`slices`). What a slice cuts off is the other functions; the per-function computation (`fnMaps`,
`fnSuccs`, `outSuccs`) stays inside the function (a branch to another function's label is a
target outside the body, a tail successor by name, not by address), and the tests check that the sliced tables are
the full text's on the test programs (`computeSliced` against `compute`). -/

/-- The function a `.type f, @function` line opens. -/
def typeOf? (s : String) : Option String :=
  match splitK s ", " with
  | [h, "@function"] => match splitK h " " with | [".type", f] => some f | _ => none
  | _ => none

/-- A slice of the text: the function it opens with, its start address, its items and the sizes
of its instructions. -/
structure Slice where
  name : String
  start : Nat
  its : List Scc.Emit.X64.Item
  sizes : List Nat

/-- **The text cut at its `.type f, @function` lines** (see above): one slice per function, in
the order of the text, up to the first section switch (which closes the last slice); the part
before the first function is no slice. Each instruction takes the next size. -/
def slices (its : List Scc.Emit.X64.Item) (sizes : List Nat) : List Slice :=
  let close (cur : Option (String × Nat × List Scc.Emit.X64.Item × List Nat)) (acc : List Slice) :
      List Slice :=
    match cur with
    | some (f, a, is, zs) => ⟨f, a, is.reverse, zs.reverse⟩ :: acc
    | none => acc
  let push (cur : Option (String × Nat × List Scc.Emit.X64.Item × List Nat))
      (it : Scc.Emit.X64.Item) (z : Option Nat) :=
    cur.map fun (f, a, is, zs) => (f, a, it :: is, match z with | some z => z :: zs | none => zs)
  let rec go : List Scc.Emit.X64.Item → List Nat → Nat →
      Option (String × Nat × List Scc.Emit.X64.Item × List Nat) → List Slice → List Slice
    | [], _, _, cur, acc => (close cur acc).reverse
    | .dir s :: rest, zs, a, cur, acc =>
      if endsText s then (close (push cur (.dir s) none) acc).reverse
      else match typeOf? s with
        | some f => go rest zs a (some (f, a, [.dir s], [])) (close cur acc)
        | none => go rest zs a (push cur (.dir s) none) acc
    | .d (.label l) :: rest, zs, a, cur, acc => go rest zs a (push cur (.d (.label l)) none) acc
    | .d d :: rest, z :: zs, a, cur, acc => go rest zs (a + z) (push cur (.d d) (some z)) acc
    | it :: rest, zs, a, cur, acc => go rest zs a (push cur it none) acc
  go its sizes 0 none []

/-- The entries of the `scc_stackmap` table with their labels (`stackEntriesWith`). -/
def stackEntries (its : List Scc.Emit.X64.Item) :
    Except String (List (String × List Int × List Int)) :=
  stackEntriesWith its pure

/-- **The tables of the functions `sel` of `p`, each on its slice**: each function's tags and
tables from its slice's items (`itemsExitsFrom` at the slice's start) and the `scc_stackmap`
entries whose labels are in the slice, merged in address order as `compute` does. An error if a
selected function has no slice or more than one. -/
def computeSliced (p : IR.Program) (its : List Scc.Emit.X64.Item) (sizes : List Nat)
    (sel : IR.Func → Bool) : Except String Tables := do
  let ents ← stackEntries its
  let sl := slices its sizes
  let xs ← (p.funcs.filter sel).mapM fun f => do
    let s ← match sl.filter (·.name == f.name) with
      | [s] => pure s
      | _ => throw s!"computeSliced: no single slice of {f.name}"
    let (items, _) ← itemsExitsFrom s.start s.its s.sizes
    let tbl := ents.filterMap fun (l, st, hp) => (labelAddr items l).map (·, st, hp)
    pure (items, ← tagsOf p items tbl f)
  let ts ← xs.mapM fun (items, ft) => compute [ft] items
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) (ts.flatMap (·.maps)),
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (ts.flatMap (·.succs)) }

/-! ## Per-function slices cut at entry labels

The kernel-run form of the slices: `slices` reads every `.type` line and `stackEntries` every
`.quad` line, which costs a certificate's kernel run more than it has. Here a function's slice
runs from its entry label (its symbol) to the next **entry label of any routine** of the text, in
text order (`entryLabels`: the IR functions, user and runtime, and the two routines that are no
IR function, `_start` and `scc_rt_morestack`), or the end of `.text`; only the selected functions'
slices are kept (`slicesByLabel`), and the call maps come from the emitter's safepoint list
(`Scc.Emit.X64.emitItemsMaps`), not from the `.quad` lines of the table
(`computeSlicedByLabel`). The tests check the safepoint list against the parsed table and the
tables against `computeSliced` and the full text's. -/

/-- **The entry labels of the text's routines**: `_start`, `scc_rt_morestack` (the routines
that are no IR function) and the IR functions of `p`. -/
def entryLabels (p : IR.Program) : List String :=
  "_start" :: IR.StackMap.morestackSym :: p.funcs.map (·.name)

/-- **The slices of the functions `sel`, cut at the entry labels `bs`**: for each label of `sel`
(in `bs`) in the text, the items from it up to the next label of `bs` or the first section
switch, read from its address with its share of the sizes; in the order of the text. The
`.globl`/`.type` lines of the next routine end the slice before it (no bytes, no labels). -/
def slicesByLabel (bs sel : List String) (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    List Slice :=
  -- `cur`: the selected function whose slice is open, its address, its items and sizes so far
  -- (reversed); `acc`: the closed slices (reversed).
  let close (cur : Option (String × Nat × List Scc.Emit.X64.Item × List Nat)) (acc : List Slice) :
      List Slice :=
    match cur with
    | some (f, a, is, zs) => ⟨f, a, is.reverse, zs.reverse⟩ :: acc
    | none => acc
  let push (cur : Option (String × Nat × List Scc.Emit.X64.Item × List Nat))
      (it : Scc.Emit.X64.Item) (z : Option Nat) :=
    cur.map fun (f, a, is, zs) => (f, a, it :: is, match z with | some z => z :: zs | none => zs)
  let rec go : List Scc.Emit.X64.Item → List Nat → Nat →
      Option (String × Nat × List Scc.Emit.X64.Item × List Nat) → List Slice → List Slice
    | [], _, _, cur, acc => (close cur acc).reverse
    | .dir s :: rest, zs, a, cur, acc =>
      if endsText s then (close (push cur (.dir s) none) acc).reverse
      else go rest zs a (push cur (.dir s) none) acc
    | .d (.label l) :: rest, zs, a, cur, acc =>
      if bs.contains l then
        go rest zs a (if sel.contains l then some (l, a, [.d (.label l)], []) else none)
          (close cur acc)
      else go rest zs a (push cur (.d (.label l)) none) acc
    | .d d :: rest, z :: zs, a, cur, acc => go rest zs (a + z) (push cur (.d d) (some z)) acc
    | it :: rest, zs, a, cur, acc => go rest zs a (push cur it none) acc
  go its sizes 0 none []

/-- **The tables of the functions `sel` of `p`, each on its slice cut at entry labels**
(`slicesByLabel`), the call maps from the emitter's safepoints `ms` (label, stack slots, heap
slots; `Scc.Emit.X64.emitItemsMaps`) whose labels are in the slice; merged in address order as
`computeSliced`. An error if a selected function has no slice or more than one. -/
def computeSlicedByLabel (p : IR.Program) (its : List Scc.Emit.X64.Item)
    (ms : List (String × List Int × List Int)) (sizes : List Nat) (sel : IR.Func → Bool) :
    Except String Tables := do
  let fs := p.funcs.filter sel
  let sl := slicesByLabel (entryLabels p) (fs.map (·.name)) its sizes
  let xs ← fs.mapM fun f => do
    let s ← match sl.filter (·.name == f.name) with
      | [s] => pure s
      | _ => throw s!"computeSlicedByLabel: no single slice of {f.name}"
    let (items, _) ← itemsExitsFrom s.start s.its s.sizes
    let tbl := ms.filterMap fun (l, st, hp) => (labelAddr items l).map (·, st, hp)
    pure (items, ← tagsOf p items tbl f)
  let ts ← xs.mapM fun (items, ft) => compute [ft] items
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) (ts.flatMap (·.maps)),
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (ts.flatMap (·.succs)) }

end Scc.Cert.MapsX64

import Scc.Emit.A64Func
import Scc.Cert.MapsCompute

/-!
# Certificate tables from AArch64 text (front end of `Scc.Cert.MapsCompute`)

AArch64: the inputs of `Scc.Cert.Maps.compute` from an emitted program
(`Scc.Emit.A64.Item`s) and its IR. Every instruction is 4 bytes.

* **Items** (`itemsExits`): the `.text` part of the emitted items (up to the first `.data`,
  `.bss` or `.section` line), a label at the offset of the next instruction, each instruction at
  its offset, classified (`classifyOp`). Frame slots are addressed from `sp`; the frame record
  is at `sp + R`, `R` read from the prologue's `add x29, sp, #R` (reset at each `.type` line), so
  `[sp, #k]` is slot `k - R`. A 64-bit `str` to `[sp, #k]` writes slot `k - R`, an `ldr`/`ldur`
  (or a narrower store) reads it, `add xd, sp, #k` takes its address. `bl`, `b`, `b.cond`,
  `cbz`/`cbnz` and `ret` give the control flow. A `bl` after `movz x29, #0` in the same
  label-free run (`switchTo`, the child stubs) never returns and is not a safe point: it is
  classified as leaving the function and listed by `exemptions`. Before `R` is known (the
  prologue's `str x29`/`str x30`) only the frame-record saves may address `sp`. Any other
  instruction that addresses `sp` (a register offset, an unknown `R`), `blr`, `br`, and any
  assembler line other than `.p2align`, `.type`, `.globl`, `.text` and `.arch` in the text fail
  the classification. Each `.type` line (and the end of the text) adds the synthetic label
  `endL f` at the end of the function before it.
* **Tags** (`tagsOf`), from the IR function (see the module docstring of `MapsCompute`: **tags
  trusted from the IR, tied to the text only via the certificates' `reproduces` guard; option B
  must discharge this**): the parameter and result registers `x0`… (`Scc.Emit.A64.argRegs`),
  tagged by `Func.heapRegs` / `Func.stackRegs`; the result registers of each call
  (`FnTags.callRes`) by the caller's own destination registers of that call (nothing from the
  callee); the slots of `Scc.Emit.A64.fnCtx` at `slotOff - (frame - 16)` from the frame
  record. The prologue's block entry is the function's symbol (its `stack_check` label, the grow
  stub's return point, is at the same address); the body runs from the first block's label to
  the first stub (`stack_grow` / `abort_stack`, `abort_overflow`, the child stubs) or the end of
  the function. The grow stub (`stack_grow`, under `Program.growth`) is `FnTags.growStub`: its
  call of `scc_rt_morestack` gets the map of its `scc_stackmap` entry (the save-area words of
  the tagged parameter registers live on entry, `8i - 64` from the stub's frame record; stack
  parameters in place).
* **Call maps** (`stackTable`): the `scc_stackmap` table of the text (its `.quad` lines), each
  entry's label resolved to its address.

Exemptions (`exemptions`, computed from the text): the routines of the text that are no IR
function (`scc_rt_morestack`; `_start` has no `.type` line and is a single branch before the
first function), the `scc_stackmap` entries outside every body other than the grow stubs'
`sp_check` entries (none today), and the calls after a zeroed frame pointer. The tests pin the
three lists per fixture.

Untrusted, like `MapsCompute`.
-/

namespace Scc.Cert.MapsA64
open Scc.Cert.Maps
open Scc.Emit.A64 (argRegs fnCtx cloneSites xregNum)

/-- The synthetic label at the end of function `f` (not in the text). -/
def endL (f : String) : String := s!".Lscc_end.{f}"

/-! ## Items -/

/-- Whether a register is `sp`. -/
def isSp {w : RegWidth} : RegOrSp w → Bool
  | .low .SP _ => true
  | _ => false

/-- The register of a `RegOrSp`, if not `sp`. -/
def spReg {w : RegWidth} : RegOrSp w → Option XReg
  | .low (.reg r) _ => some r
  | _ => none

/-- The register of a `RegOrZr`, if not the zero register. -/
def zrReg {w : RegWidth} : RegOrZr w → Option XReg
  | .low (.reg r) _ => some r
  | _ => none

/-- The integer value of a constant. -/
def constInt : ConstExpr → Option Int
  | .int64 i => some i.toInt
  | _ => none

/-- The `sp` offset `[sp, #k]` of an address with an immediate offset and no writeback. -/
def spImm (a : AddrExpr) : Option (Option Int) :=
  if isSp a.base then
    match a.off with
    | .imm ⟨c, none⟩ => some (constInt c)
    | _ => some none
  else none

/-- The `sp` offset of an unscaled address. -/
def spUnscaled (a : UnscaledAddrExpr) : Option (Option Int) :=
  if isSp a.base then some (constInt a.imm) else none

/-- An access to `sp + k`: `none` if not `sp`-based, `some none` if `sp`-based at an unknown
offset. With the frame record at `sp + R` (`r`), the slot `k - R`. -/
def slotOf (r : Option Int) : Option (Option Int) → Option (Option Int)
  | none => none
  | some (some k) => some (r.map (k - ·))
  | some none => some none

/-- **The classification of one operation** (see the module docstring); `fpZero`: `x29` was
zeroed in this label-free run; `r`: the frame record's offset from `sp`, if known. `none` for an
unclassified instruction. -/
def classifyOp (fpZero : Bool) (r : Option Int) {w : RegWidth} (op : Operation w) : Option Ins :=
  let rd (acc : Option (Option Int)) : Option Ins := match acc with
    | none => some {}
    | some (some o) => some { reads := [o] }
    | some none => none
  let wr (full : Bool) (src : Option XReg) (acc : Option (Option Int)) : Option Ins :=
    match acc with
    | none => some {}
    | some (some o) => some (if full then { writes := [o] } else { reads := [o] })
    | some none =>
      -- the frame-record saves before `R` is known
      if r.isNone && (src == some .X29 || src == some .X30) then some {} else none
  match op with
  | .LDR _ (.addr a) => rd (slotOf r (spImm a))
  | .LDR _ (.lit _) => some {}
  | .LDUR _ a => rd (slotOf r (spUnscaled a))
  | .LDRB _ a | .LDRH _ a => rd (slotOf r (spImm a))
  | .LDURB _ a | .LDURH _ a => rd (slotOf r (spUnscaled a))
  | .STR s a => wr (w == .W64) (zrReg s) (slotOf r (spImm a))
  | .STUR s a => wr (w == .W64) (zrReg s) (slotOf r (spUnscaled a))
  -- From `sp`: the frame's allocation and release (`sp := sp ± F`), the frame record
  -- (`add x29, sp, #R`), the stack check (`sub x9, sp, #F`), and a slot's address
  -- (`add xd, sp, #k`, `slotAddr`); nothing else.
  | .ADD_e d s (.imm ⟨c, sh⟩) =>
    if !isSp s || spReg d == none || spReg d == some .X29 then some {}
    else if sh == .S0 then
      match slotOf r (some (constInt c)) with
      | some (some o) => some { takes := [o] }
      | _ => none
    else none
  | .SUB_e d s (.imm _) =>
    if !isSp s || spReg d == none || spReg d == some .X9 then some {} else none
  | .ADD_e _ s _ | .SUB_e _ s _ => if isSp s then none else some {}
  | .BL t => match t with
    | .label g => some { flow := if fpZero then .stop else .call g }
    | _ => none
  | .B (.label l) => some { flow := .jmp l }
  | .B_cond _ (.label l) => some { flow := .jcc l }
  | .CBZ _ (.label l) | .CBNZ _ (.label l) => some { flow := .jcc l }
  | .RET _ => some { flow := .ret }
  | .B _ | .B_cond _ _ | .CBZ _ _ | .CBNZ _ _ | .BLR _ | .BR _ => none
  | _ =>
    -- any other instruction must not address `sp`
    if containsK (Scc.Emit.A64.ppOperation op) "[sp" then none else some {}

/-- `movz x29, #0`: the frame-record chain ends here. -/
def zeroesFp : Directive → Bool
  | .instr ⟨_, .MOVZ d (.int64 0) _⟩ => zrReg d == some .X29
  | _ => false

/-- `add x29, sp, #R`: the frame record's offset from `sp`. -/
def setsFp : Directive → Option Int
  | .instr ⟨_, .ADD_e d s (.imm ⟨c, .S0⟩)⟩ =>
    if spReg d == some .X29 && isSp s then constInt c else none
  | _ => none

/-- The assembler lines allowed in the text (they place no bytes). -/
def rawOkInText (s : String) : Bool :=
  [".p2align ", ".type ", ".globl ", ".arch ", ".size "].any (fun p => startsK s p) || s == ".text"

/-- The section switches that end `.text`. -/
def endsText (s : String) : Bool :=
  s == ".data" || s == ".bss" || startsK s ".section"

/-- The function a `.type f, %function` line opens. -/
def typeOf? (s : String) : Option String :=
  match splitK s ", " with
  | [h, "%function"] => match splitK h " " with | [".type", f] => some f | _ => none
  | _ => none

/-- `.p2align k`: `k`. -/
def p2alignOf? (s : String) : Option Nat :=
  match splitK s " " with
  | [".p2align", k] => toNatK? k
  | _ => none

/-- `--host raw`: whether the text after label `l` is in the kernel routine trampolines
(`[Tcb.kabiStartSym, Tcb.kabiEndSym)`), `kb` whether the text before it is. -/
def kabiAfter (kb : Bool) (l : String) : Bool :=
  if l == IR.Tcb.kabiStartSym then true else if l == IR.Tcb.kabiEndSym then false else kb

/-- The classification of an operation in the text (`classifyOp`); in the kernel routine
trampolines (`kb`, `kabiAfter`), a branch to a register (`br x16`, `Scc.Emit.A64.kabiItems`)
leaves the unit (`.stop`). Anywhere else, in a function body in particular, it stays
unclassified, so the tables refuse it. -/
def classifyIn (kb fpZero : Bool) (r : Option Int) {w : RegWidth} (op : Operation w) : Option Ins :=
  match kb, op with
  | true, .BR _ => some { flow := .stop }
  | _, _ => classifyOp fpZero r op

/-- **The items of the text** (see the module docstring), and the calls classified as leaving
the function after a zeroed frame pointer (`(address, callee)`). An error if an instruction or
an assembler line is unclassified. The text starts at address `a0` (`itemsExits`: 0; a slice of
the text, `Scc.Cert.MapsA64.slices`, at its own). -/
def itemsExitsFrom (a0 : Nat) (its : List Scc.Emit.A64.Item) :
    Except String (List Maps.Item × List (Nat × String)) :=
  let close (cur : Option String) (a : Nat) (acc : List Maps.Item) : List Maps.Item :=
    match cur with | some f => .label a (endL f) :: acc | none => acc
  let rec go : List Scc.Emit.A64.Item → Nat → Bool → Bool → Option Int → Option String →
      List Maps.Item → List (Nat × String) → Except String (List Maps.Item × List (Nat × String))
    | [], a, _, _, _, cur, acc, ex => .ok ((close cur a acc).reverse, ex.reverse)
    | .raw s :: rest, a, fz, kb, r, cur, acc, ex =>
      if endsText s then .ok ((close cur a acc).reverse, ex.reverse)
      else if !rawOkInText s then .error s!"itemsOf: assembler line in the text at {a}: {s}"
      else match typeOf? s with
        | some f => go rest a false kb none (some f) (close cur a acc) ex
        | none => match p2alignOf? s with
          | some k => go rest ((a + 2 ^ k - 1) / 2 ^ k * 2 ^ k) fz kb r cur acc ex
          | none => go rest a fz kb r cur acc ex
    | .d (.label l) :: rest, a, _, kb, r, cur, acc, ex =>
      go rest a false (kabiAfter kb l) r cur (.label a l :: acc) ex
    | .d d@(.instr ⟨_, op⟩) :: rest, a, fz, kb, r, cur, acc, ex =>
      match classifyIn kb fz r op with
      | some i =>
        let fz' := match i.flow with | .call _ | .stop => false | _ => fz || zeroesFp d
        let ex' := match op with
          | .BL (.label g) => if fz then (a, g) :: ex else ex
          | _ => ex
        let r' := match setsFp d with | some v => some v | none => r
        go rest (a + 4) fz' kb r' cur (.ins a 4 i :: acc) ex'
      | none => .error s!"itemsOf: unclassified instruction at {a}: {Scc.Emit.A64.ppDirective d}"
    | .d d :: _, a, _, _, _, _, _, _ => .error s!"itemsOf: unexpected directive at {a}: {Scc.Emit.A64.ppDirective d}"
    | .comment _ :: rest, a, fz, kb, r, cur, acc, ex => go rest a fz kb r cur acc ex
  go its a0 false false none none [] []

/-- **The items of the text** from address 0 (`itemsExitsFrom`). -/
def itemsExits (its : List Scc.Emit.A64.Item) :
    Except String (List Maps.Item × List (Nat × String)) :=
  itemsExitsFrom 0 its

/-- The items of the text (`itemsExits`). -/
def itemsOf (its : List Scc.Emit.A64.Item) : Except String (List Maps.Item) :=
  (·.1) <$> itemsExits its

/-! ## The `scc_stackmap` table -/

/-- The operands of a `.quad` line. -/
def quadArgs (s : String) : Option (List String) :=
  match splitK s ".quad " with
  | ["", rest] => some (splitK rest ", ")
  | _ => none

/-- **The entries of the `scc_stackmap` table** of the text, keyed by their labels: label, then
for each a check of the label (`chk`, run before the entry's counts are read), stack slots, heap
slots. -/
def stackEntriesWith {α : Type} (its : List Scc.Emit.A64.Item) (chk : String → Except String α) :
    Except String (List (α × List Int × List Int)) := do
  let rest := its.dropWhile fun | .d (.label l) => l != IR.StackMap.tableSym | _ => true
  if rest.isEmpty then throw s!"no {IR.StackMap.tableSym}"
  let qs := ((rest.drop 1).takeWhile fun | .raw s => (quadArgs s).isSome | _ => false).filterMap
    fun | .raw s => quadArgs s | _ => none
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
def stackTable (its : List Scc.Emit.A64.Item) (items : List Maps.Item) :
    Except String (List (Nat × List Int × List Int)) :=
  stackEntriesWith its fun l => match labelAddr items l with
    | some a => pure a
    | none => throw s!"{IR.StackMap.tableSym}: no label {l}"

/-! ## Tags -/

/-- The tag of an IR register of `f` (`Func.heapRegs`, `Func.stackRegs`), if any. -/
def tagOf (f : IR.Func) (r : IR.Reg) : Option Tag :=
  if f.heapRegs.contains r then some .heap else if f.stackRegs.contains r then some .stack else none

/-- The tagged machine registers `x0`… that receive the operands `vs`, in order. -/
def regTags (f : IR.Func) (vs : List IR.Operand) : List (Loc × Tag) :=
  (vs.zip argRegs).filterMap fun
    | (.reg v, m) => (tagOf f v).map ((.reg (xregNum m)), ·)
    | (.imm _, _) => none

/-- The tagged parameter registers of `f`. -/
def paramTags (f : IR.Func) : List (Loc × Tag) := regTags f (f.params.map .reg)

/-- The tagged result registers of `f`: those of its first `ret` (`tagsOf` checks that its `ret`s
agree). -/
def resultTags (f : IR.Func) : List (Loc × Tag) :=
  (f.blocks.findSome? fun b => match b.term with | .ret vs => some (regTags f vs) | _ => none).getD []

/-- The labels from which on `f`'s code is stubs, in emission order (`Scc.Emit.A64.emitFunc`),
then the end of `f`. -/
def stubLabels (c : Scc.Emit.A64.FnCtx) (growth : Bool) (f : IR.Func) : List String :=
  (if f.checkStack then [c.local (if growth then "stack_grow" else "abort_stack")] else []) ++
  (if f.blocks.any (·.insts.any fun | .addChk .. => true | _ => false)
   then [c.local "abort_overflow"] else []) ++
  (cloneSites f).map (fun (k, _) => c.local s!"child{k}") ++ [endL f.name]

/-- The body of `f` as an address range `[start, end)` of the text. -/
def bodyRange (c : Scc.Emit.A64.FnCtx) (growth : Bool) (f : IR.Func) (items : List Maps.Item) :
    Except String (Nat × Nat) := do
  let some b := f.blocks.head? | throw s!"{f.name}: no blocks"
  let some s := labelAddr items (← c.blockLabel b.label) | throw s!"{f.name}: no body label"
  let some e := labelAddr items ((stubLabels c growth f).headD (endL f.name))
    | throw s!"{f.name}: no end"
  pure (s, e)

/-- **The tags of IR function `f`, the `fi`th of `p`** (see the module docstring), with the
argument areas `areas` and its entries of the `scc_stackmap` table `tbl` (those inside its
body, and its grow stub's). An error if its `ret`s disagree on the tags of their results. -/
def tagsOf (p : IR.Program) (areas : List (IR.Sym × Nat)) (items : List Maps.Item)
    (tbl : List (Nat × List Int × List Int)) (x : IR.Func × Nat) : Except String FnTags := do
  let (f, fi) := x
  let c := fnCtx p.abortFn p.growth areas fi f
  let some b := f.blocks.head? | throw s!"{f.name}: no blocks"
  let (s, e) ← bodyRange c p.growth.isSome f items
  let rets := f.blocks.filterMap fun b => match b.term with
    | .ret vs => some (regTags f vs) | _ => none
  let result := rets.headD []
  unless rets.all (· == result) do throw s!"{f.name}: its rets disagree on the result tags"
  let slots ← c.slots.filterMapM fun r => do
    match tagOf f r with
    | some g => pure (some ((← c.slotOff r) - ((c.frame : Int) - 16), g))
    | none => pure none
  let growRa := if f.checkStack && p.growth.isSome then
      (growCall items (c.local "stack_grow")).map fun (a, z, _) => a + z
    else none
  pure {
    paramPts := [f.name]
    bodyStart := ← c.blockLabel b.label
    bodyEnd := some ((stubLabels c p.growth.isSome f).headD (endL f.name))
    growStub := if f.checkStack && p.growth.isSome then some (c.local "stack_grow") else none
    params := paramTags f
    result
    slots
    -- per call, in emission order: the caller's own tags of its destination registers
    callRes := f.blocks.flatMap fun b => b.insts.filterMap fun
      | .call ds _ _ => some (regTags f (ds.map .reg)) | _ => none
    stackmap := tbl.filter fun (a, _, _) => (s ≤ a && a < e) || some a == growRa }

/-! ## The tables -/

/-- **The tables of an emitted AArch64 program** (`Scc.Cert.Maps.compute`): its IR `p` and its
items `its`. -/
def computeA64 (p : IR.Program) (its : List Scc.Emit.A64.Item) : Except String Tables := do
  let areas ← Scc.Emit.A64.emitPre p
  let items ← itemsOf its
  let tbl ← stackTable its items
  let fns ← p.funcs.zipIdx.mapM (tagsOf p areas items tbl)
  compute fns items

/-- The items and the per-function tags `computeA64` computes from (for the checker with
witnesses, `Scc.Cert.Maps.checkW`). -/
def fnTagsA64 (p : IR.Program) (its : List Scc.Emit.A64.Item) :
    Except String (List Item × List FnTags) := do
  let areas ← Scc.Emit.A64.emitPre p
  let items ← itemsOf its
  let tbl ← stackTable its items
  pure (items, ← p.funcs.zipIdx.mapM (tagsOf p areas items tbl))

/-- **The exemptions** (see the module docstring), all computed from the text: the routines of
the text (`.type f, %function`) that are no IR function, the return addresses of the
`scc_stackmap` entries outside every function body other than the grow stubs' (whose calls have
maps, `FnTags.growStub`), and the calls after a zeroed frame pointer
(address, callee), which are no safe points. -/
def exemptions (p : IR.Program) (its : List Scc.Emit.A64.Item) :
    Except String (List String × List Nat × List (Nat × String)) := do
  let areas ← Scc.Emit.A64.emitPre p
  let (items, exits) ← itemsExits its
  let tbl ← stackTable its items
  let rs ← p.funcs.zipIdx.mapM fun (f, fi) =>
    bodyRange (fnCtx p.abortFn p.growth areas fi f) p.growth.isSome f items
  let grows := p.funcs.zipIdx.filterMap fun (f, fi) =>
    if f.checkStack && p.growth.isSome then
      (growCall items ((fnCtx p.abortFn p.growth areas fi f).local "stack_grow")).map
        fun (a, z, _) => a + z
    else none
  let fns := its.filterMap fun | .raw s => typeOf? s | _ => none
  pure (fns.filter fun f => !p.funcs.any (·.name == f),
    (tbl.filter fun (a, _, _) => !grows.contains a && !rs.any fun (s, e) => s ≤ a && a < e).map
      (·.1), exits)

/-! ## Per-function slices

The AArch64 twin of the slices of `Scc.Cert.MapsX64`: the text cut at its `.type f, %function`
lines (`slices`), each slice read from its function's start address (`itemsExitsFrom`; a
`.p2align` line before the next `.type` line is the slice's, as in the whole text), and the
tables of a set of functions computed each on its slice (`computeSliced`). -/

/-- A slice of the text: the function it opens with, its start address and its items. -/
structure Slice where
  name : String
  start : Nat
  its : List Scc.Emit.A64.Item

/-- **The text cut at its `.type f, %function` lines**: one slice per function, in the order of
the text, up to the first section switch (which closes the last slice); the part before the
first function (`_start`) is no slice. -/
def slices (its : List Scc.Emit.A64.Item) : List Slice :=
  let close (cur : Option (String × Nat × List Scc.Emit.A64.Item)) (acc : List Slice) :
      List Slice :=
    match cur with
    | some (f, a, is) => ⟨f, a, is.reverse⟩ :: acc
    | none => acc
  let push (cur : Option (String × Nat × List Scc.Emit.A64.Item)) (it : Scc.Emit.A64.Item) :=
    cur.map fun (f, a, is) => (f, a, it :: is)
  let rec go : List Scc.Emit.A64.Item → Nat → Option (String × Nat × List Scc.Emit.A64.Item) →
      List Slice → List Slice
    | [], _, cur, acc => (close cur acc).reverse
    | .raw s :: rest, a, cur, acc =>
      if endsText s then (close (push cur (.raw s)) acc).reverse
      else match typeOf? s with
        | some f => go rest a (some (f, a, [.raw s])) (close cur acc)
        | none => match p2alignOf? s with
          | some k => go rest ((a + 2 ^ k - 1) / 2 ^ k * 2 ^ k) (push cur (.raw s)) acc
          | none => go rest a (push cur (.raw s)) acc
    | .d (.label l) :: rest, a, cur, acc => go rest a (push cur (.d (.label l))) acc
    | .d d :: rest, a, cur, acc => go rest (a + 4) (push cur (.d d)) acc
    | it :: rest, a, cur, acc => go rest a (push cur it) acc
  go its 0 none []

/-- The entries of the `scc_stackmap` table with their labels (`stackEntriesWith`). -/
def stackEntries (its : List Scc.Emit.A64.Item) :
    Except String (List (String × List Int × List Int)) :=
  stackEntriesWith its pure

/-- **The tables of the functions `sel` of `p`, each on its slice** (as
`Scc.Cert.MapsX64.computeSliced`). An error if a selected function has no slice or more than
one. -/
def computeSliced (p : IR.Program) (its : List Scc.Emit.A64.Item) (sel : IR.Func → Bool) :
    Except String Tables := do
  let areas ← Scc.Emit.A64.emitPre p
  let ents ← stackEntries its
  let sl := slices its
  let xs ← (p.funcs.zipIdx.filter (sel ·.1)).mapM fun x => do
    let s ← match sl.filter (·.name == x.1.name) with
      | [s] => pure s
      | _ => throw s!"computeSliced: no single slice of {x.1.name}"
    let (items, _) ← itemsExitsFrom s.start s.its
    let tbl := ents.filterMap fun (l, st, hp) => (labelAddr items l).map (·, st, hp)
    pure (items, ← tagsOf p areas items tbl x)
  let ts ← xs.mapM fun (items, ft) => compute [ft] items
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) (ts.flatMap (·.maps)),
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (ts.flatMap (·.succs)) }

/-! ## Per-function slices cut at entry labels

The kernel-run form of the slices (the AArch64 twin of `Scc.Cert.MapsX64.slicesByLabel`): a
function's slice runs from its entry label to the next **entry label of any routine** of the
text, in text order (`entryLabels`: the IR functions, user and runtime, and the two routines
that are no IR function, `_start` and `scc_rt_morestack`), or the end of `.text`; the call maps
come from the emitter's safepoint list (`Scc.Emit.A64.emitItemsMaps`). The assembler lines just
before an entry label (its `.p2align 2` and `.type f, %function`) go with it: `itemsExitsFrom`
needs the `.type` line for the function's end label `endL f`, and the `.p2align` re-aligns an
address already aligned. `_start` (the first routine, no IR function) is never selected, as in
`slices`. -/

/-- **The entry labels of the text's routines**: `_start`, `scc_rt_morestack` (the routines
that are no IR function) and the IR functions of `p`. -/
def entryLabels (p : IR.Program) : List String :=
  "_start" :: IR.StackMap.morestackSym :: p.funcs.map (·.name)

/-- **The slices of the functions `sel`, cut at the entry labels `bs`**: for each label of `sel`
(in `bs`) in the text, the assembler lines just before it, it, and the items up to the next
label of `bs` (without the assembler lines just before that) or the first section switch, read
from its address; in the order of the text. -/
def slicesByLabel (bs sel : List String) (its : List Scc.Emit.A64.Item) : List Slice :=
  -- `cur`: the selected function whose slice is open, its address and its items so far
  -- (reversed); `pend`: the assembler lines since the last other item (reversed); `acc`: the
  -- closed slices (reversed).
  let close (cur : Option (String × Nat × List Scc.Emit.A64.Item)) (acc : List Slice) :
      List Slice :=
    match cur with
    | some (f, a, is) => ⟨f, a, is.reverse⟩ :: acc
    | none => acc
  let push (cur : Option (String × Nat × List Scc.Emit.A64.Item))
      (pend : List Scc.Emit.A64.Item) (it : Scc.Emit.A64.Item) :=
    cur.map fun (f, a, is) => (f, a, it :: (pend ++ is))
  let rec go : List Scc.Emit.A64.Item → Nat → Option (String × Nat × List Scc.Emit.A64.Item) →
      List Scc.Emit.A64.Item → List Slice → List Slice
    | [], _, cur, pend, acc => (close (cur.map fun (f, a, is) => (f, a, pend ++ is)) acc).reverse
    | .raw s :: rest, a, cur, pend, acc =>
      if endsText s then (close (push cur pend (.raw s)) acc).reverse
      else match p2alignOf? s with
        | some k => go rest ((a + 2 ^ k - 1) / 2 ^ k * 2 ^ k) cur (.raw s :: pend) acc
        | none => go rest a cur (.raw s :: pend) acc
    | .d (.label l) :: rest, a, cur, pend, acc =>
      if bs.contains l then
        go rest a (if sel.contains l then some (l, a, .d (.label l) :: pend) else none) []
          (close cur acc)
      else go rest a (push cur pend (.d (.label l))) [] acc
    | .d d :: rest, a, cur, pend, acc => go rest (a + 4) (push cur pend (.d d)) [] acc
    | it :: rest, a, cur, pend, acc => go rest a (push cur pend it) [] acc
  go its 0 none [] []

/-- **The tables of the functions `sel` of `p`, each on its slice cut at entry labels**
(`slicesByLabel`), the call maps from the emitter's safepoints `ms` (label, stack slots, heap
slots; `Scc.Emit.A64.emitItemsMaps`) whose labels are in the slice; merged in address order as
`computeSliced`. An error if a selected function has no slice or more than one. -/
def computeSlicedByLabel (p : IR.Program) (its : List Scc.Emit.A64.Item)
    (ms : List (String × List Int × List Int)) (sel : IR.Func → Bool) : Except String Tables := do
  let areas ← Scc.Emit.A64.emitPre p
  let fs := p.funcs.zipIdx.filter (sel ·.1)
  let sl := slicesByLabel (entryLabels p) (fs.map (·.1.name)) its
  let xs ← fs.mapM fun x => do
    let s ← match sl.filter (·.name == x.1.name) with
      | [s] => pure s
      | _ => throw s!"computeSlicedByLabel: no single slice of {x.1.name}"
    let (items, _) ← itemsExitsFrom s.start s.its
    let tbl := ms.filterMap fun (l, st, hp) => (labelAddr items l).map (·, st, hp)
    pure (items, ← tagsOf p areas items tbl x)
  let ts ← xs.mapM fun (items, ft) => compute [ft] items
  pure { maps := sortStable (fun a b => decide (a.pt.addr ≤ b.pt.addr)) (ts.flatMap (·.maps)),
         succs := sortStable (fun a b => decide (a.addr ≤ b.addr)) (ts.flatMap (·.succs)) }

end Scc.Cert.MapsA64

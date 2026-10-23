import Scc.Cert.PlaceA64
import Scc.Test.Src

/-!
# The placement data's frame slots agree with the block data

On the AArch64 compilations of the test programs, for every compiled
function: each node has its assembler label in the listing; at the return
point of every call with results, the first instruction stores the first
result register `x0` to the slot `<fn>_rs` gives the call's first result
(`str x0, [sp, #n]`, at the block's static stack offset `sp`: slot
`sp + n`); every slot access (at its static offset,
`Scc.Cert.Blocks.A64.step`) `[sp, #n]` of the function's blocks (but the
grow stub's, on its own save area) is at a slot of `<fn>_rs`, at the frame
record (`-16`, `-8`), below the slots (the outgoing argument area) or at or
above the region base (the incoming argument area, by a tail call); and
every slot of `<fn>_rs` is accessed there.
Checked by evaluation.
-/

namespace Scc.Test.PlaceTest

open Scc Scc.Cert Scc.Cert.Place Scc.Lower

/-- The slot offset `n` of `ldr`/`str xR, [sp, #n]` (or `[sp]`), with the
register and whether it is a load. -/
def slotAccess (ins : String) : Option (Bool × String × Int) := do
  let (mn, rest) := Blocks.word ins
  guard (mn == "ldr" || mn == "str")
  match rest.splitOn ", " with
  | [r, "[sp]"] => some (mn == "ldr", r, 0)
  | [r, "[sp", n] =>
    guard (n.startsWith "#" && n.endsWith "]")
    let k ← Blocks.int? (String.ofList ((n.toList.drop 1).dropLast))
    some (mn == "ldr", r, k)
  | _ => none

/-- The check of one compiled function `f` (see the module docstring), with
its placement `fp`, its trace `ms` and the listing's blocks `bs`. -/
def checkFn (f : IR.Func) (fp : FnPlace) (ms : Array (Node × Point))
    (bs : Array Blocks.Block) : Except String Unit := do
  let rs := fp.slots
  let lab (n : Node) : Except String String :=
    match fp.labels.lookup n with
    | some l => pure l
    | none => throw s!"{f.name}: a node without label"
  -- the call results' slots, at the return points
  for (n, _) in ms do
    let .ret l i := n | continue
    let some b := f.blocks.find? (·.label == l) | throw s!"{f.name}: no block {l}"
    let some (.call (d :: _) _ _) := b.insts[i]? | continue
    let L ← lab n
    let some blk := bs.find? (fun blk => blk.label == L && blk.off == 0)
      | throw s!"{f.name}: no block at {L}"
    match blk.ins[0]?.bind slotAccess with
    | some (false, "x0", k) =>
      unless rs.lookup d == some (blk.so.sp + k) do
        throw s!"{f.name}: at {L}, x0 goes to slot {blk.so.sp + k}, but {d}'s is {rs.lookup d}"
    | _ => throw s!"{f.name}: at {L}, no store of x0 to a slot first"
  -- every slot access, but the grow stub's
  let lo := (rs.map (·.2)).foldl min 0
  let mut seen : List Int := []
  for blk in bs do
    unless blk.fn == f.name && !blk.label.endsWith ".stack_grow" && !blk.label.endsWith ".sp_check" do
      continue
    -- the static offsets through the block (`Scc.Cert.Blocks.A64.step`)
    let mut o := blk.so
    for ins in blk.ins do
      let (o', acc) := Blocks.A64.step o (Blocks.A64.classify ins)
      if let some a := acc then
        unless rs.any (·.2 == a) || a == -16 || a == -8 || a < lo || a ≥ 0 do
          throw s!"{f.name}: {ins} at {blk.label} accesses slot {a}"
        seen := a :: seen
      match o' with
      | some o' => o := o'
      | none => break
  for (r, k) in rs do
    unless seen.contains k do throw s!"{f.name}: the slot {k} of {r} is not accessed"

/-- The check of one program (see the module docstring); `ok` or the
failure. -/
def check (src : String) : String :=
  let r : Except String Unit := do
    let c ← match Frontend.run src with
      | .ok c => pure c
      | .error _ => throw "frontend"
    let cfg : Config := { arch := .arm }
    let ir ← Lower.lowerProgram cfg c
    let asm ← Emit.A64.emitProgram ir
    let fps ← A64.places ir
    let marks ← Lower.lowerMarks cfg c
    let bs := (← Blocks.analyse Blocks.A64.isa asm).blocks
    for (name, ms) in marks do
      let some f := ir.funcs.find? (·.name == name) | throw s!"no function {name}"
      let some fp := fps.find? (·.name == name) | throw s!"no placement of {name}"
      checkFn f fp ms bs
    discard <| Place.render "test" fps marks
  match r with
  | .ok () => "ok"
  | .error m => m

#guard check (w_src% "Scc/Test/hello.w") == "ok"
#guard check (w_src% "Scc/Test/hello1.w") == "ok"
#guard check (w_src% "Scc/Test/arith.w") == "ok"
#guard check (w_src% "Scc/Test/deeprec.w") == "ok"
#guard check (w_src% "Scc/Test/growmany.w") == "ok"
#guard check (w_src% "Scc/Test/handoff.w") == "ok"
#guard check (w_src% "Scc/Test/layout.w") == "ok"
#guard check (w_src% "Scc/Test/overflow.w") == "ok"
#guard check (w_src% "Scc/Test/spill.w") == "ok"
#guard check (w_src% "Scc/Test/stackcap.w") == "ok"
#guard check (w_src% "Scc/Test/tailloop.w") == "ok"
#guard check (w_src% "Scc/Test/tailwide.w") == "ok"
#guard check (w_src% "Scc/Test/threadcap.w") == "ok"

/-- The rodata node of `hello1`: `b`'s buffer pointer, the result of
`newBuf`'s allocation call, is stored at the return point `sp0` by
`str x0, [sp]` at stack offset `-48`: `b%0`'s slot. -/
def hello1 : Except String (List FnPlace) := do
  let .ok c := Frontend.run (w_src% "Scc/Test/hello1.w") | throw "frontend"
  A64.places (← Lower.lowerProgram { arch := .arm } c)

#guard (hello1.toOption.bind fun fps => (fps.find? (·.name == "wc_rodata")).bind
  (·.slots.lookup "b%0")) == some (-48)

-- The immediate table of `hello1` (`renderImms`, `scc --code`'s
-- `hello1Imms`): one term, where `m` and `two` are the immediate 2.
#guard (do
    let .ok c := Frontend.run (w_src% "Scc/Test/hello1.w") | throw "frontend"
    let es := immEntries (← Lower.lowerMarks { arch := .arm } c)
    pure ((es.map (·.1)).map arg |>.eraseDups.length, es.map fun (_, x, k, n) => (x, k, n))
    : Except String (Nat × List (String × Nat × Nat))).toOption ==
  some (1, [("m", 0, 2), ("two", 0, 2)])

-- The table of a program without immediates is the computable empty one.
#guard (renderImms "p" []).toOption.map (·.endsWith "fun _ _ _ => none\n") == some true

end Scc.Test.PlaceTest

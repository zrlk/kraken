import Spike.Test.Cert.A64Hello1Cert
import Scc.Cert.MapsA64
import Spike.Test.MapsOracle

/-!
# Certificate tables from AArch64 text: `hello1.w` (`Scc.Cert.MapsA64`)

The AArch64 twin of `Spike/Test/MapsX64Test.lean`: the tables of `hello1.w`'s AArch64 certificate
(its IR `loweredLit` and emitted items `emittedLit`) compute (`Scc.Cert.MapsA64.computeA64`),
have the format's shape, pass the checker, and hold the expected maps: `wc_main`'s heap
parameters `a.0` (`x0`) and `a.4` (`x4`) at its entry, the heap result `x0` at `wc_rodata`'s
`ret`, the runtime's tagged TCB slots across its calls, and the save words of the heap
parameters at the grow stubs' calls. The slot offsets agree with the emitter's own safepoints
(`emittedLit.2`).
-/

namespace Scc.Cert.MapsA64Test
open SccCertificate Scc.Cert.Maps Scc.Cert.MapsA64

/-- The computed tables (or the empty tables on an error). -/
def tables : Tables :=
  match computeA64 loweredLit.1 emittedLit.1 with
  | .ok t => t
  | .error _ => { maps := [], succs := [] }

#guard (computeA64 loweredLit.1 emittedLit.1).toOption.isSome
#guard tables.g1Ok
#guard (match (do
    let areas ← Scc.Emit.A64.emitPre loweredLit.1
    let items ← itemsOf emittedLit.1
    let tbl ← stackTable emittedLit.1 items
    let fns ← loweredLit.1.funcs.zipIdx.mapM (tagsOf loweredLit.1 areas items tbl)
    pure (check fns items tables) : Except String Bool) with
  | .ok b => b
  | .error _ => false)
-- The tables are the old `List.mergeSort` form (`Scc.Cert.MapsOracle.computeOracle`) transformed
-- by the label-keyed rules (`Scc.Cert.MapsOracle.computeTransformed`).
#guard (match (do
    let areas ← Scc.Emit.A64.emitPre loweredLit.1
    let items ← itemsOf emittedLit.1
    let tbl ← stackTable emittedLit.1 items
    let fns ← loweredLit.1.funcs.zipIdx.mapM (tagsOf loweredLit.1 areas items tbl)
    pure (MapsOracle.agrees fns items) : Except String Bool) with
  | .ok b => b
  | .error _ => false)

-- The routines without tags (`_start` has no `.type` line), no `scc_stackmap` entry left without
-- a map (the grow stubs' `sp_check` entries are their calls' maps), and the calls after a zeroed
-- frame pointer: exactly `scc_rt_start`'s `switchTo` call of `scc_rt_main` (no ordinary call is
-- exempted).
/-- info: Except.ok (["scc_rt_morestack"], [], [(112, "scc_rt_main")]) -/
#guard_msgs in
#eval exemptions loweredLit.1 emittedLit.1

/-- The maps with roots: `(kind, address, roots)`. -/
def rooted : List (Kind × Nat × List (Loc × Tag)) :=
  (tables.maps.filter (!·.roots.isEmpty)).map fun m => (m.pt.kind, m.pt.addr, m.roots)

#guard rooted ==
  [(.call, 72, [(.reg 0, .heap)]),
   (.blockEntry, 72, [(.reg 0, .heap)]),
   (.call, 84, [(.slot (-16), .heap)]),
   (.blockEntry, 84, [(.slot (-16), .heap)]),
   (.blockEntry, 120, [(.reg 0, .heap)]),
   (.blockEntry, 160, [(.slot (-64), .heap)]),
   (.call, 164, [(.slot (-64), .heap), (.reg 0, .heap)]),
   (.blockEntry, 164, [(.reg 0, .heap), (.slot (-64), .heap)]),
   (.call, 284, [(.slot (-64), .heap)]),
   (.ret, 696, [(.reg 0, .heap)]),
   (.ret, 1120, [(.reg 0, .heap)]),
   (.blockEntry, 1236, [(.reg 0, .heap)]),
   (.blockEntry, 1256, [(.slot (-32), .heap)]),
   (.call, 1264, [(.slot (-32), .heap)]),
   (.blockEntry, 1264, [(.slot (-32), .heap)]),
   (.call, 4632, [(.reg 0, .heap)]),
   (.blockEntry, 4632, [(.reg 0, .heap)]),
   (.ret, 4732, [(.reg 0, .heap)]),
   (.blockEntry, 4840, [(.reg 0, .heap), (.reg 4, .heap)]),
   (.blockEntry, 4896, [(.slot (-80), .heap)]),
   (.call, 5056, [(.slot (-64), .heap)])]

-- The call maps' slots are the emitter's safepoint slots: every heap offset the emitter
-- recorded (inside a body, or a grow stub's `sp_check`, the save word `8i - 64` of a heap
-- parameter in `xi`) is listed at a call.
#guard emittedLit.2.all fun (_, _, hp) =>
  hp.all fun o => tables.maps.any fun m => m.pt.kind == .call && m.roots.contains (.slot o, .heap)

-- The grow call's return address (`sp_check`) has only the call map (no block-entry map: the
-- documented gap) and a successor entry: the stub's jump back to `stack_check`, at the function's symbol, a prologue safe point,
-- so the scheduler can always place its next breakpoint from there.
#guard (match (do
    let areas ← Scc.Emit.A64.emitPre loweredLit.1
    let items ← itemsOf emittedLit.1
    pure (loweredLit.1.funcs.zipIdx.filterMap fun (f, fi) =>
      if f.checkStack then
        let c := Scc.Emit.A64.fnCtx loweredLit.1.abortFn loweredLit.1.growth areas fi f
        match growCall items (c.local "stack_grow"), labelAddr items f.name with
        | some (a, z, _), some e => some (a + z, e)
        | _, _ => none
      else none) : Except String (List (Nat × Nat))) with
  | .ok xs => xs.length == 3 && xs.all fun (r, e) =>
      tables.succs.any (fun s => s.addr == r && s.next == [e]) &&
      tables.maps.any fun m => m.pt == ⟨.blockEntry, e⟩
  | .error _ => false)

open Scc.Emit.A64 in
-- An `sp` access at an unknown offset fails the classification; a branch through a register too.
#guard (itemsOf [.d (.label "f"), ins (.LDR (xz .X9) (.addr ⟨spW64, .reg ⟨⟨.W64, xz .X16⟩, ⟨.UXTX, .E0⟩⟩⟩))]).toOption.isNone
open Scc.Emit.A64 in
#guard (itemsOf [.d (.label "f"), callReg .X9]).toOption.isNone
open Scc.Emit.A64 in
-- A `bl` after `movz x29, #0` leaves the function only in the same label-free run.
#guard (itemsExits ([.d (.label "f")] ++ movImm .X29 0 ++ [lbl "l", call "g"])).toOption.map (·.2)
  == some []
/-! ### The kernel-reducible text tests against the core string functions

As in `Spike/Test/MapsX64Test.lean`: the forms before the change to `Scc.Cert.Maps.containsK`,
`splitK`, `startsK`, `toNatK?`, `toIntK?`, kept verbatim, agree on every instruction and line of
the fixture. -/

/-- `classifyOp`'s test of any other instruction, on `String.splitOn` (the old form). -/
private def otherOracle {w : RegWidth} (op : Operation w) : Bool :=
  ((Scc.Emit.A64.ppOperation op).splitOn "[sp").length > 1

private def rawOkOracle (s : String) : Bool :=
  [".p2align ", ".type ", ".globl ", ".arch ", ".size "].any (fun p => s.startsWith p) || s == ".text"

private def typeOfOracle (s : String) : Option String :=
  match s.splitOn ", " with
  | [h, "%function"] => match h.splitOn " " with | [".type", f] => some f | _ => none
  | _ => none

private def p2alignOracle (s : String) : Option Nat :=
  match s.splitOn " " with
  | [".p2align", k] => k.toNat?
  | _ => none

private def quadArgsOracle (s : String) : Option (List String) :=
  match s.splitOn ".quad " with
  | ["", rest] => some (rest.splitOn ", ")
  | _ => none

private def fixOps : List Directive := emittedLit.1.filterMap fun | .d d => some d | _ => none
private def fixRaws : List String := emittedLit.1.filterMap fun | .raw s => some s | _ => none

#guard fixOps.length > 1000 && fixRaws.length > 100
#guard fixOps.all fun
  | .instr ⟨_, op⟩ => otherOracle op == containsK (Scc.Emit.A64.ppOperation op) "[sp"
  | _ => true
#guard fixRaws.all fun s =>
  rawOkInText s == rawOkOracle s && typeOf? s == typeOfOracle s && p2alignOf? s == p2alignOracle s &&
  quadArgs s == quadArgsOracle s &&
  endsText s == (s == ".data" || s == ".bss" || s.startsWith ".section") &&
  ((quadArgs s).getD []).all fun a => toNatK? a == a.toNat? && toIntK? a == a.toInt?
/-- Two results agree: both errors, or the same value. -/
private def sameR {α : Type} [BEq α] : Except String α → Except String α → Bool
  | .ok a, .ok b => a == b
  | .error _, .error _ => true
  | _, _ => false

/-- `itemsExits` before the change to list accumulators (the old form, on arrays). -/
private def itemsExitsOracle (its : List Scc.Emit.A64.Item) :
    Except String (List Scc.Cert.Maps.Item × List (Nat × String)) :=
  let close (cur : Option String) (a : Nat) (acc : Array Scc.Cert.Maps.Item) : Array Scc.Cert.Maps.Item :=
    match cur with | some f => acc.push (.label a (endL f)) | none => acc
  let rec go : List Scc.Emit.A64.Item → Nat → Bool → Option Int → Option String →
      Array Scc.Cert.Maps.Item → Array (Nat × String) → Except String (List Scc.Cert.Maps.Item × List (Nat × String))
    | [], a, _, _, cur, acc, ex => .ok ((close cur a acc).toList, ex.toList)
    | .raw s :: rest, a, fz, r, cur, acc, ex =>
      if endsText s then .ok ((close cur a acc).toList, ex.toList)
      else if !rawOkInText s then .error s!"itemsOf: assembler line in the text at {a}: {s}"
      else match typeOf? s with
        | some f => go rest a false none (some f) (close cur a acc) ex
        | none => match p2alignOf? s with
          | some k => go rest ((a + 2 ^ k - 1) / 2 ^ k * 2 ^ k) fz r cur acc ex
          | none => go rest a fz r cur acc ex
    | .d (.label l) :: rest, a, _, r, cur, acc, ex => go rest a false r cur (acc.push (.label a l)) ex
    | .d d@(.instr ⟨_, op⟩) :: rest, a, fz, r, cur, acc, ex =>
      match classifyOp fz r op with
      | some i =>
        let fz' := match i.flow with | .call _ | .stop => false | _ => fz || zeroesFp d
        let ex' := match op with
          | .BL (.label g) => if fz then ex.push (a, g) else ex
          | _ => ex
        let r' := match setsFp d with | some v => some v | none => r
        go rest (a + 4) fz' r' cur (acc.push (.ins a 4 i)) ex'
      | none => .error s!"itemsOf: unclassified instruction at {a}: {Scc.Emit.A64.ppDirective d}"
    | .d d :: _, a, _, _, _, _, _ => .error s!"itemsOf: unexpected directive at {a}: {Scc.Emit.A64.ppDirective d}"
    | .comment _ :: rest, a, fz, r, cur, acc, ex => go rest a fz r cur acc ex
  go its 0 false none none #[] #[]

-- `itemsExits` accumulates in lists (cheap in the kernel): the same as its old form on arrays,
-- on the fixture and the small texts above.
#guard sameR (itemsExits emittedLit.1) (itemsExitsOracle emittedLit.1)
open Scc.Emit.A64 in
#guard [[.d (.label "f")] ++ movImm .X29 0 ++ [lbl "l", call "g"], [.d (.label "f")] ++ movImm .X29 0 ++ [call "g"],
    [.d (.label "f"), callReg .X9], []].all fun its => sameR (itemsExits its) (itemsExitsOracle its)

open Scc.Emit.A64 in
-- The kernel evaluates the classification of an instruction the `sp` test reads.
example : (classifyOp false none (w := .W64) (.MOVZ (xz .X9) (.int64 5) .LSL0)).isSome = true := by
  decide +kernel
example : typeOf? ".type wc_main, %function" = some "wc_main" := by decide +kernel

open Scc.Emit.A64 in
#guard (itemsExits ([.d (.label "f")] ++ movImm .X29 0 ++ [call "g"])).toOption.map (·.2)
  == some [(4, "g")]

end Scc.Cert.MapsA64Test

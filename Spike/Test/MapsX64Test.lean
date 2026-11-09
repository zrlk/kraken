import Spike.Test.Cert.X64Hello1Cert
import Scc.Cert.MapsX64
import Spike.Test.MapsOracle

/-!
# Certificate tables from x64 text: `hello1.w` (`Scc.Cert.MapsX64`)

The tables of `hello1.w`'s x86-64 certificate (its IR `loweredLit`, its emitted items
`emittedLit` and the instruction sizes `sizes`) compute (`Scc.Cert.MapsX64.computeX64`), have
the format's shape, pass the checker, and hold the expected maps: `wc_main`'s heap parameters
`a.0` (`%rdi`) and `a.4` (`%r8`) at its prologue entries, the heap result `%rax` at
`wc_rodata`'s `ret`, the runtime's tagged TCB slot across its calls, and the save words of the
heap parameters at the grow stubs' calls.
-/

namespace Scc.Cert.MapsX64Test
open SccCertificate Scc.Cert.Maps Scc.Cert.MapsX64

/-- The computed tables (or the empty tables on an error). -/
def tables : Tables :=
  match computeX64 loweredLit.1 emittedLit.1 sizes with
  | .ok t => t
  | .error _ => { maps := [], succs := [] }

#guard (computeX64 loweredLit.1 emittedLit.1 sizes).toOption.isSome
#guard tables.g1Ok
#guard (match (do
    let items ← itemsOf emittedLit.1 sizes
    let tbl ← stackTable emittedLit.1 items
    let fns ← loweredLit.1.funcs.mapM (tagsOf loweredLit.1 items tbl)
    pure (check fns items tables) : Except String Bool) with
  | .ok b => b
  | .error _ => false)
-- The tables are the old `List.mergeSort` form (`Scc.Cert.MapsOracle.computeOracle`) transformed
-- by the label-keyed rules (`Scc.Cert.MapsOracle.computeTransformed`), with the fixture's real instruction sizes.
#guard (match (do
    let items ← itemsOf emittedLit.1 sizes
    let tbl ← stackTable emittedLit.1 items
    let fns ← loweredLit.1.funcs.mapM (tagsOf loweredLit.1 items tbl)
    pure (MapsOracle.agrees fns items) : Except String Bool) with
  | .ok b => b
  | .error _ => false)

-- The routines without tags, no `scc_stackmap` entry left without a map (the grow stubs'
-- entries are their calls' maps), and the calls after a zeroed frame pointer: exactly `_start`'s
-- call of `scc_rt_start` and `scc_rt_start`'s `switchTo` call of `scc_rt_main` (no ordinary call
-- is exempted).
/-- info: Except.ok (["_start", "scc_rt_morestack"], [], [(6, "scc_rt_start"), (133, "scc_rt_main")]) -/
#guard_msgs in
#eval exemptions loweredLit.1 emittedLit.1 sizes

/-- The maps with roots: `(kind, address, roots)`. -/
def rooted : List (Kind × Nat × List (Loc × Tag)) :=
  (tables.maps.filter (!·.roots.isEmpty)).map fun m => (m.pt.kind, m.pt.addr, m.roots)

#guard rooted ==
  [(.call, 87, [(.reg 0, .heap)]),
   (.blockEntry, 87, [(.reg 0, .heap)]),
   (.call, 100, [(.slot (-24), .heap)]),
   (.blockEntry, 100, [(.slot (-24), .heap)]),
   (.blockEntry, 140, [(.reg 7, .heap)]),
   (.blockEntry, 144, [(.reg 7, .heap)]),
   (.blockEntry, 171, [(.slot (-8), .heap)]),
   (.call, 176, [(.slot (-8), .heap), (.reg 0, .heap)]),
   (.blockEntry, 176, [(.reg 0, .heap), (.slot (-8), .heap)]),
   (.call, 256, [(.slot (-8), .heap)]),
   (.ret, 628, [(.reg 0, .heap)]),
   (.ret, 1083, [(.reg 0, .heap)]),
   (.blockEntry, 1182, [(.reg 7, .heap)]),
   (.blockEntry, 1194, [(.slot (-8), .heap)]),
   (.call, 1206, [(.slot (-8), .heap)]),
   (.blockEntry, 1206, [(.slot (-8), .heap)]),
   (.call, 4663, [(.reg 0, .heap)]),
   (.blockEntry, 4663, [(.reg 0, .heap)]),
   (.ret, 4754, [(.reg 0, .heap)]),
   (.blockEntry, 4786, [(.reg 7, .heap), (.reg 8, .heap)]),
   (.blockEntry, 4790, [(.reg 7, .heap), (.reg 8, .heap)]),
   (.blockEntry, 4833, [(.slot (-8), .heap)]),
   (.call, 4950, [(.slot (-8), .heap)])]

-- Every grow stub's call of `scc_rt_morestack` has a call map, keyed at its return address (above:
-- the save word `-8(%rbp)` of a heap parameter in `%rdi` live on entry; an empty map for a stub
-- without one).
#guard (match (do
    let items ← itemsOf emittedLit.1 sizes
    pure (loweredLit.1.funcs.filterMap fun f =>
      if f.checkStack then (growCall items (Scc.Emit.X64.labelOf f.name "stk")).map fun (a, z, _) => a + z
      else none) : Except String (List Nat)) with
  | .ok xs => xs.all fun a => tables.maps.any fun m => m.pt == ⟨.call, a⟩
  | .error _ => false)

-- The grow call's return address has only the call map (no block-entry map: the documented gap)
-- and a successor entry: the stub's jump back to the stack check `.L{f}.chk`, a prologue safe point, so the scheduler can
-- always place its next breakpoint from there.
#guard (match (do
    let items ← itemsOf emittedLit.1 sizes
    pure (loweredLit.1.funcs.filterMap fun f =>
      if f.checkStack then
        match growCall items (Scc.Emit.X64.labelOf f.name "stk"),
          labelAddr items (Scc.Emit.X64.labelOf f.name "chk") with
        | some (a, z, _), some c => some (a + z, c)
        | _, _ => none
      else none) : Except String (List (Nat × Nat))) with
  | .ok xs => xs.length == 3 && xs.all fun (r, c) =>
      tables.succs.any (fun s => s.addr == r && s.next == [c]) &&
      tables.maps.any fun m => m.pt == ⟨.blockEntry, c⟩
  | .error _ => false)

-- A classification failure is an error: a frame access the classifier does not know.
#guard (itemsOf [.d (.label "f"), .d (Scc.Emit.X64.i64 (.add (.mem (Scc.Emit.X64.mem .rbp (-8)))
  (Scc.Emit.X64.oi 1)))] [4]).toOption.isNone
-- A call after `xorl %ebp, %ebp` leaves the function only in the same label-free run.
#guard (itemsExits [.d (Scc.Emit.X64.i32 (.xor (Scc.Emit.X64.xr .rbp) (Scc.Emit.X64.or_ .rbp))),
  .d (.label "l"), .d (Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel "g")))] [2, 5]).toOption.map
  (·.2) == some []
#guard (itemsExits [.d (Scc.Emit.X64.i32 (.xor (Scc.Emit.X64.xr .rbp) (Scc.Emit.X64.or_ .rbp))),
  .d (Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel "g")))] [2, 5]).toOption.map
  (·.2) == some [(2, "g")]
-- The sizes must match the instructions.
#guard (itemsOf [.d (Scc.Emit.X64.i64 .ret)] []).toOption.isNone

/-! ### The kernel-reducible text tests against the core string functions

`classifyOp`, `sizeOf?`, `quadArgs`, `stackTable` and `exemptions` read lines with
`Scc.Cert.Maps.containsK`, `splitK`, `startsK`, `toNatK?` and `toIntK?`. The oracles below are their
forms before that change, on `String.splitOn` / `startsWith` / `toNat?` / `toInt?`, kept verbatim;
both agree on every instruction and line of the fixture. -/

/-- `classifyOp`'s test of an unclassified operation, on `String.splitOn` (the old form). -/
private def otherOracle {w : _root_.Width} (op : Operation w) : Option Ins :=
  match Scc.Emit.X64.ppOp op with
  | some s => if (s.splitOn "(%rbp").length > 1 then none else some {}
  | none => none

private def otherNow {w : _root_.Width} (op : Operation w) : Option Ins :=
  match Scc.Emit.X64.ppOp op with
  | some s => if containsK s "(%rbp" then none else some {}
  | none => none

private def sizeOfOracle (s : String) : Option String :=
  match s.splitOn "," with
  | h :: _ => match h.splitOn " " with
    | [".size", f] => some f
    | _ => none
  | [] => none

private def quadArgsOracle (s : String) : Option (List String) :=
  match s.splitOn ".quad " with
  | ["", rest] => some (rest.splitOn ", ")
  | _ => none

/-- The text's instructions and directive lines. -/
private def fixOps : List Directive := emittedLit.1.filterMap fun | .d d => some d | _ => none
private def fixDirs : List String := emittedLit.1.filterMap fun | .dir s => some s | _ => none

#guard fixOps.length > 1000 && fixDirs.length > 100
#guard fixOps.all fun
  | .instr (.regular _ _ op) => otherOracle op == otherNow op
  | _ => true
#guard fixDirs.all fun s =>
  sizeOf? s == sizeOfOracle s && quadArgs s == quadArgsOracle s &&
  endsText s == (s == ".data" || s == ".bss" || s.startsWith ".section") &&
  ((quadArgs s).getD []).all fun a => toNatK? a == a.toNat? && toIntK? a == a.toInt?
-- `sizeOf?` (on the UTF-8 bytes) is the old form on the samples and corner cases too.
#guard (Scc.Cert.Maps.textSamples ++ [".size f", ".size f,", ".size ,", ".size  f, x", ".size f g, x",
    ".sizef, x", ".size", ".size é, .-é", "\t.size f, .-f", ".size\tf, x", " .size f, x"]).all fun s =>
  sizeOf? s == sizeOfOracle s
/-- Two results agree: both errors, or the same value. -/
private def sameR {α : Type} [BEq α] : Except String α → Except String α → Bool
  | .ok a, .ok b => a == b
  | .error _, .error _ => true
  | _, _ => false

/-- `itemsExits` before the change to list accumulators (the old form, on arrays). -/
private def itemsExitsOracle (its : List Scc.Emit.X64.Item) (sizes : List Nat) :
    Except String (List Scc.Cert.Maps.Item × List (Nat × String)) :=
  let rec go : List Scc.Emit.X64.Item → List Nat → Nat → Bool → Array Scc.Cert.Maps.Item →
      Array (Nat × String) → Except String (List Scc.Cert.Maps.Item × List (Nat × String))
    | [], [], _, _, acc, ex => .ok (acc.toList, ex.toList)
    | [], _ :: _, _, _, _, _ => .error "itemsOf: more sizes than instructions"
    | .dir s :: rest, zs, a, fz, acc, ex =>
      if endsText s then
        if zs.isEmpty then .ok (acc.toList, ex.toList)
        else .error "itemsOf: more sizes than instructions"
      else match sizeOf? s with
        | some f => go rest zs a false (acc.push (.label a (endL f))) ex
        | none => go rest zs a fz acc ex
    | .d (.label l) :: rest, zs, a, _, acc, ex => go rest zs a false (acc.push (.label a l)) ex
    | .d d :: rest, zs, a, fz, acc, ex => match zs with
      | [] => .error "itemsOf: fewer sizes than instructions"
      | z :: zt => match classify fz d with
        | some i =>
          let fz' := match i.flow with | .call _ | .stop => false | _ => fz || dirZeroesFp d
          let ex' := match d with
            | .instr (.regular _ _ (.call t)) =>
              if fz then ex.push (a, (relLabel t).getD "?") else ex
            | _ => ex
          go rest zt (a + z) fz' (acc.push (.ins a z i)) ex'
        | none => .error s!"itemsOf: unclassified instruction at {a}: {(Scc.Emit.X64.ppDirective d).getD "?"}"
    | .raw s :: _, _, a, _, _, _ => .error s!"itemsOf: raw line at {a}: {s}"
    | _ :: rest, zs, a, fz, acc, ex => go rest zs a fz acc ex
  go its sizes 0 false #[] #[]

-- `itemsExits` accumulates in lists (cheap in the kernel): the same as its old form on arrays,
-- on the fixture and the small texts above.
#guard sameR (itemsExits emittedLit.1 sizes) (itemsExitsOracle emittedLit.1 sizes)
#guard [([.d (Scc.Emit.X64.i32 (.xor (Scc.Emit.X64.xr .rbp) (Scc.Emit.X64.or_ .rbp))), .d (.label "l"),
      .d (Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel "g")))], [2, 5]),
    ([.d (Scc.Emit.X64.i32 (.xor (Scc.Emit.X64.xr .rbp) (Scc.Emit.X64.or_ .rbp))),
      .d (Scc.Emit.X64.i64 (.call (Scc.Emit.X64.rel "g")))], [2, 5]),
    ([.d (Scc.Emit.X64.i64 .ret)], []), ([.d (Scc.Emit.X64.i64 .ret)], [1, 1])].all fun (its, zs) =>
  sameR (itemsExits its zs) (itemsExitsOracle its zs)

-- A frame access the classification does not know still fails it.
#guard (classifyOp false (w := .W64) (.cmp (.mem (Scc.Emit.X64.mem .rbp 16)) (.imm (.int64 5)))).isNone
-- The kernel evaluates the classification of an instruction the frame test reads.
example : (classifyOp false (w := .W64)
    (.cmp (.mem (Scc.Emit.X64.mem .rbx 16)) (.imm (.int64 5)))).isSome = true := by decide +kernel
example : sizeOf? ".size wc_main, .-wc_main" = some "wc_main" := by decide +kernel

end Scc.Cert.MapsX64Test

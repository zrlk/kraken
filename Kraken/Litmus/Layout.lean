/-
The memory layout of a litmus test or `.kl` program, shared by the ISA
front ends: where each symbol lives, which locations it declares and at
what width, its initial memory, and how a final value is presented.

Symbols get addresses in order of first mention, each in a slot of 256
bytes (an array larger than that gets enough 256-byte slots), from an
ISA-chosen base. A symbol is
- a *scalar*: one location at its address;
- an *array* `t a[n]`: `n` locations, element `i` at `a + i * sizeof t`.

Sized and legacy tests. A test that declares
the C type of some location (`int8_t x`, `uint128_t y`, `int64_t a[2]`, the
types of `typeInfo?`) is *sized*: each typed location is declared in `Decls`
at its width, so an access at another width is reported as mixed-size, as
herd does by default ("Illegal mixed-size test"), and a 16-byte access
reaches a 16-byte location; an untyped symbol stays unsized (any width up to
8 bytes), and an address no symbol names is its own footprint (strict mode,
with overlapping footprints reported by the explorer, `Machine.succsR`). A
test that types no location is *legacy*: every symbol and every other
address is unsized, which is herd's non-mixed default and the semantics
before typed locations, so untyped tests keep their verdicts. Register types only affect
presentation.
-/
import Kraken.Litmus.Syntax
import Kraken.Promising.Basic

namespace Kraken.Litmus

open Kraken.Promising

/-- One symbol of the layout. -/
structure SymLayout where
  name : String
  addr : BitVec 64
  /-- The declared C type (the element type for an array). -/
  ty : Option String := none
  /-- `some n` for an array of `n` elements. -/
  len : Option Nat := none
  deriving Repr, Inhabited

namespace SymLayout

/-- The declared type's width in bytes and signedness, if it is a known type. -/
def elem? (s : SymLayout) : Option (Nat × Bool) := s.ty.bind typeInfo?

/-- The size of the symbol's memory (8 bytes per element if untyped). -/
def bytes (s : SymLayout) : Nat := ((s.elem?.map (·.1)).getD 8) * s.len.getD 1

/-- The location of element `i` of `s` (`i = 0` for a scalar): at the
element width if typed (only in a sized test), else unsized. -/
def cell (s : SymLayout) (i : Nat) : Loc :=
  match s.elem? with
  | some (w, _) => { addr := s.addr + BitVec.ofNat 64 (i * w), bytes := w }
  | none => { addr := s.addr, bytes := 0 }

/-- The locations of a symbol: one for a scalar, one per element for an array. -/
def cells (s : SymLayout) : List Loc := (List.range (s.len.getD 1)).map (cell s)


end SymLayout

/-- The slot of a symbol of `n` bytes: 256 bytes, or `n` rounded up to a
multiple of 256. -/
def slotBytes (n : Nat) : Nat := max 0x100 ((n + 0xff) / 0x100 * 0x100)

structure MemLayout where
  syms : List SymLayout
  /-- Some location has a declared type (see the header). -/
  sized : Bool
  deriving Repr, Inhabited

namespace MemLayout

/-- Lay out the symbols `names` (in this order; `a[1]` stands for `a`) from
`base`, with the types and array declarations of the test's init block. -/
def build (base : Nat) (t : Test) (names : List String) : Except String MemLayout := do
  -- declarations: `t a[n]` (an array) and `t x` (a typed scalar)
  let decls ← t.inits.filterMapM fun
    | .loc x _ (some ty) =>
      match arrayRef? x with
      | some (a, n) => match n.trimAscii.copy.toNat? with
        | some n =>
          if (typeInfo? ty).isNone then throw s!"unsupported: array {x} of type {ty}"
          else pure (some (a, ty, some n))
        | none => throw s!"unsupported: array size {n} in {x}"
      | none => pure (some (x, ty, none))
    | _ => pure none
  let names := (names.map baseName ++ decls.map (·.1)).eraseDups
  let (syms, _) := names.foldl (init := ([], base)) fun (acc, cur) x =>
    let (ty, len) := match decls.find? (·.1 == x) with
      | some (_, ty, len) => (some ty, len)
      | none => (none, none)
    let s : SymLayout := { name := x, addr := BitVec.ofNat 64 cur, ty, len }
    (acc ++ [s], cur + slotBytes s.bytes)
  return { syms, sized := syms.any fun s => s.elem?.isSome }

def find? (l : MemLayout) (x : String) : Option SymLayout := l.syms.find? (·.name == x)

/-- The element `a[i]` named by `x`, if `x` is one, checked against the declaration. -/
def elemRef? (l : MemLayout) (x : String) : Option (SymLayout × Nat) := do
  let (a, i) ← arrayRef? x
  let s ← l.find? a
  let i ← i.trimAscii.copy.toNat?
  if i < s.len.getD 0 then some (s, i) else none

/-- The location a name denotes: a scalar, or an array element `a[i]`; a
whole array is not one location. -/
def locOf? (l : MemLayout) (x : String) : Option Loc :=
  match arrayRef? x with
  | some _ => (l.elemRef? x).map fun (s, i) => s.cell i
  | none => match l.find? x with
    | some s => if s.len.isSome then none else some (s.cell 0)
    | none => none

/-- The address a name denotes as a value (`0:X0=x`, `0:X0=a[1]`). -/
def addrOf? (l : MemLayout) (x : String) : Option (BitVec 64) :=
  match arrayRef? x with
  | some _ => (l.elemRef? x).map fun (s, i) => (s.cell i).addr
  | none => (l.find? x).map (·.addr)

/-- The declared type of a location, array or element. -/
def typeOf (l : MemLayout) (x : String) : Option String := (l.find? (baseName x)).bind (·.ty)

/-- The symbol whose address a value is. -/
def symOf? (l : MemLayout) (v : BitVec 128) : Option String :=
  (l.syms.find? fun s => s.addr.setWidth 128 == v).map (·.name)

/-- The symbol at an address, for traces. -/
def nameAt (l : MemLayout) (a : BitVec 64) : String :=
  match l.syms.find? (·.addr == a) with
  | some s => s.name
  | none =>
    match l.syms.findSome? fun s =>
        (s.cells.zipIdx.find? fun (c, _) => c.addr == a).map fun (_, i) => s!"{s.name}[{i}]" with
    | some x => x
    | none => s!"[{a.toNat}]"

/-- A numeric or symbolic value as 128 bits. -/
def valueBits? (l : MemLayout) : Value → Option (BitVec 128)
  | .num n => some (BitVec.ofInt 128 n)
  | .sym x => (l.addrOf? x).map (·.setWidth 128)
  | .arr _ => none

/-- A value stored at a location: truncated to the location's width (64
bits for an unsized one), zero-extended to `Val`. -/
def encode (loc : Loc) (v : BitVec 128) : Val :=
  if loc.bytes == 0 then (v.setWidth 64).setWidth 128 else (v.setWidth (8 * loc.bytes)).setWidth 128

/-- The initial memory: every location the init block gives a value
(`x=1`, `t a[2]={1,2}`, `a[1]=3`); the others are `0`. -/
def initMem (l : MemLayout) (t : Test) : Except String (List (Loc × Val)) := do
  let items ← t.inits.mapM fun
    | .loc x v ty => do
      match arrayRef? x, ty with
      | some (a, _), some _ =>
        let some s := l.find? a | throw s!"unknown location {a}"
        match v with
        | .arr vs =>
          if vs.length > s.cells.length then throw s!"too many initial values for {x}"
          (s.cells.zip vs).mapM fun (c, v) => do
            let some b := l.valueBits? v | throw s!"bad initial value for {x}"
            pure (c, encode c b)
        | .num 0 => pure []
        | _ => throw s!"bad initial value for {x}"
      | _, _ =>
        let some c := l.locOf? x | throw s!"unknown location {x}"
        let some b := l.valueBits? v | throw s!"bad initial value for {x}"
        pure [(c, encode c b)]
    | .reg .. => pure []
  return items.flatten

/-- The declarations every access is resolved against: every location of
every symbol and the initial memory's; strict if sized, else legacy. -/
def decls (l : MemLayout) (initMem : List (Loc × Val)) : Decls :=
  Decls.ofInit initMem (l.syms.flatMap SymLayout.cells) (unsizedDefault := !l.sized)

/-- A value as herd prints it at the declared type `ty`, else as `dflt`
(bits, signed); an address of a symbol is the symbol. -/
def present (l : MemLayout) (ty : Option String) (dflt : Nat × Bool) (v : BitVec 128) : Value :=
  match l.symOf? v with
  | some x => .sym x
  | none =>
    let (bits, signed) := match ty.bind typeInfo? with
      | some (w, s) => (8 * w, s)
      | none => dflt
    let w := v.setWidth bits
    .num (if signed then w.toInt else w.toNat)

/-- The final value of a location observable: a scalar or element, or the
whole array as `{v0,v1,...}`. Untyped memory prints as a signed 32-bit
`int`, herd's default. -/
def finalLoc (l : MemLayout) (mem : Memory) (x : String) : Value :=
  let ty := l.typeOf x
  match l.find? x with
  | some s =>
    if s.len.isSome then .arr (s.cells.map fun c => l.present ty (32, true) (mem.finalVal c))
    else l.present ty (32, true) (mem.finalVal (s.cell 0))
  | none => match l.locOf? x with
    | some c => l.present ty (32, true) (mem.finalVal c)
    | none => .num 0

/-- Re-present a literal of a location condition (`x=-1`, `a={1,2}`) as
`finalLoc` presents the location's value. -/
partial def normLoc (l : MemLayout) (x : String) : Value → Value
  | .num n => l.present (l.typeOf x) (32, true) (BitVec.ofInt 128 n)
  | .arr vs => .arr (vs.map (l.normLoc x))
  | v => v

end MemLayout

/-! ### Tests -/

private def showInit (m : List (Loc × Val)) : List (Nat × Nat × Nat) :=
  m.map fun (p : Loc × Val) => (p.1.addr.toNat, p.1.bytes, p.2.toNat)

private def testOf (src : String) : Test := (parse src).toOption.getD default

/-- info: sized: true
x @ 0x0000000000001000 ty (some int8_t) len none
a @ 0x0000000000001100 ty (some int64_t) len (some 2)
big @ 0x0000000000001200 ty (some uint64_t) len (some 40)
y @ 0x0000000000001400 ty none len none
cells: [(0x0000000000001000#64, 1), (0x0000000000001100#64, 8), (0x0000000000001108#64, 8), (0x0000000000001400#64, 0)]
init: [(4096, (1, 127)), (4352, (8, 1)), (4360, (8, 18446744073709551614)), (5120, (0, 18446744073709551615))]
a[1] at (some 0x0000000000001108#64); a[2] is false -/
#guard_msgs in
#eval do
  let t := testOf "AArch64 T\n{ int8_t x=127; int64_t a[2]={1,-2}; uint64_t big[40]; y=-1; }\n P0;\n NOP;\nexists (a={1,-2} /\\ a[1]=-2)"
  match MemLayout.build 0x1000 t ["x", "a[2]", "big[40]", "y"] with
  | .error e => IO.println e
  | .ok l =>
    IO.println s!"sized: {l.sized}"
    for s in l.syms do IO.println s!"{s.name} @ 0x{s.addr.toHex} ty {s.ty} len {s.len}"
    let cells : List Loc := (l.syms.filter fun (s : SymLayout) => s.name != "big").flatMap SymLayout.cells
    IO.println s!"cells: {cells.map fun (c : Loc) => (c.addr, c.bytes)}"
    match l.initMem t with
    | .ok m => IO.println s!"init: {showInit m}"
    | .error e => IO.println e
    IO.println s!"a[1] at {l.addrOf? "a[1]"}; a[2] is {(l.locOf? "a[2]").isSome}"

-- An untyped test is legacy: every symbol unsized, undeclared addresses unsized.
/-- info: sized: false; decls unsized default: true; x: some { addr := 0x0000000000001000#64, bytes := 0 } -/
#guard_msgs in
#eval do
  let t := testOf "X86_64 T\n{ x=1; uint64_t 0:rax; }\n P0;\n nop;\nexists (x=1)"
  match MemLayout.build 0x1000 t ["x"] with
  | .error e => IO.println e
  | .ok l => IO.println s!"sized: {l.sized}; decls unsized default: {(l.decls []).unsizedDefault}; x: {repr (l.locOf? "x")}"

-- A 128-bit type: a 16-byte location; values up to 128 bits, presented signed or unsigned.
/-- info: (16, ([(4096, (16, 340282366920938463463374607431768211455))], (-1, 340282366920938463463374607431768211455))) -/
#guard_msgs in
#eval do
  let t := testOf "X86_64 T\n{ __int128 x=-1; }\n P0;\n nop;\nexists (x=0xffffffffffffffffffffffffffffffff)"
  match MemLayout.build 0x1000 t ["x"] with
  | .error e => IO.println e
  | .ok l =>
    let m : List (Loc × Val) := (l.initMem t).toOption.getD []
    IO.println (((l.locOf? "x").map Loc.bytes).getD 0, showInit m,
      (l.normLoc "x" (.num 0xffffffffffffffffffffffffffffffff)).toString,
      (l.present (some "uint128_t") (64, true) (BitVec.ofInt 128 (-1))).toString)

end Kraken.Litmus

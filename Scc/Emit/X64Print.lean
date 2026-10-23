/-
x64 GNU assembler printer for `scc` (AT&T syntax).

This module turns Kraken's x64 syntax (`Directive` of `Kraken/X64/Syntax.lean`)
into GNU `as` text, and wraps it into a whole assembler file together with the
lines that Kraken's syntax cannot represent.

**Items.** An emitted file is a list of `Item`s:

* `Item.d`: a Kraken directive (an instruction with 64-bit addresses, or a
  label), printed by `ppDirective`;
* `Item.dir`: an assembler directive line (section, symbol, alignment, data,
  the stack-map table), which Kraken's `stripDirectives` removes;
* `Item.raw`: an instruction line in a form Kraken's x64 syntax does not
  have, copied verbatim (Kraken's parser rejects it). The emitter writes none:
  every instruction it needs, `syscall`, `ud2`, the `%fs:` moves, `div`,
  `idiv`, `cqto` and `popcnt` included, is a Kraken directive
  (`Kraken/SYSCALL.md`);
* `Item.comment` and `Item.blank`.

**Round trip.** The printer is not trusted: a certificate re-parses the text
with Kraken's own parser (`Kraken.X64.Parser.parse` after `stripDirectives`).
For every `Item.d` the emitter produces, `parse (render d) = [d]`, and every
`Item.dir`, comment and blank line reads back as nothing (`Item.roundTrips`;
`Scc/Emit/X64Test.lean` checks it on every item of the emitted programs).

**Spelling.** `ppDirective` prints one spelling per Kraken form: width
suffixes on every mnemonic except `cmov<cc>`, `set<cc>` and the jumps (the
parser reads a suffixed `cmov<cc>q` as an unknown condition code), the
condition codes `e`/`ne`/`b`/`ae`/`a`/`be`/`l`/`le`/`g`/`ge` (the parser
reads `z`/`c`/… as the same codes), and `movabsq` for a 64-bit register
immediate outside the sign-extended 32-bit range.
-/
import Kraken.X64.Parser

namespace Scc.Emit.X64

/-! ## Registers, constants and operands -/

/-- The AT&T width suffix. -/
def sfx : _root_.Width → String
  | .W8 => "b" | .W16 => "w" | .W32 => "l" | .W64 => "q"

/-- The name of a general purpose register at a width, without `%`. -/
def lowName (r : Reg64) (w : _root_.Width) : String :=
  let legacy (q l x b : String) : String :=
    match w with | .W64 => q | .W32 => l | .W16 => x | .W8 => b
  let numbered (n : Nat) : String :=
    s!"r{n}" ++ match w with | .W64 => "" | .W32 => "d" | .W16 => "w" | .W8 => "b"
  match r with
  | .rax => legacy "rax" "eax" "ax" "al" | .rbx => legacy "rbx" "ebx" "bx" "bl"
  | .rcx => legacy "rcx" "ecx" "cx" "cl" | .rdx => legacy "rdx" "edx" "dx" "dl"
  | .rsi => legacy "rsi" "esi" "si" "sil" | .rdi => legacy "rdi" "edi" "di" "dil"
  | .rsp => legacy "rsp" "esp" "sp" "spl" | .rbp => legacy "rbp" "ebp" "bp" "bpl"
  | .r8 => numbered 8 | .r9 => numbered 9 | .r10 => numbered 10 | .r11 => numbered 11
  | .r12 => numbered 12 | .r13 => numbered 13 | .r14 => numbered 14 | .r15 => numbered 15

/-- `%name`. -/
def ppReg {w : _root_.Width} : _root_.Reg w → String
  | .low r w => "%" ++ lowName r w
  | .ah => "%ah" | .bh => "%bh" | .ch => "%ch" | .dh => "%dh"

/-- A constant: a label or a signed decimal integer. -/
def ppConst : ConstExpr → Option String
  | .label l => some l
  | .int64 i => some (toString i.toInt)
  | _ => none

/-- A memory operand with 64-bit address registers: `d(%base,%idx,s)`,
`sym(%rip)` (which the parser reads as `sym - (end of instruction)` off
`%rip`), or `(sym)`. -/
def ppAddr (a : AddrExpr) : Option String :=
  match a.base, a.disp with
  | some .rip, .sub (.label l) .after_current_instruction =>
    if a.idx.isNone then some s!"{l}(%rip)" else none
  | some (.reg r), d => do
    let ds ← match d with
      | .int64 0 => some ""
      | d => ppConst d
    let ix := match a.idx with
      | none => ""
      | some ⟨x, sc⟩ => s!",%{lowName x .W64},{sc.bytes}"
    some s!"{ds}(%{lowName r .W64}{ix})"
  | none, .label l => if a.idx.isNone then some s!"({l})" else none
  | _, _ => none

/-- A `%fs`-relative memory operand: `%fs:disp` (absolute) or
`%fs:d(%base,%idx,s)`. -/
def ppFsAddr (a : AddrExpr) : Option String :=
  match a.base, a.idx with
  | none, none => do return "%fs:" ++ (← ppConst a.disp)
  | _, _ => do return "%fs:" ++ (← ppAddr a)

def ppRM {w : _root_.Width} : RegOrMem w → Option String
  | .reg r => some (ppReg r)
  | .mem a => ppAddr a

def ppOperand {w : _root_.Width} : _root_.Operand w → Option String
  | .regOrMem rm => ppRM rm
  | .imm c => ("$" ++ ·) <$> ppConst c

/-- A jump or call target. -/
def ppTarget : RelRegOrMem → Option String
  | .rel (.sub (.label l) .after_current_instruction) => some l
  | .reg r => some ("*" ++ ppReg r)
  | .mem a => ("*" ++ ·) <$> ppAddr a
  | _ => none

/-- The condition code spellings. -/
def ppCC : CondCode → String
  | .z => "e" | .nz => "ne" | .c => "b" | .nc => "ae" | .a => "a" | .be => "be"
  | .l => "l" | .le => "le" | .ge => "ge" | .g => "g"

def ppShift : ShiftCountExpr → Option String
  | .cl => some "%cl"
  | .imm8 c => ("$" ++ ·) <$> ppConst c

/-- A 64-bit immediate that `movq` cannot encode (it is not a sign-extended
32-bit value): the assembler, and the printer, write it with `movabsq`. -/
def needsMovabs (i : Int64) : Bool := i.toInt < -2 ^ 31 || i.toInt ≥ 2 ^ 31

/-! ## Instructions -/

/-- An operation in AT&T syntax, for the forms the emitter uses (and a few
more); `none` otherwise. -/
def ppOp {w : _root_.Width} : Operation w → Option String
  | .mov d s => do
    let isReg := match d with | RegOrMem.reg _ => true | RegOrMem.mem _ => false
    match s with
    | .imm (.int64 i) =>
      if w == .W64 && isReg && needsMovabs i then
        return s!"movabsq ${i.toBitVec.toNat}, {← ppRM d}"
    | _ => pure ()
    return s!"mov{sfx w} {← ppOperand s}, {← ppRM d}"
  | @Operation.movsx _ w' d s => do return s!"movs{sfx w'}{sfx w} {← ppRM s}, {← ppRM d}"
  | @Operation.movzx _ w' d s => do return s!"movz{sfx w'}{sfx w} {← ppRM s}, {← ppRM d}"
  | .push s => do return s!"push{sfx w} {← ppOperand s}"
  | .pop d => do return s!"pop{sfx w} {← ppRM d}"
  | .setcc cc d => do return s!"set{ppCC cc} {← ppRM d}"
  | .cmovcc cc d s => do return s!"cmov{ppCC cc} {← ppRM s}, {ppReg d}"
  | .lea d a => do return s!"lea{sfx w} {← ppAddr a}, {ppReg d}"
  | .add d s => do return s!"add{sfx w} {← ppOperand s}, {← ppRM d}"
  | .sub d s => do return s!"sub{sfx w} {← ppOperand s}, {← ppRM d}"
  | .and d s => do return s!"and{sfx w} {← ppOperand s}, {← ppRM d}"
  | .or d s => do return s!"or{sfx w} {← ppOperand s}, {← ppRM d}"
  | .xor d s => do return s!"xor{sfx w} {← ppOperand s}, {← ppRM d}"
  | .cmp a b => do return s!"cmp{sfx w} {← ppOperand b}, {← ppRM a}"
  | .test a b => do return s!"test{sfx w} {← ppOperand b}, {← ppRM a}"
  | .mul s => do return s!"mul{sfx w} {← ppRM s}"
  | .imul none s1 s2 => do return s!"imul{sfx w} {← ppOperand s2}, {← ppRM s1}"
  | .neg d => do return s!"neg{sfx w} {← ppRM d}"
  | .not d => do return s!"not{sfx w} {← ppRM d}"
  | .shl d c => do return s!"shl{sfx w} {← ppShift c}, {← ppRM d}"
  | .shr d c => do return s!"shr{sfx w} {← ppShift c}, {← ppRM d}"
  | .sar d c => do return s!"sar{sfx w} {← ppShift c}, {← ppRM d}"
  | .tzcnt d s => do return s!"tzcnt{sfx w} {← ppRM s}, {ppReg d}"
  | .jcc cc l => some s!"j{ppCC cc} {l}"
  | .jmp t => do return s!"jmp {← ppTarget t}"
  | .call t => do return s!"call {← ppTarget t}"
  | .ret => some "ret"
  | .xchg r m => do return s!"xchg{sfx w} {ppReg r}, {← ppRM m}"
  | .xadd lock d s => do
    return (if lock then "lock " else "") ++ s!"xadd{sfx w} {ppReg s}, {← ppRM d}"
  | .mfence => some "mfence"
  | .div s => do return s!"div{sfx w} {← ppRM s}"
  | .idiv s => do return s!"idiv{sfx w} {← ppRM s}"
  | .cqo => match w with
    | .W64 => some "cqto" | .W32 => some "cltd" | .W16 => some "cwtd" | _ => none
  | .popcnt d s => do return s!"popcnt{sfx w} {← ppRM s}, {ppReg d}"
  | .syscall => some "syscall"
  | .ud2 => some "ud2"
  | .nop 1 => some "nop"
  -- Exactly one operand is the `%fs`-relative memory operand.
  | .movfs (.reg r) (.regOrMem (.mem a)) => do return s!"mov{sfx w} {← ppFsAddr a}, {ppReg r}"
  | .movfs (.mem a) (.regOrMem (.reg r)) => do return s!"mov{sfx w} {ppReg r}, {← ppFsAddr a}"
  | .movfs (.mem a) (.imm c) => do return s!"mov{sfx w} ${← ppConst c}, {← ppFsAddr a}"
  | _ => none

/-- A directive as one line of text (without indentation), for the forms
`ppOp` covers, with 64-bit addresses. -/
def ppDirective : Directive → Option String
  | .label l => some (l ++ ":")
  | .instr (.regular .W64 _ op) => ppOp op
  | _ => none

/-! ## Building directives -/

/-- An operation as a directive, with 64-bit addresses. -/
def op {w : _root_.Width} (o : Operation w) : Directive := .instr (.regular .W64 w o)
def i64 := @op .W64
def i32 := @op .W32
def i16 := @op .W16
def i8 := @op .W8

/-- `d(%b)`. -/
def mem (b : Reg64) (d : Int := 0) : AddrExpr :=
  { base := some (.reg b), idx := none, disp := .int64 (Int64.ofInt d) }
/-- `sym(%rip)`, as the parser reads it. -/
def ripSym (l : String) : AddrExpr :=
  { base := some .rip, idx := none, disp := .sub (.label l) .after_current_instruction }
/-- A register destination or source of width `w`. -/
def xr {w : _root_.Width} (r : Reg64) : RegOrMem w := .reg (.low r w)
def xm {w : _root_.Width} (a : AddrExpr) : RegOrMem w := .mem a
def or_ {w : _root_.Width} (r : Reg64) : _root_.Operand w := .regOrMem (.reg (.low r w))
def om {w : _root_.Width} (a : AddrExpr) : _root_.Operand w := .regOrMem (.mem a)
def oi {w : _root_.Width} (n : Int) : _root_.Operand w := .imm (.int64 (Int64.ofInt n))
def lw (r : Reg64) (w : _root_.Width) : _root_.Reg w := .low r w
/-- A direct jump or call target. -/
def rel (l : String) : RelRegOrMem := .rel (.sub (.label l) .after_current_instruction)

/-! ## Whole files -/

/-- An item of an emitted assembler file. -/
inductive Item
  /-- A Kraken directive: an instruction or a label. -/
  | d (_ : Directive)
  /-- An assembler directive line (first non-blank character `.`, no `:`),
  which `stripDirectives` removes. -/
  | dir (_ : String)
  /-- An instruction line in a form Kraken's x64 syntax lacks, copied
  verbatim (Kraken's parser rejects it). -/
  | raw (_ : String)
  /-- A full-line `#` comment. -/
  | comment (_ : String)
  /-- An empty line. -/
  | blank
  deriving Inhabited

/-- A directive line: `stripDirectives` removes it. -/
def dirOk (s : String) : Bool :=
  (s.trimAsciiStart.toString.startsWith ".") && !(s.any (· == ':')) && !(s.any (· == '\n'))

/-- A raw instruction line: one line, not a comment, and not removed by
`stripDirectives`. -/
def rawOk (s : String) : Bool :=
  let t := s.trimAsciiStart.toString
  !t.isEmpty && !(t.startsWith ".") && !(t.startsWith "#") && !(s.any (· == '\n'))

/-- The line of an item (without the newline), or `none` if the item is not
printable: a directive outside `ppDirective`'s range, a malformed directive
or raw line. -/
def Item.line? : Item → Option String
  | .d (.label l) => some (l ++ ":")
  | .d x => ("\t" ++ ·) <$> ppDirective x
  | .dir s => if dirOk s then some ("\t" ++ s.trimAsciiStart.toString) else none
  | .raw s => if rawOk s then some ("\t" ++ s.trimAsciiStart.toString) else none
  | .comment s => some ("\t# " ++ s.map (fun c => if c == '\n' || c == '\r' then ' ' else c))
  | .blank => some ""

/-- Render an item list as an assembler file, or report the first item that
is not printable. -/
def render (items : List Item) : Except String String := do
  let mut out : Array String := #[]
  for it in items do
    match it.line? with
    | some l => out := out.push l
    | none =>
      let what := match it with
        | .d x => s!"{repr x}" | .dir s => s | .raw s => s | .comment s => s | .blank => ""
      throw s!"scc (x64): unprintable item: {what}"
  return String.join (out.toList.map (· ++ "\n"))

/-- The Kraken program of an item list: everything but the Kraken directives
dropped. -/
def directives (items : List Item) : Program :=
  items.filterMap fun | .d x => some x | _ => none

/-- The raw instruction lines of an item list. -/
def rawLines (items : List Item) : List String :=
  items.filterMap fun | .raw s => some s.trimAsciiStart.toString | _ => none

/-- What a certificate does with emitted text: Kraken's parser after
`stripDirectives`. -/
def reparse (text : String) : Except String Program :=
  Kraken.X64.Parser.parse (Kraken.X64.Parser.stripDirectives text)

/-- The round trip of one item: a Kraken directive reads back as itself, a
directive line, comment or blank line as nothing. Raw lines do not round-trip
(`false`). -/
def Item.roundTrips (it : Item) : Bool :=
  match it, it.line? with
  | .raw _, _ => false
  | _, none => false
  | .d x, some l => match reparse l with
    | .ok [y] => decide (y = x)
    | _ => false
  | _, some l => match reparse l with
    | .ok [] => true
    | _ => false

/-- The round trip of a whole file without its raw lines: the re-parse of
the rendered text is the item list's Kraken program. -/
def roundTripsWithoutRaw (items : List Item) : Bool :=
  let kept := items.filter fun | .raw _ => false | _ => true
  match render kept with
  | .error _ => false
  | .ok text => match reparse text with
    | .ok p => decide (p = directives items)
    | .error _ => false

end Scc.Emit.X64

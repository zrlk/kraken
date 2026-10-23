/-
AArch64 GNU assembler printer for `scc`.

This module turns Kraken's AArch64 syntax (`Directive`/`Program` of
`Kraken/AArch64/Syntax.lean`) into GNU `as` text, and wraps it into a whole
assembler file together with the lines that Kraken's syntax cannot represent
(section and symbol directives and data).

**Round trip.** The printer is not trusted: a certificate re-parses the text
with Kraken's own parser (`Kraken.AArch64.Parser.parse` after
`stripDirectives`). For the *canonical* forms (the ones the emitter produces:
see `Scc/Emit/A64Test.lean`, which checks each of them) the round trip is the
identity:

  `reparse (render items) = .ok (directives items)`.

Forms that the parser normalises (e.g. an `ADD_e` with an unshifted register
operand and no `SP`, which the parser reads as `ADD_s`; a `NOP` at width
`W32`; `STLR` with a size that differs from the register width) are printed
faithfully but do not round-trip; the emitter avoids them.

**Raw lines.** An `Item.raw` line is copied verbatim. It must be a directive
line (first non-blank character `.`) without a `:` so that `stripDirectives`
removes it; `Item.rawOk` checks this, and `render` refuses (returns an error)
otherwise. Raw lines are therefore *invisible* to the re-parsed program; the
emitter uses them only for assembler directives (sections, symbols, data),
never for instructions: `svc`, `mrs` and `msr` of `TPIDR_EL0` are Kraken
`Operation`s (`SVC`, `MRS`, `MSR`, `Kraken/SYSCALL.md`).
-/
import Kraken.AArch64.Parser

namespace Scc.Emit.A64

/-! ## Registers -/

/-- The architectural number of a general purpose register (`X0` = 0, ...). -/
def xregNum (r : XReg) : Nat := r.ctorIdx

/-- `x<n>` or `w<n>`. -/
def regName (w : RegWidth) (n : Nat) : String :=
  (match w with | .W64 => "x" | .W32 => "w") ++ toString n

def ppXRegOrSp (w : RegWidth) : XRegOrSp → String
  | .reg r => regName w (xregNum r)
  | .SP => match w with | .W64 => "sp" | .W32 => "wsp"

def ppXRegOrZr (w : RegWidth) : XRegOrXzr → String
  | .reg r => regName w (xregNum r)
  | .XZR => match w with | .W64 => "xzr" | .W32 => "wzr"

def ppSp {w : RegWidth} : RegOrSp w → String
  | .low r _ => ppXRegOrSp w r

def ppZr {w : RegWidth} : RegOrZr w → String
  | .low r _ => ppXRegOrZr w r

/-- The zero register `XZR`/`WZR`. -/
def isZero {w : RegWidth} : RegOrZr w → Bool
  | .low .XZR _ => true
  | _ => false

/-! ## Constants and operands -/

/-- A constant expression. Integers are printed in signed decimal (the parser
reads values above `2^63` back as the same `Int64`). The `.`-relative forms and
`add`/`sub` are printed for completeness only: Kraken's parser does not read
them, and the emitter never produces them. -/
def ppConst : ConstExpr → String
  | .label l => l
  | .int64 i => toString i.toInt
  | .before_current_instruction => "."
  | .after_current_instruction => "(.+4)"
  | .add a b => s!"({ppConst a}+{ppConst b})"
  | .sub a b => s!"({ppConst a}-{ppConst b})"
  | .pg_hi21 e => ":pg_hi21:" ++ ppConst e
  | .lo12 e => ":lo12:" ++ ppConst e

/-- An immediate operand: `#n` for an integer, the bare expression otherwise
(`:lo12:sym`, `sym`). -/
def ppImm : ConstExpr → String
  | .int64 i => "#" ++ toString i.toInt
  | e => ppConst e

def ppExtendType : ExtendType → String
  | .UXTB => "uxtb" | .SXTB => "sxtb" | .UXTH => "uxth" | .SXTH => "sxth"
  | .UXTW => "uxtw" | .SXTW => "sxtw" | .UXTX => "uxtx" | .SXTX => "sxtx"

def extendAmountNat : ExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3 | .E4 => 4

def memExtendAmountNat : MemExtendAmount → Nat
  | .E0 => 0 | .E1 => 1 | .E2 => 2 | .E3 => 3

/-- The second operand of `ADD_e`-style instructions. The extension of a
register operand is always printed, so that the parser does not read it as a
shifted register. -/
def ppExtOrImm : ExtOrImmReg → String
  | .imm ⟨c, .S0⟩ => ppImm c
  | .imm ⟨c, .S12⟩ => ppImm c ++ ", lsl #12"
  | .ext ⟨⟨_, r⟩, ⟨t, a⟩⟩ =>
    ppZr r ++ ", " ++ ppExtendType t ++
      (match a with | .E0 => "" | a => " #" ++ toString (extendAmountNat a))

def ppShiftType : ShiftType → String
  | .LSL => "lsl" | .LSR => "lsr" | .ASR => "asr" | .ROR => "ror"

/-- A shifted register operand; the default `lsl #0` is omitted. -/
def ppShiftReg {w : RegWidth} (s : ShiftRegExpr w) : String :=
  if s.shift == .LSL && s.amount == 0 then ppZr s.reg
  else ppZr s.reg ++ ", " ++ ppShiftType s.shift ++ " #" ++ toString s.amount.toInt

/-- A load/store address. -/
def ppAddr (a : AddrExpr) : String :=
  let b := ppSp a.base
  match a.off with
  | .imm ⟨c, none⟩ => if c == .int64 0 then s!"[{b}]" else s!"[{b}, {ppImm c}]"
  | .imm ⟨c, some .Pre⟩ => s!"[{b}, {ppImm c}]!"
  | .imm ⟨c, some .Post⟩ => s!"[{b}], {ppImm c}"
  | .reg ⟨⟨_, r⟩, ⟨t, amt⟩⟩ =>
    let n := memExtendAmountNat amt
    let ext := match t with
      | .UXTX => if n == 0 then "" else s!", lsl #{n}"
      | .SXTX => if n == 0 then ", sxtx" else s!", sxtx #{n}"
      | .UXTW => if n == 0 then ", uxtw" else s!", uxtw #{n}"
      | .SXTW => if n == 0 then ", sxtw" else s!", sxtw #{n}"
    s!"[{b}, {ppZr r}{ext}]"

def ppUnscaled (a : UnscaledAddrExpr) : String :=
  if a.imm == .int64 0 then s!"[{ppSp a.base}]" else s!"[{ppSp a.base}, {ppImm a.imm}]"

def ppAddrOrLit : AddrOrLit → String
  | .addr a => ppAddr a
  | .lit (.addr ⟨l⟩) => l
  | .lit (.pool ⟨e⟩) => "=" ++ ppConst e

def ppBase (b : RegOrSp .W64) : String := s!"[{ppSp b}]"

def ppCond : CondCode → String
  | .EQ => "eq" | .NE => "ne" | .CS => "hs" | .CC => "lo" | .MI => "mi" | .PL => "pl"
  | .VS => "vs" | .VC => "vc" | .HI => "hi" | .LS => "ls" | .GE => "ge" | .LT => "lt"
  | .GT => "gt" | .LE => "le" | .AL => "al" | .NV => "nv"

def ppMovShift {w : RegWidth} (s : MovShift w) : String :=
  if s.toNat == 0 then "" else s!", lsl #{s.toNat}"

/-! ## Mnemonic suffixes of the ordered and atomic forms -/

/-- `B`/`H` size suffix (`""` for word/doubleword). -/
def sizeSuffix : MemWidth → String
  | .W8 => "b" | .W16 => "h" | .W32 | .W64 => ""

/-- `A`/`L`/`AL` ordering suffix. -/
def rmwSuffix : Kraken.RmwKind → String
  | .plain => "" | .acq => "a" | .rel => "l" | .acqRel => "al"

def atomicOpName : AtomicOp → String
  | .ADD => "add" | .CLR => "clr" | .EOR => "eor" | .SET => "set"
  | .SMAX => "smax" | .SMIN => "smin" | .UMAX => "umax" | .UMIN => "umin"

/-- The base mnemonic of an `LDAR`-family load. `(plain, false)` has no
mnemonic of its own; it is printed as `ldar` and does not round-trip. -/
def ldarMnemonic : Kraken.LoadKind → Bool → String
  | .acq, false => "ldar"
  | .acqPc, false => "ldapr"
  | .plain, true => "ldxr"
  | .acq, true => "ldaxr"
  | .acqPc, true => "ldaxr"
  | .plain, false => "ldar"

def stxrMnemonic : Kraken.StoreKind → String
  | .rel => "stlxr"
  | _ => "stxr"

def ldxpMnemonic : Kraken.LoadKind → String
  | .plain => "ldxp"
  | _ => "ldaxp"

/-- Barrier option, inner shareable (the domain is not modelled). -/
def barrierOption : Kraken.FenceKind → String
  | .sy => "ish" | .ld => "ishld" | .st => "ishst" | .stAll => "ishst" | .isb => "sy"

/-- A system register name. -/
def ppSysReg : SysReg → String
  | .TPIDR_EL0 => "tpidr_el0"

/-! ## Instructions -/

/-- `mnemonic` followed by its comma-separated operands. -/
def insn (mn : String) (ops : List String) : String :=
  if ops.isEmpty then mn else mn ++ " " ++ ", ".intercalate ops

/-- Print one operation in GNU syntax, in the base (non-alias) form wherever
Kraken's parser accepts it. -/
def ppOperation {w : RegWidth} : Operation w → String
  | .LDR d s => insn "ldr" [ppZr d, ppAddrOrLit s]
  | .STR s d => insn "str" [ppZr s, ppAddr d]
  | .LDUR d s => insn "ldur" [ppZr d, ppUnscaled s]
  | .STUR s d => insn "stur" [ppZr s, ppUnscaled d]
  | .LDP d1 d2 s => insn "ldp" [ppZr d1, ppZr d2, ppAddr s]
  | .STP s1 s2 d => insn "stp" [ppZr s1, ppZr s2, ppAddr d]
  | .LDRB d s => insn "ldrb" [ppZr d, ppAddr s]
  | .LDURB d s => insn "ldurb" [ppZr d, ppUnscaled s]
  | .STRB s d => insn "strb" [ppZr s, ppAddr d]
  | .STURB s d => insn "sturb" [ppZr s, ppUnscaled d]
  | .LDRSB d s => insn "ldrsb" [ppZr d, ppAddr s]
  | .LDURSB d s => insn "ldursb" [ppZr d, ppUnscaled s]
  | .LDRH d s => insn "ldrh" [ppZr d, ppAddr s]
  | .LDURH d s => insn "ldurh" [ppZr d, ppUnscaled s]
  | .STRH s d => insn "strh" [ppZr s, ppAddr d]
  | .STURH s d => insn "sturh" [ppZr s, ppUnscaled d]
  | .LDRSH d s => insn "ldrsh" [ppZr d, ppAddr s]
  | .LDURSH d s => insn "ldursh" [ppZr d, ppUnscaled s]
  | .LDRSW d s => insn "ldrsw" [ppZr d, ppAddrOrLit s]
  | .LDURSW d s => insn "ldursw" [ppZr d, ppUnscaled s]
  | .LDPSW d1 d2 s => insn "ldpsw" [ppZr d1, ppZr d2, ppAddr s]
  | .ADD_e d s1 s2 => insn "add" [ppSp d, ppSp s1, ppExtOrImm s2]
  | .ADD_s d s1 s2 => insn "add" [ppZr d, ppZr s1, ppShiftReg s2]
  -- With the zero register as destination, the flag-setting `_e` forms are
  -- printed as `cmn`/`cmp`: the parser reads `adds xzr, …`/`subs xzr, …` as
  -- the shifted-register form only.
  | .ADDS_e d s1 s2 =>
    if isZero d then insn "cmn" [ppSp s1, ppExtOrImm s2]
    else insn "adds" [ppZr d, ppSp s1, ppExtOrImm s2]
  | .ADDS_s d s1 s2 => insn "adds" [ppZr d, ppZr s1, ppShiftReg s2]
  | .SUB_e d s1 s2 => insn "sub" [ppSp d, ppSp s1, ppExtOrImm s2]
  | .SUB_s d s1 s2 => insn "sub" [ppZr d, ppZr s1, ppShiftReg s2]
  | .SUBS_e d s1 s2 =>
    if isZero d then insn "cmp" [ppSp s1, ppExtOrImm s2]
    else insn "subs" [ppZr d, ppSp s1, ppExtOrImm s2]
  | .SUBS_s d s1 s2 => insn "subs" [ppZr d, ppZr s1, ppShiftReg s2]
  | .ADC d s1 s2 => insn "adc" [ppZr d, ppZr s1, ppZr s2]
  | .ADCS d s1 s2 => insn "adcs" [ppZr d, ppZr s1, ppZr s2]
  | .SBC d s1 s2 => insn "sbc" [ppZr d, ppZr s1, ppZr s2]
  | .SBCS d s1 s2 => insn "sbcs" [ppZr d, ppZr s1, ppZr s2]
  | .SDIV d s1 s2 => insn "sdiv" [ppZr d, ppZr s1, ppZr s2]
  | .UDIV d s1 s2 => insn "udiv" [ppZr d, ppZr s1, ppZr s2]
  | .MADD d s1 s2 s3 => insn "madd" [ppZr d, ppZr s1, ppZr s2, ppZr s3]
  | .MSUB d s1 s2 s3 => insn "msub" [ppZr d, ppZr s1, ppZr s2, ppZr s3]
  | .SMULH d s1 s2 => insn "smulh" [ppZr d, ppZr s1, ppZr s2]
  | .UMULH d s1 s2 => insn "umulh" [ppZr d, ppZr s1, ppZr s2]
  | .SMADDL d s1 s2 s3 => insn "smaddl" [ppZr d, ppZr s1, ppZr s2, ppZr s3]
  | .UMADDL d s1 s2 s3 => insn "umaddl" [ppZr d, ppZr s1, ppZr s2, ppZr s3]
  | .SMSUBL d s1 s2 s3 => insn "smsubl" [ppZr d, ppZr s1, ppZr s2, ppZr s3]
  | .UMSUBL d s1 s2 s3 => insn "umsubl" [ppZr d, ppZr s1, ppZr s2, ppZr s3]
  | .AND_i d s i => insn "and" [ppSp d, ppZr s, ppImm i]
  | .AND_s d s1 s2 => insn "and" [ppZr d, ppZr s1, ppShiftReg s2]
  | .ANDS_i d s i => insn "ands" [ppZr d, ppZr s, ppImm i]
  | .ANDS_s d s1 s2 => insn "ands" [ppZr d, ppZr s1, ppShiftReg s2]
  | .ORR_i d s i => insn "orr" [ppSp d, ppZr s, ppImm i]
  | .ORR_s d s1 s2 => insn "orr" [ppZr d, ppZr s1, ppShiftReg s2]
  | .ORN_s d s1 s2 => insn "orn" [ppZr d, ppZr s1, ppShiftReg s2]
  | .EOR_i d s i => insn "eor" [ppSp d, ppZr s, ppImm i]
  | .EOR_s d s1 s2 => insn "eor" [ppZr d, ppZr s1, ppShiftReg s2]
  | .EON_s d s1 s2 => insn "eon" [ppZr d, ppZr s1, ppShiftReg s2]
  | .BIC_s d s1 s2 => insn "bic" [ppZr d, ppZr s1, ppShiftReg s2]
  | .BICS_s d s1 s2 => insn "bics" [ppZr d, ppZr s1, ppShiftReg s2]
  | .BFM d s r i => insn "bfm" [ppZr d, ppZr s, s!"#{r}", s!"#{i}"]
  | .SBFM d s r i => insn "sbfm" [ppZr d, ppZr s, s!"#{r}", s!"#{i}"]
  | .UBFM d s r i => insn "ubfm" [ppZr d, ppZr s, s!"#{r}", s!"#{i}"]
  | .CLZ d s => insn "clz" [ppZr d, ppZr s]
  | .CLS d s => insn "cls" [ppZr d, ppZr s]
  | .RBIT d s => insn "rbit" [ppZr d, ppZr s]
  | .REV d s => insn "rev" [ppZr d, ppZr s]
  | .REV16 d s => insn "rev16" [ppZr d, ppZr s]
  | .REV32 d s => insn "rev32" [ppZr d, ppZr s]
  | .EXTR d s1 s2 l => insn "extr" [ppZr d, ppZr s1, ppZr s2, s!"#{l}"]
  | .MOVZ d i s => insn "movz" [ppZr d, ppImm i] ++ ppMovShift s
  | .MOVK d i s => insn "movk" [ppZr d, ppImm i] ++ ppMovShift s
  | .MOVN d i s => insn "movn" [ppZr d, ppImm i] ++ ppMovShift s
  | .LSLV d s1 s2 => insn "lslv" [ppZr d, ppZr s1, ppZr s2]
  | .LSRV d s1 s2 => insn "lsrv" [ppZr d, ppZr s1, ppZr s2]
  | .ASRV d s1 s2 => insn "asrv" [ppZr d, ppZr s1, ppZr s2]
  | .RORV d s1 s2 => insn "rorv" [ppZr d, ppZr s1, ppZr s2]
  | .CSEL d s1 s2 c => insn "csel" [ppZr d, ppZr s1, ppZr s2, ppCond c]
  | .CSINC d s1 s2 c => insn "csinc" [ppZr d, ppZr s1, ppZr s2, ppCond c]
  | .CSINV d s1 s2 c => insn "csinv" [ppZr d, ppZr s1, ppZr s2, ppCond c]
  | .CSNEG d s1 s2 c => insn "csneg" [ppZr d, ppZr s1, ppZr s2, ppCond c]
  | .CCMP_reg s1 s2 f c => insn "ccmp" [ppZr s1, ppZr s2, s!"#{f}", ppCond c]
  | .CCMP_imm s1 i f c => insn "ccmp" [ppZr s1, s!"#{i}", s!"#{f}", ppCond c]
  | .CCMN_reg s1 s2 f c => insn "ccmn" [ppZr s1, ppZr s2, s!"#{f}", ppCond c]
  | .CCMN_imm s1 i f c => insn "ccmn" [ppZr s1, s!"#{i}", s!"#{f}", ppCond c]
  | .ADR d t => insn "adr" [ppZr d, ppConst t]
  | .ADRP d t => insn "adrp" [ppZr d, ppConst t]
  | .B t => insn "b" [ppConst t]
  | .B_cond c t => insn ("b." ++ ppCond c) [ppConst t]
  | .BL t => insn "bl" [ppConst t]
  | .BLR t => insn "blr" [ppZr t]
  | .BR t => insn "br" [ppZr t]
  | .RET t => if t == RegOrZr.X30 then "ret" else insn "ret" [ppZr t]
  | .CBZ r t => insn "cbz" [ppZr r, ppConst t]
  | .CBNZ r t => insn "cbnz" [ppZr r, ppConst t]
  | .TBZ r b t => insn "tbz" [ppZr r, s!"#{b}", ppConst t]
  | .TBNZ r b t => insn "tbnz" [ppZr r, s!"#{b}", ppConst t]
  | .LDAR k x sz d b => insn (ldarMnemonic k x ++ sizeSuffix sz) [ppZr d, ppBase b]
  | .STLR sz s b => insn ("stlr" ++ sizeSuffix sz) [ppZr s, ppBase b]
  | .STXR k sz st s b => insn (stxrMnemonic k ++ sizeSuffix sz) [ppZr st, ppZr s, ppBase b]
  | .CAS k sz rs rt b => insn ("cas" ++ rmwSuffix k ++ sizeSuffix sz) [ppZr rs, ppZr rt, ppBase b]
  | .SWP k sz rs rt b => insn ("swp" ++ rmwSuffix k ++ sizeSuffix sz) [ppZr rs, ppZr rt, ppBase b]
  | .LDOP op k sz rs rt b =>
    insn ("ld" ++ atomicOpName op ++ rmwSuffix k ++ sizeSuffix sz) [ppZr rs, ppZr rt, ppBase b]
  | .LDXP k d1 d2 b => insn (ldxpMnemonic k) [ppZr d1, ppZr d2, ppBase b]
  | .STXP k st s1 s2 b => insn (stxrMnemonic k |>.replace "xr" "xp") [ppZr st, ppZr s1, ppZr s2, ppBase b]
  | .CASP k rs1 rs2 rt1 rt2 b =>
    insn ("casp" ++ rmwSuffix k) [ppZr rs1, ppZr rs2, ppZr rt1, ppZr rt2, ppBase b]
  | .DMB k => insn "dmb" [barrierOption k]
  | .DSB k => insn "dsb" [barrierOption k]
  | .ISB => "isb"
  | .NOP => "nop"
  | .SVC imm => insn "svc" [s!"#{imm}"]
  | .MRS d sr => insn "mrs" [ppZr d, ppSysReg sr]
  | .MSR sr src => insn "msr" [ppSysReg sr, ppZr src]

def ppInstr (i : Instr) : String := ppOperation i.operation

/-- Byte arrays have no directive in Kraken's parser; they are printed as
`.byte` lines, which `stripDirectives` removes (so they do not round-trip). -/
def ppBytes (b : ByteArray) : String :=
  "\t.byte " ++ ", ".intercalate (b.toList.map toString)

/-- One directive as one line (without the newline). -/
def ppDirective : Directive → String
  | .instr i => "\t" ++ ppInstr i
  | .label l => l ++ ":"
  | .byteArray b => ppBytes b

/-! ## Labels -/

/-- A label name Kraken's parser reads back (`parseName`): a letter, `_` or
`.`, then letters, digits, `_` or `.`; and not a register name, so that a
label operand cannot be confused with a register.  Register names
(`parseXRegName`, `sp`, `wsp`, `xzr`, `wzr`) have at most three characters,
so longer names skip those lookups (which are slow to evaluate in the
kernel). -/
def labelOk (l : Label) : Bool :=
  match l.toList with
  | [] => false
  | c :: cs =>
    (c.isAlpha || c == '_' || c == '.') &&
    cs.all (fun c => c.isAlphanum || c == '_' || c == '.') &&
    (3 ≤ cs.length ||
      ((Kraken.AArch64.Parser.parseXRegName l).isNone &&
        !(["sp", "wsp", "xzr", "wzr"].contains l.toLower)))

/-! ## Whole files -/

/-- An item of an emitted assembler file: a Kraken directive (instruction or
label), or a raw directive line that Kraken's syntax does not represent. -/
inductive Item
  | d (_ : Directive)
  | raw (_ : String)
  /-- A full-line `//` comment (no code; the parser skips it). -/
  | comment (_ : String)
  deriving Inhabited

/-- The Kraken program of an item list: the raw lines and comments dropped.
This is what the re-parse of the rendered text yields. -/
def directives (items : List Item) : Program :=
  items.filterMap fun | .d x => some x | _ => none

/-- A raw line is a directive line without `:`, so that Kraken's
`stripDirectives` removes it. -/
def rawOk (s : String) : Bool :=
  (s.trimAsciiStart.toString.startsWith ".") && !(s.any (· == ':')) && !(s.any (· == '\n'))

/-- An item is printable so that it round-trips: raw lines satisfy `rawOk`,
labels satisfy `labelOk`, and no byte arrays (they are emitted as raw `.byte`
lines instead). -/
def Item.ok : Item → Bool
  | .raw s => rawOk s
  | .comment _ => true
  | .d (.label l) => labelOk l
  | .d (.byteArray _) => false
  | .d (.instr _) => true

def Item.render : Item → String
  | .raw s => "\t" ++ s.trimAsciiStart.toString
  | .comment s => "\t// " ++ s.map (fun c => if c == '\n' || c == '\r' then ' ' else c)
  | .d x => ppDirective x

/-- Render an item list as an assembler file, or report the first item that
would not round-trip. -/
def render (items : List Item) : Except String String := do
  for it in items do
    unless it.ok do
      throw s!"scc: unprintable item: {it.render}"
  return String.join (items.map fun it => it.render ++ "\n")

/-- What a certificate does with an emitted file: Kraken's parser after
`stripDirectives`. -/
def reparse (text : String) : Except String Program :=
  Kraken.AArch64.Parser.parse (Kraken.AArch64.Parser.stripDirectives text)

/-- The round-trip check for an item list (decidable equality of programs). -/
def roundTrips (items : List Item) : Bool :=
  match render items with
  | .error _ => false
  | .ok text =>
    match reparse text with
    | .ok p => decide (p = directives items)
    | .error _ => false

end Scc.Emit.A64

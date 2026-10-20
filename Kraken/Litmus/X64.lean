/-
Running an x86 litmus test on the Promising machine under the TSO profile.

herd's `X86_64` tests are in AT&T syntax, which Kraken's x64 parser reads
directly. herd's older 32-bit `X86` dialect (`MOV [x],$1`, `MOV EAX,[y]`,
`XCHG [x],EAX`, `MFENCE`) is rewritten to AT&T here.

Symbolic data locations appear in code (`movl $1,(x)`), so each thread's
executable carries, after its instructions, a padding block up to each
location followed by a `label x`: Kraken's `Executable.labels` then resolves
the symbol to the address this harness chose.
-/
import Kraken.X64.Parser
import Kraken.Promising.X64
import Kraken.Litmus.Syntax
import Kraken.Litmus.Program
import Kraken.Litmus.Layout
import Kraken.Promising.Interactive

namespace Kraken.Litmus.X64

open Kraken.Promising

/-- Symbolic locations, in 256-byte slots, above every thread's code
(`MemLayout`). Untyped tests run in legacy mode: every symbol unsized, as
before typed locations; a test that types a location is sized (see `Layout.lean`). -/
def symBase : Nat := 0x1000000

/-- The type a test declares for a register, if any. -/
def regType (t : Test) (r : ThreadReg) : Option String :=
  t.inits.findSome? fun | .reg r' _ ty => if r' == r then ty else none | _ => none

/-- `rax`, `eax`, `ax`, `al`, … → the 64-bit register. -/
def regOfName (name : String) : Option Reg64 :=
  match name.toLower with
  | "rax" | "eax" | "ax" | "al" | "ah" => some .rax
  | "rbx" | "ebx" | "bx" | "bl" | "bh" => some .rbx
  | "rcx" | "ecx" | "cx" | "cl" | "ch" => some .rcx
  | "rdx" | "edx" | "dx" | "dl" | "dh" => some .rdx
  | "rsi" | "esi" | "si" | "sil" => some .rsi
  | "rdi" | "edi" | "di" | "dil" => some .rdi
  | "rsp" | "esp" | "sp" | "spl" => some .rsp
  | "rbp" | "ebp" | "bp" | "bpl" => some .rbp
  | "r8" | "r8d" | "r8w" | "r8b" => some .r8
  | "r9" | "r9d" | "r9w" | "r9b" => some .r9
  | "r10" | "r10d" | "r10w" | "r10b" => some .r10
  | "r11" | "r11d" | "r11w" | "r11b" => some .r11
  | "r12" | "r12d" | "r12w" | "r12b" => some .r12
  | "r13" | "r13d" | "r13w" | "r13b" => some .r13
  | "r14" | "r14d" | "r14w" | "r14b" => some .r14
  | "r15" | "r15d" | "r15w" | "r15b" => some .r15
  | _ => none

/-- `xmm0` … `xmm31` → the vector register. -/
def xmmOfName (name : String) : Option RegMm :=
  let n := name.toLower
  if n.startsWith "xmm" then
    match (String.ofList (n.toList.drop 3)).toNat? with
    | some i => #[RegMm.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7, .mm8, .mm9, .mm10, .mm11,
        .mm12, .mm13, .mm14, .mm15, .mm16, .mm17, .mm18, .mm19, .mm20, .mm21, .mm22, .mm23,
        .mm24, .mm25, .mm26, .mm27, .mm28, .mm29, .mm30, .mm31][i]?
    | none => none
  else none

/-- Initialise a register (general or `xmm`) of a thread. -/
def initReg (l : MemLayout) (md : MachineData) (r : ThreadReg) (v : Value) : Except String MachineData := do
  let some val := l.valueBits? v | throw s!"bad initial value for {r.tid}:{r.reg}"
  match regOfName r.reg, xmmOfName r.reg with
  | some reg, _ => pure { md with regs := md.regs.set64 reg (val.setWidth 64) }
  | none, some x => pure { md with zmms := md.zmms.set512 x (val.setWidth 512) }
  | none, none => throw s!"unknown register {r.reg}"

/-- The value of a register observable, and its default presentation: a
general register as signed 64 bits (a 32-bit name observes the low half), an
`xmm` register as unsigned 128 bits (herd has no vector registers; this
prints the register as one number, the low lane in the low bits). -/
def regValue (md : MachineData) (reg : String) : BitVec 128 × (Nat × Bool) :=
  match regOfName reg, xmmOfName reg with
  | some r, _ =>
    let v := md.regs.get64 r
    -- a 32-bit register name observes the low half
    let v := if reg.length == 3 && reg.toLower.startsWith "e" then v.setWidth 32 |>.setWidth 64 else v
    (v.setWidth 128, (64, true))
  | none, some x => ((md.zmms.get512 x).setWidth 128, (128, false))
  | none, none => (0, (64, true))

/-- The default presentation of a register observable (`regValue`). -/
def regDefault (reg : String) : Nat × Bool :=
  if (xmmOfName reg).isSome then (128, false) else (64, true)

/-! ## The 32-bit `X86` dialect -/

namespace X86Dialect

def trim (s : String) : String := s.trimAscii.copy

/-- An operand of the `X86` dialect to AT&T: `[x]` → `(x)`, `$1` → `$1`,
`EAX` → `%eax`, `1` → `$1`. -/
def operand (o : String) : String :=
  let o := trim o
  if o.startsWith "[" then s!"({String.ofList (o.toList.drop 1).dropLast})"
  else if o.startsWith "$" then o
  else if o.toList.all Char.isDigit then s!"${o}"
  else s!"%{o.toLower}"

/-- One `X86` instruction line to AT&T. Destination-first to source-first,
`l` suffix for 32-bit operations. -/
def line (l : String) : String :=
  let l := trim l
  if l.endsWith ":" then l else
  let (lock, l) := if l.toUpper.startsWith "LOCK " then (true, trim (String.ofList (l.toList.drop 5))) else (false, l)
  let ws := l.splitOn " " |>.filter (· ≠ "")
  match ws with
  | [] => l
  | m :: rest =>
    let m := m.toLower
    let ops := (" ".intercalate rest).splitOn "," |>.filter (fun o => !(trim o).isEmpty) |>.map operand
    let suffix := if m ∈ ["mfence", "lfence", "sfence", "nop"] then "" else "l"
    let att := match ops with
      | [] => s!"{m}{suffix}"
      | [a] => s!"{m}{suffix} {a}"
      | [a, b] => s!"{m}{suffix} {b},{a}"   -- dst, src → src, dst
      | _ => l
    let att := if m.startsWith "j" then s!"{m} {" ".intercalate rest}" else att
    if lock then s!"lock {att}" else att

end X86Dialect

structure Prepared where
  config : Config Promising.X64.isa
  layout : MemLayout

/-- Lay out and initialise the test. -/
def prepare (t : Test) : Except String Prepared := do
  let isX86 := t.arch == "X86"
  -- symbolic locations: every symbol mentioned anywhere, including bare
  -- `(x)` operands in the code
  let codeSyms := t.threads.flatMap fun lines => lines.flatMap fun l =>
    (l.splitOn "(").drop 1 |>.filterMap fun part =>
      let name := String.ofList (part.toList.takeWhile fun c => c.isAlphanum || c == '_')
      if name.isEmpty || name.toList.all Char.isDigit || name.startsWith "%" then none else some name
  let x86Syms := if isX86 then t.threads.flatMap fun lines => lines.flatMap fun l =>
      (l.splitOn "[").drop 1 |>.filterMap fun part =>
        let name := String.ofList (part.toList.takeWhile fun c => c.isAlphanum || c == '_')
        if name.isEmpty then none else some name
    else []
  let syms := (t.inits.flatMap fun
      | .loc x v _ => x :: (match v with | .sym y => [y] | _ => [])
      | .reg _ v _ => (match v with | .sym y => [y] | _ => []))
    ++ t.observables.filterMap (fun | .loc x => some x | _ => none)
    ++ codeSyms ++ x86Syms
  let layout ← MemLayout.build symBase t syms
  let initMem ← layout.initMem t
  let decls := layout.decls initMem
  let states ← t.threads.mapIdxM fun tid lines => do
    let lines := if isX86 then lines.map X86Dialect.line else lines
    let prog ← match Kraken.X64.Parser.parse ("\n".intercalate lines) with
      | .ok p => pure p
      | .error e => throw s!"P{tid}: {e} (in: {lines})"
    let base : Int64 := Int64.ofNat (0x100000 * (tid + 1))
    -- instruction sizes: 1 byte each (the layout is fake; only distinctness matters)
    let codeCells : List (Directive × Nat) := prog.map fun d => (d, match d with | .label _ => 0 | _ => 1)
    let codeLen := (codeCells.map (·.2)).sum
    let endPc := base + Int64.ofNat codeLen
    -- data labels: pad up to each symbol's address
    let pad (n : Nat) : Directive × Nat := (.byteArray (.mk #[]), n)
    let (cells, _) := layout.syms.foldl (init := (codeCells, base.toBitVec.toNat + codeLen)) fun (cells, cur) x =>
      (cells ++ [pad (x.addr.toNat - cur), (.label x.name, 0)], x.addr.toNat)
    let exe : _root_.Executable := (base, cells)
    let mut md : MachineData := {}
    for i in t.inits do
      if let .reg r v _ := i then
        if r.tid == tid then md ← initReg layout md r v
    let st : MachineState := (md, base)
    let texts := (prog.zip lines).filterMap fun (d, l) => match d with | .label _ => none | _ => some l
    let showPc (pc : Int64) : String :=
      texts[(pc - base).toBitVec.toNat]?.getD s!"pc={pc}"
    pure ({ exe, endPc, st, showPc, decls } : Promising.X64.State)
  return { config := Config.init states initMem, layout }

def project (t : Test) (l : MemLayout) (c : Config Promising.X64.isa) : FinalState :=
  t.observables.map fun o => (o, match o with
    | .reg r => match c.threads[r.tid]? with
      | some th => let (v, dflt) := regValue th.st.st.1 r.reg; l.present (regType t r) dflt v
      | none => .num 0
    | .loc x => l.finalLoc c.mem x)

/-- Lay out and initialise a `.kl` program (see the AArch64 runner); data
symbols in the code resolve through labels placed after it. -/
def prepareProgram (p : Program) : Except String Prepared := do
  let t := p.toTest
  let codeSyms := p.code.flatMap fun l =>
    (l.splitOn "(").drop 1 |>.filterMap fun part =>
      let name := String.ofList (part.toList.takeWhile fun c => c.isAlphanum || c == '_')
      if name.isEmpty || name.toList.all Char.isDigit || name.startsWith "%" then none else some name
  let syms := (t.inits.flatMap fun
      | .loc x v _ => x :: (match v with | .sym y => [y] | _ => [])
      | .reg _ v _ => (match v with | .sym y => [y] | _ => []))
    ++ t.observables.filterMap (fun | .loc x => some x | _ => none) ++ codeSyms
  let layout ← MemLayout.build symBase t syms
  let initMem ← layout.initMem t
  let decls := layout.decls initMem
  let prog ← match Kraken.X64.Parser.parse ("\n".intercalate p.code) with
    | .ok pr => pure pr
    | .error e => throw s!"code: {e}"
  let base : Int64 := Int64.ofNat 0x100000
  let codeCells : List (Directive × Nat) := prog.map fun d => (d, match d with | .label _ => 0 | _ => 1)
  let codeLen := (codeCells.map (·.2)).sum
  let pad (n : Nat) : Directive × Nat := (.byteArray (.mk #[]), n)
  let (cells, _) := layout.syms.foldl (init := (codeCells, base.toBitVec.toNat + codeLen)) fun (cells, cur) x =>
    (cells ++ [pad (x.addr.toNat - cur), (.label x.name, 0)], x.addr.toNat)
  let exe : _root_.Executable := (base, cells)
  let labels := _root_.Executable.labels exe
  let texts := (prog.zip p.code).filterMap fun (d, l) => match d with | .label _ => none | _ => some l
  let showPc (pc : Int64) : String := texts[(pc - base).toBitVec.toNat]?.getD s!"pc={pc}"
  let states ← p.threads.mapM fun th => do
    let entry := labels.label th.entry
    let exit := labels.label th.exit
    if entry == -1 then throw s!"P{th.tid}: unknown entry label {th.entry}"
    if exit == -1 then throw s!"P{th.tid}: unknown exit label {th.exit}"
    let mut md : MachineData := {}
    if p.stack > 0 then
      let bottom : BitVec 64 := BitVec.ofNat 64 (0x200000 + th.tid * 0x10000)
      md := { md with dmem := Mem.storeBytes md.dmem bottom (List.replicate p.stack 0),
                      regs := md.regs.set64 .rsp (bottom + BitVec.ofNat 64 p.stack) }
    for i in t.inits do
      if let .reg r v _ := i then
        if r.tid == th.tid then md ← initReg layout md r v
    pure ({ exe, endPc := exit, st := (md, entry), showPc, decls } : Promising.X64.State)
  return { config := Config.init states initMem, layout }

/-- Location names for traces and the stepper. -/
def locNamer (l : MemLayout) (loc : Loc) : String := l.nameAt loc.addr

structure Result where
  report : String
  /-- The test's expectation holds (`Ok`). -/
  ok : Bool
  configs : Nat
  boundHit : Bool
  faults : List String
  /-- A witness trace per final state, with whether the state satisfies the condition. -/
  witnesses : List (FinalState × Bool × String)

/-- herd prints x86 registers in lower case whatever the test wrote. -/
def lowerRegs (t : Test) : Test :=
  let lo : Obs → Obs | .reg r => .reg { r with reg := r.reg.toLower } | o => o
  let rec loC : Cond → Cond
    | .eq o v => .eq (lo o) v | .not c => .not (loC c) | .and a b => .and (loC a) (loC b)
    | .or a b => .or (loC a) (loC b) | .true => .true
  { t with cond := loC t.cond, locations := t.locations.map lo,
           inits := t.inits.map fun | .reg r v ty => .reg { r with reg := r.reg.toLower } v ty | i => i }

def runPrepared (t : Test) (p : Prepared) (kind : Option String) (o : ExploreOpts) : Result :=
  let r := explore (I := Promising.X64.isa) Arch.tso p.config (project t p.layout) o
  let norm (o : Obs) (v : Value) : Value := match o, v with
    | .reg r, .num n => p.layout.present (regType t r) (regDefault r.reg) (BitVec.ofInt 128 n)
    | .loc x, v => p.layout.normLoc x v
    | _, v => v
  let env (s : FinalState) (o : Obs) : Option Value := (s.find? (·.1 == o)).map (·.2)
  -- "interesting" states: witnesses of an `exists`, violations of a `forall`/`~exists`
  let witnesses := r.witnesses.map fun (st, tr) =>
    let hit := t.cond.eval (env st) norm
    (st, (if t.quant == .forall then !hit else hit), formatTrace (locNamer p.layout) tr)
  { report := report t r.finals kind norm, ok := verdict t r.finals norm,
    configs := r.configs, boundHit := r.boundHit,
    faults := r.faults.eraseDups, witnesses }

/-- Interactive stepping of a test or program. -/
def interact (p : Prepared) (o : ExploreOpts) : IO Unit :=
  interactive (I := Promising.X64.isa) Arch.tso o (locNamer p.layout) p.config

/-- A mixed-size access makes the test unsupported, as herd rejects it
("Illegal mixed-size test") unless run with `-variant mixed`. -/
def checkMixed (r : Result) : Except String Result :=
  match r.faults.find? (·.startsWith "mixed-size access") with
  | some m => throw s!"unsupported: {m}"
  | none => pure r

def prepareAny (t : Test) : Except String Prepared := prepare t

def run (t : Test) (kind : Option String := none) (o : ExploreOpts := {}) : Except String Result := do
  let t := if t.arch == "X86_64" then lowerRegs t else t
  let p ← prepare t
  checkMixed (runPrepared t p kind o)

def runProgram (p : Program) (kind : Option String := none) (o : ExploreOpts := {}) : Except String Result := do
  let t := lowerRegs p.toTest
  let p := { p with inits := t.inits, cond := t.cond, locations := t.locations }
  let pr ← prepareProgram p
  checkMixed (runPrepared p.toTest pr kind o)

/-! ### Tests of sized tests and mixed-size reports -/

private def runSrc (src : String) : String :=
  match Kraken.Litmus.parse src >>= fun t => run t with
  | .ok r => r.report
  | .error e => s!"Unsupported: {e}"

-- A sized test (a typed location) runs in strict mode: an address no
-- symbol names (`x+8`, reached through a register) is its own footprint,
-- and two overlapping footprints there, 4 and 8 bytes, are reported as
-- mixed-size by the explorer (`Machine.overlapFault`).
/-- info: "Unsupported: unsupported: mixed-size access: 8 bytes at 0x0000000001000108 overlaps the location of 4 bytes at 0x0000000001000108" -/
#guard_msgs in
#eval runSrc "X86_64 T\n{ int64_t y; 0:rax=x; 1:rax=x; }\n P0 | P1 ;\n movl $1,8(%rax) | movq 8(%rax),%rbx ;\nexists (1:rbx=1)"

-- The same untyped is legacy: both accesses reach one unsized location.
/-- info: "Test T Allowed\nStates 2\n1:rbx=0;\n1:rbx=1;\nOk\nWitnesses\nPositive: 1 Negative: 1\nCondition exists (1:rbx=1)\nObservation T Sometimes 1 1\n" -/
#guard_msgs in
#eval runSrc "X86_64 T\n{ 0:rax=x; 1:rax=x; }\n P0 | P1 ;\n movl $1,8(%rax) | movq 8(%rax),%rbx ;\nexists (1:rbx=1)"

-- A declared width is enforced: a 4-byte access to an `int64_t` location.
/-- info: "Unsupported: unsupported: mixed-size access: 4 bytes at 0x0000000001000000, declared 8 bytes" -/
#guard_msgs in
#eval runSrc "X86_64 T\n{ int64_t x; }\n P0 ;\n movl $1,(x) ;\nexists (x=1)"

-- `xmm` registers in the init block, the condition and `locations`; a
-- 128-bit location and literal.
/-- info: "Test T Allowed\nStates 1\n0:xmm1=340282366920938463463374607431768211455; [x]=-1;\nOk\nWitnesses\nPositive: 1 Negative: 0\nCondition exists ([x]=340282366920938463463374607431768211455)\nObservation T Always 1 0\n" -/
#guard_msgs in
#eval runSrc "X86_64 T\n{ int128_t x; 0:xmm0=0xffffffffffffffffffffffffffffffff; }\n P0 ;\n movdqa %xmm0,(x) ;\n movdqa (x),%xmm1 ;\nlocations [0:xmm1;]\nexists (x=0xffffffffffffffffffffffffffffffff)"

end Kraken.Litmus.X64

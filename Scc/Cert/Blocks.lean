import Lean.Data.Json
import Scc.Config
import Scc.Cert.Gen

/-!
# Block data (`scc --blocks`)

`run arch asm` splits scc's assembler listing `asm` into *blocks*: maximal
runs of instructions the block lemmas cover (stack loads and stores,
`push`/`pop`, register operations), ending at a label, at an instruction
the lemmas do not cover, or with a branch. For each block it writes one
`block_spec` command (`Spike/Lib/X64Block.lean`, `Spike/Lib/A64Flow.lean`)
with its function's stack region and the block's static offsets at entry,
and it collects coverage statistics. A block's comment gives its address,
`at L + off`: the label before it, as written in the listing, and the byte
offset of its first instruction from that label (proofs write the node pc
as `lab L + Int64.ofNat off`). x64 cells carry their sizes in bytes, from
the assembler (`Scc.Cert.Sizes.sizesOf`): `(parse("…")).zip [z₁, …]`;
AArch64's are 4 bytes each, and its blocks are plain `parseAArch64("…")`.

Static offsets are the offsets, relative to a base fixed per function, of
the stack pointer and of the registers known to hold a stack address. On
entry the stack pointer is at offset 8 on x64 (the return address is the
cell `[8, 16)`) and 0 on AArch64. Offsets flow along fall-through and
branch edges; at a label they are the meet of all incoming edges (the same
stack pointer, the register offsets every edge agrees on), computed to a
fixpoint, so that a node's offsets hold on every edge into it and the
blocks of a function compose (`Spike/Lib/X64Cfg.lean`,
`Spike/Lib/A64Cfg.lean`). A call keeps the stack pointer and the
callee-saved registers; an instruction outside the blocks forgets the
register it may write.

A function starts at a label the listing declares a function
(`.type NAME, @function` / `%function`), or at the first label (`_start`
has no `.type` on AArch64). Any other label (`.L…`, or a global marker
inside a function such as `scc_rt_release_site`) belongs to the enclosing
function: offsets flow across it.

Each region (one per epoch, below) is `[lo, hi)`: `lo` is the least offset
accessed in it (at most 0) and `hi` the end of the highest accessed cell
(at least 0); on x64 the entry region also holds the saved `%rbp` and the
return address (`[0, 16)`).

Coverage: `covered` counts the instructions in blocks, `uncovered` the
others by reason, and `nodes` those outside blocks that a
single-instruction node lemma covers at known offsets (`flag_nd`,
`Spike/Lib/X64Flags.lean`; `si_nd`, `svc_nd`, `syscall_nd`, `fsld_nd`,
`Spike/Lib/X64Nodes.lean`, `Spike/Lib/A64Nodes.lean`; `dead_nd`,
`Spike/Lib/X64Dead.lean`; the stack switches `sw_nd`, `swand_nd`). A system
call is counted by the number the straight-line code before it sets: `sys`
(no kernel event: `rt_sigaction`, `exit_group`, `futex`, `exit`), `sys,
control only` (`write`, `clone`) or `sys, number after a label`; x64's
`arch_prctl` is not counted. After a stack switch the offsets restart at 0
in a new region with its own `[lo, hi)`: the offsets carry an epoch, and
edges of different epochs meet to unknown. Compiled functions (`wc_*`)
count as `user`, the rest as `runtime`.

The classification reads the listing's text, in the forms scc's printers
(`Scc/Emit/X64Print.lean`, `Scc/Emit/A64Print.lean`) write; it is the
Lean form of the generators that produced the data of
`Spike/Lib/X64Hello.lean` and `Spike/Lib/A64Hello.lean`, and replaces them.
This module imports no ISA.
-/

namespace Scc.Cert.Blocks

open Scc

/-! ## Text -/

/-- `s` without leading and trailing whitespace. -/
def strip (s : String) : String :=
  String.ofList ((s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- `s` without its first `n` characters. -/
def dropN (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- `s` contains `t` (`t` nonempty). -/
def has (s t : String) : Bool := (s.splitOn t).length > 1

/-- The first word of `s` (up to the first whitespace) and the rest after
that whitespace character. -/
def word (s : String) : String × String :=
  let w := s.toList.takeWhile (!·.isWhitespace)
  (String.ofList w, String.ofList (s.toList.drop (w.length + 1)))

/-- The operands after `mn ` when `ins` is `mn ` followed by exactly two
operands separated by `, `. -/
def ops2 (ins mn : String) : Option (String × String) :=
  if ins.startsWith (mn ++ " ") then
    match (dropN ins (mn.length + 1)).splitOn ", " with
    | [a, b] => some (a, b)
    | _ => none
  else none

/-- A decimal integer: `-?[0-9]+`. -/
def int? (s : String) : Option Int :=
  let nat? (l : List Char) : Option Nat :=
    if !l.isEmpty && l.all Char.isDigit then some (String.ofList l).toNat! else none
  match s.toList with
  | '-' :: ds => (nat? ds).map fun n => -(n : Int)
  | ds => (nat? ds).map fun n => (n : Int)

/-- A label: `[.A-Za-z_][A-Za-z0-9_.]*`. -/
def isLab (s : String) : Bool :=
  match s.toList with
  | c :: cs => (c == '.' || c.isAlpha || c == '_') && cs.all fun c => c.isAlphanum || c == '_' || c == '.'
  | [] => false

/-- `[a-z0-9]`. -/
def isLowNum (c : Char) : Bool := c.isLower || c.isDigit

/-- A Lean identifier for a label: every other character as `_`. -/
def ident (s : String) : String :=
  String.map (fun c => if c.isAlphanum || c == '_' then c else '_') s

/-- The functions the listing declares: `.type NAME, @function` (or
`%function`) at the start of a line. -/
def declared (lines : List String) : List String :=
  lines.filterMap fun raw => do
    let l := raw.toList.dropWhile Char.isWhitespace
    let l ← if l.take 5 == ".type".toList then some (l.drop 5) else none
    guard (l.head?.any Char.isWhitespace)
    let l := l.dropWhile Char.isWhitespace
    let nameCh (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '$'
    let c ← l.head?
    guard (c.isAlpha || c == '_' || c == '.' || c == '$')
    let name := l.takeWhile nameCh
    let l := (l.drop name.length).dropWhile Char.isWhitespace
    let l ← if l.head? == some ',' then some (l.drop 1) else none
    let l := l.dropWhile Char.isWhitespace
    guard (l.take 9 == "@function".toList || l.take 9 == "%function".toList)
    pure (String.ofList name)

/-! ## Static offsets -/

/-- Static offsets: the stack pointer's, and those of the registers holding
a stack address (most recently set first), in the region of `epoch`: the
number of stack switches on the way to the point. -/
structure SO where
  sp : Int
  regs : List (String × Int)
  epoch : Nat := 0
  deriving BEq, Repr, Inhabited

/-- The offsets at a point: no flow reaches it, an unknown stack pointer, or
known offsets. -/
inductive Pt where
  | none
  | unknown
  | known (o : SO)
  deriving BEq, Repr, Inhabited

def SO.get (o : SO) (sp r : String) : Option Int :=
  if r == sp then some o.sp else o.regs.lookup r

def SO.kill (o : SO) (r : String) : SO := { o with regs := o.regs.filter (·.1 != r) }

def SO.set (o : SO) (sp r : String) (k : Int) : SO :=
  if r == sp then { o with sp := k } else { o with regs := (r, k) :: (o.kill r).regs }

/-- The offsets both `a` and `b` guarantee. -/
def Pt.meet : Pt → Pt → Pt
  | .none, b => b
  | a, .none => a
  | .known a, .known b =>
      if a.sp == b.sp && a.epoch == b.epoch then .known { a with regs := a.regs.filter fun e => b.regs.lookup e.1 == some e.2 }
      else .unknown
  | _, _ => .unknown

/-! ## Instructions -/

/-- What a register operation does to the offsets beyond writing its
destination: `from s n` sets the destination to `s`'s offset plus `n`, when
`s`'s is known. -/
inductive Info where
  | none
  | from (s : Option String) (n : Int)
  deriving BEq, Repr

/-- The classes of instructions. -/
inductive Cls where
  /-- x64 `movq n(%b), %r`. -/
  | ld (r b : String) (n : Int)
  /-- x64 `movq %r, n(%b)`. -/
  | st (b : String) (n : Int) (r : String)
  | push (r : String)
  | pop (r : String)
  /-- A register operation writing `d` (none: no register, or the zero register). -/
  | reg (d : Option String) (info : Info)
  /-- AArch64 `ldr`/`str Xr, [sp, #n]`. -/
  | slot (isLd : Bool) (r : Option String) (n : Int)
  | jmp (l : String)
  | jcc (l : String)
  | call (l : String)
  | ret
  /-- Outside the blocks, for the given reason. -/
  | x (reason : String)
  deriving BEq, Repr

def Cls.isTerm : Cls → Bool
  | .jmp _ | .jcc _ | .call _ | .ret => true
  | _ => false

/-- An instruction set's side of the analysis. -/
structure Isa where
  /-- Comment lines start with this. -/
  comment : String
  /-- The stack pointer's name. -/
  sp : String
  /-- The offsets on entry. -/
  entry : SO
  classify : String → Cls
  /-- The single-instruction node lemma that covers an instruction outside the blocks, if any. -/
  node : String → Option String
  /-- The registers an instruction outside the blocks may write. -/
  xDsts : String → List String
  /-- The offsets after an instruction outside the blocks, at known offsets. -/
  passX : SO → String → String → Pt
  /-- The offsets after a call, from those before it and those `step` gives. -/
  afterCall : SO → Pt → Pt
  /-- At an unknown stack pointer, the instructions after which no flow continues. -/
  stops : Cls → String → Bool
  /-- The new offsets (none: not covered at these offsets) and the accessed offset. -/
  step : SO → Cls → Option SO × Option Int
  /-- Whether an instruction is a stack switch at the given offsets: a
  register operation writing the stack pointer that the block lemma does not
  cover (`sw_nd`), or x64's `andq $k, %rsp` (`swand_nd`). -/
  switch : SO → Cls → String → Bool
  /-- The region of the entry epoch before any access. -/
  region0 : Int × Int
  /-- The system-call number an instruction sets, if any. -/
  nrOf : String → Option Nat
  /-- The system calls whose kernel step has no event (`sys`). -/
  silentNrs : List Nat
  /-- The system calls the system-call node does not cover. -/
  notSysNrs : List Nat
  /-- The reason for a covered class not covered at its offsets (other than a register operation). -/
  failReason : String
  /-- Offsets as a Lean term. -/
  soLean : SO → String
  /-- Kraken's parser for the block text. -/
  parseFn : String

/-! ## x86-64 -/

namespace X64

def r64 : List String :=
  ["rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rsp", "rbp"] ++ (List.range 8).map fun i => s!"r{i + 8}"

/-- The 64-bit register a register name is part of. -/
def base (s : String) : Option String :=
  if s ∈ r64 then some s else
  let legacy := [("rax", "eax", "al"), ("rbx", "ebx", "bl"), ("rcx", "ecx", "cl"), ("rdx", "edx", "dl"),
    ("rsi", "esi", "sil"), ("rdi", "edi", "dil"), ("rsp", "esp", "spl"), ("rbp", "ebp", "bpl")]
  match legacy.find? fun (_, e, b) => s == e || s == dropN e 1 || s == b with
  | some (r, _, _) => some r
  | none =>
    if s ∈ ["ah", "bh", "ch", "dh"] then some s!"r{s.toList.head!}x" else
    (List.range 8).findSome? fun i =>
      let r := s!"r{i + 8}"
      if s == r ++ "d" || s == r ++ "w" || s == r ++ "b" then some r else none

/-- `%name`, `name` in `[a-z0-9]+`. -/
def reg? (s : String) : Option String :=
  match s.toList with
  | '%' :: n => if !n.isEmpty && n.all isLowNum then some (String.ofList n) else none
  | _ => none

/-- `$n`. -/
def imm? (s : String) : Option Int :=
  match s.toList with
  | '$' :: n => int? (String.ofList n)
  | _ => none

/-- `n(%b)` or `(%b)`: the displacement and the register name. -/
def mem? (s : String) : Option (Int × String) := do
  let (pre, post) := (s.toList.takeWhile (· != '('), s.toList.dropWhile (· != '('))
  let n ← if pre.isEmpty then some 0 else int? (String.ofList pre)
  match post with
  | '(' :: '%' :: rest =>
    let name := rest.takeWhile isLowNum
    if !name.isEmpty && rest.drop name.length == [')'] then some (n, String.ofList name) else none
  | _ => none

def ccs : List String :=
  ["e", "z", "ne", "nz", "b", "c", "nae", "ae", "nb", "nc", "a", "nbe", "be", "na", "l", "nge", "le", "ng",
   "ge", "nl", "g", "nle"]

/-- `mn` is one of `ops`, followed by one character of `sfx`. -/
def withSfx (mn : String) (ops : List String) (sfx : String) : Option String :=
  ops.find? fun o => mn.length == o.length + 1 && mn.startsWith o && sfx.toList.contains (mn.toList.getLast!)

def classify (ins : String) : Cls := Id.run do
  if let some (a, b) := ops2 ins "movq" then
    if let some (n, bn) := mem? a then
      if let some rn := reg? b then
        if let (some r, some bb) := (base rn, base bn) then return .ld r bb n
    if let some rn := reg? a then
      if let some (n, bn) := mem? b then
        if let (some r, some bb) := (base rn, base bn) then return .st bb n r
  let (w, rest) := word ins
  if w == "pushq" then
    if let some r := reg? rest then if r ∈ r64 then return .push r
  if w == "popq" then
    if let some r := reg? rest then if r ∈ r64 then return .pop r
  if w == "jmp" && isLab rest then return .jmp rest
  if w.startsWith "j" && dropN w 1 ∈ ccs && isLab rest then return .jcc rest
  if w == "call" && isLab rest then return .call rest
  if ins == "ret" then return .ret
  let mn := w
  let ops := strip rest
  if has ops "%fs:" then return .x "thread pointer"
  if mn ∈ ["syscall", "ud2", "mfence", "lock"] || mn.startsWith "xchg" || mn.startsWith "xadd" then
    return .x (if mn ∈ ["syscall", "ud2"] then "system" else "shared memory")
  let flagOps := ["and", "or", "xor", "test", "imul", "shl", "shr", "sar"]
  if mn ∈ flagOps || (withSfx mn flagOps "bwlq").isSome then return .x "undefined flags"
  if has ops "(%rip)" then return .x "label address"
  if has ops "(" && !mn.startsWith "lea" then return .x "shared memory"
  if mn ∈ ["mov", "movb", "movw", "movl", "movq", "movabsq"] then
    if let some (s, d) := ops2 ins mn then
      if let some dn := reg? d then
        if let some sn := reg? s then
          return .reg (base dn) (if mn == "movq" && sn ∈ r64 && dn ∈ r64 then .from (some sn) 0 else .none)
        if (imm? s).isSome then return .reg (base dn) .none
  if mn.length == 6 && (mn.startsWith "movz" || mn.startsWith "movs") &&
      "bwl".toList.contains (mn.toList[4]!) && "wlq".toList.contains (mn.toList[5]!) then
    if let some (s, d) := ops2 ins mn then
      if let (some _, some dn) := (reg? s, reg? d) then return .reg (base dn) .none
  if mn.startsWith "set" && dropN mn 3 ∈ ccs then
    if let some r := reg? rest then return .reg (base r) .none
  if mn.startsWith "cmov" then
    let c := dropN mn 4
    let cOk := c ∈ ccs || (!c.isEmpty && "wlq".toList.contains c.toList.getLast! &&
      String.ofList c.toList.dropLast ∈ ccs)
    if cOk then
      if let some (s, d) := ops2 ins mn then
        if let (some _, some dn) := (reg? s, reg? d) then return .reg (base dn) .none
  if mn == "leaq" then
    if let some (a, d) := ops2 ins mn then
      if let (some (n, bn), some dn) := (mem? a, reg? d) then
        if let some b := base bn then return .reg (base dn) (.from (some b) n)
  if let some op := withSfx mn ["add", "adc", "sub", "sbb", "cmp"] "bwlq" then
    if let some (s, d) := ops2 ins mn then
      if let some dn := reg? d then
        let i := imm? s
        if (reg? s).isSome || i.isSome then
          let info := match i with
            | some k =>
              if mn.toList.getLast! == 'q' && (op == "add" || op == "sub") && dn ∈ r64 then
                Info.from (some dn) (if op == "add" then k else -k)
              else .none
            | none => .none
          return .reg (if op == "cmp" then none else base dn) info
  if (withSfx mn ["inc", "dec", "neg", "not"] "bwlq").isSome then
    if let some r := reg? rest then return .reg (base r) .none
  if mn == "cqto" || mn == "cqo" then return .reg (some "rdx") .none
  if mn == "nop" then return .reg none .none
  return .x "other"

-- scc prints `cqo` as `cqto` (`Scc.Emit.X64.ppOp`): a register operation
-- writing `%rdx`, in its row (`PlaceData.X64.opK`'s `.cqo` case).
#guard classify "cqto" matches .reg (some "rdx") .none && classify "cqo" matches .reg (some "rdx") .none

/-- `flag_nd`: the register forms with undefined flags and the zeroing
`xorl %r32, %r32`; `si_nd`: `leaq L(%rip), %r` (label); `syscall_nd`:
`syscall` (sys); `fsld_nd`: `movq %fs:k, %r` (thread pointer); `dead_nd`:
`ud2`, a node no run reaches, after a call that does not return or after
`exit_group` (dead). The destination is never `%rsp`. -/
def node (ins : String) : Option String := Id.run do
  let (mn, _) := word ins
  let ok (d : String) := d ∈ r64 && d != "rsp"
  if mn ∈ ["andq", "orq", "xorq", "testq", "imulq"] then
    if let some (s, d) := ops2 ins mn then
      if let (some sn, some dn) := (reg? s, reg? d) then
        if sn ∈ r64 && ok dn then return some "flag"
  if mn ∈ ["shlq", "shrq"] then
    if let some (s, d) := ops2 ins mn then
      if let some dn := reg? d then
        if s == "%cl" && ok dn then return some "flag"
  if mn == "xorl" then
    if let some (s, d) := ops2 ins mn then
      if let (some sn, some dn) := (reg? s, reg? d) then
        if sn == dn && (base sn).any (· != "rsp") && sn ∉ r64 then return some "flag"
  if mn == "leaq" then
    if let some (a, d) := ops2 ins mn then
      if let some dn := reg? d then
        if a.endsWith "(%rip)" && isLab (String.ofList (a.toList.take (a.length - 6))) && ok dn then
          return some "label"
  if ins == "syscall" then return some "sys"
  if mn == "movq" then
    if let some (a, d) := ops2 ins mn then
      if let some dn := reg? d then
        if a.startsWith "%fs:" && (int? (dropN a 4)).isSome && ok dn then return some "thread pointer"
  if ins == "ud2" then return some "dead"
  return none

/-- The register an instruction may write: its last operand. -/
def xDst (text : String) : Option String :=
  let t := (text.toList.reverse.takeWhile isLowNum).reverse
  if !t.isEmpty && (text.toList.reverse.drop t.length).head? == some '%' then base (String.ofList t) else none

/-- **The registers an instruction may write**: its last operand's
(`xDst`), and the ones it writes besides: `mul`, `div`, `idiv` and
one-operand `imul` write `rax` and `rdx` (`rax` only at byte width) instead;
`cqto`, `cltd` and `cwtd` write `rdx`; `xchg` and `xadd` their first
operand too; `cmpxchg` writes `rax` too, `cmpxchg16b` `rax` and `rdx`. A
`lock` prefix is skipped. -/
def xDsts (text : String) : List String :=
  let t := strip text
  let t := if t.startsWith "lock " then strip (dropN t 5) else t
  let (mn, rest) := word t
  let ops := if (strip rest).isEmpty then [] else (rest.splitOn ", ").map strip
  let fam (f : String) : Bool := mn == f || [f ++ "b", f ++ "w", f ++ "l", f ++ "q"].contains mn
  let first : List String := match ops.head? with
    | some o => ((reg? o).bind base).toList
    | none => []
  let last := (xDst t).toList
  if (fam "mul" || fam "div" || fam "idiv" || (fam "imul" && ops.length == 1)) then
    if mn.endsWith "b" then ["rax"] else ["rax", "rdx"]
  else if mn ∈ ["cqto", "cltd", "cwtd"] then ["rdx"]
  else if mn == "cmpxchg16b" then ["rax", "rdx"]
  else if fam "xchg" || fam "xadd" then first ++ last
  else if fam "cmpxchg" then "rax" :: last
  else last

#guard ["addq %rax, %rcx", "mulq %rcx", "divb %cl", "idivl 8(%rsp)", "cqto", "xchgq %rax, %rcx",
  "xchgq %rax, (%rcx)", "lock xaddq %rax, %rdx", "lock cmpxchgq %rcx, (%rdx)", "lock cmpxchg16b (%rax)",
  "syscall", "imulq %rcx, %rax"].map xDsts ==
  [["rcx"], ["rax", "rdx"], ["rax"], ["rax", "rdx"], ["rdx"], ["rax", "rcx"], ["rax"], ["rax", "rdx"],
   ["rax"], ["rax", "rdx"], [], ["rax"]]

def step (o : SO) : Cls → Option SO × Option Int
  | .ld r b n =>
    match o.get "rsp" b with
    | some kb => if r == "rsp" then (none, none) else (some (o.kill r), some (kb + n))
    | none => (none, none)
  | .st b n _ =>
    match o.get "rsp" b with
    | some kb => (some o, some (kb + n))
    | none => (none, none)
  | .push _ => (some { o with sp := o.sp - 8 }, some (o.sp - 8))
  | .pop r => if r == "rsp" then (none, none) else (some { o.kill r with sp := o.sp + 8 }, some o.sp)
  | .reg d info => Id.run do
    if let .from (some s) n := info then
      if let (some k, some d) := (o.get "rsp" s, d) then return (some (o.set "rsp" d (k + n)), none)
    match d with
    | none => (some o, none)
    | some d => if d == "rsp" then (none, none) else (some (o.kill d), none)
  | .jmp _ | .jcc _ => (some o, none)
  | .call _ => (some { o with sp := o.sp - 8 }, some (o.sp - 8))
  | .ret => (some { o with sp := o.sp + 8 }, some o.sp)
  | _ => (none, none)

def isa : Isa where
  comment := "#"
  sp := "rsp"
  entry := ⟨8, [], 0⟩
  classify := classify
  node := node
  xDsts := xDsts
  passX o text _ :=
    if text == "ud2" then .none else
    let ds := xDsts text
    if "rsp" ∈ ds then .unknown
    else if text == "syscall" then .known (((o.kill "rax").kill "rcx").kill "r11")
    else .known (ds.foldl SO.kill o)
  afterCall o _ := .known (["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"].foldl SO.kill o)
  stops c text := c matches .jmp _ | .ret || text == "ud2"
  step := step
  switch o c text := match c with
    | .reg d _ => d == some "rsp" && (step o c).1.isNone
    | _ => text.startsWith "andq $" && match text.splitOn ", " with
      | [k, "%rsp"] => (int? (dropN k 6)).isSome
      | _ => false
  region0 := (0, 16)
  nrOf text := match text.splitOn ", " with
    | [a, r] =>
      if (a.startsWith "movl $" || a.startsWith "movq $") && (r == "%eax" || r == "%rax") then
        let d := dropN a 6
        if !d.isEmpty && d.all Char.isDigit then some d.toNat! else none
      else none
    | _ => none
  silentNrs := [13, 231, 202, 60]
  notSysNrs := [158]
  failReason := "non-frame memory"
  soLean o := s!"⟨{o.sp}, [{", ".intercalate (o.regs.map fun (r, k) => s!"(.{r}, {k})")}]⟩"
  parseFn := "parse"

-- The offsets after them: the registers written besides the last operand are
-- forgotten too (`rax` holding a stack offset here).
#guard
  let o : SO := ⟨0, [("rax", 8), ("rdx", 16), ("rcx", 24)], 0⟩
  ["xchgq %rax, (%rcx)", "lock xaddq %rax, (%rcx)", "lock cmpxchgq %rdx, (%rcx)", "mulq %rcx"].map
      (fun t => isa.passX o t "shared memory") ==
    [.known ⟨0, [("rdx", 16), ("rcx", 24)], 0⟩, .known ⟨0, [("rdx", 16), ("rcx", 24)], 0⟩,
     .known ⟨0, [("rdx", 16), ("rcx", 24)], 0⟩, .known ⟨0, [("rcx", 24)], 0⟩]

end X64

/-! ## AArch64 -/

namespace A64

/-- The register a destination operand names: `sp`, `xN`, or none (the zero register). -/
def base (r : String) : Option String :=
  if r == "sp" || r == "wsp" then some "sp" else
  match r.toList with
  | c :: ds => if (c == 'x' || c == 'w') && !ds.isEmpty && ds.all Char.isDigit then some ("x" ++ String.ofList ds) else none
  | [] => none

/-- `x[0-9]+` or `xzr`. -/
def isXR (s : String) : Bool :=
  s == "xzr" || match s.toList with
    | 'x' :: ds => !ds.isEmpty && ds.all Char.isDigit
    | _ => false

/-- `x0` … `x30`. -/
def isG (s : String) : Bool :=
  match s.toList with
  | ['x', d] => d.isDigit
  | ['x', a, b] => (a == '1' || a == '2') && b.isDigit || (a == '3' && b == '0')
  | _ => false

def regOps : List String :=
  ["movz", "movk", "add", "sub", "adds", "subs", "madd", "msub", "and", "orr", "eor", "ubfm", "sbfm", "lslv",
   "lsrv", "asrv", "csel", "csinc", "mrs"]

/-- `si_nd`: `adrp Xd, L`, `add Xd, Xs, :lo12:L` (label); `nop`, `msr tpidr_el0, Xs` (system);
`svc_nd`: `svc #0` (sys). -/
def node (ins : String) : Option String :=
  let (w, rest) := word ins
  if w == "adrp" && (match rest.splitOn ", " with | [d, l] => isG d && isLab l | _ => false) then some "label"
  else if w == "add" && (match rest.splitOn ", " with
      | [d, s, l] => isG d && isG s && l.startsWith ":lo12:" && isLab (dropN l 6)
      | _ => false) then some "label"
  else if ins == "nop" || (w == "msr" && match rest.splitOn ", " with
      | ["tpidr_el0", s] => isG s
      | _ => false) then some "system"
  else if ins == "svc #0" then some "sys"
  else none

def classify (ins : String) : Cls := Id.run do
  let (w, rest) := word ins
  if w == "ldr" || w == "str" then
    let n? : Option Int := match rest.splitOn ", " with
      | [r, "[sp]"] => if isXR r then some 0 else none
      | [r, "[sp", m] =>
        if isXR r && m.startsWith "#" && m.endsWith "]" then int? (String.ofList (m.toList.drop 1).dropLast)
        else none
      | _ => none
    if let some n := n? then return .slot (w == "ldr") (base ((rest.splitOn ", ").head!)) n
  if w == "b" && isLab rest then return .jmp rest
  if w.startsWith "b." && w.length > 2 && (dropN w 2).toList.all Char.isLower && isLab rest then return .jcc rest
  if w == "cbz" || w == "cbnz" then
    if let [r, l] := rest.splitOn ", " then
      if isXR r && isLab l then return .jcc l
  if w == "bl" && isLab rest then return .call rest
  if ins == "ret" then return .ret
  let mn := w
  let ops := strip rest
  if mn ∈ ["br", "blr"] then return .x "indirect branch"
  if mn ∈ ["ldar", "stlr", "swpal", "ldaddal", "casal"] then return .x "shared memory"
  if mn ∈ ["ldr", "str", "ldur", "stur"] then return .x "non-frame memory"
  if mn == "adrp" || has ops ":lo12:" then return .x "label address"
  if mn ∈ ["svc", "msr", "dmb"] then return .x "system"
  if mn ∉ regOps then return .x "other"
  let args := (ops.splitOn ",").map strip
  let a0 := args.headD ""
  let d := base a0
  if mn ∈ ["and", "orr", "eor"] && has ops "#" then return .x "other"
  if mn ∈ ["movz", "movk"] then
    let a1 := args.getD 1 ""
    if !(a1.startsWith "#" && (a1.toList.drop 1).head?.any Char.isDigit) then return .x "other"
  if mn == "adds" && has ops "#" then return .x "other"
  if (mn == "add" || mn == "sub") && args.length == 3 && args[2]!.startsWith "#" then
    let a1 := args[1]!
    if let some n := int? (dropN args[2]! 1) then
      if (a0.startsWith "x" || a0 == "sp") && (a1.startsWith "x" || a1 == "sp") then
        return .reg d (.from (base a1) (if mn == "add" then n else -n))
    return .reg d .none
  if d == some "sp" then return .x "other"
  return .reg d .none

/-- The register an instruction may write: its first operand. -/
def xDst (text : String) : Option String :=
  let (_, rest) := word (strip text)
  if (strip rest).isEmpty then none else base (strip ((rest.splitOn ",").headD ""))

/-- **The registers an instruction may write**: its first operand's
(`xDst`), and for the pair loads `ldp`, `ldpsw`, `ldxp` and `ldaxp` its
second operand's too; `casp` (any ordering suffix) writes its first two
operands (`rs1`, `rs2`); a pre- or post-indexed address (`[xN, #k]!`,
`[xN], #k`) writes its base register too. -/
def xDsts (text : String) : List String :=
  let t := strip text
  let (mn, rest) := word t
  let ops := if (strip rest).isEmpty then [] else (rest.splitOn ",").map strip
  let first := (xDst t).toList
  let second := ((ops.getD 1 "").splitOn "[").headD "" |> strip |> base |>.toList
  let ds := if mn ∈ ["ldp", "ldpsw", "ldxp", "ldaxp"] || mn.startsWith "casp" then first ++ second
    else first
  let wb : List String :=
    if has t "]!" || has t "], " then
      match t.splitOn "[" with
      | [_, a] => (base (strip ((((a.splitOn "]").headD "").splitOn ",").headD ""))).toList
      | _ => []
    else []
  ds ++ wb

#guard ["ldp x1, x2, [sp, #16]", "ldpsw x3, x4, [x0]", "ldxp x5, x6, [x0]", "ldaxp x7, x8, [x0]",
  "casp x0, x1, x2, x3, [x4]", "caspal x6, x7, x2, x3, [x4]", "ldp xzr, x2, [x0]", "ldr x1, [sp, #8]",
  "stp x1, x2, [sp]", "add sp, x9, #0", "svc #0", "ldp x29, x30, [sp], #16", "stp x29, x30, [sp, #-16]!",
  "ldr x1, [x0, #8]!", "str x1, [x2], #8"].map xDsts ==
  [["x1", "x2"], ["x3", "x4"], ["x5", "x6"], ["x7", "x8"], ["x0", "x1"], ["x6", "x7"], ["x2"], ["x1"],
   ["x1"], ["sp"], [], ["x29", "x30", "sp"], ["x29", "sp"], ["x1", "x0"], ["x1", "x2"]]

def step (o : SO) : Cls → Option SO × Option Int
  | .slot isLd r n =>
    if o.sp % 16 != 0 || n % 8 != 0 then (none, none) else
    let acc := o.sp + n
    match isLd, r with
    | true, some r => (some (o.kill r), some acc)
    | _, _ => (some o, some acc)
  | .reg d info => Id.run do
    if let .from (some s) n := info then
      if let (some k, some d) := (o.get "sp" s, d) then return (some (o.set "sp" d (k + n)), none)
    match d with
    | none => (some o, none)
    | some d => if d == "sp" then (none, none) else (some (o.kill d), none)
  | .jmp _ | .jcc _ | .ret => (some o, none)
  | .call _ => (some (o.kill "x30"), none)
  | _ => (none, none)

def isa : Isa where
  comment := "//"
  sp := "sp"
  entry := ⟨0, [], 0⟩
  classify := classify
  node := node
  xDsts := xDsts
  passX o text why :=
    let ds := xDsts text
    if "sp" ∈ ds then .unknown
    else if why == "system" || why == "shared memory" then .known { o with regs := [] }
    else .known (ds.foldl SO.kill o)
  afterCall _ n := match n with
    | .known n => .known ((List.range 19).foldl (fun o i => o.kill s!"x{i}") n)
    | n => n
  stops c _ := c matches .jmp _ | .ret
  step := step
  switch o c _ := match c with
    | .reg d _ => d == some "sp" && (step o c).1.isNone
    | _ => false
  region0 := (0, 0)
  nrOf text := match text.splitOn ", " with
    | [a, n] =>
      if (a == "mov x8" || a == "movz x8") && n.startsWith "#" then
        let d := dropN n 1
        if !d.isEmpty && d.all Char.isDigit then some d.toNat! else none
      else none
    | _ => none
  silentNrs := [134, 94, 98, 93]
  notSysNrs := []
  failReason := "unaligned stack access"
  soLean o := s!"⟨{o.sp}, [{", ".intercalate (o.regs.map fun (r, k) => s!"(.X{dropN r 1}, {k})")}]⟩"
  parseFn := "parseAArch64"

-- A pair load forgets both destinations: a stale `sp + k` fact for the
-- second one is dropped (`x2` holding a stack offset here).
#guard
  let o : SO := ⟨0, [("x1", 8), ("x2", 16), ("x3", 24)], 0⟩
  ["ldp x1, x2, [x0]", "ldaxp x1, x2, [x0]", "casp x2, x3, x4, x5, [x0]", "ldr x1, [x0]"].map
      (fun t => isa.passX o t "other") ==
    [.known ⟨0, [("x3", 24)], 0⟩, .known ⟨0, [("x3", 24)], 0⟩, .known ⟨0, [("x1", 8)], 0⟩,
     .known ⟨0, [("x2", 16), ("x3", 24)], 0⟩]

-- A write-back address writes its base: `sp`'s offset is then unknown, and a
-- stale fact for another base is dropped (`x3` here).
#guard
  let o : SO := ⟨0, [("x1", 8), ("x2", 16), ("x3", 24)], 0⟩
  ["ldp x29, x30, [sp], #16", "ldr x9, [x3, #8]!"].map (fun t => isa.passX o t "other") ==
    [.unknown, .known ⟨0, [("x1", 8), ("x2", 16)], 0⟩]

end A64

/-! ## The analysis -/

/-- A listing item: its line number, whether it is a label, and its text. -/
structure Item where
  line : Nat
  label : Bool
  text : String
  /-- The size in bytes: 0 for a label; an instruction's from the size table
  (x64), or 4 (AArch64). -/
  size : Nat := 0
  /-- The assembler directive lines since the label before it. -/
  dirs : Nat := 0
  deriving Inhabited

/-- A block: function, first and last listing line, region, entry offsets,
instructions; the label before it and its byte offset from that label; the
instructions' sizes. -/
structure Block where
  fn : String
  first : Nat
  last : Nat
  lo : Int
  hi : Int
  so : SO
  ins : Array String
  label : String := ""
  off : Nat := 0
  sizes : Array Nat := #[]
  /-- The assembler directive lines between the label and the block. -/
  dirs : Nat := 0
  /-- The instructions between the label and the block (x64's cell count). -/
  cnt : Nat := 0

/-- A counter, in first-insertion order. -/
abbrev Counter := Array (String × Nat)

def Counter.inc (c : Counter) (k : String) : Counter :=
  match c.findIdx? (·.1 == k) with
  | some i => c.modify i fun (k, n) => (k, n + 1)
  | none => c.push (k, 1)

/-- The functions of a listing, with their labels and instructions, and
the instructions' sizes: from `sizes` (one entry per instruction line, in
text order: scc's x64 size table, `Scc.Cert.Sizes.sizesOf`), or 4 each. -/
def functions (isa : Isa) (lines : List String) (sizes : Option (List Nat) := none) :
    Except String (Array (String × Array Item)) := do
  let funs := declared lines
  let mut fs : Array (String × Array Item) := #[]
  let mut szs := sizes.getD []
  let mut dirs := 0
  for (raw, i) in lines.zipIdx 1 do
    let s := strip raw
    if s.isEmpty || s.startsWith isa.comment then continue
    if !raw.startsWith "\t" && s.endsWith ":" then
      let lab := String.ofList s.toList.dropLast
      if lab ∈ funs || fs.isEmpty then fs := fs.push (lab, #[])
      fs := fs.modify (fs.size - 1) fun (f, its) => (f, its.push ⟨i, true, lab, 0, 0⟩)
      dirs := 0
      continue
    if s.startsWith "." then dirs := dirs + 1; continue
    let mut size := 4
    if sizes.isSome then
      match szs with
      | z :: t => size := z; szs := t
      | [] => throw s!"the size table ends before listing line {i}"
    if !fs.isEmpty then fs := fs.modify (fs.size - 1) fun (f, its) => (f, its.push ⟨i, false, s, size, dirs⟩)
  if sizes.isSome && !szs.isEmpty then throw "the size table has more entries than the listing has instructions"
  return fs

/-- The offsets before every item of a function (the meet at labels, to a fixpoint). -/
def offsets (isa : Isa) (fn : String) (items : Array Item) : Except String (Array Pt) := do
  let mut atLabel : List (String × Pt) := []
  let mut before : Array Pt := Array.replicate items.size .none
  for _ in [0:100] do
    let mut changed := false
    let mut o : Pt := .known isa.entry
    let mut epochs := 0
    for idx in [0:items.size] do
      let it := items[idx]!
      -- the flow into a label: the meet with its offsets so far
      let flow (atLabel : List (String × Pt)) (lab : String) (o : Pt) : List (String × Pt) × Pt × Bool :=
        let old := (atLabel.lookup lab).getD .none
        let new := old.meet o
        if new != old then ((lab, new) :: atLabel.filter (·.1 != lab), new, true) else (atLabel, new, false)
      if it.label then
        let (a, n, ch) := flow atLabel it.text o
        atLabel := a; o := n; changed := changed || ch
        continue
      before := before.set! idx o
      let c := isa.classify it.text
      if o == .none then continue
      match c with
      | .jmp l | .jcc l =>
        let (a, _, ch) := flow atLabel l o
        atLabel := a; changed := changed || ch
      | _ => pure ()
      match o with
      | .known k =>
        if isa.switch k c it.text then  -- a new region at the new stack pointer
          epochs := epochs + 1
          o := .known ⟨0, [], epochs⟩
          continue
        if let .x why := c then
          o := isa.passX k it.text why
          continue
        let n : Pt := match isa.step k c with
          | (some n, _) => .known n
          | (none, _) =>  -- not covered here: as an instruction outside the blocks
            let ds := isa.xDsts it.text
            if isa.sp ∈ ds then .unknown else .known (ds.foldl SO.kill k)
        o := match c with
          | .jmp _ | .ret => .none
          | .call _ => isa.afterCall k n
          | _ => n
      | _ =>
        if isa.stops c it.text then o := .none
    if !changed then return before
  throw s!"no fixpoint in {fn}"

/-- Block data and coverage statistics. -/
structure Result where
  blocks : Array Block
  total : Counter
  covered : Counter
  uncovered : Counter
  nodes : Counter

def analyse (isa : Isa) (asm : String) (sizes : Option (List Nat) := none) : Except String Result := do
  let mut r : Result := ⟨#[], #[], #[], #[], #[]⟩
  for (fn, items) in ← functions isa (asm.splitOn "\n") sizes do
    -- the label before each item and the item's byte offset from it
    let mut lab := fn
    let mut off := 0
    let mut cnt := 0
    let mut labOff : Array (String × Nat) := #[]
    let mut labCnt : Array Nat := #[]
    for it in items do
      if it.label then lab := it.text; off := 0; cnt := 0
      labOff := labOff.push (lab, off)
      labCnt := labCnt.push cnt
      off := off + it.size
      if !it.label then cnt := cnt + 1
    let key := if fn.startsWith "wc_" then "user" else "runtime"
    let before ← offsets isa fn items
    -- the regions: the accessed offsets, one region per epoch
    let mut regions : List (Nat × Int × Int) := [(0, isa.region0)]
    for idx in [0:items.size] do
      let it := items[idx]!
      if it.label then continue
      let .known k := before[idx]! | continue
      let c := isa.classify it.text
      if c matches .x _ then continue
      if let (some _, some a) := isa.step k c then
        let (lo, hi) := (regions.lookup k.epoch).getD (0, 0)
        regions := (k.epoch, min lo a, max hi (a + 8)) :: regions.filter (·.1 != k.epoch)
    -- the blocks
    let mut blk : Option Block := none
    let mut nr : Option Nat := none  -- the system-call number last set in straight-line code
    let flush (r : Result) (blk : Option Block) : Result :=
      match blk with
      | some b => if b.ins.isEmpty then r else { r with blocks := r.blocks.push b }
      | none => r
    for idx in [0:items.size] do
      let it := items[idx]!
      if it.label then
        nr := none
        r := flush r blk; blk := none
        continue
      r := { r with total := r.total.inc key }
      if let some n := isa.nrOf it.text then nr := some n
      let c := isa.classify it.text
      let o := before[idx]!
      let switch := match o with
        | .known k => isa.switch k c it.text
        | _ => false
      if let .x why := c then
        r := { r with uncovered := r.uncovered.inc s!"{key}: {why}" }
        match isa.node it.text, o with
        | some nd, .known _ =>
          if nd == "sys" && nr.any (· ∈ isa.notSysNrs) then
            if switch then r := { r with nodes := r.nodes.inc s!"{key}: switch" }
          else
            let nd := if nd != "sys" then nd
              else match nr with
                | none => "sys, number after a label"  -- the number must come from the node's invariant
                | some n => if n ∈ isa.silentNrs then "sys" else "sys, control only"
            r := { r with nodes := r.nodes.inc s!"{key}: {nd}" }
        | _, _ => if switch then r := { r with nodes := r.nodes.inc s!"{key}: switch" }
        r := flush r blk; blk := none
        continue
      let .known k := o | do
        r := { r with uncovered := r.uncovered.inc s!"{key}: unknown stack offset" }
        r := flush r blk; blk := none
        continue
      if (isa.step k c).1.isNone then
        let why := if c matches .reg _ _ then "stack switch" else isa.failReason
        r := { r with uncovered := r.uncovered.inc s!"{key}: {why}" }
        if switch then r := { r with nodes := r.nodes.inc s!"{key}: switch" }
        r := flush r blk; blk := none
        continue
      r := { r with covered := r.covered.inc key }
      let (lo, hi) := (regions.lookup k.epoch).getD (0, 0)
      let b0 : Block := { fn, first := it.line, last := it.line, lo, hi, so := k, ins := #[],
                          label := labOff[idx]!.1, off := labOff[idx]!.2, dirs := it.dirs,
                          cnt := labCnt[idx]! }
      let b := blk.getD b0
      blk := some { b with ins := b.ins.push it.text, last := it.line, sizes := b.sizes.push it.size }
      -- a block ends at a terminator, and after the first instruction at a
      -- transfer site's label (`scc_rt_take_site`, `scc_rt_release_site`: the
      -- x64 `nop` is a block of its own, the site's node)
      if c.isTerm || (labOff[idx]!.1.endsWith "_site" && labCnt[idx]! == 0) then
        r := flush r blk; blk := none
    r := flush r blk
  return r

/-- The `block_spec` commands: per block, a comment with its function, its
listing lines and its address (`at L + off`: the label before it, as written,
and the byte offset of its first instruction from that label), the command,
and an empty line. Blocks are named after their function and their index in
it. With `sized` (x64), the instructions are zipped with their sizes in
bytes, `(parse("…")).zip [z₁, …]`: `block_spec` takes a list of
`(Directive × Nat)` cells. -/
def render (isa : Isa) (r : Result) (sized : Bool := false) : String := Id.run do
  let mut names : Counter := #[]
  let mut out : Array String := #[]
  for b in r.blocks do
    let k := ((names.find? (·.1 == b.fn)).map (·.2)).getD 0
    names := names.inc b.fn
    let text := "\n".intercalate b.ins.toList
    let code := if sized then s!"({isa.parseFn}(\"{text}\")).zip {b.sizes.toList}"
      else s!"{isa.parseFn}(\"{text}\")"
    out := out.push s!"-- {b.fn}, listing lines {b.first}–{b.last}, at {b.label} + {b.off}"
    out := out.push s!"block_spec {ident b.fn}_{k} ({b.lo}) {b.hi} {isa.soLean b.so} {code}"
    out := out.push ""
  return "\n".intercalate out.toList

/-- The block names of `render`, in block order. -/
def names (r : Result) : Array String := Id.run do
  let mut cnt : Counter := #[]
  let mut out : Array String := #[]
  for b in r.blocks do
    let k := ((cnt.find? (·.1 == b.fn)).map (·.2)).getD 0
    cnt := cnt.inc b.fn
    out := out.push s!"{ident b.fn}_{k}"
  return out

/-- The check of a table: `Scc.Cert.Rt.A64.blocksIn`, a `Prop` closed by
`kernel_rfl`. -/
def codeCheck : String := "blocksIn"

/-- A function's part of a table name: `ident`, without leading `_`. -/
def fnId (fn : String) : String := String.ofList ((ident fn).toList.dropWhile (· == '_'))

/-- **The code check of an AArch64 listing** (`scc --code`), for the
program `{pfx}Prog`: per function, the table `{pfx}T_<fn>` of its blocks
grouped by label (`Scc.Cert.Rt.A64.Grp`: the blocks after a label, each with
its instruction count from the label and the text of its `block_spec`, named
in a comment after it), in program order as `blocksIn`'s single pass needs;
then `{pfx}T`, all of them, and `{pfx}T_in`, its check by `kernel_rfl`. A
block with an assembler directive between it and its label is an error: the
offset would not count it. With `sized` (x64, `Scc.Cert.Rt.X64.Grp`), each
block has its instruction count and its byte offset from the label, and its
instructions are zipped with their sizes. -/
def renderCode (r : Result) (pfx : String) (check : String := codeCheck) (sized : Bool := false) :
    Except String String := do
  let nms := names r
  -- the functions in block order, each with its groups: label, blocks (place, name, code)
  let mut fns : Array (String × Array (String × Array (String × String × String))) := #[]
  for (b, nm) in r.blocks.zip nms do
    if b.dirs > 0 then
      throw s!"{b.fn}: an assembler directive between {b.label} and listing line {b.first}"
    let text := "\n".intercalate b.ins.toList
    let ent := if sized then (s!"{b.cnt}, {b.off}", nm, s!"(parse(\"{text}\")).zip {b.sizes.toList}")
      else (s!"{b.off / 4}", nm, s!"parseAArch64(\"{text}\")")
    if !fns.back?.any (·.1 == b.fn) then fns := fns.push (b.fn, #[])
    let last := fns.size - 1
    let sameLab := fns[last]!.2.back?.any (·.1 == b.label)
    fns := fns.modify last fun (f, gs) =>
      (f, if sameLab then gs.modify (gs.size - 1) fun (l, es) => (l, es.push ent) else gs.push (b.label, #[ent]))
  let mut out : Array String := #[]
  for (f, gs) in fns do
    let t := s!"{pfx}T_{fnId f}"
    let grp (g : String × Array (String × String × String)) : String :=
      let es := g.2.toList.map fun (k, nm, code) => s!"({k}, {code}) /- {nm} -/"
      s!"  ⟨\"{g.1}\", [" ++ ",\n    ".intercalate es ++ "]⟩"
    out := out.push s!"/-- The blocks of `{f}`. -/
def {t} : List Grp := [
{",\n".intercalate (gs.toList.map grp)}
]
"
  let ts := fns.toList.map fun (f, _) => s!"{pfx}T_{fnId f}"
  out := out.push s!"/-- All the blocks of the program. -/
def {pfx}T : List Grp :=
{" ++\n".intercalate (ts.map ("  " ++ ·))}

theorem {pfx}T_in : {check} {pfx}{if sized then "Cells" else "Prog"} {pfx}T := by kernel_rfl
"
  return "\n".intercalate out.toList

open Lean in
/-- The coverage statistics, as JSON. -/
def stats (isa : Isa) (r : Result) : Json :=
  let obj (c : Counter) : Json := Json.mkObj (c.toList.map fun (k, n) => (k, toJson n))
  let sorted (c : Counter) : Counter := c.qsort (·.1 < ·.1)
  let lens := r.blocks.map (·.ins.size)
  let hist : Counter := (lens.foldl (fun c n => Counter.inc c (toString n)) #[]).qsort
    fun a b => a.1.toNat! < b.1.toNat!
  Json.mkObj [
    ("total", obj r.total), ("covered", obj r.covered),
    ("uncovered", obj (sorted r.uncovered)), ("nodes", obj (sorted r.nodes)),
    ("blocks", toJson r.blocks.size),
    ("user_blocks", toJson (r.blocks.filter (·.fn.startsWith "wc_")).size),
    ("max_block", toJson (lens.foldl max 0)),
    ("terminated", toJson (r.blocks.filter fun b => (isa.classify b.ins.back!).isTerm).size),
    ("hist", obj hist)]

def isaOf : Arch → Isa
  | .x64 => X64.isa
  | .arm => A64.isa

/-- The block data of a listing: the `block_spec` commands and the coverage
statistics (JSON). x64 needs the instructions' sizes (`sizes`, one per
instruction line in text order); AArch64's are 4 each. -/
def run (arch : Arch) (asm : String) (sizes : Option (List Nat) := none) : Except String (String × String) := do
  let isa := isaOf arch
  let sized := arch matches .x64
  if sized && sizes.isNone then throw "x64 block data needs the instruction sizes"
  let r ← analyse isa asm (if sized then sizes else none)
  return (render isa r sized, (stats isa r).pretty)

/-- The base name of an input file and its identifier prefix (`p` before
a leading digit). -/
def codeName (name : String) : String × String :=
  let base := (name.splitOn "/").getLast!
  let stem := ((base.splitOn ".").dropLast).headD base
  let pfx0 := fnId (if stem.isEmpty then base else stem)
  (base, if pfx0.isEmpty || (pfx0.get 0).isDigit then "p" ++ pfx0 else pfx0)

/-- The label offsets `offs` in the order of their labels' definitions in
the text `asm` (`L:` lines), the others after them in their order: the
order of the code cells' labels, which `Scc.Cert.Link.X64.sizeOkL` checks
the offsets in. -/
def textOrder (asm : String) (offs : List (String × Nat)) : List (String × Nat) :=
  let defs := (asm.splitOn "\n").filterMap fun l =>
    if l.endsWith ":" && !l.startsWith "\t" then some (String.ofList (l.toList.dropLast)) else none
  let inText := defs.filterMap fun l => (offs.lookup l).map (l, ·)
  inText ++ offs.filter fun (l, _) => !defs.contains l

/-- The layout definition of a code check file: `{pfx}Λ`, the static link's
layout `link`, with the immediate table `imms` (its text, defining
`{pfx}Imms`) if any. -/
def layoutDef (imms : Option String) (pfx link : String) : String :=
  match imms with
  | none => s!"/-- **The layout of the program's static link.** -/
def {pfx}Λ : Scc.Sem.Layout := {link}
"
  | some t => s!"{t}
/-- **The layout of the program's static link**, with its immediate table. -/
{if (t.splitOn "noncomputable def").length > 1 then "noncomputable " else ""}def {pfx}Λ : Scc.Sem.Layout := \{ {link} with imms := {pfx}Imms }
"

/-- **The code check file of an x64 listing** (`scc --arch x64 --code`), for
the input file `name`, with the listing's size table and label offsets
(`sizes`, from GNU `as`, untrusted): the twin of `code`'s AArch64 file. It
embeds the listing as the canonical loader's text (`{pfx}Asm`: the text, its
sizes and label offsets), lays out its code cells (`{pfx}Cells`, by
`scc_x64_cells%`) and reads its data sections (`{pfx}Secs`) at elaboration
time, checked by `#guard`; checks every block at its place
(`renderCode`, `Scc.Cert.Rt.X64.blocksIn`), the runtime's code that the
runtime proofs take as hypotheses (`printIn`, `abortIn`, `morestackIn`;
`scc_rt_main`'s tail by `mainIn` and `hello.w`'s `wc_printL` by `printLIn`
when the listing has them in the shape Spike proves), and states
the layout of its static link (`{pfx}Λ`, `Scc/Cert/LinkX64.lean`) with its
well-formedness, abort labels, image and the loader's checks, by
`decide +kernel`. `wide`, if any, is the one-word fragment check of the
listing (`Scc.Cert.WideCheckX64.check`, from `scc-x64`): a program outside
the fragment is refused, and the file states `{pfx}_wide`, its cells'
program in the fragment (`Scc.Cert.WideX64.wideIn`, by `decide +kernel`).
`imms`, if any, is the program's immediate table (`{pfx}Imms`,
`Scc.Cert.Place.renderImms`): the file states it and sets `{pfx}Λ`'s
`imms` to it. `frames`, if any, is the text of the stack depth limit
(`{pfx}Frames`, `Scc.Lower.StackBudget.render`), stated before the layout;
`need`, if any, the text of the stack need table (`{pfx}Need` and its
check `{pfx}Need_ok`, `Scc.Lower.renderNeed`), stated after the runtime. -/
def codeX64 (name asm : String) (sizes : Option (List Nat × List (String × Nat)))
    (wide : Option (String → Except String Unit) := none) (imms : Option String := none)
    (frames : Option String := none) (need : Option String := none) :
    Except String String := do
  let some (szs, offs) := sizes | throw "the x64 code check needs the instruction sizes"
  if let some w := wide then w asm
  let (base, pfx) := codeName name
  let r ← analyse X64.isa asm (some szs)
  let tables ← renderCode r pfx (sized := true)
  let hasPrintL := (asm.splitOn "\n").contains "wc_printL:"
  -- the label offsets in the text's order, the code cells' (`sizeOkL`)
  let offs := textOrder asm offs
  let offsT := ", ".intercalate (offs.map fun (l, o) => s!"({Gen.quoteLine l}, {o})")
  -- `scc_rt_main`'s tail as `Spike.Lib.X64.MainTail` has it (`Scc.Cert.Rt.X64.Abort.mainIn`)
  let hasMainTail := (asm.splitOn ".Lscc_rt_main.x3:\n\tmovq %rax, -48(%rbp)\n\tmovq -48(%rbp), %rdi\n\tmovl $231, %eax\n\tsyscall\n").length > 1
  let mainThm := if hasMainTail then s!"
/-- The tail of `scc_rt_main` (`Scc/Cert/Rt/X64Abort.lean`). -/
theorem {pfx}_mainTail : Scc.Cert.Rt.X64.Abort.mainIn {pfx}Cells = true := by decide +kernel
" else ""
  let printLImport := if hasPrintL then "\nimport Scc.Cert.Rt.X64PrintL" else ""
  let wideImport := if wide.isSome then "\nimport Scc.Cert.Rt.WideX64" else ""
  let wideThm := if wide.isSome then s!"
/-- The program writes words only (`Scc/Cert/Rt/WideX64.lean`,
`wideSt_threadAt`). -/
theorem {pfx}_wide : Scc.Cert.WideX64.wideIn ({pfx}Cells.map (·.1)) = true := by decide +kernel
" else ""
  let printLThm := if hasPrintL then s!"
/-- `wc_printL`'s code and labels (`Scc/Cert/Rt/X64PrintL.lean`). -/
theorem {pfx}_printL : Scc.Cert.Rt.X64.PrintL.printLIn {pfx}Cells = true := by decide +kernel
" else ""
  let needTextX := match need with
    | some t => s!"/-! ## The stack need -/\n\n{t}\n"
    | none => ""
  return s!"import Scc.Cert.Rt.CodeX64
import Scc.Cert.LinkX64
import Scc.Cert.Rt.X64Print
import Scc.Cert.Rt.X64Abort
import Scc.Cert.Rt.X64MorestackIn
import Scc.Cert.NeedX64{printLImport}{wideImport}

/-!
# Every block of `{base}`'s x64 code at its place

Generated by `scc --arch x64 --code`. `{pfx}Asm` is the text `scc` wrote with
the length of each instruction and the offsets of its labels as GNU `as`
assembled it (untrusted: the canonical loader checks them, `SizeCheck`);
`{pfx}Cells` and `{pfx}Secs` are the code cells and the data sections the
canonical loader reads from it (`Scc.Sem.X64.cellsOf`,
`Scc.Sem.dataSections`, at elaboration time); the kernel cannot run the
parsers, so these two equations are the trust boundary, checked by
evaluation (`#guard`).

Per function, the table of its `block_spec` blocks (`scc --blocks`, named in
comments), grouped by the label before them with their instruction counts
and byte offsets from it, in program order; `{pfx}T_in` checks them all
against `{pfx}Cells` by `kernel_rfl` (`blocksIn`,
`Scc/Cert/Rt/CodeX64.lean`): every block is code at its label and offset in
every valid layout of the cells (`codeAt_of_blocksIn`), the loaded thread's
included (`lays_threadAt`, `endPc_threadAt`). `{pfx}_print`, `{pfx}_abort`
and `{pfx}_morestack` (with `{pfx}_mainTail` and `{pfx}_printL`, when
stated) check the code the runtime's proofs take as hypotheses (`Scc/Cert/Rt/X64Print.lean`, `X64Abort.lean`,
`X64MorestackIn.lean`).

`{pfx}Λ` is the layout of the program's static link (`Scc.Cert.Link`),
with the program's immediate table `{pfx}Imms` when stated (`Layout.imms`):
`{pfx}Λ_wf` its well-formedness, `{pfx}Λ_aborts` its abort labels in the
code, `{pfx}Λ_image` each data symbol's item in its image
(`Scc.Cert.Link.image_symbols`), `{pfx}Λ_load` the canonical loader's checks
of it (but the entry state's), with a valid layout of the loaded thread
(`validLayout_of_loadOk`). `{pfx}_wide`, if stated, puts the program in the
one-word fragment (`Scc.Cert.WideX64.wideIn`), so its certification
semantics writes words only (`wideSt_threadAt`). `{pfx}Need`, if stated, is
the stack need of its stack-checked functions, checked on `{pfx}Cells`
(`{pfx}Need_ok`, `Scc/Cert/NeedX64.lean`).
-/

namespace SccCode

open Kraken Kraken.Promising.X64 Kraken.X64.Parser Scc.Cert.Rt.X64 Scc.Cert.Link.X64

/-- The assembler text `scc --arch x64` wrote, verbatim. -/
def {pfx}Text : String := {Gen.quote asm}

/-- The text with its instruction lengths and label offsets, as GNU `as`
assembled it (untrusted). -/
def {pfx}Asm : Scc.Sem.X64.Asm where
  text := {pfx}Text
  sizes := {szs}
  labelOffs := [{offsT}]

/-- The code cells the canonical loader lays out from `{pfx}Asm`. -/
def {pfx}Cells : List (Directive × Nat) := scc_x64_cells% {pfx}Asm

/-- The data sections the canonical loader reads from `{pfx}Text`. -/
def {pfx}Secs : Scc.Sem.DataSecs := scc_data_secs% {pfx}Text

#guard parsesTo {pfx}Asm {pfx}Cells {pfx}Secs
{wideThm}
{tables}
/-! ## The runtime -/

/-- `scc_rt_print`'s code and labels (`Scc/Cert/Rt/X64Print.lean`). -/
theorem {pfx}_print : Scc.Cert.Rt.X64.Print.printIn {pfx}Cells = true := by decide +kernel

/-- `scc_rt_abort`'s code and labels (`Scc/Cert/Rt/X64Abort.lean`), stub by
stub (`abortIn_of`: one declaration each bounds the kernel's memory). -/
theorem {pfx}_abort_overflow : Scc.Cert.Rt.X64.Abort.stubIn {pfx}Cells
    Spike.Lib.X64.Abort.overflow Spike.Lib.X64.Abort.x1Overflow = true := by decide +kernel

theorem {pfx}_abort_heap : Scc.Cert.Rt.X64.Abort.stubIn {pfx}Cells
    Spike.Lib.X64.Abort.heap Spike.Lib.X64.Abort.x1Heap = true := by decide +kernel

theorem {pfx}_abort_stack : Scc.Cert.Rt.X64.Abort.stubIn {pfx}Cells
    Spike.Lib.X64.Abort.stack Spike.Lib.X64.Abort.x1Stack = true := by decide +kernel

theorem {pfx}_abort_write : Scc.Cert.Rt.X64.Abort.stubIn {pfx}Cells
    Spike.Lib.X64.Abort.write Spike.Lib.X64.Abort.x1Write = true := by decide +kernel

theorem {pfx}_abort_threads : Scc.Cert.Rt.X64.Abort.stubIn {pfx}Cells
    Spike.Lib.X64.Abort.threads Spike.Lib.X64.Abort.x1Threads = true := by decide +kernel

theorem {pfx}_abort_disp : Scc.Cert.Rt.X64.Abort.dispIn {pfx}Cells = true := by decide +kernel

theorem {pfx}_abort : Scc.Cert.Rt.X64.Abort.abortIn {pfx}Cells = true :=
  Scc.Cert.Rt.X64.Abort.abortIn_of {pfx}_abort_overflow {pfx}_abort_heap {pfx}_abort_stack
    {pfx}_abort_write {pfx}_abort_threads {pfx}_abort_disp

/-- `scc_rt_morestack`'s code (`Scc/Cert/Rt/X64MorestackIn.lean`). -/
theorem {pfx}_morestack : Scc.Cert.Rt.X64.Morestack.morestackIn {pfx}Cells = true := by decide +kernel
{mainThm}{printLThm}
{needTextX}/-! ## The layout -/

{frames.getD ""}{layoutDef imms pfx s!"linkOf {pfx}Cells {pfx}Secs"}
theorem {pfx}Λ_wf : {pfx}Λ.WF := Scc.Cert.Link.wfB_sound (by decide +kernel)

theorem {pfx}Λ_aborts : abortsIn {pfx}Cells {pfx}Λ = true := by decide +kernel

theorem {pfx}Λ_image : imageIn {pfx}Cells {pfx}Secs {pfx}Λ = true := by decide +kernel

/-! The loader's checks part by part (`loadOk_of`: one declaration each
bounds the kernel's memory). -/

theorem {pfx}Λ_size : sizeOkW (Int64.ofNat {pfx}Λ.code.lo) {pfx}Cells {pfx}Asm.labelOffs = true := by
  decide +kernel

theorem {pfx}Λ_labels : labelsNodupL (Int64.ofNat {pfx}Λ.code.lo) {pfx}Cells = true := by decide +kernel

theorem {pfx}Λ_quads : quadsOkL (Int64.ofNat {pfx}Λ.code.lo) {pfx}Cells {pfx}Secs.rodata = true := by
  decide +kernel

theorem {pfx}Λ_syms : (Scc.Sem.rodataFits {pfx}Λ {pfx}Secs.rodata && Scc.Sem.symsAgree {pfx}Λ {pfx}Secs.rodata &&
    Scc.Sem.symsAbove {pfx}Λ.code.lo (Scc.Sem.X64.codeEnd {pfx}Λ.code.lo {pfx}Cells) (Scc.Sem.loadSyms {pfx}Λ {pfx}Secs.rodata) &&
    symsAround {pfx}Λ.code.lo {pfx}Cells (Scc.Sem.loadSyms {pfx}Λ {pfx}Secs.rodata) &&
    noClash {pfx}Λ.code.lo {pfx}Cells (Scc.Sem.loadSyms {pfx}Λ {pfx}Secs.rodata) &&
    decide (Scc.Sem.X64.codeEnd {pfx}Λ.code.lo {pfx}Cells < 2 ^ 64)) = true := by decide +kernel

theorem {pfx}Λ_load : loadOk {pfx}Λ {pfx}Cells {pfx}Secs {pfx}Asm.labelOffs = true :=
  loadOk_of {pfx}Λ_size {pfx}Λ_labels {pfx}Λ_quads {pfx}Λ_syms

end SccCode
"

/-- **The code check file** of an AArch64 listing (`scc --code`), for the
input file `name`: self-contained, it embeds the listing (`{pfx}Asm`),
parses it as the canonical loader does (`{pfx}Prog`, `{pfx}Secs`, by
`scc_arm_text%` and `scc_data_secs%` at elaboration time, checked by
`#guard`), checks every block at its place (`renderCode`) and the
runtime's never-returning code (`abortIn`, and `mainIn`/`mainIn0` when the
listing has `scc_rt_main`'s tail in a shape Spike proves), `hello.w`'s
`wc_printL` by `printLIn` when the listing has it, and states the
layout of its static link (`{pfx}Λ`, `Scc/Cert/LinkA64.lean`) with its
well-formedness, its abort labels, its image and the loader's checks, by
`decide +kernel`; the prefix `pfx` is the input's base name as an
identifier. `wide`, if any, is the one-word fragment check of the listing
(`Scc.Cert.WideCheckA64.check`, from `scc-arm`): a program outside the
fragment is refused, and the file states `{pfx}_wide`, its program in the
fragment (`Scc.Cert.WideA64.wideIn`, by `decide +kernel`). `imms`, if any,
is the program's immediate table (`{pfx}Imms`, `Scc.Cert.Place.renderImms`):
the file states it and sets `{pfx}Λ`'s `imms` to it. `frames`, if any, is
the text of the stack depth limit (`{pfx}Frames`,
`Scc.Lower.StackBudget.render`), stated before the layout. `need`, if any,
is the text of the AArch64 stack need table (`{pfx}Need` and its check
`{pfx}Need_ok`, `Scc.Lower.renderNeed`), stated after the blocks. -/
def code (arch : Arch) (name asm : String) (wide : Option (String → Except String Unit) := none)
    (sizes : Option (List Nat × List (String × Nat)) := none) (imms : Option String := none)
    (frames : Option String := none) (need : Option String := none) :
    Except String String := do
  if arch matches .x64 then return ← codeX64 name asm sizes wide imms frames need
  if let some w := wide then w asm
  let (base, pfx) := codeName name
  let r ← analyse A64.isa asm
  let tables ← renderCode r pfx
  let wideThm := if wide.isSome then s!"
/-- The program writes words only (`Scc/Cert/Rt/WideA64.lean`). -/
theorem {pfx}_wide : Scc.Cert.WideA64.wideIn {pfx}Prog = true := by decide +kernel
" else ""
  -- `scc_rt_main`'s tail in a shape Spike proves (`Scc.Cert.Rt.A64.Abort`:
  -- after a setup block `mainIn`, without one `mainIn0`)
  let tailOf (sp k : String) : String :=
    s!".L1_scc_rt_main.{sp}:\n\tstr x0, [sp, #{k}]\n\tldr x0, [sp, #{k}]\n\tmovz x8, #94\n\tsvc #0\n"
  let mainThm :=
    if (asm.splitOn (tailOf "sp1" "40")).length > 1 then s!"
/-- The tail of `scc_rt_main`, after a setup block (`Scc/Cert/Rt/A64Abort.lean`). -/
theorem {pfx}_mainTail : Scc.Cert.Rt.A64.Abort.mainIn {pfx}Prog = true := by decide +kernel
"
    else if (asm.splitOn (tailOf "sp0" "8")).length > 1 then s!"
/-- The tail of `scc_rt_main`, without a setup block (`Scc/Cert/Rt/A64Abort.lean`). -/
theorem {pfx}_mainTail : Scc.Cert.Rt.A64.Abort.mainIn0 {pfx}Prog = true := by decide +kernel
"
    else ""
  -- `hello.w`'s `wc_printL` (`Scc.Cert.Rt.A64.PrintL`)
  let hasPrintL := (asm.splitOn "\n").contains "wc_printL:"
  let printLImport := if hasPrintL then "\nimport Scc.Cert.Rt.A64PrintL" else ""
  let printLThm := if hasPrintL then s!"
/-- `wc_printL`'s code and labels (`Scc/Cert/Rt/A64PrintL.lean`). -/
theorem {pfx}_printL : Scc.Cert.Rt.A64.PrintL.printLIn {pfx}Prog = true := by decide +kernel
" else ""
  let needText := match need with
    | some t => s!"/-! ## The stack need -/\n\n{t}\n"
    | none => ""
  return s!"import Scc.Cert.Rt.CodeA64
import Scc.Cert.LinkA64
import Scc.Cert.Rt.WideA64
import Scc.Cert.Rt.A64Abort
import Scc.Cert.NeedA64{printLImport}

/-!
# Every block of `{base}`'s AArch64 code at its place

Generated by `scc --code`. `{pfx}Prog` and `{pfx}Secs` are the program and
the data sections the canonical loader reads from the listing `{pfx}Asm`
(`Scc.Sem.A64.textProgram`, `Scc.Sem.dataSections`, at elaboration time); the
kernel cannot run the parsers, so these two equations are the trust boundary,
checked by evaluation (`#guard`).

Per function, the table of its `block_spec` blocks (`scc --blocks`, named in
comments), grouped by the label before them with their instruction counts
from it, in program order; `{pfx}T_in` checks them all against `{pfx}Prog` by
`kernel_rfl` (`{codeCheck}`, `Scc/Cert/Rt/CodeA64.lean`): every block is code
at its label and offset in every layout of the program
(`codeAt_of_blocksIn`), the loaded thread's included (`lays_threadAt`).

`{pfx}Λ` is the layout of the program's static link (`Scc.Cert.Link`),
with the program's immediate table `{pfx}Imms` when stated (`Layout.imms`):
`{pfx}Λ_wf` its well-formedness, `{pfx}Λ_aborts` its abort labels in the
program, `{pfx}Λ_image` each data symbol's item in its image
(`Scc.Cert.Link.image_symbols`), `{pfx}Λ_load` the canonical loader's checks
of it (but the entry state's), with a valid layout of the loaded thread
(`validLayout_of_loadOk`). `{pfx}_wide`, if stated, puts the program in the
one-word fragment (`Scc.Cert.WideA64.wideIn`), so its certification
semantics writes words only (`wideSt_threadAt`). `{pfx}_abort` checks the
abort stubs and `scc_rt_abort`, `{pfx}_print` `scc_rt_print`
(`Scc/Cert/Rt/A64Print.lean`), and `{pfx}_mainTail`, when stated (the
listing has it in a shape Spike proves), the tail of `scc_rt_main`: the
code the runtime's proofs take as hypotheses (`Scc/Cert/Rt/A64Abort.lean`);
`{pfx}_printL`, when stated, `wc_printL`'s (`Scc/Cert/Rt/A64PrintL.lean`).
`{pfx}Need`, if stated, is
the stack need of its stack-checked functions, checked on `{pfx}Prog`
(`{pfx}Need_ok`, `Scc/Cert/NeedA64.lean`).
-/

namespace SccCode

open Kraken Kraken.Promising.AArch64 Kraken.AArch64.Parser Scc.Cert.Rt.A64 Scc.Cert.Link.A64

/-- The assembler text `scc --arch arm` wrote, verbatim. -/
def {pfx}Asm : String := {Gen.quote asm}

/-- The program the canonical loader reads from `{pfx}Asm`. -/
def {pfx}Prog : Program := scc_arm_text% {pfx}Asm

/-- The data sections the canonical loader reads from `{pfx}Asm`. -/
def {pfx}Secs : Scc.Sem.DataSecs := scc_data_secs% {pfx}Asm

#guard parsesTo {pfx}Asm {pfx}Prog {pfx}Secs
{wideThm}
{tables}
/-! ## The runtime -/

/-- The abort stubs and `scc_rt_abort`'s code and labels
(`Scc/Cert/Rt/A64Abort.lean`). -/
theorem {pfx}_abort : Scc.Cert.Rt.A64.Abort.abortIn {pfx}Prog = true := by decide +kernel

/-- `scc_rt_print`'s code and labels (`Scc/Cert/Rt/A64Print.lean`). -/
theorem {pfx}_print : Scc.Cert.Rt.A64.Print.printIn {pfx}Prog = true := by decide +kernel
{mainThm}{printLThm}
{needText}/-! ## The layout -/

{frames.getD ""}{layoutDef imms pfx s!"linkOf {pfx}Prog {pfx}Secs"}
theorem {pfx}Λ_wf : {pfx}Λ.WF := Scc.Cert.Link.wfB_sound (by decide +kernel)

theorem {pfx}Λ_aborts : abortsIn {pfx}Prog {pfx}Λ = true := by decide +kernel

theorem {pfx}Λ_image : imageIn {pfx}Prog {pfx}Secs {pfx}Λ = true := by decide +kernel

theorem {pfx}Λ_load : loadOk {pfx}Λ {pfx}Prog {pfx}Secs = true := by decide +kernel

end SccCode
"

/-- The `block_spec` commands of a listing (or the error), for `#eval`. -/
def blocks (arch : Arch) (asm : String) (sizes : Option (List Nat) := none) : String :=
  match run arch asm sizes with
  | .ok (lines, _) => lines
  | .error m => s!"error: {m}"

end Scc.Cert.Blocks

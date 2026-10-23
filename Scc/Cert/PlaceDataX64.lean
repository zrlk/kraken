import Scc.Cert.PlaceOKX64
import Scc.Lower.SpecX64

/-!
# The x86-64 placement data of scc's output, computed

The x86-64 twin of `Scc/Cert/PlaceDataA64.lean`. `Out.ofEmitted e sizes
labelOffs`: scc's x86-64 output (`Scc.Lower.X64.Emitted`) as the output
`PlaceOK` checks (`Scc/Cert/PlaceOKX64.lean`): the code cells (the
instruction list at the assembler's sizes, `sizedCells`, as the canonical
loader lays it out, `Scc.Sem.X64.cellsOf`), the data sections, the
assembler's label offsets, and the placement data computed from the cells
and the IR by a function the kernel evaluates, so that
`placeOK cfg (Out.ofEmitted (lowerAll cfg p) sizes labelOffs)` is decided on
scc's own pipeline, with no table as an input. The sizes and the label
offsets are the assembler's (`Scc.Cert.Sizes.sizesOf`): untrusted, checked
by A2 (`sizeOkL` inside `loadOk`); with sizes that do not fit the
instruction list, the cells are empty and no component holds.

The placement data (`placeDataOf`):

* **the block table with its static offsets** (`blocksOf?`): the analysis of
  `scc --blocks` (`Scc.Cert.Blocks.analyse` with `Blocks.X64.isa` and the
  size table) over the cells instead of the listing's text. A function
  starts at a label of a function the listing declares (`.type NAME,
  @function`: `_start`, the IR's functions and, with growable stacks,
  `scc_rt_morestack`) or at the first label. Each instruction is classified
  as the text analysis classifies its printed form
  (`Scc.Emit.X64.ppDirective`): `clsOf` follows `Blocks.X64.classify` case
  by case, `dstsOf` is `Blocks.X64.xDsts` (the register the last operand
  names, and the ones the instruction writes besides); jump and call targets are taken to be labels in the text's sense
  (`Blocks.isLab`), as every label scc writes is. A row's place is its cell
  count and byte offset from its label (the cells' sizes; labels have
  none); its cells are the output's. The static offsets flow to a fixpoint
  per function (`fixOffsets`, `Blocks.offsets`, from `%rsp` at 8), the
  regions are the accessed offsets per epoch (`regionsOf`, the entry
  epoch's from `[0, 16)`), and the blocks are cut where `Blocks.analyse`
  cuts them (`cutItem`); the rows are grouped by label in program order
  (`fnGrps`), as `Blocks.renderCode` writes the table, each group with the
  indices from its label of the cells the analysis puts in no row
  (`OGrp.ev`, which A3's coverage checks); a label whose run has no row
  has no group;
* **the stack need table**: `Emitted.need` (`Scc.Lower.stackNeed`), empty
  with non-tail recursion;
* **the shape of `scc_rt_main`'s tail**: after a setup block exactly when
  the entry point takes the setup block's result (`EntryArg.setupTid`).

Nothing here is trusted: `PlaceOK` checks every row it reads (A3, A5). The
test `Spike/Test/X64PlaceData.lean` checks the computed tables against the
ones `scc --code` and `Scc.Cert.Blocks.offsX64` write.

The offsets' fixpoint has fuel (100 passes per function, `fixOffsets`); a
function whose offsets do not settle within it makes `blocksOf?` `none`,
and the block table is then empty, which A3's coverage rejects for any
listing with a row to place: the check fails closed.

To decide `placeOK` by the kernel, the source program must be stated as a
term (as `Spike/Test/A64Hello1PlaceOKE.lean` does): the frontend's parser is
`partial`, so the kernel does not reduce `Frontend.run`.
-/

namespace Scc.Cert.PlaceOK.X64

open Kraken Kraken.Promising Kraken.Promising.X64

namespace Data

/-! ## Classification -/

/-- The 64-bit register a register operand is part of (`Blocks.X64.base`
of its printed name). -/
def baseR {w : Width} : Reg w → Reg64
  | .low r _ => r
  | .ah => .rax | .bh => .rbx | .ch => .rcx | .dh => .rdx

/-- A register operand prints a name of `Blocks.X64.r64` (a 64-bit one). -/
def is64 {w : Width} : Reg w → Bool
  | .low _ .W64 => true
  | _ => false

/-- A memory operand prints `n(%b)` or `(%b)` (`Blocks.X64.mem?`): the
displacement and the base. -/
def memOf (a : AddrExpr) : Option (Int × Reg64) :=
  match a.base, a.idx, a.disp with
  | some (.reg b), none, .int64 n => some (n.toInt, b)
  | _, _, _ => none

/-- A register-or-memory operand prints a register. -/
def rmReg {w : Width} : RegOrMem w → Option (Reg w)
  | .reg r => some r
  | .mem _ => none

/-- An operand prints a memory operand (a `(`). -/
def opMem {w : Width} : Operand w → Bool
  | .regOrMem (.mem _) => true
  | _ => false

/-- An operand prints a register. -/
def opReg {w : Width} : Operand w → Option (Reg w)
  | .regOrMem (.reg r) => some r
  | _ => none

/-- An operand prints a decimal immediate (`Blocks.X64.imm?`). -/
def opImm {w : Width} : Operand w → Option Int
  | .imm (.int64 i) => some i.toInt
  | _ => none

/-- A register-or-memory operand prints a memory operand. -/
def rmMem {w : Width} : RegOrMem w → Bool
  | .mem _ => true
  | .reg _ => false

/-- The classes of `Blocks.Cls` on x86-64: a frame slot load or store
(`movq n(%b), %r`, `movq %r, n(%b)`), a push or pop of a 64-bit register, a
register operation writing `d` (`src`: `Info.from`), a branch, a call,
`ret`, or an instruction outside the blocks. -/
inductive K where
  | ld (r b : Reg64) (n : Int)
  | st (b : Reg64) (n : Int)
  | push
  | pop (r : Reg64)
  | reg (d : Option Reg64) (src : Option (Reg64 × Int))
  | jmp (l : Label)
  | jcc (l : Label)
  | call (l : Label)
  | ret
  | x
  deriving DecidableEq

/-- A terminator (`Blocks.Cls.isTerm`). -/
def K.isTerm : K → Bool
  | .jmp _ | .jcc _ | .call _ | .ret => true
  | _ => false

/-- `Blocks.X64.classify`'s `add`/`sub`/`cmp` case (`adc`/`sbb` are not
printed): a register destination and a register or decimal source; `addq`
and `subq` of an immediate to a 64-bit register set it from itself. -/
def arithK {w : Width} (isCmp : Bool) (neg : Option Bool) (d : RegOrMem w) (s : Operand w) : K :=
  match rmReg d with
  | some dr =>
    let src : Option (Reg64 × Int) :=
      match opImm s, neg with
      | some k, some ng => if w == .W64 && is64 dr then some (baseR dr, if ng then -k else k) else none
      | _, _ => none
    if (opReg s).isSome || (opImm s).isSome then .reg (if isCmp then none else some (baseR dr)) src
    else .x
  | none => .x

/-- **The class of an operation** (64-bit addresses), as
`Blocks.X64.classify` classifies its printed form (`Scc.Emit.X64.ppOp`).
Every memory operand other than `movq`'s frame slots puts an instruction
outside the blocks, as do the flag-undefined operations, `%fs`, atomics,
`syscall` and `ud2`. -/
def opK {w : Width} : Operation w → K
  | .mov d s =>
    let movq := w == .W64 && !(match d, s with
      | .reg _, .imm (.int64 i) => Scc.Emit.X64.needsMovabs i
      | _, _ => false)
    let slot : Option K :=
      if movq then
        match s, d with
        | .regOrMem (.mem a), .reg r => (memOf a).map fun (n, b) => .ld (baseR r) b n
        | .regOrMem (.reg _), .mem a => (memOf a).map fun (n, b) => .st b n
        | _, _ => none
      else none
    match slot with
    | some k => k
    | none =>
      if rmMem d || opMem s then .x else
      match rmReg d, s with
      | some dr, .regOrMem (.reg sr) =>
        .reg (some (baseR dr)) (if movq && is64 sr && is64 dr then some (baseR sr, 0) else none)
      | some dr, .imm (.int64 _) => .reg (some (baseR dr)) none
      | _, _ => .x
  | @Operation.movsx _ w' d s | @Operation.movzx _ w' d s =>
    if rmMem d || rmMem s then .x else
    if w' != .W64 && w != .W8 then
      match rmReg d, rmReg s with
      | some dr, some _ => .reg (some (baseR dr)) none
      | _, _ => .x
    else .x
  | .push s =>
    match w, s with
    | .W64, .regOrMem (.reg (.low _ .W64)) => .push
    | _, _ => .x
  | .pop d =>
    match w, d with
    | .W64, .reg (.low r .W64) => .pop r
    | _, _ => .x
  | .setcc _ d => match d with
    | .reg r => .reg (some (baseR r)) none
    | .mem _ => .x
  | .cmovcc _ d s => if rmMem s then .x else .reg (some (baseR d)) none
  | .lea d a =>
    match a.base with
    | some .rip => .x
    | _ =>
      if w == .W64 then
        match memOf a with
        | some (n, b) => .reg (some (baseR d)) (some (b, n))
        | none => .x
      else .x
  | .add d s => if rmMem d || opMem s then .x else arithK false (some false) d s
  | .sub d s => if rmMem d || opMem s then .x else arithK false (some true) d s
  | .cmp a b => if rmMem a || opMem b then .x else arithK true none a b
  | .neg d | .not d => match d with
    | .reg r => .reg (some (baseR r)) none
    | .mem _ => .x
  | .jcc _ l => .jcc l
  | .jmp (.rel (.sub (.label l) .after_current_instruction)) => .jmp l
  | .call (.rel (.sub (.label l) .after_current_instruction)) => .call l
  | .ret => .ret
  | .nop 1 => .reg none none
  | .cqo => if w == .W64 then .reg (some .rdx) none else .x
  | _ => .x

-- `cqto` writes `%rdx` and is covered (Kraken's `RegOnly .cqo`): it stays in
-- its row, not a single instruction (A3's `evOk` would reject it).
#guard opK (w := .W64) .cqo == .reg (some .rdx) none && opK (w := .W32) .cqo == .x

/-- **The class of an instruction** (`opK` of its operation, 64-bit
addresses; any other form is not printed). -/
def clsOf : Instr → K
  | .regular .W64 _ op => opK op
  | _ => .x

/-- The register a register-or-memory operand prints, if any. -/
def rmDst {w : Width} : RegOrMem w → Option Reg64
  | .reg r => some (baseR r)
  | .mem _ => none

/-- The register an operand prints, if any. -/
def opDst {w : Width} : Operand w → Option Reg64
  | .regOrMem rm => rmDst rm
  | .imm _ => none

/-- **The register an instruction may write**, as `Blocks.X64.xDst` reads
its printed form: the register its last operand names, if it is one. -/
def dstOf : Instr → Option Reg64
  | .regular .W64 _ op => match op with
    | .mov d _ | .movsx d _ | .movzx d _ | .pop d | .setcc _ d | .add d _ | .sub d _ | .and d _
    | .or d _ | .xor d _ | .shl d _ | .shr d _ | .sar d _ | .neg d | .not d | .cmp d _ | .test d _
    | .mul d | .div d | .idiv d | .xchg _ d | .xadd _ d _ => rmDst d
    | .imul none s _ => rmDst s
    | .push s => opDst s
    | .cmovcc _ d _ | .lea d _ | .tzcnt d _ | .popcnt d _ => some (baseR d)
    | .jmp (.reg r) | .call (.reg r) => some (baseR r)
    | .movfs (.reg r) _ => some (baseR r)
    | _ => none
  | _ => none

/-- **The registers an instruction may write**, as `Blocks.X64.xDsts`
reads its printed form: `dstOf`'s, and the ones it writes besides (`mul`,
`div`, `idiv` and one-operand `imul`: `rax` and `rdx` instead, `rax` only at
byte width; `cqo`: `rdx`; `xchg` and `xadd`: their register operand too;
`cmpxchg`: `rax` too; `cmpxchg16b`: `rax` and `rdx`). -/
def dstsOf : Instr → List Reg64
  | i@(.regular .W64 w op) => match op with
    | .mul _ | .div _ | .idiv _ | .imul1 _ => if w == .W8 then [.rax] else [.rax, .rdx]
    | .cqo => [.rdx]
    | .xchg r m => baseR r :: (rmDst m).toList
    | .xadd _ d s => baseR s :: (rmDst d).toList
    | .cmpxchg _ d _ => .rax :: (rmDst d).toList
    | _ => (dstOf i).toList
  | .avx .W64 _ (.cmpxchg16b _ _) => [.rax, .rdx]
  | i => (dstOf i).toList

/-- `ud2`. -/
def isUd2 : Instr → Bool
  | .regular .W64 _ .ud2 => true
  | _ => false

/-- `syscall`. -/
def isSyscall : Instr → Bool
  | .regular .W64 _ .syscall => true
  | _ => false

/-- `andq $k, %rsp` (`Blocks.X64.isa.switch`'s second case). -/
def isAndRsp : Instr → Bool
  | .regular .W64 .W64 (.and (.reg (.low .rsp .W64)) (.imm (.int64 _))) => true
  | _ => false

/-! ## Static offsets -/

/-- `Blocks.SO` over Kraken's registers: `%rsp`'s offset, the registers'
(most recently set first), the epoch. -/
structure SO where
  sp : Int
  regs : List (Reg64 × Int)
  epoch : Nat
  deriving DecidableEq

/-- `Blocks.Pt`. -/
inductive Pt where
  | none
  | unknown
  | known (o : SO)
  deriving DecidableEq

def SO.get (o : SO) (r : Reg64) : Option Int :=
  if r == .rsp then some o.sp else Spike.Lib.lk o.regs r

def SO.kill (o : SO) (r : Reg64) : SO := { o with regs := o.regs.filter (·.1 != r) }

def SO.set (o : SO) (r : Reg64) (k : Int) : SO :=
  if r == .rsp then { o with sp := k } else { o with regs := (r, k) :: (o.kill r).regs }

/-- `Blocks.Pt.meet`. -/
def Pt.meet : Pt → Pt → Pt
  | .none, b => b
  | a, .none => a
  | .known a, .known b =>
    if a.sp == b.sp && a.epoch == b.epoch then
      .known { a with regs := a.regs.filter fun e => Spike.Lib.lk b.regs e.1 == some e.2 }
    else .unknown
  | _, _ => .unknown

/-- `Blocks.X64.step`: the offsets after a covered instruction (none: not
covered at these offsets) and the offset it accesses. -/
def step (o : SO) : K → Option SO × Option Int
  | .ld r b n =>
    match o.get b with
    | some kb => if r == .rsp then (none, none) else (some (o.kill r), some (kb + n))
    | none => (none, none)
  | .st b n =>
    match o.get b with
    | some kb => (some o, some (kb + n))
    | none => (none, none)
  | .push => (some { o with sp := o.sp - 8 }, some (o.sp - 8))
  | .pop r => if r == .rsp then (none, none) else (some { o.kill r with sp := o.sp + 8 }, some o.sp)
  | .reg d src =>
    let viaSrc : Option SO := match src, d with
      | some (s, n), some d => (o.get s).map fun k => o.set d (k + n)
      | _, _ => none
    match viaSrc with
    | some o' => (some o', none)
    | none => match d with
      | none => (some o, none)
      | some d => if d == .rsp then (none, none) else (some (o.kill d), none)
  | .jmp _ | .jcc _ => (some o, none)
  | .call _ => (some { o with sp := o.sp - 8 }, some (o.sp - 8))
  | .ret => (some { o with sp := o.sp + 8 }, some o.sp)
  | .x => (none, none)

/-- `Blocks.X64.isa.switch`: a register operation writing `%rsp` that
`step` does not cover, or `andq $k, %rsp`. -/
def switch (o : SO) (i : Instr) : K → Bool
  | .reg d src => d == some .rsp && (step o (.reg d src)).1.isNone
  | _ => isAndRsp i

/-- `Blocks.X64.isa.passX`: the offsets after an instruction outside the
blocks. -/
def passX (o : SO) (i : Instr) : Pt :=
  if isUd2 i then .none else
  let ds := dstsOf i
  if ds.contains .rsp then .unknown
  else if isSyscall i then .known (((o.kill .rax).kill .rcx).kill .r11)
  else .known (ds.foldl SO.kill o)

-- `xchg`, `lock xadd` and `lock cmpxchg` with a memory operand forget the
-- registers they write besides their last operand (`rax` holding a stack
-- offset here), as `Blocks.X64.isa.passX` does; `mulq` forgets `rax` and
-- `rdx`, not its operand.
#guard
  let o : SO := ⟨0, [(.rax, 8), (.rdx, 16), (.rcx, 24)], 0⟩
  let m : RegOrMem .W64 := .mem ⟨some (.reg .rcx), none, .int64 0⟩
  let r (x : Reg64) : Reg .W64 := .low x .W64
  passX o (.regular .W64 .W64 (.xchg (r .rax) m)) = .known ⟨0, [(.rdx, 16), (.rcx, 24)], 0⟩ &&
  passX o (.regular .W64 .W64 (.xadd true m (r .rax))) = .known ⟨0, [(.rdx, 16), (.rcx, 24)], 0⟩ &&
  passX o (.regular .W64 .W64 (.cmpxchg true m (r .rdx))) = .known ⟨0, [(.rdx, 16), (.rcx, 24)], 0⟩ &&
  passX o (.regular .W64 .W64 (.mul (.reg (r .rcx)))) = .known ⟨0, [(.rcx, 24)], 0⟩

/-- `Blocks.X64.isa.afterCall`: the offsets before the call, the
caller-saved registers forgotten. -/
def afterCall (o : SO) : Pt :=
  .known ([Reg64.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11].foldl SO.kill o)

/-! ## Functions -/

/-! Labels are compared by their keys (`Rt.X64.key`, injective), computed
once per occurrence: comparing the strings themselves is slow in the
kernel. -/

/-- The value at key `k` of an association list. -/
def lkN {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (j, a) :: l, k => if Nat.beq j k then some a else lkN l k

/-- An item of a function: a label (with its key), or an instruction cell
with its class (`clsOf`) and the key of the label it branches to. -/
inductive It where
  | lab (l : Label) (key : Nat)
  | ins (i : Instr) (z : Nat) (c : K) (tgt : Nat)

/-- The item of an instruction cell. -/
def It.ofIns (i : Instr) (z : Nat) : It :=
  let c := clsOf i
  .ins i z c (match c with | .jmp l | .jcc l => Rt.X64.key l | _ => 0)

/-- **The functions of the cells** (`Blocks.functions`): a function starts
at a label whose key is in `decl` or at the first label; cells before the
first label are dropped. -/
def splitFns (decl : List Nat) (cells : List (Directive × Nat)) : List (Label × List It) :=
  go cells none []
where
  go : List (Directive × Nat) → Option (Label × List It) → List (Label × List It) →
      List (Label × List It)
    | [], cur, acc => (match cur with | some (f, its) => (f, its.reverse) :: acc | none => acc).reverse
    | (.label l, _) :: ds, none, acc => go ds (some (l, [.lab l (Rt.X64.key l)])) acc
    | (.label l, _) :: ds, some (f, its), acc =>
      let k := Rt.X64.key l
      if decl.any (Nat.beq · k) then go ds (some (l, [.lab l k])) ((f, its.reverse) :: acc)
      else go ds (some (f, .lab l k :: its)) acc
    | (.instr i, z) :: ds, cur, acc => go ds (cur.map fun (f, its) => (f, It.ofIns i z :: its)) acc
    | (.byteArray _, _) :: ds, cur, acc => go ds cur acc

/-! ## The offsets before every item -/

/-- The flow `o` into label `lab`: the meet with its offsets so far, and
whether they changed. -/
def flow (atLabel : List (Nat × Pt)) (lab : Nat) (o : Pt) : List (Nat × Pt) × Pt × Bool :=
  let old := (lkN atLabel lab).getD .none
  let new := old.meet o
  if new != old then ((lab, new) :: atLabel.filter (!Nat.beq ·.1 lab), new, true) else (atLabel, new, false)

/-- The state of one pass: the offsets at the labels, those flowing, the
epochs so far, whether a label's changed, the offsets before each item
(last first). -/
structure PassSt where
  atLabel : List (Nat × Pt)
  o : Pt
  epochs : Nat
  changed : Bool
  before : List Pt

/-- One item of a pass of `Blocks.offsets`. -/
def passItem (st : PassSt) : It → PassSt
  | .lab _ k =>
    let (a, n, ch) := flow st.atLabel k st.o
    { st with atLabel := a, o := n, changed := st.changed || ch, before := st.o :: st.before }
  | .ins i _ c tgt =>
    let st := { st with before := st.o :: st.before }
    if st.o == .none then st else
    let st := match c with
      | .jmp _ | .jcc _ =>
        let (a, _, ch) := flow st.atLabel tgt st.o
        { st with atLabel := a, changed := st.changed || ch }
      | _ => st
    match st.o with
    | .known k =>
      if switch k i c then { st with epochs := st.epochs + 1, o := .known ⟨0, [], st.epochs + 1⟩ } else
      match c with
      | .x => { st with o := passX k i }
      | _ =>
        let n : Pt := match step k c with
          | (some n, _) => .known n
          | (none, _) =>
            let ds := dstsOf i
            if ds.contains .rsp then .unknown else .known (ds.foldl SO.kill k)
        { st with o := match c with
            | .jmp _ | .ret => .none
            | .call _ => afterCall k
            | _ => n }
    | _ =>
      match c with
      | .jmp _ | .ret => { st with o := .none }
      | _ => if isUd2 i then { st with o := .none } else st

/-- The offsets before every item of a function to a fixpoint of the
offsets at its labels (`Blocks.offsets`, at most `fuel` passes, from `%rsp`
at 8). -/
def fixOffsets (its : List It) : (fuel : Nat) → List (Nat × Pt) → Option (List Pt)
  | 0, _ => none
  | fuel + 1, atLabel =>
    let st := its.foldl passItem ⟨atLabel, .known ⟨8, [], 0⟩, 0, false, []⟩
    if st.changed then fixOffsets its fuel st.atLabel else some st.before.reverse

/-! ## Regions and blocks -/

/-- The region of each epoch: the least offset accessed in it (at most 0)
and the end of the highest accessed word (the entry epoch's at least 16). -/
def regionsOf (its : List It) (before : List Pt) : List (Nat × Int × Int) :=
  (its.zip before).foldl (fun regions (it, o) =>
    match it, o with
    | .ins _ _ c _, .known k =>
      match c with
      | .x => regions
      | c => match step k c with
        | (some _, some a) =>
          let (lo, hi) := (regions.lookup k.epoch).getD (0, 0)
          (k.epoch, min lo a, max hi (a + 8)) :: regions.filter (·.1 != k.epoch)
        | _ => regions
    | _, _ => regions) [(0, 0, 16)]

/-- A row being cut: its label, its cell count and byte offset from the
label, its region, its entry offsets and its cells (last first). -/
structure Row where
  l : Label
  key : Nat
  k : Nat
  off : Nat
  lo : Int
  hi : Int
  o : SO
  cells : List (Directive × Nat)

/-- The label ends `_site` (a transfer site's label, whose first
instruction is a block of its own). -/
def isSite (l : Label) : Bool :=
  "_site".toByteArray.data.toList.reverse.isPrefixOf l.toByteArray.data.toList.reverse

/-- The state of the cut: the label before the item, its key, whether it is
a transfer site's, the cells and bytes since it, the row being cut, the
label's rows cut (last first, cells last first), its single instructions
(last first), the groups closed (last first). -/
structure CutSt where
  lab : Label
  key : Nat
  site : Bool
  cnt : Nat
  off : Nat
  blk : Option Row
  bs : List Row
  ev : List Nat
  grps : List Rt.X64.OGrp

/-- End the row being cut. -/
def CutSt.flush (st : CutSt) : CutSt :=
  match st.blk with
  | some b => { st with blk := none, bs := if b.cells.isEmpty then st.bs else b :: st.bs }
  | none => st

/-- The offsets of the placement data (`Spike.Lib.X64.SO`). -/
def SO.toBlock (o : SO) : Spike.Lib.X64.SO := ⟨o.sp, o.regs⟩

/-- A row cut, as the table's (its cells in order). -/
def Row.toBlk (r : Row) : Rt.X64.OBlk := ⟨r.k, r.off, r.lo, r.hi, r.o.toBlock, r.cells.reverse⟩

/-- **End the label's run**: its group, if the run has a row (its rows and
single instructions in order). A run of single instructions only has no
group (`Blocks.renderCode` writes no row for it; A3 allows that when they
are all `evOk`). -/
def CutSt.close (st : CutSt) : CutSt :=
  let st := st.flush
  if st.bs.isEmpty then { st with ev := [] } else
  { st with bs := [], ev := [],
            grps := ⟨st.lab, st.bs.reverse.map Row.toBlk, st.ev.reverse⟩ :: st.grps }

/-- One item of the cut (`Blocks.analyse`'s blocks). An instruction the
analysis puts in no block (one of class `.x`, one without known offsets,
one whose offsets `step` loses) is a single instruction of the label's
group, at its index from the label. -/
def cutItem (regions : List (Nat × Int × Int)) (st : CutSt) : It × Pt → CutSt
  | (.lab l k, _) => { st.close with lab := l, key := k, site := isSite l, cnt := 0, off := 0 }
  | (.ins i z c _, o) =>
    let single : CutSt := { st.flush with ev := st.cnt :: st.ev }
    let st' : CutSt :=
      match c, o with
      | .x, _ => single
      | _, .known k =>
        if (step k c).1.isNone then single else
        let (lo, hi) := (regions.lookup k.epoch).getD (0, 0)
        let b := st.blk.getD ⟨st.lab, st.key, st.cnt, st.off, lo, hi, k, []⟩
        let st := { st with blk := some { b with cells := (.instr i, z) :: b.cells } }
        if c.isTerm || (st.site && st.cnt == 0) then st.flush else st
      | _, _ => single
    { st' with cnt := st.cnt + 1, off := st.off + z }

/-- **The groups of one function**, in program order (none: no fixpoint):
one per label whose run has a row, with its rows (consecutive,
`Blocks.renderCode`'s table) and the indices of its cells in no row. -/
def fnGrps (fn : Label) (its : List It) : Option (List Rt.X64.OGrp) := do
  let before ← fixOffsets its 100 []
  let regions := regionsOf its before
  let st := (its.zip before).foldl (cutItem regions)
    ⟨fn, Rt.X64.key fn, isSite fn, 0, 0, none, [], [], []⟩
  pure st.close.grps.reverse

/-- The functions the listing declares (`.type NAME, @function`): `_start`,
the IR's, and `scc_rt_morestack` with growable stacks. -/
def declared (ir : IR.Program) : List Label :=
  "_start" :: ir.funcs.map (·.name) ++ (if ir.growth.isSome then [IR.StackMap.morestackSym] else [])

/-- **The block table with its static offsets** of code cells whose
functions are those of `ir` (none: an offsets fixpoint not reached). -/
def blocksOf? (ir : IR.Program) (cells : List (Directive × Nat)) : Option (List Rt.X64.OGrp) := do
  let gs ← (splitFns ((declared ir).map Rt.X64.key) cells).mapM fun (fn, its) => fnGrps fn its
  pure gs.flatten

end Data

open Data

/-- **The code cells of scc's x86-64 output** at the assembler's sizes
(`sizedCells`, as `Scc.Sem.X64.cellsOf` lays out the text); empty where the
sizes do not fit the instruction list. -/
def cellsOfEmitted (e : Scc.Lower.X64.Emitted) (sizes : List Nat) : List (Directive × Nat) :=
  (e.prog.bind (sizedCells · sizes)).getD []

/-- **The placement data of scc's x86-64 output** on its code cells: the
block table computed from the cells (`Data.blocksOf?`; empty where its
offsets reach no fixpoint), the stack need table, the shape of
`scc_rt_main`'s tail. -/
def placeDataOf (e : Scc.Lower.X64.Emitted) (cells : List (Directive × Nat)) : PlaceData where
  blocks := (blocksOf? e.low.ir cells).getD []
  need := e.need.getD []
  tail := if e.low.checked.entry.arg == .setupTid then .setup else .bare
  ir := some e.low.ir

/-- **scc's x86-64 output as `PlaceOK` reads it**, at the assembler's sizes
and label offsets (untrusted, checked by A2): the code cells, the data
sections, the label offsets, the placement data computed from the output. -/
def Out.ofEmitted (e : Scc.Lower.X64.Emitted) (sizes : List Nat) (labelOffs : List (String × Nat)) :
    Out :=
  let cells := cellsOfEmitted e sizes
  ⟨cells, ⟨e.secs.data, e.secs.bss, e.secs.rodata⟩, labelOffs, placeDataOf e cells⟩

/-- The output names the IR it was emitted from, for every emission. -/
theorem place_ir_ofEmitted (e : Scc.Lower.X64.Emitted) (sizes : List Nat) (labelOffs : List (String × Nat)) :
    (Out.ofEmitted e sizes labelOffs).place.ir = some e.low.ir := rfl

/-- **scc's output names its lowered IR** (A9's IR), for every program. -/
theorem lowerAll_place_ir (cfg : Scc.Config) (p : CoreTerm.Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) :
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.ir =
      some (Scc.Lower.X64.lowerAll cfg p).low.ir := rfl

end Scc.Cert.PlaceOK.X64

import Scc.Cert.PlaceOKA64
import Scc.Lower.SpecA64

/-!
# The AArch64 placement data of scc's output, computed

`Out.ofEmitted e`: scc's AArch64 output (`Scc.Lower.A64.Emitted`) as the
output `PlaceOK` checks (`Scc/Cert/PlaceOKA64.lean`): the instruction list,
the data sections, and the placement data computed from the instruction
list and the IR by a function the kernel evaluates, so that
`placeOK cfg (Out.ofEmitted (lowerAll cfg p))` is decided on scc's own
pipeline, with no table as an input.

The placement data (`placeDataOf`):

* **the block table with its static offsets** (`blocksOf`): the analysis of
  `scc --blocks` (`Scc.Cert.Blocks.analyse` with `Blocks.A64.isa`) over the
  instruction list instead of the listing's text. A function starts at a
  label of a function the IR declares (`.type NAME, %function` in the
  listing: the IR's functions and, with growable stacks, `scc_rt_morestack`)
  or at the first label. Each instruction is classified as the text
  analysis classifies its printed form (`Scc.Emit.A64.ppInstr`): `clsOf`
  follows `Blocks.A64.classify` case by case, `dstsOf` is `Blocks.A64.xDsts`
  (the registers it writes). The static offsets flow to a
  fixpoint per function (`fixOffsets`, `Blocks.offsets`), the regions are
  the accessed offsets per epoch (`regionsOf`), and the blocks are cut where
  `Blocks.analyse` cuts them (`cutItem`); the rows are grouped by label in
  program order (`fnGrps`), as `Blocks.renderCode` writes the table, each
  group with the indices from its label of the instructions the analysis
  puts in no row (`OGrp.ev`, which A3's coverage checks), and a group with
  no row for a label whose instructions are all such;
* **the stack need table**: `Emitted.need` (`Scc.Lower.stackNeed`), empty
  with non-tail recursion;
* **the shape of `scc_rt_main`'s tail**: after a setup block exactly when
  the entry point takes the setup block's result (`EntryArg.setupTid`).

Nothing here is trusted: `PlaceOK` checks every row it reads (A3, A5). The
test `Spike/Test/A64PlaceData.lean` checks the computed tables against the
ones `scc --code` and `Scc.Cert.Blocks.offsA64` write.

The offsets' fixpoint has fuel (100 passes per function, `fixOffsets`); a
function whose offsets do not settle within it makes `blocksOf?` `none`,
and the block table is then empty (`placeDataOf`), which A3's coverage
rejects for any program with an instruction: the check fails closed.

To decide `placeOK` by the kernel, the source program must be stated as a
term (`Spike/Test/A64Hello1PlaceOKE.lean`, checked against the frontend by
`#guard`): the frontend's parser is `partial`, so the kernel does not
reduce `Frontend.run`. The externs' signatures are terms for the same
reason (`Frontend.printSig`, `Frontend.printOwnSig`), so that programs
declaring `print` reduce.
-/

namespace Scc.Cert.PlaceOK.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

namespace Data

/-! ## Classification -/

/-- The register a destination operand names, as `Blocks.A64.base` reads
its printed form: `xN`/`wN` as `xN`, the zero register as none. -/
def zrR {w : RegWidth} : RegOrZr w → Option XRegOrSp
  | .low (.reg x) _ => some (.reg x)
  | .low .XZR _ => none

/-- The register a destination operand names (`sp`/`wsp` as `sp`). -/
def spR {w : RegWidth} : RegOrSp w → Option XRegOrSp
  | .low r _ => some r

/-- A constant expression prints `:lo12:`. -/
def lo12In : ConstExpr → Bool
  | .lo12 _ => true
  | .add a b | .sub a b => lo12In a || lo12In b
  | .pg_hi21 e => lo12In e
  | _ => false

/-- An integer constant (printed `#n` as an immediate). -/
def isInt : ConstExpr → Bool
  | .int64 _ => true
  | _ => false

/-- The second operand of an `_e` form prints `:lo12:`. -/
def extLo12 : ExtOrImmReg → Bool
  | .imm ⟨c, _⟩ => lo12In c
  | .ext _ => false

/-- The second operand of an `_e` form prints a `#`. -/
def extHash : ExtOrImmReg → Bool
  | .imm ⟨c, .S0⟩ => isInt c
  | .imm ⟨_, .S12⟩ => true
  | .ext ⟨_, ⟨_, a⟩⟩ => a != .E0

/-- A shifted register operand prints a `#` (a shift other than `lsl #0`). -/
def shiftHash {w : RegWidth} (s : ShiftRegExpr w) : Bool :=
  !(s.shift == .LSL && s.amount == 0)

/-- The classes of `Blocks.Cls` on AArch64: a frame slot access, a register
operation writing `d` (`src`: `Info.from`), a branch, a call, `ret`, or an
instruction outside the blocks (`sys`: for the reason `system` or `shared
memory`, after which the analysis forgets every register offset). -/
inductive K where
  | slot (isLd : Bool) (r : Option XRegOrSp) (n : Int)
  | reg (d : Option XRegOrSp) (src : Option (Option XRegOrSp × Int))
  | jmp (l : Label)
  | jcc (l : Label)
  | call (l : Label)
  | ret
  | x (sys : Bool)
  deriving DecidableEq

/-- A terminator (`Blocks.Cls.isTerm`). -/
def K.isTerm : K → Bool
  | .jmp _ | .jcc _ | .call _ | .ret => true
  | _ => false

/-- A register operation of `Blocks.A64.regOps` that prints no `:lo12:`, as
`Blocks.A64.classify` reads it: `and`/`orr`/`eor` and `adds` with a `#` and
`movz`/`movk` without a non-negative integer are outside the blocks; `add`
and `sub` of an integer immediate between 64-bit registers or `sp` set the
destination from the source; any other write of `sp` is outside the blocks. -/
def regK (d : Option XRegOrSp) : K :=
  if d == some .SP then .x false else .reg d none

/-- **The class of an instruction**, as `Blocks.A64.classify` classifies its
printed form. -/
def clsOf : Instr → K
  | ⟨.W64, .LDR t (.addr ⟨.low .SP _, .imm ⟨.int64 n, none⟩⟩)⟩ => .slot true (zrR t) n.toInt
  | ⟨.W64, .STR t ⟨.low .SP _, .imm ⟨.int64 n, none⟩⟩⟩ => .slot false (zrR t) n.toInt
  | ⟨_, .B (.label l)⟩ => .jmp l
  | ⟨_, .B_cond _ (.label l)⟩ => .jcc l
  | ⟨.W64, .CBZ _ (.label l)⟩ => .jcc l
  | ⟨.W64, .CBNZ _ (.label l)⟩ => .jcc l
  | ⟨_, .BL (.label l)⟩ => .call l
  | ⟨_, .RET t⟩ => if t == RegOrZr.X30 then .ret else .x false
  -- shared memory
  | ⟨_, .LDAR .acq false .W32 _ _⟩ | ⟨_, .LDAR .acq false .W64 _ _⟩
  | ⟨_, .LDAR .plain false .W32 _ _⟩ | ⟨_, .LDAR .plain false .W64 _ _⟩
  | ⟨_, .STLR .W32 _ _⟩ | ⟨_, .STLR .W64 _ _⟩
  | ⟨_, .SWP .acqRel .W32 _ _ _⟩ | ⟨_, .SWP .acqRel .W64 _ _ _⟩
  | ⟨_, .LDOP .ADD .acqRel .W32 _ _ _⟩ | ⟨_, .LDOP .ADD .acqRel .W64 _ _ _⟩
  | ⟨_, .CAS .acqRel .W32 _ _ _⟩ | ⟨_, .CAS .acqRel .W64 _ _ _⟩ => .x true
  -- system
  | ⟨_, .SVC _⟩ | ⟨_, .MSR _ _⟩ | ⟨_, .DMB _⟩ => .x true
  -- register operations
  | ⟨w, .ADD_e d s (.imm ⟨.int64 n, .S0⟩)⟩ =>
    .reg (spR d) (if w == .W64 then some (spR s, n.toInt) else none)
  | ⟨w, .SUB_e d s (.imm ⟨.int64 n, .S0⟩)⟩ =>
    .reg (spR d) (if w == .W64 then some (spR s, -n.toInt) else none)
  | ⟨_, .ADD_e d _ e⟩ | ⟨_, .SUB_e d _ e⟩ => if extLo12 e then .x false else regK (spR d)
  | ⟨_, .ADD_s d _ _⟩ | ⟨_, .SUB_s d _ _⟩ | ⟨_, .SUBS_s d _ _⟩ => regK (zrR d)
  | ⟨_, .ADDS_e d _ e⟩ =>
    if extLo12 e then .x false
    else match d with
      | .low .XZR _ => .x false
      | _ => if extHash e then .x false else regK (zrR d)
  | ⟨_, .ADDS_s d _ s⟩ => if shiftHash s then .x false else regK (zrR d)
  | ⟨_, .SUBS_e d _ e⟩ =>
    if extLo12 e then .x false
    else match d with
      | .low .XZR _ => .x false
      | _ => regK (zrR d)
  | ⟨_, .AND_i d _ i⟩ | ⟨_, .ORR_i d _ i⟩ | ⟨_, .EOR_i d _ i⟩ =>
    if lo12In i || isInt i then .x false else regK (spR d)
  | ⟨_, .AND_s d _ s⟩ | ⟨_, .ORR_s d _ s⟩ | ⟨_, .EOR_s d _ s⟩ =>
    if shiftHash s then .x false else regK (zrR d)
  | ⟨_, .MOVZ d (.int64 i) _⟩ | ⟨_, .MOVK d (.int64 i) _⟩ =>
    if 0 ≤ i.toInt then regK (zrR d) else .x false
  | ⟨_, .MADD d ..⟩ | ⟨_, .MSUB d ..⟩ | ⟨_, .UBFM d ..⟩ | ⟨_, .SBFM d ..⟩ | ⟨_, .LSLV d ..⟩
  | ⟨_, .LSRV d ..⟩ | ⟨_, .ASRV d ..⟩ | ⟨_, .CSEL d ..⟩ | ⟨_, .CSINC d ..⟩ | ⟨_, .MRS d _⟩ =>
    regK (zrR d)
  | _ => .x false

/-- **The register an instruction outside the blocks may write**, as
`Blocks.A64.xDst` reads its printed form: the register its first operand
names (`sp` included, the zero register and non-registers as none). -/
def dstOf : Instr → Option XRegOrSp
  | ⟨_, op⟩ => match op with
    | .LDR d _ | .LDUR d _ | .LDP d _ _ | .LDRB d _ | .LDURB d _ | .LDRSB d _ | .LDURSB d _
    | .LDRH d _ | .LDURH d _ | .LDRSH d _ | .LDURSH d _ | .LDRSW d _ | .LDURSW d _ | .LDPSW d _ _ => zrR d
    | .STR s _ | .STUR s _ | .STP s _ _ | .STRB s _ | .STURB s _ | .STRH s _ | .STURH s _ => zrR s
    | .ADD_e d _ _ | .SUB_e d _ _ | .AND_i d _ _ | .ORR_i d _ _ | .EOR_i d _ _ => spR d
    | .ADDS_e d s _ | .SUBS_e d s _ => match d with
      | .low .XZR _ => spR s
      | _ => zrR d
    | .ADD_s d .. | .ADDS_s d .. | .SUB_s d .. | .SUBS_s d .. | .ADC d .. | .ADCS d .. | .SBC d ..
    | .SBCS d .. | .SDIV d .. | .UDIV d .. | .MADD d .. | .MSUB d .. | .SMULH d .. | .UMULH d ..
    | .SMADDL d .. | .UMADDL d .. | .SMSUBL d .. | .UMSUBL d .. | .AND_s d .. | .ANDS_i d ..
    | .ANDS_s d .. | .ORR_s d .. | .ORN_s d .. | .EOR_s d .. | .EON_s d .. | .BIC_s d .. | .BICS_s d ..
    | .BFM d .. | .SBFM d .. | .UBFM d .. | .CLZ d .. | .CLS d .. | .RBIT d .. | .REV d .. | .REV16 d ..
    | .REV32 d .. | .EXTR d .. | .MOVZ d .. | .MOVK d .. | .MOVN d .. | .LSLV d .. | .LSRV d ..
    | .ASRV d .. | .RORV d .. | .CSEL d .. | .CSINC d .. | .CSINV d .. | .CSNEG d .. | .ADR d _
    | .ADRP d _ | .MRS d _ => zrR d
    | .CCMP_reg s .. | .CCMP_imm s .. | .CCMN_reg s .. | .CCMN_imm s .. => zrR s
    | .BLR t | .BR t | .CBZ t _ | .CBNZ t _ | .TBZ t .. | .TBNZ t .. => zrR t
    | .RET t => if t == RegOrZr.X30 then none else zrR t
    | .LDAR _ _ _ d _ | .STLR _ d _ | .STXR _ _ d _ _ | .CAS _ _ d _ _ | .SWP _ _ d _ _
    | .LDOP _ _ _ d _ _ | .LDXP _ d _ _ | .STXP _ d _ _ _ | .CASP _ d _ _ _ _ => zrR d
    | _ => none

/-- The base register an address writes back (pre- or post-indexed). -/
def wbR (a : AddrExpr) : Option XRegOrSp :=
  match a.off with
  | .imm ⟨_, some _⟩ => spR a.base
  | _ => none

/-- The base register an instruction writes back: a load or store through
a pre- or post-indexed address. -/
def wbOf : Instr → Option XRegOrSp
  | ⟨_, op⟩ => match op with
    | .LDR _ (.addr a) | .LDRSW _ (.addr a) | .STR _ a | .LDP _ _ a | .STP _ _ a | .LDPSW _ _ a
    | .LDRB _ a | .STRB _ a | .LDRSB _ a | .LDRH _ a | .STRH _ a | .LDRSH _ a => wbR a
    | _ => none

/-- **The registers an instruction outside the blocks may write**, as
`Blocks.A64.xDsts` reads its printed form: `dstOf`'s, and for the pair
loads `ldp`, `ldpsw`, `ldxp` and `ldaxp` the second destination too;
`casp` writes `rs1` and `rs2` (its first two operands); a pre- or
post-indexed address writes its base too (`wbOf`). -/
def dstsOf (i : Instr) : List XRegOrSp :=
  let ds := match i with
    | ⟨_, .LDP d1 d2 _⟩ | ⟨_, .LDPSW d1 d2 _⟩ | ⟨_, .LDXP _ d1 d2 _⟩ => (zrR d1).toList ++ (zrR d2).toList
    | ⟨_, .CASP _ rs1 rs2 _ _ _⟩ => (zrR rs1).toList ++ (zrR rs2).toList
    | _ => (dstOf i).toList
  ds ++ (wbOf i).toList

-- The pair forms name both destinations, as `Blocks.A64.xDsts` reads them.
#guard [dstsOf ⟨.W64, .LDP .X1 .X2 ⟨.SP, .imm ⟨.int64 16, none⟩⟩⟩,
    dstsOf ⟨.W64, .LDPSW .X3 .X4 ⟨.X0, .imm ⟨.int64 0, none⟩⟩⟩,
    dstsOf ⟨.W64, .LDXP .plain .X5 .X6 .X0⟩, dstsOf ⟨.W64, .LDXP .acq .X7 .X8 .X0⟩,
    dstsOf ⟨.W64, .CASP .acqRel .X6 .X7 .X2 .X3 .X4⟩,
    dstsOf ⟨.W64, .LDP .XZR .X2 ⟨.X0, .imm ⟨.int64 0, none⟩⟩⟩,
    dstsOf ⟨.W64, .STP .X1 .X2 ⟨.SP, .imm ⟨.int64 0, none⟩⟩⟩,
    dstsOf ⟨.W64, .LDP .X29 .X30 ⟨.SP, .imm ⟨.int64 16, some .Post⟩⟩⟩,
    dstsOf ⟨.W64, .LDR .X1 (.addr ⟨.X0, .imm ⟨.int64 8, some .Pre⟩⟩)⟩] ==
  [[.reg .X1, .reg .X2], [.reg .X3, .reg .X4], [.reg .X5, .reg .X6], [.reg .X7, .reg .X8],
   [.reg .X6, .reg .X7], [.reg .X2], [.reg .X1], [.reg .X29, .reg .X30, .SP], [.reg .X1, .reg .X0]]

/-! ## Static offsets -/

/-- `Blocks.SO` over Kraken's registers: `sp`'s offset, the registers'
(most recently set first), the epoch. -/
structure SO where
  sp : Int
  regs : List (XReg × Int)
  epoch : Nat
  deriving DecidableEq

/-- `Blocks.Pt`. -/
inductive Pt where
  | none
  | unknown
  | known (o : SO)
  deriving DecidableEq

def SO.get (o : SO) : XRegOrSp → Option Int
  | .SP => some o.sp
  | .reg x => Spike.Lib.lk o.regs x

def SO.kill (o : SO) (x : XReg) : SO := { o with regs := o.regs.filter (·.1 != x) }

/-- `Blocks.SO.kill` of a destination (`sp`: unchanged, the callers check it
first). -/
def killR (o : SO) : XRegOrSp → SO
  | .reg x => o.kill x
  | .SP => o

def SO.set (o : SO) : XRegOrSp → Int → SO
  | .SP, k => { o with sp := k }
  | .reg x, k => { o with regs := (x, k) :: (o.kill x).regs }

/-- `Blocks.Pt.meet`. -/
def Pt.meet : Pt → Pt → Pt
  | .none, b => b
  | a, .none => a
  | .known a, .known b =>
    if a.sp == b.sp && a.epoch == b.epoch then
      .known { a with regs := a.regs.filter fun e => Spike.Lib.lk b.regs e.1 == some e.2 }
    else .unknown
  | _, _ => .unknown

/-- `Blocks.A64.step`: the offsets after a covered instruction (none: not
covered at these offsets) and the offset it accesses. -/
def step (o : SO) : K → Option SO × Option Int
  | .slot isLd r n =>
    if o.sp % 16 != 0 || n % 8 != 0 then (none, none) else
    let acc := o.sp + n
    match isLd, r with
    | true, some (.reg r) => (some (o.kill r), some acc)
    | true, some .SP => (some o, some acc)
    | _, _ => (some o, some acc)
  | .reg d src =>
    let viaSrc : Option SO := match src, d with
      | some (some s, n), some d => (o.get s).map fun k => o.set d (k + n)
      | _, _ => none
    match viaSrc with
    | some o' => (some o', none)
    | none => match d with
      | none => (some o, none)
      | some .SP => (none, none)
      | some (.reg x) => (some (o.kill x), none)
  | .jmp _ | .jcc _ | .ret => (some o, none)
  | .call _ => (some (o.kill .X30), none)
  | .x _ => (none, none)

/-- `Blocks.A64.isa.switch`: a register operation writing `sp` that `step`
does not cover. -/
def switch (o : SO) : K → Bool
  | .reg d src => d == some .SP && (step o (.reg d src)).1.isNone
  | _ => false

/-- `Blocks.A64.isa.passX`: the offsets after an instruction outside the
blocks. -/
def passX (o : SO) (i : Instr) (sys : Bool) : Pt :=
  let ds := dstsOf i
  if ds.contains .SP then .unknown
  else if sys then .known { o with regs := [] }
  else .known (ds.foldl killR o)

-- A pair load forgets both destinations, as `Blocks.A64.isa.passX` does: a
-- stale `sp + k` fact for the second one is dropped (`x2` here).
#guard
  let o : SO := ⟨0, [(.X1, 8), (.X2, 16), (.X3, 24)], 0⟩
  [passX o ⟨.W64, .LDP .X1 .X2 ⟨.X0, .imm ⟨.int64 0, none⟩⟩⟩ false,
   passX o ⟨.W64, .LDXP .acq .X1 .X2 .X0⟩ false,
   passX o ⟨.W64, .CASP .plain .X2 .X3 .X4 .X5 .X0⟩ false] ==
    [.known ⟨0, [(.X3, 24)], 0⟩, .known ⟨0, [(.X3, 24)], 0⟩, .known ⟨0, [(.X1, 8)], 0⟩]

-- A write-back address writes its base: `sp`'s offset is then unknown, and a
-- stale fact for another base is dropped (`x3` here).
#guard
  let o : SO := ⟨0, [(.X1, 8), (.X2, 16), (.X3, 24)], 0⟩
  [passX o ⟨.W64, .LDP .X29 .X30 ⟨.SP, .imm ⟨.int64 16, some .Post⟩⟩⟩ false,
   passX o ⟨.W64, .LDR .X9 (.addr ⟨.X3, .imm ⟨.int64 8, some .Pre⟩⟩)⟩ false] ==
    [.unknown, .known ⟨0, [(.X1, 8), (.X2, 16)], 0⟩]

/-- `Blocks.A64.isa.afterCall`: a call forgets `x0` … `x18`. -/
def afterCall (n : Pt) : Pt :=
  match n with
  | .known n => .known ((List.range 19).foldl (fun o i => o.kill (xregOf i)) n)
  | n => n
where
  /-- The general register numbered `i` (`x0` … `x18` here). -/
  xregOf (i : Nat) : XReg :=
    match i with
    | 0 => .X0 | 1 => .X1 | 2 => .X2 | 3 => .X3 | 4 => .X4 | 5 => .X5 | 6 => .X6 | 7 => .X7
    | 8 => .X8 | 9 => .X9 | 10 => .X10 | 11 => .X11 | 12 => .X12 | 13 => .X13 | 14 => .X14
    | 15 => .X15 | 16 => .X16 | 17 => .X17 | _ => .X18

/-! ## Functions -/

/-! Labels are compared by their keys (`Rt.A64.key`, injective), computed
once per occurrence: comparing the strings themselves is slow in the
kernel. -/

/-- The value at key `k` of an association list. -/
def lkN {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (j, a) :: l, k => if Nat.beq j k then some a else lkN l k

/-- An item of a function: a label (with its key), or an instruction with
its class (`clsOf`) and the key of the label it branches to. -/
inductive It where
  | lab (l : Label) (key : Nat)
  | ins (i : Instr) (c : K) (tgt : Nat)

/-- The item of an instruction. -/
def It.ofIns (i : Instr) : It :=
  let c := clsOf i
  .ins i c (match c with | .jmp l | .jcc l => Rt.A64.key l | _ => 0)

/-- **The functions of a program** (`Blocks.functions`): a function starts
at a label whose key is in `decl` or at the first label; instructions
before the first label and data are dropped. -/
def splitFns (decl : List Nat) (prog : List Directive) : List (Label × List It) :=
  go prog none []
where
  go : List Directive → Option (Label × List It) → List (Label × List It) → List (Label × List It)
    | [], cur, acc => (match cur with | some (f, its) => (f, its.reverse) :: acc | none => acc).reverse
    | .label l :: ds, none, acc => go ds (some (l, [.lab l (Rt.A64.key l)])) acc
    | .label l :: ds, some (f, its), acc =>
      let k := Rt.A64.key l
      if decl.any (Nat.beq · k) then go ds (some (l, [.lab l k])) ((f, its.reverse) :: acc)
      else go ds (some (f, .lab l k :: its)) acc
    | .instr i :: ds, cur, acc => go ds (cur.map fun (f, its) => (f, It.ofIns i :: its)) acc
    | .byteArray _ :: ds, cur, acc => go ds cur acc

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
  | .ins i c tgt =>
    let st := { st with before := st.o :: st.before }
    if st.o == .none then st else
    let st := match c with
      | .jmp _ | .jcc _ =>
        let (a, _, ch) := flow st.atLabel tgt st.o
        { st with atLabel := a, changed := st.changed || ch }
      | _ => st
    match st.o with
    | .known k =>
      if switch k c then { st with epochs := st.epochs + 1, o := .known ⟨0, [], st.epochs + 1⟩ } else
      match c with
      | .x sys => { st with o := passX k i sys }
      | _ =>
        let n : Pt := match step k c with
          | (some n, _) => .known n
          | (none, _) =>
            let ds := dstsOf i
            if ds.contains .SP then .unknown else .known (ds.foldl killR k)
        { st with o := match c with
            | .jmp _ | .ret => .none
            | .call _ => afterCall n
            | _ => n }
    | _ => match c with
      | .jmp _ | .ret => { st with o := .none }
      | _ => st

/-- The offsets before every item of a function to a fixpoint of the
offsets at its labels (`Blocks.offsets`, at most `fuel` passes). -/
def fixOffsets (its : List It) : (fuel : Nat) → List (Nat × Pt) → Option (List Pt)
  | 0, _ => none
  | fuel + 1, atLabel =>
    let st := its.foldl passItem ⟨atLabel, .known ⟨0, [], 0⟩, 0, false, []⟩
    if st.changed then fixOffsets its fuel st.atLabel else some st.before.reverse

/-! ## Regions and blocks -/

/-- The region of each epoch: the least offset accessed in it (at most 0)
and the end of the highest accessed cell (at least 0). -/
def regionsOf (its : List It) (before : List Pt) : List (Nat × Int × Int) :=
  (its.zip before).foldl (fun regions (it, o) =>
    match it, o with
    | .ins _ c _, .known k =>
      match c with
      | .x _ => regions
      | c => match step k c with
        | (some _, some a) =>
          let (lo, hi) := (regions.lookup k.epoch).getD (0, 0)
          (k.epoch, min lo a, max hi (a + 8)) :: regions.filter (·.1 != k.epoch)
        | _ => regions
    | _, _ => regions) [(0, 0, 0)]

/-- A row being cut: its label, its instruction count from the label, its
region, its entry offsets and its instructions (last first). -/
structure Row where
  l : Label
  key : Nat
  k : Nat
  lo : Int
  hi : Int
  o : SO
  ins : List Directive

/-- The label ends `_site` (a transfer site's label, whose first
instruction is a block of its own). -/
def isSite (l : Label) : Bool :=
  "_site".toByteArray.data.toList.reverse.isPrefixOf l.toByteArray.data.toList.reverse

/-- The state of the cut: the label before the item, its key, whether it is
a transfer site's, the instructions since it, the row being cut, the label's
rows cut (last first, instructions last first), its single instructions
(last first), the groups closed (last first). -/
structure CutSt where
  lab : Label
  key : Nat
  site : Bool
  cnt : Nat
  blk : Option Row
  bs : List Row
  ev : List Nat
  grps : List Rt.A64.OGrp

/-- End the row being cut. -/
def CutSt.flush (st : CutSt) : CutSt :=
  match st.blk with
  | some b => { st with blk := none, bs := if b.ins.isEmpty then st.bs else b :: st.bs }
  | none => st

/-- The offsets of the placement data (`Spike.Lib.A64.Flow.SO`). -/
def SO.toFlow (o : SO) : Spike.Lib.A64.Flow.SO := ⟨o.sp, o.regs⟩

/-- A row cut, as the table's (its instructions in order). -/
def Row.toBlk (r : Row) : Rt.A64.OBlk := ⟨r.k, r.lo, r.hi, r.o.toFlow, r.ins.reverse⟩

/-- **End the label's run**: its group, if the run has an instruction (its
rows and single instructions in order; `Blocks.renderCode` writes no row
for single instructions, so the group may have none). -/
def CutSt.close (st : CutSt) : CutSt :=
  let st := st.flush
  if st.bs.isEmpty && st.ev.isEmpty then st else
  { st with bs := [], ev := [],
            grps := ⟨st.lab, st.bs.reverse.map Row.toBlk, st.ev.reverse⟩ :: st.grps }

/-- One item of the cut (`Blocks.analyse`'s blocks). An instruction the
analysis puts in no block (one of class `.x`, one without known offsets,
one whose offsets `step` loses) is a single instruction of the label's
group, at its index from the label. -/
def cutItem (regions : List (Nat × Int × Int)) (st : CutSt) : It × Pt → CutSt
  | (.lab l k, _) => { st.close with lab := l, key := k, site := isSite l, cnt := 0 }
  | (.ins i c _, o) =>
    let single : CutSt := { st.flush with ev := st.cnt :: st.ev }
    let st' : CutSt :=
      match c, o with
      | .x _, _ => single
      | _, .known k =>
        if (step k c).1.isNone then single else
        let (lo, hi) := (regions.lookup k.epoch).getD (0, 0)
        let b := st.blk.getD ⟨st.lab, st.key, st.cnt, lo, hi, k, []⟩
        let st := { st with blk := some { b with ins := .instr i :: b.ins } }
        if c.isTerm || (st.site && st.cnt == 0) then st.flush else st
      | _, _ => single
    { st' with cnt := st.cnt + 1 }

/-- **The groups of one function**, in program order (none: no fixpoint):
one per label whose run has an instruction, with its rows (consecutive,
`Blocks.renderCode`'s table) and the indices of its instructions in no
row. -/
def fnGrps (fn : Label) (its : List It) : Option (List Rt.A64.OGrp) := do
  let before ← fixOffsets its 100 []
  let regions := regionsOf its before
  let st := (its.zip before).foldl (cutItem regions) ⟨fn, Rt.A64.key fn, isSite fn, 0, none, [], [], []⟩
  pure st.close.grps.reverse

/-- The functions the listing declares (`.type NAME, %function`): the IR's,
and `scc_rt_morestack` with growable stacks. -/
def declared (ir : IR.Program) : List Label :=
  ir.funcs.map (·.name) ++ (if ir.growth.isSome then [IR.StackMap.morestackSym] else [])

/-- **The block table with its static offsets** of an instruction list
whose functions are those of `ir` (none: an offsets fixpoint not reached). -/
def blocksOf? (ir : IR.Program) (prog : List Directive) : Option (List Rt.A64.OGrp) := do
  let gs ← (splitFns ((declared ir).map Rt.A64.key) prog).mapM fun (fn, its) => fnGrps fn its
  pure gs.flatten

end Data

open Data

/-- **The placement data of scc's AArch64 output**: the block table computed
from the instruction list (`Data.blocksOf?`; empty where its offsets reach
no fixpoint, which no row then covers), the stack need table, the shape of
`scc_rt_main`'s tail, and the lowered IR (A9). -/
def placeDataOf (e : Scc.Lower.A64.Emitted) : PlaceData where
  blocks := (blocksOf? e.low.ir e.prog).getD []
  need := e.need.getD []
  tail := if e.low.checked.entry.arg == .setupTid then .setup else .bare
  ir := some e.low.ir

/-- **scc's AArch64 output as `PlaceOK` reads it**: the instruction list,
the data sections, no assembler offsets, the placement data computed from
the output. -/
def Out.ofEmitted (e : Scc.Lower.A64.Emitted) : Out :=
  ⟨e.prog, ⟨e.secs.data, e.secs.bss, e.secs.rodata⟩, [], placeDataOf e⟩

/-- The output names the IR it was emitted from, for every emission. -/
theorem place_ir_ofEmitted (e : Scc.Lower.A64.Emitted) : (Out.ofEmitted e).place.ir = some e.low.ir := rfl

/-- **scc's output names its lowered IR** (A9's IR), for every program. -/
theorem lowerAll_place_ir (cfg : Scc.Config) (p : CoreTerm.Prog) :
    (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.ir = some (Scc.Lower.A64.lowerAll cfg p).low.ir := rfl

end Scc.Cert.PlaceOK.A64

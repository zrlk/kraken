/-
Coverage test for `Operation.deps` (`Kraken/AArch64/Deps.lean`).

There is no lemma relating `Operation.deps` to `Operation.interp`; this file
checks by *testing* that the dependency table over-approximates what the
interpreter actually does with the registers, per operation constructor:

- **Writes.** Every register whose value differs between the input and the
  output state (the flags included) is in `loadDefs ∪ statusDefs ∪ defs`.
- **Reads.** For every register `r` not in `addrRegs ∪ dataRegs ∪ condRegs`,
  perturbing `r` in the input leaves the outcome — registers, flags, data
  memory, the branch target, and the trace of unmapped-memory events —
  unchanged. If `r` is not a declared write, it is masked in the comparison;
  if it is, the written value must not change (a write that merges the old
  value, like `MOVK`, is a read).

Each operation runs from a baseline state whose registers point into a mapped
512-byte region (so loads and stores hit `dmem`) and from a few pseudo-random
states (deterministic `StdGen`); every `undefined Bool` is resolved both ways,
other `undefined`s to a fixed value; `require_*` and `fence` are followed.
Unmapped accesses are answered with a value derived from the address and
recorded in the outcome, so a moved footprint shows up as a changed trace.

The constructor-coverage check compares the constructors reached by the
operation list below against `Operation`'s constructor list from the
environment, so a new constructor fails the test until it is added here.
-/
import Kraken.AArch64.Semantics
import Kraken.AArch64.Deps

namespace DepsTests

open Kraken (InstrDeps)

instance : Labels where label _ := 0x8000

/-! ## Register access by `RegId` -/

def xregs : Array XReg :=
  #[.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15,
    .X16, .X17, .X18, .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

def allRegIds : List RegId := (List.finRange 31).map RegId.x ++ [.sp, .nzcv]

def flagsToUInt64 (f : StatusFlags) : UInt64 :=
  f.n.toUInt64 <<< 3 ||| f.z.toUInt64 <<< 2 ||| f.c.toUInt64 <<< 1 ||| f.v.toUInt64

def flagsOfUInt64 (v : UInt64) : StatusFlags :=
  { n := v &&& 8 != 0, z := v &&& 4 != 0, c := v &&& 2 != 0, v := v &&& 1 != 0 }

def getReg (s : MachineData) : RegId → UInt64
  | .x n => s.regs.getXReg xregs[n]
  | .sp => s.regs.SP
  | .nzcv => flagsToUInt64 s.status

def setReg (s : MachineData) : RegId → UInt64 → MachineData
  | .x n, v => { s with regs := s.regs.setXReg xregs[n] v.toBitVec }
  | .sp, v => { s with regs := { s.regs with SP := v } }
  | .nzcv, v => { s with status := flagsOfUInt64 v }

/-! ## Running one operation to all of its outcomes -/

/-- The result of one run: the final machine data, the pc (`fallthrough` if the
operation did not jump), and the trace of effects that were not served from
`dmem`, in order. -/
structure Outcome where
  st : MachineData
  pc : Int64
  events : List String
  deriving BEq

def fallthrough : Int64 := 0x4004

/-- The value an unmapped load of `w` bytes at `addr` returns. -/
def unmappedVal (addr : BitVec 64) (w : MemWidth) : w.type :=
  (hash addr).toBitVec.setWidth w.bits

partial def collect (e : Effects) (events : List String) : List Outcome :=
  match e with
  | .done (s, pc) => [{ st := s, pc, events := events.reverse }]
  | .unimplemented msg => [{ st := {}, pc := 0, events := (s!"unimplemented {msg}" :: events).reverse }]
  | .unaligned_sp sp => [{ st := {}, pc := 0, events := (s!"unaligned_sp {sp.toNat}" :: events).reverse }]
  | .nonmem_load dmem addr w ret =>
    collect (ret (unmappedVal addr w) dmem) (s!"load {addr.toNat} {w}" :: events)
  | @Effects.nonmem_store dmem addr w v ret =>
    collect (ret dmem) (s!"store {addr.toNat} {w} {v.toNat}" :: events)
  | .sync_load k xcl dmem addr w ret =>
    collect (ret (unmappedVal addr w) dmem) (s!"sync_load {repr k} {xcl} {addr.toNat} {w}" :: events)
  | @Effects.sync_store k xcl dmem addr w v ret =>
    let ev := s!"sync_store {repr k} {xcl} {addr.toNat} {w} {v.toNat}"
    if xcl then collect (ret false dmem) (s!"{ev} fail" :: events) ++ collect (ret true dmem) (s!"{ev} ok" :: events)
    else collect (ret true dmem) (ev :: events)
  | .rmw k noRet dmem addr w op ret =>
    let old := unmappedVal addr w
    let new := match op old with | some n => s!"{n.toNat}" | none => "none"
    let nr := if noRet then " noRet" else ""
    collect (ret old dmem) (s!"rmw {repr k}{nr} {addr.toNat} {w} {old.toNat} -> {new}" :: events)
  | .sync_load_pair k xcl dmem addr w ret =>
    let a2 := addr + w.bytesv
    collect (ret (unmappedVal addr w) (unmappedVal a2 w) dmem)
      (s!"sync_load_pair {repr k} {xcl} {addr.toNat} {w}" :: events)
  | @Effects.sync_store_pair k xcl dmem addr w v1 v2 ret =>
    -- One `sync_store` event per half (so `checkPerStore` sees two stores), then the outcome.
    let evs := s!"sync_store {repr k} {xcl} {(addr + w.bytesv).toNat} {w} {v2.toNat} (pair, high)" ::
      s!"sync_store {repr k} {xcl} {addr.toNat} {w} {v1.toNat} (pair, low)" :: events
    if xcl then collect (ret false dmem) ("pair fail" :: evs) ++ collect (ret true dmem) ("pair ok" :: evs)
    else collect (ret true dmem) evs
  | @Effects.rmw_pair k dmem addr w cmp1 cmp2 new1 new2 ret =>
    let o1 := unmappedVal addr w
    let o2 := unmappedVal (addr + w.bytesv) w
    collect (ret o1 o2 dmem)
      (s!"rmw_pair {repr k} {addr.toNat} {w} {o1.toNat} {o2.toNat} cmp {cmp1.toNat} {cmp2.toNat} new {new1.toNat} {new2.toNat}" :: events)
  | .fence k ok => collect (ok ()) (s!"fence {repr k}" :: events)
  | .require_read_access _ _ ok | .require_write_access _ _ ok | .require_exec_access _ ok =>
    collect (ok ()) events
  | @Effects.undefined _ inst ret =>
    match inst with
    | .bool => collect (ret false) ("undefined false" :: events) ++ collect (ret true) ("undefined true" :: events)
    | .bitvec w => collect (ret (NondetSupportingType.from_hash (α := w.type) 0x5EED)) ("undefined bitvec" :: events)
    | .statusFlags => collect (ret (NondetSupportingType.from_hash (α := StatusFlags) 0x5EED)) ("undefined flags" :: events)

def run {w} (op : Operation w) (s : MachineData) : List Outcome :=
  let p : Std.Rco Int64 := .mk 0x4000 fallthrough
  collect (op.interp p s (fun s => .done (s, fallthrough)) (fun pc s => .done (s, pc))) []

/-! ## States -/

def regionBase : Nat := 0x10000
def regionSize : Nat := 0x200

/-- The mapped region, filled with pseudo-random bytes. -/
def initMem (g : StdGen) : DataMem × StdGen :=
  (List.range (regionSize / 8)).foldl (init := ({}, g)) fun (m, g) i =>
    let (v, g) := randNat g 0 (2^64 - 1)
    (Mem.storeInt m (BitVec.ofNat 64 (regionBase + 8 * i)) 8 v, g)

/-- Every register points into the region (8-byte aligned, with room on both
sides for the offsets the operand list uses), `SP` in its middle, flags clear. -/
def baseline (mem : DataMem) : MachineData :=
  let regs := (List.finRange 31).foldl (init := ({} : Reg64s)) fun regs i =>
    regs.setXReg xregs[i] (BitVec.ofNat 64 (regionBase + 0x40 + 8 * i.val))
  { regs := { regs with SP := (regionBase + 0x100).toUInt64 }, status := ⟨false, false, false, false⟩, dmem := mem }

/-- A pseudo-random register value: half the time a pointer into the region,
otherwise a small or an arbitrary 64-bit value. `SP` is always an aligned pointer. -/
def randomReg (g : StdGen) (isSp : Bool) : UInt64 × StdGen :=
  let (k, g) := randNat g 0 3
  if isSp || k < 2 then
    let (off, g) := randNat g 3 0x1B
    ((regionBase + 16 * off).toUInt64, g)
  else if k == 2 then
    let (v, g) := randNat g 0 255
    (v.toUInt64, g)
  else
    let (v, g) := randNat g 0 (2^64 - 1)
    (v.toUInt64, g)

def randomState (mem : DataMem) (g : StdGen) : MachineData × StdGen :=
  let s0 : MachineData := { dmem := mem }
  let (s, g) := allRegIds.foldl (init := (s0, g)) fun (s, g) r =>
    match r with
    | .nzcv => let (v, g) := randNat g 0 15; (setReg s r v.toUInt64, g)
    | .sp => let (v, g) := randomReg g true; (setReg s r v, g)
    | .x _ => let (v, g) := randomReg g false; (setReg s r v, g)
  (s, g)

/-! ## The checks -/

def readSet (d : InstrDeps RegId) : List RegId := d.addrRegs ++ d.dataRegs ++ d.condRegs
def writeSet (d : InstrDeps RegId) : List RegId := d.loadDefs ++ d.statusDefs ++ d.defs

def maskReg (o : Outcome) (r : RegId) : Outcome := { o with st := setReg o.st r 0 }

def isFault (o : Outcome) : Bool :=
  o.events.any fun e => e.startsWith "unimplemented" || e.startsWith "unaligned_sp"

/-- The violations of `deps` for `op` run from `s`, with a perturbation value
drawn from `g` per register in addition to the complement of its value. -/
def checkState (name : String) {w} (op : Operation w) (d : InstrDeps RegId) (s : MachineData) (g : StdGen) :
    List String × StdGen :=
  let outs := run op s
  let faults := if outs.any isFault then [s!"{name}: faulted: {outs.filter isFault |>.map (·.events)}"] else []
  -- Writes.
  let writes := outs.flatMap fun o =>
    allRegIds.filterMap fun r =>
      if getReg o.st r != getReg s r && !(writeSet d).contains r
      then some s!"{name}: {repr r} written but not in defs" else none
  -- Reads.
  let (reads, g) := allRegIds.foldl (init := (([] : List String), g)) fun (acc, g) r =>
    if (readSet d).contains r then (acc, g) else
    let (rnd, g) := match r with
      | .nzcv => let (v, g) := randNat g 0 15; (v.toUInt64, g)
      | _ => let (v, g) := randNat g 0 (2^64 - 1); (v.toUInt64, g)
    let flip := match r with | .nzcv => getReg s r ^^^ 0xF | _ => ~~~(getReg s r)
    let norm (os : List Outcome) := if (writeSet d).contains r then os else os.map (maskReg · r)
    let bad := [flip, rnd].any fun v => norm (run op (setReg s r v)) != norm outs
    (if bad then s!"{name}: {repr r} read but not in deps" :: acc else acc, g)
  (faults ++ writes ++ reads.reverse, g)

/-- The store events of an outcome, in order. -/
def storeEvents (o : Outcome) : List String :=
  o.events.filter fun e => e.startsWith "store " || e.startsWith "sync_store "

/-- Per-store data dependencies (`dataRegsPer`, `STP`): run from `s` with no
mapped memory, so every store is an event; there must be one entry per store,
each a subset of `dataRegs`, and perturbing a register outside
`addrRegs ∪ condRegs ∪ dataRegsPer[k]` must leave store `k` (address, width,
value) unchanged. -/
def checkPerStore (name : String) {w} (op : Operation w) (d : InstrDeps RegId) (s : MachineData) (g : StdGen) :
    List String × StdGen :=
  if d.dataRegsPer.isEmpty then ([], g) else
  let s := { s with dmem := {} }
  let stores (s : MachineData) := (run op s).map storeEvents
  let outs := stores s
  let shape := (if outs.any (·.length != d.dataRegsPer.length) then
      [s!"{name}: {d.dataRegsPer.length} dataRegsPer entries for {outs.map (·.length)} stores"] else []) ++
    (if d.dataRegsPer.any (·.any (!d.dataRegs.contains ·)) then [s!"{name}: dataRegsPer not within dataRegs"] else [])
  let (bad, g) := d.dataRegsPer.zipIdx.foldl (init := (([] : List String), g)) fun (acc, g) (regs, k) =>
    allRegIds.foldl (init := (acc, g)) fun (acc, g) r =>
      if (d.addrRegs ++ d.condRegs ++ regs).contains r then (acc, g) else
      let (rnd, g) := match r with
        | .nzcv => let (v, g) := randNat g 0 15; (v.toUInt64, g)
        | _ => let (v, g) := randNat g 0 (2^64 - 1); (v.toUInt64, g)
      let flip := match r with | .nzcv => getReg s r ^^^ 0xF | _ => ~~~(getReg s r)
      let kth (os : List (List String)) := os.map (·[k]?)
      if [flip, rnd].any fun v => kth (stores (setReg s r v)) != kth outs
      then (s!"{name}: store {k} reads {repr r} but not in its dataRegsPer" :: acc, g) else (acc, g)
  (shape ++ bad.reverse, g)

/-- Baseline plus `n` random states. -/
def checkOpWith (name : String) {w} (op : Operation w) (d : InstrDeps RegId) (mem : DataMem) (g : StdGen)
    (n : Nat := 3) : List String × StdGen :=
  let (v, g) := checkState name op d (baseline mem) g
  let (vp, g) := checkPerStore name op d (baseline mem) g
  (List.range n).foldl (init := (v ++ vp, g)) fun (v, g) _ =>
    let (s, g) := randomState mem g
    let (v', g) := checkState name op d s g
    let (vp, g) := checkPerStore name op d s g
    (v ++ v' ++ vp, g)

def ctorName {w} (op : Operation w) : Lean.Name := (Lean.toExpr op).getAppFn.constName!

/-! ## The operations

At least one instance per constructor and operand shape: register, immediate and
memory forms, both widths, `XZR`/`WZR` and `SP` where the syntax admits them,
every addressing mode (offset, pre/post-index, register offset, literal). -/

def a (base : RegOrSp .W64) (off : Int64 := 0) : AddrExpr :=
  { base, off := .imm { imm := .int64 off, index := none } }
def aPre (base : RegOrSp .W64) (off : Int64) : AddrExpr :=
  { base, off := .imm { imm := .int64 off, index := some .Pre } }
def aPost (base : RegOrSp .W64) (off : Int64) : AddrExpr :=
  { base, off := .imm { imm := .int64 off, index := some .Post } }
def aReg (base : RegOrSp .W64) (idx : RegOrZrW) (ty : MemExtendType := .UXTX)
    (am : MemExtendAmount := .E0) : AddrExpr :=
  { base, off := .reg { reg := idx, ext := { type := ty, amount := am } } }
def u (base : RegOrSp .W64) (imm : Int64 := 0) : UnscaledAddrExpr := { base, imm := .int64 imm }
def ext (r : RegOrZrW) (ty : ExtendType := .UXTX) (am : ExtendAmount := .E0) : ExtOrImmReg :=
  .ext { reg := r, ext := { type := ty, amount := am } }
def imm12 (i : Int64) (sh : ImmShift := .S0) : ExtOrImmReg := .imm { imm := .int64 i, shift := sh }
def sh {w} (r : RegOrZr w) (amt : Int64 := 0) (ty : ShiftType := .LSL) : ShiftRegExpr w :=
  { reg := r, amount := amt, shift := ty }
def lbl : ConstExpr := .label "L"
def lit : AddrOrLit := .lit (.addr { label := "L" })
def pool : AddrOrLit := .lit (.pool { expr := .int64 77 })

abbrev Op := (w : RegWidth) × Operation w
def x {w} (op : Operation w) : Op := ⟨w, op⟩

def ops : List Op := [
  -- Loads and stores.
  x (.LDR .X0 (.addr (a .X1))), x (.LDR .W0 (.addr (a .X1 8))), x (.LDR .X0 (.addr (a .SP 16))),
  x (.LDR .X0 (.addr (aReg .X1 ⟨.W64, .X2⟩))), x (.LDR .W0 (.addr (aReg .X1 ⟨.W32, .W2⟩ .SXTW .E2))),
  x (.LDR .X0 (.addr (aReg .SP ⟨.W64, .X2⟩ .UXTX .E3))),
  x (.LDR .X0 (.addr (aPre .X1 8))), x (.LDR .X0 (.addr (aPost .X1 8))), x (.LDR .W0 (.addr (aPre .SP 16))),
  x (.LDR .XZR (.addr (a .X1))), x (.LDR .WZR (.addr (aPost .X1 4))), x (.LDR .X0 lit), x (.LDR .W0 pool),
  x (.STR .X0 (a .X1)), x (.STR .W0 (a .X1 4)), x (.STR .XZR (a .X1)), x (.STR .X0 (aPre .SP (-16))),
  x (.STR .X0 (aPost .X1 8)), x (.STR .X0 (aReg .X1 ⟨.W64, .X2⟩ .UXTX .E3)), x (.STR .W0 (a .SP)),
  x (.STR .W0 (aReg .X1 ⟨.W32, .W2⟩ .UXTW)),
  x (.LDUR .X0 (u .X1 (-8))), x (.LDUR .W0 (u .SP 8)), x (.LDUR .XZR (u .X1)),
  x (.STUR .X0 (u .X1 8)), x (.STUR .W0 (u .X1 (-4))), x (.STUR .XZR (u .SP)),
  x (.LDP .X0 .X2 (a .X1)), x (.LDP .W0 .W2 (a .X1 8)), x (.LDP .X0 .X2 (aPre .SP 16)),
  x (.LDP .X0 .X2 (aPost .X1 16)), x (.LDP .X0 .XZR (a .X1)), x (.LDP .W0 .W2 (aPost .SP 16)),
  x (.STP .X0 .X2 (a .X1)), x (.STP .W0 .W2 (aPre .SP (-16))), x (.STP .X0 .X2 (aPost .X1 16)),
  x (.STP .XZR .X2 (a .X1)), x (.STP .X29 .X30 (aPre .SP (-32))),
  x (.LDRB .W0 (a .X1)), x (.LDRB .W0 (aReg .X1 ⟨.W64, .X2⟩)), x (.LDRB .W0 (aPre .X1 1)),
  x (.LDRB .WZR (a .SP)), x (.LDURB .W0 (u .X1 1)),
  x (.STRB .W0 (a .X1)), x (.STRB .WZR (a .X1 2)), x (.STRB .W0 (aPost .X1 1)), x (.STURB .W0 (u .X1 (-1))),
  x (.LDRSB .X0 (a .X1)), x (.LDRSB .W0 (a .X1 1)), x (.LDRSB .X0 (aReg .X1 ⟨.W32, .W2⟩ .SXTW)),
  x (.LDURSB .X0 (u .X1)), x (.LDURSB .W0 (u .X1 2)),
  x (.LDRH .W0 (a .X1)), x (.LDRH .W0 (aReg .X1 ⟨.W64, .X2⟩ .UXTX .E1)), x (.LDURH .W0 (u .X1 2)),
  x (.STRH .W0 (a .X1)), x (.STRH .W0 (aPost .X1 2)), x (.STRH .WZR (a .X1)), x (.STURH .W0 (u .X1 4)),
  x (.LDRSH .X0 (a .X1)), x (.LDRSH .W0 (aReg .X1 ⟨.W64, .X2⟩ .UXTX .E1)),
  x (.LDURSH .X0 (u .X1)), x (.LDURSH .W0 (u .X1 2)),
  x (.LDRSW .X0 (.addr (a .X1))), x (.LDRSW .X0 (.addr (aReg .X1 ⟨.W32, .W2⟩ .SXTW .E2))), x (.LDRSW .X0 lit),
  x (.LDRSW .XZR (.addr (aPre .X1 4))), x (.LDURSW .X0 (u .X1 4)),
  x (.LDPSW .X0 .X2 (a .X1)), x (.LDPSW .X0 .X2 (aPre .X1 8)), x (.LDPSW .X0 .X2 (aPost .SP 16)),
  -- Arithmetic.
  x (.ADD_e .X0 .X1 (imm12 5)), x (.ADD_e .X0 .X1 (imm12 1 .S12)), x (.ADD_e .X0 .X1 (ext ⟨.W64, .X2⟩)),
  x (.ADD_e .SP .SP (imm12 16)), x (.ADD_e .X0 .SP (imm12 0)), x (.ADD_e .W0 .W1 (ext ⟨.W32, .W2⟩ .UXTB .E2)),
  x (.ADD_e .X0 .X1 (ext ⟨.W32, .W2⟩ .SXTW .E1)), x (.ADD_e .WSP .W1 (ext ⟨.W32, .WZR⟩)),
  x (.ADD_s .X0 .X1 (sh .X2 3)), x (.ADD_s .W0 .W1 (sh .WZR)), x (.ADD_s .XZR .X1 (sh .X2)),
  x (.ADD_s .X0 .XZR (sh .X2 4 .LSR)), x (.ADD_s .W0 .W1 (sh .W2 2 .ASR)),
  x (.ADDS_e .X0 .X1 (imm12 1)), x (.ADDS_e .XZR .SP (imm12 0)), x (.ADDS_e .W0 .W1 (ext ⟨.W32, .W2⟩ .UXTH)),
  x (.ADDS_e .X0 .SP (ext ⟨.W64, .X2⟩)),
  x (.ADDS_s .X0 .X1 (sh .X2)), x (.ADDS_s .WZR .W1 (sh .W2)), x (.ADDS_s .X0 .XZR (sh .X2 1)),
  x (.SUB_e .X0 .X1 (imm12 5)), x (.SUB_e .SP .SP (imm12 16)), x (.SUB_e .W0 .W1 (ext ⟨.W32, .W2⟩)),
  x (.SUB_e .X0 .SP (ext ⟨.W64, .X2⟩ .UXTX .E2)),
  x (.SUB_s .X0 .X1 (sh .X2 1)), x (.SUB_s .W0 .WZR (sh .W2)), x (.SUB_s .XZR .X1 (sh .X2)),
  x (.SUBS_e .X0 .X1 (imm12 1)), x (.SUBS_e .XZR .X1 (imm12 7)), x (.SUBS_e .W0 .W1 (ext ⟨.W32, .W2⟩ .SXTB)),
  x (.SUBS_e .XZR .SP (imm12 0)),
  x (.SUBS_s .X0 .X1 (sh .X2)), x (.SUBS_s .WZR .W1 (sh .W2 3 .ROR)), x (.SUBS_s .X0 .XZR (sh .X2)),
  x (.ADC .X0 .X1 .X2), x (.ADC .W0 .W1 .WZR), x (.ADCS .X0 .X1 .X2), x (.ADCS .WZR .W1 .W2),
  x (.SBC .X0 .X1 .X2), x (.SBC .W0 .WZR .W2), x (.SBCS .X0 .X1 .X2), x (.SBCS .W0 .W1 .W2),
  x (.SDIV .X0 .X1 .X2), x (.SDIV .W0 .W1 .W2), x (.UDIV .X0 .X1 .X2), x (.UDIV .W0 .W1 .WZR),
  x (.MADD .X0 .X1 .X2 .X3), x (.MADD .W0 .W1 .W2 .WZR), x (.MSUB .X0 .X1 .X2 .X3), x (.MSUB .W0 .W1 .W2 .WZR),
  x (.SMULH .X0 .X1 .X2), x (.UMULH .X0 .X1 .X2),
  x (.SMADDL .X0 .W1 .W2 .X3), x (.UMADDL .X0 .W1 .W2 .XZR), x (.SMSUBL .X0 .W1 .W2 .X3), x (.UMSUBL .X0 .W1 .W2 .X3),
  -- Logic.
  x (.AND_i .X0 .X1 0xFF), x (.AND_i .SP .X1 (.int64 (-16))), x (.AND_i .W0 .W1 0xF0), x (.AND_i .WSP .WZR 0xF0),
  x (.AND_s .X0 .X1 (sh .X2 4 .ROR)), x (.AND_s .W0 .W1 (sh .W2)), x (.AND_s .XZR .X1 (sh .X2)),
  x (.ANDS_i .X0 .X1 0xFF), x (.ANDS_i .XZR .X1 0xFF), x (.ANDS_i .W0 .W1 0x7),
  x (.ANDS_s .X0 .X1 (sh .X2)), x (.ANDS_s .WZR .W1 (sh .W2 1 .LSR)),
  x (.ORR_i .X0 .X1 0xFF), x (.ORR_i .SP .X1 0x10), x (.ORR_i .W0 .W1 0x1),
  x (.ORR_s .X0 .XZR (sh .X1)), x (.ORR_s .W0 .W1 (sh .W2 8 .LSL)), x (.ORR_s .X0 .X1 (sh .X2 7 .ROR)),
  x (.ORN_s .X0 .X1 (sh .X2)), x (.ORN_s .W0 .WZR (sh .W2)),
  x (.EOR_i .X0 .X1 0xFF), x (.EOR_i .SP .X1 0x10), x (.EOR_i .W0 .W1 0xF),
  x (.EOR_s .X0 .X1 (sh .X2)), x (.EOR_s .W0 .W0 (sh .W0)), x (.EOR_s .XZR .X1 (sh .X2)),
  x (.EON_s .X0 .X1 (sh .X2 2 .LSR)), x (.EON_s .W0 .W1 (sh .W2)),
  x (.BIC_s .X0 .X1 (sh .X2)), x (.BIC_s .W0 .W1 (sh .WZR)),
  x (.BICS_s .X0 .X1 (sh .X2)), x (.BICS_s .WZR .W1 (sh .W2)),
  -- Bitfields and bit manipulation.
  x (.BFM .X0 .X1 8 15), x (.BFM .W0 .W1 28 3), x (.BFM .X0 .XZR 0 7), x (.BFM .XZR .X1 0 7),
  x (.SBFM .X0 .X1 0 7), x (.SBFM .W0 .W1 4 31), x (.UBFM .X0 .X1 3 63), x (.UBFM .W0 .W1 28 3),
  x (.CLZ .X0 .X1), x (.CLZ .W0 .W1), x (.CLS .X0 .X1), x (.CLS .W0 .WZR),
  x (.RBIT .X0 .X1), x (.RBIT .W0 .W1), x (.REV .X0 .X1), x (.REV .W0 .W1),
  x (.REV16 .X0 .X1), x (.REV16 .W0 .W1), x (.REV32 .X0 .X1),
  x (.EXTR .X0 .X1 .X2 8), x (.EXTR .W0 .W1 .W2 4), x (.EXTR .X0 .X1 .X1 0), x (.EXTR .X0 .XZR .X2 63),
  -- Move wide.
  x (.MOVZ .X0 0x1234 .LSL16), x (.MOVZ .W0 0x1234 .LSL0), x (.MOVZ .XZR 1 .LSL0),
  x (.MOVK .X0 0x1234 .LSL32), x (.MOVK .W0 0x1234 .LSL16), x (.MOVK .X0 0x1 .LSL48),
  x (.MOVN .X0 0x1234 .LSL48), x (.MOVN .W0 0x1234 .LSL0),
  -- Variable shifts.
  x (.LSLV .X0 .X1 .X2), x (.LSLV .W0 .W1 .W2), x (.LSRV .X0 .X1 .X2), x (.LSRV .W0 .W1 .WZR),
  x (.ASRV .X0 .X1 .X2), x (.ASRV .W0 .WZR .W2), x (.RORV .X0 .X1 .X2), x (.RORV .W0 .W1 .W2),
  -- Conditional select and compare.
  x (.CSEL .X0 .X1 .X2 .EQ), x (.CSEL .W0 .W1 .WZR .NE), x (.CSEL .X0 .X1 .X2 .AL),
  x (.CSINC .X0 .X1 .X2 .CS), x (.CSINC .W0 .WZR .WZR .LT), x (.CSINC .X0 .X1 .X1 .HI),
  x (.CSINV .X0 .X1 .X2 .MI), x (.CSINV .W0 .WZR .WZR .GE), x (.CSNEG .X0 .X1 .X2 .VS), x (.CSNEG .W0 .W1 .W1 .LE),
  x (.CCMP_reg .X0 .X1 0 .EQ), x (.CCMP_reg .W0 .WZR 5 .GT), x (.CCMP_imm .X0 3 15 .NE), x (.CCMP_imm .W0 0 8 .LS),
  x (.CCMN_reg .X0 .X1 0 .CC), x (.CCMN_reg .W0 .W1 2 .PL), x (.CCMN_imm .X0 3 4 .VC), x (.CCMN_imm .W0 1 1 .NV),
  -- Addressing.
  x (.ADR .X0 lbl), x (.ADR .X0 0x100), x (.ADR .XZR lbl), x (.ADRP .X0 lbl), x (.ADRP .X0 0x1000),
  -- Control flow.
  x (.B lbl), x (.B 0x100), x (.B_cond .EQ lbl), x (.B_cond .LT 0x40), x (.B_cond .AL lbl),
  x (.BL lbl), x (.BL 0x100), x (.BLR .X1), x (.BLR .XZR), x (.BR .X1), x (.BR .X30), x (.RET .X30), x (.RET .X1),
  x (.CBZ .X0 lbl), x (.CBZ .W0 0x20), x (.CBZ .XZR lbl), x (.CBNZ .X0 lbl), x (.CBNZ .W0 lbl), x (.CBNZ .WZR lbl),
  x (.TBZ .X0 3 lbl), x (.TBZ .W0 31 0x10), x (.TBNZ .X0 63 lbl), x (.TBNZ .W0 0 lbl), x (.TBNZ .XZR 5 lbl),
  x (.NOP (w := .W64)), x (.NOP (w := .W32)),
  -- Acquire/release, exclusive, atomic, barriers.
  x (.LDAR .acq false .W64 .X0 .X1), x (.LDAR .acqPc false .W32 .W0 .X1), x (.LDAR .plain true .W64 .X0 .X1),
  x (.LDAR .acq true .W8 .W0 .X1), x (.LDAR .acq false .W16 .W0 .SP), x (.LDAR .acq false .W64 .XZR .X1),
  x (.LDAR .plain true .W32 .WZR .SP),
  x (.STLR .W64 .X0 .X1), x (.STLR .W8 .W0 .X1), x (.STLR .W16 .W0 .SP), x (.STLR .W64 .XZR .X1), x (.STLR .W32 .W0 .X1),
  x (.STXR .plain .W64 .W2 .X0 .X1), x (.STXR .rel .W32 .W2 .W0 .X1), x (.STXR .plain .W8 .WZR .W0 .X1),
  x (.STXR .rel .W16 .W2 .WZR .SP), x (.STXR .plain .W64 .W0 .X0 .X1),
  x (.CAS .plain .W64 .X0 .X2 .X1), x (.CAS .acqRel .W32 .W0 .W2 .X1), x (.CAS .acq .W8 .W0 .W2 .X1),
  x (.CAS .rel .W16 .W0 .W2 .SP), x (.CAS .plain .W64 .XZR .X2 .X1), x (.CAS .plain .W64 .X0 .XZR .X1),
  x (.SWP .plain .W64 .X0 .X2 .X1), x (.SWP .acqRel .W32 .W0 .W2 .X1), x (.SWP .acq .W8 .W0 .W2 .SP),
  x (.SWP .rel .W16 .W0 .WZR .X1), x (.SWP .plain .W64 .XZR .X2 .X1), x (.SWP .plain .W64 .X0 .X0 .X1),
  x (.LDOP .ADD .plain .W64 .X0 .X2 .X1), x (.LDOP .CLR .acq .W32 .W0 .W2 .X1), x (.LDOP .EOR .rel .W8 .W0 .W2 .X1),
  x (.LDOP .SET .acqRel .W16 .W0 .W2 .SP), x (.LDOP .SMAX .plain .W64 .X0 .XZR .X1), x (.LDOP .SMIN .acq .W32 .W0 .W2 .X1),
  x (.LDOP .UMAX .rel .W64 .XZR .X2 .X1), x (.LDOP .UMIN .acqRel .W32 .W0 .W0 .X1),
  x (.LDXP .plain .X0 .X2 .X1), x (.LDXP .acq .W0 .W2 .X1), x (.LDXP .plain .XZR .X2 .SP), x (.LDXP .acq .X0 .X1 .X1),
  x (.STXP .plain .W3 .X0 .X2 .X1), x (.STXP .rel .W3 .W0 .W2 .X1), x (.STXP .plain .WZR .XZR .X2 .SP),
  x (.STXP .rel .W0 .X0 .X0 .X1),
  x (.CASP .plain .X0 .X1 .X2 .X3 .X4), x (.CASP .acq .W4 .W5 .W6 .W7 .X1), x (.CASP .rel .X30 .XZR .X2 .X3 .SP),
  x (.CASP .acqRel .X2 .X3 .X2 .X3 .X2),
  x (.DMB .sy), x (.DMB .ld), x (.DMB .st), x (.DSB .sy), x (.DSB .st), x (.DSB .ld), x (.ISB)]

/-! ## Results -/

/-- All violations over all operations, deduplicated and sorted. -/
def violations : List String :=
  let g := mkStdGen 20241007
  let (mem, g) := initMem g
  let (v, _) := ops.foldl (init := (([] : List String), g)) fun (acc, g) (⟨_, op⟩ : Op) =>
    let (v, g) := checkOpWith (ctorName op).toString op op.deps mem g
    (acc ++ v, g)
  (v.eraseDups.toArray.qsort (· < ·)).toList

/-- info: [] -/
#guard_msgs in
#eval violations

-- The harness does detect omissions: with empty deps, `ADD X0, X1, X2` reads
-- `X1`/`X2` and writes `X0`; `STR X0, [X1, #8]!` reads `X0`/`X1` and writes `X1`;
-- `B.EQ` reads the flags; `MOVK` reads its destination.
/--
info: Operation.ADD_e: RegId.x 0 written but not in defs
Operation.ADD_e: RegId.x 1 read but not in deps
Operation.ADD_e: RegId.x 2 read but not in deps
Operation.B_cond: RegId.nzcv read but not in deps
Operation.MOVK: RegId.x 0 read but not in deps
Operation.STR: RegId.x 0 read but not in deps
Operation.STR: RegId.x 1 read but not in deps
Operation.STR: RegId.x 1 written but not in defs
-/
#guard_msgs in
#eval
  let g := mkStdGen 7
  let (mem, g) := initMem g
  let planted : List Op := [x (.ADD_e .X0 .X1 (ext ⟨.W64, .X2⟩)), x (.STR .X0 (aPre .X1 8)),
    x (.B_cond .EQ lbl), x (.MOVK .X0 0x1234 .LSL16)]
  let (v, _) := planted.foldl (init := (([] : List String), g)) fun (acc, g) (⟨_, op⟩ : Op) =>
    let (v, g) := checkOpWith (ctorName op).toString op
      { defs := match op with | .MOVK .. => [.x 0] | _ => [] } mem g
    (acc ++ v, g)
  IO.println (String.intercalate "\n" (v.eraseDups.toArray.qsort (· < ·)).toList)

-- The per-store check detects swapped or missing `dataRegsPer` entries of
-- `STP X0, X2, [X1]`: the first store's data is `X0`, the second's `X2`.
/--
info: Operation.STP: 1 dataRegsPer entries for [2] stores
Operation.STP: store 0 reads RegId.x 0 but not in its dataRegsPer
Operation.STP: store 0 reads RegId.x 0 but not in its dataRegsPer
Operation.STP: store 1 reads RegId.x 2 but not in its dataRegsPer
-/
#guard_msgs in
#eval
  let g := mkStdGen 7
  let (mem, g) := initMem g
  let op := Operation.STP .X0 .X2 (a .X1)
  let d := op.deps
  let (v1, g) := checkPerStore "Operation.STP" op { d with dataRegsPer := [[.x 2], [.x 0]] } (baseline mem) g
  let (v2, _) := checkPerStore "Operation.STP" op { d with dataRegsPer := [[.x 2]] } (baseline mem) g
  IO.println (String.intercalate "\n" ((v1 ++ v2).toArray.qsort (· < ·)).toList)

-- herd's `NoRet`: on unmapped memory the `rmw` effect is flagged `noRet` exactly
-- when the old value goes to the zero register (`Rt` of `SWP`/`LD<op>`, so every
-- `ST<op>`; the comparand `Rs` of `CAS`), whatever the ordering suffix.
/--
info: [["rmw Kraken.RmwKind.acq noRet 0 w64 0 -> 0"], ["rmw Kraken.RmwKind.acqRel 0 w64 0 -> 2"],
  ["rmw Kraken.RmwKind.acq noRet 0 w32 0 -> 0"], ["rmw Kraken.RmwKind.acq 0 w32 0 -> 0"],
  ["rmw Kraken.RmwKind.rel noRet 0 w32 0 -> 0"], ["rmw Kraken.RmwKind.acqRel 0 w64 0 -> 0"]]
-/
#guard_msgs in
#eval
  let s : MachineData := { regs := ({} : Reg64s).setXReg .X2 2 }
  let cases : List Op := [x (.CAS .acq .W64 .XZR .X0 .X1), x (.CAS .acqRel .W64 .X0 .X2 .X1),
    x (.SWP .acq .W32 .W0 .WZR .X1), x (.SWP .acq .W32 .W0 .W2 .X1),
    x (.LDOP .ADD .rel .W32 .W0 .WZR .X1), x (.LDOP .ADD .acqRel .W64 .X0 .X2 .X1)]
  cases.map fun ⟨_, op⟩ => ((run op s).map fun (o : Outcome) => o.events).flatten

-- Every constructor of `Operation` is reached by `ops`.
open Lean in
/-- info: constructors not covered: [] -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Unit from do
  let env ← getEnv
  let some (.inductInfo info) := env.find? ``Operation | throwError "`Operation` not found"
  let covered := ops.map fun ⟨_, op⟩ => ctorName op
  let missing := info.ctors.filter fun c => !covered.contains c
  logInfo m!"constructors not covered: {missing}"

end DepsTests

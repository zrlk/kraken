/-
**The AArch64 lowering rows at every width, on
`isaLSE2`.** The width-generic twin of
`Lower/EventsA64.lean` and `Lower/EventsA64Inf.lean`, whose 64-bit statements
are unchanged.

Each row is stated once for every register width `w : RegWidth` (`W`/`X`
registers) and, where the instruction carries one, every access width
`m : MemWidth` (`B`/`H`/`W`/`X` forms: `ldarb`, `casb`, `swph`, …). The
access is `m.bytes` (resp. `w.bytes`) wide; the declarations must agree at
that width (`AgreesAt a m.bytes`) for the access to resolve to the single
location `⟨a, m.bytes⟩`.

- loads: `exec_ldrG` (`ldr Wt|Xt, [Xn, #i]`), `exec_ldarG` (`ldar`/`ldapr`/
  `ldaxr`, `k`, `xcl`, any `m`); plain 8/16-bit loads: `exec_ldrb`, `exec_ldrh`;
- stores: `exec_strG`, `exec_stlrG` (any `m`); `exec_strb`, `exec_strh`;
- RMWs: `exec_casG` (operation `casOpG m.bits`), `exec_swpG`, `exec_ldopG`;
- each with `_agrees` (resolved to one event) and `_mapped` (address in `dmem`:
  no event);
- `instrSemInf_<row>G`: the `InstrSemInf` corollaries (32-bit and narrower
  rows on the fuel-free machine), as in `EventsA64Inf.lean`.

The value a load passes on is `v.setWidth w.bits` (resp. `(v.setWidth
m.bits).zeroExtend w.bits`); the value a store writes is the register's,
truncated to the access width (`BitVec.take`), zero-extended to `Val`.
-/
import Kraken.Promising.Lower.EventsA64Inf

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- Read the cell through `execLSE2_of_cellAt_free` and unfold it (the
`EventsA64.lean` macro; local there). -/
local macro "cellW" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free $hc trivial]
  simp [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad, AddrExpr.interpLoad,
    AddrExpr.interpStore, AddrExpr.checkSPAlignment, AddrExpr.eval, MachineData.load, MachineData.store,
    MachineData.loadK, MachineData.storeK, MachineData.rmwK, RegOrSp.interpBase,
    toEv, EvTree.map, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-- The address `[Xn, #i]`. -/
abbrev immAddr (st : State) (n : XReg) (i : Int64) : BitVec 64 :=
  BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt)

/-- The address `[Xn]`. -/
abbrev baseAddr (st : State) (n : XReg) : BitVec 64 := (st.st.1.regs.getXReg n).toBitVec

/-- The operation of `cas` at `b` bits: write `new` iff the old value's low
`b` bits are `cmp`. (`casOp` is the case `b = 64`.) -/
def casOpG (b : Nat) (cmp new : BitVec b) (old : Val) : Option Val :=
  if old.setWidth b = cmp then some (new.setWidth 128) else none

section Rows

variable {st : State} {sz : Nat}

/-- **`ldr Wt|Xt, [Xn, #i]`**, unmapped: one plain `w.bytes`-byte load. -/
theorem exec_ldrG {w : RegWidth} {dst : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨w, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isaLSE2.exec st = some (.access st.decls a w.bytes fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth w.bits) })) := by
  cases w <;> cellW hc [ha, hdm]

theorem exec_ldrG_agrees {w : RegWidth} {dst : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨w, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isaLSE2.exec st = some (.load .plain false ⟨a, w.bytes⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth w.bits) })) := by
  rw [exec_ldrG hc ha hdm, access_agrees hag]

theorem exec_ldrG_mapped {w : RegWidth} {dst : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨w, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (BitVec.ofInt w.bits j) })) := by
  cases w <;> cellW hc [ha, hdm]

/-- **`ldrb Wt, [Xn, #i]`**, unmapped: one plain 1-byte load. -/
theorem exec_ldrb {dst : RegOrZr .W32} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W32, .LDRB dst ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a 1 = none) :
    isaLSE2.exec st = some (.access st.decls a 1 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst ((v.setWidth 8).zeroExtend 32) })) := by
  cellW hc [ha, hdm]

/-- **`ldrh Wt, [Xn, #i]`**, unmapped: one plain 2-byte load. -/
theorem exec_ldrh {dst : RegOrZr .W32} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W32, .LDRH dst ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a 2 = none) :
    isaLSE2.exec st = some (.access st.decls a 2 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst ((v.setWidth 16).zeroExtend 32) })) := by
  cellW hc [ha, hdm]

/-- **`ldar`/`ldapr`/`ldaxr` (+`b`/`h`) `Wt|Xt, [Xn]`** (kind `k`,
exclusivity `xcl`, access width `m`), unmapped: one `m.bytes`-byte load of
kind `k`. -/
theorem exec_ldarG {w : RegWidth} {m : MemWidth} {dst : RegOrZr w} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt st (.instr ⟨w, .LDAR k xcl m dst (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) :
    isaLSE2.exec st = some (.access st.decls (baseAddr st n) m.bytes fun l => .load k xcl l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  cases w <;> cellW hc [hdm]

theorem exec_ldarG_agrees {w : RegWidth} {m : MemWidth} {dst : RegOrZr w} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt st (.instr ⟨w, .LDAR k xcl m dst (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) (hag : st.decls.AgreesAt (baseAddr st n) m.bytes) :
    isaLSE2.exec st = some (.load k xcl ⟨baseAddr st n, m.bytes⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  rw [exec_ldarG hc hdm, access_agrees hag]

theorem exec_ldarG_mapped {w : RegWidth} {m : MemWidth} {dst : RegOrZr w} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt st (.instr ⟨w, .LDAR k xcl m dst (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst ((BitVec.ofInt m.bits j).zeroExtend w.bits) })) := by
  cases w <;> cellW hc [hdm]

/-- **`str Wt|Xt, [Xn, #i]`**, unmapped: one plain `w.bytes`-byte store. -/
theorem exec_strG {w : RegWidth} {src : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨w, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isaLSE2.exec st = some (.access st.decls a w.bytes fun l => .store .plain false l
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cases w <;> cellW hc [ha, hdm]

theorem exec_strG_agrees {w : RegWidth} {src : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨w, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isaLSE2.exec st = some (.store .plain false ⟨a, w.bytes⟩
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_strG hc ha hdm, access_agrees hag]

theorem exec_strG_mapped {w : RegWidth} {src : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨w, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with dmem := Mem.storeInt st.st.1.dmem a w.bytes (st.st.1.regs.getRegOrZr src).toInt })) := by
  cases w <;> cellW hc [ha, hdm]

/-- **`strb Wt, [Xn, #i]`**, unmapped: one plain 1-byte store. -/
theorem exec_strb {src : RegOrZr .W32} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W32, .STRB src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a 1 = none) :
    isaLSE2.exec st = some (.access st.decls a 1 fun l => .store .plain false l
      (((st.st.1.regs.getRegOrZr src).take 8).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cellW hc [ha, hdm]

/-- **`strh Wt, [Xn, #i]`**, unmapped: one plain 2-byte store. -/
theorem exec_strh {src : RegOrZr .W32} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W32, .STRH src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a 2 = none) :
    isaLSE2.exec st = some (.access st.decls a 2 fun l => .store .plain false l
      (((st.st.1.regs.getRegOrZr src).take 16).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cellW hc [ha, hdm]

/-- **`stlr` (+`b`/`h`) `Wt|Xt, [Xn]`**, unmapped: one `m.bytes`-byte
release store of the register's low `m.bits`. -/
theorem exec_stlrG {w : RegWidth} {m : MemWidth} {src : RegOrZr w} {n : XReg}
    (hc : CellAt st (.instr ⟨w, .STLR m src (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) :
    isaLSE2.exec st = some (.access st.decls (baseAddr st n) m.bytes fun l => .store .rel false l
      (((st.st.1.regs.getRegOrZr src).take m.bits).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cases w <;> cellW hc [hdm]

theorem exec_stlrG_agrees {w : RegWidth} {m : MemWidth} {src : RegOrZr w} {n : XReg}
    (hc : CellAt st (.instr ⟨w, .STLR m src (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) (hag : st.decls.AgreesAt (baseAddr st n) m.bytes) :
    isaLSE2.exec st = some (.store .rel false ⟨baseAddr st n, m.bytes⟩
      (((st.st.1.regs.getRegOrZr src).take m.bits).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_stlrG hc hdm, access_agrees hag]

theorem exec_stlrG_mapped {w : RegWidth} {m : MemWidth} {src : RegOrZr w} {n : XReg}
    (hc : CellAt st (.instr ⟨w, .STLR m src (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = some j) :
    isaLSE2.exec st = some (.done (after st sz { st.st.1 with
      dmem := Mem.storeInt st.st.1.dmem (baseAddr st n) m.bytes ((st.st.1.regs.getRegOrZr src).take m.bits).toInt })) := by
  cases w <;> cellW hc [hdm]

/-- **`cas`/`casa`/`casl`/`casal` (+`b`/`h`) `Ws|Xs, Wt|Xt, [Xn]`**,
unmapped: one `m.bytes`-byte RMW of kind `k`, writing `Rt`'s low `m.bits`
iff the old value is `Rs`'s; `Rs` gets the old value. `noRet` iff `Rs` is the
zero register. -/
theorem exec_casG {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .CAS k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) :
    isaLSE2.exec st = some (.access st.decls (baseAddr st n) m.bytes fun l =>
      .rmw k rs.isZr l (casOpG m.bits ((st.st.1.regs.getRegOrZr rs).take m.bits)
        ((st.st.1.regs.getRegOrZr rt).take m.bits)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rs ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  cases w <;> cellW hc [hdm, casOpG]

theorem exec_casG_agrees {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .CAS k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) (hag : st.decls.AgreesAt (baseAddr st n) m.bytes) :
    isaLSE2.exec st = some (.rmw k rs.isZr ⟨baseAddr st n, m.bytes⟩ (casOpG m.bits ((st.st.1.regs.getRegOrZr rs).take m.bits)
        ((st.st.1.regs.getRegOrZr rt).take m.bits)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rs ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  rw [exec_casG hc hdm, access_agrees hag]

theorem exec_casG_mapped {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .CAS k m rs rt (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = some j) :
    ∃ s', isaLSE2.exec st = some (.done (after st sz s')) := by
  cases w <;> by_cases he : BitVec.ofInt m.bits j = (st.st.1.regs.getRegOrZr rs).take m.bits <;>
    exact ⟨_, by cellW hc [hdm, he]⟩

/-- **`swp`/`swpa`/`swpl`/`swpal` (+`b`/`h`)**, unmapped: one `m.bytes`-byte
RMW writing `Rs`'s low `m.bits`; `Rt` gets the old value. -/
theorem exec_swpG {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .SWP k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) :
    isaLSE2.exec st = some (.access st.decls (baseAddr st n) m.bytes fun l =>
      .rmw k rt.isZr l (fun _ => some (((st.st.1.regs.getRegOrZr rs).take m.bits).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rt ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  cases w <;> cellW hc [hdm]

theorem exec_swpG_mapped {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .SWP k m rs rt (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = some j) :
    ∃ s', isaLSE2.exec st = some (.done (after st sz s')) := by
  cases w <;> exact ⟨_, by cellW hc [hdm]⟩

/-- **`ldadd` and the other `ld<op>` (+`a`/`l`/`al`, +`b`/`h`)**, unmapped:
one `m.bytes`-byte RMW writing `op old Rs` at `m.bits`; `Rt` gets the old
value. -/
theorem exec_ldopG {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {op : AtomicOp} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .LDOP op k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none) :
    isaLSE2.exec st = some (.access st.decls (baseAddr st n) m.bytes fun l =>
      .rmw k rt.isZr l (fun old => some ((op.apply (old.setWidth m.bits)
        ((st.st.1.regs.getRegOrZr rs).take m.bits)).setWidth 128))
        fun v => .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rt ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  cases w <;> cellW hc [hdm]

theorem exec_ldopG_mapped {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {op : AtomicOp} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .LDOP op k m rs rt (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = some j) :
    ∃ s', isaLSE2.exec st = some (.done (after st sz s')) := by
  cases w <;> exact ⟨_, by cellW hc [hdm]⟩

/-- **`swp` (+`a`/`l`/`al`, +`b`/`h`)**: the tree resolved at an agreeing
address, one RMW at `⟨Xn, m.bytes⟩`; `instrSemInf_rmw_at` applies to it. -/
theorem exec_swpG_agrees {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨w, .SWP k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none)
    (hag : st.decls.AgreesAt (baseAddr st n) m.bytes) :
    isaLSE2.exec st = some (.rmw k rt.isZr ⟨baseAddr st n, m.bytes⟩
      (fun _ => some (((st.st.1.regs.getRegOrZr rs).take m.bits).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with
        regs := st.st.1.regs.setRegOrZr rt ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  rw [exec_swpG hc hdm, access_agrees hag]

/-- **`ldadd` and the other `ld<op>` (+`a`/`l`/`al`, +`b`/`h`)**: the tree
resolved at an agreeing address; `instrSemInf_rmw_at` applies to it. -/
theorem exec_ldopG_agrees {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {op : AtomicOp}
    {k : RmwKind} (hc : CellAt st (.instr ⟨w, .LDOP op k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (baseAddr st n) m.bytes = none)
    (hag : st.decls.AgreesAt (baseAddr st n) m.bytes) :
    isaLSE2.exec st = some (.rmw k rt.isZr ⟨baseAddr st n, m.bytes⟩
      (fun old => some ((op.apply (old.setWidth m.bits) ((st.st.1.regs.getRegOrZr rs).take m.bits)).setWidth 128))
      fun v => .done (after st sz { st.st.1 with
        regs := st.st.1.regs.setRegOrZr rt ((v.setWidth m.bits).zeroExtend w.bits) })) := by
  rw [exec_ldopG hc hdm, access_agrees hag]

end Rows

/-! The 32-bit instances the lowering pilot uses (`ldr w`, `str w`): 4-byte
events. -/

example {st : State} {sz : Nat} {dst : RegOrZr .W32} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W32, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a 4 = none) (hag : st.decls.AgreesAt a 4) :
    isaLSE2.exec st = some (.load .plain false ⟨a, 4⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 32) })) :=
  exec_ldrG_agrees hc ha hdm hag

example {st : State} {sz : Nat} {src : RegOrZr .W32} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W32, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr st n i = a) (hdm : Mem.loadInt st.st.1.dmem a 4 = none) (hag : st.decls.AgreesAt a 4) :
    isaLSE2.exec st = some (.store .plain false ⟨a, 4⟩
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) :=
  exec_strG_agrees hc ha hdm hag

/-! ## On the fuel-free machine -/

section Inf

variable (A : Arch) (tid : Nat) {c c' : Config isaLSE2} {t : Thread isaLSE2}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`ldr Wt|Xt, [Xn, #i]`**: one plain read of `⟨a, w.bytes⟩`. -/
theorem instrSemInf_ldrG {w : RegWidth} {dst : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt (stOf t) (.instr ⟨w, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : immAddr (stOf t) n i = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, w.bytes⟩ ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.setRegOrZr dst (v.setWidth w.bits) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (exec_ldrG_agrees hc ha hdm hag)

/-- **`ldar`/`ldapr`/`ldaxr` (+`b`/`h`) `Wt|Xt, [Xn]`**: one read of kind `k`
of `⟨Xn, m.bytes⟩`. -/
theorem instrSemInf_ldarG {w : RegWidth} {m : MemWidth} {dst : RegOrZr w} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt (stOf t) (.instr ⟨w, .LDAR k xcl m dst (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (baseAddr (stOf t) n) m.bytes = none)
    (hag : (stOf t).decls.AgreesAt (baseAddr (stOf t) n) m.bytes) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) k xcl ⟨baseAddr (stOf t) n, m.bytes⟩ ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := (stOf t).st.1.regs.setRegOrZr dst ((v.setWidth m.bits).zeroExtend w.bits) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (exec_ldarG_agrees hc hdm hag)

/-- **`str Wt|Xt, [Xn, #i]`**: one plain write to `⟨a, w.bytes⟩`. -/
theorem instrSemInf_strG {w : RegWidth} {src : RegOrZr w} {n : XReg} {i : Int64}
    (hc : CellAt (stOf t) (.instr ⟨w, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : immAddr (stOf t) n i = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false ⟨a, w.bytes⟩
        (((stOf t).st.1.regs.getRegOrZr src).setWidth 128) none ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (exec_strG_agrees hc ha hdm hag)

/-- **`stlr` (+`b`/`h`) `Wt|Xt, [Xn]`**: one release write to
`⟨Xn, m.bytes⟩`. -/
theorem instrSemInf_stlrG {w : RegWidth} {m : MemWidth} {src : RegOrZr w} {n : XReg}
    (hc : CellAt (stOf t) (.instr ⟨w, .STLR m src (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (baseAddr (stOf t) n) m.bytes = none)
    (hag : (stOf t).decls.AgreesAt (baseAddr (stOf t) n) m.bytes) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .rel false ⟨baseAddr (stOf t) n, m.bytes⟩
        ((((stOf t).st.1.regs.getRegOrZr src).take m.bits).setWidth 128) none ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (exec_stlrG_agrees hc hdm hag)

/-- **`cas`/`casa`/`casl`/`casal` (+`b`/`h`) `Ws|Xs, Wt|Xt, [Xn]`**: one RMW
at `⟨Xn, m.bytes⟩` with operation `casOpG m.bits Rs Rt` (no write when the
comparison fails). -/
theorem instrSemInf_casG {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt (stOf t) (.instr ⟨w, .CAS k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (baseAddr (stOf t) n) m.bytes = none)
    (hag : (stOf t).decls.AgreesAt (baseAddr (stOf t) n) m.bytes) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (if rs.isZr then .plain else (A.rmwKind k).loadKind) false ⟨baseAddr (stOf t) n, m.bytes⟩ rs.isZr ∧
      ((casOpG m.bits (((stOf t).st.1.regs.getRegOrZr rs).take m.bits)
            (((stOf t).st.1.regs.getRegOrZr rt).take m.bits) old = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, casOpG m.bits (((stOf t).st.1.regs.getRegOrZr rs).take m.bits)
            (((stOf t).st.1.regs.getRegOrZr rt).take m.bits) old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true ⟨baseAddr (stOf t) n, m.bytes⟩ new
            (some tr) (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) rs.isZr ⟨baseAddr (stOf t) n, m.bytes⟩
            { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := (stOf t).st.1.regs.setRegOrZr rs ((old.setWidth m.bits).zeroExtend w.bits) }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_iff A tid ht (exec_casG_agrees hc hdm hag)

/-- **`swp` at every width on the fuel-free machine**: `instrSemInf_rmw_at`
at the resolved tree (`exec_swpG_agrees`). -/
theorem instrSemInf_swpG {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {k : RmwKind}
    (hc : CellAt (stOf t) (.instr ⟨w, .SWP k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (baseAddr (stOf t) n) m.bytes = none)
    (hag : (stOf t).decls.AgreesAt (baseAddr (stOf t) n) m.bytes) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (if rt.isZr then .plain else (A.rmwKind k).loadKind) false ⟨baseAddr (stOf t) n, m.bytes⟩ rt.isZr ∧
      ((some ((((stOf t).st.1.regs.getRegOrZr rs).take m.bits).setWidth 128) = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, some ((((stOf t).st.1.regs.getRegOrZr rs).take m.bits).setWidth 128) = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true ⟨baseAddr (stOf t) n, m.bytes⟩ new
            (some tr) (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) rt.isZr ⟨baseAddr (stOf t) n, m.bytes⟩
            { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := (stOf t).st.1.regs.setRegOrZr rt ((old.setWidth m.bits).zeroExtend w.bits) }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (exec_swpG_agrees hc hdm hag)

end Inf

end Kraken.Promising.Lower.A64

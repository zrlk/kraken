/-
**The x64 lowering rows at every operand width,
on `X64.isa` (TSO).** The width-generic twin of
`Lower/EventsX64.lean` and `Lower/EventsX64Inf.lean`, whose 64-bit statements
are unchanged.

Each row is stated once for every operand width `w : Width` (`b`/`w`/`l`/`q`
suffixes: `movl`, `lock cmpxchgl`, `xchgl`, `lock xaddl`, …) under 64-bit
addressing (`opW w o`, i.e. `Instr.regular .W64 w o`). The access is
`w.bytes` wide; with `AgreesAt a w.bytes` it resolves to the single location
`⟨a, w.bytes⟩`.

- `exec_loadG` (`mov r, [m]`), `exec_storeG` (`mov [m], r`);
- `exec_cmpxchgG` (`lock cmpxchg [m], r`, operation `cmpxOpG`, post-state
  `cmpxPostG w`), `exec_xchgG`, `exec_xaddG`;
- each with `_agrees` and `_mapped`, and an `InstrSemInf` corollary
  `instrSemInf_<row>G`.

A load passes on `v.setWidth w.bits` and `regs.set r` writes it at width `w`
(for `w = .W32` x86 zero-extends into the 64-bit register; `Reg64s.set`
does).
-/
import Kraken.Promising.Lower.EventsX64Inf

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- Read the cell through `exec_of_cellAt` and unfold it (the
`EventsX64.lean` macro; local there). -/
local macro "cellW" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, Width.bytesv, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

/-- A `w`-bit, 64-bit-addressed instruction (`op64` is `opW .W64`). -/
abbrev opW (w : Width) (o : Operation w) : Directive := .instr (.regular .W64 w o)

/-- The operation of `cmpxchg` at `b` bits: write `new` iff the old value's
low `b` bits are `acc`; a failed compare writes nothing. (`cmpxOp` is the
case `b = 64`.) -/
def cmpxOpG {b : Nat} (acc new : BitVec b) (old : Val) : Option Val :=
  if old.setWidth b = acc then some (new.setWidth 128) else none

/-- The machine data after a `w`-bit `cmpxchg` read `old`: the flags of
`acc - old` (`acc` the low `w` bits of `rax`), and on failure `acc := old`.
(`cmpxPost` is the case `w = .W64`.) -/
def cmpxPostG (w : Width) (s : MachineData) (old : BitVec w.bits) : MachineData :=
  let acc := s.regs.get (.low .rax w)
  let d := acc - old
  let status := StatusFlags.from_result d {
      cf := d.unsigned != acc.unsigned - old.unsigned
      af := (d.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
      of := d.signed != acc.signed - old.signed }
  let s := if old == acc then s else s.setReg (.low .rax w) old
  { s with status }

section Rows

variable {st : State} {sz : Nat}

/-- **`mov r, [m]`** at width `w`, unmapped: one plain `w.bytes`-byte load. -/
theorem exec_loadG {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isa.exec st = some (.access st.decls a w.bytes fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth w.bits) })) := by
  cases w <;> cellW hc [ha, hdm]

theorem exec_loadG_agrees {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isa.exec st = some (.load .plain false ⟨a, w.bytes⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth w.bits) })) := by
  rw [exec_loadG hc ha hdm, access_agrees hag]

theorem exec_loadG_mapped {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set r (BitVec.ofInt w.bits j) })) := by
  cases w <;> cellW hc [ha, hdm]

/-- **`mov [m], r`** at width `w`, unmapped: one plain `w.bytes`-byte store. -/
theorem exec_storeG {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isa.exec st = some (.access st.decls a w.bytes fun l => .store .plain false l
      ((st.st.1.regs.get r).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cases w <;> cellW hc [ha, hdm]

theorem exec_storeG_agrees {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isa.exec st = some (.store .plain false ⟨a, w.bytes⟩
      ((st.st.1.regs.get r).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_storeG hc ha hdm, access_agrees hag]

theorem exec_storeG_mapped {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    isa.exec st = some (.done (after st sz
      { st.st.1 with dmem := Mem.storeInt st.st.1.dmem a w.bytes (st.st.1.regs.get r).toInt })) := by
  cases w <;> cellW hc [ha, hdm]

/-- **`lock cmpxchg [m], r`** at width `w`, unmapped: one locked (`.acqRel`)
RMW, writing `r` iff the old value is `rax`'s low `w` bits (`cmpxOpG`); then
`cmpxPostG w`. -/
theorem exec_cmpxchgG {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isa.exec st = some (.access st.decls a w.bytes fun l =>
      .rmw .acqRel false l (cmpxOpG (st.st.1.regs.get (.low .rax w)) (st.st.1.regs.get r)) fun v =>
      .done (after st sz (cmpxPostG w st.st.1 (v.setWidth w.bits)))) := by
  cases w <;> cellW hc [ha, hdm, cmpxOpG, cmpxPostG]

theorem exec_cmpxchgG_agrees {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt st (opW w (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isa.exec st = some (.rmw .acqRel false ⟨a, w.bytes⟩
      (cmpxOpG (st.st.1.regs.get (.low .rax w)) (st.st.1.regs.get r)) fun v =>
      .done (after st sz (cmpxPostG w st.st.1 (v.setWidth w.bits)))) := by
  rw [exec_cmpxchgG hc ha hdm, access_agrees hag]

theorem exec_cmpxchgG_mapped {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt st (opW w (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    ∃ s', isa.exec st = some (.done (after st sz s')) := by
  by_cases he : BitVec.ofInt w.bits j = st.st.1.regs.get (.low .rax w) <;> cases w <;>
    (try simp at he) <;> exact ⟨_, by cellW hc [ha, hdm, he]⟩

/-- **`xchg r, [m]`** at width `w` (locked with or without the prefix),
unmapped: one locked RMW writing `r`; `r` gets the old value. -/
theorem exec_xchgG {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isa.exec st = some (.access st.decls a w.bytes fun l =>
      .rmw .acqRel false l (fun _ => some ((st.st.1.regs.get r).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth w.bits) })) := by
  cases w <;> cellW hc [ha, hdm]

theorem exec_xchgG_agrees {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isa.exec st = some (.rmw .acqRel false ⟨a, w.bytes⟩ (fun _ => some ((st.st.1.regs.get r).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth w.bits) })) := by
  rw [exec_xchgG hc ha hdm, access_agrees hag]

theorem exec_xchgG_mapped {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    ∃ s', isa.exec st = some (.done (after st sz s')) := by
  cases w <;> exact ⟨_, by cellW hc [ha, hdm]⟩

/-- **`lock xadd [m], r`** at width `w`, unmapped: one locked RMW writing
`old + r`; `r` gets the old value, the flags those of the addition. -/
theorem exec_xaddG {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none) :
    isa.exec st = some (.access st.decls a w.bytes fun l =>
      .rmw .acqRel false l (fun old => some ((old.setWidth w.bits + st.st.1.regs.get r).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with
        regs := st.st.1.regs.set r (v.setWidth w.bits)
        status := LockBinOp.add.status (v.setWidth w.bits) (st.st.1.regs.get r)
          (v.setWidth w.bits + st.st.1.regs.get r) false })) := by
  cases w <;> cellW hc [ha, hdm]

theorem exec_xaddG_agrees {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a w.bytes = none)
    (hag : st.decls.AgreesAt a w.bytes) :
    isa.exec st = some (.rmw .acqRel false ⟨a, w.bytes⟩
      (fun old => some ((old.setWidth w.bits + st.st.1.regs.get r).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with
        regs := st.st.1.regs.set r (v.setWidth w.bits)
        status := LockBinOp.add.status (v.setWidth w.bits) (st.st.1.regs.get r)
          (v.setWidth w.bits + st.st.1.regs.get r) false })) := by
  rw [exec_xaddG hc ha hdm, access_agrees hag]

theorem exec_xaddG_mapped {w : Width} {r : Reg w} {m : AddrExpr} (hc : CellAt st (opW w (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a w.bytes = some j) :
    ∃ s', isa.exec st = some (.done (after st sz s')) := by
  cases w <;> exact ⟨_, by cellW hc [ha, hdm]⟩

end Rows

/-! ## On the fuel-free machine -/

section Inf

variable (A : Arch) (tid : Nat) {c c' : Config isa} {t : Thread isa}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`mov r, [m]`** at width `w`: one plain read of `⟨a, w.bytes⟩`. -/
theorem instrSemInf_loadG {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt (stOf t) (opW w (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, w.bytes⟩ ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.set r (v.setWidth w.bits) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (exec_loadG_agrees hc ha hdm hag)

/-- **`mov [m], r`** at width `w`: one plain write to `⟨a, w.bytes⟩`. -/
theorem instrSemInf_storeG {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt (stOf t) (opW w (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false ⟨a, w.bytes⟩
        (((stOf t).st.1.regs.get r).setWidth 128) none ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (exec_storeG_agrees hc ha hdm hag)

/-- **`lock cmpxchg [m], r`** at width `w`: one locked RMW at `⟨a, w.bytes⟩`
with operation `cmpxOpG rax r`; a failed compare is the `op old = none`
branch (no write). -/
theorem instrSemInf_cmpxchgG {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt (stOf t) (opW w (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, w.bytes⟩ false ∧
      ((cmpxOpG ((stOf t).st.1.regs.get (.low .rax w)) ((stOf t).st.1.regs.get r) old = none ∧
          cf = rmwFenceOpt A c1) ∨
       (∃ new c2, cmpxOpG ((stOf t).st.1.regs.get (.low .rax w)) ((stOf t).st.1.regs.get r) old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, w.bytes⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, w.bytes⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz (cmpxPostG w (stOf t).st.1 (old.setWidth w.bits))) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (exec_cmpxchgG_agrees hc ha hdm hag)

/-- **`xchg r, [m]`** at width `w`: one locked RMW at `⟨a, w.bytes⟩` writing
`r` (the operation always writes). -/
theorem instrSemInf_xchgG {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt (stOf t) (opW w (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, w.bytes⟩ false ∧
      ((some (((stOf t).st.1.regs.get r).setWidth 128) = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, some (((stOf t).st.1.regs.get r).setWidth 128) = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, w.bytes⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, w.bytes⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.set r (old.setWidth w.bits) }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (op := fun _ => some (((stOf t).st.1.regs.get r).setWidth 128))
    (exec_xchgG_agrees hc ha hdm hag)

/-- **`lock xadd [m], r`** at width `w`: one locked RMW at `⟨a, w.bytes⟩`
writing `old + r`. -/
theorem instrSemInf_xaddG {w : Width} {r : Reg w} {m : AddrExpr}
    (hc : CellAt (stOf t) (opW w (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a w.bytes = none)
    (hag : (stOf t).decls.AgreesAt a w.bytes) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, w.bytes⟩ false ∧
      ((some ((old.setWidth w.bits + (stOf t).st.1.regs.get r).setWidth 128) = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, some ((old.setWidth w.bits + (stOf t).st.1.regs.get r).setWidth 128) = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, w.bytes⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, w.bytes⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := (stOf t).st.1.regs.set r (old.setWidth w.bits)
          status := LockBinOp.add.status (old.setWidth w.bits) ((stOf t).st.1.regs.get r)
            (old.setWidth w.bits + (stOf t).st.1.regs.get r) false }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (exec_xaddG_agrees hc ha hdm hag)

end Inf

end Kraken.Promising.Lower.X64

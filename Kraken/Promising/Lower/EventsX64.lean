/-
**Which memory event each x64 lowering-table instruction
is, on `X64.isa` (TSO).** The x64 twin of
`Lower/EventsA64.lean`.

For each lowering-table row, the `EvTree` that `X64.isa.exec` gives at a cell
holding the row's instruction. Generic over registers, addressing modes
(`eaddr`: the effective address of any `AddrExpr` under 64-bit addressing),
pc, cell size `sz`, executable layout and declarations; the only hypothesis
on the cell is `CellAt st d sz`. All rows are 64-bit (`Instr.regular .W64
.W64`).

## Shapes

- **Memory rows**, address `a` not in the thread-private `dmem` (`hdm`):
  `exec_<row>` gives `.access st.decls a 8 (fun l => <event at l>)`;
  `exec_<row>_agrees` adds `st.decls.AgreesAt a 8` and resolves it to the
  single event at `⟨a, 8⟩`; `exec_<row>_mapped` (address in `dmem`) is a
  no-event step.
  - load: `exec_load` (`mov r64, [m]`), one plain `.load`;
  - store: `exec_store` (`mov [m], r64`), one plain non-exclusive `.store`;
  - RMWs, all locked (`.acqRel`; under TSO `Arch.rmwFence` adds the
    surrounding `fence .sy`), `noRet = false` (x86 has no `NoRet` atomics):
    `exec_cmpxchg` (`lock cmpxchg [m], r64`, operation `cmpxOp rax r`: a failed
    compare writes nothing), `exec_xchg` (`xchg r64, [m]`, locked
    with or without the prefix), `exec_xadd` (`lock xadd [m], r64`); the
    `_mapped` forms are existential in the new private state.
- **Fence**: `exec_mfence`, one `.fence .sy`.
- **16 bytes**: `exec_cmpxchg16b` (`lock cmpxchg16b [m]`, 16-aligned): one
  16-byte `.rmw` (`rmw16`); `exec_movdqa_load`/`exec_movdqa_store` (aligned
  `movdqa`, which the SDM guarantees single-copy atomic): one 16-byte event;
  `exec_movups_load`/`exec_movups_store` (unaligned-form `movups`, not single-copy atomic):
  **two** 8-byte events, lower address first, both pieces unmapped and within
  one cache line.
- **No-event rows** (`.done`): `exec_mov_rr`, `exec_mov_ri`, `exec_lea`,
  `exec_add_rr` (`exec_add_flags` with the flags, `addFlags_cf` the carry), `exec_cmp_rr`, `exec_jmp_label`, `exec_jcc`, `exec_jmp_reg`.
- **Calls** (`call`, `ret` touch the stack, `X64/Semantics.lean` `.call`/`.ret`):
  `exec_call_label`, `exec_call_reg`, `exec_ret` with the stack slot mapped in
  `dmem` (`[rsp-8, rsp)` for `call`, `[rsp, rsp+8)` for `ret`): **no event**.
  With the slot unmapped the step is a **shared event**: `call` is one plain
  8-byte store of the return address at `rsp - 8` (`exec_call_label_shared`,
  `exec_call_reg_shared`), `ret` one plain 8-byte load at `rsp`
  (`exec_ret_shared`).

`Lower/EventsX64Inf.lean` composes these with the `InstrSemInf` shape lemmas.
-/
import Kraken.Promising.Lower.Events
import Kraken.Promising.SLR.X64Bridge
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **The cell at `st`'s pc is `d`, of `sz` bytes**: `st`'s executable is
validly laid out, `codeAt` finds `d` at the pc (behind any labels), and the
pc is short of the end address. Any executable, any layout, any
declarations. -/
structure CellAt (st : State) (d : Directive) (sz : Nat) : Prop where
  valid : Kraken.Executable.ValidLayout st.exe
  ne : (st.st.2 == st.endPc) = false
  code : ∃ rest, Kraken.Executable.codeAt st.exe st.st.2 = (d, sz) :: rest

/-- The cell's address range, for operand interpretation. -/
abbrev rangeOf (st : State) (sz : Nat) : Std.Rco Int64 := .mk st.st.2 (st.st.2 + .ofNat sz)

/-- **`isa`'s tree at a cell, any declarations** (`exec_eq_of_codeAt` without
`decls = {}`): the translation of the cell's interpretation, with
fall-through and jump continuations that stop at the next machine state. -/
theorem exec_of_cellAt {st : State} {d : Directive} {sz : Nat} (h : CellAt st d sz) :
    exec st = some ((toEv st.decls (@Directive.interp (_root_.Executable.labels st.exe) d st.st.1
      (rangeOf st sz) (fun s' => .done (s', st.st.2 + .ofNat sz))
      (fun pc s' => .done (s', pc)))).map fun s => { st with st := s }) := by
  obtain ⟨hv, hne, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at hcode hat hne hv ⊢
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [exec, hdir, Option.isNone_some, Bool.or_false, hne, Bool.false_eq_true, ↓reduceIte]
  congr 2
  unfold Executable.step
  letI := Executable.labels exe
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

theorem map_access {σ τ : Type} (f : σ → τ) (ds : Decls) (a : BitVec 64) (n : Nat) (k : Loc → EvTree σ) :
    (EvTree.access ds a n k).map f = EvTree.access ds a n fun l => (k l).map f := by
  unfold EvTree.access; split <;> rfl

/-- An access at an agreeing address is its own footprint. -/
theorem access_agrees {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} (h : ds.AgreesAt a n)
    (k : Loc → EvTree σ) : EvTree.access ds a n k = k ⟨a, n⟩ := by
  rw [EvTree.access_of_agreesAt h, EvTree.access_empty]

/-- The state after a cell: machine data `s'`, pc `pc + sz`. -/
abbrev after (st : State) (sz : Nat) (s' : MachineData) : State := { st with st := (s', st.st.2 + .ofNat sz) }

/-- The state with machine data `s'` at pc `pc`. -/
abbrev jumpTo (st : State) (s' : MachineData) (pc : Int64) : State := { st with st := (s', pc) }

/-- **The effective address of a memory operand** under 64-bit addressing, at
the cell. -/
abbrev eaddr (st : State) (sz : Nat) (m : AddrExpr) : BitVec 64 :=
  (@AddrExpr.interp (_root_.Executable.labels st.exe) ⟨.W64⟩ m st.st.1.regs (rangeOf st sz)).zeroExtend 64

/-- The effective address of `o(%r)`: the base register plus the
displacement. -/
theorem eaddr_reg_disp (st : State) (sz : Nat) (r : Reg64) (o : Int64) :
    eaddr st sz { base := some (.reg r), idx := none, disp := .int64 o } =
      BitVec.ofInt 64 ((st.st.1.regs.get64 r).toInt + o.toInt) := by
  simp [eaddr, AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.take]

/-- The effective address of `0(%r)` (`(%r)`): the base register. -/
theorem eaddr_reg (st : State) (sz : Nat) (r : Reg64) :
    eaddr st sz { base := some (.reg r), idx := none, disp := .int64 0 } = st.st.1.regs.get64 r := by
  simp [eaddr, AddrExpr.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.take]

/-- A 64-bit, 64-bit-addressed instruction. -/
abbrev op64 (o : Operation .W64) : Directive := .instr (.regular .W64 .W64 o)

/-- `rsp`'s value. -/
abbrev rspOf (s : MachineData) : BitVec 64 := s.regs.get64 .rsp

/-- Read the cell through `exec_of_cellAt` and unfold it. -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  try simp only [rspOf, Reg64s.get64] at *
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    MachineData.set, MachineData.load, MachineData.store, MachineData.rmwK, RegOrMem.rmw,
    MachineData.setReg, RelRegOrMem.interp, ConstExpr.interp, Width.bytesv, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

section Loads

variable {st : State} {sz : Nat}

/-- **`mov r64, [m]`**, address unmapped in `dmem`: one plain 8-byte load. -/
theorem exec_load {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth 64) })) := by
  cell hc [ha, hdm]

/-- `mov r64, [m]` at an agreeing address: the load of `⟨a, 8⟩`. -/
theorem exec_load_agrees {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none)
    (hag : st.decls.AgreesAt a 8) :
    isa.exec st = some (.load .plain false ⟨a, 8⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth 64) })) := by
  rw [exec_load hc ha hdm, access_agrees hag]

/-- `mov r64, [m]` at an address mapped in `dmem`: no event. -/
theorem exec_load_mapped {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set r (BitVec.ofInt 64 j) })) := by
  cell hc [ha, hdm]

end Loads

section Stores

variable {st : State} {sz : Nat}

/-- **`mov [m], r64`**, address unmapped: one plain, non-exclusive 8-byte
store. -/
theorem exec_store {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l => .store .plain false l
      ((st.st.1.regs.get r).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cell hc [ha, hdm]

theorem exec_store_agrees {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none)
    (hag : st.decls.AgreesAt a 8) :
    isa.exec st = some (.store .plain false ⟨a, 8⟩
      ((st.st.1.regs.get r).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_store hc ha hdm, access_agrees hag]

/-- `mov [m], r64` at a mapped address: no event (`dmem` updated). -/
theorem exec_store_mapped {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isa.exec st = some (.done (after st sz
      { st.st.1 with dmem := Mem.storeInt st.st.1.dmem a 8 (st.st.1.regs.get r).toInt })) := by
  cell hc [ha, hdm]

end Stores

section Rmw

variable {st : State} {sz : Nat}

/-- The operation of `cmpxchg`: write `new` iff the old value is `acc` (`rax`);
a failed compare writes nothing. -/
def cmpxOp (acc new : BitVec 64) (old : Val) : Option Val :=
  if old.setWidth 64 = acc then some (new.setWidth 128) else none

/-- The machine data after `cmpxchg` read `old`: the flags of `rax - old`
(`ZF` iff equal), and on failure `rax := old`. -/
def cmpxPost (s : MachineData) (old : BitVec 64) : MachineData :=
  let acc := s.regs.get (.low .rax .W64)
  let d := acc - old
  let status := StatusFlags.from_result d {
      cf := d.unsigned != acc.unsigned - old.unsigned
      af := (d.take 4).unsigned != (acc.take 4).unsigned - (old.take 4).unsigned,
      of := d.signed != acc.signed - old.signed }
  let s := if old == acc then s else s.setReg (.low .rax .W64) old
  { s with status }

/-- **`lock cmpxchg [m], r64`**, address unmapped: one locked (`.acqRel`) RMW,
writing `r` iff the old value is `rax`'s (`cmpxOp`); then `cmpxPost`. -/
theorem exec_cmpxchg {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l =>
      .rmw .acqRel false l (cmpxOp (st.st.1.regs.get (.low .rax .W64)) (st.st.1.regs.get r)) fun v =>
      .done (after st sz (cmpxPost st.st.1 (v.setWidth 64)))) := by
  cell hc [ha, hdm, cmpxOp, cmpxPost]

theorem exec_cmpxchg_agrees {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none)
    (hag : st.decls.AgreesAt a 8) :
    isa.exec st = some (.rmw .acqRel false ⟨a, 8⟩ (cmpxOp (st.st.1.regs.get (.low .rax .W64)) (st.st.1.regs.get r))
      fun v => .done (after st sz (cmpxPost st.st.1 (v.setWidth 64)))) := by
  rw [exec_cmpxchg hc ha hdm, access_agrees hag]

/-- `lock cmpxchg` at a mapped address: no event. -/
theorem exec_cmpxchg_mapped {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    ∃ s', isa.exec st = some (.done (after st sz s')) := by
  by_cases he : BitVec.ofInt 64 j = st.st.1.regs.rax.toBitVec <;>
    exact ⟨_, by cell hc [ha, hdm, he]⟩

/-- **`xchg r64, [m]`** (locked with or without the prefix), address
unmapped: one locked RMW writing `r`; `r` gets the old value. -/
theorem exec_xchg {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l =>
      .rmw .acqRel false l (fun _ => some ((st.st.1.regs.get r).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.set r (v.setWidth 64) })) := by
  cell hc [ha, hdm]

theorem exec_xchg_mapped {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    ∃ s', isa.exec st = some (.done (after st sz s')) :=
  ⟨_, by cell hc [ha, hdm]⟩

/-- **`lock xadd [m], r64`**, address unmapped: one locked RMW writing
`old + r`; `r` gets the old value, the flags those of the addition. -/
theorem exec_xadd {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isa.exec st = some (.access st.decls a 8 fun l =>
      .rmw .acqRel false l (fun old => some ((old.setWidth 64 + st.st.1.regs.get r).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with
        regs := st.st.1.regs.set r (v.setWidth 64)
        status := LockBinOp.add.status (v.setWidth 64) (st.st.1.regs.get r)
          (v.setWidth 64 + st.st.1.regs.get r) false })) := by
  cell hc [ha, hdm]

theorem exec_xadd_mapped {r : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    ∃ s', isa.exec st = some (.done (after st sz s')) :=
  ⟨_, by cell hc [ha, hdm]⟩

end Rmw

section Fence

variable {st : State} {sz : Nat}

/-- **`mfence`**: one `.sy` fence. -/
theorem exec_mfence (hc : CellAt st (op64 .mfence) sz) :
    isa.exec st = some (.fence .sy fun _ => .done (after st sz st.st.1)) := by
  cell hc []

end Fence


/-! ## 16-byte accesses

`lock cmpxchg16b` (16-aligned, else `#GP`) is one 16-byte RMW (`rmw16`);
the aligned `movdqa` (and `movaps`/`movapd`), which the SDM guarantees
single-copy atomic, is one 16-byte event. Unaligned-form 16-byte moves
(`movups`, `movdqu`) are two 8-byte single-copy-atomic pieces in address
order (`loadPieces`/`storePieces`) and are not stated here. -/

/-- Read a vector cell through `exec_of_cellAt` and unfold it. -/
local macro "cellV" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show X64.exec _ = _
  rw [exec_of_cellAt $hc]
  try simp only [eaddr, BitVec.setWidth_eq] at *
  simp [Directive.interp, Instr.interp, AvxOperation.interp, toEv, EvTree.map, AvxRegOrMem.interp,
    MachineData.loadAvx, MachineData.storeAvx, MachineData.setAvxLegacy, MachineData.setAvxLegacyReg,
    MachineData.rmw16K, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

section Vec

variable {st : State} {sz : Nat}

omit st sz in
private theorem w128_beq : (AvxWidth.W128 == AvxWidth.W128) = true := rfl

/-- `cmpxchg16b`'s comparand `rdx:rax`. -/
abbrev acc16 (s : MachineData) : BitVec 128 := s.regs.get64 .rdx ++ s.regs.get64 .rax

/-- `cmpxchg16b`'s new value `rcx:rbx`. -/
abbrev new16 (s : MachineData) : BitVec 128 := s.regs.get64 .rcx ++ s.regs.get64 .rbx

/-- The operation of `cmpxchg16b`: write `new` iff the old value is `acc`. -/
def cmpx16Op (acc new : BitVec 128) (old : Val) : Option Val := if old == acc then some new else none

/-- The machine data after `cmpxchg16b` read `old`: `ZF` iff equal, and on
failure `rdx:rax := old`. -/
def cmpx16Post (s : MachineData) (old : BitVec 128) : MachineData :=
  let s' := if old == acc16 s then s else
    { s with regs := (s.regs.set64 .rax (old.extractLsb' 0 64)).set64 .rdx (old.extractLsb' 64 64) }
  { s' with status := { s'.status with zf := old == acc16 s } }

/-- **`lock cmpxchg16b [m]`**, 16-aligned, unmapped: one locked 16-byte RMW
(`rmw16`), writing `rcx:rbx` iff the old value is `rdx:rax`. -/
theorem exec_cmpxchg16b {m : AddrExpr} (hc : CellAt st (.instr (.avx .W64 .W128 (.cmpxchg16b true m))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (h16 : isAligned 16 a = true)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none) :
    isa.exec st = some (.access st.decls a 16 fun l =>
      .rmw .acqRel false l (cmpx16Op (acc16 st.st.1) (new16 st.st.1)) fun v =>
      .done (after st sz (cmpx16Post st.st.1 v))) := by
  show X64.exec _ = _
  rw [exec_of_cellAt hc]
  simp only [eaddr] at ha
  simp only [Directive.interp, Instr.interp, AvxOperation.interp, ha, h16, ite_true, MachineData.rmw16K, hdm,
    toEv, EvTree.map, map_access]
  rfl

/-- **Aligned `movdqa xmm, [m]`**, unmapped: one plain 16-byte load. -/
theorem exec_movdqa_load {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt st (.instr (.avx .W64 .W128 (.movdqa (.avx x) (.mem m)))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (h16 : isAligned 16 a = true)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none) :
    isa.exec st = some (.access st.decls a 16 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with zmms := st.st.1.zmms.setLegacy x v })) := by
  cellV hc [ha, h16, hdm, w128_beq]

/-- **Aligned `movdqa [m], xmm`**, unmapped: one plain 16-byte store. -/
theorem exec_movdqa_store {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt st (.instr (.avx .W64 .W128 (.movdqa (.mem m) (.avx x)))) sz)
    {a : BitVec 64} (ha : eaddr st sz m = a) (h16 : isAligned 16 a = true)
    (hdm : Mem.loadInt st.st.1.dmem a 16 = none) :
    isa.exec st = some (.access st.decls a 16 fun l => .store .plain false l (st.st.1.zmms.get x) fun _ =>
      .done (after st sz st.st.1)) := by
  cellV hc [ha, h16, hdm, w128_beq]

end Vec

/-! ## No-event instructions: register operations and branches

Each is `.done`: the thread's next state, no memory event (the source-stutter
case of `Lower.instrSemInf_done_stutter`). -/

section NoEvent

variable {st : State} {sz : Nat}

/-- **`mov r64, r64'`**: no event. -/
theorem exec_mov_rr {d s : Reg .W64} (hc : CellAt st (op64 (.mov (.reg d) (.reg s))) sz) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set d (st.st.1.regs.get s) })) := by
  cell hc []

/-- The value of an immediate at the cell, as 64 bits. -/
abbrev immVal (st : State) (sz : Nat) (c : ConstExpr) : BitVec 64 :=
  (@ConstExpr.interp (_root_.Executable.labels st.exe) c (rangeOf st sz)).toBitVec.truncate 64

/-- **`mov r64, imm`**: no event. -/
theorem exec_mov_ri {d : Reg .W64} {c : ConstExpr} (hc : CellAt st (op64 (.mov (.reg d) (.imm c))) sz) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set d (immVal st sz c) })) := by
  cell hc []

/-- **`lea r64, [m]`**: no event (no access); `r := eaddr m`. -/
theorem exec_lea {d : Reg .W64} {m : AddrExpr} (hc : CellAt st (op64 (.lea d m)) sz) :
    isa.exec st = some (.done (after st sz { st.st.1 with regs := st.st.1.regs.set d (eaddr st sz m) })) := by
  cell hc []

/-- **`add r64, r64'`**: no event; `d := d + s`, the flags those of the sum. -/
theorem exec_add_rr {d s : Reg .W64} (hc : CellAt st (op64 (.add (.reg d) (.reg s))) sz) :
    ∃ fl, isa.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.set d (st.st.1.regs.get s + st.st.1.regs.get d), status := fl })) :=
  ⟨_, by cell hc []⟩

/-- The flags `add` sets for the 64-bit sum of `a` (source) and `b`
(destination). -/
def addFlags (a b : BitVec 64) : StatusFlags :=
  .from_result (a + b) {
    cf := (a + b).unsigned != a.unsigned + b.unsigned,
    af := ((a + b).take 4).unsigned != (a.take 4).unsigned + (b.take 4).unsigned,
    of := (a + b).signed != a.signed + b.signed }

/-- `add`'s carry: the unsigned sum does not fit in 64 bits. -/
theorem addFlags_cf (a b : BitVec 64) : (addFlags a b).cf = decide (2 ^ 64 ≤ a.toNat + b.toNat) := by
  simp [addFlags, StatusFlags.from_result, BitVec.unsigned, BitVec.toNat_add]
  have ha := a.isLt
  have hb := b.isLt
  rw [Bool.eq_iff_iff]
  simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
  omega

/-- **`add r64, r64'`** with its flags (`exec_add_rr` leaves them
existential): no event; `d := s + d`, the flags `addFlags s d`. -/
theorem exec_add_flags {d s : Reg .W64} (hc : CellAt st (op64 (.add (.reg d) (.reg s))) sz) :
    isa.exec st = some (.done (after st sz
      { st.st.1 with
        regs := st.st.1.regs.set d (st.st.1.regs.get s + st.st.1.regs.get d)
        status := addFlags (st.st.1.regs.get s) (st.st.1.regs.get d) })) := by
  cell hc [addFlags]

/-- **`cmp r64, r64'`**: no event; only the flags change. -/
theorem exec_cmp_rr {a b : Reg .W64} (hc : CellAt st (op64 (.cmp (.reg a) (.reg b))) sz) :
    ∃ fl, isa.exec st = some (.done (after st sz { st.st.1 with status := fl })) :=
  ⟨_, by cell hc []⟩

omit st sz in
private theorem int64_add_sub (a b : Int64) : a + (b - a) = b := by
  rw [Int64.add_comm, Int64.sub_add_cancel]

/-- The address of a label of `st`'s executable. -/
abbrev labelAddr (st : State) (L : Label) : Int64 := (_root_.Executable.labels st.exe).label L

/-- **`jmp L`** (the parser's `.rel (L - after_current_instruction)`): no
event; jump to `L`. -/
theorem exec_jmp_label {L : Label}
    (hc : CellAt st (op64 (.jmp (.rel (.sub (.label L) .after_current_instruction)))) sz) :
    isa.exec st = some (.done (jumpTo st st.st.1 (labelAddr st L))) := by
  cell hc [int64_add_sub]

/-- **`jcc L`**: no event; jump iff the condition holds. -/
theorem exec_jcc {cc : CondCode} {L : Label} (hc : CellAt st (op64 (.jcc cc L)) sz) :
    isa.exec st = some (.done (jumpTo st st.st.1
      (if cc.interp st.st.1.status then labelAddr st L else st.st.2 + .ofNat sz))) := by
  by_cases h : cc.interp st.st.1.status = true <;> cell hc [h]

/-- **`jmp *r64`**: no event; jump to the address `r` holds. -/
theorem exec_jmp_reg {r : Reg .W64} (hc : CellAt st (op64 (.jmp (.reg r))) sz) :
    isa.exec st = some (.done (jumpTo st st.st.1 (Int64.ofBitVec (st.st.1.regs.get r)))) := by
  cell hc []

end NoEvent

/-! ## `call` and `ret`: the stack slot

`call` stores the return address at `rsp - 8` and `ret` loads it from `rsp`
(`X64/Semantics.lean`, `.call`/`.ret`), through the ordinary mapped-first
`store`/`load`. With the slot mapped in `dmem` (the stack in private memory,
as the draft calling convention proposes) the step is **no event**; otherwise it is one plain 8-byte
**shared** store (`call`) or load (`ret`). -/

section Calls

variable {st : State} {sz : Nat}

/-- The return address `call` pushes: the address behind the cell. -/
abbrev retAddr (st : State) (sz : Nat) : BitVec 64 := (st.st.2 + .ofNat sz).toBitVec

/-- The machine data after `call` pushed into a mapped slot. -/
abbrev callPost (st : State) (sz : Nat) : MachineData :=
  { st.st.1 with regs := st.st.1.regs.set64 .rsp (rspOf st.st.1 - 8#64)
                 dmem := Mem.storeInt st.st.1.dmem (rspOf st.st.1 - 8#64) 8 (retAddr st sz).toInt }

/-- **`call L`, stack slot `[rsp-8, rsp)` mapped in `dmem`**: no event;
`rsp -= 8`, the return address written to the slot, jump to `L`. -/
theorem exec_call_label {L : Label}
    (hc : CellAt st (op64 (.call (.rel (.sub (.label L) .after_current_instruction)))) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (rspOf st.st.1 - 8#64) 8 = some j) :
    isa.exec st = some (.done (jumpTo st (callPost st sz) (labelAddr st L))) := by
  cell hc [hdm, int64_add_sub, callPost, retAddr]

/-- **`call *r64`, slot mapped**: no event; jump to the address `r` held. -/
theorem exec_call_reg {r : Reg .W64} (hc : CellAt st (op64 (.call (.reg r))) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (rspOf st.st.1 - 8#64) 8 = some j) :
    isa.exec st = some (.done (jumpTo st (callPost st sz) (Int64.ofBitVec (st.st.1.regs.get r)))) := by
  cell hc [hdm, callPost, retAddr]

/-- **`call L`, slot not mapped**: a **shared event**, one plain 8-byte store
of the return address at `rsp - 8`. -/
theorem exec_call_label_shared {L : Label}
    (hc : CellAt st (op64 (.call (.rel (.sub (.label L) .after_current_instruction)))) sz)
    (hdm : Mem.loadInt st.st.1.dmem (rspOf st.st.1 - 8#64) 8 = none) :
    isa.exec st = some (.access st.decls (rspOf st.st.1 - 8#64) 8 fun l =>
      .store .plain false l ((retAddr st sz).setWidth 128) fun _ =>
      .done (jumpTo st { st.st.1 with regs := st.st.1.regs.set64 .rsp (rspOf st.st.1 - 8#64) }
        (labelAddr st L))) := by
  cell hc [hdm, int64_add_sub]

/-- **`call *r64`, slot not mapped**: one plain 8-byte shared store. -/
theorem exec_call_reg_shared {r : Reg .W64} (hc : CellAt st (op64 (.call (.reg r))) sz)
    (hdm : Mem.loadInt st.st.1.dmem (rspOf st.st.1 - 8#64) 8 = none) :
    isa.exec st = some (.access st.decls (rspOf st.st.1 - 8#64) 8 fun l =>
      .store .plain false l ((retAddr st sz).setWidth 128) fun _ =>
      .done (jumpTo st { st.st.1 with regs := st.st.1.regs.set64 .rsp (rspOf st.st.1 - 8#64) }
        (Int64.ofBitVec (st.st.1.regs.get r)))) := by
  cell hc [hdm]

/-- **`ret`, stack slot `[rsp, rsp+8)` mapped in `dmem`**: no event; `rsp
+= 8`, jump to the address the slot held. -/
theorem exec_ret (hc : CellAt st (op64 .ret) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (rspOf st.st.1) 8 = some j) :
    isa.exec st = some (.done (jumpTo st { st.st.1 with regs := st.st.1.regs.set64 .rsp (rspOf st.st.1 + 8#64) }
      (Int64.ofBitVec (BitVec.ofInt 64 j)))) := by
  cell hc [hdm]

/-- **`ret`, slot not mapped**: a **shared event**, one plain 8-byte load at
`rsp`; jump to the value read. -/
theorem exec_ret_shared (hc : CellAt st (op64 .ret) sz)
    (hdm : Mem.loadInt st.st.1.dmem (rspOf st.st.1) 8 = none) :
    isa.exec st = some (.access st.decls (rspOf st.st.1) 8 fun l => .load .plain false l fun v =>
      .done (jumpTo st { st.st.1 with regs := st.st.1.regs.set64 .rsp (rspOf st.st.1 + 8#64) }
        (Int64.ofBitVec (v.setWidth 64)))) := by
  cell hc [hdm]

end Calls

end Kraken.Promising.Lower.X64

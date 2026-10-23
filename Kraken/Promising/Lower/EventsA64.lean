/-
**Which memory event each lowering-table instruction is,
on AArch64 `isaLSE2`.**

The per-instruction half of `Lower/Events.lean`: for each lowering-table
row, the `EvTree` that `isaLSE2.exec` gives at a cell holding the row's
instruction. Generic over registers, immediates, pc, cell size `sz`
(`ValidLayout.instr_size` makes it 4), executable layout and declarations;
the only hypothesis on the cell is `CellAt st d sz`.

## Shapes

- **Memory rows**, address `a` not in the thread-private `dmem` (`hdm`):
  `exec_<row>` gives `.access st.decls a 8 (fun l => <event at l>)`;
  `exec_<row>_agrees` adds `st.decls.AgreesAt a 8` and resolves it to the
  single event at `⟨a, 8⟩`; `exec_<row>_mapped` (address in `dmem`) is a
  no-event step. `exec_ldr_sp`/`exec_str_sp`: `ldr`/`str` at `[sp, #i]`
  (`sp` 16-aligned), mapped, no event.
  - loads: `exec_ldr` (plain), `exec_ldar` (kind `k`, exclusivity `xcl`:
    `ldar` is `.acq`, `ldapr` is `.acqPc`), one `.load`;
  - stores: `exec_str` (plain), `exec_stlr` (`.rel`), one non-exclusive
    `.store`;
  - RMWs: `exec_cas` (operation `casOp`), `exec_swp`, `exec_ldop`
    (`ldadd` etc.), one `.rmw`; the mapped forms are existential in the
    new private state.
- **Fences**: `exec_dmb` (any `FenceKind`: `dmb ish`, `dmb ishst`), one
  `.fence`.
- **LSE2 pairs**: `exec_ldp_lse2`/`exec_stp_lse2`: one 16-byte event when the
  address is 16-aligned and `pairIsOneLoc st.decls a .W64` (the declarations
  have a 16-byte location at `a`); `exec_ldp_two`: two 8-byte loads
  otherwise. `exec_casp`: off a 16-byte location (`caspIsOneLoc` false),
  `caspTree`, two RMWs in one tree (herd's `casp` is not single-copy atomic
  as a pair), hence in one instruction step. `exec_casp16`: on a 16-aligned
  declared 16-byte location, one 16-byte RMW (`toEvCASP`).
- **No-event rows** (`.done`): `exec_add_s`, `exec_add_e`, `exec_orr_s`
  (`mov`), `exec_movz`, `exec_adds_s`, `exec_subs_s`, `exec_subs_e` (`cmp`), `exec_b`,
  `exec_bcond`, `exec_cbz`, `exec_cbnz`, `exec_bl`, `exec_blr`, `exec_br`,
  `exec_ret`.

`Lower/EventsA64Inf.lean` composes these with the `InstrSemInf` shape lemmas;
`Lower/CallsA64.lean` covers `bl`/`ret`/`blr`.
-/
import Kraken.Promising.Lower.Events
import Kraken.Promising.SeqLinkAArch64Step
import Kraken.Promising.SLR.EnvG.NoFaultDCommon

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **The cell at `st`'s pc is `d`, of `sz` bytes**: `st`'s executable is
validly laid out, `codeAt` finds `d` at the pc (behind any labels), and the
pc is short of the end address. Any executable, any layout, any
declarations. -/
structure CellAt (st : State) (d : Directive) (sz : Nat) : Prop where
  valid : Kraken.Executable.ValidLayout st.exe
  ne : (st.st.2 == st.endPc) = false
  code : ∃ rest, Kraken.Executable.codeAt st.exe st.st.2 = (d, sz) :: rest

/-- The continuation `Executable.step` gives a cell: fall through to the next
cell (`pc + sz`), or jump. -/
abbrev nextS (st : State) (sz : Nat) (s' : MachineData) : Effects := .done (s', st.st.2 + .ofNat sz)

abbrev jmpS (pc : Int64) (s' : MachineData) : Effects := .done (s', pc)

/-- **`isaLSE2`'s tree at a cell, any declarations** (`execLSE2_of_codeAt`
without `decls = declsOf L`): the translation of the cell's FEAT_LSE2
reading; for a cell other than a `CASP` of `X` registers (`execLSE2_of_cellAt_casp`
for those). -/
theorem execLSE2_of_cellAt {st : State} {d : Directive} {sz : Nat} (h : CellAt st d sz)
    (hx : d.isCaspX = false) :
    execLSE2 st = some ((toEv st.decls (@Directive.interpLSE2 (_root_.Executable.labels st.exe) d
      st.st.1 (.mk st.st.2 (st.st.2 + .ofNat sz)) (nextS st sz) jmpS)).map fun s => { st with st := s }) := by
  obtain ⟨hv, hne, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc', ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at hne hcode hat hv ⊢
  have hdir : ({ exe, endPc := endPc', st := (s, pc), showPc, decls } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hcell : ({ exe, endPc := endPc', st := (s, pc), showPc, decls } : State).cell = some (d, sz) := by
    unfold State.cell
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [execLSE2, hdir, hne, Option.isNone_some, Bool.or_false, Bool.false_eq_true, ite_false]
  letI := Executable.labels exe
  cases hl : lse2Effects { exe, endPc := endPc', st := (s, pc), showPc, decls } with
  | some ef =>
    simp only [lse2Effects, hcell] at hl
    simp only [Directive.interpLSE2, hl, Option.getD_some]
  | none =>
    simp only [lse2Effects, hcell] at hl
    rw [Directive.interpLSE2_of_none _ hl]
    simp only [State.isCaspX, hdir, hx, exec, hne, Option.isNone_some, Bool.or_false, Bool.false_eq_true,
      ite_false]
    congr 2
    unfold Executable.step
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]

/-- **`isaLSE2`'s tree at a `CASP` cell of `X` registers, any declarations**:
the translation of `Directive.interp` by `toEvCASP`. -/
theorem execLSE2_of_cellAt_casp {st : State} {d : Directive} {sz : Nat} (h : CellAt st d sz)
    (hx : d.isCaspX = true) :
    execLSE2 st = some ((toEvCASP st.decls (@Directive.interp (_root_.Executable.labels st.exe) d
      st.st.1 (.mk st.st.2 (st.st.2 + .ofNat sz)) (nextS st sz) jmpS)).map fun s => { st with st := s }) := by
  obtain ⟨hv, hne, rest, hcode⟩ := h
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc', ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at hne hcode hat hv ⊢
  have hdir : ({ exe, endPc := endPc', st := (s, pc), showPc, decls } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  have hcell : ({ exe, endPc := endPc', st := (s, pc), showPc, decls } : State).cell = some (d, sz) := by
    unfold State.cell
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) =
        Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  letI := Executable.labels exe
  have hl : lse2Effects { exe, endPc := endPc', st := (s, pc), showPc, decls } = none := by
    simp only [lse2Effects, hcell, Directive.interpLSE2?_none_of_isCaspX hx]
  simp only [execLSE2, hdir, hne, hl, State.isCaspX, hx, Option.isNone_some, Bool.or_false,
    Bool.false_eq_true, ite_false, ite_true]
  congr 2
  unfold Executable.step
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]

/-- At a cell without a FEAT_LSE2 reading (every cell but a 64-bit
`LDP`/`STP`), `isaLSE2`'s tree is the translation of `Directive.interp`. -/
theorem execLSE2_of_cellAt_free {st : State} {d : Directive} {sz : Nat} (h : CellAt st d sz)
    (hf : d.LSE2Free) :
    execLSE2 st = some ((toEv st.decls (@Directive.interp (_root_.Executable.labels st.exe) d
      st.st.1 (.mk st.st.2 (st.st.2 + .ofNat sz)) (nextS st sz) jmpS)).map fun s => { st with st := s }) := by
  rw [execLSE2_of_cellAt h (by revert hf; unfold Directive.isCaspX; split <;> simp [Directive.LSE2Free])]
  letI := Executable.labels st.exe
  rw [Directive.interpLSE2_of_none _ (Directive.interpLSE2?_none_of_free hf _ _ _)]

theorem map_access {σ τ : Type} (f : σ → τ) (ds : Decls) (a : BitVec 64) (n : Nat) (k : Loc → EvTree σ) :
    (EvTree.access ds a n k).map f = EvTree.access ds a n fun l => (k l).map f := by
  unfold EvTree.access; split <;> rfl

/-- The state after a cell: machine data `s'`, pc `pc + sz`. -/
abbrev after (st : State) (sz : Nat) (s' : MachineData) : State := { st with st := (s', st.st.2 + .ofNat sz) }

/-- An access at an agreeing address is its own footprint. -/
theorem access_agrees {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} (h : ds.AgreesAt a n)
    (k : Loc → EvTree σ) : EvTree.access ds a n k = k ⟨a, n⟩ := by
  rw [EvTree.access_of_agreesAt h, EvTree.access_empty]

/-- Read the cell through `execLSE2_of_cellAt_free` and unfold it. -/
local macro "cell" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free $hc trivial]
  simp [Directive.interp, Instr.interp, Operation.interp, AddrOrLit.interpLoad, AddrExpr.interpLoad,
    AddrExpr.interpStore, AddrExpr.checkSPAlignment, AddrExpr.eval, MachineData.load, MachineData.store,
    MachineData.loadK, MachineData.storeK, MachineData.rmwK, MachineData.rmwPairK, RegOrSp.interpBase,
    toEv, EvTree.map, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

section Loads

variable {st : State} {sz : Nat}

/-- **`ldr Xt, [Xn, #i]`** (no writeback), address unmapped in `dmem`: one
plain 8-byte load. -/
theorem exec_ldr {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l => .load .plain false l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  cell hc [ha, hdm]

/-- `ldr` at an agreeing address: the load of `⟨a, 8⟩`. -/
theorem exec_ldr_agrees {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) (hag : st.decls.AgreesAt a 8) :
    isaLSE2.exec st = some (.load .plain false ⟨a, 8⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  rw [exec_ldr hc ha hdm, access_agrees hag]

/-- `ldr` at an address mapped in `dmem`: no event. -/
theorem exec_ldr_mapped {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (BitVec.ofInt 64 j) })) := by
  cell hc [ha, hdm]

/-- **`ldr Xt, [sp, #i]`**, `sp` 16-aligned (the alignment check passes), the
address mapped in `dmem`: no event. -/
theorem exec_ldr_sp {dst : RegOrZr .W64} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDR dst (.addr ⟨.SP, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    (hal : st.st.1.regs.SP.toBitVec % 16#64 = 0#64)
    {a : BitVec 64} (ha : BitVec.ofInt 64 (st.st.1.regs.SP.toBitVec.toInt + i.toInt) = a)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (BitVec.ofInt 64 j) })) := by
  cell hc [hal, ha, hdm]

/-- **`ldar Xt, [Xn]` / `ldapr Xt, [Xn]`** (`k = .acq` / `.acqPc`; with
`xcl` also `ldxr`/`ldaxr`), address unmapped: one 8-byte load of kind `k`. -/
theorem exec_ldar {dst : RegOrZr .W64} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt st (.instr ⟨.W64, .LDAR k xcl .W64 dst (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none) :
    isaLSE2.exec st = some (.access st.decls (st.st.1.regs.getXReg n).toBitVec 8 fun l => .load k xcl l fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  cell hc [hdm]

theorem exec_ldar_agrees {dst : RegOrZr .W64} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt st (.instr ⟨.W64, .LDAR k xcl .W64 dst (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none)
    (hag : st.decls.AgreesAt (st.st.1.regs.getXReg n).toBitVec 8) :
    isaLSE2.exec st = some (.load k xcl ⟨(st.st.1.regs.getXReg n).toBitVec, 8⟩ fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (v.setWidth 64) })) := by
  rw [exec_ldar hc hdm, access_agrees hag]

theorem exec_ldar_mapped {dst : RegOrZr .W64} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt st (.instr ⟨.W64, .LDAR k xcl .W64 dst (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst (BitVec.ofInt 64 j) })) := by
  cell hc [hdm]

end Loads

section Stores

variable {st : State} {sz : Nat}

/-- **`str Xt, [Xn, #i]`** (no writeback), address unmapped: one plain
8-byte store. -/
theorem exec_str {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l => .store .plain false l
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cell hc [ha, hdm]

theorem exec_str_agrees {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt st.st.1.dmem a 8 = none) (hag : st.decls.AgreesAt a 8) :
    isaLSE2.exec st = some (.store .plain false ⟨a, 8⟩
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_str hc ha hdm, access_agrees hag]

/-- `str` at a mapped address: no event (`dmem` updated). -/
theorem exec_str_mapped {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with dmem := Mem.storeInt st.st.1.dmem a 8 (st.st.1.regs.getRegOrZr src).toInt })) := by
  cell hc [ha, hdm]

/-- **`str Xt, [sp, #i]`**, `sp` 16-aligned (the alignment check passes), the
address mapped in `dmem`: no event, `dmem` updated. -/
theorem exec_str_sp {src : RegOrZr .W64} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STR src ⟨.SP, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    (hal : st.st.1.regs.SP.toBitVec % 16#64 = 0#64)
    {a : BitVec 64} (ha : BitVec.ofInt 64 (st.st.1.regs.SP.toBitVec.toInt + i.toInt) = a)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem a 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with dmem := Mem.storeInt st.st.1.dmem a 8 (st.st.1.regs.getRegOrZr src).toInt })) := by
  cell hc [hal, ha, hdm]

/-- **`stlr Xt, [Xn]`**, address unmapped: one 8-byte release store. -/
theorem exec_stlr {src : RegOrZr .W64} {n : XReg}
    (hc : CellAt st (.instr ⟨.W64, .STLR .W64 src (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none) :
    isaLSE2.exec st = some (.access st.decls (st.st.1.regs.getXReg n).toBitVec 8 fun l => .store .rel false l
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  cell hc [hdm]

theorem exec_stlr_agrees {src : RegOrZr .W64} {n : XReg}
    (hc : CellAt st (.instr ⟨.W64, .STLR .W64 src (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none)
    (hag : st.decls.AgreesAt (st.st.1.regs.getXReg n).toBitVec 8) :
    isaLSE2.exec st = some (.store .rel false ⟨(st.st.1.regs.getXReg n).toBitVec, 8⟩
      ((st.st.1.regs.getRegOrZr src).setWidth 128) fun _ => .done (after st sz st.st.1)) := by
  rw [exec_stlr hc hdm, access_agrees hag]

theorem exec_stlr_mapped {src : RegOrZr .W64} {n : XReg}
    (hc : CellAt st (.instr ⟨.W64, .STLR .W64 src (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = some j) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with dmem := st.st.1.dmem.storeInt (st.st.1.regs.getXReg n).toBitVec 8
                                (st.st.1.regs.getRegOrZr src).toInt })) := by
  cell hc [hdm]

end Stores

section Rmw

variable {st : State} {sz : Nat}

/-- The operation of `cas`: write `new` iff the old value is `cmp`. -/
def casOp (cmp new : BitVec 64) (old : Val) : Option Val :=
  if old.setWidth 64 = cmp then some (new.setWidth 128) else none

/-- **`cas Xs, Xt, [Xn]`** (`k`: `cas`/`casa`/`casl`/`casal` =
`.plain`/`.acq`/`.rel`/`.acqRel`), address unmapped: one RMW, writing `Xt`
iff the old value is `Xs`; `Xs` gets the old value. `noRet` iff `Xs` is the
zero register. -/
theorem exec_cas {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .CAS k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none) :
    isaLSE2.exec st = some (.access st.decls (st.st.1.regs.getXReg n).toBitVec 8 fun l =>
      .rmw k rs.isZr l (casOp (st.st.1.regs.getRegOrZr rs) (st.st.1.regs.getRegOrZr rt)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rs (v.setWidth 64) })) := by
  cell hc [hdm, casOp]

theorem exec_cas_agrees {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .CAS k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none)
    (hag : st.decls.AgreesAt (st.st.1.regs.getXReg n).toBitVec 8) :
    isaLSE2.exec st = some (.rmw k rs.isZr ⟨(st.st.1.regs.getXReg n).toBitVec, 8⟩
      (casOp (st.st.1.regs.getRegOrZr rs) (st.st.1.regs.getRegOrZr rt)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rs (v.setWidth 64) })) := by
  rw [exec_cas hc hdm, access_agrees hag]

/-- `cas` at a mapped address: no event. -/
theorem exec_cas_mapped {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .CAS k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = some j) :
    ∃ s', isaLSE2.exec st = some (.done (after st sz s')) := by
  by_cases he : (BitVec.ofInt 64 j) = st.st.1.regs.getRegOrZr rs <;>
    exact ⟨_, by cell hc [hdm, he]⟩

/-- **`swp Xs, Xt, [Xn]`** (`k`: `swp`/`swpa`/`swpl`/`swpal`), address
unmapped: one RMW writing `Xs`; `Xt` gets the old value. -/
theorem exec_swp {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .SWP k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none) :
    isaLSE2.exec st = some (.access st.decls (st.st.1.regs.getXReg n).toBitVec 8 fun l =>
      .rmw k rt.isZr l (fun _ => some ((st.st.1.regs.getRegOrZr rs).setWidth 128)) fun v =>
      .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rt (v.setWidth 64) })) := by
  cell hc [hdm]

theorem exec_swp_mapped {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .SWP k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = some j) :
    ∃ s', isaLSE2.exec st = some (.done (after st sz s')) :=
  ⟨_, by cell hc [hdm]⟩

/-- **`ldadd Xs, Xt, [Xn]` and the other `ld<op>`** (`k`: none/`a`/`l`/`al`),
address unmapped: one RMW writing `op old Xs`; `Xt` gets the old value. -/
theorem exec_ldop {rs rt : RegOrZr .W64} {n : XReg} {op : AtomicOp} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .LDOP op k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none) :
    isaLSE2.exec st = some (.access st.decls (st.st.1.regs.getXReg n).toBitVec 8 fun l =>
      .rmw k rt.isZr l (fun old => some ((op.apply (old.setWidth 64) (st.st.1.regs.getRegOrZr rs)).setWidth 128))
        fun v => .done (after st sz { st.st.1 with regs := st.st.1.regs.setRegOrZr rt (v.setWidth 64) })) := by
  cell hc [hdm]

theorem exec_ldop_mapped {rs rt : RegOrZr .W64} {n : XReg} {op : AtomicOp} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .LDOP op k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    {j : Int} (hdm : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = some j) :
    ∃ s', isaLSE2.exec st = some (.done (after st sz s')) :=
  ⟨_, by cell hc [hdm]⟩

end Rmw

section Fence

variable {st : State} {sz : Nat}

/-- **`dmb <opt>`** (`dmb ish` is `k = .sy`, `dmb ishst` is `k = .st`,
`dmb ishld` is `k = .ld`): one fence. -/
theorem exec_dmb {k : FenceKind} (hc : CellAt st (.instr ⟨.W64, .DMB k⟩) sz) :
    isaLSE2.exec st = some (.fence k fun _ => .done (after st sz st.st.1)) := by
  cell hc []

end Fence

/-! ## FEAT_LSE2 pairs and `CASP` -/

/-- Read an `LDP`/`STP` cell through its FEAT_LSE2 reading. -/
local macro "cellP" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt $hc rfl]
  simp [Directive.interpLSE2, Directive.interpLSE2?, Directive.interp, Instr.interp, Operation.interp,
    MachineData.load, MachineData.store, AddrExpr.checkSPAlignment, AddrExpr.eval,
    MachineData.loadPairK, MachineData.storePairK, toEv, EvTree.map, MachineData.setRegOrZr,
    Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, MemWidth.bytesv, $ts,*]
  try (simp only [map_access, EvTree.map])
  try rfl))

section Pair

variable {st : State} {sz : Nat}

/-- **16-byte-aligned `ldp Xt1, Xt2, [Xn, #i]` on a declared 16-byte
location** (`pairIsOneLoc`), both halves unmapped: under FEAT_LSE2 **one**
plain 16-byte load; `Xt1` gets the low half. -/
theorem exec_ldp_lse2 {dst1 dst2 : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDP dst1 dst2 ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (h16 : a % 16#64 = 0#64) (hone : pairIsOneLoc st.decls a .W64 = true)
    (hdm1 : Mem.loadInt st.st.1.dmem a 8 = none) (hdm2 : Mem.loadInt st.st.1.dmem (a + 8#64) 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 16 fun l => .load .plain false l fun v =>
      .done (after st sz
        { st.st.1 with regs := (st.st.1.regs.setRegOrZr dst1 (v.setWidth 64)).setRegOrZr dst2
                                 ((v >>> 64).setWidth 64) })) := by
  cellP hc [ha, h16, hone, hdm1, hdm2]

/-- `ldp` as above, but on an address that is not a declared 16-byte
location: **two** plain 8-byte loads, lower address first (as herd). -/
theorem exec_ldp_two {dst1 dst2 : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .LDP dst1 dst2 ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hone : pairIsOneLoc st.decls a .W64 = false)
    (hdm1 : Mem.loadInt st.st.1.dmem a 8 = none) (hdm2 : Mem.loadInt st.st.1.dmem (a + 8#64) 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 8 fun l1 => .load .plain false l1 fun v1 =>
      .access st.decls (a + 8#64) 8 fun l2 => .load .plain false l2 fun v2 =>
      .done (after st sz
        { st.st.1 with regs := (st.st.1.regs.setRegOrZr dst1 (v1.setWidth 64)).setRegOrZr dst2
                                 (v2.setWidth 64) })) := by
  by_cases h16 : a % 16#64 = 0#64
  · cellP hc [ha, h16, hone, hdm1, hdm2]
  · cellP hc [ha, h16, hone, hdm1, hdm2]

/-- **16-byte-aligned `stp Xt1, Xt2, [Xn, #i]` on a declared 16-byte
location**, both halves unmapped: under FEAT_LSE2 **one** plain 16-byte
store of `Xt2 : Xt1`. -/
theorem exec_stp_lse2 {src1 src2 : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt st (.instr ⟨.W64, .STP src1 src2 ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 ((st.st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (h16 : a % 16#64 = 0#64) (hone : pairIsOneLoc st.decls a .W64 = true)
    (hdm1 : Mem.loadInt st.st.1.dmem a 8 = none) (hdm2 : Mem.loadInt st.st.1.dmem (a + 8#64) 8 = none) :
    isaLSE2.exec st = some (.access st.decls a 16 fun l => .store .plain false l
      (((st.st.1.regs.getRegOrZr src2).setWidth 128 <<< 64) ||| (st.st.1.regs.getRegOrZr src1).setWidth 128)
      fun _ => .done (after st sz st.st.1)) := by
  cellP hc [ha, h16, hone, hdm1, hdm2]

theorem map_caspTree {σ τ : Type} (f : σ → τ) (ds : Decls) (k : RmwKind) (addr : BitVec 64) {w : MemWidth}
    (cmp1 cmp2 new1 new2 : w.type) (ret : w.type → w.type → EvTree σ) :
    (caspTree ds k addr cmp1 cmp2 new1 new2 ret).map f =
      caspTree ds k addr cmp1 cmp2 new1 new2 fun o1 o2 => (ret o1 o2).map f := by
  unfold caspTree
  simp only [EvTree.map]
  congr 1; funext succ; congr 1; funext rev
  split <;> simp only [map_access, EvTree.map, apply_ite (EvTree.map f)] <;>
    (congr 1; funext l; congr 1; funext o1; congr 1; funext l'; congr 1; funext o2; split
     · rfl
     · congr 1; funext i; exact i.elim0)

/-- **`casp Xs1, Xs2, Xt1, Xt2, [Xn]`** (any kind), both halves unmapped:
`caspTree`, i.e. **two** `rmw` events of kind `k`, one per half, in either
order, inside a `choose` of the outcome (success/failure) and the order; both
in the one instruction step. -/
theorem exec_casp {rs1 rs2 rt1 rt2 : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .CASP k rs1 rs2 rt1 rt2 (.low (.reg n) .W64)⟩) sz)
    (hdm1 : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none)
    (hdm2 : Mem.loadInt st.st.1.dmem ((st.st.1.regs.getXReg n).toBitVec + 8#64) 8 = none)
    (hone : caspIsOneLoc st.decls (st.st.1.regs.getXReg n).toBitVec = false) :
    isaLSE2.exec st = some (caspTree st.decls k (st.st.1.regs.getXReg n).toBitVec (w := .W64)
      (st.st.1.regs.getRegOrZr rs1) (st.st.1.regs.getRegOrZr rs2)
      (st.st.1.regs.getRegOrZr rt1) (st.st.1.regs.getRegOrZr rt2) fun o1 o2 =>
      .done (after st sz { st.st.1 with regs := (st.st.1.regs.setRegOrZr rs1 o1).setRegOrZr rs2 o2 })) := by
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_casp hc rfl]
  simp [Directive.interp, Instr.interp, Operation.interp, RegOrSp.interpBase, MachineData.rmwPairK, toEv,
    toEvCASP, MachineData.setRegOrZr, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, MemWidth.bytesv,
    hdm1, hdm2, hone, map_caspTree, EvTree.map]

/-- **`casp Xs1, Xs2, Xt1, Xt2, [Xn]`** (any kind `k`) on a 16-aligned declared
16-byte location, both halves unmapped: **one** 16-byte `rmw` of kind `k`
(`toEvCASP`), single-copy atomic as on hardware (Arm ARM B2.2.1). It writes
`Xt2 : Xt1` iff the low half is `Xs1` and the high half `Xs2`, and nothing
otherwise; `Xs1`/`Xs2` get the old halves. -/
theorem exec_casp16 {rs1 rs2 rt1 rt2 : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt st (.instr ⟨.W64, .CASP k rs1 rs2 rt1 rt2 (.low (.reg n) .W64)⟩) sz)
    (hdm1 : Mem.loadInt st.st.1.dmem (st.st.1.regs.getXReg n).toBitVec 8 = none)
    (hdm2 : Mem.loadInt st.st.1.dmem ((st.st.1.regs.getXReg n).toBitVec + 8#64) 8 = none)
    (h16 : (st.st.1.regs.getXReg n).toBitVec % 16#64 = 0#64)
    (hone : caspIsOneLoc st.decls (st.st.1.regs.getXReg n).toBitVec = true) :
    isaLSE2.exec st = some (.access st.decls (st.st.1.regs.getXReg n).toBitVec 16 fun l =>
      .rmw k false l (fun old =>
          if old.setWidth 64 == st.st.1.regs.getRegOrZr rs1 && (old >>> 64).setWidth 64 == st.st.1.regs.getRegOrZr rs2
          then some ((st.st.1.regs.getRegOrZr rt2).setWidth 128 <<< 64 ||| (st.st.1.regs.getRegOrZr rt1).setWidth 128)
          else none)
        fun old => .done (after st sz { st.st.1 with
          regs := (st.st.1.regs.setRegOrZr rs1 (old.setWidth 64)).setRegOrZr rs2 ((old >>> 64).setWidth 64) })) := by
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_casp hc rfl]
  simp [Directive.interp, Instr.interp, Operation.interp, RegOrSp.interpBase, MachineData.rmwPairK, toEv,
    toEvCASP, MachineData.setRegOrZr, Reg64s.getRegOrSp, Reg64s.getRegOrSp64, RegOrSp.base, MemWidth.bytesv,
    hdm1, hdm2, h16, hone, map_access, EvTree.map]
  rfl

end Pair

/-! ## No-event instructions: register operations and branches

Each is `.done`: the thread's next state, no memory event (the source-stutter
case of `Lower.instrSemInf_done_stutter`). -/

/-- The state with machine data `s'` at pc `pc`. -/
abbrev jumpTo (st : State) (s' : MachineData) (pc : Int64) : State := { st with st := (s', pc) }

/-- The cell's address range, for operand interpretation. -/
abbrev rangeOf (st : State) (sz : Nat) : Std.Rco Int64 := .mk st.st.2 (st.st.2 + .ofNat sz)

/-- Read a register or branch cell (no memory unfolding). -/
local macro "cellR" hc:ident "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  show execLSE2 _ = _
  rw [execLSE2_of_cellAt_free $hc trivial]
  simp only [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, MachineData.setRegOrZr,
    MachineData.setRegOrSp, $ts,*]
  try rfl))

section NoEvent

variable {st : State} {sz : Nat}

/-- **`add Xd, Xn, <shifted Xm>`**: no event. -/
theorem exec_add_s {dst src1 : RegOrZr .W64} {src2 : ShiftRegExpr .W64}
    (hc : CellAt st (.instr ⟨.W64, .ADD_s dst src1 src2⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst
                               (st.st.1.regs.getRegOrZr src1 + src2.interp st.st.1.regs (rangeOf st sz)) })) := by
  cellR hc []

/-- **`add Xd|SP, Xn|SP, #imm` / `<extended Xm>`** (also `mov` to or from
`SP`): no event. -/
theorem exec_add_e {dst src1 : RegOrSp .W64} {src2 : ExtOrImmReg}
    (hc : CellAt st (.instr ⟨.W64, .ADD_e dst src1 src2⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrSp dst (st.st.1.regs.getRegOrSp src1 +
                               @ExtOrImmReg.interp (_root_.Executable.labels st.exe) .W64 src2 st.st.1.regs
                                 (rangeOf st sz)) })) := by
  cellR hc []

/-- **`orr Xd, Xn, <shifted Xm>`** (`mov Xd, Xm` is `orr Xd, xzr, Xm`): no
event. -/
theorem exec_orr_s {dst src1 : RegOrZr .W64} {src2 : ShiftRegExpr .W64}
    (hc : CellAt st (.instr ⟨.W64, .ORR_s dst src1 src2⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst
                               (st.st.1.regs.getRegOrZr src1 ||| src2.interp st.st.1.regs (rangeOf st sz)) })) := by
  cellR hc []

/-- **`movz Xd, #imm, lsl #s`** (`mov Xd, #imm`): no event. -/
theorem exec_movz {dst : RegOrZr .W64} {imm : ConstExpr} {shift : MovShift .W64}
    (hc : CellAt st (.instr ⟨.W64, .MOVZ dst imm shift⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with regs := st.st.1.regs.setRegOrZr dst
                               (((BitVec.ofInt 64 (@ConstExpr.interp (_root_.Executable.labels st.exe) imm
                                   (rangeOf st sz)).toInt) &&& 0xFFFF#64) <<< shift.toNat) })) := by
  cellR hc []

/-- **`adds Xd, Xn, <shifted Xm>`**: no event; the sum, and its flags. -/
theorem exec_adds_s {dst src1 : RegOrZr .W64} {src2 : ShiftRegExpr .W64}
    (hc : CellAt st (.instr ⟨.W64, .ADDS_s dst src1 src2⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with
        status := StatusFlags.adds (st.st.1.regs.getRegOrZr src1 + src2.interp st.st.1.regs (rangeOf st sz))
          (st.st.1.regs.getRegOrZr src1) (src2.interp st.st.1.regs (rangeOf st sz))
        regs := st.st.1.regs.setRegOrZr dst
          (st.st.1.regs.getRegOrZr src1 + src2.interp st.st.1.regs (rangeOf st sz)) })) := by
  cellR hc []

/-- **`subs Xd, Xn, <shifted Xm>`** (`cmp Xn, Xm` is `subs xzr, Xn, Xm`): no
event; sets the flags. -/
theorem exec_subs_s {dst src1 : RegOrZr .W64} {src2 : ShiftRegExpr .W64}
    (hc : CellAt st (.instr ⟨.W64, .SUBS_s dst src1 src2⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with
        status := StatusFlags.subs (st.st.1.regs.getRegOrZr src1 - src2.interp st.st.1.regs (rangeOf st sz))
          (st.st.1.regs.getRegOrZr src1) (src2.interp st.st.1.regs (rangeOf st sz))
        regs := st.st.1.regs.setRegOrZr dst
          (st.st.1.regs.getRegOrZr src1 - src2.interp st.st.1.regs (rangeOf st sz)) })) := by
  cellR hc []

/-- **`subs Xd, Xn|SP, #imm` / `<extended Xm>`** (`cmp Xn, #imm`): no event;
sets the flags. -/
theorem exec_subs_e {dst : RegOrZr .W64} {src1 : RegOrSp .W64} {src2 : ExtOrImmReg}
    (hc : CellAt st (.instr ⟨.W64, .SUBS_e dst src1 src2⟩) sz) :
    isaLSE2.exec st = some (.done (after st sz
      { st.st.1 with
        status := StatusFlags.subs (st.st.1.regs.getRegOrSp src1 -
            @ExtOrImmReg.interp (_root_.Executable.labels st.exe) .W64 src2 st.st.1.regs (rangeOf st sz))
          (st.st.1.regs.getRegOrSp src1)
          (@ExtOrImmReg.interp (_root_.Executable.labels st.exe) .W64 src2 st.st.1.regs (rangeOf st sz))
        regs := st.st.1.regs.setRegOrZr dst (st.st.1.regs.getRegOrSp src1 -
            @ExtOrImmReg.interp (_root_.Executable.labels st.exe) .W64 src2 st.st.1.regs (rangeOf st sz)) })) := by
  cellR hc []

/-- The target of a direct branch at the cell (a label's address, or
`pc + imm`). -/
abbrev branchTarget (st : State) (sz : Nat) (target : ConstExpr) : Int64 :=
  @ConstExpr.evalBranchTarget (_root_.Executable.labels st.exe) target (rangeOf st sz)

/-- **`b target`**: no event; jump. -/
theorem exec_b {target : ConstExpr} (hc : CellAt st (.instr ⟨.W64, .B target⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1 (branchTarget st sz target))) := by
  cellR hc []

/-- **`b.cond target`**: no event; jump iff the condition holds. -/
theorem exec_bcond {cond : CondCode} {target : ConstExpr} (hc : CellAt st (.instr ⟨.W64, .B_cond cond target⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1
      (if cond.interp st.st.1.status then branchTarget st sz target else st.st.2 + .ofNat sz))) := by
  by_cases h : cond.interp st.st.1.status = true <;> cellR hc [h]

/-- **`cbz Xt, target`**: no event; jump iff `Xt = 0`. -/
theorem exec_cbz {reg : RegOrZr .W64} {target : ConstExpr} (hc : CellAt st (.instr ⟨.W64, .CBZ reg target⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1
      (if st.st.1.regs.getRegOrZr reg = 0 then branchTarget st sz target else st.st.2 + .ofNat sz))) := by
  by_cases h : st.st.1.regs.getRegOrZr reg = 0 <;> cellR hc [h, beq_iff_eq, bne_iff_ne, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte]

/-- **`cbnz Xt, target`**: no event; jump iff `Xt ≠ 0`. -/
theorem exec_cbnz {reg : RegOrZr .W64} {target : ConstExpr} (hc : CellAt st (.instr ⟨.W64, .CBNZ reg target⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1
      (if st.st.1.regs.getRegOrZr reg ≠ 0 then branchTarget st sz target else st.st.2 + .ofNat sz))) := by
  by_cases h : st.st.1.regs.getRegOrZr reg = 0 <;> cellR hc [h, beq_iff_eq, bne_iff_ne, ne_eq, not_false_eq_true, not_true_eq_false, ↓reduceIte]

/-- The return address `bl`/`blr` writes to `X30`: the address behind the
cell, as bits. -/
abbrev retAddr (st : State) (sz : Nat) : BitVec 64 := BitVec.ofInt 64 (st.st.2 + .ofNat sz).toInt

/-- **`bl target`**: no event; `X30` gets the return address, then jump. -/
theorem exec_bl {target : ConstExpr} (hc : CellAt st (.instr ⟨.W64, .BL target⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st
      { st.st.1 with regs := st.st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr st sz) }
      (branchTarget st sz target))) := by
  cellR hc []

/-- **`blr Xn`**: no event; `X30` gets the return address, then jump to the
address `Xn` held before. -/
theorem exec_blr {r : RegOrZr .W64} (hc : CellAt st (.instr ⟨.W64, .BLR r⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st
      { st.st.1 with regs := st.st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr st sz) }
      (Int64.ofInt (st.st.1.regs.getRegOrZr r).signed))) := by
  cellR hc []

/-- **`br Xn`**: no event; jump to the address `Xn` holds. -/
theorem exec_br {r : RegOrZr .W64} (hc : CellAt st (.instr ⟨.W64, .BR r⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1 (Int64.ofInt (st.st.1.regs.getRegOrZr r).signed))) := by
  cellR hc []

/-- **`ret Xn`** (`ret` is `ret x30`): no event; jump to the address `Xn`
holds. -/
theorem exec_ret {r : RegOrZr .W64} (hc : CellAt st (.instr ⟨.W64, .RET r⟩) sz) :
    isaLSE2.exec st = some (.done (jumpTo st st.st.1 (Int64.ofInt (st.st.1.regs.getRegOrZr r).signed))) := by
  cellR hc []

end NoEvent

end Kraken.Promising.Lower.A64

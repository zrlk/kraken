/-
**x64 instructions with undefined flags, on `X64.isa`.** The
`Lower/EventsX64.lean` rows for `and`/`or`/`xor`/`test`/`imul`/`shl`/`shr`/
`sar`.

These leave some status flags architecturally undefined (`AF` for the logic
operations; `SF`/`ZF`/`AF`/`PF` for `imul`; `AF`, and `OF` unless the count
is 1, for the shifts). Kraken's semantics reads an undefined flag through
`Effects.undefined`, which `toEv` (`Promising/X64.lean`) turns into a
two-way `choose`, so the tree at such a cell is a (nested) finite choice of
`done` leaves rather than one `done`, and the no-event rows' shape
(`isa.exec st = some (.done s)`, `instrSemInf_done_stutter`) does not apply.

## ISA-neutral: silent trees (`Lower/Silent.lean`)

- `SilentTree P t`: `t` is a finite choice, at least one branch at every
  node, of `done` leaves, each satisfying `P`. A `.done s` tree is
  `SilentTree (· = s)` (`silentTree_done`); a two-way choice of dones
  `silentTree_choose2`.
- `SilentTree.run`: every run of such a tree is a successful leaf, in the
  context it started from; `SilentTree.exists_run`: some leaf is run.
- `instrSemInf_silent`: an `InstrSemInf` step at such a tree is the
  `instrSemInf_done_iff` outcome of some leaf satisfying `P`;
  `instrSemInf_of_silent_leaf`/`instrSemInf_silent_exists`: the converse, and
  some leaf can be stepped to; `instrSemInf_silent_stutter`: the
  `instrSemInf_done_stutter` form; `stepOne_silent_no_error`: no error
  outcome.

## x64 rows (64-bit operands, 64-bit addressing)

- **Logic** (`AF` undefined, `CF = OF = 0`, `ZF`/`SF`/`PF` of the result:
  `logicFlags v af`): `exec_and_rr`/`exec_and_ri`, `exec_or_rr`/`exec_or_ri`,
  `exec_xor_rr`/`exec_xor_ri` (destination written, `logicPost`),
  `exec_test_rr`/`exec_test_ri` (flags only, `testPost`); each the exact tree
  `.choose 2 fun i => .done (… (i.val == 1))`, the choice being `AF`.
  Stutter forms `stutter_<row>`: `∃ af, Stutter … (logicPost …)`.
- **`imul`** (two- and three-operand, `SF`/`ZF`/`AF`/`PF` undefined, `CF =
  OF = imulOvf`): `exec_imul_rr`, `exec_imul_rri`, exact trees of four
  nested choices; `silent_imul_rr`/`silent_imul_rri` and `stutter_imul_rr`/
  `stutter_imul_rri`: destination `d := a * b`, flags arbitrary but for
  `CF = OF = imulOvf a b`.
- **Shifts by an immediate** (count `shCount st sz k`, masked to 6 bits,
  nonzero): `silent_shl_ri`, `silent_shr_ri`, `silent_sar_ri` (`d := a <<<
  n`, `a.ushiftRight n`, `a.sshiftRight n`, flags arbitrary) and their
  stutter forms.

`silent_*` rows are `∃ t, isa.exec st = some t ∧ SilentTree P t`: the
result register is the given value and the flags are universally quantified
over the choice (`P s'` says `s' = after st sz {…, status := fl}` for some
`fl`).
-/
import Kraken.Promising.Lower.EventsX64Inf
import Kraken.Promising.Lower.Silent

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- Read the cell through `exec_of_cellAt` and unfold it (`EventsX64.lean`'s
local `cell`, repeated: local macros do not cross files). -/
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

/-! ## Logic operations -/

section Logic

variable {st : State} {sz : Nat}

/-- The flags of `and`/`or`/`xor`/`test` with result `v`: `CF = OF = 0`,
`ZF`/`SF`/`PF` of `v`, `AF` the undefined bit `af`. -/
def logicFlags (v : BitVec 64) (af : Bool) : StatusFlags := .from_result v { cf := false, af, of := false }

/-- The state after a logic operation wrote `v` to `d`, `AF` bit `af`. -/
abbrev logicPost (st : State) (sz : Nat) (d : Reg .W64) (v : BitVec 64) (af : Bool) : State :=
  after st sz { st.st.1 with regs := st.st.1.regs.set d v, status := logicFlags v af }

/-- The state after `test` with result `v`, `AF` bit `af`: flags only. -/
abbrev testPost (st : State) (sz : Nat) (v : BitVec 64) (af : Bool) : State :=
  after st sz { st.st.1 with status := logicFlags v af }

/-- **`and r64, r64'`**: no event; `d := d &&& s`, a choice of `AF`. -/
theorem exec_and_rr {d s : Reg .W64} (hc : CellAt st (op64 (.and (.reg d) (.reg s))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (logicPost st sz d (st.st.1.regs.get d &&& st.st.1.regs.get s) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`and r64, imm`**: no event; `d := d &&& imm`, a choice of `AF`. -/
theorem exec_and_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.and (.reg d) (.imm k))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (logicPost st sz d (st.st.1.regs.get d &&& immVal st sz k) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`or r64, r64'`**: no event; `d := d ||| s`, a choice of `AF`. -/
theorem exec_or_rr {d s : Reg .W64} (hc : CellAt st (op64 (.or (.reg d) (.reg s))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (logicPost st sz d (st.st.1.regs.get d ||| st.st.1.regs.get s) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`or r64, imm`**: no event; `d := d ||| imm`, a choice of `AF`. -/
theorem exec_or_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.or (.reg d) (.imm k))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (logicPost st sz d (st.st.1.regs.get d ||| immVal st sz k) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`xor r64, r64'`**: no event; `d := d ^^^ s`, a choice of `AF`. -/
theorem exec_xor_rr {d s : Reg .W64} (hc : CellAt st (op64 (.xor (.reg d) (.reg s))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (logicPost st sz d (st.st.1.regs.get d ^^^ st.st.1.regs.get s) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`xor r64, imm`**: no event; `d := d ^^^ imm`, a choice of `AF`. -/
theorem exec_xor_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.xor (.reg d) (.imm k))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (logicPost st sz d (st.st.1.regs.get d ^^^ immVal st sz k) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`test r64, r64'`**: no event; the flags of `a &&& b`, a choice of `AF`. -/
theorem exec_test_rr {a b : Reg .W64} (hc : CellAt st (op64 (.test (.reg a) (.reg b))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (testPost st sz (st.st.1.regs.get a &&& st.st.1.regs.get b) (i.val == 1))) := by
  cell hc [logicFlags]

/-- **`test r64, imm`**: no event; the flags of `a &&& imm`, a choice of `AF`. -/
theorem exec_test_ri {a : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.test (.reg a) (.imm k))) sz) :
    isa.exec st = some (.choose 2 fun i => .done
      (testPost st sz (st.st.1.regs.get a &&& immVal st sz k) (i.val == 1))) := by
  cell hc [logicFlags]

/-- `xor r, r` (the zeroing idiom) writes 0 and sets `ZF`. -/
theorem logicFlags_xor_self_zf (v : BitVec 64) (af : Bool) : (logicFlags (v ^^^ v) af).zf = true := by
  simp [logicFlags, StatusFlags.from_result]

/-- `test` sets `ZF` iff the conjunction is zero. -/
theorem logicFlags_zf (v : BitVec 64) (af : Bool) : (logicFlags v af).zf = (v == 0#64) := rfl

end Logic

/-! ## `imul` -/

section Imul

variable {st : State} {sz : Nat}

/-- `imul`'s carry and overflow: the signed product does not fit in 64 bits. -/
def imulOvf (a b : BitVec 64) : Bool := (a * b).signed != a.signed * b.signed

/-- The state after `imul` wrote `a * b` to `d`, with the undefined `SF`,
`ZF`, `AF`, `PF` given. -/
abbrev imulPost (st : State) (sz : Nat) (d : Reg .W64) (a b : BitVec 64) (sf zf af pf : Bool) : State :=
  after st sz { st.st.1 with
    regs := st.st.1.regs.set d (a * b)
    status := { cf := imulOvf a b, pf := pf, af := af, zf := zf, sf := sf, of := imulOvf a b } }

/-- **`imul r64, r64'`** (two operands): no event; `d := d * s`, a choice
of each of `SF`, `ZF`, `AF`, `PF`. -/
theorem exec_imul_rr {d s : Reg .W64} (hc : CellAt st (op64 (.imul none (.reg d) (.reg s))) sz) :
    isa.exec st = some (.choose 2 fun sf => .choose 2 fun zf => .choose 2 fun af => .choose 2 fun pf => .done
      (imulPost st sz d (st.st.1.regs.get d) (st.st.1.regs.get s)
        (sf.val == 1) (zf.val == 1) (af.val == 1) (pf.val == 1))) := by
  cell hc [imulPost, imulOvf, BitVec.signed]

/-- **`imul r64, r64', imm`** (three operands): no event; `d := s * imm`, a
choice of each of `SF`, `ZF`, `AF`, `PF`. -/
theorem exec_imul_rri {d s : Reg .W64} {k : ConstExpr}
    (hc : CellAt st (op64 (.imul (some (.reg d)) (.reg s) (.imm k))) sz) :
    isa.exec st = some (.choose 2 fun sf => .choose 2 fun zf => .choose 2 fun af => .choose 2 fun pf => .done
      (imulPost st sz d (st.st.1.regs.get s) (immVal st sz k)
        (sf.val == 1) (zf.val == 1) (af.val == 1) (pf.val == 1))) := by
  cell hc [imulPost, imulOvf, BitVec.signed]

/-- `imulPost`'s four nested choices are a silent tree, each leaf `d := a *
b` with flags `fl` whose `CF` and `OF` are `imulOvf a b`. -/
theorem silentTree_imulPost (st : State) (sz : Nat) (d : Reg .W64) (a b : BitVec 64) :
    SilentTree (fun s' => ∃ fl : StatusFlags, fl.cf = imulOvf a b ∧ fl.of = imulOvf a b ∧
        s' = after st sz { st.st.1 with regs := st.st.1.regs.set d (a * b), status := fl })
      (.choose 2 fun sf => .choose 2 fun zf => .choose 2 fun af => .choose 2 fun pf => .done
        (imulPost st sz d a b (sf.val == 1) (zf.val == 1) (af.val == 1) (pf.val == 1)) : EvTree State) :=
  ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨by decide, fun _ => ⟨_, rfl, rfl, rfl⟩⟩⟩⟩⟩

/-- **`imul r64, r64'`, flags arbitrary**: `d := d * s`; `CF = OF =
imulOvf`. -/
theorem silent_imul_rr {d s : Reg .W64} (hc : CellAt st (op64 (.imul none (.reg d) (.reg s))) sz) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      fl.cf = imulOvf (st.st.1.regs.get d) (st.st.1.regs.get s) ∧
      fl.of = imulOvf (st.st.1.regs.get d) (st.st.1.regs.get s) ∧
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d (st.st.1.regs.get d * st.st.1.regs.get s), status := fl }) t :=
  ⟨_, exec_imul_rr hc, silentTree_imulPost ..⟩

/-- **`imul r64, r64', imm`, flags arbitrary**: `d := s * imm`; `CF = OF =
imulOvf`. -/
theorem silent_imul_rri {d s : Reg .W64} {k : ConstExpr}
    (hc : CellAt st (op64 (.imul (some (.reg d)) (.reg s) (.imm k))) sz) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      fl.cf = imulOvf (st.st.1.regs.get s) (immVal st sz k) ∧
      fl.of = imulOvf (st.st.1.regs.get s) (immVal st sz k) ∧
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d (st.st.1.regs.get s * immVal st sz k), status := fl }) t :=
  ⟨_, exec_imul_rri hc, silentTree_imulPost ..⟩

end Imul

/-! ## Shifts by an immediate -/

section Shift

variable {st : State} {sz : Nat}

/-- The count of a shift by the immediate `k` at the cell: its low 8 bits,
masked to 6 (a 64-bit operand). -/
abbrev shCount (st : State) (sz : Nat) (k : ConstExpr) : Nat :=
  @ShiftCountExpr.interpMasked (_root_.Executable.labels st.exe) (.imm8 k) st.st.1 (rangeOf st sz) .W64

theorem shCount_lt (st : State) (sz : Nat) (k : ConstExpr) : shCount st sz k < 64 :=
  Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

/-- **`shl r64, imm`, flags arbitrary** (count `n = shCount st sz k`,
nonzero): no event; `d := a <<< n`. -/
theorem silent_shl_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.shl (.reg d) (.imm8 k))) sz)
    (hk : shCount st sz k ≠ 0) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d (st.st.1.regs.get d <<< shCount st sz k), status := fl }) t := by
  have hlt := shCount_lt st sz k
  have hk' : (shCount st sz k == 0) = false := by simpa using hk
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [shCount] at hk' hlt
  by_cases h1 : (shCount st sz k == 1) = true <;> simp only [shCount, Bool.not_eq_true] at h1 <;>
    simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, h1,
      RegOrMem.interp, toEv, EvTree.map, SilentTree]

/-- **`shr r64, imm`, flags arbitrary** (count `n = shCount st sz k`,
nonzero): no event; `d := a.ushiftRight n`. -/
theorem silent_shr_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.shr (.reg d) (.imm8 k))) sz)
    (hk : shCount st sz k ≠ 0) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d ((st.st.1.regs.get d).ushiftRight (shCount st sz k)), status := fl }) t := by
  have hlt := shCount_lt st sz k
  have hk' : (shCount st sz k == 0) = false := by simpa using hk
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [shCount] at hk' hlt
  by_cases h1 : (shCount st sz k == 1) = true <;> simp only [shCount, Bool.not_eq_true] at h1 <;>
    simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, h1,
      RegOrMem.interp, toEv, EvTree.map, SilentTree]

/-- **`sar r64, imm`, flags arbitrary** (count `n = shCount st sz k`,
nonzero): no event; `d := a.sshiftRight n`. -/
theorem silent_sar_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt st (op64 (.sar (.reg d) (.imm8 k))) sz)
    (hk : shCount st sz k ≠ 0) :
    ∃ t, isa.exec st = some t ∧ SilentTree (fun s' => ∃ fl : StatusFlags,
      s' = after st sz { st.st.1 with
        regs := st.st.1.regs.set d ((st.st.1.regs.get d).sshiftRight (shCount st sz k)), status := fl }) t := by
  have hlt := shCount_lt st sz k
  have hk' : (shCount st sz k == 0) = false := by simpa using hk
  refine ⟨_, exec_of_cellAt hc, ?_⟩
  simp only [shCount] at hk' hlt
  by_cases h1 : (shCount st sz k == 1) = true <;> simp only [shCount, Bool.not_eq_true] at h1 <;>
    simp [Directive.interp, Instr.interp, Operation.interp, MachineData.set, MachineData.setReg, hk', hlt, h1,
      RegOrMem.interp, toEv, EvTree.map, SilentTree]

end Shift

/-! ## Source stutter -/

section Stutter

variable (A : Arch) (tid : Nat) {c c' : Config isa} {t : Thread isa}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **Any cell whose tree is silent is a source stutter** at one of its
leaves. -/
theorem stutter_of_silent {tree : EvTree State} {P : State → Prop} (hex : isa.exec t.st = some tree)
    (hs : SilentTree P tree) (h : InstrSemInf A tid c c') : ∃ s, P s ∧ Stutter A tid c c' t s :=
  instrSemInf_silent_stutter A tid ht hex hs h

/-- A two-way choice of `done`s is a source stutter at one of its branches. -/
theorem stutter_of_choose2 {f : Fin 2 → State} (hex : isa.exec t.st = some (.choose 2 fun i => .done (f i)))
    (h : InstrSemInf A tid c c') : ∃ i, Stutter A tid c c' t (f i) := by
  obtain ⟨_, ⟨i, rfl⟩, hs⟩ := stutter_of_silent A tid ht hex (silentTree_choose2 f) h
  exact ⟨i, hs⟩

/-- **`and r64, r64'`**: a stutter, `AF` arbitrary. -/
theorem stutter_and_rr {d s : Reg .W64} (hc : CellAt (stOf t) (op64 (.and (.reg d) (.reg s))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (logicPost (stOf t) sz d ((stOf t).st.1.regs.get d &&& (stOf t).st.1.regs.get s) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_and_rr hc) h
  ⟨_, hs⟩

/-- **`and r64, imm`**: a stutter, `AF` arbitrary. -/
theorem stutter_and_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.and (.reg d) (.imm k))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (logicPost (stOf t) sz d ((stOf t).st.1.regs.get d &&& immVal (stOf t) sz k) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_and_ri hc) h
  ⟨_, hs⟩

/-- **`or r64, r64'`**: a stutter, `AF` arbitrary. -/
theorem stutter_or_rr {d s : Reg .W64} (hc : CellAt (stOf t) (op64 (.or (.reg d) (.reg s))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (logicPost (stOf t) sz d ((stOf t).st.1.regs.get d ||| (stOf t).st.1.regs.get s) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_or_rr hc) h
  ⟨_, hs⟩

/-- **`or r64, imm`**: a stutter, `AF` arbitrary. -/
theorem stutter_or_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.or (.reg d) (.imm k))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (logicPost (stOf t) sz d ((stOf t).st.1.regs.get d ||| immVal (stOf t) sz k) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_or_ri hc) h
  ⟨_, hs⟩

/-- **`xor r64, r64'`**: a stutter, `AF` arbitrary. -/
theorem stutter_xor_rr {d s : Reg .W64} (hc : CellAt (stOf t) (op64 (.xor (.reg d) (.reg s))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (logicPost (stOf t) sz d ((stOf t).st.1.regs.get d ^^^ (stOf t).st.1.regs.get s) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_xor_rr hc) h
  ⟨_, hs⟩

/-- **`xor r64, imm`**: a stutter, `AF` arbitrary. -/
theorem stutter_xor_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.xor (.reg d) (.imm k))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (logicPost (stOf t) sz d ((stOf t).st.1.regs.get d ^^^ immVal (stOf t) sz k) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_xor_ri hc) h
  ⟨_, hs⟩

/-- **`test r64, r64'`**: a stutter, `AF` arbitrary. -/
theorem stutter_test_rr {a b : Reg .W64} (hc : CellAt (stOf t) (op64 (.test (.reg a) (.reg b))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (testPost (stOf t) sz ((stOf t).st.1.regs.get a &&& (stOf t).st.1.regs.get b) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_test_rr hc) h
  ⟨_, hs⟩

/-- **`test r64, imm`**: a stutter, `AF` arbitrary. -/
theorem stutter_test_ri {a : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.test (.reg a) (.imm k))) sz)
    (h : InstrSemInf A tid c c') : ∃ af : Bool, Stutter A tid c c' t (testPost (stOf t) sz ((stOf t).st.1.regs.get a &&& immVal (stOf t) sz k) af) :=
  let ⟨_, hs⟩ := stutter_of_choose2 A tid ht (exec_test_ri hc) h
  ⟨_, hs⟩

/-- **`imul r64, r64'`**: a stutter, `d := d * s`, flags arbitrary but for
`CF = OF = imulOvf`. -/
theorem stutter_imul_rr {d s : Reg .W64} (hc : CellAt (stOf t) (op64 (.imul none (.reg d) (.reg s))) sz)
    (h : InstrSemInf A tid c c') :
    ∃ fl : StatusFlags, fl.cf = imulOvf ((stOf t).st.1.regs.get d) ((stOf t).st.1.regs.get s) ∧ fl.of = imulOvf ((stOf t).st.1.regs.get d) ((stOf t).st.1.regs.get s) ∧
      Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with
        regs := (stOf t).st.1.regs.set d ((stOf t).st.1.regs.get d * (stOf t).st.1.regs.get s), status := fl }) := by
  obtain ⟨tr, hex, hs⟩ := silent_imul_rr hc
  obtain ⟨_, ⟨fl, h1, h2, rfl⟩, hst⟩ := stutter_of_silent A tid ht hex hs h
  exact ⟨fl, h1, h2, hst⟩

/-- **`imul r64, r64', imm`**: a stutter, `d := s * imm`, flags arbitrary
but for `CF = OF = imulOvf`. -/
theorem stutter_imul_rri {d s : Reg .W64} {k : ConstExpr}
    (hc : CellAt (stOf t) (op64 (.imul (some (.reg d)) (.reg s) (.imm k))) sz) (h : InstrSemInf A tid c c') :
    ∃ fl : StatusFlags, fl.cf = imulOvf ((stOf t).st.1.regs.get s) (immVal (stOf t) sz k) ∧
      fl.of = imulOvf ((stOf t).st.1.regs.get s) (immVal (stOf t) sz k) ∧
      Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with
        regs := (stOf t).st.1.regs.set d ((stOf t).st.1.regs.get s * immVal (stOf t) sz k), status := fl }) := by
  obtain ⟨tr, hex, hs⟩ := silent_imul_rri hc
  obtain ⟨_, ⟨fl, h1, h2, rfl⟩, hst⟩ := stutter_of_silent A tid ht hex hs h
  exact ⟨fl, h1, h2, hst⟩

/-- **`shl r64, imm`** (nonzero count): a stutter, flags arbitrary. -/
theorem stutter_shl_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.shl (.reg d) (.imm8 k))) sz)
    (hk : shCount (stOf t) sz k ≠ 0) (h : InstrSemInf A tid c c') :
    ∃ fl : StatusFlags, Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with
      regs := (stOf t).st.1.regs.set d ((stOf t).st.1.regs.get d <<< shCount (stOf t) sz k), status := fl }) := by
  obtain ⟨tr, hex, hs⟩ := silent_shl_ri hc hk
  obtain ⟨_, ⟨fl, rfl⟩, hst⟩ := stutter_of_silent A tid ht hex hs h
  exact ⟨fl, hst⟩

/-- **`shr r64, imm`** (nonzero count): a stutter, flags arbitrary. -/
theorem stutter_shr_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.shr (.reg d) (.imm8 k))) sz)
    (hk : shCount (stOf t) sz k ≠ 0) (h : InstrSemInf A tid c c') :
    ∃ fl : StatusFlags, Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with
      regs := (stOf t).st.1.regs.set d (((stOf t).st.1.regs.get d).ushiftRight (shCount (stOf t) sz k)), status := fl }) := by
  obtain ⟨tr, hex, hs⟩ := silent_shr_ri hc hk
  obtain ⟨_, ⟨fl, rfl⟩, hst⟩ := stutter_of_silent A tid ht hex hs h
  exact ⟨fl, hst⟩

/-- **`sar r64, imm`** (nonzero count): a stutter, flags arbitrary. -/
theorem stutter_sar_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.sar (.reg d) (.imm8 k))) sz)
    (hk : shCount (stOf t) sz k ≠ 0) (h : InstrSemInf A tid c c') :
    ∃ fl : StatusFlags, Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with
      regs := (stOf t).st.1.regs.set d (((stOf t).st.1.regs.get d).sshiftRight (shCount (stOf t) sz k)), status := fl }) := by
  obtain ⟨tr, hex, hs⟩ := silent_sar_ri hc hk
  obtain ⟨_, ⟨fl, rfl⟩, hst⟩ := stutter_of_silent A tid ht hex hs h
  exact ⟨fl, hst⟩

end Stutter

end Kraken.Promising.Lower.X64

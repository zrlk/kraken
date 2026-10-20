/-
**The AArch64 `isaLSE2` lowering rows on the fuel-free
machine.** Each row's `exec` lemma (`EventsA64.lean`) composed with the
event-level characterisation of `InstrSemInf` (`Events.lean`): an
`InstrSemInf` step of a thread whose pc is at the row's cell *is* the row's
event (a read, write, fence or RMW at the computed location), followed by
`finishInstr` and certification; a no-event row is a *source stutter*.

Hypotheses throughout: `ht` (the thread), `hc : CellAt` (the cell at the
pc), and for memory rows the address computation `ha`, `hdm` (address not in
the thread-private `dmem`) and `hag` (the declarations agree on the access,
so `access` resolves to the single location `⟨a, 8⟩`).
-/
import Kraken.Promising.Lower.CallsA64

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- A thread's state, at `State` (`isaLSE2.State` unfolds to it). -/
abbrev stOf (t : Thread isaLSE2) : State := t.st

/-- The instruction views of `t`'s next instruction. -/
abbrev ivOf (t : Thread isaLSE2) : InstrViews := instrViews t (isaLSE2.deps t.st)

/-- **Source stutter at `s`**: only `tid`'s thread changes, memory does not;
the new state is `s`, the promises are kept, and the views are kept up to a
`vCAP` bump by the instruction's `condW` view. -/
def Stutter (A : Arch) (tid : Nat) (c c' : Config isaLSE2) (t : Thread isaLSE2) (s : State) : Prop :=
  ∃ th, c' = c.withThread tid th c.mem ∧ th.st = s ∧ th.prom = t.prom ∧
    (th.views = t.views ∨ th.views = { t.views with vCAP := max t.views.vCAP (ivOf t).condW }) ∧
    CertOk A tid th c.mem

variable (A : Arch) (tid : Nat) {c c' : Config isaLSE2} {t : Thread isaLSE2}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-! ## Loads -/

/-- **`ldr Xt, [Xn, #i]`**: one plain read of `⟨a, 8⟩`. -/
theorem instrSemInf_ldr {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 (((stOf t).st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none) (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, 8⟩ ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.setRegOrZr dst (v.setWidth 64) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (exec_ldr_agrees hc ha hdm hag)

/-- **`ldar`/`ldapr`/`ldaxr` `Xt, [Xn]`** (kind `k`, exclusivity `xcl`): one
read of `⟨Xn, 8⟩`; `ldar` is `k = .acq`, `ldapr` is `k = .acqPc`. -/
theorem instrSemInf_ldar {dst : RegOrZr .W64} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .LDAR k xcl .W64 dst (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem ((stOf t).st.1.regs.getXReg n).toBitVec 8 = none)
    (hag : (stOf t).decls.AgreesAt ((stOf t).st.1.regs.getXReg n).toBitVec 8) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) k xcl ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 8⟩ ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.setRegOrZr dst (v.setWidth 64) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (exec_ldar_agrees hc hdm hag)

/-! ## Stores -/

/-- **`str Xt, [Xn, #i]`**: one plain, non-exclusive write to `⟨a, 8⟩`. -/
theorem instrSemInf_str {src : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .STR src ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩⟩) sz)
    {a : BitVec 64} (ha : BitVec.ofInt 64 (((stOf t).st.1.regs.getXReg n).toBitVec.toInt + i.toInt) = a)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none) (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false ⟨a, 8⟩
        (((stOf t).st.1.regs.getRegOrZr src).setWidth 128) none ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (exec_str_agrees hc ha hdm hag)

/-- **`stlr Xt, [Xn]`**: one release write to `⟨Xn, 8⟩`. -/
theorem instrSemInf_stlr {src : RegOrZr .W64} {n : XReg}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .STLR .W64 src (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem ((stOf t).st.1.regs.getXReg n).toBitVec 8 = none)
    (hag : (stOf t).decls.AgreesAt ((stOf t).st.1.regs.getXReg n).toBitVec 8) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .rel false
        ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 8⟩ (((stOf t).st.1.regs.getRegOrZr src).setWidth 128) none ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (exec_stlr_agrees hc hdm hag)

/-! ## Fences -/

/-- **`dmb ish`/`dmb ishst`** (kind `k`): one fence, memory unchanged. -/
theorem instrSemInf_dmb {k : FenceKind} (hc : CellAt (stOf t) (.instr ⟨.W64, .DMB k⟩) sz) :
    InstrSemInf A tid c c' ↔ ∃ th,
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1)
        (fenceStep (ctx0 tid t c.mem) k) ∧
      CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem :=
  instrSemInf_fence_iff A tid ht (exec_dmb hc)

/-! ## RMWs

`instrSemInf_rmw_iff` at the row's tree; the conclusion is that lemma's
right-hand side at the row's `k`, `noRet`, location and operation. -/

/-- **`cas`/`casa`/`casl`/`casal` `Xs, Xt, [Xn]`**: one RMW at `⟨Xn, 8⟩` with
operation `casOp Xs Xt` (no write when the comparison fails). -/
theorem instrSemInf_cas {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .CAS k .W64 rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem ((stOf t).st.1.regs.getXReg n).toBitVec 8 = none)
    (hag : (stOf t).decls.AgreesAt ((stOf t).st.1.regs.getXReg n).toBitVec 8) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (if rs.isZr then .plain else (A.rmwKind k).loadKind) false
          ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 8⟩ rs.isZr ∧
      ((casOp ((stOf t).st.1.regs.getRegOrZr rs) ((stOf t).st.1.regs.getRegOrZr rt) old = none ∧
          cf = rmwFenceOpt A c1) ∨
       (∃ new c2, casOp ((stOf t).st.1.regs.getRegOrZr rs) ((stOf t).st.1.regs.getRegOrZr rt) old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true
            ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 8⟩ new (some tr) (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) rs.isZr ⟨((stOf t).st.1.regs.getXReg n).toBitVec, 8⟩
            { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.setRegOrZr rs (old.setWidth 64) }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_iff A tid ht (exec_cas_agrees hc hdm hag)

/-- **`swp`/`ldadd`/… resolved**: after `access` resolves (`hag`), a
`swp`/`ld<op>` tree is one RMW at `⟨Xn, 8⟩`. Stated once for the resolved
tree shape (`exec_swp`/`exec_ldop` give it under `map_access`/`access_agrees`). -/
theorem instrSemInf_rmw_at {k : RmwKind} {noRet : Bool} {l : Loc} {op : Val → Option Val}
    {f : Val → State} (hex : isaLSE2.exec t.st = some (.rmw k noRet l op fun v => .done (f v))) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (if noRet then .plain else (A.rmwKind k).loadKind) false l noRet ∧
      ((op old = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, op old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true l new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) noRet l { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t) (f old) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_iff A tid ht hex

/-! ## No-event rows: source stutter -/

/-- Any cell whose tree is `.done s` is a source stutter at `s`. -/
theorem stutter_of_exec {s : State} (hex : isaLSE2.exec t.st = some (.done s))
    (h : InstrSemInf A tid c c') : Stutter A tid c c' t s :=
  instrSemInf_done_stutter A tid ht hex h

/-- **`b L`**: a stutter to the branch target. -/
theorem stutter_b {target : ConstExpr} (hc : CellAt (stOf t) (.instr ⟨.W64, .B target⟩) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (branchTarget (stOf t) sz target)) :=
  stutter_of_exec A tid ht (exec_b hc) h

/-- **`b.cond L`**: a stutter to the target or the next cell. -/
theorem stutter_bcond {cond : CondCode} {target : ConstExpr}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .B_cond cond target⟩) sz) (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (if cond.interp (stOf t).st.1.status
      then branchTarget (stOf t) sz target else (stOf t).st.2 + .ofNat sz)) :=
  stutter_of_exec A tid ht (exec_bcond hc) h

/-- **`cbz Xt, L`**. -/
theorem stutter_cbz {reg : RegOrZr .W64} {target : ConstExpr}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .CBZ reg target⟩) sz) (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (if (stOf t).st.1.regs.getRegOrZr reg = 0
      then branchTarget (stOf t) sz target else (stOf t).st.2 + .ofNat sz)) :=
  stutter_of_exec A tid ht (exec_cbz hc) h

/-- **`cbnz Xt, L`**. -/
theorem stutter_cbnz {reg : RegOrZr .W64} {target : ConstExpr}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .CBNZ reg target⟩) sz) (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (if (stOf t).st.1.regs.getRegOrZr reg ≠ 0
      then branchTarget (stOf t) sz target else (stOf t).st.2 + .ofNat sz)) :=
  stutter_of_exec A tid ht (exec_cbnz hc) h

/-- **`bl L`**: a stutter to `L` with `x30 := pc + sz`. -/
theorem stutter_bl {target : ConstExpr} (hc : CellAt (stOf t) (.instr ⟨.W64, .BL target⟩) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t)
      { (stOf t).st.1 with regs := (stOf t).st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr (stOf t) sz) }
      (branchTarget (stOf t) sz target)) :=
  stutter_of_exec A tid ht (exec_bl hc) h

/-- **`blr Xn`**: a stutter to the computed target `Xn`, with `x30 := pc + sz`. -/
theorem stutter_blr {r : RegOrZr .W64} (hc : CellAt (stOf t) (.instr ⟨.W64, .BLR r⟩) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t)
      { (stOf t).st.1 with regs := (stOf t).st.1.regs.setRegOrZr (.low (.reg .X30) .W64) (retAddr (stOf t) sz) }
      (Int64.ofBitVec ((stOf t).st.1.regs.getRegOrZr r))) := by
  have := stutter_of_exec A tid ht (exec_blr hc) h
  rwa [jump_target_eq] at this

/-- **`br Xn`**: a stutter to the computed target `Xn`. -/
theorem stutter_br {r : RegOrZr .W64} (hc : CellAt (stOf t) (.instr ⟨.W64, .BR r⟩) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (Int64.ofBitVec ((stOf t).st.1.regs.getRegOrZr r))) := by
  have := stutter_of_exec A tid ht (exec_br hc) h
  rwa [jump_target_eq] at this

/-- **`ret Xn`** (`ret` is `ret x30`): a stutter to the computed target `Xn`. -/
theorem stutter_ret {r : RegOrZr .W64} (hc : CellAt (stOf t) (.instr ⟨.W64, .RET r⟩) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (Int64.ofBitVec ((stOf t).st.1.regs.getRegOrZr r))) := by
  have := stutter_of_exec A tid ht (exec_ret hc) h
  rwa [jump_target_eq] at this

/-- **`add`/`mov` (`orr`, `movz`)/`cmp` (`subs`)**: a stutter to the next cell,
memory untouched; the register/flag update is the one in `exec_add_s`,
`exec_add_e`, `exec_orr_s`, `exec_movz`, `exec_subs_s`, `exec_subs_e`. -/
theorem stutter_alu {s' : MachineData} (hex : isaLSE2.exec t.st = some (.done (after (stOf t) sz s')))
    (h : InstrSemInf A tid c c') : Stutter A tid c c' t (after (stOf t) sz s') :=
  stutter_of_exec A tid ht hex h

example {dst src1 : RegOrZr .W64} {src2 : ShiftRegExpr .W64}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .ADD_s dst src1 src2⟩) sz) (h : InstrSemInf A tid c c') :
    ∃ s', Stutter A tid c c' t (after (stOf t) sz s') :=
  ⟨_, stutter_alu A tid ht (exec_add_s hc) h⟩

example {dst src1 : RegOrZr .W64} {src2 : ShiftRegExpr .W64}
    (hc : CellAt (stOf t) (.instr ⟨.W64, .SUBS_s dst src1 src2⟩) sz) (h : InstrSemInf A tid c c') :
    ∃ s', Stutter A tid c c' t (after (stOf t) sz s') :=
  ⟨_, stutter_alu A tid ht (exec_subs_s hc) h⟩

end Kraken.Promising.Lower.A64

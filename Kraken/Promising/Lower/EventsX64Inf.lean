/-
**The x64 lowering rows on the fuel-free machine.** The x64 twin of
`Lower/EventsA64Inf.lean`: each row's `exec`
lemma (`EventsX64.lean`) composed with the event-level characterisation of
`InstrSemInf` (`Events.lean`). An `InstrSemInf` step of a thread whose pc is
at the row's cell *is* the row's event (a read, write, fence or RMW at the
computed location), followed by `finishInstr` and certification; a no-event
row is a *source stutter*.

The architecture `A` is generic, as in `Events.lean`; the x64 target is
`X64.isa` under the TSO profile, where `rmwFenceOpt A` is the `fence .sy`
around every locked RMW.

Hypotheses throughout: `ht` (the thread), `hc : CellAt` (the cell at the
pc), and for memory rows the address computation `ha`, `hdm` (address not in
the thread-private `dmem`) and `hag` (the declarations agree on the access,
so `access` resolves to the single location `⟨a, 8⟩`, or `⟨a, 16⟩`).
-/
import Kraken.Promising.Lower.EventsX64

namespace Kraken.Promising.Lower.X64

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

/-- A thread's state, at `State` (`isa.State` unfolds to it). -/
abbrev stOf (t : Thread isa) : State := t.st

/-- The instruction views of `t`'s next instruction. -/
abbrev ivOf (t : Thread isa) : InstrViews := instrViews t (isa.deps t.st)

/-- **Source stutter at `s`**: only `tid`'s thread changes, memory does not;
the new state is `s`, the promises are kept, and the views are kept up to a
`vCAP` bump by the instruction's `condW` view. -/
def Stutter (A : Arch) (tid : Nat) (c c' : Config isa) (t : Thread isa) (s : State) : Prop :=
  ∃ th, c' = c.withThread tid th c.mem ∧ th.st = s ∧ th.prom = t.prom ∧
    (th.views = t.views ∨ th.views = { t.views with vCAP := max t.views.vCAP (ivOf t).condW }) ∧
    CertOk A tid th c.mem

variable (A : Arch) (tid : Nat) {c c' : Config isa} {t : Thread isa}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-! ## Loads and stores -/

/-- **`mov r64, [m]`**: one plain read of `⟨a, 8⟩`. -/
theorem instrSemInf_load {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt (stOf t) (op64 (.mov (.reg r) (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, 8⟩ ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.set r (v.setWidth 64) }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (exec_load_agrees hc ha hdm hag)

/-- **`mov [m], r64`**: one plain, non-exclusive write to `⟨a, 8⟩`. -/
theorem instrSemInf_store {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt (stOf t) (op64 (.mov (.mem m) (.reg r))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false ⟨a, 8⟩
        (((stOf t).st.1.regs.get r).setWidth 128) none ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (exec_store_agrees hc ha hdm hag)

/-! ## RMWs -/

/-- **A resolved locked RMW** (`noRet = false`, kind `k`): one RMW at `l`.
Every x64 RMW row below is this at its operation. -/
theorem instrSemInf_rmw_at {k : RmwKind} {l : Loc} {op : Val → Option Val}
    {f : Val → State} (hex : isa.exec t.st = some (.rmw k false l op fun v => .done (f v))) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind k).loadKind false l false ∧
      ((op old = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, op old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true l new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind k) false l { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (f old) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem := by
  rw [instrSemInf_rmw_iff A tid ht hex]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- **`lock cmpxchg [m], r64`**: one locked RMW at `⟨a, 8⟩` with operation
`cmpxOp rax r`; a failed compare is the `op old = none` branch (no write). -/
theorem instrSemInf_cmpxchg {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt (stOf t) (op64 (.cmpxchg true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, 8⟩ false ∧
      ((cmpxOp ((stOf t).st.1.regs.get (.low .rax .W64)) ((stOf t).st.1.regs.get r) old = none ∧
          cf = rmwFenceOpt A c1) ∨
       (∃ new c2, cmpxOp ((stOf t).st.1.regs.get (.low .rax .W64)) ((stOf t).st.1.regs.get r) old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, 8⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, 8⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (cmpxPost (stOf t).st.1 (old.setWidth 64))) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (exec_cmpxchg_agrees hc ha hdm hag)

/-- **`xchg r64, [m]`**: one locked RMW at `⟨a, 8⟩` writing `r`. -/
theorem instrSemInf_xchg {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt (stOf t) (op64 (.xchg r (.mem m))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, 8⟩ false ∧
      ((some (((stOf t).st.1.regs.get r).setWidth 128) = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, some (((stOf t).st.1.regs.get r).setWidth 128) = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, 8⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, 8⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with regs := (stOf t).st.1.regs.set r (old.setWidth 64) }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (op := fun _ => some (((stOf t).st.1.regs.get r).setWidth 128))
    (by rw [exec_xchg hc ha hdm, access_agrees hag])

/-- **`lock xadd [m], r64`**: one locked RMW at `⟨a, 8⟩` writing `old + r`. -/
theorem instrSemInf_xadd {r : Reg .W64} {m : AddrExpr}
    (hc : CellAt (stOf t) (op64 (.xadd true (.mem m) r)) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (hdm : Mem.loadInt (stOf t).st.1.dmem a 8 = none)
    (hag : (stOf t).decls.AgreesAt a 8) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, 8⟩ false ∧
      ((some ((old.setWidth 64 + (stOf t).st.1.regs.get r).setWidth 128) = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, some ((old.setWidth 64 + (stOf t).st.1.regs.get r).setWidth 128) = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, 8⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, 8⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := (stOf t).st.1.regs.set r (old.setWidth 64)
          status := LockBinOp.add.status (old.setWidth 64) ((stOf t).st.1.regs.get r)
            (old.setWidth 64 + (stOf t).st.1.regs.get r) false }) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (by rw [exec_xadd hc ha hdm, access_agrees hag])

/-- **`lock cmpxchg16b [m]`** (16-aligned): one locked 16-byte RMW at
`⟨a, 16⟩` with operation `cmpx16Op rdx:rax rcx:rbx`. -/
theorem instrSemInf_cmpxchg16b {m : AddrExpr}
    (hc : CellAt (stOf t) (.instr (.avx .W64 .W128 (.cmpxchg16b true m))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (h16 : isAligned 16 a = true)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 16 = none) (hag : (stOf t).decls.AgreesAt a 16) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 cf th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (A.rmwKind .acqRel).loadKind false ⟨a, 16⟩ false ∧
      ((cmpx16Op (acc16 (stOf t).st.1) (new16 (stOf t).st.1) old = none ∧ cf = rmwFenceOpt A c1) ∨
       (∃ new c2, cmpx16Op (acc16 (stOf t).st.1) (new16 (stOf t).st.1) old = some new ∧
          c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind .acqRel).storeKind true ⟨a, 16⟩ new (some tr)
            (c1.loadViews.getLastD 0) ∧
          cf = rmwFenceOpt A (rmwBump (A.rmwKind .acqRel) false ⟨a, 16⟩ { c2 with rmwWrote := true }))) ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (cmpx16Post (stOf t).st.1 old)) cf ∧
      CertOk A tid th cf.mem ∧ c' = c.withThread tid th cf.mem :=
  instrSemInf_rmw_at A tid ht (by rw [exec_cmpxchg16b hc ha h16 hdm, access_agrees hag])

/-! ## Fence and aligned 16-byte moves -/

/-- **`mfence`**: one `.sy` fence, memory unchanged. -/
theorem instrSemInf_mfence (hc : CellAt (stOf t) (op64 .mfence) sz) :
    InstrSemInf A tid c c' ↔ ∃ th,
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1)
        (fenceStep (ctx0 tid t c.mem) .sy) ∧
      CertOk A tid th c.mem ∧ c' = c.withThread tid th c.mem :=
  instrSemInf_fence_iff A tid ht (exec_mfence hc)

/-- **Aligned `movdqa xmm, [m]`**: one plain 16-byte read of `⟨a, 16⟩`. -/
theorem instrSemInf_movdqa_load {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt (stOf t) (.instr (.avx .W64 .W128 (.movdqa (.avx x) (.mem m)))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (h16 : isAligned 16 a = true)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 16 = none) (hag : (stOf t).decls.AgreesAt a 16) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨a, 16⟩ ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with zmms := (stOf t).st.1.zmms.setLegacy x v }) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (by rw [exec_movdqa_load hc ha h16 hdm, access_agrees hag])

/-- **Aligned `movdqa [m], xmm`**: one plain 16-byte write to `⟨a, 16⟩`. -/
theorem instrSemInf_movdqa_store {x : AvxReg .W128} {m : AddrExpr}
    (hc : CellAt (stOf t) (.instr (.avx .W64 .W128 (.movdqa (.mem m) (.avx x)))) sz)
    {a : BitVec 64} (ha : eaddr (stOf t) sz m = a) (h16 : isAligned 16 a = true)
    (hdm : Mem.loadInt (stOf t).st.1.dmem a 16 = none) (hag : (stOf t).decls.AgreesAt a 16) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false ⟨a, 16⟩
        ((stOf t).st.1.zmms.get x) none ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t) (after (stOf t) sz (stOf t).st.1) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (by rw [exec_movdqa_store hc ha h16 hdm, access_agrees hag])

/-! ## No-event rows: source stutter -/

/-- Any cell whose tree is `.done s` is a source stutter at `s`. -/
theorem stutter_of_exec {s : State} (hex : isa.exec t.st = some (.done s))
    (h : InstrSemInf A tid c c') : Stutter A tid c c' t s :=
  instrSemInf_done_stutter A tid ht hex h

/-- **`mov r64, r64'`**. -/
theorem stutter_mov_rr {d s : Reg .W64} (hc : CellAt (stOf t) (op64 (.mov (.reg d) (.reg s))) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (after (stOf t) sz
      { (stOf t).st.1 with regs := (stOf t).st.1.regs.set d ((stOf t).st.1.regs.get s) }) :=
  stutter_of_exec A tid ht (exec_mov_rr hc) h

/-- **`mov r64, imm`**. -/
theorem stutter_mov_ri {d : Reg .W64} {k : ConstExpr} (hc : CellAt (stOf t) (op64 (.mov (.reg d) (.imm k))) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (after (stOf t) sz
      { (stOf t).st.1 with regs := (stOf t).st.1.regs.set d (immVal (stOf t) sz k) }) :=
  stutter_of_exec A tid ht (exec_mov_ri hc) h

/-- **`lea r64, [m]`** (no access). -/
theorem stutter_lea {d : Reg .W64} {m : AddrExpr} (hc : CellAt (stOf t) (op64 (.lea d m)) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (after (stOf t) sz
      { (stOf t).st.1 with regs := (stOf t).st.1.regs.set d (eaddr (stOf t) sz m) }) :=
  stutter_of_exec A tid ht (exec_lea hc) h

/-- **`add r64, r64'`**: a stutter to the next cell, flags `fl`. -/
theorem stutter_add_rr {d s : Reg .W64} (hc : CellAt (stOf t) (op64 (.add (.reg d) (.reg s))) sz)
    (h : InstrSemInf A tid c c') :
    ∃ fl, Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with
      regs := (stOf t).st.1.regs.set d ((stOf t).st.1.regs.get s + (stOf t).st.1.regs.get d), status := fl }) :=
  let ⟨_, hex⟩ := exec_add_rr hc
  ⟨_, stutter_of_exec A tid ht hex h⟩

/-- **`cmp r64, r64'`**: a stutter to the next cell, only the flags change. -/
theorem stutter_cmp_rr {a b : Reg .W64} (hc : CellAt (stOf t) (op64 (.cmp (.reg a) (.reg b))) sz)
    (h : InstrSemInf A tid c c') :
    ∃ fl, Stutter A tid c c' t (after (stOf t) sz { (stOf t).st.1 with status := fl }) :=
  let ⟨_, hex⟩ := exec_cmp_rr hc
  ⟨_, stutter_of_exec A tid ht hex h⟩

/-- **`jmp L`**. -/
theorem stutter_jmp_label {L : Label}
    (hc : CellAt (stOf t) (op64 (.jmp (.rel (.sub (.label L) .after_current_instruction)))) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (labelAddr (stOf t) L)) :=
  stutter_of_exec A tid ht (exec_jmp_label hc) h

/-- **`jcc L`**. -/
theorem stutter_jcc {cc : CondCode} {L : Label} (hc : CellAt (stOf t) (op64 (.jcc cc L)) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1
      (if cc.interp (stOf t).st.1.status then labelAddr (stOf t) L else (stOf t).st.2 + .ofNat sz)) :=
  stutter_of_exec A tid ht (exec_jcc hc) h

/-- **`jmp *r64`**. -/
theorem stutter_jmp_reg {r : Reg .W64} (hc : CellAt (stOf t) (op64 (.jmp (.reg r))) sz)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (stOf t).st.1 (Int64.ofBitVec ((stOf t).st.1.regs.get r))) :=
  stutter_of_exec A tid ht (exec_jmp_reg hc) h

/-! ## `call`/`ret`

With the stack slot mapped in `dmem`: source stutters. Unmapped: the
`InstrSemInf` step is one plain shared write (`call`) or read (`ret`). -/

/-- **`call L`, slot mapped**: a stutter to `L`, `rsp -= 8`, the return
address in the private slot. -/
theorem stutter_call_label {L : Label}
    (hc : CellAt (stOf t) (op64 (.call (.rel (.sub (.label L) .after_current_instruction)))) sz)
    {j : Int} (hdm : Mem.loadInt (stOf t).st.1.dmem (rspOf (stOf t).st.1 - 8#64) 8 = some j)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (callPost (stOf t) sz) (labelAddr (stOf t) L)) :=
  stutter_of_exec A tid ht (exec_call_label hc hdm) h

/-- **`call *r64`, slot mapped**. -/
theorem stutter_call_reg {r : Reg .W64} (hc : CellAt (stOf t) (op64 (.call (.reg r))) sz)
    {j : Int} (hdm : Mem.loadInt (stOf t).st.1.dmem (rspOf (stOf t).st.1 - 8#64) 8 = some j)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t) (callPost (stOf t) sz) (Int64.ofBitVec ((stOf t).st.1.regs.get r))) :=
  stutter_of_exec A tid ht (exec_call_reg hc hdm) h

/-- **`ret`, slot mapped**: a stutter to the address the slot held. -/
theorem stutter_ret (hc : CellAt (stOf t) (op64 .ret) sz)
    {j : Int} (hdm : Mem.loadInt (stOf t).st.1.dmem (rspOf (stOf t).st.1) 8 = some j)
    (h : InstrSemInf A tid c c') :
    Stutter A tid c c' t (jumpTo (stOf t)
      { (stOf t).st.1 with regs := (stOf t).st.1.regs.set64 .rsp (rspOf (stOf t).st.1 + 8#64) }
      (Int64.ofBitVec (BitVec.ofInt 64 j))) :=
  stutter_of_exec A tid ht (exec_ret hc hdm) h

/-- **`call L`, slot not mapped**: one plain shared write of the return
address to `⟨rsp - 8, 8⟩`. -/
theorem instrSemInf_call_label_shared {L : Label}
    (hc : CellAt (stOf t) (op64 (.call (.rel (.sub (.label L) .after_current_instruction)))) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (rspOf (stOf t).st.1 - 8#64) 8 = none)
    (hag : (stOf t).decls.AgreesAt (rspOf (stOf t).st.1 - 8#64) 8) :
    InstrSemInf A tid c c' ↔ ∃ c1 th,
      c1 ∈ writeSuccs A tid ((ivOf t).forStore 0) (ctx0 tid t c.mem) .plain false
        ⟨rspOf (stOf t).st.1 - 8#64, 8⟩ ((retAddr (stOf t) sz).setWidth 128) none ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (jumpTo (stOf t) { (stOf t).st.1 with regs := (stOf t).st.1.regs.set64 .rsp (rspOf (stOf t).st.1 - 8#64) }
          (labelAddr (stOf t) L)) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_store_iff A tid ht (by rw [exec_call_label_shared hc hdm, access_agrees hag])

/-- **`ret`, slot not mapped**: one plain shared read of `⟨rsp, 8⟩`; jump to
the value read. -/
theorem instrSemInf_ret_shared (hc : CellAt (stOf t) (op64 .ret) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (rspOf (stOf t).st.1) 8 = none)
    (hag : (stOf t).decls.AgreesAt (rspOf (stOf t).st.1) 8) :
    InstrSemInf A tid c c' ↔ ∃ ts v c1 th,
      (ts, v, c1) ∈ readSuccs A (ivOf t) (ctx0 tid t c.mem) .plain false ⟨rspOf (stOf t).st.1, 8⟩ ∧
      th ∈ finishInstr t (isa.deps t.st) (ivOf t)
        (jumpTo (stOf t) { (stOf t).st.1 with regs := (stOf t).st.1.regs.set64 .rsp (rspOf (stOf t).st.1 + 8#64) }
          (Int64.ofBitVec (v.setWidth 64))) c1 ∧
      CertOk A tid th c1.mem ∧ c' = c.withThread tid th c1.mem :=
  instrSemInf_load_iff A tid ht (by rw [exec_ret_shared hc hdm, access_agrees hag])

end Kraken.Promising.Lower.X64

/-
**`ret0.w`'s runtime entry, `scc_rt_main`'s prologue and tail, and
`wc_main`'s prologue** (AArch64) in any valid layout of `ret0Prog`
(`Spike/Lib/A64Ret0Code.lean`), from the checks of
`Spike/Lib/A64CodeSegs.lean` decided once on the program (`decide +kernel`):

- `ret0_start_seg`: `scc_rt_start` up to its call of `scc_rt_alloc_tcb`;
- `ret0_main_prologue_seg`, `ret0_wc_prologue_seg`: the stack-checked
  prologues (frames 48 and 32, the limit at `[tpidr_el0, #8]`);
- `ret0_main_exit_seg`: from the return of `wc_main`, `exit_group`, a
  segment to any fragment;
- `ret0_wc_body_seg`: `wc_main`'s body, the overflow-checked add (the
  branch to the abort not taken) and the return of `42`.

The limit's offset and `wc_main`'s frame are checked against the thread
control block's layout and the placement data (`#guard`).
-/
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64Ret0Rows
import Spike.Lib.A64Ret0Place

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)

set_option linter.unusedSimpArgs false

/-! ## `ret0.w` -/

section Ret0

open SccCode

-- The limit's offset is the thread control block's (`Scc.IR.Tcb.stackLimit`), and `wc_main`'s frame is
-- the placement data's: its one IR register at the frame's base.
#guard Scc.IR.Tcb.stackLimit = 8
#guard SccPlace.ret0.wc_main_rs "y%0" = some (-32)

/-- `scc_rt_main`'s prologue. -/
abbrev mainPro : Bool := prologueIn ret0Prog "scc_rt_main" ".L1_scc_rt_main.stack_check" ".L1_scc_rt_main.0_entry" 48 8
  ".L1_scc_rt_main.stack_grow" [(.X0, 0)]

/-- `wc_main`'s prologue. -/
abbrev wcPro : Bool := prologueIn ret0Prog "wc_main" ".L18_wc_main.stack_check" ".L18_wc_main.0_entry" 32 8
  ".L18_wc_main.stack_grow" []

#guard mainPro
#guard wcPro
#guard exitIn ret0Prog ".L1_scc_rt_main.sp0" 8
#guard startIn ret0Prog

theorem ret0_mainPro : mainPro = true := by decide +kernel
theorem ret0_wcPro : wcPro = true := by decide +kernel
theorem ret0_exitIn : exitIn ret0Prog ".L1_scc_rt_main.sp0" 8 = true := by decide +kernel
theorem ret0_startIn : startIn ret0Prog = true := by decide +kernel

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`ret0Prog`. Its states lie in `W`, none moved by
`K` (`hW`). -/
theorem ret0_start_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + Int64.ofNat (4 * 9))
    (ho : SO.le nC.o Abort.oI = true)
    (hW : StartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩)
      (At exe endPc R F nC) :=
  start_seg_ofW hp hend ret0_startIn hK hF hR hal hlo hhi hpc ho hW hedge

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`ret0Prog`. -/
theorem ret0_start_seg (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + Int64.ofNat (4 * 9))
    (ho : SO.le nC.o Abort.oI = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩)
      (At exe endPc R F nC) :=
  (ret0_start_segW hp hend hK hF hR hal hlo hhi hpc ho StartW.triv hedge).toSeg

/-- **S5: `scc_rt_main`'s prologue** in any valid layout of `ret0Prog`. Its states lie in `W`, none moved by `K`
(`hW`). -/
theorem ret0_main_prologue_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L1_scc_rt_main.0_entry")
    (ho : SO.le nb.o (oFr 48) = true)
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 48 8
      ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (48 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 48 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 48 σ.regs }).regs →
          σ'.slot = stSlots (-(48 : Int64).toInt) σ'.regs [(.X0, 0)] (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend ret0_mainPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hW hedge

/-- **S5: `scc_rt_main`'s prologue** in any valid layout of `ret0Prog`. -/
theorem ret0_main_prologue_seg (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L1_scc_rt_main.0_entry")
    (ho : SO.le nb.o (oFr 48) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (48 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 48 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 48 σ.regs }).regs →
          σ'.slot = stSlots (-(48 : Int64).toInt) σ'.regs [(.X0, 0)] (frSlot σ) → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (ret0_main_prologue_segW hp hend hF hR hal hlo hhi hpc ho ProW.triv hedge).toSeg

/-- **`wc_main`'s prologue** in any valid layout of `ret0Prog`. Its states lie in `W`, none moved by `K`
(`hW`). -/
theorem ret0_wc_prologue_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L18_wc_main.0_entry")
    (ho : SO.le nb.o (oFr 32) = true)
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 32 8
      ".L18_wc_main.stack_grow" [] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 32 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 32 σ.regs }).regs →
          σ'.slot = stSlots (-(32 : Int64).toInt) σ'.regs [] (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend ret0_wcPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hW hedge

/-- **`wc_main`'s prologue** in any valid layout of `ret0Prog`. -/
theorem ret0_wc_prologue_seg (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L18_wc_main.0_entry")
    (ho : SO.le nb.o (oFr 32) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 32 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 32 σ.regs }).regs →
          σ'.slot = stSlots (-(32 : Int64).toInt) σ'.regs [] (frSlot σ) → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (ret0_wc_prologue_segW hp hend hF hR hal hlo hhi hpc ho ProW.triv hedge).toSeg

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`ret0Prog`: from the return of `wc_main` (`sp` at the frame's base), a
segment to any fragment, given the `exit_group` with the status in `x0` is
matched there (`hok`). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem ret0_main_exit_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog) {n : ND}
    {Q : Frag isaLSE2} (hpc : n.pc = (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0")
    (hsp : n.o.sp = -48) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hW : ExitW W K exe endPc R F n 8)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) : SegW W K p lbl ms (At exe endPc R F n) Q :=
  exitTail_seg_ofW hp hend ret0_exitIn hpc hK hF hR hal hlo hhi (by rw [hsp]; decide) (by rw [hsp]; decide) hW
    hok

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`ret0Prog`: from the return of `wc_main` (`sp` at the frame's base), a
segment to any fragment, given the `exit_group` with the status in `x0` is
matched there (`hok`). -/
theorem ret0_main_exit_seg (hp : Lays exe ret0Prog) (hend : endPc = endOf exe ret0Prog) {n : ND}
    {Q : Frag isaLSE2} (hpc : n.pc = (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp0")
    (hsp : n.o.sp = -48) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hok : ∀ s c σ0, n.J σ0 c →
      At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun σ _ => σ.regs.X0 = σ0.regs.X0⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) : Seg p lbl ms (At exe endPc R F n) Q :=
  (ret0_main_exit_segW hp hend hpc hsp hK hF hR hal hlo hhi ExitW.triv hok).toSeg

end Ret0

/-! ## `wc_main`'s body -/

/-- `let y = x + 2` with `x = 40`: the add and its overflow check. -/
def wcAdd : List Directive := parseAArch64("movz x9, #40
movz x10, #2
adds x9, x9, x10
b.hs .L18_wc_main.abort_overflow")

block_spec wcAdd (-32) 0 (⟨-32, []⟩ : SO) wcAdd

/-- `ret y`: `y` spilled to its slot, then the return block. -/
def wcRet : List Directive := spStr .X9 0 :: retBlk 32 [.slot 0]

/-- `wcRet` is the parser's form of the listing. -/
example : wcRet = parseAArch64("str x9, [sp]
ldr x0, [sp]
ldr x29, [sp, #16]
ldr x30, [sp, #24]
add sp, sp, #32
ret") := by decide

/-- The return is covered. -/
theorem wcRet_ok : okBlk (-32) 0 ⟨-32, []⟩ wcRet = true := by decide


/-- **`wc_main`'s body in `prog`**: the add at `.0_entry`, the return after it. -/
def wcBodyIn (prog : List Directive) : Bool :=
  blockAt prog ".L18_wc_main.0_entry" 0 wcAdd && blockAt prog ".L18_wc_main.0_entry" 4 wcRet

/-- The body's check on `ret0Prog`. -/
theorem ret0_wcBodyIn : wcBodyIn SccCode.ret0Prog = true := by decide +kernel

/-- A block's run: its first directive's step, then the rest. -/
theorem arun_cons (lab : Label → Int64) (d : Directive) (ds : List Directive) (am : AM) :
    arun lab (d :: ds) am = arun lab ds (dstep lab am d) := rfl

/-- `str x9, [sp]` in a frame of 32. -/
theorem dstep_spStr0 (lab : Label → Int64) (pc : Int64) (σ : AS) :
    dstep lab ⟨pc, ⟨-32, []⟩, σ⟩ (spStr .X9 0) =
      ⟨pc + 4, ⟨-(32 : Int64).toInt, []⟩, { σ with slot := Spike.Lib.upd σ.slot (-32) σ.regs.X9.toBitVec }⟩ := by
  simp [spStr, dstep, classify, RegOnly, AI.so, AI.step, AI.tgt, SO.write, SO.get, SO.set, lk, regDst, zrB, soReg,
    Reg64s.getRegOrZr_X]

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- The body's entry offsets are below the prologue's exit offsets. -/
theorem wcBody_le : SO.le ⟨-32, []⟩ (oFr 32) = true := by decide

/-- `wc_main`'s node at the return block (`y = 42` in `x9`). -/
def wcN4 (lab : Label → Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨lab ".L18_wc_main.0_entry" + 4 + 4 + 4 + 4, ⟨-32, []⟩, fun σ c => ∃ σ0, J σ0 c ∧
    σ.slot = σ0.slot ∧ σ.regs.X9.toBitVec = 42#64⟩

/-- **`wc_main`'s body's states inside `W`**, none moved by `K`: the add's
block and the return's. -/
structure WcBodyW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Spike.Lib.Region) (F : MachineData → Prop) (J : AS → Ctl → Prop) : Prop where
  w0 : BlkW W K exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_main.0_entry", ⟨-32, []⟩, J⟩ wcAdd
  w1 : BlkW W K exe endPc R F (wcN4 (_root_.Executable.labels exe).label J) wcRet

/-- The body is inside the trivial predicate, with no outside moves. -/
theorem WcBodyW.triv {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {J : AS → Ctl → Prop} : WcBodyW (fun _ _ => True) (fun _ _ => False) exe endPc R F J :=
  ⟨BlkW.triv, BlkW.triv⟩

/-- **`wc_main`'s body is one segment** in any valid layout of `ret0Prog`:
from `.0_entry` (`sp` at the frame's base) the add does not overflow,
`y = 42` is stored in its slot, and the return reaches the saved return
address with `x0 = 42`, `x29`/`x30` restored and `sp` back at offset 0. Its states lie in `W`, none moved by `K`
(`hW`, `WcBodyW`). -/
theorem ret0_wc_body_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : WcBodyW W K exe endPc R F J) (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot (-8)))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, σ'.slot = Spike.Lib.upd σ.slot (-32) 42#64 → σ'.regs.X0.toBitVec = 42#64 →
      σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) → x.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_main.0_entry", ⟨-32, []⟩, J⟩)
      (At exe endPc R F x) := by
  have hin := ret0_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  let lab := (_root_.Executable.labels exe).label
  let n4 : ND := ⟨lab ".L18_wc_main.0_entry" + 4 + 4 + 4 + 4, ⟨-32, []⟩, fun σ c => ∃ σ0, J σ0 c ∧
    σ.slot = σ0.slot ∧ σ.regs.X9.toBitVec = 42#64⟩
  have one : ∀ {P : Frag isaLSE2} {n : ND},
      SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW W K p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.seq (Q := At exe endPc R F n4) ?_ ?_
  · refine one (seg_ndW (by simp [wcAdd]) wcAdd_ok hF hR hal hlo hhi (code_of hp hend hin.1 (ofNat4_zero _))
      hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, ?_⟩⟩)
    · rw [wcAdd_run]
    · rw [wcAdd_run]; rfl
    · rw [wcAdd_run]; exact ⟨rfl, rfl⟩
  · refine one (seg_ndW (n := n4) (by simp [wcRet]) wcRet_ok hF hR hal hlo hhi
      (code_of hp hend hin.2 (by simp only [ofNat4_succ, ofNat4_zero]; rfl)) hW.w1
      fun σ c ⟨σ0, hJ, hs, h9⟩ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    rw [show wcRet = spStr .X9 0 :: retBlk 32 [.slot 0] from rfl, arun_cons]
    rw [show n4.o = ⟨-32, []⟩ from rfl, dstep_spStr0]
    obtain ⟨h1, h2, h3, _, h5, h6, h7⟩ := retBlk_run (_root_.Executable.labels exe).label (n4.pc + 4)
      { σ with slot := Spike.Lib.upd σ.slot (-32) σ.regs.X9.toBitVec } (F := 32) (by decide) [.slot 0]
    have hs' : Spike.Lib.upd σ.slot (-32) σ.regs.X9.toBitVec = Spike.Lib.upd σ0.slot (-32) 42#64 := by rw [hs, h9]
    refine ⟨?_, ?_, hedge σ0 c hJ _ ?_ ?_ ?_ ?_⟩
    · rw [h1, hra σ0 c hJ]; simp [hs, Spike.Lib.upd_apply]
    · rw [ho, h2]; rfl
    · rw [h3]; exact hs'
    · have := h7 .X0 (.slot 0) (by simp [retRegs])
      refine this.trans ?_
      simp [RW.val, hs, h9, Spike.Lib.upd_apply]
    · rw [h5]; simp [hs, Spike.Lib.upd_apply]
    · rw [h6]; simp [hs, Spike.Lib.upd_apply]

/-- **`wc_main`'s body is one segment** in any valid layout of `ret0Prog`:
from `.0_entry` (`sp` at the frame's base) the add does not overflow,
`y = 42` is stored in its slot, and the return reaches the saved return
address with `x0 = 42`, `x29`/`x30` restored and `sp` back at offset 0. -/
theorem ret0_wc_body_seg (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot (-8)))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, σ'.slot = Spike.Lib.upd σ.slot (-32) 42#64 → σ'.regs.X0.toBitVec = 42#64 →
      σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) → x.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_main.0_entry", ⟨-32, []⟩, J⟩)
      (At exe endPc R F x) :=
  (ret0_wc_body_segW hp hend hF hR hal hlo hhi ho WcBodyW.triv hra hedge).toSeg

end Fn

end Spike.Lib.A64.Flow

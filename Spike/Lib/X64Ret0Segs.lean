/-
**The code-checked segments of `ret0.w` on x64**: the instances of
`Spike/Lib/X64CodeSegs.lean` for `SccCode.ret0Cells`, each check decided
once by the kernel; the x64 twin of `Spike/Lib/A64Ret0Segs.lean`.

- `ret0_start_seg` (S1): `scc_rt_start` up to its first call;
- `ret0_main_prologue_seg` (S5), `ret0_wc_prologue_seg`: the stack-checked
  prologues (frames 32 and 16, the limit at `%fs:8`);
- `ret0_main_exit_seg` (S6): from the return of `wc_main`, `exit_group`, a
  segment to any fragment;
- `ret0_wc_body_seg`: `wc_main`'s body, the overflow-checked add (the
  branch to the abort not taken) and the return of `42`.

Offsets are from `%rsp` at the function's entry; `%rbp` is at `-8` in
both frames. The limit's offset is checked against the thread control
block's layout (`#guard`).
-/
import Spike.Lib.X64CodeSegs
import Spike.Lib.X64Ret0Code
import Scc.IR.Core

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field)

set_option linter.unusedSimpArgs false

/-! ## `ret0.w` -/

section Ret0

open SccCode

-- The limit's offset is the thread control block's (`Scc.IR.Tcb.stackLimit`).
#guard Scc.IR.Tcb.stackLimit = 8

/-- `scc_rt_main`'s prologue: a frame of 32, `%rdi` stored at `-8(%rbp)`. -/
abbrev mainPro : Bool := prologueIn ret0Cells "scc_rt_main" ".Lscc_rt_main.chk" ".Lscc_rt_main.entry" 32 8
  ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)]

/-- `wc_main`'s prologue: a frame of 16. -/
abbrev wcPro : Bool := prologueIn ret0Cells "wc_main" ".Lwc_main.chk" ".Lwc_main.entry" 16 8 ".Lwc_main.stk"
  5 9 3 2 4 []

/-- `scc_rt_main`'s `exit_group` tail. -/
abbrev mainExit : Bool := exitIn ret0Cells ".Lscc_rt_main.x2" (-16) 4 4 5

#guard mainPro
#guard wcPro
#guard mainExit
#guard startIn ret0Cells

theorem ret0_mainPro : mainPro = true := by decide +kernel
theorem ret0_wcPro : wcPro = true := by decide +kernel
theorem ret0_mainExit : mainExit = true := by decide +kernel
theorem ret0_startIn : startIn ret0Cells = true := by decide +kernel

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`ret0Cells`. Its states lie in `W`, none moved by
`K` (`hW`). -/
theorem ret0_start_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {nC : ND} (hpc : nC.pc = (_root_.Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hW : XStartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) :=
  start_seg_ofW hp hend ret0_startIn hK hF hR hlo hhi hpc ho hW hedge

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`ret0Cells`. -/
theorem ret0_start_seg (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {nC : ND} (hpc : nC.pc = (_root_.Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) :=
  (ret0_start_segW hp hend hK hF hR hlo hhi hpc ho XStartW.triv hedge).toSeg

/-- **S5: `scc_rt_main`'s prologue** in any valid layout of `ret0Cells`. Its states lie in `W`, none moved by
`K` (`hW`). -/
theorem ret0_main_prologue_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.entry")
    (ho : SO.le nb.o (oF 32) = true)
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 32 8 ".Lscc_rt_main.stk"
      5 9 3 2 4 [(.rdi, -8, 4)] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 32 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4)] (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend ret0_mainPro (by decide) hF hR hlo hhi (by decide) hpc ho hW hedge

/-- **S5: `scc_rt_main`'s prologue** in any valid layout of `ret0Cells`. -/
theorem ret0_main_prologue_seg (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.entry")
    (ho : SO.le nb.o (oF 32) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 32 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4)] (xS1 σ).slot → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (ret0_main_prologue_segW hp hend hF hR hlo hhi hpc ho XProW.triv hedge).toSeg

/-- **`wc_main`'s prologue** in any valid layout of `ret0Cells`. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem ret0_wc_prologue_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_main.entry")
    (ho : SO.le nb.o (oF 16) = true)
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 16 8 ".Lwc_main.stk"
      5 9 3 2 4 [] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 16 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [] (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend ret0_wcPro (by decide) hF hR hlo hhi (by decide) hpc ho hW hedge

/-- **`wc_main`'s prologue** in any valid layout of `ret0Cells`. -/
theorem ret0_wc_prologue_seg (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_main.entry")
    (ho : SO.le nb.o (oF 16) = true)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (16 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 16 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [] (xS1 σ).slot → nb.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  (ret0_wc_prologue_segW hp hend hF hR hlo hhi hpc ho XProW.triv hedge).toSeg

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`ret0Cells`: from the return of `wc_main` (`%rbp` at `-8`, its offset alone
known), a segment to any fragment, given the `exit_group` with the status in
`%rax` is matched there (`hok`). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem ret0_main_exit_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells) {n : ND}
    {Q : Frag isa} {sp : Int} (hpc : n.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.x2")
    (hno : n.o = ⟨sp, [(.rbp, -8)]⟩) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hW : XExitW W K exe endPc R F n sp (-8) (-16) 4 4 5)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5,
      ⟨sp, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q :=
  exitTail_seg_ofW (lo := -40) (hi := 0) hp hend ret0_mainExit hpc hno hK hF hR hlo hhi (by decide) hW hok

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`ret0Cells`: from the return of `wc_main` (`%rbp` at `-8`, its offset alone
known), a segment to any fragment, given the `exit_group` with the status in
`%rax` is matched there (`hok`). -/
theorem ret0_main_exit_seg (hp : Lays exe ret0Cells) (hend : endPc = endOf exe ret0Cells) {n : ND}
    {Q : Frag isa} {sp : Int} (hpc : n.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.x2")
    (hno : n.o = ⟨sp, [(.rbp, -8)]⟩) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5,
      ⟨sp, [(.rbp, -8)]⟩, fun σ _ => σ.regs.rdi.toBitVec = σ0.regs.rax.toBitVec⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (ret0_main_exit_segW hp hend hpc hno hK hF hR hlo hhi XExitW.triv hok).toSeg

end Ret0

/-! ## `wc_main`'s body -/

/-- `let y = x + 2` with `x = 40`: the add and its overflow check. -/
def wcAdd : List (Directive × Nat) := (parse("movq $40, %rax
movq $2, %rcx
addq %rcx, %rax
jb .Lwc_main.ovf")).zip [7, 7, 3, 2]

/-- `ret y`: `y` spilled to its slot and reloaded, the frame popped, the
return. -/
def wcRet : List (Directive × Nat) := (parse("movq %rax, -8(%rbp)
movq -8(%rbp), %rax
movq %rbp, %rsp
popq %rbp
ret")).zip [4, 4, 3, 1, 1]

/-- The body's offsets: `%rsp` at the frame's base, `%rbp` at the saved
`%rbp`. -/
abbrev oB : SO := ⟨-24, [(.rbp, -8)]⟩

block_spec wcAdd (-24) 8 oB wcAdd
block_spec wcRet (-24) 8 oB wcRet

/-- **`wc_main`'s body in `cells`**: the add at `.entry`, the return after
it. -/
def wcBodyIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.entry" 0 wcAdd && blockAtB cells ".Lwc_main.entry" 19 wcRet

/-- The body's check on `ret0Cells`. -/
theorem ret0_wcBodyIn : wcBodyIn SccCode.ret0Cells = true := by decide +kernel

/-- The body's entry offsets are below the prologue's exit offsets. -/
theorem wcBody_le : SO.le oB (oF 16) = true := by decide

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- `wc_main`'s node at the return block (`y = 42` in `%rax`). -/
def wcN1 (pc : Int64) (J : AS → Ctl → Prop) : ND :=
  ⟨pc + 19, oB, fun σ c => ∃ σ0, J σ0 c ∧ σ.slot = σ0.slot ∧ σ.regs.rax.toBitVec = 42#64 ∧ σ.regs.rbp = σ0.regs.rbp⟩

/-- **`wc_main`'s body's states inside `W`**, none moved by `K`: the add's
block and the return's. -/
structure WcBodyW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64)
    (R : Region) (F : MachineData → Prop) (J : AS → Ctl → Prop) : Prop where
  w0 : BlkW W K exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, J⟩ wcAdd
  w1 : BlkW W K exe endPc R F (wcN1 ((_root_.Executable.labels exe).label ".Lwc_main.entry") J) wcRet

/-- The body is inside the trivial predicate, with no outside moves. -/
theorem WcBodyW.triv {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {J : AS → Ctl → Prop} : WcBodyW (fun _ _ => True) (fun _ _ => False) exe endPc R F J :=
  ⟨BlkW.triv, BlkW.triv⟩

/-- **`wc_main`'s body is one segment** in any valid layout of `ret0Cells`:
from `.entry` (`%rsp` at the frame's base) the add does not overflow,
`y = 42` is stored in its slot, and the return reaches the saved return
address with `%rax = 42`, `%rbp` restored and `%rsp` past the return
address (offset 8). Its states lie in `W`,
none moved by `K` (`hW`, `WcBodyW`). -/
theorem ret0_wc_body_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hW : WcBodyW W K exe endPc R F J)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, σ'.slot = upd σ.slot (-16) 42#64 → σ'.regs.rax.toBitVec = 42#64 →
      σ'.regs.rbp.toBitVec = σ.slot (-8) → σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 → x.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, J⟩)
      (At exe endPc R F x) := by
  have hin := ret0_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  let pc := (_root_.Executable.labels exe).label ".Lwc_main.entry"
  let n1 : ND := ⟨pc + 19, oB, fun σ c => ∃ σ0, J σ0 c ∧
    σ.slot = σ0.slot ∧ σ.regs.rax.toBitVec = 42#64 ∧ σ.regs.rbp = σ0.regs.rbp⟩
  have one : ∀ {P : Frag isa} {n : ND},
      SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW W K p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.seq (Q := At exe endPc R F n1) ?_ ?_
  · refine one (seg_ndW (by simp [wcAdd]) wcAdd_ok hF hR hlo hhi (code_field hp hend hin.1 (ofNat_zero' _))
      hW.w0 fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, ?_⟩⟩)
    · rw [wcAdd_run]
    · rw [wcAdd_run]; rfl
    · rw [wcAdd_run]; refine ⟨rfl, ?_, ?_⟩ <;> simp [Reg64s.set64]
  · refine one (seg_ndW (n := n1) (by simp [wcRet]) wcRet_ok hF hR hlo hhi (code_field hp hend hin.2 rfl) hW.w1
      fun σ c ⟨σ0, hJ, hs, h9, hb⟩ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, hedge σ0 c hJ _ ?_ ?_ ?_ ?_⟩⟩)
    · rw [wcRet_run, hra σ0 c hJ, hs]
    · rw [wcRet_run]; exact ho
    · rw [wcRet_run]; simp only [hs, h9]
    · rw [wcRet_run]; simp [Reg64s.set64, h9]
    · rw [wcRet_run]; simp [Reg64s.set64, hs]
    · rw [wcRet_run]; simp [Reg64s.set64, hb]

/-- **`wc_main`'s body is one segment** in any valid layout of `ret0Cells`:
from `.entry` (`%rsp` at the frame's base) the add does not overflow,
`y = 42` is stored in its slot, and the return reaches the saved return
address with `%rax = 42`, `%rbp` restored and `%rsp` past the return
address (offset 8). -/
theorem ret0_wc_body_seg (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, σ'.slot = upd σ.slot (-16) 42#64 → σ'.regs.rax.toBitVec = 42#64 →
      σ'.regs.rbp.toBitVec = σ.slot (-8) → σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 → x.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, J⟩)
      (At exe endPc R F x) :=
  (ret0_wc_body_segW hp hend hF hR hlo hhi ho WcBodyW.triv hra hedge).toSeg

end Fn

end Spike.Lib.X64.Flow

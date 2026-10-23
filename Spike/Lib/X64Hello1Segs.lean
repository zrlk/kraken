/-
**`hello1.w`'s runtime entry, prologues and `exit_group` tail** (x64) in
any valid layout of `hello1Cells` (`Spike/Lib/X64Hello1Code.lean`), inside
`W` from the start, from the checks of `Spike/Lib/X64CodeSegs.lean` decided
once on the cells (`decide +kernel`): the x64 twin of
`Spike/Lib/A64Hello1Segs.lean`.

- `hello1_start_segW`: `scc_rt_start` up to its call of `scc_rt_alloc_tcb`;
- `hello1_main_prologue_segW`, `hello1_rodata_prologue_segW`,
  `hello1_wc_prologue_segW`: the stack-checked prologues of `scc_rt_main`,
  `wc_rodata` and `wc_main` (frames 64, 32 and 80 below the saved `%rbp`,
  the limit at `%fs:8`);
- `hello1_main_exit_segW`: from the return of `wc_main` (`.x3`, the status
  spilled at `-48(%rbp)`), `exit_group`, a segment to any fragment;
- `seg_print_ofW`: `scc_rt_print` in any valid layout of cells with
  `printIn` (`hello1_print`), its write system call a given segment
  (`hsys`, as in `Scc.Cert.Rt.X64.Print.seg_print_of`: a write to the
  output is no row's, `SysOk`).

Each plain form is the `W` form inside the trivial predicate (`.toSeg`).
Offsets are from `%rsp` at the function's entry; `%rbp` is at `-8`. The
limit's offset is checked against the thread control block's layout and
`wc_main`'s spilled arguments against `Spike.Lib.X64.Flow.Hello1.CallF`
(`#guard`).
-/
import Spike.Lib.X64CodeSegs
import Spike.Lib.X64Hello1Rows
import Spike.Lib.X64Hello1CallF
import Scc.Cert.Rt.X64Print

namespace Spike.Lib.X64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field label_labelGapB)

set_option linter.unusedSimpArgs false

/-! ## `hello1.w`'s checks -/

section Hello1

open SccCode

-- The limit's offset is the thread control block's (`Scc.IR.Tcb.stackLimit`), and `wc_main`'s spills the
-- caller frame's (`Hello1.CallF.wc_main_callF`: offsets from the saved `%rbp`, here from it by `-8`).
#guard Scc.IR.Tcb.stackLimit = 8
#guard Hello1.CallF.wc_main_callF.map (·.1) = [-8, -16, -24, -32, -40]

/-- `scc_rt_main`'s prologue: a frame of 64, `%rdi` (the thread pointer)
stored at `-8(%rbp)`. -/
abbrev h1MainPro : Bool := prologueIn hello1Cells "scc_rt_main" ".Lscc_rt_main.chk" ".Lscc_rt_main.entry" 64 8
  ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)]

/-- `wc_rodata`'s prologue: a frame of 32, nothing spilled. -/
abbrev h1RodataPro : Bool := prologueIn hello1Cells "wc_rodata" ".Lwc_rodata.chk" ".Lwc_rodata.entry" 32 8
  ".Lwc_rodata.stk" 5 9 3 2 4 []

/-- `wc_main`'s prologue: a frame of 80, its argument's five words stored
at `-8(%rbp)`…`-40(%rbp)`. -/
abbrev h1WcPro : Bool := prologueIn hello1Cells "wc_main" ".Lwc_main.chk" ".Lwc_main.entry" 80 8
  ".Lwc_main.stk" 5 9 3 2 4 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)]

/-- `scc_rt_main`'s `exit_group` tail, after `wc_main` returns. -/
abbrev h1MainExit : Bool := exitIn hello1Cells ".Lscc_rt_main.x3" (-48) 4 4 5

theorem hello1_mainPro : h1MainPro = true := by decide +kernel
theorem hello1_rodataPro : h1RodataPro = true := by decide +kernel
theorem hello1_wcPro : h1WcPro = true := by decide +kernel
theorem hello1_mainExit : h1MainExit = true := by decide +kernel
theorem hello1_startIn : startIn hello1Cells = true := by decide +kernel

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`hello1Cells`. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_start_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {nC : ND} (hpc : nC.pc = (_root_.Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hW : XStartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) :=
  start_seg_ofW hp hend hello1_startIn hK hF hR hlo hhi hpc ho hW hedge

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`hello1Cells`. -/
theorem hello1_start_seg (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {nC : ND} (hpc : nC.pc = (_root_.Executable.labels exe).label startE + 7 + 34 + 2)
    (ho : SO.le nC.o oS = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", ⟨0, []⟩, J⟩)
      (At exe endPc R F nC) :=
  (hello1_start_segW hp hend hK hF hR hlo hhi hpc ho XStartW.triv hedge).toSeg

/-- **`scc_rt_main`'s prologue** in any valid layout of `hello1Cells`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_prologue_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.entry")
    (ho : SO.le nb.o (oF 64) = true)
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 64 8
      ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 64 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4)] (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend hello1_mainPro (by decide) hF hR hlo hhi (by decide) hpc ho hW hedge

/-- **`wc_rodata`'s prologue** in any valid layout of `hello1Cells`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_rodata_prologue_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_rodata.entry")
    (ho : SO.le nb.o (oF 32) = true)
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 32 8
      ".Lwc_rodata.stk" 5 9 3 2 4 [] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 32 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [] (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend hello1_rodataPro (by decide) hF hR hlo hhi (by decide) hpc ho hW hedge

/-- **`wc_main`'s prologue** in any valid layout of `hello1Cells`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_wc_prologue_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -88) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".Lwc_main.entry")
    (ho : SO.le nb.o (oF 80) = true)
    (hW : XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 80 8
      ".Lwc_main.stk" 5 9 3 2 4 [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (80 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = xFrRegs 80 (v.setWidth 64) σ.regs →
          σ'.slot = xStSlots σ'.regs [(.rdi, -8, 4), (.rsi, -16, 4), (.rdx, -24, 4), (.rcx, -32, 4), (.r8, -40, 4)]
            (xS1 σ).slot → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend hello1_wcPro (by decide) hF hR hlo hhi (by decide) hpc ho hW hedge

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`hello1Cells`: from the return of `wc_main` (`%rbp` at `-8`, its offset
alone known), a segment to any fragment, given the `exit_group` with the
status in `%rax` is matched there (`hok`). Its states lie in `W`, none
moved by `K` (`hW`). -/
theorem hello1_main_exit_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells) {n : ND}
    {Q : Frag isa} {sp : Int} (hpc : n.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.x3")
    (hno : n.o = ⟨sp, [(.rbp, -8)]⟩) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    (hW : XExitW W K exe endPc R F n sp (-8) (-48) 4 4 5)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5,
      ⟨sp, [(.rbp, -8)]⟩, fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    SegW W K p lbl ms (At exe endPc R F n) Q :=
  exitTail_seg_ofW (lo := -72) (hi := 0) hp hend hello1_mainExit hpc hno hK hF hR hlo hhi (by decide) hW
    fun s c σ0 hJ ⟨he, hn, hdc, hpc, σ, hA, hD, _⟩ => hok s c σ0 hJ ⟨he, hn, hdc, hpc, σ, hA, hD, trivial⟩

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`hello1Cells` (`hello1_main_exit_segW` inside the trivial predicate). -/
theorem hello1_main_exit_seg (hp : Lays exe hello1Cells) (hend : endPc = endOf exe hello1Cells) {n : ND}
    {Q : Frag isa} {sp : Int} (hpc : n.pc = (_root_.Executable.labels exe).label ".Lscc_rt_main.x3")
    (hno : n.o = ⟨sp, [(.rbp, -8)]⟩) (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -72) (hhi : 0 ≤ R.hi)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5,
      ⟨sp, [(.rbp, -8)]⟩, fun _ _ => True⟩ s c → SysOk p ms s c (.exitGroup σ0.regs.rax.toNat)) :
    Seg p lbl ms (At exe endPc R F n) Q :=
  (hello1_main_exit_segW hp hend hpc hno hK hF hR hlo hhi XExitW.triv hok).toSeg

end Hello1

/-! ## `scc_rt_print` -/

section Print

open Scc.Cert.Rt.X64.Print (printIn off0)
open Spike.Lib.X64.Print

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {c0 : Ctl} {rbp0 ra : BitVec 64}

/-- **`scc_rt_print` is one segment inside `W`** in any valid layout `exe`
of cells `cells` with `printIn cells = true` (`hello1_print` for
`hello1Cells`), for any frame condition `F` no write inside its region
breaks, given its write system call as a segment inside `W` (`hsys`, the
given node of `Scc.Cert.Rt.X64.Print.seg_print_of`); its block nodes'
states lie in `W`, none moved by `K` (`hW`). `seg_print_of` with
`seg_printW`. -/
theorem seg_print_ofW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)}
    (hp : Lays exe cells) (hend : endPc = endOf exe cells) (hprog : printIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi)
    (hW : PrintW c0 rbp0 ra W K exe endPc R F)
    (hsys : SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .sys))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 rbp0 ra .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label c0 rbp0 ra x) s c) := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, hgap⟩ := hprog
  refine seg_printW hF hR hlo hhi ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [label_labelGapB hp hgap]; rfl) hW hsys
  · exact code_field hp hend h0 (off0 _)
  · exact code_field hp hend h1 (off0 _)
  · exact code_field hp hend h2 (off0 _)
  · exact code_field hp hend h3 rfl
  · exact code_field hp hend h4 (off0 _)
  · exact code_field hp hend h5 rfl
  · exact code_field hp hend h6 rfl
  · exact code_field hp hend h7 (off0 _)
  · exact code_field hp hend h8 rfl
  · exact code_field hp hend h9 (off0 _)
  · exact code_field hp hend h10 rfl
  · exact code_field hp hend h11 (off0 _)
  · exact code_field hp hend h12 (off0 _)
  · exact code_field hp hend h13 (off0 _)
  · exact code_field hp hend hs rfl

end Print

end Spike.Lib.X64.Flow

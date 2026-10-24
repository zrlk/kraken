/-
**`hello1.w`'s runtime entry, prologues and `exit_group` tail** (AArch64)
in any valid layout of `hello1Prog` (`Spike/Lib/A64Hello1Code.lean`), inside
`W` from the start, from the checks of `Spike/Lib/A64CodeSegs.lean` decided
once on the program (`decide +kernel`):

- `hello1_start_segW`: `scc_rt_start` up to its call of `scc_rt_alloc_tcb`;
- `hello1_main_prologue_segW`, `hello1_rodata_prologue_segW`,
  `hello1_wc_prologue_segW`: the stack-checked prologues of `scc_rt_main`,
  `wc_rodata` and `wc_main` (frames 80, 48 and 96, the limit at
  `[tpidr_el0, #8]`);
- `hello1_main_exit_segW`: from the return of `wc_main` (`.sp1`, the status
  spilled at 40), `exit_group`, a segment to any fragment;
- `seg_print_ofW`: `scc_rt_print` in any valid layout of a program with
  `printIn` (`hello1_print`), its write system call a given segment (a
  write to the output is no row's: `SysOk`).

Each plain form is the `W` form inside the trivial predicate (`.toSeg`).
The limit's offset and the frames are checked against the thread control
block's layout and the placement data (`#guard`).
-/
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64Hello1Rows
import Spike.Lib.A64Hello1Place
import Scc.Cert.Rt.A64Print

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt label_labelGap)

set_option linter.unusedSimpArgs false

/-! ## `hello1.w`'s checks -/

section Hello1

open SccCode

-- The limit's offset is the thread control block's (`Scc.IR.Tcb.stackLimit`), and `wc_main`'s frame
-- the placement data's: its five IR registers at the frame's base.
#guard Scc.IR.Tcb.stackLimit = 8
#guard SccPlace.hello1.wc_main_rs "a.0" = some (-96)
#guard SccPlace.hello1.wc_main_rs "a.4" = some (-64)

/-- `scc_rt_main`'s prologue: frame 80, `x0` (the thread pointer) at 0. -/
abbrev h1MainPro : Bool := prologueIn hello1Prog "scc_rt_main" ".L1_scc_rt_main.stack_check"
  ".L1_scc_rt_main.0_entry" 80 8 ".L1_scc_rt_main.stack_grow" [(.X0, 0)]

/-- `wc_rodata`'s prologue: frame 48, nothing spilled. -/
abbrev h1RodataPro : Bool := prologueIn hello1Prog "wc_rodata" ".L18_wc_rodata.stack_check"
  ".L18_wc_rodata.0_entry" 48 8 ".L18_wc_rodata.stack_grow" []

/-- `wc_main`'s prologue: frame 96, its argument's five words at 0–32. -/
abbrev h1WcPro : Bool := prologueIn hello1Prog "wc_main" ".L19_wc_main.stack_check" ".L19_wc_main.0_entry" 96 8
  ".L19_wc_main.stack_grow" [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)]

theorem hello1_mainPro : h1MainPro = true := by decide +kernel
theorem hello1_rodataPro : h1RodataPro = true := by decide +kernel
theorem hello1_wcPro : h1WcPro = true := by decide +kernel
theorem hello1_exitIn : exitIn hello1Prog ".L1_scc_rt_main.sp1" 40 = true := by decide +kernel
theorem hello1_startIn : startIn hello1Prog = true := by decide +kernel

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`hello1Prog`. Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_start_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + Int64.ofNat (4 * 9))
    (ho : SO.le nC.o Abort.oI = true)
    (hW : StartW W K exe endPc R F J)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩)
      (At exe endPc R F nC) :=
  start_seg_ofW hp hend hello1_startIn hK hF hR hal hlo hhi hpc ho hW hedge

/-- **S1: `scc_rt_start` up to its first call** in any valid layout of
`hello1Prog`. -/
theorem hello1_start_seg (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : AS → Ctl → Prop} {nC : ND}
    (hpc : nC.pc = (_root_.Executable.labels exe).label startE + Int64.ofNat (4 * 9))
    (ho : SO.le nC.o Abort.oI = true)
    (hedge : ∀ σ c, J σ c → nC.J (startS (_root_.Executable.labels exe).label σ) c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_start", Abort.oE, J⟩)
      (At exe endPc R F nC) :=
  (hello1_start_segW hp hend hK hF hR hal hlo hhi hpc ho StartW.triv hedge).toSeg

/-- **`scc_rt_main`'s prologue** in any valid layout of `hello1Prog`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_prologue_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L1_scc_rt_main.0_entry")
    (ho : SO.le nb.o (oFr 80) = true)
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "scc_rt_main") 80 8
      ".L1_scc_rt_main.stack_grow" [(.X0, 0)] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (80 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 80 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 80 σ.regs }).regs →
          σ'.slot = stSlots (-(80 : Int64).toInt) σ'.regs [(.X0, 0)] (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend hello1_mainPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hW hedge

/-- **`wc_rodata`'s prologue** in any valid layout of `hello1Prog`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_rodata_prologue_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L18_wc_rodata.0_entry")
    (ho : SO.le nb.o (oFr 48) = true)
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_rodata") 48 8
      ".L18_wc_rodata.stack_grow" [] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (48 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 48 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 48 σ.regs }).regs →
          σ'.slot = stSlots (-(48 : Int64).toInt) σ'.regs [] (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_rodata", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend hello1_rodataPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hW hedge

/-- **`wc_main`'s prologue** in any valid layout of `hello1Prog`. Its
states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_wc_prologue_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog)
    {J : AS → Ctl → Prop} {nb : ND} (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi)
    (hpc : nb.pc = (_root_.Executable.labels exe).label ".L19_wc_main.0_entry")
    (ho : SO.le nb.o (oFr 96) = true)
    (hW : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") 96 8
      ".L19_wc_main.stack_grow" [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)] J)
    (hedge : ∀ σ c, J σ c →
      ms.rt (tcbA σ.regs 8).toNat ∧ ms.mp ⟨tcbA σ.regs 8, 8⟩ false ∧
      (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA σ.regs 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (96 : Int64).toBitVec).toNat ∧
        ∀ σ' : AS, σ'.regs = frRegs 96 (ldStep .X10 (v.setWidth 64) { σ with regs := chkRegs 96 σ.regs }).regs →
          σ'.slot = stSlots (-(96 : Int64).toInt) σ'.regs [(.X0, 0), (.X1, 8), (.X2, 16), (.X3, 24), (.X4, 32)]
            (frSlot σ) → nb.J σ' c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (At exe endPc R F nb) :=
  prologue_seg_ofW hp hend hello1_wcPro (by decide) (by decide) hF hR hal hlo hhi (by decide) hpc ho hW hedge

/-- **S6: `scc_rt_main`'s `exit_group` tail** in any valid layout of
`hello1Prog`: from the return of `wc_main` (`sp` at the frame's base), a
segment to any fragment, given the `exit_group` with the status in `x0` is
matched there (`hok`). Its states lie in `W`, none moved by `K` (`hW`). -/
theorem hello1_main_exit_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe hello1Prog) (hend : endPc = endOf exe hello1Prog) {n : ND}
    {Q : Frag isaLSE2} (hpc : n.pc = (_root_.Executable.labels exe).label ".L1_scc_rt_main.sp1")
    (hsp : n.o.sp = -80) (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hW : ExitW W K exe endPc R F n 40)
    (hok : ∀ s c σ0, n.J σ0 c → At exe endPc R F ⟨n.pc + 4 + 4 + 4, ⟨n.o.sp, []⟩, fun _ _ => True⟩ s c →
      SysOk p ms s c (.exitGroup σ0.regs.X0.toNat)) : SegW W K p lbl ms (At exe endPc R F n) Q :=
  exitTail_seg_ofW hp hend hello1_exitIn hpc hK hF hR hal hlo hhi (by rw [hsp]; decide) (by rw [hsp]; decide) hW
    fun s c σ0 hJ ⟨he, hn, hdc, hpc, σ, hA, hD, _⟩ => hok s c σ0 hJ ⟨he, hn, hdc, hpc, σ, hA, hD, trivial⟩

end Hello1

/-! ## `scc_rt_print` -/

section Print

open Scc.Cert.Rt.A64.Print (printIn code_field add4 add0)
open Spike.Lib.A64.Print

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {c0 : Ctl} {x29 ra : BitVec 64}

/-- **`scc_rt_print` is one segment inside `W`** in any valid layout `exe`
of a program `prog` with `printIn prog = true` (`hello1_print` for
`hello1Prog`), given its write system call as a segment inside `W`
(`hsvc`); its block nodes' states lie in `W`, none moved by `K` (`hW`).
`Scc.Cert.Rt.A64.Print.seg_print_of` with `seg_printW`. -/
theorem seg_print_ofW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hW : PrintW c0 x29 ra W K exe endPc R F)
    (hsvc : SegW W K p lbl ms
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .svc))
      (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .n5))) :
    SegW W K p lbl ms (At exe endPc R F (N (_root_.Executable.labels exe).label c0 x29 ra .e))
      (fun s c => ∃ x, At exe endPc R F (E (_root_.Executable.labels exe).label c0 x29 ra x) s c) := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hgap⟩ := hprog
  refine seg_printW hF hR hal hlo hhi ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [label_labelGap hp hgap]; simp only [add4, add0]) hW hsvc
  · exact code_field hp hend h0 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h1 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h2 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h3 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h4 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h5 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h6 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h7 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h8 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h9 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h10 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h11 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h12 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h13 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h14 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h15 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend hs (by simp only [N, pcSvc, add4, add0])

end Print

end Spike.Lib.A64.Flow

/-
**`ZXObl` at `X := AbX μ lab`** (row 5i-hab1, AArch64; the landing twin of
`A64HelloAbOblZ.zObl_abX`): the worker's abort facts at the two landings off the nodes of the spawned child's run
(`SegRP.WcXObl`), so that `SegRP.seg_childPPXc` lands in `XHF ∧ AbX μ lab` (`ZXObl.and`).

Both landings are at fixed pcs, and the facts are read off the pc and the instruction there only (no register,
no frame condition), as `AbObl.nodeW_abX`:

- `hXR`, `print`'s return landing: the pc is `print`'s return address, `wc_worker`'s `.0_entry` 21 instructions
  on (`Body.wkE_X30`), which is `.L20_wc_worker.sp4` (decided at helloProg's code labels); its cell is
  `movz x9, #1` (`HelloTail.b0`, `Wk.tailCode`).
- `hXE`, `wc_worker`'s return landing: the pc is the return address `ra`, the thread worker's `.sp0`
  (`ZXObl.hwcX`'s `hra`); its cell is `mrs x9, tpidr_el0` (`HThrTail.b0`, `thrCode`).

At each: a single cell without an event stepping 4 bytes on (`exec_movz`, `exec_mrs`), its next pc off the write
abort's pcs (`abSiHC`, decided), its pc off the exits and the transfer sites (`PcOffA`, from `tlRuns`/`thrRuns`).

- `abX_cell`: `AbX` at a state at a single cell without an event, given those three facts.
- `abX_sp4`, `abX_thrSp0`: `AbX` at every state of `exe` at `.L20_wc_worker.sp4` and at the thread worker's
  `.sp0`.
- `wcRet_sp4`: `print`'s return address from `wc_worker`'s call is `.L20_wc_worker.sp4`.
- `zXObl_abX`: `ZXObl (AbX μ lab)`.

Deviation from `zObl_abX`'s node lemmas: a landing is not a node (no `NodeZA`/`NodeW`, no region), so the cell's
facts are taken at the state directly.
-/
import Spike.Lib.A64HelloAbOblZ
import Spike.Lib.A64HelloWorkerSegRPX

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt exec_movz exec_mrs)
open Scc.Sem (Marks TreeLeaf)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib (Region FragS)
open Spike.Lib.A64.Flow (AS At ofNat4_succ ofNat4_zero)
open Spike.Lib.A64.Flow.Worker.Hello.SegRP (ZXObl WcXObl)
open Spike.Lib.A64WakeOff (PcOffA pcOffA_add)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open Spike.Lib.LowerA64 (labC)
open SccCode (helloProg)

/-! ## The landings' checks (decided at helloProg's code labels) -/

/-- The next pc after `.L20_wc_worker.sp4`'s first cell is off the write abort's pcs. -/
theorem landC_sp4 : abSiHC ".L20_wc_worker.sp4" 0 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-- The next pc after the thread worker's `.sp0`'s first cell is off the write abort's pcs. -/
theorem landC_thrSp0 : abSiHC (HThrTail.pfx0 ++ ".sp0") 0 = true := by
  simp only [abSiHC, ← Scc.Cert.Rt.A64.codeT_eq]; decide +kernel

/-- The labels `wcRet_sp4` reads resolve. -/
theorem wcRetLabs_chk : [".L20_wc_worker.0_entry", ".L20_wc_worker.sp4"].all
    (fun x => (codeOf Spike.Lib.A64.HelloPh.lo helloProg x).isSome) = true := by
  decide +kernel

/-- `wc_worker`'s `.0_entry` 21 instructions on is `.sp4`, at helloProg's code labels. -/
theorem wcRetC :
    labC Spike.Lib.A64.HelloPh.lo helloProg ".L20_wc_worker.0_entry" + Int64.ofNat (4 * 21) =
      labC Spike.Lib.A64.HelloPh.lo helloProg ".L20_wc_worker.sp4" := by
  decide +kernel

/-! ## A single cell at a state -/

section Cell

variable {μ : Marks} {lab : Label → Int64}

/-- **`AbX` at a state at a single cell without an event** (`nodeW_abX`'s body at a state): the cell other than an
`svc`, its every leaf 4 bytes on (`hex`, `hl`), its next pc off the write abort's pcs (`h`), its pc off the exits
and the transfer sites (`hq`). -/
theorem abX_cell (hμ : MarksL μ lab) {s : State} {c : Ctl} {fs : List TermRun.Frame} {d : Directive}
    {l : Label} {k : Nat} {tree : EvTree isaLSE2.State}
    (hq : PcOffA lab s.st.2) (hpc : s.st.2 = lab l + Int64.ofNat (4 * k)) (h : abSiH lab l k = true)
    (hc : CellAt s d 4) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) (hex : isaLSE2.exec s = some tree)
    (hl : ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat 4) : AbX μ lab s c fs := by
  simp only [abSiH, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at h
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.A64.WriteAb.Ab lab s' :=
    fun s' hs' => Spike.Lib.A64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h)
  refine AbX.of_off hμ (Spike.Lib.A64ConsumerA.AbSt.ofLeaves (pcOff_of hμ hq).noTake
    (Scc.Sem.A64.atSvc_false_of_cellAt hc hd) fun t ht => ?_) hq
  rw [hex] at ht; cases ht; exact Spike.Lib.A64Consumer.allInv_of_leaf tree hnab

end Cell

/-! ## The two landings -/

section Land

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
  (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo helloProg l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `.L20_wc_worker.sp4`**: its first cell `movz x9, #1` (`HelloTail.b0`). -/
theorem abX_sp4 {s : State} {c : Ctl} {fs : List TermRun.Frame} (hs : s.exe = exe) (hn : s.endPc = endPc)
    (hpc : s.st.2 = (_root_.Executable.labels exe).label ".L20_wc_worker.sp4") :
    AbX μ (_root_.Executable.labels exe).label s c fs := by
  have hcd := (Wk.tailCode hp hend (c0 := c) (c1 := c) (c2 := c) (A := 0) (B := 0) (x29 := 0) (ra := 0)
    (tp := 0)).sp4 s hs hn
  have hc := hcd.cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [HelloTail.N])
  have he : s.st.2 = (_root_.Executable.labels exe).label ".L20_wc_worker.sp4" + Int64.ofNat (4 * 0) := by
    rw [hpc, ofNat4_zero]
  have hq := pcOffA_add (k := 0) (runsOffA_of_chk hp tlRuns_chk) (List.Mem.head _) (Nat.le_refl 0)
    (by omega) he
  rw [ofNat4_zero] at hq
  exact abX_cell hμ hq he (abSiHC_sound hlab landC_sp4) hc nofun (exec_movz hc) fun s' hs' => by cases hs'; rfl

/-- **`AbX` at the thread worker's `.sp0`**: its first cell `mrs x9, tpidr_el0` (`HThrTail.b0`). -/
theorem abX_thrSp0 {s : State} {c : Ctl} {fs : List TermRun.Frame} (hs : s.exe = exe) (hn : s.endPc = endPc)
    (hpc : s.st.2 = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0")) :
    AbX μ (_root_.Executable.labels exe).label s c fs := by
  have hcd := (thrCode hp hend (c0 := c) (tp := 0)).sp0 s hs hn
  have hc := hcd.cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [HThrTail.N])
  have he : s.st.2 = (_root_.Executable.labels exe).label (HThrTail.pfx0 ++ ".sp0") + Int64.ofNat (4 * 0) := by
    rw [hpc, ofNat4_zero]
  have hq := pcOffA_add (k := 0) (runsOffA_of_chk hp thrRuns_chk) (List.Mem.head _) (Nat.le_refl 0)
    (by omega) he
  rw [ofNat4_zero] at hq
  exact abX_cell hμ hq he (abSiHC_sound hlab landC_thrSp0) hc nofun (exec_mrs hc) fun s' hs' => by cases hs'; rfl

omit hp hend hμ [Kraken.Executable.ValidLayout exe] in
/-- **`print`'s return address from `wc_worker`'s call is `.L20_wc_worker.sp4`** (`Body.wkE_X30`, `wcRetC`). -/
theorem wcRet_sp4 {J Kc : AS → Ctl → Prop} {σC : AS} {c : Ctl}
    (hJ : (Body.wCall (_root_.Executable.labels exe).label J Kc).J σC c) :
    Int64.ofBitVec σC.regs.X30.toBitVec = (_root_.Executable.labels exe).label ".L20_wc_worker.sp4" := by
  obtain ⟨⟨σ0, c0, -, rfl⟩, -⟩ := hJ
  have hl := Spike.Lib.A64.HelloWf.lab_labCH hlab wcRetLabs_chk
  rw [Body.wkC_eq, Body.wkE_X30, Spike.Lib.int64_ofBitVec_toBitVec, hl _ (by decide), hl _ (by decide)]
  exact wcRetC

/-- **`ZXObl` at `AbX`**: `print`'s return landing at `.L20_wc_worker.sp4` (`wcRet_sp4`, `abX_sp4`), and
`wc_worker`'s return landing at the thread worker's `.sp0` (`hra`, `abX_thrSp0`). -/
theorem zXObl_abX {R : Region} {F : MachineData → Prop} {w : Child.Words} {tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} :
    ZXObl (AbX μ (_root_.Executable.labels exe).label) exe endPc R F w tp w0 w1 w2 w3 w4 n m :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hra =>
    { hXR := fun _ _ _ _ _ _ _ _ _ _ σC _ _ hJ _ _ _ hA =>
        abX_sp4 hp hend hlab hμ hA.1 hA.2.1 (hA.2.2.2.1.trans (wcRet_sp4 hlab hJ))
      hXE := fun _ _ ⟨y, hA⟩ => by
        cases y
        exact abX_thrSp0 hp hend hlab hμ hA.1 hA.2.1 (hA.2.2.2.1.trans hra) }⟩

end Land

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.abX_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.abX_cell

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.zXObl_abX' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.zXObl_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.landC_sp4' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.landC_sp4

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.landC_thrSp0' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.landC_thrSp0

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcRetLabs_chk' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcRetLabs_chk

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcRetC' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcRetC

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.abX_sp4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.abX_sp4

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.abX_thrSp0' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.abX_thrSp0

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcRet_sp4' depends on axioms:
  [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.wcRet_sp4

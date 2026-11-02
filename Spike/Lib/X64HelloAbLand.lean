/-
**`AbX` at the two landings off the nodes** (x86-64; the twin of `Spike/Lib/A64HelloAbLand.lean`): `ZXObl`
(`X64HelloWorkerSegRPX`) at `X := AbX μ lab`. `print`'s return landing is at `wc_worker`'s `.x17` (the return
address the `call` pushes, the caller's cell `-96`: `wcRet_x17`), whose first cell is the load `movq -40(%rbp),
%rcx` (`HelloTail.b0`); `wc_worker`'s return landing is at the thread worker's `.x13` (`hra`), whose first cell is
the load of the thread pointer `movq %fs:…` (`HThrTail`'s `.x13`). Each is a single cell without an event, its
next pc off the write abort's pcs (decided), its pc off the exits and the transfer sites (`tlRuns`, `thrRuns`).

- `landS_x17`: the decided check at `.x17`'s first cell (`.x13`'s is `thS_x13`).
- `abX_cellD`: `AbX` at a state at a single cell without an event.
- `ld_leaf`: a load's leaves are its size on.
- `abX_x17`, `abX_x13`: `AbX` at the two landings.
- `wcRet_x17`: `print`'s return address from `wc_worker`'s call is `.x17`.
- `zXObl_abX`: `ZXObl` at `AbX`.

Unlike AArch64 (the landings at `.L20_wc_worker.sp4` and the thread worker's `.sp0`, their first cells a `movz`
and an `mrs` of `TPIDR_EL0`, 4-byte instructions, `print`'s return address in `x30`), the landings are at `.x17`
and `.x13`, their first cells a frame load and a `%fs`-relative load (sized cells, with the empty declarations at
the landing state), and `print`'s return address is the caller's cell `-96`.
-/
import Spike.Lib.X64HelloAbOblU
import Spike.Lib.X64HelloWorkerSegRPX

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt eaddr exec_load_agrees exec_load_mapped op64)
open Scc.Sem (Marks TreeLeaf)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (Region)
open Spike.Lib.X64 (AS mB ldDir fsDir agrees_of_decls)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.Worker.Hello.SegRP (ZXObl)
open Spike.Lib.X64WakeOff (PcOffA pcOffA_at)
open Spike.Lib.X64.RunsOff (runsOffA_of_chk)
open SccCode (helloCells)

/-! ## The landings' check (decided at helloCells' code labels) -/

/-- The next pc after `.Lwc_worker.x17`'s first cell (4 bytes) is off the write abort's pcs. -/
theorem landS_x17 : Spike.Lib.X64.HelloWf.siAbH ".Lwc_worker.x17" 0 4 = true := by
  simp only [Spike.Lib.X64.HelloWf.siAbH, ← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel

/-! ## A single cell at a state -/

section Cell

variable {μ : Marks} {lab : Label → Int64}

/-- **`AbX` at a state at a single cell without an event** (`cellZA_abXD`'s body at a state): the cell other than
a `syscall` (`hsys`), its every leaf `z` bytes on (`hex`, `hl`), its next pc off the write abort's pcs (`h`), its
pc off the exits and the transfer sites (`hq`). -/
theorem abX_cellD (hμ : MarksL μ lab) {s : State} {c : Ctl} {fs : List TermRun.Frame} {d : Directive} {z : Nat}
    {l : Label} {k : Nat} {tree : EvTree isa.State}
    (hq : PcOffA lab s.st.2) (hpc : s.st.2 = lab l + Int64.ofNat k)
    (h : lab l + Int64.ofNat k + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hc : CellAt s d z) (hsys : ∀ w w', d ≠ .instr (.regular w w' .syscall)) (hex : isa.exec s = some tree)
    (hl : ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) : AbX μ lab s c fs := by
  have hnab : ∀ s', TreeLeaf tree s' → ¬ Spike.Lib.X64.WriteAb.Ab lab s' :=
    fun s' hs' => Spike.Lib.X64.WriteAb.not_ab_of_pc (by rw [hl s' hs', hpc]; exact h)
  refine AbX.of_off hμ (Spike.Lib.X64ConsumerA.AbSt.ofLeaves (pcOff_of hμ hq).noTake
    (Scc.Sem.X64.atSyscall_false_of_cellAt hc hsys) fun t ht => ?_) hq
  rw [hex] at ht; cases ht; exact Spike.Lib.X64Consumer.allInv_of_leaf tree hnab

/-- **A load's leaves are `z` bytes on.** -/
theorem ld_leaf {s : State} {z : Nat} {b r : Reg64} {k : Int64} (hc : CellAt s (ldDir b k r) z)
    (hd : s.decls = {}) :
    ∃ tree, isa.exec s = some tree ∧ ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z := by
  cases hm : Mem.loadInt s.st.1.dmem (eaddr s z (mB b k)) 8 with
  | none =>
    refine ⟨_, exec_load_agrees hc rfl hm (agrees_of_decls hd _ _), fun s' hs' => ?_⟩
    obtain ⟨_, rfl⟩ := hs'
    rfl
  | some j =>
    refine ⟨_, exec_load_mapped hc rfl hm, fun s' hs' => ?_⟩
    cases hs'
    rfl

end Cell

/-! ## The two landings -/

section Land

variable {μ : Marks} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
variable (hp : Lays exe helloCells kp) (hend : endPc = endOf exe helloCells kp)
  (hlab : ∀ l x, Scc.Sem.X64.codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some x →
    (_root_.Executable.labels exe).label l = Int64.ofNat x)
  (hμ : MarksL μ (_root_.Executable.labels exe).label)
include hp hend hlab hμ

/-- **`AbX` at `.Lwc_worker.x17`**: its first cell `movq -40(%rbp), %rcx` (`HelloTail.b0`). -/
theorem abX_x17 {s : State} {c : Ctl} {fs : List TermRun.Frame} (hs : s.exe = exe) (hn : s.endPc = endPc)
    (hd : s.decls = {}) (hpc : s.st.2 = (_root_.Executable.labels exe).label ".Lwc_worker.x17") :
    AbX μ (_root_.Executable.labels exe).label s c fs := by
  have hcd := (Labels.wkTailCode hp hend (c0 := c) (c1 := c) (c2 := c) (A := 0) (B := 0) (rbp0 := 0) (ra := 0)
    (tp := 0) (sp := 0)).e s hs hn
  have he : s.st.2 = (_root_.Executable.labels exe).label ".Lwc_worker.x17" + Int64.ofNat 0 :=
    hpc.trans (ofNat_zero' _).symm
  have hc : CellAt s (ldDir .rbp (-40) .rcx) 4 := hcd.cell (j := 0) (by decide) rfl rfl he
  have hq := pcOffA_at (runsOffA_of_chk hp tlRuns_chk) (List.Mem.head _) (Nat.le_refl 0) (by decide) he
  obtain ⟨tree, hex, hl⟩ := ld_leaf hc hd
  exact abX_cellD hμ hq he (Spike.Lib.X64.HelloWf.siAbH_sound hlab landS_x17) hc
    (fun w w' h => by unfold ldDir Spike.Lib.X64.AI.toDir op64 at h; cases h) hex hl

/-- **`AbX` at the thread worker's `.x13`**: its first cell, the load of the thread pointer (`HThrTail`'s
`.x13`, `movfs_leaf`). -/
theorem abX_x13 {s : State} {c : Ctl} {fs : List TermRun.Frame} (hs : s.exe = exe) (hn : s.endPc = endPc)
    (hd : s.decls = {}) (hpc : s.st.2 = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13") :
    AbX μ (_root_.Executable.labels exe).label s c fs := by
  have hcd := (thrCode hp hend (c0 := c) (tp := 0) (sp := 0)).x13 s hs hn
  have he : s.st.2 = (_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x13" + Int64.ofNat 0 :=
    hpc.trans (ofNat_zero' _).symm
  have hc := hcd.cell0 rfl rfl hpc
  have hq := pcOffA_at (runsOffA_of_chk hp thrRuns_chk) (List.Mem.head _) (Nat.le_refl 0) (by decide) he
  obtain ⟨tree, hex, hl⟩ := movfs_leaf hc hd
  exact abX_cellD hμ hq he (Spike.Lib.X64.HelloWf.siAbH_sound hlab thS_x13) hc
    (fun w w' h => by unfold fsDir op64 at h; cases h) hex hl

omit hend hlab hμ in
/-- **`print`'s return address from `wc_worker`'s call is `.Lwc_worker.x17`** (`Body.wkC_ra`, `Wk.hgap`). -/
theorem wcRet_x17 {J Kc : AS → Ctl → Prop} {σC : AS} {c : Ctl}
    (hJ : (Body.wCall (_root_.Executable.labels exe).label J Kc).J σC c) :
    Int64.ofBitVec (σC.slot (-96)) = (_root_.Executable.labels exe).label ".Lwc_worker.x17" := by
  obtain ⟨⟨σ0, c0, fl, -, rfl⟩, -⟩ := hJ
  rw [Body.wkC_ra _ σ0 fl (Wk.hgap hp)]
  rfl

/-- **`ZXObl` at `AbX`**: `print`'s return landing at `.Lwc_worker.x17` (`wcRet_x17`, `abX_x17`), and
`wc_worker`'s return landing at the thread worker's `.x13` (`hra`, `abX_x13`). -/
theorem zXObl_abX {R : Region} {F : MachineData → Prop} {w : Child.Words} {tp : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} :
    ZXObl (AbX μ (_root_.Executable.labels exe).label) exe endPc R F w tp w0 w1 w2 w3 w4 n m :=
  ⟨fun _ _ _ _ _ _ _ _ _ hra =>
    { hXR := fun _ _ _ _ _ _ _ _ _ σC _ _ hJ _ _ _ hA =>
        abX_x17 hp hend hlab hμ hA.1 hA.2.1 hA.2.2.1 (hA.2.2.2.1.trans (wcRet_x17 hp hJ))
      hXE := fun _ _ ⟨y, hA⟩ => by
        cases y
        exact abX_x13 hp hend hlab hμ hA.1 hA.2.1 hA.2.2.1 (hA.2.2.2.1.trans hra) }⟩

end Land

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.landS_x17'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.landS_x17

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abX_cellD'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abX_cellD

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.ld_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.ld_leaf

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abX_x17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abX_x17

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abX_x13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abX_x13

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRet_x17'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.wcRet_x17

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.zXObl_abX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.zXObl_abX

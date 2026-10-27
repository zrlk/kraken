/-
**The write abort path's obligations inside `SFactsA`** (AArch64): the
`Abort.Disp.StubWW` of a jump to `scc_rt_abort` with `x0 = 4`
(`Spike/Lib/A64AbortWriteW.lean`) at `W := SFactsA … frs Dt (WriteAb.Ab lab)`
with the write abort phase (`Spike/Lib/A64WriteAb.lean`), for any program
with the abort code (`Scc.Cert.Rt.A64.Abort.abortIn`), an instance's facts at
the frames `frs` (`InstOk` at `own · frs`, `Spike/Lib/Rt/A64RtW.lean`) and the
path's phase check (`abortPhWriteOk`, `Spike/Lib/A64AbortPhW.lean`).

The source control `c0` is `print`'s jump to the abort after its refused
`write`: unlike the heap path's allocation it is not stuck, so the facts the
path needs at every frame run from it are given (`RefCtl`).

* `RefCtl`: the facts of `c0` the path needs (not a `ret` at the outermost
  frame, its loads and stores one cell, placed at every memory of the frame
  condition, frame runs from and into it keeping the owned words, its
  allocations passing the zero check);
* `sfactsA_doneW`, `sfactsA_svcW`: `SFactsA` in the phase `Ab` at an
  instruction without an event off the sites, and at `svc #0` with the abort
  facts and the write tail given;
* `ab_dispE`, `ab_dispT`, `d0_x0`, `t_run` and the `mem*` lemmas: the
  path's states in `WriteAb.Ab`;
* `blkW_writeA`, `nodeW_si_writeA`: a block and a single instruction of the
  path (as `blkW_heapA`, `nodeW_si_heapA`, `Spike/Lib/A64StubHA.lean`), each
  state in the phase (`hAb`);
* `stubWW_sfactsA`: `StubWW` inside `SFactsA … frs Dt (WriteAb.Ab lab)`, the
  write tail `Dt` holding at the stub's `write` (`hwr`), the exit call the
  write abort site.
-/
import Spike.Lib.A64AbortPhW
import Spike.Lib.A64AbortStubCode
import Spike.Lib.A64SegInstA
import Spike.Lib.A64WriteAb

namespace Spike.Lib.A64.StubW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi atSvc_of_cellAt atSvc_false_of_cellAt mem_certSuccs_svc)
open Spike.Lib.Consumer1 (allInv_true OneCellTy)
open Spike.Lib.A64Consumer
open Spike.Lib.A64ConsumerS (OwnS PlacedS)
open Spike.Lib.A64ConsumerA
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (StackOff stackOff_stable)
open Spike.Lib.A64.Rt (InstOk owned_off)
open Scc.Cert.Rt.A64 (blockAt)
open Scc.Cert.Rt.A64.Print (add4 add0)

/-! ## The control at the jump to the abort -/

/-- **The facts of the source control of the write abort path** at the
frames `frs`: not a `ret` at the outermost frame, every load and store of a
frame run from it one cell, placed at every memory of the frame condition
`F` (`PlacedSE`: a model term of an extern needs only its frames placed),
every frame run from or into it keeping the owned words, every allocation
of a frame run from it passing the zero check. -/
structure RefCtl (Λ : Scc.Sem.Layout) (p : Prog) (own : OwnS) (lbl : Lbl) (F : MachineData → Prop) (c0 : Ctl)
    (frs : List TermRun.Frame) : Prop where
  noRet : frs = [] → ∀ a, c0.term ≠ .ret a
  cell : ∀ c' fs', FrameRun p (c0, frs) (c', fs') → ∀ x a e ty w,
    (c'.term = .let_ x (.load true a) e ∨ ∃ b, c'.term = .let_ x (.store true a b none) e) →
    TermRun.evalAt c'.env a = some (ty, [w]) → OneCellTy ty
  place : ∀ s : State, F s.st.1 → Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c0 frs
  runOut : ∀ (s : State) c' fs', FrameRun p (c0, frs) (c', fs') → own s fs' = own s frs
  runIn : ∀ (s : State) c₁ fs₁, FrameRun p (c₁, fs₁) (c0, frs) → own s frs = own s fs₁
  zero : ∀ c' fs', FrameRun p (c0, frs) (c', fs') → ∀ x a τ e, c'.term = .let_ x (.newBuf a τ) e →
    ZeroOkTy τ = true

/-! ## `SFactsA` at one state in the phase -/

section State

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS} {lbl : Lbl}
  {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame} {Dt : State → Prop} {F : MachineData → Prop}
  {Ab : State → Prop}

open Kraken.Promising.Lower.A64 (CellAt after)

/-- **`SFactsA` in the phase at an instruction without an event** (not an
`svc`, its step `.done s'`), off the marks' sites, at a control with
`RefCtl`'s facts: the leaf owns what `s` owns and is in the take phase iff
`s` is; in that phase the range is owned. -/
theorem sfactsA_doneW {s' : State} {d : Directive} {sz : Nat} (hc : RefCtl Λ p own lbl F c fs)
    (hpl : Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c fs) (hP : PcOff μ s)
    (hcl : CellAt s d sz) (hd : ∀ imm, d ≠ .instr ⟨.W64, .SVC imm⟩) (hex : isaLSE2.exec s = some (.done s'))
    (hown : own s' fs = own s fs) (htk : Tk s' ↔ Tk s) (hO : Tk s → Owned Λ rS s) (hAb : Ab s) :
    SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab := by
  have hs : abi.atSys s = false := atSvc_false_of_cellAt hcl hd
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hP.noSite
      mapped := fun _ e he => by rw [hex] at he; cases he; nofun
      place := hpl
      svc := fun h => by rw [hs] at h; cases h
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun c' fs' hr _ tree he => by
        rw [hex] at he; cases he
        refine .inl ⟨?_, trivial⟩
        show own s' fs' = own s fs'
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact hown
      ownSys := fun _ _ _ h => by rw [hs] at h; cases h
      ownTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      site := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkTake := fun a ha hpc => (hP.noTake a ha hpc).elim
      tkInstr := fun _ _ tree he => by rw [hex] at he; cases he; exact htk
      tkSys := fun h => by rw [hs] at h; cases h
      owned := hO
      wrTail := fun h => by rw [hs] at h; cases h
      wr := fun _ _ _ _ => wrOkA_of_noWr (noWr_done hex)
      zero := hc.zero
      abortOk := fun k a ha hpc => (hP.noAbort k a ha hpc).elim
      abInstr := fun hn => (hn hAb).elim
      abSys := fun hn => (hn hAb).elim
      abTake := fun hn => (hn hAb).elim }

/-- **`SFactsA` in the phase at `svc #0`** off the release and take sites,
at a control with `RefCtl`'s facts, with the write abort facts (`hab`) and
the write tail (`hwr`) given: every state the kernel resumes in is past it,
owning what `s` owns and in the take phase iff `s` is. -/
theorem sfactsA_svcW (hc : RefCtl Λ p own lbl F c fs) (hpl : Spike.Lib.A64ConsumerS.PlacedSE Λ lbl s c fs)
    (hrel : ∀ a, μ.site .release = some a → pcOf s ≠ a) (htake : ∀ a, μ.site .take = some a → pcOf s ≠ a)
    (hcl : CellAt s Spike.Lib.A64.Flow.svcDir 4)
    (hnext : ∀ m, own (after s 4 m) fs = own s fs ∧ (Tk (after s 4 m) ↔ Tk s)) (hO : Tk s → Owned Λ rS s)
    (hab : ∀ k a, μ.abortAt k = some a → pcOf s = a → (k = .writeErr ∧ Ab s) ∧
      ∀ v, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup v) →
        v % 256 = Scc.Sem.Kernel.abortStatus)
    (hwr : ∀ fd buf n, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write fd buf n) → Dt s)
    (hAb : Ab s) :
    SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c fs Dt Ab := by
  have hs : abi.atSys s = true := atSvc_of_cellAt hcl
  have hsucc : ∀ call, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      ∀ s' ∈ Scc.Sem.Kernel.certSuccs abi s call, own s' fs = own s fs ∧ (Tk s' ↔ Tk s) := by
    intro call hd s' hs'
    obtain ⟨r, -, rfl⟩ := (mem_certSuccs_svc hcl hd).1 hs'
    exact hnext _
  refine
    { noRet := hc.noRet
      cell := hc.cell
      noSite := hrel
      mapped := fun h => by rw [hs] at h; cases h
      place := hpl
      svc := fun _ => ⟨0, 4, hcl⟩
      ownRun := fun c₁ fs₁ c₂ fs₂ hr h => by
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hc.runOut s c₂ fs₂ hr
        · exact hc.runIn s c₁ fs₁ hr
      ownInstr := fun _ _ _ h => by rw [hs] at h; cases h
      ownSys := fun c' fs' hr _ call hd s' hs' => by
        rw [hc.runOut s' c' fs' hr, hc.runOut s c' fs' hr]
        exact (hsucc call hd s' hs').1
      ownTake := fun a ha hpc => (htake a ha hpc).elim
      site := fun a ha hpc => (htake a ha hpc).elim
      tkTake := fun a ha hpc => (htake a ha hpc).elim
      tkInstr := fun _ h => by rw [hs] at h; cases h
      tkSys := fun _ call hd s' hs' => (hsucc call hd s' hs').2
      owned := hO
      wrTail := fun _ => hwr
      wr := fun _ _ _ h => by rw [hs] at h; cases h
      zero := hc.zero
      abortOk := fun k a ha hpc => let ⟨h1, h2⟩ := hab k a ha hpc; ⟨.inl h1, h2⟩
      abInstr := fun hn => (hn hAb).elim
      abSys := fun hn => (hn hAb).elim
      abTake := fun hn => (hn hAb).elim }

end State

/-! ## The path's states in the phase -/

section Phase

variable {lab : Label → Int64}

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over the dispatcher's register-only and
memory prefixes. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [Flow.arun, Flow.dstep, Flow.classify, Flow.RegOnly, Flow.AI.so, Flow.AI.step, Flow.AI.tgt,
    Flow.soReg, Flow.regDst, Flow.zrB, Flow.regRes, Operation.interp, MachineData.setRegOrZr,
    MachineData.setRegOrSp, Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64,
    Reg64s.setRegOrSp, Reg64s.getRegOrSp, Reg64s.setRegOrSp64, Reg64s.getRegOrSp64, Reg64s.setXReg,
    Reg64s.getXReg, ShiftRegExpr.interp, ExtOrImmReg.interp, ConstExpr.interp, RegOrZr.base, RegOrSp.base,
    Flow.SO.get, Flow.SO.set, Flow.SO.kill, Flow.SO.write, Flow.SO.killZ, Spike.Lib.lk, Spike.Lib.rm])

/-- The dispatcher's prologue keeps `x0` before each instruction. -/
theorem d0_x0 (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < Abort.Disp.d0.length) :
    (Flow.arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.regs.X0 = σ.regs.X0 := by
  simp only [Abort.Disp.d0] at hk ⊢
  simp only [List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- A test of the dispatcher keeps the frame's offset and slots before each
instruction. -/
theorem t_run {blk : List Directive}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4)
    (pc : Int64) (σ : Flow.AS) {k : Nat} (hk : k < blk.length) :
    (Flow.arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).so.sp = -32 ∧
      (Flow.arun lab (blk.take k) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot = σ.slot := by
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4] at hk ⊢ <;>
    simp only [List.length_cons, List.length_nil] at hk <;>
    rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The word at `[sp]` from the abstract state, `sp` at the frame's `-32`. -/
theorem sp_four {R : Spike.Lib.Region} {o : SO} {s : State} {σ : Flow.AS} (hA : Flow.Abs R o s.st.1 σ) (ho : o.sp = -32)
    (hoff : R.Off (-32)) (h4 : (σ.slot (-32)).toNat = 4) : WriteAb.spLoad s 0 = some 4#64 := by
  obtain ⟨j, hj, hjv⟩ := hA.slot (-32) hoff
  have hsp := hA.so .SP o.sp rfl
  rw [← hA.regs, ho] at hsp
  simp only [Reg64s.getRegOrSp64] at hsp
  simp only [WriteAb.spLoad, Scc.Sem.A64.privLoad, hsp]
  rw [show R.addr (-32) + 0 = R.addr (-32) from BitVec.add_zero _, hj, Option.map_some, hjv]
  exact congrArg some (BitVec.eq_of_toNat_eq (by simpa using h4))

/-- A state of the dispatcher's prologue with `x0 = 4` is in the phase. -/
theorem ab_dispE {R : Spike.Lib.Region} {o : SO} {s : State} {σ : Flow.AS} (hmem : s.st.2 ∈ WriteAb.dispEPcs lab)
    (hA : Flow.Abs R o s.st.1 σ) (h4 : σ.regs.X0.toBitVec.toNat = 4) : WriteAb.Ab lab s :=
  .inr (.inr (.inr (.inl ⟨hmem, by rw [hA.regs]; exact UInt64.toNat_inj.mp (by simpa using h4)⟩)))

/-- A state of the dispatcher's tests with `4` at `[sp]` is in the phase. -/
theorem ab_dispT {R : Spike.Lib.Region} {o : SO} {s : State} {σ : Flow.AS} (hmem : s.st.2 ∈ WriteAb.dispTPcs lab)
    (hA : Flow.Abs R o s.st.1 σ) (ho : o.sp = -32) (hoff : R.Off (-32)) (h4 : (σ.slot (-32)).toNat = 4) :
    WriteAb.Ab lab s :=
  .inr (.inr (.inr (.inr (.inl ⟨hmem, sp_four hA ho hoff h4⟩))))

/-- The prologue's pcs are `dispEPcs`. -/
theorem memE {k : Nat} (hk : k < Abort.Disp.d0.length) :
    lab "scc_rt_abort" + Int64.ofNat (4 * k) ∈ WriteAb.dispEPcs lab := by
  simp only [Abort.Disp.d0, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> simp [WriteAb.dispEPcs]

/-- The four tests' pcs are `dispTPcs`. -/
theorem memT {l : Label} {blk : List Directive}
    (hl : l = ".L12_scc_rt_abort.0_entry" ∨ l = ".L12_scc_rt_abort.2_next1" ∨ l = ".L12_scc_rt_abort.4_next3" ∨
      l = ".L12_scc_rt_abort.6_next5")
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.t3 ∨ blk = Abort.Disp.t4)
    {k : Nat} (hk : k < blk.length) : lab l + Int64.ofNat (4 * k) ∈ WriteAb.dispTPcs lab := by
  have hk4 : k < 4 := by
    rcases hb with rfl | rfl | rfl | rfl <;>
      simpa only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.t3, Abort.Disp.t4, List.length_cons,
        List.length_nil] using hk
  rcases hl with rfl | rfl | rfl | rfl <;> rcases k with _|_|_|_|k <;> (try omega) <;>
    simp [WriteAb.dispTPcs]

/-- The jumps to the next test are `dispTPcs`. -/
theorem memJ {l : Label}
    (hl : l = ".L12_scc_rt_abort.0_entry" ∨ l = ".L12_scc_rt_abort.2_next1" ∨ l = ".L12_scc_rt_abort.4_next3")
    {k : Nat} (hk : k < 1) : lab l + 4 + 4 + 4 + 4 + Int64.ofNat (4 * k) ∈ WriteAb.dispTPcs lab := by
  rcases hl with rfl | rfl | rfl <;> rcases k with _|k <;> (try omega) <;>
    simp [WriteAb.dispTPcs, Int64.add_assoc]

/-- The jump to the write stub's pcs are `g4Pcs`. -/
theorem memG {k : Nat} (hk : k < Abort.Disp.g4.length) :
    lab ".L12_scc_rt_abort.7_is6" + Int64.ofNat (4 * k) ∈ WriteAb.g4Pcs lab := by
  simp only [Abort.Disp.g4, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> simp [WriteAb.g4Pcs]

/-- The write stub's prologue is in `stubPcs`. -/
theorem memB0 {k : Nat} (hk : k < Abort.b0.length) :
    lab Abort.write.fn + Int64.ofNat (4 * k) ∈ WriteAb.stubPcs lab := by
  simp only [Abort.b0, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|k <;> (try omega) <;> simp [WriteAb.stubPcs]

/-- The write stub's argument block is in `stubPcs`. -/
theorem memB1 {k : Nat} (hk : k < Abort.b1Write.length) :
    lab Abort.write.entry + 4 + 4 + Int64.ofNat (4 * k) ∈ WriteAb.stubPcs lab := by
  simp only [Abort.b1Write, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> simp [WriteAb.stubPcs, Int64.add_assoc]

/-- The write stub's block after the call is in `stubPcs`. -/
theorem memB2 {k : Nat} (hk : k < Abort.b2.length) :
    Abort.pcSvc lab Abort.write + 4 + Int64.ofNat (4 * k) ∈ WriteAb.stubPcs lab := by
  simp only [Abort.b2, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|k <;> (try omega) <;> simp [WriteAb.stubPcs, Int64.add_assoc]

/-- The write stub's system call is in `stubPcs`. -/
theorem memSvc : Abort.pcSvc lab Abort.write ∈ WriteAb.stubPcs lab := by
  simp [WriteAb.stubPcs, Int64.add_assoc]

end Phase

/-! ## The path's blocks and single instructions -/

section Nodes

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame} {R : Region} {F : MachineData → Prop} {Ab : State → Prop}

/-- **A block of the write abort path inside `SFactsA`** at the frames
`frs`: as `blkW_heapA` with the source control's facts `RefCtl` (`hc`), each
state before an instruction in the phase (`hAb`). -/
theorem blkW_writeA {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp) {n : ND}
    {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc) (hok : Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m)
    (hph : blkPh okPc ph (fun _ => false) lab (lab l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true) (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs)
    (hAb : ∀ (s : State) σ c j m, n.J σ c → j < blk.length →
      Flow.Abs R (Flow.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (Flow.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      Ab { s with st := (m, n.pc + Int64.ofNat (4 * j)) }) :
    BlkW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt Ab) K exe endPc R F n blk := by
  have hcode := code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [he, ← hI.labOk] at hph
  obtain ⟨hpc, hph', -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
  intro s σ c hs hn _ _ hA hD hJc k hk m hA' hDm
  have hab := hAb s σ c k m hJc hk hA'
  obtain rfl := hJ σ c hJc
  obtain ⟨hP, hK⟩ := hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } hs hn rfl
  refine ⟨?_, hK⟩
  obtain ⟨a, hca, haok, -⟩ := Flow.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hcell : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s hs hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hlA : labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [hs]
  obtain ⟨m', hex, -, -⟩ := Flow.exec_ai haok hR hal hlo hhi hcell hreg hA'
  rw [hlA] at hex
  obtain ⟨hown, htk⟩ := hph' σ c hJc k hk a hca { s with st := (m, n.pc + Int64.ofNat (4 * k)) }
    { s with st := (m', a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
      (Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) } hs hn hs hn rfl rfl
  exact sfactsA_doneW hc (hc.place _ (hF _ _ hD hDm)) hP hcell (AI.not_svc hreg) hex
    hown htk (fun _ => owned_off hR (by omega) hl hh hsub (stackOff_stable hfit _ _ (hFO _ hD) hDm)
      fun k' hk' => Option.isSome_iff_exists.mpr (by obtain ⟨j, hj, -⟩ := hA'.slot k' hk'; exact ⟨j, hj⟩)) hab

/-- **A single instruction without an event (`SI`) of the write abort path
inside `SFactsA`**: as `nodeW_si_heapA` with `RefCtl` (`hc`), every state at
its pc in the phase (`hAb`). -/
theorem nodeW_si_writeA {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    {n : ND} {si : SI} {l : Label} {k : Nat} {q : Int64} {c0 : Ctl} {Dt : State → Prop}
    (hb : blockAt prog l k [si.toDir] = true) (he : lab l + Int64.ofNat (4 * k) = q) (hp : n.pc = q)
    (hok : okPc q.toBitVec.toNat = true) (hph : ph (q + Int64.ofNat 4).toBitVec.toNat = ph q.toBitVec.toNat)
    (hR : R.OK) (hR8 : R.base.toNat % 8 = 0) (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0)
    (hsub : rS.Sub Λ.stackPool) (hFO : ∀ m, F m → StackOff rS R m)
    (hJ : ∀ σ c, n.J σ c → c = c0) (hc : RefCtl Λ p own lbl F c0 frs) (hAb : ∀ s : State, s.st.2 = q → Ab s) :
    NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt Ab) K exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJc⟩
  obtain rfl := hJ σ c hJc
  rw [hp] at hpc
  have hP := hI.off s (by unfold pcOf; rw [hpc]; exact hok)
  have hcell := Spike.Lib.A64.Rt.cellOf hI hb he hs hn hpc
  have hnx := Spike.Lib.A64.Rt.next_same hI hpc hph
  refine ⟨sfactsA_doneW hc (hc.place s hD) hP.1 hcell
    (by cases si <;> intro imm h <;> cases h) (exec_si hcell) (hnx _).1 (hnx _).2
    (fun _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => ?_) (hAb s hpc), hP.2⟩
  obtain ⟨j, hj, -⟩ := hA.slot k hk
  rw [hj]; rfl

end Nodes

/-! ## `StubWW` (the phase check `abortPhWriteOk` in `Spike/Lib/A64AbortPhW.lean`) -/

section Stub

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : OwnS} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : Spike.Lib.A64ConsumerS.InvS}
  {lsize : Lsize} {frs : List TermRun.Frame}
  {al : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {R : Region} {F : MachineData → Prop}

/-- **The write abort path's obligations inside `SFactsA … frs Dt
(WriteAb.Ab lab)`** (`Abort.Disp.StubWW`), for a program with the abort code
(`hprog`), an instance's facts at the frames `frs` (`hI`) and the path's
phase check (`hphs`). The callee's region holds the stub's frame (`hlo`,
`hhi`); the words of `rS` lie off it in the frame condition (`hFO`); the
source control `c0` has `RefCtl`'s facts (`hc`). The exit call is the write
abort site: off the release and take sites (`hrel`, `htk`), no other kind's
(`hk`), no outside move (`hKex`), the memory side's abort (`hms`). The write
tail `Dt` holds at the `write` (`hwr`). -/
theorem stubWW_sfactsA {kp : Nat} (hI : InstOk exe endPc prog lab μ (fun s => own s frs) Tk K okPc ph kp)
    {c0 : Ctl} {Dt : State → Prop}
    (hprog : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hphs : abortPhWriteOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hl : R.lo % 8 = 0)
    (hh : R.hi % 8 = 0) (hF : FStable R F) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hc : RefCtl Λ p own lbl F c0 frs)
    (hrel : ∀ a, μ.site .release = some a → (lab Abort.write.exit).toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.write.exit).toBitVec.toNat ≠ a)
    (hk : ∀ k a, μ.abortAt k = some a → (lab Abort.write.exit).toBitVec.toNat = a → k = .writeErr)
    (hKex : ∀ s s', pcOf s = (lab Abort.write.exit).toBitVec.toNat → ¬ K s s')
    (hms : ∀ s : State, s.exe = exe → s.st.2 = lab Abort.write.exit → ms.abortAt s)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hwr : ∀ s c, At exe endPc R F (Abort.N lab Abort.write c0 .svc) s c → Dt s) :
    Abort.Disp.StubWW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt (WriteAb.Ab lab))
      K p al ms exe endPc R F c0 := by
  have hlab := hI.labOk
  subst hlab
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hoff : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  have hsd := hprog
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst := hsd.1.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, hx, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, hj2, -, ht3, hj3, -, ht4, -, hg4, -⟩ := hdi
  simp only [abortPhWriteOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pj2, pt3, pj3, pt4, pg4, pb0, o1, q1, o1b, q1b, pb1, o7, q7, pb2, qx⟩ := hphs
  have hown : ∀ (s : State) (o : SO) σ, Flow.Abs R o s.st.1 σ → F s.st.1 → Tk s → Owned Λ rS s :=
    fun s _ σ hA hD _ => owned_off hR hR8 hl hh hsub (hFO _ hD) fun k hk => by
      obtain ⟨j, hj, -⟩ := hA.slot k hk
      rw [hj]; rfl
  have he7 : (_root_.Executable.labels exe).label Abort.write.entry + Int64.ofNat (4 * 7) =
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .svc).pc := by
    simp only [Abort.N, Abort.pcSvc, add4, add0]
  have hsvcW : NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt
      (WriteAb.Ab (_root_.Executable.labels exe).label)) K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .svc) := by
    intro s c hAt
    obtain ⟨hs, hn, -, hpc, σ, hA, hD, hJ, -, -⟩ := id hAt
    have hc0 : c = c0 := hJ
    subst hc0
    have hAb : WriteAb.Ab (_root_.Executable.labels exe).label s := WriteAb.ab_stub (by rw [hpc]; exact memSvc)
    rw [← he7] at hpc
    have hP := hI.off s (by unfold pcOf; rw [hpc]; exact o7)
    exact ⟨sfactsA_svcW hc (hc.place s hD) hP.1.noSite hP.1.noTake
      (Spike.Lib.A64.Rt.cellOf hI hsvcIn rfl hs hn hpc) (Spike.Lib.A64.Rt.next_same hI hpc q7) (hown s _ σ hA hD)
      (fun k a ha e => (hP.1.noAbort k a ha e).elim) (fun _ _ _ _ => hwr s c hAt) hAb, hP.2⟩
  have hsex : NodeW (fun s c => SFactsA Λ μ p rd G own rS Tk ar J lbl lsize s c frs Dt
      (WriteAb.Ab (_root_.Executable.labels exe).label)) K exe endPc R F
      (Abort.N (_root_.Executable.labels exe).label Abort.write c0 .ex) := by
    rintro s c ⟨hs, hn, -, hpc, σ, hA, hD, hJ, h8, h0⟩
    have hc0 : c = c0 := hJ
    subst hc0
    have hpcN : pcOf s = ((_root_.Executable.labels exe).label Abort.write.exit).toBitVec.toNat := by
      unfold pcOf; rw [hpc]; rfl
    have hAb : WriteAb.Ab (_root_.Executable.labels exe).label s :=
      WriteAb.ab_stub (by rw [hpc]; simp [Abort.N, WriteAb.stubPcs])
    have hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) =
        some (.exitGroup σ.regs.X0.toNat) := by
      rw [← svcCall_exitGroup (by rw [h8]; rfl), svcCall, ← hA.regs]; rfl
    refine ⟨sfactsA_svcW hc (hc.place s hD) (fun a ha => hpcN ▸ hrel a ha)
      (fun a ha => hpcN ▸ htk a ha) (Spike.Lib.A64.Rt.cellOf hI hx (add0 _) hs hn hpc)
      (Spike.Lib.A64.Rt.next_same hI hpc qx) (hown s _ σ hA hD)
      (fun k a ha e => ⟨⟨hk k a ha (hpcN ▸ e), hAb⟩, fun v hv => ?_⟩)
      (fun _ _ _ h => by rw [hd] at h; cases h) hAb, fun s' => hKex s s' hpcN⟩
    rw [hd] at hv
    cases hv
    rw [h0]; rfl
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 := .inr (.inr (.inr rfl))
  have hj : ∀ {j : Nat}, j < Abort.Disp.j1.length → j < 1 := fun h => h
  exact stubWW_of_code hI.lays hI.endOk hprog hK hF
    (blkW_writeA hI hd0 (by simp only [Abort.Disp.DN.nd4, add0]) Abort.Disp.d0_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pd0 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA =>
        ab_dispE (memE hk) hA ((congrArg (fun x => x.toBitVec.toNat) (d0_x0 _ _ hk)).trans hJ.2))
    (blkW_writeA hI ht1 (by simp only [Abort.Disp.DN.nd4, add0]) Abort.Disp.t1_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt1 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inl rfl) hT1 hk) hA (t_run hT1 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run hT1 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hj1 (by simp only [Abort.Disp.DN.nd4, add4, add0]) Abort.Disp.j1_ok hR hal (by omega) hhi hl
      hh hF hsub hfit hFO pj1 rfl (fun _ _ h => h.1) hc
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ab_dispT (memJ (.inl rfl) (by decide)) hA rfl hoff hJ.2)
    (blkW_writeA hI ht2 (by simp only [Abort.Disp.DN.nd4, add0]) Abort.Disp.t2_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt2 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inr (.inl rfl)) hT2 hk) hA (t_run hT2 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run hT2 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hj2 (by simp only [Abort.Disp.DN.nd4, add4, add0]) Abort.Disp.j2_ok hR hal (by omega) hhi hl
      hh hF hsub hfit hFO pj2 rfl (fun _ _ h => h.1) hc
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ab_dispT (memJ (.inr (.inl rfl)) (by decide)) hA rfl hoff hJ.2)
    (blkW_writeA hI ht3 (by simp only [Abort.Disp.DN.nd4, add0]) Abort.Disp.t3_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt3 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run hT3 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run hT3 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hj3 (by simp only [Abort.Disp.DN.nd4, add4, add0]) Abort.Disp.j3_ok hR hal (by omega) hhi hl
      hh hF hsub hfit hFO pj3 rfl (fun _ _ h => h.1) hc
      fun _ σ _ j _ hJ hk hA => by
        obtain rfl : j = 0 := by have := hj hk; omega
        exact ab_dispT (memJ (.inr (.inr rfl)) (by decide)) hA rfl hoff hJ.2)
    (blkW_writeA hI ht4 (by simp only [Abort.Disp.DN.nd4, add0]) Abort.Disp.t4_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pt4 rfl (fun _ _ h => h.1) hc
      fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inr (.inr (.inr rfl))) hT4 hk) hA (t_run hT4 _ _ hk).1 hoff
        ((congrArg (fun f => (f (-32)).toNat) (t_run hT4 _ _ hk).2).trans hJ.2))
    (blkW_writeA hI hg4 (by simp only [Abort.Disp.DN.nd4, add0]) Abort.Disp.g4_ok hR hal (by omega) hhi hl hh
      hF hsub hfit hFO pg4 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_g4 (memG hk))
    (blkW_writeA hI hb0 (by simp only [Abort.N, add0]) Abort.b0_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb0 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_stub (memB0 hk))
    (nodeW_si_writeA (si := .adrp .X9 Abort.write.msg) hI hn1 rfl (by simp only [Abort.N, add0]) o1 q1
      hR hR8 hl hh hsub hFO (fun _ _ h => h) hc
      fun _ h => WriteAb.ab_stub (by rw [h, add0]; simp [WriteAb.stubPcs]))
    (nodeW_si_writeA (si := .addLo12 .X9 .X9 Abort.write.msg) hI hn1b rfl (by simp only [Abort.N, add4, add0])
      o1b q1b hR hR8 hl hh hsub hFO (fun _ _ h => h) hc
      fun _ h => WriteAb.ab_stub (by rw [h, add4, add0]; simp [WriteAb.stubPcs]))
    (blkW_writeA hI hb1 (by simp only [Abort.N, add4, add0]) Abort.b1Write_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb1 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_stub (memB1 hk))
    hsvcW
    (blkW_writeA hI hb2 (by simp only [Abort.N, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal hlo hhi hl hh
      hF hsub hfit hFO pb2 rfl (fun _ _ h => h) hc
      fun _ _ _ _ _ _ hk _ => WriteAb.ab_stub (memB2 hk))
    hsex
    (fun s c ⟨hs, _, _, hpc, _⟩ => hms s hs hpc)

end Stub

end Spike.Lib.A64.StubW

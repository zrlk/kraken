/-
**`AbX` at every node of `print`'s write abort path** (row 5i-hab1, AArch64; P4's abort half): `AbortObl` at
`Z := AbX μ lab · · fs`. Every state of the path is in the write abort's
phase `WriteAb.Ab lab` (the dispatcher's prologue with `x0 = 4`, its tests
with `4` at `[sp]`, the jump to the stub and the stub: `A64StubWA`'s `ab_*`
and `mem*` lemmas from the nodes' invariants `Abort.Disp.DN.nd4`), where
`AbSt` is vacuous; an abort site there is `writeErr`'s: at the stub's exit
by `MarksL.k_of_wexit`, elsewhere none (the path's pcs off the exits and the
transfer sites, `hoff`, decided on the listing).

No code fact is needed: `WriteAb.Ab` reads the pc and the abstract state.

- `abortRunsX`: `abortRuns` less the exit call.
- `blkZA_abX`: `AbX` at a block node's states in the phase (`hAb`, the form
  of `StubW.blkW_writeA`'s), off the exits (`hoff`).
- `abortObl_abX`: `AbortObl (AbX μ lab · · fs)` for any source control;
  `abortObl_abXH` at hello's listing (`abortRunsX_chk`, decided).
-/
import Spike.Lib.A64HelloAbortObl
import Spike.Lib.A64HelloAbObl
import Spike.Lib.A64StubWA

namespace Spike.Lib.A64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks)
open Spike.Lib (Region)
open Spike.Lib.A64.Flow (ND NodeW At ofNat4_zero)
open Spike.Lib.A64.Flow.Worker (NodeZA AbortObl abortRuns)
open Spike.Lib.A64WakeOff (PcOffA RunsOffA pcOffA_add)
open Spike.Lib.A64.StubW (ab_dispE ab_dispT d0_x0 t_run memE memT memJ memG memB0 memB1 memB2 memSvc)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Cert.Rt.A64 (Lays)
open Spike.Lib.A64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloProg)

/-- **The abort path's pcs less the exit call** (`abortRuns`'s first
eight runs): off every exit and transfer site in hello's listing. -/
def abortRunsX : List (Label × Nat × Nat) :=
  [("scc_rt_abort", 0, 5), (".L12_scc_rt_abort.0_entry", 0, 5), (".L12_scc_rt_abort.2_next1", 0, 5),
    (".L12_scc_rt_abort.4_next3", 0, 5), (".L12_scc_rt_abort.6_next5", 0, 4), (".L12_scc_rt_abort.7_is6", 0, 4),
    ("scc_rt_abort_write", 0, 4), (".L16_scc_rt_abort_write.0_entry", 0, 11)]

section Nodes

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {fs : List TermRun.Frame}

/-- **`AbX` at a block node's states in the phase** (`hAb`), its pcs off the
exits and the transfer sites (`hoff`). -/
theorem blkZA_abX (hμ : MarksL μ (_root_.Executable.labels exe).label) {n : ND} {blk : List Directive}
    (hAb : ∀ (s : State) σ c j m, n.J σ c → j < blk.length →
      Flow.Abs R (Flow.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (Flow.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label { s with st := (m, n.pc + Int64.ofNat (4 * j)) })
    (hoff : ∀ j < blk.length, PcOffA (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * j))) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n blk :=
  fun s σ c _ _ _ _ _ _ hJ k hk m hA' _ =>
    ⟨AbX.of_ab (hAb s σ c k m hJ hk hA') fun _ a ha hpc =>
      ((pcOff_of hμ (s := { s with st := (m, n.pc + Int64.ofNat (4 * k)) }) (hoff k hk)).noAbort _ a ha hpc).elim,
      fun _ h => h⟩

/-- **`AbX` at a single node's states in the phase**, its pc off the exits
or the write exit itself (`hk`). -/
theorem nodeW_abXA {n : ND}
    (hAb : ∀ s : State, s.st.2 = n.pc → Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s)
    (hk : ∀ s : State, s.st.2 = n.pc → ∀ k a, μ.abortAt k = some a → Scc.Sem.A64.pcOf s = a → k = .writeErr) :
    NodeW (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) (fun _ _ => False) exe endPc R F n :=
  fun s _ ⟨_, _, _, hpc, _⟩ => ⟨AbX.of_ab (hAb s hpc) (hk s hpc), fun _ h => h⟩

set_option hygiene false in
/-- A pc `label l + 4 (j0 + k)` of a run of `abortRunsX` is off the exits. -/
local macro "zo " l:term:max j0:term:max hi:term:max : term =>
  `(fun k hk => pcOffA_add hoff (l := $l) (lo := 0) (hi := $hi) (c := $j0) (by simp [abortRunsX]) (by omega)
      (by simp only [List.length_cons, List.length_nil, Abort.Disp.d0, Abort.Disp.t1, Abort.Disp.t2,
        Abort.Disp.t3, Abort.Disp.t4, Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, Abort.Disp.g4, Abort.b0,
        Abort.b1Write, Abort.b2] at hk; omega)
      (by
        simp only [Abort.Disp.DN.nd4, Abort.N, Abort.pcSvc, Abort.write, Int64.add_assoc]
        all_goals first | exact (ofNat4_zero _).symm | (congr 1 <;> decide)))

/-- The stub's single nodes `.n1`, `.n1b`, `.svc` are off the exits. -/
theorem pcOff_n1 {lab : String → Int64} (hoff : RunsOffA lab abortRunsX) {c0 : Ctl} :
    PcOffA lab (Abort.N lab Abort.write c0 .n1).pc ∧ PcOffA lab (Abort.N lab Abort.write c0 .n1b).pc ∧
      PcOffA lab (Abort.N lab Abort.write c0 .svc).pc := by
  have hE : ∀ j, j < 11 → PcOffA lab (lab ".L16_scc_rt_abort_write.0_entry" + Int64.ofNat (4 * j)) :=
    fun j hj => hoff (".L16_scc_rt_abort_write.0_entry", 0, 11) (by simp [abortRunsX]) j (Nat.zero_le _) hj
  have h0 := hE 0 (by decide)
  have h1 := hE 1 (by decide)
  have h7 := hE 7 (by decide)
  rw [ofNat4_zero] at h0
  rw [show Int64.ofNat (4 * 1) = 4 by decide] at h1
  rw [show Int64.ofNat (4 * 7) = 4 + 4 + 4 + 4 + 4 + 4 + 4 by decide] at h7
  simp only [Int64.add_assoc] at h7
  simp only [Abort.N, Abort.pcSvc, Abort.write, Int64.add_assoc]
  exact ⟨h0, h1, h7⟩

/-- **`AbX` at every node of the write abort path** for any source control
`c0`, in a region reaching 48 bytes down, the path's pcs off the exits
and the transfer sites (`hoff`; for hello, `runsOffA_of_chk` on
`abortRunsX`). -/
theorem abortObl_abX (hμ : MarksL μ (_root_.Executable.labels exe).label)
    (hoff : RunsOffA (_root_.Executable.labels exe).label abortRunsX)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c0 : Ctl} :
    AbortObl (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F c0 := by
  have hoff32 : R.Off (-32) := ⟨by decide, by omega, by omega⟩
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 := .inr (.inr (.inr rfl))
  have hj : ∀ {j : Nat}, j < Abort.Disp.j1.length → j < 1 := fun h => h
  have hkoff : ∀ (s : State) (q : Int64), s.st.2 = q → PcOffA (_root_.Executable.labels exe).label q →
      ∀ k a, μ.abortAt k = some a → Scc.Sem.A64.pcOf s = a → k = .writeErr :=
    fun s q hq hP k a ha hpc => ((pcOff_of hμ (s := s) (hq ▸ hP)).noAbort k a ha hpc).elim
  exact
    { de := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispE (memE hk) hA ((congrArg (fun x => x.toBitVec.toNat) (d0_x0 _ _ hk)).trans hJ.2))
        (zo "scc_rt_abort" 0 5)
      dt1 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inl rfl) hT1 hk) hA (t_run hT1 _ _ hk).1 hoff32
          ((congrArg (fun f => (f (-32)).toNat) (t_run hT1 _ _ hk).2).trans hJ.2))
        (zo ".L12_scc_rt_abort.0_entry" 0 5)
      dj1 := blkZA_abX hμ (fun _ σ _ j _ hJ hk hA => by
          obtain rfl : j = 0 := by have := hj hk; omega
          exact ab_dispT (memJ (.inl rfl) (by decide)) hA rfl hoff32 hJ.2)
        (zo ".L12_scc_rt_abort.0_entry" 4 5)
      dt2 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispT (memT (.inr (.inl rfl)) hT2 hk) hA (t_run hT2 _ _ hk).1 hoff32
          ((congrArg (fun f => (f (-32)).toNat) (t_run hT2 _ _ hk).2).trans hJ.2))
        (zo ".L12_scc_rt_abort.2_next1" 0 5)
      dj2 := blkZA_abX hμ (fun _ σ _ j _ hJ hk hA => by
          obtain rfl : j = 0 := by have := hj hk; omega
          exact ab_dispT (memJ (.inr (.inl rfl)) (by decide)) hA rfl hoff32 hJ.2)
        (zo ".L12_scc_rt_abort.2_next1" 4 5)
      dt3 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispT (memT (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run hT3 _ _ hk).1 hoff32
          ((congrArg (fun f => (f (-32)).toNat) (t_run hT3 _ _ hk).2).trans hJ.2))
        (zo ".L12_scc_rt_abort.4_next3" 0 5)
      dj3 := blkZA_abX hμ (fun _ σ _ j _ hJ hk hA => by
          obtain rfl : j = 0 := by have := hj hk; omega
          exact ab_dispT (memJ (.inr (.inr rfl)) (by decide)) hA rfl hoff32 hJ.2)
        (zo ".L12_scc_rt_abort.4_next3" 4 5)
      dt4 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispT (memT (.inr (.inr (.inr rfl))) hT4 hk) hA (t_run hT4 _ _ hk).1 hoff32
          ((congrArg (fun f => (f (-32)).toNat) (t_run hT4 _ _ hk).2).trans hJ.2))
        (zo ".L12_scc_rt_abort.6_next5" 0 4)
      dg4 := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.A64.WriteAb.ab_g4 (memG hk))
        (zo ".L12_scc_rt_abort.7_is6" 0 4)
      se := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.A64.WriteAb.ab_stub (memB0 hk))
        (zo "scc_rt_abort_write" 0 4)
      sn1 := nodeW_abXA (fun _ h => Spike.Lib.A64.WriteAb.ab_stub (by rw [h]; simp [Abort.N, WriteAb.stubPcs]))
        fun s h => hkoff s _ h (by
          exact (pcOff_n1 hoff).1)
      sn1b := nodeW_abXA (fun _ h => Spike.Lib.A64.WriteAb.ab_stub (by rw [h]; simp [Abort.N, WriteAb.stubPcs]))
        fun s h => hkoff s _ h (by
          exact (pcOff_n1 hoff).2.1)
      sn2 := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.A64.WriteAb.ab_stub (memB1 hk))
        (zo ".L16_scc_rt_abort_write.0_entry" 2 11)
      svc := nodeW_abXA (fun _ h => Spike.Lib.A64.WriteAb.ab_stub (by rw [h]; exact memSvc))
        fun s h => hkoff s _ h (by
          exact (pcOff_n1 hoff).2.2)
      sn5 := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.A64.WriteAb.ab_stub (memB2 hk))
        (zo ".L16_scc_rt_abort_write.0_entry" 8 11)
      sex := nodeW_abXA (fun _ h => Spike.Lib.A64.WriteAb.ab_stub (by rw [h]; simp [Abort.N, WriteAb.stubPcs]))
        fun s h => hμ.k_of_wexit h }

/-- `abortRunsX` off the exits and the transfer sites in hello's listing. -/
theorem abortRunsX_chk : runsNeChk helloProg abortRunsX abPtsA = true := by decide +kernel

/-- **`abortObl_abX` at hello's listing** (`hoff` decided). -/
theorem abortObl_abXH [Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloProg kp)
    (hμ : MarksL μ (_root_.Executable.labels exe).label) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c0 : Ctl} :
    AbortObl (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F c0 :=
  abortObl_abX hμ (runsOffA_of_chk hp abortRunsX_chk) hlo hhi

end Nodes

end Spike.Lib.A64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.abortObl_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.abortObl_abX

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.AbObl.abortObl_abXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.AbObl.abortObl_abXH

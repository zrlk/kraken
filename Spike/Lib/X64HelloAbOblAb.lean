/-
**`AbX` at every node of `print`'s write abort path** (x86-64; the twin of
`Spike/Lib/A64HelloAbOblAb.lean`): `AbortObl` at `Z := AbX μ lab · · fs`.
Every state of the path is in the write abort's phase `WriteAb.Ab lab` (the
dispatcher's prologue with `%rdi = 4`, its tests with `4` at `-8(%rbp)`, the
jump to the stub and the stub: `X64StubWA`'s `ab_*` and `mem*` lemmas from the
nodes' invariants `Abort.Disp.DN.nd4`), where `AbSt` is vacuous; an abort site
there is `writeErr`'s: at the stub's exit by `MarksL.k_of_wexit`, elsewhere
none (the path's pcs off the exits and the transfer sites, `hoff`, decided on
the listing).

No code fact is needed: `WriteAb.Ab` reads the pc and the abstract state.

- `abortRunsX`: `abortRuns` less the exit call.
- `blkZA_abX`: `AbX` at a block node's states in the phase (`hAb`, the form
  of `StubW.blkW_writeA`'s), off the exits (`hoff`).
- `abortObl_abX`: `AbortObl (AbX μ lab · · fs)` for any source control;
  `abortObl_abXH` at hello's listing (`abortRunsX_chk`, decided).

Unlike AArch64 (forced by the x86-64 stub, `Spike/Lib/X64Abort.lean`,
`Spike/Lib/X64AbortWriteW.lean`):
- the runs are byte runs (`abortRuns`'s first eight) and a block's pcs are
  `cellOff` bytes on (AArch64: `4 * j`), each run's bound decided per block
  (`zoff`);
- the stub's single nodes are `n1` (the `leaq`), `sys` (the `write` call) and
  `ex`: there is no `n1b`, and the system-call field is `sys` (AArch64:
  `svc`);
- the region is the callee's `[-24, 16)` (`hlo`, `hhi`, as `PrintTCSX`'s
  `hZA` gives it; AArch64: `R.lo ≤ -48`, `0 ≤ R.hi`), the code `4` at
  `-8(%rbp)` (AArch64: `[sp, #-32]`).
-/
import Spike.Lib.X64HelloAbortObl
import Spike.Lib.X64HelloAbObl
import Spike.Lib.X64StubWA

namespace Spike.Lib.X64.Flow.Worker.Hello.AbObl

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Spike.Lib (Region)
open Spike.Lib.X64 (ND NodeW At cellOff)
open Spike.Lib.X64.Flow.Worker (NodeZA AbortObl abortRuns)
open Spike.Lib.X64WakeOff (PcOffA RunsOffA pcOffA_add pcOffA_at)
open Spike.Lib.X64.StubW (ab_dispE ab_dispT d0_rdi t_run memE memT memJ memG memX0 memX1 memX2 memSys)
open Scc.Cert.Rt.X64 (Lays)
open Spike.Lib.X64.RunsOff (runsNeChk abPtsA runsOffA_of_chk)
open SccCode (helloCells)

/-- **The abort path's pcs less the exit call** (`abortRuns`'s first
eight runs): off every exit and transfer site in hello's listing. -/
def abortRunsX : List (Label × Nat × Nat) :=
  [("scc_rt_abort", 0, 12), (".Lscc_rt_abort.entry", 0, 18), (".Lscc_rt_abort.next1", 0, 18),
    (".Lscc_rt_abort.next3", 0, 18), (".Lscc_rt_abort.next5", 0, 16), (".Lscc_rt_abort.is6", 0, 9),
    ("scc_rt_abort_write", 0, 8), (".Lscc_rt_abort_write.entry", 0, 52)]

/-- `abortRunsX` is `abortRuns` less its last run, the exit call. -/
example : abortRuns = abortRunsX ++ [("scc_rt_abort_write_exit", 0, 2)] := rfl

/-- **A block's pcs in a run are off**: the block at `c` bytes after the
run's label `l`, its cells within the run (`hb`). -/
theorem zoff {lab : String → Int64} (hoff : RunsOffA lab abortRunsX) {l : Label} {c hi : Nat}
    {blk : List (Directive × Nat)} {q : Int64} (hq : (l, 0, hi) ∈ abortRunsX)
    (hb : ∀ j < blk.length, c + cellOff blk j < hi) (hq' : q = lab l + Int64.ofNat c) :
    ∀ j < blk.length, PcOffA lab (q + Int64.ofNat (cellOff blk j)) :=
  fun j hj => pcOffA_add hoff hq (Nat.zero_le _) (hb j hj) hq'

section Nodes

variable {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {fs : List TermRun.Frame}

/-- **`AbX` at a block node's states in the phase** (`hAb`), its pcs off the
exits and the transfer sites (`hoff`). -/
theorem blkZA_abX (hμ : MarksL μ (_root_.Executable.labels exe).label) {n : ND} {blk : List (Directive × Nat)}
    (hAb : ∀ (s : State) σ c j m, n.J σ c → j < blk.length →
      Spike.Lib.X64.Abs R (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.X64.arun (_root_.Executable.labels exe).label (blk.take j) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label
        { s with st := (m, n.pc + Int64.ofNat (cellOff blk j)) })
    (hoff : ∀ j < blk.length, PcOffA (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (cellOff blk j))) :
    NodeZA (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F n blk :=
  fun s σ c _ _ _ _ _ _ hJ k hk m hA' _ =>
    ⟨AbX.of_ab (hAb s σ c k m hJ hk hA') fun _ a ha hpc =>
      ((pcOff_of hμ (s := { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }) (hoff k hk)).noAbort _ a ha
        hpc).elim,
      fun _ h => h⟩

/-- **`AbX` at a single node's states in the phase**, its pc off the exits
or the write exit itself (`hk`). -/
theorem nodeW_abXA {n : ND}
    (hAb : ∀ s : State, s.st.2 = n.pc → Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s)
    (hk : ∀ s : State, s.st.2 = n.pc → ∀ k a, μ.abortAt k = some a → Scc.Sem.X64.pcOf s = a → k = .writeErr) :
    NodeW (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) (fun _ _ => False) exe endPc R F n :=
  fun s _ ⟨_, _, _, hpc, _⟩ => ⟨AbX.of_ab (hAb s hpc) (hk s hpc), fun _ h => h⟩

/-- **`AbX` at every node of the write abort path** for any source control
`c0`, in the callee's region `[-24, 16)`, the path's pcs off the exits and
the transfer sites (`hoff`; for hello, `runsOffA_of_chk` on `abortRunsX`). -/
theorem abortObl_abX (hμ : MarksL μ (_root_.Executable.labels exe).label)
    (hoff : RunsOffA (_root_.Executable.labels exe).label abortRunsX)
    (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) {c0 : Ctl} :
    AbortObl (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F c0 := by
  have hoff8 : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have z0 : ∀ a : Int64, a + Int64.ofNat 0 = a := fun a => by
    rw [show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  have hT1 : Abort.Disp.t1 = Abort.Disp.t1 ∨ Abort.Disp.t1 = Abort.Disp.t2 ∨ Abort.Disp.t1 = Abort.Disp.t3 ∨
    Abort.Disp.t1 = Abort.Disp.t4 := .inl rfl
  have hT2 : Abort.Disp.t2 = Abort.Disp.t1 ∨ Abort.Disp.t2 = Abort.Disp.t2 ∨ Abort.Disp.t2 = Abort.Disp.t3 ∨
    Abort.Disp.t2 = Abort.Disp.t4 := .inr (.inl rfl)
  have hT3 : Abort.Disp.t3 = Abort.Disp.t1 ∨ Abort.Disp.t3 = Abort.Disp.t2 ∨ Abort.Disp.t3 = Abort.Disp.t3 ∨
    Abort.Disp.t3 = Abort.Disp.t4 := .inr (.inr (.inl rfl))
  have hT4 : Abort.Disp.t4 = Abort.Disp.t1 ∨ Abort.Disp.t4 = Abort.Disp.t2 ∨ Abort.Disp.t4 = Abort.Disp.t3 ∨
    Abort.Disp.t4 = Abort.Disp.t4 := .inr (.inr (.inr rfl))
  have hj : ∀ {blk : List (Directive × Nat)} {j : Nat},
      (blk = Abort.Disp.j1 ∨ blk = Abort.Disp.j2 ∨ blk = Abort.Disp.j3) → j < blk.length → j = 0 := by
    intro blk j hb hk
    rcases hb with rfl | rfl | rfl <;>
      simp only [Abort.Disp.j1, Abort.Disp.j2, Abort.Disp.j3, List.length_zip, List.length_cons,
        List.length_nil] at hk <;> omega
  have hkoff : ∀ (s : State) (q : Int64), s.st.2 = q → PcOffA (_root_.Executable.labels exe).label q →
      ∀ k a, μ.abortAt k = some a → Scc.Sem.X64.pcOf s = a → k = .writeErr :=
    fun s q hq hP k a ha hpc => ((pcOff_of hμ (s := s) (hq ▸ hP)).noAbort k a ha hpc).elim
  exact
    { de := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA => ab_dispE (memE hk) hA ((d0_rdi _ _ hk).trans hJ.2))
        (zoff hoff (l := "scc_rt_abort") (c := 0) (hi := 12) (by simp [abortRunsX]) (by decide) (z0 _).symm)
      dt1 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA => ab_dispT (memT (.inl rfl) hT1 hk) hA (t_run hT1 _ _ hk).1
          hoff8 ((congrArg (fun f => f (-8)) (t_run hT1 _ _ hk).2).trans hJ.2))
        (zoff hoff (l := ".Lscc_rt_abort.entry") (c := 0) (hi := 18) (by simp [abortRunsX]) (by decide)
          (z0 _).symm)
      dj1 := blkZA_abX hμ (fun _ σ _ j _ hJ hk hA => by
          obtain rfl := hj (.inl rfl) hk
          exact ab_dispT (memJ (.inl rfl) (.inl rfl) hk) hA
            (by first | rfl | simp [Spike.Lib.X64.arun, SO.get, Spike.Lib.lk, Abort.Disp.oD]) hoff8 hJ.2)
        (zoff hoff (l := ".Lscc_rt_abort.entry") (c := 16) (hi := 18) (by simp [abortRunsX]) (by decide) rfl)
      dt2 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispT (memT (.inr (.inl rfl)) hT2 hk) hA (t_run hT2 _ _ hk).1 hoff8
            ((congrArg (fun f => f (-8)) (t_run hT2 _ _ hk).2).trans hJ.2))
        (zoff hoff (l := ".Lscc_rt_abort.next1") (c := 0) (hi := 18) (by simp [abortRunsX]) (by decide)
          (z0 _).symm)
      dj2 := blkZA_abX hμ (fun _ σ _ j _ hJ hk hA => by
          obtain rfl := hj (.inr (.inl rfl)) hk
          exact ab_dispT (memJ (.inr (.inl rfl)) (.inr (.inl rfl)) hk) hA
            (by first | rfl | simp [Spike.Lib.X64.arun, SO.get, Spike.Lib.lk, Abort.Disp.oD]) hoff8 hJ.2)
        (zoff hoff (l := ".Lscc_rt_abort.next1") (c := 16) (hi := 18) (by simp [abortRunsX]) (by decide) rfl)
      dt3 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispT (memT (.inr (.inr (.inl rfl))) hT3 hk) hA (t_run hT3 _ _ hk).1 hoff8
            ((congrArg (fun f => f (-8)) (t_run hT3 _ _ hk).2).trans hJ.2))
        (zoff hoff (l := ".Lscc_rt_abort.next3") (c := 0) (hi := 18) (by simp [abortRunsX]) (by decide)
          (z0 _).symm)
      dj3 := blkZA_abX hμ (fun _ σ _ j _ hJ hk hA => by
          obtain rfl := hj (.inr (.inr rfl)) hk
          exact ab_dispT (memJ (.inr (.inr rfl)) (.inr (.inr rfl)) hk) hA
            (by first | rfl | simp [Spike.Lib.X64.arun, SO.get, Spike.Lib.lk, Abort.Disp.oD]) hoff8 hJ.2)
        (zoff hoff (l := ".Lscc_rt_abort.next3") (c := 16) (hi := 18) (by simp [abortRunsX]) (by decide) rfl)
      dt4 := blkZA_abX hμ (fun _ σ _ _ _ hJ hk hA =>
          ab_dispT (memT (.inr (.inr (.inr rfl))) hT4 hk) hA (t_run hT4 _ _ hk).1 hoff8
            ((congrArg (fun f => f (-8)) (t_run hT4 _ _ hk).2).trans hJ.2))
        (zoff hoff (l := ".Lscc_rt_abort.next5") (c := 0) (hi := 16) (by simp [abortRunsX]) (by decide)
          (z0 _).symm)
      dg4 := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.X64.WriteAb.ab_g4 (memG hk))
        (zoff hoff (l := ".Lscc_rt_abort.is6") (c := 0) (hi := 9) (by simp [abortRunsX]) (by decide) (z0 _).symm)
      se := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.X64.WriteAb.ab_stub (memX0 hk))
        (zoff hoff (l := "scc_rt_abort_write") (c := 0) (hi := 8) (by simp [abortRunsX]) (by decide) (z0 _).symm)
      sn1 := nodeW_abXA
        (fun _ h => Spike.Lib.X64.WriteAb.ab_stub (by rw [h]; simp [Abort.N, Spike.Lib.X64.WriteAb.stubPcs]))
        fun s h => hkoff s _ h (pcOffA_at hoff (l := ".Lscc_rt_abort_write.entry") (c := 0) (hi := 52)
          (by simp [abortRunsX]) (Nat.le_refl _) (by decide) (z0 _).symm)
      sn2 := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.X64.WriteAb.ab_stub (memX1 hk))
        (zoff hoff (l := ".Lscc_rt_abort_write.entry") (c := 7) (hi := 52) (by simp [abortRunsX]) (by decide) rfl)
      sys := nodeW_abXA (fun _ h => Spike.Lib.X64.WriteAb.ab_stub (by rw [h]; exact memSys))
        fun s h => hkoff s _ h (pcOffA_at hoff (l := ".Lscc_rt_abort_write.entry") (c := 34) (hi := 52)
          (by simp [abortRunsX]) (Nat.zero_le _) (by decide) rfl)
      sn5 := blkZA_abX hμ (fun _ _ _ _ _ _ hk _ => Spike.Lib.X64.WriteAb.ab_stub (memX2 hk))
        (zoff hoff (l := ".Lscc_rt_abort_write.entry") (c := 36) (hi := 52) (by simp [abortRunsX]) (by decide)
          rfl)
      sex := nodeW_abXA
        (fun _ h => Spike.Lib.X64.WriteAb.ab_stub (by rw [h]; simp [Abort.N, Spike.Lib.X64.WriteAb.stubPcs]))
        fun _ h => hμ.k_of_wexit h }

/-- `abortRunsX` off the exits and the transfer sites in hello's listing. -/
theorem abortRunsX_chk : runsNeChk helloCells abortRunsX abPtsA = true := by decide +kernel

/-- **`abortObl_abX` at hello's listing** (`hoff` decided). -/
theorem abortObl_abXH [Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloCells kp)
    (hμ : MarksL μ (_root_.Executable.labels exe).label) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) {c0 : Ctl} :
    AbortObl (fun s c => AbX μ (_root_.Executable.labels exe).label s c fs) exe endPc R F c0 :=
  abortObl_abX hμ (runsOffA_of_chk hp abortRunsX_chk) hlo hhi

end Nodes

end Spike.Lib.X64.Flow.Worker.Hello.AbObl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abortObl_abX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abortObl_abX

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.AbObl.abortObl_abXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.AbObl.abortObl_abXH

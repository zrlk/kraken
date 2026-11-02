/-
**hello.w on x86-64: main after a refused `clone` inside `SFactsAC`**, the
twin of `Spike/Lib/A64HelloSpawnFailAC.lean`: the path's states in the
threads abort phase `Hello.ThreadsAb.AcH lab ".Lwc_main"`
(`Spike/Lib/X64HelloThreadsAb.lean`) at hello's frame of 128 and listing
(`SccCode.helloCells`), for the nodes of `X64HelloSpawnFail.fN`: the
`testq` at `pcRet` (`.x25 + 96`) and the `je` at `pcJe` (`.x25 + 99`) with
`%rax` a refusal, `.x26`'s store at `pcSt` with `%rax` a refusal, `.x26`'s
tests with the stored result `-120(%rbp)` (`slot (-120)`) a refusal,
`.spawnfail5` unconditionally.

- `x26_run`: `.x26`'s block past its store keeps `%rbp` at the frame's base
  and has the stored `%rax` at `slot (-120)`.
- `bp120`: the word at `-120(%rbp)` from the abstract state.
- `ac_ts`, `ac_je'`, `ac_x26`, `ac_fl`: the nodes' states in `AcH`.
- `failInB`, `hello_failInB`: the path's code as `blockAtB` facts in
  `helloCells` (the form `blkW_threadsAC` and `nodeW_test_threadsAC` read).

The blocks' obligations are `X64StubTAC.blkW_threadsAC` and the test row's
`X64SpawnFailAC.nodeW_test_threadsAC`, both generic in the cells and the
phase, applied at the consumer (as `X64WakeRefBlk` does for wake).

**Deviation from the A64 file.** As in `Spike/Lib/X64SpawnFailAC.lean`:
four nodes (`ts`, `je`, `x26`, `fl`; A64: `cb`, `cl`, `fl`), so A64's
`ac_cb`/`ac_cl` are `ac_ts`/`ac_je'`/`ac_x26`; A64's `cl_run_sp` and
`sp112` are `x26_run` and `bp120` (a `%rbp` slot, A64: `[sp + 112]`,
`slot (-32)`); A64's `cb_noRet`/`cl_noRet`/`flB_noRet` are `by decide` at
the use (x86-64's `noRetBlk` decides on the concrete blocks); A64's
`blkWs_spawnFail_hello` has no consumer and is not twinned.
-/
import Spike.Lib.X64HelloSpawnFail
import Spike.Lib.X64HelloSpawnFailS
import Spike.Lib.X64SpawnFailAC

namespace Spike.Lib.X64.Flow.Worker.Hello.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64Consumer
open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Scc.Cert.Rt.X64 (blockAtB)
open Spike.Lib.X64.Flow.Worker.Hello.Child (x25L)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (oP tsB jeB x26B x26L)
open Spike.Lib.X64.ThreadsAb (CloneRef)
open Spike.Lib.X64.Hello.ThreadsAb (AcH)

set_option linter.unusedSimpArgs false

/-- The abstract run's simp set over `.x26`'s block
(`Spike/Lib/X64SpawnFailAC.lean`'s). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, Spike.Lib.X64.classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- `.x26`'s block past its store keeps `%rbp` at main's frame's base and
has the stored `%rax` at `slot (-120)`. -/
theorem x26_run (lab : Label → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k < x26B.length) (h1 : 1 ≤ k) :
    (arun lab (x26B.take k) ⟨pc, oP, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (x26B.take k) ⟨pc, oP, σ⟩).σ.slot (-120) = σ.regs.get64 .rax := by
  simp only [x26B] at hk ⊢
  simp only [List.length_zip, List.length_cons, List.length_nil] at hk
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- The word at `-120(%rbp)` from the abstract state, `%rbp` at the frame's
base. -/
theorem bp120 {R : Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ)
    (ho : o.get .rbp = some 0) (hoff : R.Off (-120)) :
    Spike.Lib.X64.WriteAb.bpLoad s (-120) = some (σ.slot (-120)) := by
  have := Spike.Lib.X64ConsumerA.ThreadsAcSt.load_of_abs hA (r := .rbp) (k := -120) (d := -120)
    (by simpa using ho) hoff
  rw [← this]; rfl

/-- A disjunction of up to four equations, one of them by `rfl`. -/
local macro "pick_rfl" : tactic =>
  `(tactic| first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr (Or.inl rfl)) |
    exact Or.inr (Or.inr (Or.inr rfl)) | exact Or.inr rfl | rfl)

section Ac

variable {lab : Label → Int64} {cP : Ctl} {cA mT : BitVec 64} {R : Region}

/-- The `testq` after the call, `%rax` a refusal, is in `AcH`. -/
theorem ac_ts (s : State) (σ : AS) (c : Ctl) (hJ : (fN lab cP cA mT .ts).J σ c)
    (hA : Abs R (fN lab cP cA mT .ts).o s.st.1 σ) (hp : s.st.2 = lab x25L + Int64.ofNat 96) :
    AcH lab ".Lwc_main" s := by
  refine Spike.Lib.X64.Hello.ThreadsAb.ac_ret ?_ ?_
  · rw [hp]; show lab x25L + Int64.ofNat 96 = lab x25L + Int64.ofNat 94 + 2
    rw [Int64.add_assoc]; rfl
  · rw [hA.regs]; exact hJ.2.1

/-- The `je` after the test, `%rax` a refusal, is in `AcH`. -/
theorem ac_je' (s : State) (σ : AS) (c : Ctl) (j : Nat) (m : MachineData) (hJ : (fN lab cP cA mT .je).J σ c)
    (hj : j < jeB.length)
    (hA : Abs R (arun lab (jeB.take j) ⟨(fN lab cP cA mT .je).pc, (fN lab cP cA mT .je).o, σ⟩).so m
      (arun lab (jeB.take j) ⟨(fN lab cP cA mT .je).pc, (fN lab cP cA mT .je).o, σ⟩).σ) :
    AcH lab ".Lwc_main" { s with st := (m, (fN lab cP cA mT .je).pc + Int64.ofNat (cellOff jeB j)) } := by
  obtain rfl : j = 0 := by simp only [jeB, List.length_zip, List.length_cons, List.length_nil] at hj; omega
  refine Spike.Lib.X64.Hello.ThreadsAb.ac_je ?_ ?_
  · show lab x25L + 99 + Int64.ofNat (cellOff jeB 0) = lab x25L + Int64.ofNat 94 + 5
    rw [cellOff_zero, ofNat_zero', Int64.add_assoc]; rfl
  · show CloneRef m.regs.rax.toBitVec
    rw [hA.regs]
    exact hJ.2.1

/-- `.x26`'s store and tests are in `AcH`: `%rax` a refusal at the store,
the stored result `-120(%rbp)` past it. -/
theorem ac_x26 (hoff : R.Off (-120)) (s : State) (σ : AS) (c : Ctl) (j : Nat) (m : MachineData)
    (hJ : (fN lab cP cA mT .x26).J σ c) (hj : j < x26B.length)
    (hA : Abs R (arun lab (x26B.take j) ⟨(fN lab cP cA mT .x26).pc, (fN lab cP cA mT .x26).o, σ⟩).so m
      (arun lab (x26B.take j) ⟨(fN lab cP cA mT .x26).pc, (fN lab cP cA mT .x26).o, σ⟩).σ) :
    AcH lab ".Lwc_main" { s with st := (m, (fN lab cP cA mT .x26).pc + Int64.ofNat (cellOff x26B j)) } := by
  rcases Nat.eq_zero_or_pos j with rfl | h1
  · refine .inr (.inl ⟨?_, ?_⟩)
    · show lab x26L + Int64.ofNat (cellOff x26B 0) = lab x26L
      rw [cellOff_zero]; exact ofNat_zero' _
    · show CloneRef m.regs.rax.toBitVec
      rw [hA.regs]
      exact hJ.2.1
  · obtain ⟨hbp, hsl⟩ := x26_run lab (fN lab cP cA mT .x26).pc σ hj h1
    refine .inr (.inr (.inl ⟨?_, _, bp120 (s := { s with st := (m, _) }) hA hbp hoff, ?_⟩))
    · have hj5 : j < 5 := by simp [x26B] at hj; omega
      show lab x26L + Int64.ofNat (cellOff x26B j) ∈ Spike.Lib.X64.Hello.ThreadsAb.tailPcsH lab ".Lwc_main"
      simp only [Spike.Lib.X64.Hello.ThreadsAb.tailPcs, List.mem_cons, List.mem_nil_iff, or_false]
      rcases j with _|_|_|_|_|j <;> (try omega) <;> pick_rfl
    · exact (congrArg CloneRef hsl).mpr hJ.2.1

/-- `.spawnfail5` is in `AcH`. -/
theorem ac_fl (s : State) (j : Nat) (m : MachineData) (hj : j < flB.length) :
    AcH lab ".Lwc_main" { s with st := (m, (fN lab cP cA mT .fl).pc + Int64.ofNat (cellOff flB j)) } := by
  have hj2 : j < 2 := by simpa [flB] using hj
  refine Spike.Lib.X64.Hello.ThreadsAb.ac_fail ?_
  show lab flL + Int64.ofNat (cellOff flB j) ∈ Spike.Lib.X64.ThreadsAb.failPcs lab ".Lwc_main"
  simp only [Spike.Lib.X64.ThreadsAb.failPcs, List.mem_cons, List.mem_nil_iff, or_false]
  rcases j with _|_|j
  · exact .inl (by rw [cellOff_zero]; exact ofNat_zero' _)
  · exact .inr rfl
  · omega

end Ac

/-! ## The path's code in hello's program -/

/-- **The refusal path's code as `blockAtB` facts** (`failIn`'s blocks and
row, by byte offset). -/
def failInB (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells x25L 96 tsB && blockAtB cells x25L 99 jeB && blockAtB cells x26L 0 x26B &&
    blockAtB cells flL 0 flB

theorem hello_failInB : failInB SccCode.helloCells = true := by decide +kernel

end Spike.Lib.X64.Flow.Worker.Hello.SpawnFail

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.x26_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.x26_run

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.bp120' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.bp120

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_ts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_ts

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_je'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_je'

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_x26' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_x26

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.ac_fl

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failInB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.SpawnFail.hello_failInB

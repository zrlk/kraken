/-
**wake.w on x86-64: main after a refused `clone`** (the spawn's refusal
half, twin of `Spike/Lib/A64WakeSpawnFail.lean`; the parent half is
`Spike/Lib/X64WakeParent.lean`): back from main's `clone`
(`ThreadsAb.cloneAt`, `.Lwc_main.x3 + 46`) with a refusal in `%rax`
(`ThreadsAb.CloneRef`: `-EAGAIN` or `-ENOMEM`), main runs

    testq %rax, %rax                    -- row (test_ndW): ZF clear
    je .Lwc_main.child.scc_rt_thr_worker                -- not taken
    .x22: movq %rax, -56(%rbp); movq -56(%rbp), %rax; movq $0, %rcx
          cmpq %rcx, %rax; jl .Lwc_main.spawnfail5      -- taken (%rax < 0)
    .spawnfail5: movq $5, %rdi; call scc_rt_abort

in its frame (`oW`), and the call `scc_rt_abort(5)` does not return
(`Abort.Disp.seg_jabort5W`, the dispatcher in `[-24, 16)` below the pushed
return address), with the return address `ThreadsAb.raT lab ".Lwc_main"`
that the `call` pushes at `-72` carried to the threads stub.

- `flB`: `.spawnfail5`'s block.
- `fN lab cP cA m`: the nodes (`FN`: `ts`, `je`, `x22`, `fl`); `fE`: the
  exit, at `scc_rt_abort` with `%rdi = 5`, the return address at `-72`.
- `failIn cells`, `wake_failIn`: the blocks and rows at their places.
- `seg_failW`: from `fN .ts` to `fE` inside `W`.
- `seg_spawnFailW`: from `fN .ts` to any fragment: `seg_failW` then
  `seg_jabort5W`, given the threads abort path's obligations (`StubTW`) per
  caller state.

**Unlike AArch64**: the result's test is a row (`testq`, `test_ndW`) and the
`je` a block of its own, so there are four nodes (`ts`, `je`, `x22`, `fl`;
A64: `cb`, `cl`, `fl`) and the test's obligation is a `NodeW`; the code
checks are `blockAt cells l k off` on any cells passing `failIn` (A64:
`wakeProg` only, `seg_spawnFailW_wake`), so `seg_spawnFailW` takes
`hp hend hin` and no separate code premises; the prefix is fixed to
`.Lwc_main` (as `X64WakeParent`'s blocks name their labels); main's slots
`MS cA m` are the cell at `-16` and main's word at `-8` (`WcClone.FrW`'s;
A64: `-72`, `-80`); the call pushes the return address at `-72`, so the
region needs `R.lo ≤ -104`, `16 ≤ R.hi` (no alignment premise).
-/
import Spike.Lib.X64WakeParent
import Spike.Lib.X64AbortThreadsW
import Spike.Lib.X64ThreadsAb
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.WakePh.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (oW x21L)
open Spike.Lib.X64.WakePh.Parent (tsB jeB x22B x22L jeB_ok jeB_run x22B_ok x22B_run)
open Spike.Lib.X64.ThreadsAb (CloneRef raT)
open Scc.Cert.Rt.X64 (Lays endOf blockAt labelGap codeAt_blockAt_lays label_labelGap_lays)

/-! ## The block -/

/-- `.spawnfail5`: the threads code and the call of the dispatcher. -/
def flB : List (Directive × Nat) := (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5]

block_spec flB (-72) 16 oW flB

/-- `.spawnfail5`'s label. -/
abbrev flL : Label := ".Lwc_main.spawnfail5"

/-- **The refusal path's blocks and rows in `cells`**: the test and the
`je` at `.x21 + 48`, `+ 51` (`Parent.parentIn`'s), `.x22` fifteen cells
(53 bytes) after `.x21`, its block, `.spawnfail5`'s. -/
def failIn (cells : List (Directive × Nat)) : Bool :=
  blockAt cells x21L 13 48 tsB && blockAt cells x21L 14 51 jeB && labelGap cells x21L x22L 15 53 &&
    blockAt cells x22L 0 0 x22B && blockAt cells flL 0 0 flB

theorem wake_failIn : failIn SccCode.wakeCells = true := by decide +kernel

/-! ## The nodes -/

/-- The refusal path's internal nodes. -/
inductive FN where
  | ts | je | x22 | fl

/-- **Main's slots of the spawn's words**: the box's cell `cA` at `-16` and
main's `ThreadId` word `m` at `-8` (`WcClone.FrW`'s). -/
def MS (cA m : BitVec 64) (σ : AS) : Prop := σ.slot (-16) = cA ∧ σ.slot (-8) = m

variable (lab : Label → Int64) (cP : Ctl) (cA m : BitVec 64)

/-- **The refusal path's nodes**: past the clone (`ts`, `%rax` a refusal),
the `je` (`ZF` clear), `.x22` (`%rax` a refusal), `.spawnfail5` (`fl`); the
source at `cP` and main's slots `MS cA m` throughout. -/
def fN : FN → ND
  | .ts => ⟨lab x21L + 48, oW, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MS cA m σ⟩
  | .je => ⟨lab x21L + 51, oW, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MS cA m σ ∧
      σ.status.zf = false⟩
  | .x22 => ⟨lab x22L, oW, fun σ c => c = cP ∧ CloneRef (σ.regs.get64 .rax) ∧ MS cA m σ⟩
  | .fl => ⟨lab flL, oW, fun σ c => c = cP ∧ MS cA m σ⟩

/-- **The exit**: the call of `scc_rt_abort` with `%rdi = 5` and the return
address `raT lab ".Lwc_main"` at `-72`, in main's frame with its slots
`MS cA m`. -/
def fE : ND :=
  ⟨lab "scc_rt_abort", ⟨-72, [(.rbp, 0)]⟩, fun σ c => c = cP ∧ σ.regs.get64 .rdi = 5#64 ∧
    σ.slot (-72) = raT lab ".Lwc_main" ∧ MS cA m σ⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {cP : Ctl} {cA m : BitVec 64}

/-- **Main after a refused clone is one segment inside `W`**, from `fN .ts`
to the call of `scc_rt_abort(5)` (`fE`): `ZF` clear (a refusal is not `0`),
the `je` not taken, the `jl` taken (a refusal is negative), `.spawnfail5`'s
`call`. -/
theorem seg_failW {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : failIn cells = true) {W : Frag isa} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -72) (hhi : 16 ≤ R.hi)
    (hWts : NodeW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .ts))
    (hWje : BlkW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .je) jeB)
    (hWx22 : BlkW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .x22) x22B)
    (hWfl : BlkW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .fl) flB) :
    SegW W K p lbl ms (At exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .ts))
      (At exe endPc R F (fE (_root_.Executable.labels exe).label cP cA m)) := by
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨bts, bje⟩, hgap⟩, b22⟩, bfl⟩ := hin
  let lab := (_root_.Executable.labels exe).label
  have hg : lab x22L = lab x21L + Int64.ofNat 53 := label_labelGap_lays hp hgap
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)}, blockAt cells l k off b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)}, blockAt cells l k 0 b = true →
      ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s (lab l) b :=
    fun h s he hn => by simpa using code h s he hn
  refine (fn_segW (N := fN lab cP cA m) (E := fun _ : Unit => fE lab cP cA m) (fun i => ?_) FN.ts).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case ts =>
    refine test_ndW hF (fun s he hn => code bts s he hn) hWts fun σ c hJ af =>
      ⟨c, .refl c, .inl ⟨FN.je, ?_, rfl, ?_⟩⟩
    · show lab x21L + 51 = lab x21L + Int64.ofNat 48 + Int64.ofNat 3
      rw [Int64.add_assoc]; rfl
    · obtain ⟨hc, hr, hms⟩ := hJ
      refine ⟨hc, hr, hms, ?_⟩
      rw [testStep_zf, BitVec.and_self]
      simpa only [beq_eq_false_iff_ne, ne_eq] using hr.ne_zero
  case je =>
    refine seg_ndW (by simp [jeB]) jeB_ok hF hR (by omega) hhi (fun s he hn => code bje s he hn) hWje
      fun σ c hJ => ⟨c, .refl c, .inl ⟨FN.x22, ?_, rfl, hJ.1, hJ.2.1, hJ.2.2.1⟩⟩
    obtain ⟨-, -, -, hz⟩ := hJ
    show lab x22L = (arun lab jeB ⟨lab x21L + 51, oW, σ⟩).pc
    rw [jeB_run]
    simp only [hz, hg, Bool.false_eq_true, ite_false, Int64.add_assoc]; rfl
  case x22 =>
    refine seg_ndW (by simp [x22B]) x22B_ok hF hR (by omega) hhi (fun s he hn => code0 b22 s he hn) hWx22
      fun σ c hJ => ⟨c, .refl c, .inl ⟨FN.fl, ?_, rfl, ?_⟩⟩
    · obtain ⟨-, hr, -⟩ := hJ
      have hm : σ.regs.rax.toBitVec.msb = true := by
        have := hr.slt; simpa [BitVec.slt_zero_eq_msb] using this
      show lab flL = (arun lab x22B ⟨lab x22L, oW, σ⟩).pc
      rw [x22B_run]; simp only [hm, ite_true]
    · obtain ⟨rfl, -, h16, h8⟩ := hJ
      show c = c ∧ MS cA m (arun lab x22B ⟨lab x22L, oW, σ⟩).σ
      rw [x22B_run]
      exact ⟨rfl, by simp [upd, h16], by simp [upd, h8]⟩
  case fl =>
    refine seg_ndW (by simp [flB]) flB_ok hF hR hlo hhi (fun s he hn => code0 bfl s he hn) hWfl
      fun σ c hJ => ⟨c, .refl c, .inr ⟨(), ?_, ?_, ?_⟩⟩
    · show lab "scc_rt_abort" = (arun lab flB ⟨lab flL, oW, σ⟩).pc
      rw [flB_run]
    · show SO.le ⟨-72, [(.rbp, 0)]⟩ (arun lab flB ⟨lab flL, oW, σ⟩).so = true
      rw [flB_run]; rfl
    · obtain ⟨rfl, h16, h8⟩ := hJ
      show c = c ∧ (arun lab flB ⟨lab flL, oW, σ⟩).σ.regs.get64 .rdi = 5#64 ∧
        (arun lab flB ⟨lab flL, oW, σ⟩).σ.slot (-72) = raT lab ".Lwc_main" ∧
        MS cA m (arun lab flB ⟨lab flL, oW, σ⟩).σ
      rw [flB_run]
      refine ⟨rfl, ?_, ?_, ?_, ?_⟩
      · simp (disch := decide) only [Reg64s.get64_set64_self, Reg64s.get64_set64_ne]
      · simp only [upd_apply, ↓reduceIte, raT, Int64.toBitVec_add]; rfl
      · simp [upd, h16]
      · simp [upd, h8]

/-- **Main after a refused clone does not return**: `seg_failW`, then the
call of `scc_rt_abort(5)` (`seg_jabort5W`, the dispatcher in `[-24, 16)`
below the pushed return address at `-72`, the return address
`raT lab ".Lwc_main"`), given the threads abort path's obligations there
per caller state (`hstub`). -/
theorem seg_spawnFailW {cells : List (Directive × Nat)} {kp : Nat} (hp : Lays exe cells kp)
    (hend : endPc = endOf exe cells kp) (hin : failIn cells = true)
    {W : Frag isa} {K : State → State → Prop} {Q : Frag isa}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -104) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hWts : NodeW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .ts))
    (hWje : BlkW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .je) jeB)
    (hWx22 : BlkW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .x22) x22B)
    (hWfl : BlkW W K exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fE (_root_.Executable.labels exe).label cP cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-72 - 8) (-24) 16)
        (fun m' => F m' ∧ CKept R (-72 - 8) (-24) 16 m0 m' ∧ Abs R ⟨-72, [(.rbp, 0)]⟩ m0 σC) c0
        (raT (_root_.Executable.labels exe).label ".Lwc_main")) :
    SegW W K p lbl ms (At exe endPc R F (fN (_root_.Executable.labels exe).label cP cA m .ts)) Q :=
  (seg_failW hp hend hin hF hR (by omega) hhi hWts hWje hWx22 hWfl).seq
    (Abort.Disp.seg_jabort5W (nC := fE (_root_.Executable.labels exe).label cP cA m) rfl
      (fun σ c h => h.2.1) (fun σ c h => h.2.2.1) hF hR (by show R.lo ≤ -72 - 32; omega)
      (by show (-72 : Int) + 8 ≤ R.hi; omega) (by show (-72 : Int) % 8 = 0; decide) hK hstub)

end Seg

end Spike.Lib.X64.WakePh.SpawnFail

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.wake_failIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.wake_failIn

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.seg_failW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.seg_failW

/-- info: 'Spike.Lib.X64.WakePh.SpawnFail.seg_spawnFailW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.SpawnFail.seg_spawnFailW

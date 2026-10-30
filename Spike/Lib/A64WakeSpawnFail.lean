/-
**wake.w on AArch64: main after a refused `clone`** (the
spawn's refusal half; the parent half is `Spike/Lib/A64WakeParent.lean`):
back from main's `clone` (`ThreadsAb.cloneAt`) with a refusal in `x0`
(`ThreadsAb.CloneRef`: `-EAGAIN` or `-ENOMEM`), main runs

    cbz x0, .child9                 -- not taken (x0 ≠ 0)
    .clone9: str x0, [sp, #48]; ldr x9, [sp, #48]; movz x10, #0
             subs xzr, x9, x10; b.lt .1_spawnfail5   -- taken (x0 < 0)
    .1_spawnfail5: movz x0, #5; bl scc_rt_abort

in its frame (`sp` at offset `-80`), and the call `scc_rt_abort(5)` does not
return (`Abort.Disp.seg_jabort5W`, the dispatcher in the 48 bytes below the
frame), with the return address `ThreadsAb.raT lab pfx` that the `bl` writes
carried to the threads stub.

- `subs0_lt`: `subs xzr, x, #0` of a negative `x` takes `b.lt`.
- `flB`: `.1_spawnfail5`'s block.
- `fN pfx lab cP`: the nodes (`FN`: `cb`, `cl`, `fl`); `fE pfx lab cP`: the
  exit, at `scc_rt_abort` with `x0 = 5`, `x30 = raT lab pfx`.
- `seg_failW`: from `fN .cb` to `fE` inside `W`, given the three blocks' code
  and the label gap from the `cbz` to `.clone9`.
- `seg_spawnFailW`: from `fN .cb` to any fragment: `seg_failW` then
  `seg_jabort5W`, given the threads abort path's obligations (`StubTW`) per
  caller state.
- `failIn`, `wake_failIn`: the blocks in wake's program;
  `seg_spawnFailW_wake`: `seg_spawnFailW` in any valid layout of `wakeProg`.
-/
import Spike.Lib.A64WakeParent
import Spike.Lib.A64AbortThreadsW
import Spike.Lib.A64ThreadsAb

namespace Spike.Lib.A64.Flow.Worker.Wake.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (oP cbPT_run cbP_ok cbP_run cl cl_ok cl_run clT_run)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.ThreadsAb (CloneRef raT)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- `.1_spawnfail5`: the threads code and the call of the dispatcher. -/
def flB : List Directive := parseAArch64("movz x0, #5
bl scc_rt_abort")

block_spec flB (-80) 0 oP flB

/-- `subs xzr, x, #0` of a negative `x`: `n ≠ v`, `b.lt` taken. -/
theorem subs0_lt {x : BitVec 64} (h : x.slt 0#64 = true) :
    (StatusFlags.subs x x 0#64).n ≠ (StatusFlags.subs x x 0#64).v := by
  have hm : x.msb = true := by simpa [BitVec.slt_zero_eq_msb] using h
  simp [StatusFlags.subs, hm]

/-- The `bl`'s return address, eight bytes past its block's label. -/
theorem ofInt_add8 (l : Int64) :
    BitVec.ofInt 64 ((l.toInt + 4 + 4).bmod 18446744073709551616) = (l + 8).toBitVec := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_ofInt]
  have h1 : (l + 8).toBitVec.toInt = (l + 8).toInt := rfl
  rw [h1, Int64.toInt_add]
  simp only [Int.bmod_bmod]
  congr 1
  rw [show Int64.toInt 8 = 8 from rfl]; omega

/-! ## The nodes -/

/-- The refusal path's internal nodes. -/
inductive FN where
  | cb | cl | fl

/-- **Main's slots of the spawn's words**: the box's cell `cA` at `-72` and
main's `ThreadId` word `m` at `-80` (`WcSp4.FrW`'s), which the source's
`c` and `p` are placed at once the path reuses `x9` and `x10`. -/
def MS (cA m : BitVec 64) (σ : AS) : Prop := σ.slot (-72) = cA ∧ σ.slot (-80) = m

variable (pfx : String) (lab : Label → Int64) (cP : Ctl) (cA m : BitVec 64)

/-- **The refusal path's nodes**: past the clone (`cb`, `x0` a refusal),
`.clone9` (`cl`, `x0` a refusal), `.1_spawnfail5` (`fl`); the source at
`cP` and main's slots `MS cA m` throughout. -/
def fN : FN → ND
  | .cb => ⟨lab (pfx ++ ".sp6") + Int64.ofNat (4 * 13) + 4, oP,
      fun σ c => c = cP ∧ CloneRef σ.regs.X0.toBitVec ∧ MS cA m σ⟩
  | .cl => ⟨lab (pfx ++ ".clone9"), oP, fun σ c => c = cP ∧ CloneRef σ.regs.X0.toBitVec ∧ MS cA m σ⟩
  | .fl => ⟨lab (pfx ++ ".1_spawnfail5"), oP, fun σ c => c = cP ∧ MS cA m σ⟩

/-- **The exit**: the call of `scc_rt_abort` with `x0 = 5` and the return
address `raT lab pfx`, in main's frame with its slots `MS cA m`. -/
def fE : ND :=
  ⟨lab "scc_rt_abort", oP, fun σ c => c = cP ∧ σ.regs.X0 = 5 ∧ σ.regs.X30.toBitVec = raT lab pfx ∧ MS cA m σ⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {pfx : String} {cP : Ctl} {cA m : BitVec 64}

/-- **Main after a refused clone is one segment inside `W`**, from `fN .cb`
to the call of `scc_rt_abort(5)` (`fE`): the `cbz` not taken (a refusal is
not `0`), the `b.lt` taken (a refusal is negative), `.1_spawnfail5`'s
`bl`. -/
theorem seg_failW {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi)
    (hcb : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cb).pc (cb pfx))
    (hcl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cl).pc (cl pfx))
    (hfl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .fl).pc flB)
    (hg : (_root_.Executable.labels exe).label (pfx ++ ".clone9") =
      (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 13) + 4 + 4)
    (hWcb : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cb) (cb pfx))
    (hWcl : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cl) (cl pfx))
    (hWfl : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .fl) flB) :
    SegW W K p lbl ms (At exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cb))
      (At exe endPc R F (fE pfx (_root_.Executable.labels exe).label cP cA m)) := by
  refine (fn_segW (N := fN pfx (_root_.Executable.labels exe).label cP cA m)
    (E := fun _ : Unit => fE pfx (_root_.Executable.labels exe).label cP cA m) (fun i => ?_) FN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case cb =>
    refine seg_ndW (by simp [cb]) cbP_ok hF hR hal hlo hhi hcb hWcb fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hc, hr, hms⟩ := hJ
    rw [fN, cbP_run, cbPT_run]
    have hne : ¬ σ.regs.X0.toBitVec = 0 := hr.ne_zero
    refine .inl ⟨FN.cl, ?_, rfl, hc, ?_, ?_⟩
    · simp only [fN, rl, Reg64s.getRegOrZr]
      simp [hne, Reg64s.getRegOrZr, Reg64s.getXReg, hg]
      exact fun h => (hne h).elim
    · simpa [Reg64s.getRegOrZr] using hr
    · simpa [MS] using hms
  case cl =>
    refine seg_ndW (by simp [cl]) cl_ok hF hR hal hlo hhi hcl hWcl fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hc, hr, hms⟩ := hJ
    rw [fN, cl_run, clT_run]
    have hlt := subs0_lt hr.slt
    refine .inl ⟨FN.fl, ?_, rfl, ?_⟩
    · have hm : σ.regs.X0.toBitVec.msb = true := by simpa [BitVec.slt_zero_eq_msb] using hr.slt
      simp [fN, rl, Spike.Lib.upd_apply, hlt, hm]
    · simp_all [fN, MS, Spike.Lib.upd_apply]
  case fl =>
    refine seg_ndW (by simp [flB]) flB_ok hF hR hal hlo hhi hfl hWfl fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [fN, flB_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩
    · simp [fE]
    · refine ⟨hJ.1, rfl, ofInt_add8 _, ?_⟩
      simpa [MS] using hJ.2

/-- **Main after a refused clone does not return**: `seg_failW`, then the
call of `scc_rt_abort(5)` (`seg_jabort5W`, the dispatcher in the 48 bytes
below main's frame, the return address `raT lab pfx`), given the threads
abort path's obligations there per caller state (`hstub`). -/
theorem seg_spawnFailW {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hcb : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cb).pc (cb pfx))
    (hcl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cl).pc (cl pfx))
    (hfl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .fl).pc flB)
    (hg : (_root_.Executable.labels exe).label (pfx ++ ".clone9") =
      (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 13) + 4 + 4)
    (hWcb : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cb) (cb pfx))
    (hWcl : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cl) (cl pfx))
    (hWfl : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fE pfx (_root_.Executable.labels exe).label cP cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-80) (-48) 0)
        (fun m => F m ∧ CKept R (-80) (-48) 0 m0 m ∧ Abs R oP m0 σC) c0
        (raT (_root_.Executable.labels exe).label pfx)) :
    SegW W K p lbl ms (At exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cb)) Q :=
  (seg_failW hF hR hal (by omega) hhi hcb hcl hfl hg hWcb hWcl hWfl).seq
    (Abort.Disp.seg_jabort5W (nC := fE pfx (_root_.Executable.labels exe).label cP cA m) rfl
      (fun σ c ⟨_, h5, _⟩ => by rw [h5]; rfl) (fun σ c ⟨_, _, h, _⟩ => h) hF hR hal
      (by show R.lo ≤ -80 - 48; omega) (by show (-80 : Int) < R.hi; omega) (by show (-80 : Int) % 16 = 0; decide) hK hstub)

end Seg

/-! ## In wake's program -/

/-- The refusal path's blocks in wake's program (the `cbz`, `.clone9`'s
first block and the label gap are `Parent.parentIn`'s). -/
abbrev failIn : Bool :=
  blockAt wakeProg (pfxM ++ ".sp6") 14 (cb pfxM) && labelGap wakeProg (pfxM ++ ".sp6") (pfxM ++ ".clone9") 15 &&
    blockAt wakeProg (pfxM ++ ".clone9") 0 (cl pfxM) && blockAt wakeProg (pfxM ++ ".1_spawnfail5") 0 flB

theorem wake_failIn : failIn = true := by decide +kernel

section Wake

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {cA m : BitVec 64}

/-- **`seg_spawnFailW` in any valid layout of `wakeProg`**: every code fact
and the label gap decided (`wake_failIn`). -/
theorem seg_spawnFailW_wake (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -128) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hWcb : BlkW W K exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .cb) (cb pfxM))
    (hWcl : BlkW W K exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .cl) (cl pfxM))
    (hWfl : BlkW W K exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fE pfxM (_root_.Executable.labels exe).label cP cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-80) (-48) 0)
        (fun m => F m ∧ CKept R (-80) (-48) 0 m0 m ∧ Abs R oP m0 σC) c0
        (raT (_root_.Executable.labels exe).label pfxM)) :
    SegW W K p lbl ms (At exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .cb)) Q := by
  have hin := wake_failIn
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hcb, hgap⟩, hcl⟩, hfl⟩ := hin
  have hg := label_labelGap hp hgap
  rw [show 4 * 15 = 4 * (13 + 1 + 1) from rfl, ofNat4_succ, ofNat4_succ] at hg
  exact seg_spawnFailW hF hR hal hlo hhi hK
    (code_of hp hend hcb (by simp only [fN, ofNat4_succ, ofNat4_zero]))
    (code_of hp hend hcl (ofNat4_zero _)) (code_of hp hend hfl (ofNat4_zero _)) hg hWcb hWcl hWfl hstub

end Wake

end Spike.Lib.A64.Flow.Worker.Wake.SpawnFail

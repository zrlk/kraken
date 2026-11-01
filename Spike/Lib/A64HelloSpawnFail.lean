/-
**hello.w on AArch64: main after a refused `clone`** (B4b,
the spawn's refusal half; the parent half is
`Spike/Lib/A64HelloParent.lean`): back from main's `clone` with a refusal
in `x0` (`ThreadsAb.CloneRef`: `-EAGAIN` or `-ENOMEM`), main runs

    cbz x0, .child13                 -- not taken (x0 ≠ 0)
    .clone13: str x0, [sp, #112]; ldr x9, [sp, #112]; movz x10, #0
              subs xzr, x9, x10; b.lt .1_spawnfail5   -- taken (x0 < 0)
    .1_spawnfail5: movz x0, #5; bl scc_rt_abort

in its frame (`sp` at offset `-144`), and the call `scc_rt_abort(5)` does
not return (`Abort.Disp.seg_jabort5W`, the dispatcher in the 48 bytes below
the frame), with the return address `ThreadsAb.raT lab pfx` that the `bl`
writes carried to the threads stub. wake.w's
(`Spike/Lib/A64WakeSpawnFail.lean`) at hello's frame of 144 and listing
(`SccCode.helloProg`); `subs0_lt` and `ofInt_add8` are wake's (generic).

- `flB`: `.1_spawnfail5`'s block.
- `MS cA m`: main's slots of the spawn's words, the cell `cA` at `-104`
  (`[sp, #40]`) and main's `ThreadId` word `m` at `-112` (`[sp, #32]`).
- `fN pfx lab cP`: the nodes (`FN`: `cb`, `cl`, `fl`); `fE pfx lab cP`: the
  exit, at `scc_rt_abort` with `x0 = 5`, `x30 = raT lab pfx`.
- `seg_failW`, `seg_spawnFailW`: as wake's.
- `failIn`, `hello_failIn`: the blocks in hello's program;
  `seg_spawnFailW_hello`: `seg_spawnFailW` in any valid layout of
  `helloProg`.

Deferred: wake's `A64SpawnFailAC` (the blocks inside `SFactsAC` at
`ThreadsAb.Ac`) needs a hello `ThreadsAb` (its pcs are wake's: `cloneAt =
.sp6 + 52`, `.clone9`); with B4c.
-/
import Spike.Lib.A64HelloParent
import Spike.Lib.A64WakeSpawnFail
import Spike.Lib.A64AbortThreadsW
import Spike.Lib.A64ThreadsAb

namespace Spike.Lib.A64.Flow.Worker.Hello.SpawnFail

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (oP cbPT_run cbP_ok cbP_run cl cl_ok cl_run clT_run)
open Spike.Lib.A64.Flow.Worker.Wake.SpawnFail (subs0_lt ofInt_add8)
open SccCode (helloProg)
open Spike.Lib.A64.ThreadsAb (CloneRef raT)

set_option linter.unusedSimpArgs false

/-! ## The blocks -/

/-- `.1_spawnfail5`: the threads code and the call of the dispatcher. -/
def flB : List Directive := parseAArch64("movz x0, #5
bl scc_rt_abort")

block_spec flB (-144) 0 oP flB

/-! ## The nodes -/

/-- The refusal path's internal nodes. -/
inductive FN where
  | cb | cl | fl

/-- **Main's slots of the spawn's words**: the box's cell `cA` at `-104` and
main's `ThreadId` word `m` at `-112` (hello's frame of 144), which the source's
`c` and `p` are placed at once the path reuses `x9` and `x10`. -/
def MS (cA m : BitVec 64) (σ : AS) : Prop := σ.slot (-104) = cA ∧ σ.slot (-112) = m

variable (pfx : String) (lab : Label → Int64) (cP : Ctl) (cA m : BitVec 64)

/-- **The refusal path's nodes**: past the clone (`cb`, `x0` a refusal),
`.clone13` (`cl`, `x0` a refusal), `.1_spawnfail5` (`fl`); the source at
`cP` and main's slots `MS cA m` throughout. -/
def fN : FN → ND
  | .cb => ⟨lab (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4, oP,
      fun σ c => c = cP ∧ CloneRef σ.regs.X0.toBitVec ∧ MS cA m σ⟩
  | .cl => ⟨lab (pfx ++ ".clone13"), oP, fun σ c => c = cP ∧ CloneRef σ.regs.X0.toBitVec ∧ MS cA m σ⟩
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
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hcb : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cb).pc (cb pfx))
    (hcl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cl).pc (cl pfx))
    (hfl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .fl).pc flB)
    (hg : (_root_.Executable.labels exe).label (pfx ++ ".clone13") =
      (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4 + 4)
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
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hcb : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cb).pc (cb pfx))
    (hcl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .cl).pc (cl pfx))
    (hfl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fN pfx (_root_.Executable.labels exe).label cP cA m .fl).pc flB)
    (hg : (_root_.Executable.labels exe).label (pfx ++ ".clone13") =
      (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4 + 4)
    (hWcb : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cb) (cb pfx))
    (hWcl : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cl) (cl pfx))
    (hWfl : BlkW W K exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fE pfx (_root_.Executable.labels exe).label cP cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-144) (-48) 0)
        (fun m => F m ∧ CKept R (-144) (-48) 0 m0 m ∧ Abs R oP m0 σC) c0
        (raT (_root_.Executable.labels exe).label pfx)) :
    SegW W K p lbl ms (At exe endPc R F (fN pfx (_root_.Executable.labels exe).label cP cA m .cb)) Q :=
  (seg_failW hF hR hal (by omega) hhi hcb hcl hfl hg hWcb hWcl hWfl).seq
    (Abort.Disp.seg_jabort5W (nC := fE pfx (_root_.Executable.labels exe).label cP cA m) rfl
      (fun σ c ⟨_, h5, _⟩ => by rw [h5]; rfl) (fun σ c ⟨_, _, h, _⟩ => h) hF hR hal
      (by show R.lo ≤ -144 - 48; omega) (by show (-144 : Int) < R.hi; omega)
      (by show (-144 : Int) % 16 = 0; decide) hK hstub)

end Seg

/-! ## In hello's program -/

/-- The refusal path's blocks in hello's program (the `cbz`, `.clone13`'s
first block and the label gap are `Parent.parentIn`'s). -/
abbrev failIn : Bool :=
  blockAt helloProg (pfxM ++ ".sp6") 26 (cb pfxM) &&
    labelGap helloProg (pfxM ++ ".sp6") (pfxM ++ ".clone13") 27 &&
    blockAt helloProg (pfxM ++ ".clone13") 0 (cl pfxM) && blockAt helloProg (pfxM ++ ".1_spawnfail5") 0 flB

theorem hello_failIn : failIn = true := by decide +kernel

section Hello

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {cA m : BitVec 64}

/-- **`seg_spawnFailW` in any valid layout of `helloProg`**: every code fact
and the label gap decided (`hello_failIn`). -/
theorem seg_spawnFailW_hello (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hWcb : BlkW W K exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .cb) (cb pfxM))
    (hWcl : BlkW W K exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .cl) (cl pfxM))
    (hWfl : BlkW W K exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fE pfxM (_root_.Executable.labels exe).label cP cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-144) (-48) 0)
        (fun m => F m ∧ CKept R (-144) (-48) 0 m0 m ∧ Abs R oP m0 σC) c0
        (raT (_root_.Executable.labels exe).label pfxM)) :
    SegW W K p lbl ms (At exe endPc R F (fN pfxM (_root_.Executable.labels exe).label cP cA m .cb)) Q := by
  have hin := hello_failIn
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hcb, hgap⟩, hcl⟩, hfl⟩ := hin
  have hg := label_labelGap hp hgap
  rw [show 4 * 27 = 4 * (25 + 1 + 1) from rfl, ofNat4_succ, ofNat4_succ] at hg
  exact seg_spawnFailW hF hR hal hlo hhi hK
    (code_of hp hend hcb (by simp only [fN, ofNat4_succ, ofNat4_zero]))
    (code_of hp hend hcl (ofNat4_zero _)) (code_of hp hend hfl (ofNat4_zero _)) hg hWcb hWcl hWfl hstub

end Hello

end Spike.Lib.A64.Flow.Worker.Hello.SpawnFail

/--
info: 'Spike.Lib.A64.Flow.Worker.Hello.SpawnFail.seg_spawnFailW_hello' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.SpawnFail.seg_spawnFailW_hello

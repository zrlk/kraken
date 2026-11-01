/-
**hello.w on AArch64: main after a refused `clone`, the slice's slots carried** (AArch64): `A64HelloSpawnFail`'s nodes
with main's
slots of all five of the spawn's packet words. hello's `spawnTermH` reads `p = sl ++ [c, me]`, so placing the
source on the refusal path (`PlacedSE`, `placedSE_slotsH`) needs the slice's words at `-144`, `-128`, `-120`
besides the cell at `-104` and main's id at `-112`; `Hello.SpawnFail.MS` carries the latter two only (wake's packet
is `(c, me)`). The blocks store only to `-32`, so every slot is kept; the proofs are `A64HelloSpawnFail`'s.

- `MSS sl cA m`: main's slots `sl.1` at `-144`, `sl.2.2.1` at `-128`, `sl.2.2.2` at `-120`, `cA` at `-104`, `m`
  at `-112` (`FrWH`'s, which `RefH.refuse_atH` reads).
- `fNS pfx lab cP sl`, `fES pfx lab cP sl`: `SpawnFail.fN`/`fE` at `MSS`.
- `seg_failWS`, `seg_spawnFailWS`, `seg_spawnFailWS_hello`: as `A64HelloSpawnFail`'s (`failIn` and
  `hello_failIn` reused).

`A64HelloSpawnFail` is unchanged. No absolute address appears in this file.
-/
import Spike.Lib.A64HelloSpawnFail

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

/-! ## The nodes -/

/-- **Main's slots of the spawn's five packet words**: the slice's words `sl.1` at `-144`, `sl.2.2.1` at `-128`
and `sl.2.2.2` at `-120`, the box's cell `cA` at `-104` and main's `ThreadId` word `m` at `-112` (hello's frame of
144). -/
def MSS (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) (cA m : BitVec 64) (σ : AS) : Prop :=
  σ.slot (-144) = sl.1 ∧ σ.slot (-128) = sl.2.2.1 ∧ σ.slot (-120) = sl.2.2.2 ∧ σ.slot (-104) = cA ∧
    σ.slot (-112) = m

variable (pfx : String) (lab : Label → Int64) (cP : Ctl) (sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64)
  (cA m : BitVec 64)

/-- **The refusal path's nodes at `MSS`** (`fN`'s). -/
def fNS : FN → ND
  | .cb => ⟨lab (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4, oP,
      fun σ c => c = cP ∧ CloneRef σ.regs.X0.toBitVec ∧ MSS sl cA m σ⟩
  | .cl => ⟨lab (pfx ++ ".clone13"), oP, fun σ c => c = cP ∧ CloneRef σ.regs.X0.toBitVec ∧ MSS sl cA m σ⟩
  | .fl => ⟨lab (pfx ++ ".1_spawnfail5"), oP, fun σ c => c = cP ∧ MSS sl cA m σ⟩

/-- **The exit at `MSS`** (`fE`'s): the call of `scc_rt_abort` with `x0 = 5` and the return address `raT lab pfx`.
-/
def fES : ND :=
  ⟨lab "scc_rt_abort", oP, fun σ c => c = cP ∧ σ.regs.X0 = 5 ∧ σ.regs.X30.toBitVec = raT lab pfx ∧ MSS sl cA m σ⟩

/-! ## The segment -/

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {pfx : String} {cP : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {cA m : BitVec 64}

/-- **Main after a refused clone is one segment inside `W`**, from `fNS .cb`
to the call of `scc_rt_abort(5)` (`fES`): the `cbz` not taken (a refusal is
not `0`), the `b.lt` taken (a refusal is negative), `.1_spawnfail5`'s
`bl`. -/
theorem seg_failWS {W : Frag isaLSE2} {K : State → State → Prop}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    (hcb : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cb).pc (cb pfx))
    (hcl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cl).pc (cl pfx))
    (hfl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .fl).pc flB)
    (hg : (_root_.Executable.labels exe).label (pfx ++ ".clone13") =
      (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4 + 4)
    (hWcb : BlkW W K exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cb) (cb pfx))
    (hWcl : BlkW W K exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cl) (cl pfx))
    (hWfl : BlkW W K exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .fl) flB) :
    SegW W K p lbl ms (At exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cb))
      (At exe endPc R F (fES pfx (_root_.Executable.labels exe).label cP sl cA m)) := by
  refine (fn_segW (N := fNS pfx (_root_.Executable.labels exe).label cP sl cA m)
    (E := fun _ : Unit => fES pfx (_root_.Executable.labels exe).label cP sl cA m) (fun i => ?_) FN.cb).mono_post
    fun _ _ ⟨_, h⟩ => h
  cases i
  case cb =>
    refine seg_ndW (by simp [cb]) cbP_ok hF hR hal hlo hhi hcb hWcb fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hc, hr, hms⟩ := hJ
    rw [fNS, cbP_run, cbPT_run]
    have hne : ¬ σ.regs.X0.toBitVec = 0 := hr.ne_zero
    refine .inl ⟨FN.cl, ?_, rfl, hc, ?_, ?_⟩
    · simp only [fNS, rl, Reg64s.getRegOrZr]
      simp [hne, Reg64s.getRegOrZr, Reg64s.getXReg, hg]
      exact fun h => (hne h).elim
    · simpa [Reg64s.getRegOrZr] using hr
    · simpa [MSS] using hms
  case cl =>
    refine seg_ndW (by simp [cl]) cl_ok hF hR hal hlo hhi hcl hWcl fun σ c hJ => ⟨c, .refl c, ?_⟩
    obtain ⟨hc, hr, hms⟩ := hJ
    rw [fNS, cl_run, clT_run]
    have hlt := subs0_lt hr.slt
    refine .inl ⟨FN.fl, ?_, rfl, ?_⟩
    · have hm : σ.regs.X0.toBitVec.msb = true := by simpa [BitVec.slt_zero_eq_msb] using hr.slt
      simp [fNS, rl, Spike.Lib.upd_apply, hlt, hm]
    · simp_all [fNS, MSS, Spike.Lib.upd_apply]
  case fl =>
    refine seg_ndW (by simp [flB]) flB_ok hF hR hal hlo hhi hfl hWfl fun σ c hJ => ⟨c, .refl c, ?_⟩
    rw [fNS, flB_run]
    refine .inr ⟨(), ?_, rfl, ?_⟩
    · simp [fES]
    · refine ⟨hJ.1, rfl, ofInt_add8 _, ?_⟩
      simpa [MSS] using hJ.2

/-- **Main after a refused clone does not return**: `seg_failWS`, then the
call of `scc_rt_abort(5)` (`seg_jabort5W`, the dispatcher in the 48 bytes
below main's frame, the return address `raT lab pfx`), given the threads
abort path's obligations there per caller state (`hstub`). -/
theorem seg_spawnFailWS {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hcb : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cb).pc (cb pfx))
    (hcl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cl).pc (cl pfx))
    (hfl : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .fl).pc flB)
    (hg : (_root_.Executable.labels exe).label (pfx ++ ".clone13") =
      (_root_.Executable.labels exe).label (pfx ++ ".sp6") + Int64.ofNat (4 * 25) + 4 + 4)
    (hWcb : BlkW W K exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cb) (cb pfx))
    (hWcl : BlkW W K exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cl) (cl pfx))
    (hWfl : BlkW W K exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fES pfx (_root_.Executable.labels exe).label cP sl cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-144) (-48) 0)
        (fun m => F m ∧ CKept R (-144) (-48) 0 m0 m ∧ Abs R oP m0 σC) c0
        (raT (_root_.Executable.labels exe).label pfx)) :
    SegW W K p lbl ms (At exe endPc R F (fNS pfx (_root_.Executable.labels exe).label cP sl cA m .cb)) Q :=
  (seg_failWS hF hR hal (by omega) hhi hcb hcl hfl hg hWcb hWcl hWfl).seq
    (Abort.Disp.seg_jabort5W (nC := fES pfx (_root_.Executable.labels exe).label cP sl cA m) rfl
      (fun σ c ⟨_, h5, _⟩ => by rw [h5]; rfl) (fun σ c ⟨_, _, h, _⟩ => h) hF hR hal
      (by show R.lo ≤ -144 - 48; omega) (by show (-144 : Int) < R.hi; omega)
      (by show (-144 : Int) % 16 = 0; decide) hK hstub)

end Seg

/-! ## In hello's program -/

section Hello

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {R : Spike.Lib.Region} {F : MachineData → Prop} {cP : Ctl} {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64}
  {cA m : BitVec 64}

/-- **`seg_spawnFailWS` in any valid layout of `helloProg`**: every code fact
and the label gap decided (`hello_failIn`). -/
theorem seg_spawnFailWS_hello (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {W : Frag isaLSE2} {K : State → State → Prop} {Q : Frag isaLSE2}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hWcb : BlkW W K exe endPc R F (fNS pfxM (_root_.Executable.labels exe).label cP sl cA m .cb) (cb pfxM))
    (hWcl : BlkW W K exe endPc R F (fNS pfxM (_root_.Executable.labels exe).label cP sl cA m .cl) (cl pfxM))
    (hWfl : BlkW W K exe endPc R F (fNS pfxM (_root_.Executable.labels exe).label cP sl cA m .fl) flB)
    (hstub : ∀ m0 σC c0, (fES pfxM (_root_.Executable.labels exe).label cP sl cA m).J σC c0 →
      Abort.Disp.StubTW W K p lbl ms exe endPc (R.callee (-144) (-48) 0)
        (fun m => F m ∧ CKept R (-144) (-48) 0 m0 m ∧ Abs R oP m0 σC) c0
        (raT (_root_.Executable.labels exe).label pfxM)) :
    SegW W K p lbl ms (At exe endPc R F (fNS pfxM (_root_.Executable.labels exe).label cP sl cA m .cb)) Q := by
  have hin := hello_failIn
  simp only [failIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨hcb, hgap⟩, hcl⟩, hfl⟩ := hin
  have hg := label_labelGap hp hgap
  rw [show 4 * 27 = 4 * (25 + 1 + 1) from rfl, ofNat4_succ, ofNat4_succ] at hg
  exact seg_spawnFailWS hF hR hal hlo hhi hK
    (code_of hp hend hcb (by simp only [fNS, ofNat4_succ, ofNat4_zero]))
    (code_of hp hend hcl (ofNat4_zero _)) (code_of hp hend hfl (ofNat4_zero _)) hg hWcb hWcl hWfl hstub

end Hello

end Spike.Lib.A64.Flow.Worker.Hello.SpawnFail

/--
info: 'Spike.Lib.A64.Flow.Worker.Hello.SpawnFail.seg_spawnFailWS_hello' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Spike.Lib.A64.Flow.Worker.Hello.SpawnFail.seg_spawnFailWS_hello

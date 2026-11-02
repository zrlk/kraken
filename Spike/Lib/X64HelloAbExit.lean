/-
**hello.w on x86-64: the abort phase's `exit_group` is at an abort site** (the twin of
`Spike/Lib/HelloAbExit.lean`; `X64HelloStep1Sys.AbExit`, the premise of `sysStepP_of`), reduced to two facts. At
the instance the abort phase is `Worker.AbW exe`: the pc is the `write(2, …)` system call of `scc_rt_abort_write`
(`Abort.pcSys … write`) or its exit call (`scc_rt_abort_write_exit`).

- `ExitSite exe μ`: the exit call's address is an abort site of `μ`; `exitSite_P`: so at the canonical target's
  marks of the placed layout (`X64HelloCompatI.μP`, the `writeErr` site: `marks_target`, `PlaceWX.abortAt_eq`,
  `site_ofH` at `hello_exitLabel`).
- `SvcNoExit D exe`: at the `write(2, …)` call's pc no worker state decodes to an `exit_group` (the call there is
  the stub's `write`); `svcNoExit_of`: from the worker's fragment `NNH`, whose condition pins the stub's
  `exit_group` to its exit label (`AbC`), the exit label off the `write`'s pc (`exit_ne_svc`,
  `Abort.Code.hexit`).
- `abExit_of`: `AbExit D μ (AbW exe)` from the two.
- `abExit_DR`: `AbExit` at the instance's worker side `helloDR`, from the exit site alone (`exitSite_P` at the
  placed layout).

## Differences from the AArch64 version

- The stub's `write` is its `syscall` at `entry + 34` (`Abort.pcSys`; AArch64: the `svc`, `Abort.pcSvc`), the
  exit call at `entry + 52` (`Abort.Code.hexit`; AArch64: four instructions past the `svc`).
- `hello_exitLabel` is the `writeErr` exit's membership in the sites' labels (`siteLabels Λ`), the form the
  x86-64 `X64HelloCompatI.site_ofH` reads (AArch64: the label's directive in `helloProg`); `exitSite_P` needs no
  `o.prog = helloProg` and its parse is `cellsOf asm = some o.prog`.
- AArch64's `sysStepP_ofX` has no consumer and is not twinned.
-/
import Spike.Lib.X64HelloStep1Sys
import Spike.Lib.X64HelloCompatI
import Spike.Lib.X64HelloWorkerRR

namespace Spike.Lib.X64HelloAbExit

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloW1 (WSideH)
open Spike.Lib.X64HelloStep1Sys (AbExit)
open Spike.Lib.X64.Flow.Worker (AbW)
open SccCode (helloCells)

/-! ## The two facts -/

/-- **The exit call of `scc_rt_abort_write` is an abort site of `μ`.** -/
def ExitSite (exe : _root_.Executable) (μ : Marks) : Prop :=
  ∃ k, μ.abortAt k = some ((_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.exit).toBitVec.toNat

/-- **No `exit_group` at the stub's `write(2, …)` call**: a worker state at its pc decodes to no `exit_group`. -/
def SvcNoExit {ι : Type} (D : WSideH ι) (exe : _root_.Executable) : Prop :=
  ∀ w s c fs v, D.Wi w s c fs →
    s.st.2 = Spike.Lib.X64.Abort.pcSys (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write →
    abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.exitGroup v)

/-! ## The reduction -/

/-- **`AbExit` at the abort phase `AbW exe`** from the exit call's abort site and no `exit_group` at the stub's
`write`. -/
theorem abExit_of {ι : Type} {D : WSideH ι} {exe : _root_.Executable} {μ : Marks} (hx : ExitSite exe μ)
    (hsvc : SvcNoExit D exe) : AbExit D μ (AbW exe) := by
  intro w s c fs v hW hab ha hd
  rcases hab with hpc | hpc
  · exact absurd hd (hsvc w s c fs v hW hpc ha)
  · obtain ⟨k, hk⟩ := hx
    exact ⟨k, _, hk, by show s.st.2.toBitVec.toNat = _; rw [hpc]⟩

/-! ## The exit site at the placed layout -/

/-- **The `writeErr` exit's label is a site label** (the form `X64HelloCompatI.site_ofH` reads). -/
theorem hello_exitLabel (Λ : Scc.Sem.Layout) : Λ.abortLbl .writeErr ∈ Scc.Cert.Rt.X64.siteLabels Λ := by
  simp [Scc.Cert.Rt.X64.siteLabels]

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {H : Scc.Sem.Hooks isa} {E : Scc.Sem.Entry} {asm : Scc.Sem.X64.Asm}

/-- **The exit call is the `writeErr` site** of the canonical target's marks at the placed layout. -/
theorem exitSite_P (hpa : Scc.Sem.X64.cellsOf asm = some o.prog) :
    ExitSite (RuntimeLayout.ofPlaceWX hp i).exe (X64HelloCompatI.μP hp i H E asm) := by
  refine ⟨.writeErr, ?_⟩
  rw [X64HelloCompatI.μP, Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target _ hpa, PlaceWX.abortAt_eq hp i]
  have h := X64HelloCompatI.site_ofH hp i (hello_exitLabel Λ0)
  rw [PlaceWX.abortLbl_of_placeWX hp] at h
  exact h

end Place

/-! ## No `exit_group` at the stub's `write`, from the worker's fragment -/

section Svc

variable {endPc : Int64} {exe : _root_.Executable}

/-- **The stub's exit call is not its `write`**: the exit label is `18` bytes past the `write`'s `syscall`
(`Abort.Code.hexit`). -/
theorem exit_ne_svc [Kraken.Executable.ValidLayout exe] {kp : Nat} (hl : Scc.Cert.Rt.X64.Lays exe helloCells kp)
    (hend : endPc = Scc.Cert.Rt.X64.endOf exe helloCells kp) :
    (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.exit ≠
      Spike.Lib.X64.Abort.pcSys (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write := by
  have hc : (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.exit =
      (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.entry + 52 :=
    (Scc.Cert.Rt.X64.Abort.code_stubs (c0 := ⟨.ret (.var "x"), [], none⟩) hl hend SccCode.hello_abort .write).hexit
  rw [hc]
  show _ ≠ (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.entry + 34
  generalize (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.entry = x
  intro h
  have h' := congrArg Int64.toBitVec h
  simp only [Int64.toBitVec_add] at h'
  have h52 : (52 : Int64).toBitVec = 52#64 := rfl
  have h34 : (34 : Int64).toBitVec = 34#64 := rfl
  rw [h52, h34] at h'
  bv_omega

/-- **`SvcNoExit` from the worker's fragment** (`NNH`: an `exit_group` of the abort stub is at its exit label,
`AbC`), the exit label off the `write`'s pc. -/
theorem svcNoExit_of {ι : Type} {D : WSideH ι}
    (hW : ∀ w s c fs, D.Wi w s c fs → Spike.Lib.X64.Flow.Worker.NNH exe endPc s)
    (hne : (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write.exit ≠
      Spike.Lib.X64.Abort.pcSys (_root_.Executable.labels exe).label Spike.Lib.X64.Abort.write) :
    SvcNoExit D exe := by
  intro w s c fs v hWi hpc ha hd
  rcases (hW w s c fs hWi).2.2.2 ha _ hd with h | ⟨_, _, h⟩ | h | ⟨_, h⟩
  · cases h
  · cases h
  · rcases h with ⟨_, _, _, h⟩ | ⟨h2, _⟩
    · cases h
    · exact hne (h2.symm.trans hpc)
  · exact h v rfl

/-- **`AbExit` at the worker side `helloDR`** (the instance's `D`): the exit call's abort site (`hx`,
`exitSite_P` at the placed layout) and `SvcNoExit` by `svcNoExit_of` at `helloDR_nn`. -/
theorem abExit_DR [Kraken.Executable.ValidLayout exe] {kp : Nat} {ι : Type}
    (hl : Scc.Cert.Rt.X64.Lays exe helloCells kp) (hend : endPc = Scc.Cert.Rt.X64.endOf exe helloCells kp)
    {SR : ι → Inv2Core.SpawnRec} {lbl : ι → WeakMem.AllocLabel → Option Nat}
    {ms : ι → List TermRun.Frame → MemSide isa} {P Z X : ι → FragS isa} {hK : ∀ w fs, (ms w fs).K = some abi}
    {hseg : ∀ w, HelloSegTCSX.SegTCSX (fun s c fs => Spike.Lib.X64.Flow.Worker.NNH exe endPc s ∧ Z w s c fs)
      (X w) X64HelloSrc.helloSrc (lbl w) (ms w) (P w) (fun _ _ _ => False)}
    {cw : ι → TermRun.Word} {bufL : ι → WeakMem.AllocLabel} {nB mB : ι → Nat} {μ : Marks}
    (hx : ExitSite exe μ) :
    AbExit (X64HelloWorkerRR.helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) μ (AbW exe) :=
  abExit_of hx (svcNoExit_of (fun w s c fs h =>
    (X64HelloWorkerRR.helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).1)
    (exit_ne_svc hl hend))

end Svc

end Spike.Lib.X64HelloAbExit

/-- info: 'Spike.Lib.X64HelloAbExit.abExit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAbExit.abExit_of

/-- info: 'Spike.Lib.X64HelloAbExit.hello_exitLabel' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAbExit.hello_exitLabel

/-- info: 'Spike.Lib.X64HelloAbExit.exitSite_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAbExit.exitSite_P

/-- info: 'Spike.Lib.X64HelloAbExit.exit_ne_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAbExit.exit_ne_svc

/-- info: 'Spike.Lib.X64HelloAbExit.svcNoExit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAbExit.svcNoExit_of

/-- info: 'Spike.Lib.X64HelloAbExit.abExit_DR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAbExit.abExit_DR

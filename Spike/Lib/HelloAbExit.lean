/-
**hello.w on AArch64: the abort phase's `exit_group` is at an abort site**
(`HelloStep1Sys.AbExit`, the premise of `sysStepP_of`), reduced to two
facts. At the instance the abort phase is `Worker.AbW exe`: the pc is the
`write(2, …)` system call of `scc_rt_abort_write` (`Abort.pcSvc … write`)
or its exit call (`scc_rt_abort_write_exit`).

- `ExitSite exe μ`: the exit call's address is an abort site of `μ`;
  `exitSite_P`: so at the canonical target's marks of the placed layout
  (`HelloCompatI.μP`, the `writeErr` site: `marks_target`,
  `PlaceW.abortAt_eq`, `site_ofH`).
- `SvcNoExit D exe`: at the `write(2, …)` call's pc no worker state
  decodes to an `exit_group` (the call there is the stub's `write`);
  `svcNoExit_of`: from the worker's fragment `NNH`, whose condition pins
  the stub's `exit_group` to its exit label (`AbC`), the exit label off the
  `write`'s pc (`exit_ne_svc`, `Abort.Code.hexit`).
- `abExit_of`: `AbExit D μ (AbW exe)` from the two.
- `sysStepP_ofX`: `sysStepP_of` with `AbExit` by `abExit_of`.
- `abExit_DR`: `AbExit` at the instance's worker side `helloDR`, from the
  exit site alone (`exitSite_P` at the placed layout).
-/
import Spike.Lib.HelloStep1Sys
import Spike.Lib.HelloCompatI

namespace Spike.Lib.HelloAbExit

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloStep1Sys (AbExit)
open Spike.Lib.A64.Flow.Worker (AbW)
open SccCode (helloProg)

/-! ## The two facts -/

/-- **The exit call of `scc_rt_abort_write` is an abort site of `μ`.** -/
def ExitSite (exe : _root_.Executable) (μ : Marks) : Prop :=
  ∃ k, μ.abortAt k = some ((_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write.exit).toBitVec.toNat

/-- **No `exit_group` at the stub's `write(2, …)` call**: a worker state at
its pc decodes to no `exit_group`. -/
def SvcNoExit {ι : Type} (D : WSideH ι) (exe : _root_.Executable) : Prop :=
  ∀ w s c fs v, D.Wi w s c fs →
    s.st.2 = Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write →
    abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.exitGroup v)

/-! ## The reduction -/

/-- **`AbExit` at the abort phase `AbW exe`** from the exit call's abort site
and no `exit_group` at the stub's `write`. -/
theorem abExit_of {ι : Type} {D : WSideH ι} {exe : _root_.Executable} {μ : Marks} (hx : ExitSite exe μ)
    (hsvc : SvcNoExit D exe) : AbExit D μ (AbW exe) := by
  intro w s c fs v hW hab ha hd
  rcases hab with hpc | hpc
  · exact absurd hd (hsvc w s c fs v hW hpc ha)
  · obtain ⟨k, hk⟩ := hx
    exact ⟨k, _, hk, by show s.st.2.toBitVec.toNat = _; rw [hpc]⟩

/-! ## The exit site at the placed layout -/

/-- `scc_rt_abort_write_exit` is a label of hello's program. -/
theorem hello_exitLabel : Directive.label "scc_rt_abort_write_exit" ∈ helloProg :=
  HelloCompatI.mem_of_anyH (by decide +kernel)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {asm : String}

/-- **The exit call is the `writeErr` site** of the canonical target's marks
at the placed layout. -/
theorem exitSite_P (ho : o.prog = helloProg) (hpa : textProgram asm = .ok o.prog) :
    ExitSite (RuntimeLayout.ofPlaceW hp i).exe (HelloCompatI.μP hp i H E asm) := by
  refine ⟨.writeErr, ?_⟩
  rw [HelloCompatI.μP, Spike.Lib.A64.Flow.Worker.Wake.AbOffW.marks_target _ hpa, PlaceW.abortAt_eq hp i]
  exact HelloCompatI.site_ofH hp i ho hello_exitLabel

end Place

/-! ## `SysStepP` -/

section Step

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {Q : WakeRel} {μ : Marks} {D : WSideH Q.ι}
  {M : WakeM0.MSide Q.ι} {exe : _root_.Executable} {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0}
  {hem : HelloW1Store.NoWrite D} {r0 r1 : Q.ι → Range}

/-- **`sysStepP_of` at the abort phase `AbW exe`**, `AbExit` by `abExit_of`. -/
theorem sysStepP_ofX (hC : HelloAssembly.HelloCompat Q D M μ Λ arch (AbW exe) hcw hem)
    (hms : ∀ w fs, D.ms w fs = D.ms w []) (hown : Q.own = WakeOwn.wakeOwn)
    (hKR : Q.KR = HelloKRE.KRHE D r0 r1) (hx : ExitSite exe μ)
    (hsvc : SvcNoExit D exe) (hw1 : HelloStep1Sys.Write1StepP Q D μ Λ arch) :
    HelloStep1D.SysStepP Q D μ Λ arch :=
  HelloStep1Sys.sysStepP_of hC hms hown hKR (abExit_of hx hsvc) hw1

end Step

/-! ## No `exit_group` at the stub's `write`, from the worker's fragment -/

section Svc

variable {endPc : Int64} {exe : _root_.Executable}

/-- **The stub's exit call is not its `write`**: the exit label is four
instructions past the `write`'s `svc` (`Abort.Code.hexit`). -/
theorem exit_ne_svc [Kraken.Executable.ValidLayout exe] {kp : Nat} (hl : Scc.Cert.Rt.A64.Lays exe helloProg kp)
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe helloProg kp) :
    (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write.exit ≠
      Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write := by
  have hc : (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write.exit =
      Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write + 4 + 4 + 4 + 4 :=
    (Scc.Cert.Rt.A64.Abort.code_stubs (c0 := ⟨.ret (.var "x"), [], none⟩) hl hend SccCode.hello_abort .write).hexit
  rw [hc]
  generalize Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write = x
  intro h
  have h' := congrArg Int64.toBitVec h
  have h4 : (4 : Int64).toBitVec = 4#64 := rfl
  simp only [Int64.toBitVec_add, h4] at h'
  bv_omega

/-- **`SvcNoExit` from the worker's fragment** (`NNH`: an `exit_group` of
the abort stub is at its exit label, `AbC`), the exit label off the
`write`'s pc. -/
theorem svcNoExit_of {ι : Type} {D : WSideH ι}
    (hW : ∀ w s c fs, D.Wi w s c fs → Spike.Lib.A64.Flow.Worker.NNH exe endPc s)
    (hne : (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write.exit ≠
      Spike.Lib.A64.Abort.pcSvc (_root_.Executable.labels exe).label Spike.Lib.A64.Abort.write) :
    SvcNoExit D exe := by
  intro w s c fs v hWi hpc ha hd
  rcases (hW w s c fs hWi).2.2.2 ha _ hd with h | ⟨_, _, h⟩ | h | ⟨_, h⟩
  · cases h
  · cases h
  · rcases h with ⟨_, _, _, h⟩ | ⟨h2, _⟩
    · cases h
    · exact hne (h2.symm.trans hpc)
  · exact h v rfl

/-- **`AbExit` at the worker side `helloDR`** (the instance's `D`): the exit
call's abort site (`hx`, `exitSite_P` at the placed layout) and `SvcNoExit`
by `svcNoExit_of` at `helloDR_nn`. -/
theorem abExit_DR [Kraken.Executable.ValidLayout exe] {kp : Nat} {ι : Type}
    (hl : Scc.Cert.Rt.A64.Lays exe helloProg kp) (hend : endPc = Scc.Cert.Rt.A64.endOf exe helloProg kp)
    {SR : ι → Inv2Core.SpawnRec} {lbl : ι → WeakMem.AllocLabel → Option Nat}
    {ms : ι → List TermRun.Frame → MemSide isaLSE2} {P Z X : ι → FragS isaLSE2} {hK : ∀ w fs, (ms w fs).K = some abi}
    {hseg : ∀ w, HelloSegTCSX.SegTCSX (fun s c fs => Spike.Lib.A64.Flow.Worker.NNH exe endPc s ∧ Z w s c fs) (X w)
      HelloSrc.helloSrc (lbl w) (ms w) (P w) (fun _ _ _ => False)}
    {cw : ι → TermRun.Word} {bufL : ι → WeakMem.AllocLabel} {nB mB : ι → Nat} {μ : Marks}
    (hx : ExitSite exe μ) :
    AbExit (HelloWorkerRR.helloDR exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB) μ (AbW exe) :=
  abExit_of hx (svcNoExit_of (fun w s c fs h =>
    (HelloWorkerRR.helloDR_nn exe endPc SR lbl ms P Z X hK hseg cw bufL nB mB w s c fs h).1) (exit_ne_svc hl hend))

end Svc

end Spike.Lib.HelloAbExit

/-- info: 'Spike.Lib.HelloAbExit.abExit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAbExit.abExit_of

/-- info: 'Spike.Lib.HelloAbExit.exitSite_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAbExit.exitSite_P

/-- info: 'Spike.Lib.HelloAbExit.sysStepP_ofX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAbExit.sysStepP_ofX

/-- info: 'Spike.Lib.HelloAbExit.exit_ne_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAbExit.exit_ne_svc

/-- info: 'Spike.Lib.HelloAbExit.svcNoExit_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAbExit.svcNoExit_of

/-- info: 'Spike.Lib.HelloAbExit.abExit_DR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloAbExit.abExit_DR

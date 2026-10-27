/-
**A closed `Correct` on the canonical AArch64 target**: the text

    _start: movz x0, #42; movz x8, #94; svc #0

(`exit_group(42)`) is a correct lowering of the program whose `main`
returns `42`, on `canonical 1` (the kernel model's hooks, Linux entry
state), under `Scc.Correct`'s configuration with no thread budget (one
thread slot, source capacity 1).

The trust boundary is the parse of the text (`Scc/Sem/LoadA64.lean`):
`textProgram toyAsm = .ok toyProg` and `dataSections toyAsm = some {}`, the
two hypotheses of `toy_correct`, checked by evaluation (`#guard`, below).
The kernel cannot evaluate Kraken's parser (`Std.Internal.Parsec`, with
`partial` combinators, over `String`); the compiler's `scc_arm_reparse%`
already trusts the parser by evaluation in the same way. Everything after
the parse is proved.

The proof is a step-wise simulation (`Scc.Sem.StepSim`) on the extended
machine `ExtMachine.ofHooks` (not `ofBase`, whose run inversion the
`Spike/Bridge` consumers use):

- **Phases.** The target thread is at `movz x0` (`atJ 0 md0`), `movz x8`
  (`atJ 1 md1`) or `svc` (`atJ 2 md2`) with no promise and the loaded
  memory, the kernel state as loaded (`Ph`); or the process has exited with
  `exit 42`. The source is at `main`'s tail call (`s0`) before the exit and
  at `ret 42` (`s1`) after it.
- **Steps.** The two `movz` are instruction steps matched by no source step
  (`exec0`, `exec1`, `instrSemC_done_iff`); a promise step is impossible
  (`no_certOkC`: certification under `certExec` passes no store, and stops
  at `exit_group`, where `certExec` has no branch); the `svc` is the
  kernel's `exit_group` step (`sysStep_cases`), matched by the source's tail
  call into `main`, after which `mainExit` is `[exit 42]`. No spawn, no
  range transfer (no transfer label resolves), no abort (no abort label
  resolves: the abort clause is vacuous).
- **Progress.** No fault (no instruction step errs, `exit_group` is
  supported, no thread halts, `movz` touches no memory), and the live thread
  steps; after the exit the configuration has exited.
- **Components.** The witness maps source thread 0 to target thread 0 and
  nothing else: the source has no memory and its only variable (`a : unit`)
  has no words.
-/
import Scc.Sem.ExtSim
import Scc.Sem.LoadA64
import Scc.Sem.SysA64
import Scc.Sem.SysLink
import Kraken.Promising.Lower.CodeSegA64
import Kraken.AArch64.Parser
import Spike.Lib.Thread
import Spike.Bridge.Progress
import Scc.Sem.CertStep

namespace Spike.Lib.A64ExtToy

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64

/-! ## The text and its cells -/

/-- The text: `exit_group(42)`. -/
def toyAsm : String := "\t.text\n\t.globl _start\n_start:\n\tmovz x0, #42\n\tmovz x8, #94\n\tsvc #0\n"

/-- `movz x0, #42`. -/
def d1 : Directive := .instr ⟨.W64, .MOVZ (.low (.reg .X0) .W64) (.int64 42) .LSL0⟩

/-- `movz x8, #94` (`exit_group`). -/
def d2 : Directive := .instr ⟨.W64, .MOVZ (.low (.reg .X8) .W64) (.int64 94) .LSL0⟩

/-- `svc #0`. -/
def d3 : Directive := .instr ⟨.W64, .SVC 0⟩

/-- The parsed program of the text. -/
def toyProg : Program := [.label "_start", d1, d2, d3]

open Kraken.AArch64.Parser in
/-- `toyProg` is Kraken's parse of the instructions. -/
example : toyProg = parseAArch64("_start:
movz x0, #42
movz x8, #94
svc #0") := by decide +kernel

-- The trust boundary, checked by evaluation: the canonical loader's parse of
-- the text is `toyProg`, with no data section.
#guard (textProgram toyAsm).toOption == some toyProg
#guard (dataSections toyAsm).isEqSome {}

/-- The layout: `trivLayout` (code at 16, no static data). -/
abbrev Λ : Scc.Sem.Layout := trivLayout

/-- The loaded thread state (`threadAt` at `Λ.code.lo`). -/
def st0 : State := threadAt Entry.linux Λ.code.lo toyProg []

/-- The start of the text. -/
def pc0 : Int64 := st0.exe.1

/-- The loaded state at instruction `j`, with machine data `m`. -/
def atJ (j : Nat) (m : MachineData) : State := { st0 with st := (m, pc0 + .ofNat (4 * j)) }

theorem validLayout : Kraken.Executable.ValidLayout st0.exe := by
  constructor <;> first
  | decide +kernel
  | (intro i; rcases i with _ | _ | _ | _ | _ | i <;>
      simp_all [st0, threadAt, toyProg, placeSyms, placeBelow, symsBelow, exeStart, symsFrom, padTo, Directive.fakeSize, d1, d2, d3])

theorem endPc_eq : st0.endPc = st0.exe.1 + .ofNat (st0.exe.2.map (·.2)).sum := by decide +kernel

theorem codeAt_pc0 : Kraken.Executable.codeAt st0.exe pc0 = [d1, d2, d3].map (·, 4) ++ [] := by
  rw [pc0, Kraken.Executable.codeAt_start]; decide +kernel

/-- **Instruction `j` is the 4-byte cell at `atJ j m`.** -/
theorem cell {j : Nat} {d : Directive} (hd : [d1, d2, d3][j]? = some d) (m : MachineData) :
    CellAt (atJ j m) d 4 :=
  cellAt_segment4 validLayout endPc_eq codeAt_pc0 (by decide) hd m

/-- The machine data as loaded. -/
def md0 : MachineData := st0.st.1

/-- After `movz x0, #42`. -/
def md1 : MachineData := { md0 with regs := md0.regs.setRegOrZr (.low (.reg .X0) .W64) 42#64 }

/-- After `movz x8, #94`. -/
def md2 : MachineData := { md1 with regs := md1.regs.setRegOrZr (.low (.reg .X8) .W64) 94#64 }

theorem st0_eq : st0 = atJ 0 md0 := by
  have h : st0.st.2 = pc0 + .ofNat (4 * 0) := by decide +kernel
  simp only [atJ, md0]; rw [← h]

theorem exec0 : isaLSE2.exec (atJ 0 md0) = some (.done (atJ 1 md1)) := by
  rw [exec_movz (cell (j := 0) rfl md0)]
  simp only [after, atJ, md1]
  congr 3
  all_goals decide +kernel

theorem exec1 : isaLSE2.exec (atJ 1 md1) = some (.done (atJ 2 md2)) := by
  rw [exec_movz (cell (j := 1) rfl md1)]
  simp only [after, atJ, md2]
  congr 3
  all_goals decide +kernel

theorem exec2 : isaLSE2.exec (atJ 2 md2) = some (.fault (pendingSyscallMsg 0)) :=
  exec_svc (cell (j := 2) rfl md2)

theorem atSvc0 : atSvc (atJ 0 md0) = false :=
  atSvc_false_of_cellAt (cell (j := 0) rfl md0) (by intro _ h; cases h)

theorem atSvc1 : atSvc (atJ 1 md1) = false :=
  atSvc_false_of_cellAt (cell (j := 1) rfl md1) (by intro _ h; cases h)

theorem atSvc2 : atSvc (atJ 2 md2) = true := atSvc_of_cellAt (cell (j := 2) rfl md2)

/-- At the `svc` the call is `exit_group(42)`. -/
theorem decode2 : Kernel.decode abi.nrs (abi.nr (atJ 2 md2)) (abi.arg (atJ 2 md2)) = some (.exitGroup 42) := by
  decide +kernel

/-- `certExec` at the `svc`: no branch (`exit_group` does not return). -/
theorem certExec2 : ∃ f, Kernel.certExec abi (atJ 2 md2) = some (.choose 0 f) :=
  ⟨_, Kernel.certExec_of_decode atSvc2 decode2⟩

/-! ## Certification passes no store -/

/-- Off a system call, `stepOneWith cexec` is `stepOne`. -/
theorem stepOneWith_eq {I : ISA} {A : Arch} {cexec : I.State → Option (EvTree I.State)} {t : Thread I}
    {tid : Nat} {mem : Memory} (h : cexec t.st = I.exec t.st) :
    stepOneWith A cexec t tid mem = stepOne A t tid mem := by
  unfold stepOneWith stepOne; rw [h]

/-- The three code states. -/
def Code (s : State) : Prop := s = atJ 0 md0 ∨ s = atJ 1 md1 ∨ s = atJ 2 md2

/-- With no transfer site in the marks, the solo projection at `svc` has no
branch (`exit_group` does not return). -/
theorem soloExec2 {μ : Marks} {x : Kernel.KState} {tid : Nat} (hμ : ∀ k, μ.site k = none) :
    ∃ f, Kernel.soloExec abi Arch.armv8 μ x tid (atJ 2 md2) = some (.choose 0 f) := by
  have ha : abi.atSys (atJ 2 md2) = true := atSvc2
  have h : Kernel.soloExec abi Arch.armv8 μ x tid (atJ 2 md2) = some (Kernel.leaves []) := by
    simp only [Kernel.soloExec, Kernel.siteAt, hμ, reduceCtorEq, ite_false, ha, ite_true, decode2]
    rfl
  exact ⟨_, h⟩

/-- **No certification at the code empties a promise set**: with no
transfer site in the marks, a solo step of the solo projection
(`Kernel.certSem`) at a `movz` is `stepOne` and keeps the promises
(`k_done_out`), and at the `svc` there is none (`exit_group` has no
branch). -/
theorem no_certOkC {μ : Marks} {x : Kernel.KState} {tid : Nat} {t : Thread isaLSE2} {mem : Memory}
    (hμ : ∀ k, μ.site k = none) (hc : Code t.st) (hp : t.prom ≠ []) :
    ¬ CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x tid) tid t mem := by
  rintro ⟨t', mem', hrun, hp'⟩
  have hsite : ∀ s, Kernel.siteAt abi μ s = none := fun s => by simp [Kernel.siteAt, hμ]
  suffices H : ∀ q q', ThreadNPC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ x tid) tid q q' → Code q.1.st →
      q.1.prom ≠ [] → q'.1.prom ≠ [] from H (t, mem) (t', mem') hrun hc hp hp'
  intro q q' hr
  induction hr with
  | refl => exact fun _ h => h
  | step hs _ ih =>
    intro hc hp
    obtain ⟨outs, o, hso, ho, rfl⟩ := hs
    rcases hc with h0 | h1 | h2
    · have he : Kernel.soloExec abi Arch.armv8 μ x tid _ = _ := h0 ▸ Kernel.soloExec_of_not_atSys abi (hsite _) atSvc0
      have hd : Kernel.certDeps abi _ = _ := h0 ▸ Kernel.certDeps_of_not_atSys abi atSvc0
      rw [CertSem.step_eq_stepOne (cs := Kernel.certSem abi Arch.armv8 μ x tid) _ he hd] at hso
      obtain ⟨-, hpr, -, -, hst⟩ := Spike.Lib.k_done_out (F := 0) Arch.armv8 (h0 ▸ exec0) ⟨outs, o, hso, ho, rfl⟩
      exact ih (.inr (.inl hst)) (hpr ▸ hp)
    · have he : Kernel.soloExec abi Arch.armv8 μ x tid _ = _ := h1 ▸ Kernel.soloExec_of_not_atSys abi (hsite _) atSvc1
      have hd : Kernel.certDeps abi _ = _ := h1 ▸ Kernel.certDeps_of_not_atSys abi atSvc1
      rw [CertSem.step_eq_stepOne (cs := Kernel.certSem abi Arch.armv8 μ x tid) _ he hd] at hso
      obtain ⟨-, hpr, -, -, hst⟩ := Spike.Lib.k_done_out (F := 0) Arch.armv8 (h1 ▸ exec1) ⟨outs, o, hso, ho, rfl⟩
      exact ih (.inr (.inr hst)) (hpr ▸ hp)
    · obtain ⟨f, hf⟩ := soloExec2 (x := x) (tid := tid) hμ
      simp only [CertSem.step, stepOneWithD, Kernel.certSem, h2, hf, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def, Option.some.injEq] at hso
      subst hso
      simp [runTree] at ho

/-! ## The loaded configuration and the marks -/

/-- The target: `canonical 1`. -/
abbrev T : Target := canonical 1

/-- The kernel state as loaded. -/
def K0 : Kernel.KState := Kernel.KState.init 1 Entry.linux Λ

/-- The kernel state after `exit_group(42)`. -/
def K1 : Kernel.KState := { K0 with exited := some (.exit (Kernel.exitCode 42)) }

/-- The loaded memory: no initial word (`trivLayout` has no image, the text no `.rodata`). -/
def mem0 : Memory := { init := imageMem Λ ++ wordsMem [], msgs := #[] }

/-- The loaded configuration. -/
def t0 : T.M.Cfg := loadProg (kernel 1) Entry.linux Λ toyProg [] (imageMem Λ ++ wordsMem [])

/-- **The load**, from the parse of the text. -/
theorem load_eq (hp : textProgram toyAsm = .ok toyProg) (hd : dataSections toyAsm = some {}) :
    T.load toyAsm Λ = some t0 := by
  refine (load_of_parsed (kernel 1) Entry.linux Λ hp hd).trans ?_
  rw [loadParsed]
  split
  · rfl
  · rename_i h; exact absurd (by decide +kernel) h

/-- Only `_start` resolves. -/
theorem labelAddr_ne {l : String} (h : l ≠ "_start") :
    Scc.Sem.labelAddr labelName Directive.fakeSize Λ.code.lo l toyProg = none := by
  simp [Scc.Sem.labelAddr, toyProg, labelName, d1, d2, d3, Ne.symm h]

/-- **No transfer site resolves.** -/
theorem site_none (hp : textProgram toyAsm = .ok toyProg) (k : XferKind) : (T.marks toyAsm Λ).site k = none := by
  exact (resolve_of_parsed (kernel 1) Entry.linux Λ hp _).trans (labelAddr_ne (by cases k <;> decide))

/-- **No abort site resolves.** -/
theorem abortAt_none (hp : textProgram toyAsm = .ok toyProg) (k : AbortKind) :
    (T.marks toyAsm Λ).abortAt k = none := by
  exact (resolve_of_parsed (kernel 1) Entry.linux Λ hp _).trans (labelAddr_ne (by cases k <;> decide))

/-! ## The target phases -/

/-- **Before the exit**: one thread, at the code, with no promise; memory
and kernel state as loaded. -/
def Pre (t : T.M.Cfg) : Prop :=
  ∃ th, t.1.threads = #[th] ∧ th.prom = [] ∧ t.1.mem = mem0 ∧ t.2 = K0 ∧ Code th.st

/-- **After the exit**: the process has exited with `exit 42`. -/
def Post (t : T.M.Cfg) : Prop :=
  ∃ th, t.1.threads = #[th] ∧ th.prom = [] ∧ t.1.mem = mem0 ∧ t.2 = K1 ∧ th.st = atJ 2 md2

theorem pre_t0 : Pre t0 := ⟨_, rfl, rfl, rfl, rfl, .inl st0_eq⟩

theorem get_one {th : Thread isaLSE2} {c : Config isaLSE2} (h : c.threads = #[th]) {tid : Nat}
    {t : Thread isaLSE2} (ht : c.threads[tid]? = some t) : tid = 0 ∧ th = t := by
  rw [h] at ht
  rcases tid with _ | n
  · exact ⟨rfl, Option.some.inj ht⟩
  · simp at ht

/-- After the exit no thread steps. -/
theorem post_no_step {μ : Marks} {t t' : T.M.Cfg} {tid : Nat} {es : List Ev} (h : Post t)
    (hs : T.M.Step μ tid t es t') : False := by
  obtain ⟨-, -, -, -, h2, -⟩ := h
  obtain ⟨-, hx, -⟩ := hs.runs
  rw [h2] at hx
  cases hx

/-- The `svc` thread may take a kernel step: it is at a system call, runs,
and the process has not exited. -/
theorem ready2 {t : T.M.Cfg} {th : Thread isaLSE2} (hk : t.2 = K0) (h2 : th.st = atJ 2 md2) :
    Kernel.ready abi 0 t th = true := by
  simp only [Kernel.ready, hk]
  rw [show abi.atSys th.st = atSvc th.st from rfl, h2, atSvc2]
  decide +kernel

/-- The call at the `svc`. -/
theorem callOf2 {th : Thread isaLSE2} (h2 : th.st = atJ 2 md2) : Kernel.callOf abi th = some (.exitGroup 42) := by
  rw [Kernel.callOf, h2]; exact decode2

/-- At a `movz` the thread is not ready for a kernel step. -/
theorem not_ready {t : T.M.Cfg} {th : Thread isaLSE2} (h : atSvc th.st = false) :
    Kernel.ready abi 0 t th = false := by
  simp only [Kernel.ready]
  rw [show abi.atSys th.st = atSvc th.st from rfl, h, Bool.false_and, Bool.false_and]

/-- A `movz` step keeps the phase's shape. -/
theorem pre_of_fin {t : T.M.Cfg} {th th' : Thread isaLSE2} {s : State} (hth : t.1.threads = #[th])
    (hpr : th.prom = []) (hm : t.1.mem = mem0) (hk : t.2 = K0)
    (hfin : th' ∈ finishInstr th (isaLSE2.deps th.st) (instrViews th (isaLSE2.deps th.st)) s
      (Live.TicketStep.ctx0 0 th t.1.mem)) (hc : Code s) :
    Pre (t.1.withThread 0 th' t.1.mem, t.2) := by
  refine ⟨th', by simp only [Config.withThread, hth]; rfl, (finishInstr_relKey hfin).1.trans hpr, hm, hk, ?_⟩
  rw [finishInstr_st hfin]; exact hc

/-- **The steps before the exit**: a `movz` (no event, still before the
exit), or `exit_group(42)` (the event `exit 42`, after the exit). -/
theorem pre_step (hp : textProgram toyAsm = .ok toyProg) {t t' : T.M.Cfg} {tid : Nat} {es : List Ev}
    (h : Pre t) (hs : T.M.Step (T.marks toyAsm Λ) tid t es t') :
    (es = [] ∧ Pre t') ∨ (es = [.exit (Kernel.exitCode 42)] ∧ Post t') := by
  obtain ⟨th, hth, hpr, hm, hk, hc⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hnot : ∀ {s : State}, th.st = s → atSvc s = false → atSvc th.st = false := fun h e => h ▸ e
  cases hs with
  | instr _ hns _ hstep =>
    rcases hstep with hi | ⟨t2, w, ht2, -, hcert, -⟩
    · refine .inl ⟨rfl, ?_⟩
      rcases hc with h0 | h1 | h2
      · obtain ⟨th', hfin, -, rfl⟩ := (ExtMachine.instrSemC_done_iff ht1 (h0 ▸ exec0)).mp hi
        exact pre_of_fin hth hpr hm hk hfin (.inr (.inl rfl))
      · obtain ⟨th', hfin, -, rfl⟩ := (ExtMachine.instrSemC_done_iff ht1 (h1 ▸ exec1)).mp hi
        exact pre_of_fin hth hpr hm hk hfin (.inr (.inr rfl))
      · exact absurd ⟨th, ht1, show atSvc th.st = true from h2 ▸ atSvc2⟩ hns
    · obtain rfl := Option.some.inj (ht2.symm.trans ht1)
      exact absurd hcert (no_certOkC (site_none hp) hc (by simp))
  | spawn _ hsp =>
    obtain ⟨j, r, hsp, -⟩ := hsp
    rcases hc with h0 | h1 | h2
    · simp [Kernel.spawnStep, ht1, not_ready (hnot h0 atSvc0)] at hsp
    · simp [Kernel.spawnStep, ht1, not_ready (hnot h1 atSvc1)] at hsp
    · simp [Kernel.spawnStep, ht1, ready2 hk h2, callOf2 h2] at hsp
  | sys _ hsys _ _ _ =>
    obtain ⟨p, hsys, -⟩ := hsys
    rcases hc with h0 | h1 | h2
    · simp [Kernel.sysStep, ht1, not_ready (hnot h0 atSvc0)] at hsys
    · simp [Kernel.sysStep, ht1, not_ready (hnot h1 atSvc1)] at hsys
    obtain ⟨-, call, hcall, hcases⟩ := Kernel.sysStep_cases ht1 hsys (fun _ _ _ h => by
      rw [callOf2 h2] at h; cases h)
    rw [callOf2 h2] at hcall
    cases hcall
    rcases hcases with ⟨_, _, _, _, _, _, h, _⟩ | ⟨_, _, _, hg, _⟩ | ⟨h, _⟩ | ⟨v, hv, hx⟩
    · cases h
    · exact absurd rfl (hg 42)
    · cases h
    cases hv
    rcases hx with ⟨-, rfl, rfl⟩ | ⟨k, -, hv, -⟩
    · exact .inr ⟨rfl, th, hth, hpr, hm, by rw [hk]; rfl, h2⟩
    · exact absurd hv (by decide)
  | xfer k _ hsite _ =>
    obtain ⟨a, ha, -⟩ := hsite
    rw [site_none hp] at ha; cases ha

/-! ## Progress -/

theorem abi_atSys (s : State) : abi.atSys s = atSvc s := rfl

/-- Before the exit thread 0 runs. -/
theorem runs_pre {t : T.M.Cfg} {th : Thread isaLSE2} (hth : t.1.threads = #[th]) (hk : t.2 = K0) :
    T.M.runs t 0 := by
  refine ⟨⟨th, by rw [hth]; rfl⟩, by rw [hk]; rfl, ?_⟩
  show ¬ Kernel.KState.runs t.2 0 = false
  rw [hk]; decide +kernel

/-- No thread at the code has halted. -/
theorem not_halted {th : Thread isaLSE2} (hc : Code th.st) : th.halted = false := by
  rcases hc with h | h | h <;> simp [Thread.halted, h, exec0, exec1, exec2]

/-- **Before the exit there is progress**: no fault, and the thread steps
(a `movz` instruction step, or `exit_group`). -/
theorem pre_progress (hp : textProgram toyAsm = .ok toyProg) {t : T.M.Cfg} (h : Pre t) :
    T.M.Progress (T.marks toyAsm Λ) t := by
  obtain ⟨th, hth, hpr, hm, hk, hc⟩ := h
  have ht : t.1.threads[0]? = some th := by rw [hth]; rfl
  refine ⟨?_, .inr ⟨⟨0, by rw [hk]; rfl, (runs_pre hth hk).2.2, th, ht, fun h => by
    rw [not_halted hc] at h; cases h.1⟩, fun tid hl => ?_⟩⟩
  · rintro (⟨tid, m, ⟨⟨t1, ht1⟩, -, -⟩, hns, outs, hs, hm⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, ht1, -, -, hns, hex, htouch⟩))
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      have hs' : stepOne Arch.armv8 th 0 t.1.mem = some outs := by
        simp only [stepThread, ht1] at hs; exact hs
      rcases hc with h0 | h1 | h2
      · exact Spike.Bridge.stepOne_no_error Arch.armv8 (h0 ▸ exec0) (Spike.Bridge.runTree_done_ok Arch.armv8 _ _ _ _)
          hs' m hm
      · exact Spike.Bridge.stepOne_no_error Arch.armv8 (h1 ▸ exec1) (Spike.Bridge.runTree_done_ok Arch.armv8 _ _ _ _)
          hs' m hm
      · exact hns ⟨th, ht1, show atSvc th.st = true from h2 ▸ atSvc2⟩
    · unfold Kernel.faultAt at hf
      split at hf
      · rename_i t1 ht1
        obtain ⟨rfl, rfl⟩ := get_one hth ht1
        rw [not_halted hc, Bool.or_false] at hf
        rcases hc with h0 | h1 | h2
        · simp [abi_atSys, h0, atSvc0] at hf
        · simp [abi_atSys, h1, atSvc1] at hf
        · simp [abi_atSys, h2, atSvc2, callOf2 h2] at hf
      · cases hf
    · obtain ⟨rfl, rfl⟩ := get_one hth ht1
      rcases hc with h0 | h1 | h2
      · rw [h0, exec0] at hex; cases hex; cases htouch
      · rw [h1, exec1] at hex; cases hex; cases htouch
      · exact absurd ((show atSvc th.st = true from h2 ▸ atSvc2).symm.trans hns) (by decide)
  · obtain ⟨-, -, t1, ht1, -⟩ := hl
    obtain ⟨rfl, rfl⟩ := get_one hth ht1
    have hsite : ∀ k, ¬ T.M.AtSite (T.marks toyAsm Λ) k t 0 := fun k ⟨a, ha, _⟩ => by
      rw [site_none hp] at ha; cases ha
    have hmovz : ∀ {s : State}, isaLSE2.exec th.st = some (.done s) → atSvc th.st = false →
        ∃ es c', T.M.Step (T.marks toyAsm Λ) 0 t es c' := by
      intro s hex hsvc
      obtain ⟨th', hfin⟩ := Spike.Bridge.finishInstr_nonempty th (isaLSE2.deps th.st)
        (instrViews th (isaLSE2.deps th.st)) s (Live.TicketStep.ctx0 0 th t.1.mem)
      have hi := (ExtMachine.instrSemC_done_iff (A := Arch.armv8)
        (cexec := Kernel.certSem abi Arch.armv8 (T.marks toyAsm Λ) t.2 0) ht1 hex).mpr
        ⟨th', hfin, certOkC_of_prom_nil ((finishInstr_relKey hfin).1.trans hpr), rfl⟩
      exact ⟨[], _, .instr (runs_pre hth hk) (fun ⟨t2, ht2, h2⟩ => by
        rw [ht1] at ht2; cases ht2; exact absurd (hsvc.symm.trans h2) (by decide)) hsite (.inl hi)⟩
    rcases hc with h0 | h1 | h2
    · exact hmovz (h0 ▸ exec0) (h0 ▸ atSvc0)
    · exact hmovz (h1 ▸ exec1) (h1 ▸ atSvc1)
    · exact ⟨_, _, .sys (runs_pre hth hk)
        (Kernel.sys_exitGroup (K := abi) Arch.armv8 1 ht1 (ready2 hk h2) hpr (callOf2 h2))
        (by simp) (fun k hk => by simp at hk)
        (fun _ _ k a ha => by have := ha.symm.trans (abortAt_none hp k); cases this)⟩

/-- **After the exit there is progress**: the process has exited, with no
fault. -/
theorem post_progress {μ : Marks} {t : T.M.Cfg} (h : Post t) : T.M.Progress μ t := by
  obtain ⟨th, -, -, -, hk, -⟩ := h
  refine ⟨?_, .inl ?_⟩
  · rintro (⟨tid, m, ⟨-, hx, -⟩, -⟩ | (⟨tid, hf⟩ | ⟨tid, t1, e, -, -, hx, -⟩))
    · rw [hk] at hx; cases hx
    · unfold Kernel.faultAt at hf
      split at hf
      · rw [hk] at hf; simp [K1] at hf
      · cases hf
    · rw [hk] at hx; cases hx
  · show (match (kernel 1).exited t.2 with
      | some o => some o
      | none => if t.1.final then some .halted else none).isSome
    rw [show (kernel 1).exited t.2 = t.2.exited from rfl, hk]; rfl

/-- Memory holds no shared message and no initial word. -/
theorem inLayout_mem {t : T.M.Cfg} (hm : t.1.mem = mem0) : InLayout Λ t := by
  simp [InLayout, hm, mem0, imageMem, wordsMem, trivLayout]

/-! ## The source -/

/-- The source program: `main` returns `42`. -/
def toyP : CoreTerm.Prog :=
  [{ name := "main", idx := [], arg := "a", argTy := .unit, retTy := .int, body := .ret (.lit 42) }]

/-- The certificate's configuration: the layout, no thread budget, one
thread slot, source capacity 1, the empty setup block. -/
def toyCfg : CertCfg := { Λ := Λ, B := ⟨0, 0, 0⟩, slots := 1, cap := 1 }

/-- The source instance `Scc.Correct` states. -/
abbrev S : SrcSem := SrcSem.source (toyCfg.src .arm) toyP

/-- The start: `main`'s tail call. -/
def s0 : TermRun.Cfg := { SrcSem.mainStart with cap := 1 }

/-- In `main`, at `ret 42`. -/
def s1 : TermRun.Cfg := { s0 with ths := #[{ term := .ret (.lit 42), env := [("a", .unit, [])] }] }

theorem threadSteps_s0 : TermRun.threadSteps toyP Promises.Knobs.all .arm s0 0 = [s1] := rfl

/-- **The tail call into `main`** is a step of thread 0 with the event
`exit 42`: `main` is then at `ret 42` (`mainExit`). -/
theorem src_step : S.step 0 s0 [.exit (Kernel.exitCode 42)] s1 :=
  ⟨rfl, .inl (.inl ⟨by
    show s1 ∈ TermRun.threadSteps toyP Promises.Knobs.all .arm s0 0
    rw [threadSteps_s0]; exact List.mem_singleton_self _, s1, .refl _, rfl⟩), rfl⟩

/-! ## The relation and its components -/

/-- **The relation**: before the exit with the start, after it with `main`
at `ret 42`. -/
def R (t : T.M.Cfg) (s : TermRun.Cfg) : Prop := (Pre t ∧ s = s0) ∨ (Post t ∧ s = s1)

/-- The witness: source thread 0 is target thread 0; nothing else is placed. -/
def wit : Witness T.M := { Witness.empty T.M with thr := fun i => if i = 0 then some 0 else none }

/-- **The components** of a one-thread configuration holding no stack
range, against either source configuration. -/
theorem components {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isaLSE2} (hth : t.1.threads = #[th])
    (hheld : t.2.held = []) (hs : s = s0 ∨ s = s1) : Components T.M Λ wit t s := by
  have hsize : s.ths.size = 1 := by rcases hs with rfl | rfl <;> rfl
  have hmem : s.mem = #[] := by rcases hs with rfl | rfl <;> rfl
  have hsr : ∀ j, T.M.stackRange t j = none := by
    intro j
    show Kernel.stackRangeOf abi t j = none
    unfold Kernel.stackRangeOf
    split <;> simp [hheld]
  constructor
  · intro i hi
    rw [hsize] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨0, rfl, by rw [hth]; exact Nat.one_pos⟩
  · intro i i' j h1 h2
    simp only [wit] at h1 h2
    split at h1 <;> split at h2 <;> simp_all
  · intro j tt _ hj
    obtain ⟨rfl, -⟩ := get_one hth hj
    exact ⟨0, by rw [hsize]; decide, rfl⟩
  · intro l b h; cases h
  · intro l b h; cases h
  · intro l l' b b' _ _ _ h; cases h
  · intro m hm; rw [hmem] at hm; cases hm
  · intro _ _; rfl
  · intro k m hm; rw [hmem] at hm; simp at hm
  · intro k m hm; rw [hmem] at hm; simp at hm
  · intro k1 k2 k1' k2' m1 m2 hm; rw [hmem] at hm; simp at hm
  · intro k' m' _ ⟨l, b, _, hb, _⟩; cases hb
  · intro _ k' m' _ ⟨l, b, _, hb, _⟩; cases hb
  · intro i th j tt _ _ _ d e _ x ty ws _ k wd pl _ hpl; cases hpl
  · intro i th' hth' d e xs he _ _ x _ ty ws hl k hk
    exfalso
    have hth0 : th'.env = [("a", .unit, [])] ∧ th'.stack = [] := by
      rcases hs with rfl | rfl
      all_goals
        rcases i with _ | i
        · obtain rfl := Option.some.inj hth'
          exact ⟨rfl, rfl⟩
        · simp [s0, s1, SrcSem.mainStart] at hth'
    rcases d with _ | d
    · simp only [frameEnvs, hth0.2, List.map_nil, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      rw [hth0.1] at hl
      have hws : ws = [] := by
        unfold TermRun.lookupE at hl
        by_cases hx : "a" = x
        · simp [hx] at hl; exact hl.2
        · simp [hx] at hl
      subst hws; exact absurd hk (Nat.not_lt_zero _)
    · simp [frameEnvs, hth0.2] at he
  · intro j rg h; rw [hsr] at h; cases h
  · intro j j' rg rg' _ h; rw [hsr] at h; cases h
  · intro j rg h; rw [hsr] at h; cases h
  · intro j rg h; rw [hsr] at h; cases h
  · intro j pl h; exact h.elim
  · intro _ _ _ _ _ _ _ _ _ _ h; exact h
  · intro _ _ _ _ _ _ _ _ _ h; cases h

theorem components_R {t : T.M.Cfg} {s : TermRun.Cfg} (h : R t s) :
    ∃ w : Witness T.M, Components T.M Λ w t (S.core s) := by
  rcases h with ⟨⟨th, hth, -, -, hk, -⟩, rfl⟩ | ⟨⟨th, hth, -, -, hk, -⟩, rfl⟩
  · exact ⟨wit, components hth (by rw [hk]; rfl) (.inl rfl)⟩
  · exact ⟨wit, components hth (by rw [hk]; rfl) (.inr rfl)⟩

/-! ## The simulation -/

/-- **The step-wise simulation.** -/
theorem stepSim (hp : textProgram toyAsm = .ok toyProg) (hd : dataSections toyAsm = some {}) :
    StepSim T S Λ toyAsm R where
  init t h := by
    rw [load_eq hp hd] at h
    cases h
    exact ⟨s0, rfl, .inl ⟨pre_t0, rfl⟩⟩
  step tid t es t' s hR hs := by
    rcases hR with ⟨h, rfl⟩ | ⟨h, -⟩
    · rcases pre_step hp h hs with ⟨rfl, h'⟩ | ⟨rfl, h'⟩
      · exact ⟨s0, .refl _, .inl ⟨h', rfl⟩⟩
      · exact ⟨s1, LRun.step (es := [.exit (Kernel.exitCode 42)]) (tr := []) ⟨0, src_step⟩ (.refl _),
          .inr ⟨h', rfl⟩⟩
    · exact (post_no_step h hs).elim

/-- **The toy text is a correct lowering of `toyP` on `canonical 1`**,
given the parse of the text (`#guard`-checked above). -/
theorem toy_correct (hp : textProgram toyAsm = .ok toyProg) (hd : dataSections toyAsm = some {}) :
    Scc.Correct toyCfg toyAsm toyP := by
  refine ⟨⟨rfl, ?_, by decide⟩, ?_⟩
  · show Target.threadSlots T toyAsm Λ ≤ 1
    unfold Target.threadSlots
    rw [load_eq hp hd]
    decide +kernel
  · refine correct_of_stepSim (stepSim hp hd) trivLayout_wf ⟨t0, load_eq hp hd⟩ ?_ ?_ ?_
    · intro t0' tr t h0 hr
      obtain ⟨s, -, hR⟩ := (stepSim hp hd).reach h0 hr
      rcases hR with ⟨h, -⟩ | ⟨h, -⟩
      · exact ⟨pre_progress hp h, inLayout_mem h.choose_spec.2.2.1⟩
      · exact ⟨post_progress h, inLayout_mem h.choose_spec.2.2.1⟩
    · intro t0' tr t tid es t' k s _ _ _ _ hs hk
      obtain ⟨a, ha, -⟩ := hs.abort_at hk
      have := ha.symm.trans (abortAt_none hp k)
      cases this
    · intro t s h
      exact components_R h

end Spike.Lib.A64ExtToy

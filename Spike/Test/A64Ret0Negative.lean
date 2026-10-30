/-
**A negative check of the `ret0` instance on AArch64**: the proof of
`ret0_correct_inst` is not vacuous. A one-instruction change of the program
(`corruptProg`: `wc_main`'s `movz x9, #40` made `movz x9, #41`, every label
where it was) is run, and the obligation the proof discharges at its
`exit_group` is shown false.

**Executed, not proved** (`#guard`, `#eval`): that `corruptProg` differs from
`ret0Prog` in exactly one directive, and that the canonical target's run of
its load exits with `43` where `ret0Prog`'s exits with `42`
(`Spike/Test/A64Ret0Correct.lean`). These run witnesses rest on the executed
runner (`Scc.Sem.Test.run`), of which no soundness against `TPar`'s machine
is proved.

**Proved** (kernel-checked, no `sorry`, `native_decide` or axiom beyond the
standard three):
- `corrupt_load`: the canonical loader's checks pass on `corruptProg`;
- `not_mainExit43`: from the source start no local run reaches a `main`
  exit with code `43` (`MainExit … 43` is false at every memory side and
  state), while `mainExit42` gives `MainExit … 42` at `ret0`'s exit node;
- `corrupt_wc_body_seg`: in any valid layout of `corruptProg`, `wc_main`'s
  body returns with `x0 = 43` (and `43` in `y`'s slot);
- `corrupt_exit_seg`: from `.sp0` with `x0 = 43`, the `exit_group` tail of
  `corruptProg` is a segment given `main` exits with `43` there off an
  abort site, the `SysOk (.exitGroup 43)` obligation that
  `corrupt_sysOk_false` shows false.
So `ret0Src` cannot be matched at the `exit_group` the corrupted program
reaches. The full `¬ Correct` (which needs the target run as a `Run`, i.e.
the runner's soundness) is not proved here.
-/
import Spike.Lib.A64Ret0Correct
import Scc.Sem.Test.Run

namespace Spike.Test.A64Ret0Negative

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64Consumer (TPar)
open Spike.Lib.A64.Flow.Ret0 (seg_one mainNX)
open Spike.Lib.A64.Flow.Ret0.Inst (μ0 labT mainBody mainEnv exitEnv start_step ret0_exit)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Lib.A64.Flow.Ret0.Correct (ret0MS)
open Spike.Lib.Ret0Src (ret0Src ret0Body)
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open SccCode (ret0Λ ret0Prog ret0Secs)

set_option linter.unusedSimpArgs false

/-! ## The corrupted program -/

/-- `movz x9, #41`: `wc_main`'s first instruction with `40` changed to `41`. -/
def movz41 : Directive :=
  .instr { operation_size := .W64, operation := .MOVZ (.low (.reg .X9) .W64) (.int64 41) .LSL0 }

/-- `movz41` is the parser's form of the text. -/
example : parseAArch64("movz x9, #41") = [movz41] := by decide

/-- The index of `wc_main`'s `movz x9, #40` in `ret0Prog`, right after `.L18_wc_main.0_entry`. -/
def wcIdx : Nat := 1281

#guard ret0Prog[wcIdx - 1]? == some (.label ".L18_wc_main.0_entry")
#guard ret0Prog[wcIdx]? == (parseAArch64("movz x9, #40")).head?

/-- **The corrupted program**: `ret0Prog` with `wc_main`'s `movz x9, #40`
replaced by `movz x9, #41`, every other directive (and so every label's
address) unchanged. -/
def corruptProg : Program := ret0Prog.set wcIdx movz41

-- Exactly one directive differs.
#guard corruptProg.length == ret0Prog.length &&
  ((ret0Prog.zip corruptProg).filter fun (a, b) => a != b).length == 1

/-- The canonical loader's checks pass on the corrupted program. -/
theorem corrupt_load : loadOk ret0Λ corruptProg ret0Secs = true := by decide +kernel

/-- info: "out=\"\" events=[exit 43] stop=exited steps=294 poolMsgs=0" -/
#guard_msgs in
#eval match TPar.load (corruptProg, ret0Secs) ret0Λ with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.run abi Arch.armv8 pcOf μ 400 0 { cfg := c }
    s!"out={repr r.outText} events={r.other} stop={r.stop} steps={r.steps} " ++
      s!"poolMsgs={Scc.Sem.Test.msgsIn r.cfg ret0Λ.stackPool}"
  | none => "load refused"

/-! ## The source: no exit with `43`

`LocalStep` is deterministic, so every local run from the source start
`c0` visits `c0`, `main`'s body, the control after `let x`, and `ret y`
with `y = 40 + 2`, where it stops. -/

/-- A step's surroundings, to apply a `LocalStep`. -/
def g0 (p : Prog) : TermRun.G := { p := p, k := {}, arch := .arm, n := 1, i := 0, lbase := 0 }
/-- The thread of a control. -/
def th0 (c : Ctl) : TermRun.TTh := { term := c.term, env := c.env }

/-- **`LocalStep` is deterministic.** -/
theorem localStep_det {p : Prog} {c c₁ c₂ : Ctl} (h₁ : LocalStep p c c₁) (h₂ : LocalStep p c c₂) : c₁ = c₂ := by
  have e := (h₁.2 (g0 p) #[] [] (th0 c) rfl rfl rfl rfl rfl).symm.trans (h₂.2 (g0 p) #[] [] (th0 c) rfl rfl rfl rfl rfl)
  simp only [List.cons.injEq, Prod.mk.injEq, TermRun.TTh.mk.injEq, and_true, true_and] at e
  obtain ⟨t1, e1, h1⟩ := c₁
  obtain ⟨t2, e2, h2⟩ := c₂
  simp only at h₁ h₂ e
  obtain ⟨rfl, rfl⟩ := e
  have a := h₁.1
  have b := h₂.1
  simp only at a b
  subst a b
  rfl

/-- `ret0Src`'s `main`. -/
def mainD : Decl := { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := ret0Body }
/-- The controls of the source start's run: `main`'s body, after `let x`, at `ret y`. -/
def k1 : Ctl := ⟨mainBody, mainEnv mainD, none⟩
def k2 : Ctl := ⟨.let_ "y" (.add (.var "x") (.lit 2)) (.ret (.var "y")),
    ("x", .intS (.lit 40), [TermRun.cst (.num 40)]) :: mainEnv mainD, none⟩
def k3 : Ctl := ⟨.ret (.var "y"), exitEnv (mainEnv mainD), none⟩

/-- The run's steps; `ret y` with one frame has none. -/
theorem step01 : LocalStep ret0Src Spike.Lib.A64Consumer.c0 k1 := start_step rfl rfl
theorem step12 : LocalStep ret0Src k1 k2 := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht he _ _
  simp only [TermRun.tstep, ht, k1, mainBody, TermRun.evalOp, TermRun.evalAt, TermRun.ol, Option.map,
      Option.toList, List.map, TermRun.withS, TermRun.stOf, he, k2]
theorem step23 : LocalStep ret0Src k2 k3 := by
  refine ⟨rfl, ?_⟩
  intro g mem pairs th _ ht he _ _
  simp only [TermRun.tstep, ht, TermRun.evalOp, TermRun.evalAt, TermRun.lookupE, TermRun.ol, he,
      List.find?, Option.map, Option.toList, TermRun.withS, TermRun.stOf, k2, k3]
  rfl
theorem stuck3 {c : Ctl} : ¬ LocalStep ret0Src k3 c := by
  intro h
  have := h.2 (g0 ret0Src) #[] [] (th0 k3) rfl rfl rfl rfl rfl
  simp [TermRun.tstep, th0, k3] at this

/-- The controls a local run from `c0` visits. -/
def Reach (c : Ctl) : Prop := c = Spike.Lib.A64Consumer.c0 ∨ c = k1 ∨ c = k2 ∨ c = k3

/-- Local runs stay in `Reach`. -/
theorem reach_run {c c' : Ctl} (h : LocalRun ret0Src c c') (hc : Reach c) : Reach c' := by
  induction h with
  | refl => exact hc
  | step hs _ ih =>
    apply ih
    rcases hc with rfl | rfl | rfl | rfl
    · exact .inr (.inl (localStep_det hs step01))
    · exact .inr (.inr (.inl (localStep_det hs step12)))
    · exact .inr (.inr (.inr (localStep_det hs step23)))
    · exact (stuck3 hs).elim

/-- **No `main` exit with `43`** from the source start. -/
theorem not_mainExit43 {I : Kraken.Promising.ISA} (ms : MemSide I) (s : I.State) :
    ¬ MainExit ret0Src ms s Spike.Lib.A64Consumer.c0 43 := by
  rintro ⟨c', hr, -, hx⟩
  have h := hx { mem := #[], ths := #[th0 c'] } (th0 c') rfl rfl rfl rfl
  rcases reach_run hr (.inl rfl) with rfl | rfl | rfl | rfl <;> revert h <;> decide
/-- **`ret0`'s exit is `42`**: `MainExit … 42` at `ret0`'s `exit_group`
node off an abort site (`ret0_exit` at `ret0Src`). -/
theorem mainExit42 (ls0 : A64Consumer.Lsize) (R' : Region) (F' : MachineData → Prop) (s : State)
    (h : At ret0Exe ret0End R' F' (mainNX labT) s Spike.Lib.A64Consumer.c0) (hn : ¬ (ret0MS ls0).abortAt s) :
    MainExit ret0Src (ret0MS ls0) s Spike.Lib.A64Consumer.c0 42 :=
  ret0_exit rfl rfl rfl R' F' s h hn

/-- **The `exit_group(43)` obligation is false** off an abort site: the
`SysOk` the corrupted program's exit needs. -/
theorem corrupt_sysOk_false {I : Kraken.Promising.ISA} (ms : MemSide I) (s : I.State) (hn : ¬ ms.abortAt s) :
    ¬ SysOk ret0Src ms s Spike.Lib.A64Consumer.c0 (.exitGroup 43) :=
  fun h => not_mainExit43 ms s (h.2.2.2 43 rfl hn)

/-! ## The target: `x0 = 43` at the `exit_group` -/

/-- `wc_main`'s add in `corruptProg`: `x = 41`. -/
def wcAdd41 : List Directive := parseAArch64("movz x9, #41
movz x10, #2
adds x9, x9, x10
b.hs .L18_wc_main.abort_overflow")

block_spec wcAdd41 (-32) 0 (⟨-32, []⟩ : SO) wcAdd41

/-- **`wc_main`'s body in `prog`** with `wcAdd41`. -/
def corruptBodyIn (prog : List Directive) : Bool :=
  blockAt prog ".L18_wc_main.0_entry" 0 wcAdd41 && blockAt prog ".L18_wc_main.0_entry" 4 wcRet

/-- The body's check on `corruptProg`. -/
theorem corrupt_bodyIn : corruptBodyIn corruptProg = true := by decide +kernel
/-- The `exit_group` tail's check on `corruptProg`. -/
theorem corrupt_exitIn : exitIn corruptProg ".L1_scc_rt_main.sp0" 8 = true := by decide +kernel

section Fn
variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_main`'s body in `corruptProg` returns `43`**: as
`ret0_wc_body_seg`, with `43` for `42`. -/
theorem corrupt_wc_body_seg (hp : Lays exe corruptProg) (hend : endPc = endOf exe corruptProg)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot (-8)))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, σ'.slot = Spike.Lib.upd σ.slot (-32) 43#64 → σ'.regs.X0.toBitVec = 43#64 →
      σ'.regs.X29.toBitVec = σ.slot (-16) → σ'.regs.X30.toBitVec = σ.slot (-8) → x.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_main.0_entry", ⟨-32, []⟩, J⟩)
      (At exe endPc R F x) := by
  have hin := corrupt_bodyIn
  simp only [corruptBodyIn, Bool.and_eq_true] at hin
  let lab := (_root_.Executable.labels exe).label
  let n4 : ND := ⟨lab ".L18_wc_main.0_entry" + 4 + 4 + 4 + 4, ⟨-32, []⟩, fun σ c => ∃ σ0, J σ0 c ∧
    σ.slot = σ0.slot ∧ σ.regs.X9.toBitVec = 43#64⟩
  refine Seg.seq (Q := At exe endPc R F n4) ?_ ?_
  · refine seg_one (seg_nd (by simp [wcAdd41]) wcAdd41_ok hF hR hal hlo hhi (code_of hp hend hin.1 (ofNat4_zero _))
      fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, ?_⟩⟩)
    · rw [wcAdd41_run]
    · rw [wcAdd41_run]; rfl
    · rw [wcAdd41_run]; exact ⟨rfl, rfl⟩
  · refine seg_one (seg_nd (n := n4) (by simp [wcRet]) wcRet_ok hF hR hal hlo hhi
      (code_of hp hend hin.2 (by simp only [ofNat4_succ, ofNat4_zero]; rfl))
      fun σ c ⟨σ0, hJ, hs, h9⟩ => ⟨c, .refl c, .inl ⟨(), ?_⟩⟩)
    rw [show wcRet = spStr .X9 0 :: retBlk 32 [.slot 0] from rfl, arun_cons]
    rw [show n4.o = ⟨-32, []⟩ from rfl, dstep_spStr0]
    obtain ⟨h1, h2, h3, _, h5, h6, h7⟩ := retBlk_run (_root_.Executable.labels exe).label (n4.pc + 4)
      { σ with slot := Spike.Lib.upd σ.slot (-32) σ.regs.X9.toBitVec } (F := 32) (by decide) [.slot 0]
    have hs' : Spike.Lib.upd σ.slot (-32) σ.regs.X9.toBitVec = Spike.Lib.upd σ0.slot (-32) 43#64 := by rw [hs, h9]
    refine ⟨?_, ?_, hedge σ0 c hJ _ ?_ ?_ ?_ ?_⟩
    · rw [h1, hra σ0 c hJ]; simp [hs, Spike.Lib.upd_apply]
    · rw [ho, h2]; rfl
    · rw [h3]; exact hs'
    · have := h7 .X0 (.slot 0) (by simp [retRegs])
      refine this.trans ?_
      simp [RW.val, hs, h9, Spike.Lib.upd_apply]
    · rw [h5]; simp [hs, Spike.Lib.upd_apply]
    · rw [h6]; simp [hs, Spike.Lib.upd_apply]
end Fn

section Exit
variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- Back from `wc_main` at `.sp0` with `43` in `x0`. -/
def exitN43 (lab : Label → Int64) (c0 : Ctl) : ND :=
  ⟨lab ".L1_scc_rt_main.sp0", ⟨-48, []⟩, fun σ c => c = c0 ∧ σ.regs.X0.toBitVec = 43#64⟩

/-- **`corruptProg`'s `exit_group` tail with `x0 = 43`**: a segment given
that `main` exits with `43` off an abort site, which is false at `ret0Src`
from the source start (`not_mainExit43`). -/
theorem corrupt_exit_seg (hp : Lays exe corruptProg) (hend : endPc = endOf exe corruptProg)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c0 : Ctl} {Q : Frag isaLSE2}
    (hexit : ∀ s, ¬ ms.abortAt s → MainExit p ms s c0 43) :
    Seg p lbl ms (At exe endPc R F (exitN43 (_root_.Executable.labels exe).label c0)) Q := by
  refine exitTail_seg_of hp hend corrupt_exitIn rfl hK hF hR hal hlo hhi
    (by show Spike.Lib.offOk (-48) 0 (-48 + Int64.toInt 8) = true; decide) (by show (-48 : Int) % 16 = 0; decide)
    fun s c σ0 ⟨hc, h43⟩ _ => ?_
  have h : σ0.regs.X0.toNat = 43 := by
    rw [show σ0.regs.X0.toNat = σ0.regs.X0.toBitVec.toNat from rfl, h43]; rfl
  rw [h, hc]
  exact SysOk.exitGroup_main (hexit s)
end Exit

/-- info: 'Spike.Test.A64Ret0Negative.corrupt_sysOk_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrupt_sysOk_false

/-- info: 'Spike.Test.A64Ret0Negative.corrupt_exit_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrupt_exit_seg

end Spike.Test.A64Ret0Negative

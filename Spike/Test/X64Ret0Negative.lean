/-
**A negative check of the `ret0` instance on x86-64**: the proof of
`ret0_correct_inst` is not vacuous. A one-instruction change of the program
(`corruptCells`: `wc_main`'s `movq $40, %rax` made `movq $41, %rax`, of the
same length, so every label where it was) is run, and the obligation the
proof discharges at its `exit_group` is shown false. The x86-64 twin of
`Spike/Test/A64Ret0Negative.lean`.

**Executed, not proved** (`#guard`, `#eval`): that `corruptCells` differs
from `ret0Cells` in exactly one cell, that it is the canonical loader's
parse of `corruptAsm` (`ret0Asm`'s text with that one instruction changed),
and that the canonical target's run of its load exits with `43` where
`ret0Asm`'s exits with `42` (`Spike/Test/X64Ret0Correct.lean`). These run
witnesses rest on the executed parser and runner (`Scc.Sem.X64.cellsOf`,
`Scc.Sem.Test.run`), of which no soundness against `T`'s machine is proved.

**Proved** (kernel-checked, no `sorry`, `native_decide` or axiom beyond the
standard three):
- `corrupt_load`: the canonical loader's checks pass on `corruptCells`;
- `not_mainExit43`: from the source start no local run reaches a `main`
  exit with code `43` (`MainExit … 43` is false at every memory side and
  state), while `mainExit42` gives `MainExit … 42` at `ret0`'s exit node;
- `corrupt_wc_body_seg`: in any valid layout of `corruptCells`, `wc_main`'s
  body returns with `%rax = 43` (and `43` in `y`'s slot);
- `corrupt_exit_seg`: from `.x2` with `%rax = 43`, the `exit_group` tail of
  `corruptCells` is a segment given `main` exits with `43` there off an
  abort site, the `SysOk (.exitGroup 43)` obligation that
  `corrupt_sysOk_false` shows false.
So `ret0Src` cannot be matched at the `exit_group` the corrupted program
reaches. The full `¬ Correct` (which needs the target run as a `Run`, i.e.
the runner's soundness) is not proved here.
-/
import Spike.Lib.X64Ret0Correct
import Scc.Sem.Test.Run

namespace Spike.Test.X64Ret0Negative

open CoreLang CoreTerm
open Kraken Kraken.X64.Parser Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.Link.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64Consumer (T msOf Lsize)
open Spike.Lib.X64.Flow.Ret0 (mainNX)
open Spike.Lib.X64.Flow.Ret0.Inst (μ0 labT own mainBody mainEnv exitEnv start_step ret0_exit)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End)
open Spike.Lib.Ret0Src (ret0Src ret0Body)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field)
open SccCode (ret0Λ ret0Cells ret0Secs ret0Asm ret0Text)

set_option linter.unusedSimpArgs false

/-! ## The corrupted program -/

/-- `movq $41, %rax`: `wc_main`'s first instruction with `40` changed to `41`. -/
def mov41 : Directive :=
  .instr (.regular .W64 .W64 (.mov (.reg (.low .rax .W64)) (.imm (.int64 41))))

/-- `mov41` is the parser's form of the text. -/
example : parse("movq $41, %rax") = [mov41] := by decide

/-- The index of `wc_main`'s `movq $40, %rax` in `ret0Cells`, right after `.Lwc_main.entry`. -/
def wcIdx : Nat := 1190

#guard ret0Cells[wcIdx - 1]? == some (.label ".Lwc_main.entry", 0)
#guard ret0Cells[wcIdx]? == ((parse("movq $40, %rax")).head?.map (·, 7))

/-- **The corrupted program**: `ret0Cells` with `wc_main`'s `movq $40, %rax`
replaced by `movq $41, %rax` (both 7 bytes), every other cell (and so every
label's address) unchanged. -/
def corruptCells : List (Directive × Nat) := ret0Cells.set wcIdx (mov41, 7)

-- Exactly one cell differs.
#guard corruptCells.length == ret0Cells.length &&
  ((ret0Cells.zip corruptCells).filter fun (a, b) => a != b).length == 1

/-- **The corrupted listing**: `ret0Asm`'s text with its one `movq $40, %rax`
made `movq $41, %rax`, the same sizes and label offsets. -/
def corruptAsm : Scc.Sem.X64.Asm := { ret0Asm with text := ret0Text.replace "movq $40, %rax" "movq $41, %rax" }

-- The text has exactly one such instruction, and the loader's parse of the corrupted listing is `corruptCells`.
#guard (ret0Text.splitOn "movq $40, %rax").length == 2
#guard Scc.Sem.X64.cellsOf corruptAsm == some corruptCells

theorem corrupt_size : sizeOkW (Int64.ofNat ret0Λ.code.lo) corruptCells corruptAsm.labelOffs = true := by
  decide +kernel

theorem corrupt_labels : labelsNodupL (Int64.ofNat ret0Λ.code.lo) corruptCells = true := by decide +kernel

theorem corrupt_quads : quadsOkL (Int64.ofNat ret0Λ.code.lo) corruptCells ret0Secs.rodata = true := by
  decide +kernel

theorem corrupt_syms : (Scc.Sem.rodataFits ret0Λ ret0Secs.rodata && Scc.Sem.symsAgree ret0Λ ret0Secs.rodata &&
    Scc.Sem.symsAbove ret0Λ.code.lo (Scc.Sem.X64.codeEnd ret0Λ.code.lo corruptCells) (Scc.Sem.loadSyms ret0Λ ret0Secs.rodata) &&
    symsOk ret0Λ.code.lo corruptCells (Scc.Sem.loadSyms ret0Λ ret0Secs.rodata)) = true := by decide +kernel

/-- The canonical loader's checks pass on the corrupted program. -/
theorem corrupt_load : loadOk ret0Λ corruptCells ret0Secs corruptAsm.labelOffs = true :=
  loadOk_of corrupt_size corrupt_labels corrupt_quads corrupt_syms

/-- info: "out=\"\" events=[exit 43] stop=exited steps=277 poolMsgs=0" -/
#guard_msgs in
#eval match T.load corruptAsm ret0Λ with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.run abi Arch.tso pcOf μ 400 0 { cfg := c }
    s!"out={repr r.outText} events={r.other} stop={r.stop} steps={r.steps} " ++
      s!"poolMsgs={Scc.Sem.Test.msgsIn r.cfg ret0Λ.stackPool}"
  | none => "load refused"

/-! ## The source: no exit with `43`

`LocalStep` is deterministic, so every local run from the source start
`c0` visits `c0`, `main`'s body, the control after `let x`, and `ret y`
with `y = 40 + 2`, where it stops. -/

/-- A step's surroundings, to apply a `LocalStep`. -/
def g0 (p : Prog) : TermRun.G := { p := p, k := {}, arch := .tso, n := 1, i := 0, lbase := 0 }
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
theorem step01 : LocalStep ret0Src Spike.Lib.X64Consumer.c0 k1 := start_step rfl rfl
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
def Reach (c : Ctl) : Prop := c = Spike.Lib.X64Consumer.c0 ∨ c = k1 ∨ c = k2 ∨ c = k3

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
    ¬ MainExit ret0Src ms s Spike.Lib.X64Consumer.c0 43 := by
  rintro ⟨c', hr, -, hx⟩
  have h := hx { mem := #[], ths := #[th0 c'] } (th0 c') rfl rfl rfl rfl
  rcases reach_run hr (.inl rfl) with rfl | rfl | rfl | rfl <;> revert h <;> decide

/-- **`ret0`'s exit is `42`**: `MainExit … 42` at `ret0`'s `exit_group`
node off an abort site (`ret0_exit` at `ret0Src`), at any of the instance's
memory sides. -/
theorem mainExit42 (rd : TermRun.Word → Prop) (G : Loc → Val → Prop) (ls0 : Lsize) (R' : Region)
    (F' : MachineData → Prop) (s : State)
    (h : At ret0Exe ret0End R' F' (mainNX labT) s Spike.Lib.X64Consumer.c0)
    (hn : ¬ (msOf ret0Λ μ0 rd G own ret0Λ.static ls0).abortAt s) :
    MainExit ret0Src (msOf ret0Λ μ0 rd G own ret0Λ.static ls0) s Spike.Lib.X64Consumer.c0 42 :=
  ret0_exit rfl rfl rfl R' F' s h hn

/-- **The `exit_group(43)` obligation is false** off an abort site: the
`SysOk` the corrupted program's exit needs. -/
theorem corrupt_sysOk_false {I : Kraken.Promising.ISA} (ms : MemSide I) (s : I.State) (hn : ¬ ms.abortAt s) :
    ¬ SysOk ret0Src ms s Spike.Lib.X64Consumer.c0 (.exitGroup 43) :=
  fun h => not_mainExit43 ms s (h.2.2.2 43 rfl hn)

/-! ## The target: `%rax = 43` at the `exit_group` -/

/-- `wc_main`'s add in `corruptCells`: `x = 41`. -/
def wcAdd41 : List (Directive × Nat) := (parse("movq $41, %rax
movq $2, %rcx
addq %rcx, %rax
jb .Lwc_main.ovf")).zip [7, 7, 3, 2]

block_spec wcAdd41 (-24) 8 oB wcAdd41

/-- **`wc_main`'s body in `cells`** with `wcAdd41`. -/
def corruptBodyIn (cells : List (Directive × Nat)) : Bool :=
  blockAtB cells ".Lwc_main.entry" 0 wcAdd41 && blockAtB cells ".Lwc_main.entry" 19 wcRet

/-- The body's check on `corruptCells`. -/
theorem corrupt_bodyIn : corruptBodyIn corruptCells = true := by decide +kernel
/-- The `exit_group` tail's check on `corruptCells`. -/
theorem corrupt_exitIn : exitIn corruptCells ".Lscc_rt_main.x2" (-16) 4 4 5 = true := by decide +kernel

section Fn
variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`wc_main`'s body in `corruptCells` returns `43`**: as
`ret0_wc_body_seg`, with `43` for `42`. -/
theorem corrupt_wc_body_seg (hp : Lays exe corruptCells) (hend : endPc = endOf exe corruptCells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {x : ND} (ho : SO.le x.o ⟨8, []⟩ = true)
    (hra : ∀ σ c, J σ c → x.pc = Int64.ofBitVec (σ.slot 0))
    (hedge : ∀ σ c, J σ c → ∀ σ' : AS, σ'.slot = upd σ.slot (-16) 43#64 → σ'.regs.rax.toBitVec = 43#64 →
      σ'.regs.rbp.toBitVec = σ.slot (-8) → σ'.regs.rsp.toBitVec = σ.regs.rbp.toBitVec + 8#64 + 8#64 → x.J σ' c) :
    Seg p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", oB, J⟩)
      (At exe endPc R F x) := by
  have hin := corrupt_bodyIn
  simp only [corruptBodyIn, Bool.and_eq_true] at hin
  let pc := (_root_.Executable.labels exe).label ".Lwc_main.entry"
  let n1 : ND := ⟨pc + 19, oB, fun σ c => ∃ σ0, J σ0 c ∧
    σ.slot = σ0.slot ∧ σ.regs.rax.toBitVec = 43#64 ∧ σ.regs.rbp = σ0.regs.rbp⟩
  have one : ∀ {P : Frag isa} {n : ND},
      SegW (fun _ _ => True) (fun _ _ => False) p lbl ms P
        (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim)) →
      SegW (fun _ _ => True) (fun _ _ => False) p lbl ms P (At exe endPc R F n) := fun h =>
    h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim
  refine SegW.toSeg (W := fun _ _ => True) (SegW.seq (Q := At exe endPc R F n1) ?_ ?_)
  · refine one (seg_ndW (by simp [wcAdd41]) wcAdd41_ok hF hR hlo hhi (code_field hp hend hin.1 (ofNat_zero' _))
      BlkW.triv fun σ c hJ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, σ, hJ, ?_⟩⟩)
    · rw [wcAdd41_run]
    · rw [wcAdd41_run]; rfl
    · rw [wcAdd41_run]; refine ⟨rfl, ?_, ?_⟩ <;> simp [Reg64s.set64]
  · refine one (seg_ndW (n := n1) (by simp [wcRet]) wcRet_ok hF hR hlo hhi (code_field hp hend hin.2 rfl) BlkW.triv
      fun σ c ⟨σ0, hJ, hs, h9, hb⟩ => ⟨c, .refl c, .inl ⟨(), ?_, ?_, hedge σ0 c hJ _ ?_ ?_ ?_ ?_⟩⟩)
    · rw [wcRet_run, hra σ0 c hJ, hs]
    · rw [wcRet_run]; exact ho
    · rw [wcRet_run]; simp only [hs, h9]
    · rw [wcRet_run]; simp [Reg64s.set64, h9]
    · rw [wcRet_run]; simp [Reg64s.set64, hs]
    · rw [wcRet_run]; simp [Reg64s.set64, hb]
end Fn

section Exit
variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- Back from `wc_main` at `.x2` with `43` in `%rax`. -/
def exitN43 (lab : Label → Int64) (c0 : Ctl) : ND :=
  ⟨lab ".Lscc_rt_main.x2", ⟨-40, [(.rbp, -8)]⟩, fun σ c => c = c0 ∧ σ.regs.rax.toBitVec = 43#64⟩

/-- **`corruptCells`' `exit_group` tail with `%rax = 43`**: a segment given
that `main` exits with `43` off an abort site, which is false at `ret0Src`
from the source start (`not_mainExit43`). -/
theorem corrupt_exit_seg (hp : Lays exe corruptCells) (hend : endPc = endOf exe corruptCells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 0 ≤ R.hi) {c0 : Ctl} {Q : Frag isa}
    (hexit : ∀ s, ¬ ms.abortAt s → MainExit p ms s c0 43) :
    Seg p lbl ms (At exe endPc R F (exitN43 (_root_.Executable.labels exe).label c0)) Q := by
  refine exitTail_seg_of (lo := -40) (hi := 0) hp hend corrupt_exitIn rfl rfl hK hF hR hlo hhi (by decide)
    fun s c σ0 ⟨hc, h43⟩ _ => ?_
  have h : σ0.regs.rax.toNat = 43 := by
    rw [show σ0.regs.rax.toNat = σ0.regs.rax.toBitVec.toNat from rfl, h43]; rfl
  rw [h, hc]
  exact SysOk.exitGroup_main (hexit s)
end Exit

/-- info: 'Spike.Test.X64Ret0Negative.corrupt_sysOk_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrupt_sysOk_false

/-- info: 'Spike.Test.X64Ret0Negative.corrupt_exit_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrupt_exit_seg

/-- info: 'Spike.Test.X64Ret0Negative.corrupt_wc_body_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms corrupt_wc_body_seg

end Spike.Test.X64Ret0Negative

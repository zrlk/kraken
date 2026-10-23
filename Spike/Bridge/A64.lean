/-
The bridge spike on AArch64 (`isaLSE2`, `Arch.armv8`): the writer's
`stlr x1, [x0]` and the reader's `ldar x2, [x0]`, parsed by Kraken's AArch64
parser and laid out as the runners do, with `x0 = 0x1000` (the flag) and
`x1 = 1`.

`shape` discharges `Shape` from the per-row `exec` lemmas of
`Kraken.Promising.Lower.A64` (`exec_stlr_agrees`, `exec_ldar_agrees`);
everything else is the ISA-independent development of
`Spike/Bridge/Sim.lean`, instantiated:

* `sim_step_a64`: every `StepSemInf Arch.armv8` step from a related pair is
  one WeakCore step of the same thread, promise steps included, each
  certified by lockstep;
* `sim_a64`: the `Sim.sim` clause for `Target.ofBase isaLSE2 Arch.armv8`,
  with trace equality;
* `components_a64`: the components of `R` (thread map, layout injection,
  value representation on memory and registers), for the register
  observation `regVal` (`x0` holds the flag reference, `x2` the value read);
* `correct_a64_of_progress`: `Correct` under the layout `layoutΛ`, given the
  target's progress;
* `progress_a64`, `correct_a64`: progress discharged
  (`Spike/Bridge/Progress.lean`), so `Correct` holds without hypotheses.
-/
import Spike.Bridge.Progress
import Kraken.Promising.Lower.EventsA64Inf
import Kraken.Promising.Lower.CodeSegA64
import Kraken.AArch64.Parser
import Kraken.AArch64.WP.LayoutOfSize

namespace Spike.Bridge.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.AArch64.Parser Kraken.Promising.Lower.A64
open Kraken.Promising.Live.Inf
open Scc.Sem (SrcSem ExtMachine Target Correct Budget)

/-! ## The programs and start states -/

/-- The writer: a release store of `x1` to the flag at `x0`. -/
def wprog : Program := parseAArch64("
    stlr x1, [x0]
")

/-- The reader: an acquire load of the flag at `x0` into `x2`. -/
def rprog : Program := parseAArch64("
    ldar x2, [x0]
")

/-- The parsed `stlr`. -/
abbrev dW : Directive := .instr ⟨.W64, .STLR .W64 (.low (.reg .X1) .W64) (.low (.reg .X0) .W64)⟩

/-- The parsed `ldar`. -/
abbrev dR : Directive := .instr ⟨.W64, .LDAR .acq false .W64 (.low (.reg .X2) .W64) (.low (.reg .X0) .W64)⟩

theorem wprog_eq : wprog = [dW] := by decide
theorem rprog_eq : rprog = [dR] := by decide

/-- The writer's text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layoutW : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize wprog
/-- The reader's text at `0x100000`. -/
@[reducible] def layoutR : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize rprog

instance validW : Executable.ValidLayout (layoutW wprog) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)
instance validR : Executable.ValidLayout (layoutR rprog) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- The flag's address. -/
abbrev F : BitVec 64 := 0x1000

/-- Thread `0`: `x0 = 0x1000`, `x1 = 1`. -/
def st0 : State where
  exe := layoutW wprog
  endPc := 0x100000 + 4
  st := ({ regs := { X0 := 0x1000, X1 := 1 } }, 0x100000)

/-- Thread `1`: `x0 = 0x1000`. -/
def st1 : State where
  exe := layoutR rprog
  endPc := 0x100000 + 4
  st := ({ regs := { X0 := 0x1000 } }, 0x100000)

/-- The writer after its store. -/
abbrev sW : State := after st0 4 st0.st.1

/-- The reader after loading `v`. -/
abbrev fR (v : Val) : State :=
  after st1 4 { st1.st.1 with regs := st1.st.1.regs.setRegOrZr (.low (.reg .X2) .W64) (v.setWidth 64) }

/-! ## The instruction shapes -/

theorem codeW : Kraken.Executable.codeAt st0.exe st0.st.2 = [(dW, 4)] := by
  show Kraken.Executable.codeAt (layoutW wprog) 0x100000 = _
  rw [Layout.ofSize_apply, wprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress,
    Kraken.Executable.withAddresses_dropWhile_start, Kraken.Executable.withAddresses_map_snd]
  decide

theorem codeR : Kraken.Executable.codeAt st1.exe st1.st.2 = [(dR, 4)] := by
  show Kraken.Executable.codeAt (layoutR rprog) 0x100000 = _
  rw [Layout.ofSize_apply, rprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress,
    Kraken.Executable.withAddresses_dropWhile_start, Kraken.Executable.withAddresses_map_snd]
  decide

/-- The writer's tree: one release store of `1` to `⟨0x1000, 8⟩`. -/
theorem exec_w : isaLSE2.exec st0 = some (.store .rel false ⟨F, 8⟩ 1 fun _ => .done sW) := by
  rw [exec_stlr_agrees (cellAt_of_codeAt validW (by decide) codeW : CellAt st0 dW 4)
    (by simp [st0, Mem.loadInt, Mem.loadBytes, List.allSome]; rfl) rfl]
  rfl

/-- The reader's tree: one acquire load of `⟨0x1000, 8⟩`. -/
theorem exec_r : isaLSE2.exec st1 = some (.load .acq false ⟨F, 8⟩ fun v => .done (fR v)) := by
  rw [exec_ldar_agrees (cellAt_of_codeAt validR (by decide) codeR : CellAt st1 dR 4)
    (by simp [st1, Mem.loadInt, Mem.loadBytes, List.allSome]; rfl) rfl]
  rfl

/-- At the end of the text there is no next instruction. -/
theorem exec_end {s : State} (h : (s.st.2 == s.endPc) = true) : isaLSE2.exec s = none := by
  simp only [isaLSE2]
  unfold execLSE2
  split
  · rfl
  · rename_i h'; simp [h] at h'

theorem shape : Shape isaLSE2 F 1 st0 sW st1 fR where
  wr := ⟨.rel, exec_w⟩
  wd := exec_end (by decide)
  rd := ⟨.acq, exec_r⟩
  rdd _ := exec_end (by show (st1.st.2 + Int64.ofNat 4 == st1.endPc) = true; decide)
  one := by decide

/-! ## The theorems -/

variable {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- **The simulation step on AArch64.** -/
theorem sim_step_a64 {c c' : Config isaLSE2} {s : TermRun.Cfg} {tid : Nat} (hR : Rel F 1 st0 sW st1 fR c s)
    (h : StepSemInf Arch.armv8 tid c c') :
    ∃ s', SrcSem.StepBy prog k arch tid s s' ∧ Rel F 1 st0 sW st1 fR c' s' :=
  sim_step Arch.armv8 shape hR h

/-- **The `Sim.sim` clause on AArch64**, with trace equality. -/
theorem sim_a64 (rv : State → RegId → BitVec 64) (pl : State → BitVec 64 → Option (BitVec 64))
    (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase isaLSE2 Arch.armv8 rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase isaLSE2 Arch.armv8 rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep prog k arch (· = srcInit)).Reach tr' s ∧ Rel F 1 st0 sW st1 fR t.1 s ∧
        Scc.Sem.obs tr = tr' :=
  sim_clause_eq Arch.armv8 shape rv pl Λ μ

/-- The general registers, by index. -/
def xregs : List XReg :=
  [.X0, .X1, .X2, .X3, .X4, .X5, .X6, .X7, .X8, .X9, .X10, .X11, .X12, .X13, .X14, .X15, .X16, .X17, .X18,
   .X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29, .X30]

/-- The register observation: the 64-bit value of `xN` (`0` for `sp` and
the flags, which hold no source word here). -/
def regVal (s : State) : RegId → BitVec 64
  | .x n => ((xregs[n.val]?).map fun r => (s.st.1.regs.getXReg r).toBitVec).getD 0
  | _ => 0

theorem regs : Regs (I := isaLSE2) regVal F st0 sW st1 fR (RegId.x 0) (RegId.x 2) where
  f0 := by decide
  fW := by decide
  f1 := by decide
  fAfter _ := rfl
  r _ := by simp [regVal, xregs, st1]

/-- A layout with the flag's word in `data` and no static labels. -/
def layoutΛ : Scc.Sem.Layout where
  code := ⟨0x100000, 64⟩
  data := ⟨0x1000, 16⟩
  heap := ⟨0x2000, 16⟩
  stackPool := ⟨0x3000, 16⟩
  pinned := ⟨0x4000, 16⟩
  static _ := none
  image := []
  symbols := []
  abortLbl ak := s!"scc_abort_{ak.idx}"

theorem layoutΛ_wf : layoutΛ.WF where
  inSpace r hr := by
    simp only [Scc.Sem.Layout.regions, layoutΛ, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Scc.Sem.Range.InSpace] <;> omega
  aligned r hr := by
    simp only [Scc.Sem.Layout.regions, layoutΛ, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp only [Scc.Sem.Range.Aligned]
  disjoint := by simp only [layoutΛ, Scc.Sem.Range.Disjoint]; omega
  abortInj ak ak' h := by
    cases ak <;> cases ak' <;> first | rfl | simp [layoutΛ, Scc.Sem.AbortKind.idx] at h
  image p hp := by simp [layoutΛ] at hp
  symIn p hp := by simp [layoutΛ] at hp
  symAbove p hp := by simp [layoutΛ] at hp
  symNodup := by simp [layoutΛ]
  pos r hr := by
    simp only [Scc.Sem.Layout.regions, layoutΛ, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

theorem flagIn : FlagIn layoutΛ F where
  static _ := rfl
  align := by decide
  sub := by simp [layoutΛ, Scc.Sem.Range.Sub]

/-- **The components of `R` on AArch64**, under `layoutΛ`. -/
theorem components_a64 (pl : State → BitVec 64 → Option (BitVec 64))
    {t : (ExtMachine.ofBase isaLSE2 Arch.armv8 regVal pl).Cfg} {s : TermRun.Cfg}
    (hR : Rel F 1 st0 sW st1 fR t.1 s) :
    Scc.Sem.Components (ExtMachine.ofBase isaLSE2 Arch.armv8 regVal pl) layoutΛ
      (witness (I := isaLSE2) Arch.armv8 regVal pl F (RegId.x 0) (RegId.x 2)) t s :=
  components shape regs flagIn hR

/-- **`Correct` on AArch64, given progress.** -/
theorem correct_a64_of_progress (pl : State → BitVec 64 → Option (BitVec 64)) (B : Budget)
    (hprog : ProgressOf (I := isaLSE2) Arch.armv8 regVal pl st0 st1 F) :
    Correct (Target.ofBase isaLSE2 Arch.armv8 regVal pl) (SrcSem.ofStep prog k arch (· = srcInit)) layoutΛ B
      (asmOf st0 st1 F) :=
  correct_of_progress Arch.armv8 shape regs flagIn layoutΛ_wf B hprog

/-- **Progress on A64**: every configuration reachable from the loaded start
configuration has no faulting step, and every live thread can step. -/
theorem progress_a64 (pl : State → BitVec 64 → Option (BitVec 64)) :
    ProgressOf (I := isaLSE2) Arch.armv8 regVal pl st0 st1 F :=
  progressOf Arch.armv8 shape regVal pl

/-- **`Correct` on A64**, every clause discharged, progress included. -/
theorem correct_a64 (pl : State → BitVec 64 → Option (BitVec 64)) (B : Budget) :
    Correct (Target.ofBase isaLSE2 Arch.armv8 regVal pl) (SrcSem.ofStep prog k arch (· = srcInit)) layoutΛ B
      (asmOf st0 st1 F) :=
  correct Arch.armv8 shape regs flagIn layoutΛ_wf B

end Spike.Bridge.A64

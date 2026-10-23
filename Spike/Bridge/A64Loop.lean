/-
The bridge spike, spinning-reader variant on AArch64: the reader is
`l: ldar x2, [x0]; cbz x2, l`, the writer as in `Spike/Bridge/A64.lean`.

* `loopShape`: the reader's event trees have the shape `LoopShape`
  (`Spike/Bridge/Loop.lean`): at a loop head (`Head`) one acquire load of
  the flag, at the test (`Mid v`) the `cbz`, back to the head if the low
  64 bits of the value read are `0`, to the end of the text otherwise;
* `sim_step_loop_a64`: every `StepSemInf Arch.armv8` step from a related
  pair is matched by a source run with the empty trace (stutter form);
* `sim_loop_a64`: the `Sim.sim` clause for `Target.ofBase isaLSE2
  Arch.armv8` against the spinning source program `progL`, with trace
  equality.
-/
import Spike.Bridge.A64
import Spike.Bridge.LoopCorrect

namespace Spike.Bridge.A64Loop

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.AArch64.Parser Kraken.Promising.Lower.A64
open Kraken.Promising.Live.Inf
open Scc.Sem (SrcSem Target)
open Spike.Bridge.A64 (F st0 sW dR shape regVal xregs regs layoutΛ flagIn layoutΛ_wf)

/-- The spinning reader: an acquire load of the flag at `x0` into `x2`, until
it is non-zero. -/
def lprog : Program := parseAArch64("
l:
    ldar x2, [x0]
    cbz x2, l
")

/-- The parsed `cbz`. -/
abbrev dC : Directive := .instr ⟨.W64, .CBZ (.low (.reg .X2) .W64) (.label "l")⟩

theorem lprog_eq : lprog = [.label "l", dR, dC] := by decide

/-- The reader's text at `0x100000`, each directive its `fakeSize`. -/
@[reducible] def layoutL : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize lprog

instance validL : Executable.ValidLayout (layoutL lprog) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- Thread `1`: `x0 = 0x1000`, at the loop head. -/
def st1 : State where
  exe := layoutL lprog
  endPc := 0x100000 + 8
  st := ({ regs := { X0 := 0x1000 } }, 0x100000)

/-- The reader with registers `r` at `pc`. -/
abbrev atL (r : Reg64s) (pc : Int64) : State := { st1 with st := ({ st1.st.1 with regs := r }, pc) }

/-- At the loop head, with the flag's address in `x0`. -/
def Head (s : State) : Prop := ∃ r, s = atL r 0x100000 ∧ r.getXReg .X0 = 0x1000

/-- At the `cbz`, with the flag's address in `x0` and the value read in `x2`. -/
def Mid (v : Val) (s : State) : Prop :=
  ∃ r, s = atL r 0x100004 ∧ r.getXReg .X0 = 0x1000 ∧ r.getRegOrZr (.low (.reg .X2) .W64) = v.setWidth 64

/-- At the end of the text, with the flag's address in `x0` and the value
read in `x2`. -/
def Exit (v : Val) (s : State) : Prop :=
  ∃ r, s = atL r 0x100008 ∧ r.getXReg .X0 = 0x1000 ∧ r.getRegOrZr (.low (.reg .X2) .W64) = v.setWidth 64

/-! ## The instruction shapes -/

theorem codeH : Kraken.Executable.codeAt (layoutL lprog) 0x100000 = [(dR, 4), (dC, 4)] := by
  rw [Layout.ofSize_apply, lprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress,
    Kraken.Executable.withAddresses_dropWhile_start, Kraken.Executable.withAddresses_map_snd]
  decide

theorem codeM : Kraken.Executable.codeAt (layoutL lprog) 0x100004 = [(dC, 4)] := by
  rw [Layout.ofSize_apply, lprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress, List.map,
    withAddresses_cons, withAddresses_nil]
  decide

/-- The tree at the loop head: one acquire load of `⟨0x1000, 8⟩`. -/
theorem exec_head (r : Reg64s) (h0 : r.getXReg .X0 = 0x1000) :
    isaLSE2.exec (atL r 0x100000) = some (.load .acq false ⟨F, 8⟩ fun v =>
      .done (atL (r.setRegOrZr (.low (.reg .X2) .W64) (v.setWidth 64)) 0x100004)) := by
  rw [exec_ldar_agrees (cellAt_of_codeAt validL (by dsimp only [atL]; decide) codeH : CellAt (atL r 0x100000) dR 4)
    (by simp [h0, st1, Mem.loadInt, Mem.loadBytes, List.allSome]; rfl) rfl]
  simp only [h0]
  rfl

/-- The label `l` is the loop head. -/
theorem lab_l : (_root_.Executable.labels (layoutL lprog)).label "l" = 0x100000 := by
  show ((Kraken.Executable.withAddresses (layoutL lprog)).findSome?
    (fun (p, d, _) => if d = .label "l" then some p else none)).getD (-1) = _
  rw [Layout.ofSize_apply, lprog_eq]
  simp only [List.map, withAddresses_cons, withAddresses_nil]
  decide

/-- The tree at the `cbz`: back to the head if `x2 = 0`, else to the end. -/
theorem exec_mid (r : Reg64s) :
    isaLSE2.exec (atL r 0x100004) = some (.done
      (atL r (if r.getRegOrZr (.low (.reg .X2) .W64) = 0 then 0x100000 else 0x100008))) := by
  have hbt : branchTarget (atL r 0x100004) 4 (.label "l") = 0x100000 := lab_l
  rw [exec_cbz (cellAt_of_codeAt validL (by dsimp only [atL]; decide) codeM : CellAt (atL r 0x100004) dC 4)]
  split
  · rw [hbt]
  · rfl

/-- Writing `x2` keeps `x0`. -/
theorem set_x0 (r : Reg64s) (w : BitVec 64) :
    (r.setRegOrZr (.low (.reg .X2) .W64) w).getXReg .X0 = r.getXReg .X0 := by
  rfl

/-- Reading `x2` after writing it. -/
theorem set_x2 (r : Reg64s) (w : BitVec 64) :
    (r.setRegOrZr (.low (.reg .X2) .W64) w).getRegOrZr (.low (.reg .X2) .W64) = w := by
  simp [Reg64s.setRegOrZr, Reg64s.getRegOrZr, Reg64s.setRegOrZr64, Reg64s.getRegOrZr64]
  rfl

/-- **The spinning reader's event trees have the shape `LoopShape`.** -/
theorem loopShape : LoopShape isaLSE2 F Head Mid Exit where
  hd := by
    rintro _ ⟨r, rfl, h0⟩
    exact ⟨.acq, _, exec_head r h0, fun v => ⟨_, rfl, (set_x0 r _).trans h0, set_x2 r _⟩⟩
  md := by
    rintro v _ ⟨r, rfl, h0, h2⟩
    refine ⟨_, exec_mid r, ?_⟩
    rw [h2]
    by_cases hz : v.setWidth 64 = 0
    · simp only [hz, ↓reduceIte]
      exact .inr (.inl ⟨trivial, r, rfl, h0⟩)
    · simp only [hz, ↓reduceIte]
      exact .inr (.inr ⟨hz, r, rfl, h0, h2⟩)
  ex := by
    rintro _ _ ⟨r, rfl, -, -⟩
    exact A64.exec_end (by show ((0x100008 : Int64) == 0x100000 + 8) = true; decide)

theorem head_st1 : Head st1 := ⟨st1.st.1.regs, rfl, by decide⟩

variable {k : Promises.Knobs} {arch : WeakMem.Arch} {init : TermRun.Cfg → Prop}

/-! ## The theorems -/

/-- **The simulation step of the variant on AArch64**, stutter form. -/
theorem sim_step_loop_a64 {c c' : Config isaLSE2} {s : TermRun.Cfg} {tid : Nat}
    (hR : RelL F 1 st0 sW Head Mid Exit c s) (h : StepSemInf Arch.armv8 tid c c') :
    ∃ s', (SrcSem.ofStep progL k arch init).Run s [] s' ∧ RelL F 1 st0 sW Head Mid Exit c' s' :=
  sim_step_loop Arch.armv8 shape.toWShape loopShape hR h

/-- **The `Sim.sim` clause of the variant on AArch64**, with trace equality. -/
theorem sim_loop_a64 (rv : State → RegId → BitVec 64) (pl : State → BitVec 64 → Option (BitVec 64))
    (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase isaLSE2 Arch.armv8 rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase isaLSE2 Arch.armv8 rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep progL k arch (· = srcInitL)).Reach tr' s ∧ RelL F 1 st0 sW Head Mid Exit t.1 s ∧
        Scc.Sem.obs tr = tr' :=
  sim_clause_loop Arch.armv8 shape.toWShape loopShape head_st1 rv pl Λ μ

/-- `x0` and `x2` through the register observation. -/
theorem regVal_x0 (r : Reg64s) (pc : Int64) (h0 : r.getXReg .X0 = 0x1000) : regVal (atL r pc) (.x 0) = F := by
  simp [regVal, xregs, h0]

theorem regVal_x2 (r : Reg64s) (pc : Int64) :
    regVal (atL r pc) (.x 2) = r.getRegOrZr (.low (.reg .X2) .W64) := by
  simp [regVal, xregs, Reg64s.getRegOrZr, Reg64s.getRegOrZr64]
  rfl

/-- **Where the source words live**: `x0` holds the flag's address
throughout, `x2` the value read at the test and the exit. -/
theorem regsL : RegsL (I := isaLSE2) regVal F st0 sW Head Mid Exit (RegId.x 0) (RegId.x 2) where
  f0 := regs.f0
  fW := regs.fW
  hd := by rintro _ ⟨r, rfl, h0⟩; exact regVal_x0 r _ h0
  md := by rintro v _ ⟨r, rfl, h0, h2⟩; exact ⟨regVal_x0 r _ h0, (regVal_x2 r _).trans h2⟩
  ex := by rintro v _ ⟨r, rfl, h0, h2⟩; exact ⟨regVal_x0 r _ h0, (regVal_x2 r _).trans h2⟩

/-- **`Correct` for the variant on AArch64** under `layoutΛ`, every clause
discharged, progress included. -/
theorem correct_loop_a64 (pl : State → BitVec 64 → Option (BitVec 64)) (B : Scc.Sem.Budget) :
    Scc.Sem.Correct (Target.ofBase isaLSE2 Arch.armv8 regVal pl) (SrcSem.ofStep progL k arch (· = srcInitL))
      layoutΛ B (asmOf st0 st1 F) :=
  correctL Arch.armv8 loopShape shape.toWShape head_st1 regsL flagIn layoutΛ_wf B

end Spike.Bridge.A64Loop

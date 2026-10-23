/-
The bridge spike, spinning-reader variant on x64: the reader is
`l: movq (%rdi), %rax; cmpq $0, %rax; jz l`, the writer as in
`Spike/Bridge/X64.lean`. Labels occupy no bytes, every other cell one byte
(`exeL`). The test is `cmp` with an immediate rather than `test`: Kraken's
`test` leaves the auxiliary-carry flag unspecified (an event-tree choice),
while `cmp` gives a register-only `.done` tree.

* `loopShape`: the reader's event trees have the shape `LoopShape`
  (`Spike/Bridge/Loop.lean`): at a loop head (`Head`) one load of the flag;
  at the test (`Mid v`) the `cmp`, which stays at the test with the zero
  flag set iff `rax = 0`, then the `jz`, back to the head if the low 64 bits
  of the value read are `0`, to the end of the text otherwise;
* `sim_step_loop_x64`: every `StepSemInf Arch.tso` step from a related pair
  is matched by a source run with the empty trace (stutter form);
* `sim_loop_x64`: the `Sim.sim` clause for `Target.ofBase isa Arch.tso`
  against the spinning source program `progL`, with trace equality.
-/
import Spike.Bridge.X64
import Spike.Bridge.LoopCorrect

namespace Spike.Bridge.X64Loop

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Kraken.Promising.Live.Inf
open Scc.Sem (SrcSem Target)
open Spike.Bridge.X64 (F st0 sW mF dR shape regVal regs layoutΛ flagIn layoutΛ_wf)

/-- The spinning reader: a load of the flag at `rdi` into `rax`, until it is
non-zero. -/
def lprog : Program := parse("
l:
    movq (%rdi), %rax
    cmpq $0, %rax
    jz l
")

/-- The parsed `cmp`. -/
abbrev dT : Directive := op64 (.cmp (.reg (.low .rax .W64)) (.imm (.int64 0)))

/-- The parsed `jz`. -/
abbrev dJ : Directive := op64 (.jcc .z "l")

theorem lprog_eq : lprog = [.label "l", dR, dT, dJ] := by decide

/-- Cell sizes: labels none, every other directive one byte. -/
def lsize : Directive → Nat
  | .label _ => 0
  | _ => 1

/-- The reader's text at `0x100000`. -/
def exeL : _root_.Executable := Kraken.Layout.ofSize 0x100000 lsize lprog lprog

theorem exeL_snd : exeL.2 = [(.label "l", 0), (dR, 1), (dT, 1), (dJ, 1)] := by
  rw [exeL, Layout.ofSize_apply, lprog_eq]
  rfl

instance validL : Kraken.Executable.ValidLayout exeL where
  label_size i l z h := by
    rw [exeL_snd] at h
    rcases i with _ | _ | _ | _ | i <;> simp at h
    exact h.2.symm
  instr_size i d z h hd := by
    rw [exeL_snd] at h
    rcases i with _ | _ | _ | _ | i <;> simp at h
    · exact absurd h.1.symm (hd _)
    all_goals omega
  no_wrap := by rw [exeL_snd]; decide
  align_addr i aw w n pad z h := by
    rw [exeL_snd] at h
    rcases i with _ | _ | _ | _ | i <;> simp at h
    all_goals (obtain ⟨⟨rfl, rfl, h⟩, -⟩ := h; cases h)

/-- Thread `1`: `rdi = 0x1000`, at the loop head. -/
def st1 : State where
  exe := exeL
  endPc := 0x100000 + 3
  st := ({ regs := { rdi := 0x1000 } }, 0x100000)

/-- The reader with registers `r` and flags `fl` at `pc`. -/
abbrev atL (r : Reg64s) (fl : StatusFlags) (pc : Int64) : State :=
  { st1 with st := ({ st1.st.1 with regs := r, status := fl }, pc) }

/-- `rax`'s value. -/
abbrev rax (r : Reg64s) : BitVec 64 := r.get (.low .rax .W64)

/-- At the loop head, with the flag's address in `rdi`. -/
def Head (s : State) : Prop := ∃ r fl, s = atL r fl 0x100000 ∧ r.rdi = 0x1000

/-- At the test, with the flag's address in `rdi` and the value read in
`rax`: before the `cmp`, or before the `jz` with the zero flag set iff
`rax = 0`. -/
def Mid (v : Val) (s : State) : Prop :=
  ∃ r fl, r.rdi = 0x1000 ∧ rax r = v.setWidth 64 ∧
    (s = atL r fl 0x100001 ∨ (s = atL r fl 0x100002 ∧ (CondCode.z.interp fl = true ↔ rax r = 0)))

/-- At the end of the text, with the flag's address in `rdi` and the value
read in `rax`. -/
def Exit (v : Val) (s : State) : Prop :=
  ∃ r fl, s = atL r fl 0x100003 ∧ r.rdi = 0x1000 ∧ rax r = v.setWidth 64

/-! ## The instruction shapes -/

theorem code0 : Kraken.Executable.codeAt exeL 0x100000 = [(dR, 1), (dT, 1), (dJ, 1)] := by
  rw [exeL, Layout.ofSize_apply, lprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress, List.map,
    withAddresses_cons, withAddresses_nil]
  decide

theorem code1 : Kraken.Executable.codeAt exeL 0x100001 = [(dT, 1), (dJ, 1)] := by
  rw [exeL, Layout.ofSize_apply, lprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress, List.map,
    withAddresses_cons, withAddresses_nil]
  decide

theorem code2 : Kraken.Executable.codeAt exeL 0x100002 = [(dJ, 1)] := by
  rw [exeL, Layout.ofSize_apply, lprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress, List.map,
    withAddresses_cons, withAddresses_nil]
  decide

/-- The label `l` is the loop head. -/
theorem lab_l : (_root_.Executable.labels exeL).label "l" = 0x100000 := by
  show ((Kraken.Executable.withAddresses exeL).findSome?
    (fun (p, d, _) => if d = .label "l" then some p else none)).getD (-1) = _
  rw [exeL, Layout.ofSize_apply, lprog_eq]
  simp only [List.map, withAddresses_cons, withAddresses_nil]
  decide

/-- The tree at the loop head: one load of `⟨0x1000, 8⟩`. -/
theorem exec_head (r : Reg64s) (fl : StatusFlags) (h0 : r.rdi = 0x1000) :
    isa.exec (atL r fl 0x100000) = some (.load .plain false ⟨F, 8⟩ fun v =>
      .done (atL (r.set (.low .rax .W64) (v.setWidth 64)) fl 0x100001)) := by
  rw [exec_load_agrees (cellAt_of_codeAt validL (by dsimp only [atL]; decide) code0 :
      CellAt (atL r fl 0x100000) dR 1) (a := F)
    (by simp [h0, mF, eaddr, AddrExpr.interp]; rfl)
    (by simp [st1, Mem.loadInt, Mem.loadBytes, List.allSome]; rfl) rfl]
  rfl

/-- The tree at the `cmp`: flags only, the zero flag set iff `rax = 0`. -/
theorem exec_cmp (r : Reg64s) (fl : StatusFlags) :
    ∃ fl', isa.exec (atL r fl 0x100001) = some (.done (atL r fl' 0x100002)) ∧
      (CondCode.z.interp fl' = true ↔ rax r = 0) := by
  show ∃ fl', X64.exec _ = _ ∧ _
  rw [exec_of_cellAt (cellAt_of_codeAt validL (by dsimp only [atL]; decide) code1 :
      CellAt (atL r fl 0x100001) dT 1)]
  simp [Directive.interp, Instr.interp, Operation.interp, toEv, EvTree.map, Operand.interp, RegOrMem.interp,
    ConstExpr.interp]
  refine ⟨_, rfl, ?_⟩
  simp [StatusFlags.from_result]

/-- The tree at the `jz`: back to the head if the zero flag is set, else to
the end. -/
theorem exec_jz (r : Reg64s) (fl : StatusFlags) :
    isa.exec (atL r fl 0x100002) = some (.done
      (atL r fl (if CondCode.z.interp fl then 0x100000 else 0x100003))) := by
  rw [exec_jcc (cellAt_of_codeAt validL (by dsimp only [atL]; decide) code2 :
      CellAt (atL r fl 0x100002) dJ 1)]
  have hl : labelAddr (atL r fl 0x100002) "l" = 0x100000 := lab_l
  split
  · rw [hl]
  · rfl

/-- Writing `rax` keeps `rdi`. -/
theorem set_rdi (r : Reg64s) (w : BitVec 64) : (r.set (.low .rax .W64) w).rdi = r.rdi := rfl

/-- Reading `rax` after writing it. -/
theorem set_rax (r : Reg64s) (w : BitVec 64) : rax (r.set (.low .rax .W64) w) = w := by
  simp [Reg64s.set]

/-- **The spinning reader's event trees have the shape `LoopShape`.** -/
theorem loopShape : LoopShape isa F Head Mid Exit where
  hd := by
    rintro _ ⟨r, fl, rfl, h0⟩
    exact ⟨.plain, _, exec_head r fl h0, fun v => ⟨_, fl, (set_rdi r _).trans h0, set_rax r _, .inl rfl⟩⟩
  md := by
    rintro v _ ⟨r, fl, h0, h2, rfl | ⟨rfl, hz⟩⟩
    · obtain ⟨fl', hex, hz'⟩ := exec_cmp r fl
      exact ⟨_, hex, .inl ⟨r, fl', h0, h2, .inr ⟨rfl, hz'⟩⟩⟩
    · refine ⟨_, exec_jz r fl, ?_⟩
      rw [h2] at hz
      by_cases hv : v.setWidth 64 = 0
      · simp only [hz.mpr hv, ↓reduceIte]
        exact .inr (.inl ⟨hv, r, fl, rfl, h0⟩)
      · have : CondCode.z.interp fl = false := by
          cases h : CondCode.z.interp fl
          · rfl
          · exact absurd (hz.mp h) hv
        simp only [this, Bool.false_eq_true, ↓reduceIte]
        exact .inr (.inr ⟨hv, r, fl, rfl, h0, h2⟩)
  ex := by
    rintro _ _ ⟨r, fl, rfl, -, -⟩
    exact X64.exec_end (by show ((0x100003 : Int64) == 0x100000 + 3) = true; decide)

theorem head_st1 : Head st1 := ⟨st1.st.1.regs, st1.st.1.status, rfl, rfl⟩

variable {k : Promises.Knobs} {arch : WeakMem.Arch} {init : TermRun.Cfg → Prop}

/-! ## The theorems -/

/-- **The simulation step of the variant on x64**, stutter form. -/
theorem sim_step_loop_x64 {c c' : Config isa} {s : TermRun.Cfg} {tid : Nat}
    (hR : RelL F 1 st0 sW Head Mid Exit c s) (h : StepSemInf Arch.tso tid c c') :
    ∃ s', (SrcSem.ofStep progL k arch init).Run s [] s' ∧ RelL F 1 st0 sW Head Mid Exit c' s' :=
  sim_step_loop Arch.tso shape.toWShape loopShape hR h

/-- **The `Sim.sim` clause of the variant on x64**, with trace equality. -/
theorem sim_loop_x64 (rv : State → RegId → BitVec 64) (pl : State → BitVec 64 → Option (BitVec 64))
    (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase isa Arch.tso rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase isa Arch.tso rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep progL k arch (· = srcInitL)).Reach tr' s ∧ RelL F 1 st0 sW Head Mid Exit t.1 s ∧
        Scc.Sem.obs tr = tr' :=
  sim_clause_loop Arch.tso shape.toWShape loopShape head_st1 rv pl Λ μ

/-- `rdi` and `rax` through the register observation. -/
theorem regVal_rdi (r : Reg64s) (fl : StatusFlags) (pc : Int64) (h0 : r.rdi = 0x1000) :
    regVal (atL r fl pc) (.r .rdi) = F := by
  simp [regVal, Reg64s.get64, h0]

theorem regVal_rax (r : Reg64s) (fl : StatusFlags) (pc : Int64) : regVal (atL r fl pc) (.r .rax) = rax r := by
  simp [regVal, Reg64s.get64]

/-- **Where the source words live**: `rdi` holds the flag's address
throughout, `rax` the value read at the test and the exit. -/
theorem regsL : RegsL (I := isa) regVal F st0 sW Head Mid Exit (RegId.r .rdi) (RegId.r .rax) where
  f0 := regs.f0
  fW := regs.fW
  hd := by rintro _ ⟨r, fl, rfl, h0⟩; exact regVal_rdi r fl _ h0
  md := by
    rintro v _ ⟨r, fl, h0, h2, rfl | ⟨rfl, -⟩⟩ <;> exact ⟨regVal_rdi r fl _ h0, (regVal_rax r fl _).trans h2⟩
  ex := by rintro v _ ⟨r, fl, rfl, h0, h2⟩; exact ⟨regVal_rdi r fl _ h0, (regVal_rax r fl _).trans h2⟩

/-- **`Correct` for the variant on x64** under `layoutΛ`, every clause
discharged, progress included. -/
theorem correct_loop_x64 (pl : State → BitVec 64 → Option (BitVec 64)) (B : Scc.Sem.Budget) :
    Scc.Sem.Correct (Target.ofBase isa Arch.tso regVal pl) (SrcSem.ofStep progL k arch (· = srcInitL))
      layoutΛ B (asmOf st0 st1 F) :=
  correctL Arch.tso loopShape shape.toWShape head_st1 regsL flagIn layoutΛ_wf B

end Spike.Bridge.X64Loop

/-
The bridge spike on x64 (`isa`, `Arch.tso`): the writer's
`movq %rsi, (%rdi)` and the reader's `movq (%rdi), %rax`, parsed by Kraken's
x64 parser and laid out as the litmus driver does (one byte per cell), with
`rdi = 0x1000` (the flag) and `rsi = 1`. A release store and an acquire
load are plain moves on x64 (the store and load kinds are `plain`;
`Arch.tso` orders them).

`shape` discharges `Shape` from the per-row `exec` lemmas of
`Kraken.Promising.Lower.X64` (`exec_store_agrees`, `exec_load_agrees`);
everything else is the ISA-independent development of
`Spike/Bridge/Sim.lean`, instantiated as in `Spike/Bridge/A64.lean`:
`sim_step_x64`, `sim_x64`, `components_x64` (`rdi` holds the flag reference,
`rax` the value read), `correct_x64_of_progress`, and `progress_x64`,
`correct_x64` (progress discharged, `Spike/Bridge/Progress.lean`).
-/
import Spike.Bridge.Progress
import Kraken.Promising.Lower.EventsX64Inf
import Kraken.Promising.Lower.CodeSegX64
import Kraken.X64.Parser

namespace Spike.Bridge.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Kraken.Promising.Live.Inf
open Scc.Sem (SrcSem ExtMachine Target Correct Budget)

/-! ## The programs and start states -/

/-- The writer: a store of `rsi` to the flag at `rdi`. -/
def wprog : Program := parse("
  movq %rsi, (%rdi)
")

/-- The reader: a load of the flag at `rdi` into `rax`. -/
def rprog : Program := parse("
  movq (%rdi), %rax
")

/-- The address operand `(%rdi)`. -/
def mF : AddrExpr := { base := some (.reg .rdi), idx := none, disp := .int64 0 }

/-- The parsed store. -/
abbrev dW : Directive := op64 (.mov (.mem mF) (.reg (.low .rsi .W64)))

/-- The parsed load. -/
abbrev dR : Directive := op64 (.mov (.reg (.low .rax .W64)) (.mem mF))

theorem wprog_eq : wprog = [dW] := by decide
theorem rprog_eq : rprog = [dR] := by decide

/-- One byte per cell at `0x100000`, as the litmus driver lays out x64
text. -/
def exeOf (p : Program) : _root_.Executable := Kraken.Layout.ofSize 0x100000 (fun _ => 1) p p

/-- A one-instruction text laid out by `exeOf` is valid. -/
theorem valid_one {d : Directive} (hd : ∀ l, d ≠ .label l)
    (ha : ∀ aw w n pad, d ≠ .instr (.regular aw w (.nopalign n pad))) :
    Kraken.Executable.ValidLayout (exeOf [d]) where
  label_size i l z h := by
    rw [exeOf, Layout.ofSize_apply] at h
    rcases i with _ | i
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      exact absurd h.1 (hd l)
    · simp at h
  instr_size i d' z h _ := by
    rw [exeOf, Layout.ofSize_apply] at h
    rcases i with _ | i
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      omega
    · simp at h
  no_wrap := by rw [exeOf, Layout.ofSize_apply]; simp
  align_addr i aw w n pad z h := by
    rw [exeOf, Layout.ofSize_apply] at h
    rcases i with _ | i
    · simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
      exact absurd h.1 (ha aw w n pad)
    · simp at h

instance validW : Kraken.Executable.ValidLayout (exeOf wprog) := by
  rw [wprog_eq]
  exact valid_one (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)

instance validR : Kraken.Executable.ValidLayout (exeOf rprog) := by
  rw [rprog_eq]
  exact valid_one (fun _ h => by cases h) (fun _ _ _ _ h => by cases h)

/-- The flag's address. -/
abbrev F : BitVec 64 := 0x1000

/-- Thread `0`: `rdi = 0x1000`, `rsi = 1`. -/
def st0 : State where
  exe := exeOf wprog
  endPc := 0x100000 + 1
  st := ({ regs := { rdi := 0x1000, rsi := 1 } }, 0x100000)

/-- Thread `1`: `rdi = 0x1000`. -/
def st1 : State where
  exe := exeOf rprog
  endPc := 0x100000 + 1
  st := ({ regs := { rdi := 0x1000 } }, 0x100000)

/-- The writer after its store. -/
abbrev sW : State := after st0 1 st0.st.1

/-- The reader after loading `v`. -/
abbrev fR (v : Val) : State :=
  after st1 1 { st1.st.1 with regs := st1.st.1.regs.set (.low .rax .W64) (v.setWidth 64) }

/-! ## The instruction shapes -/

theorem codeW : Kraken.Executable.codeAt st0.exe st0.st.2 = [(dW, 1)] := by
  show Kraken.Executable.codeAt (exeOf wprog) 0x100000 = _
  rw [exeOf, Layout.ofSize_apply, wprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress,
    Kraken.Executable.withAddresses_dropWhile_start, Kraken.Executable.withAddresses_map_snd]
  decide

theorem codeR : Kraken.Executable.codeAt st1.exe st1.st.2 = [(dR, 1)] := by
  show Kraken.Executable.codeAt (exeOf rprog) 0x100000 = _
  rw [exeOf, Layout.ofSize_apply, rprog_eq]
  simp only [Kraken.Executable.codeAt, Kraken.Executable.directivesFromAddress,
    Kraken.Executable.withAddresses_dropWhile_start, Kraken.Executable.withAddresses_map_snd]
  decide

/-- The writer's tree: one plain store of `1` to `⟨0x1000, 8⟩`. -/
theorem exec_w : isa.exec st0 = some (.store .plain false ⟨F, 8⟩ 1 fun _ => .done sW) := by
  rw [exec_store_agrees (cellAt_of_codeAt validW (by decide) codeW : CellAt st0 dW 1) (a := F) (by decide)
    (by simp [st0, Mem.loadInt, Mem.loadBytes, List.allSome]; rfl) rfl]
  rfl

/-- The reader's tree: one plain load of `⟨0x1000, 8⟩`. -/
theorem exec_r : isa.exec st1 = some (.load .plain false ⟨F, 8⟩ fun v => .done (fR v)) := by
  rw [exec_load_agrees (cellAt_of_codeAt validR (by decide) codeR : CellAt st1 dR 1) (a := F) (by decide)
    (by simp [st1, Mem.loadInt, Mem.loadBytes, List.allSome]; rfl) rfl]

/-- At the end of the text there is no next instruction. -/
theorem exec_end {s : State} (h : (s.st.2 == s.endPc) = true) : isa.exec s = none := by
  simp only [isa]
  unfold Kraken.Promising.X64.exec
  split
  · rfl
  · rename_i h'; simp [h] at h'

theorem shape : Shape isa F 1 st0 sW st1 fR where
  wr := ⟨.plain, exec_w⟩
  wd := exec_end (by decide)
  rd := ⟨.plain, exec_r⟩
  rdd _ := exec_end (by show (st1.st.2 + Int64.ofNat 1 == st1.endPc) = true; decide)
  one := by decide

/-! ## The theorems -/

variable {k : Promises.Knobs} {arch : WeakMem.Arch}

/-- **The simulation step on x64.** -/
theorem sim_step_x64 {c c' : Config isa} {s : TermRun.Cfg} {tid : Nat} (hR : Rel F 1 st0 sW st1 fR c s)
    (h : StepSemInf Arch.tso tid c c') :
    ∃ s', SrcSem.StepBy prog k arch tid s s' ∧ Rel F 1 st0 sW st1 fR c' s' :=
  sim_step Arch.tso shape hR h

/-- **The `Sim.sim` clause on x64**, with trace equality. -/
theorem sim_x64 (rv : State → RegId → BitVec 64) (pl : State → BitVec 64 → Option (BitVec 64))
    (Λ : Scc.Sem.Layout) (μ : Scc.Sem.Marks) :
    ∀ t0 tr t, (Target.ofBase isa Arch.tso rv pl).load (asmOf st0 st1 F) Λ = some t0 →
      (Target.ofBase isa Arch.tso rv pl).M.Run μ t0 tr t →
      ∃ tr' s, (SrcSem.ofStep prog k arch (· = srcInit)).Reach tr' s ∧ Rel F 1 st0 sW st1 fR t.1 s ∧
        Scc.Sem.obs tr = tr' :=
  sim_clause_eq Arch.tso shape rv pl Λ μ

/-- The register observation: the 64-bit value of a general register (`0`
for the flags and the vector registers, which hold no source word here). -/
def regVal (s : State) : RegId → BitVec 64
  | .r r => s.st.1.regs.get64 r
  | _ => 0

theorem regs : Regs (I := isa) regVal F st0 sW st1 fR (RegId.r .rdi) (RegId.r .rax) where
  f0 := by decide
  fW := by decide
  f1 := by decide
  fAfter _ := rfl
  r _ := by simp [regVal, st1, Reg64s.set, Reg64s.set64, Reg64s.get64]

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

/-- **The components of `R` on x64**, under `layoutΛ`. -/
theorem components_x64 (pl : State → BitVec 64 → Option (BitVec 64))
    {t : (ExtMachine.ofBase isa Arch.tso regVal pl).Cfg} {s : TermRun.Cfg}
    (hR : Rel F 1 st0 sW st1 fR t.1 s) :
    Scc.Sem.Components (ExtMachine.ofBase isa Arch.tso regVal pl) layoutΛ
      (witness (I := isa) Arch.tso regVal pl F (RegId.r .rdi) (RegId.r .rax)) t s :=
  components shape regs flagIn hR

/-- **`Correct` on x64, given progress.** -/
theorem correct_x64_of_progress (pl : State → BitVec 64 → Option (BitVec 64)) (B : Budget)
    (hprog : ProgressOf (I := isa) Arch.tso regVal pl st0 st1 F) :
    Correct (Target.ofBase isa Arch.tso regVal pl) (SrcSem.ofStep prog k arch (· = srcInit)) layoutΛ B
      (asmOf st0 st1 F) :=
  correct_of_progress Arch.tso shape regs flagIn layoutΛ_wf B hprog

/-- **Progress on X64**: every configuration reachable from the loaded start
configuration has no faulting step, and every live thread can step. -/
theorem progress_x64 (pl : State → BitVec 64 → Option (BitVec 64)) :
    ProgressOf (I := isa) Arch.tso regVal pl st0 st1 F :=
  progressOf Arch.tso shape regVal pl

/-- **`Correct` on X64**, every clause discharged, progress included. -/
theorem correct_x64 (pl : State → BitVec 64 → Option (BitVec 64)) (B : Budget) :
    Correct (Target.ofBase isa Arch.tso regVal pl) (SrcSem.ofStep prog k arch (· = srcInit)) layoutΛ B
      (asmOf st0 st1 F) :=
  correct Arch.tso shape regs flagIn layoutΛ_wf B

end Spike.Bridge.X64

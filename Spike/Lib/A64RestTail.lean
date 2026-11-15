import Spike.Lib.RestTail
import Spike.Lib.A64LabelCongr
import Spike.Lib.A64TextTail
import Spike.Lib.A64ConsumerA
import Spike.Lib.StepOneMap
import Kraken.Promising.SLR.EnvG.A64MaskCore
import Scc.Sem.SysA64

/-!
**Relabelling an AArch64 thread's executable and end** (the AArch64 half of
the post-pass transfer of `Rest2A`).

A post-pass program differs from the program the stage-wise proof covers only
in a tail and in where a few labels sit. The transfer runs each target state
`s` of the stage-wise proof as `relab exe endPc s`: the same machine state,
under the post-pass executable and end. This file shows that one `isaLSE2`
step commutes with `relab` at a cell both executables hold, as long as the
cell names none of the labels that moved (`execLSE2_relab`).
-/

namespace Spike.Lib.A64RestTail

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt nextS jmpS execLSE2_of_cellAt execLSE2_of_cellAt_casp)
open Spike.Lib.A64LabelCongr (Directive.Free lse2_congr directive_congr)

/-- A thread with another executable and end. -/
def relab (exe : _root_.Executable) (endPc : Int64) (s : State) : State := { s with exe, endPc }

theorem evTree_map_map {σ τ υ : Type} (f : σ → τ) (g : τ → υ) :
    ∀ t : EvTree σ, EvTree.map g (EvTree.map f t) = EvTree.map (g ∘ f) t := by
  intro t
  induction t <;> simp only [EvTree.map] <;> (try congr 1) <;> (try funext b) <;> (try cases b) <;> simp_all

/-- **One `isaLSE2` step commutes with relabelling** at a cell `d` of `sz`
bytes that both `s`'s executable and `exe` hold at the pc, when the two
executables' labels agree off `B` and `d` names no label of `B`. -/
theorem execLSE2_relab {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} {B : List _root_.Label} (h : CellAt s d sz)
    (h' : CellAt (relab exe endPc s) d sz)
    (hL : ∀ l, l ∉ B → (_root_.Executable.labels exe).label l = (_root_.Executable.labels s.exe).label l)
    (hf : Directive.Free B d) :
    execLSE2 (relab exe endPc s) = (execLSE2 s).map (EvTree.map (relab exe endPc)) := by
  cases hx : d.isCaspX
  · rw [execLSE2_of_cellAt h' hx, execLSE2_of_cellAt h hx, Option.map_some, evTree_map_map]
    show some (EvTree.map _ (toEv s.decls (@Directive.interpLSE2 (_root_.Executable.labels exe) d
      s.st.1 (.mk s.st.2 (s.st.2 + .ofNat sz)) (nextS s sz) jmpS))) = _
    rw [lse2_congr _ _ hL d hf]
    rfl
  · rw [execLSE2_of_cellAt_casp h' hx, execLSE2_of_cellAt_casp h hx, Option.map_some, evTree_map_map]
    show some (EvTree.map _ (toEvCASP s.decls (@Directive.interp (_root_.Executable.labels exe) d
      s.st.1 (.mk s.st.2 (s.st.2 + .ofNat sz)) (nextS s sz) jmpS))) = _
    rw [directive_congr _ _ hL d hf]
    rfl

/-- **An `isaLSE2` step only moves the machine state**: its tree is a tree of
machine states, each leaf `s` with that machine state. -/
theorem execLSE2_shape {s : State} {t : EvTree State} (hx : execLSE2 s = some t) :
    ∃ t0 : EvTree MachineState, t = t0.map fun st => { s with st } := by
  unfold execLSE2 at hx
  split at hx
  · cases hx
  · split at hx
    · cases hx; exact ⟨_, rfl⟩
    · split at hx
      · cases hx; exact ⟨_, rfl⟩
      · unfold exec at hx
        split at hx
        · cases hx
        · cases hx; exact ⟨_, rfl⟩

/-- Relabelling back undoes relabelling, at a state of the first executable
and end. -/
theorem relab_relab {exe exe' : _root_.Executable} {endPc endPc' : Int64} {s : State} (he : s.exe = exe)
    (hn : s.endPc = endPc) : relab exe endPc (relab exe' endPc' s) = s := by
  cases s; cases he; cases hn; rfl

/-- `State.directive` is the first cell of `codeAt` at the pc. -/
private theorem directive_eq_codeAt (s : State) :
    s.directive = ((Kraken.Executable.codeAt s.exe s.st.2).head?).map (·.1) := by
  unfold State.directive Kraken.Executable.codeAt
  congr 3

/-- **A step that neither halts nor faults is at an instruction cell**: in a
validly laid-out executable, `isaLSE2` stepping `s` to a tree other than a
fault means the pc is short of the end and at an instruction (a data cell's
step is a fault). -/
theorem instr_of_execLSE2 {s : State} (hv : Kraken.Executable.ValidLayout s.exe) {t : EvTree State}
    (hx : execLSE2 s = some t) (hf : ∀ m, t ≠ .fault m) : ∃ i z, CellAt s (.instr i) z := by
  have hne : (s.st.2 == s.endPc) = false := by
    unfold execLSE2 at hx
    cases h : (s.st.2 == s.endPc)
    · rfl
    · simp [h] at hx
  have hdir : s.directive.isSome := by
    unfold execLSE2 at hx
    cases h : s.directive
    · simp [h] at hx
    · rfl
  rw [directive_eq_codeAt] at hdir
  obtain ⟨⟨d, z⟩, rest, hc⟩ : ∃ c rest, Kraken.Executable.codeAt s.exe s.st.2 = c :: rest := by
    cases h : Kraken.Executable.codeAt s.exe s.st.2 with
    | nil => rw [h] at hdir; cases hdir
    | cons c rest => exact ⟨c, rest, rfl⟩
  have hcell : CellAt s d z := ⟨hv, hne, rest, hc⟩
  cases d with
  | instr i => exact ⟨i, z, hcell⟩
  | label l =>
    unfold Kraken.Executable.codeAt at hc
    have hl := List.head_dropWhile_not (fun c : Directive × Nat => c.1.isLabel) (by rw [hc]; nofun)
    have hh : (List.dropWhile (fun c : Directive × Nat => c.1.isLabel)
        (Kraken.Executable.directivesFromAddress s.exe s.st.2)).head (by rw [hc]; nofun) = (.label l, z) := by
      simp only [hc, List.head_cons]
    rw [hh] at hl
    cases hl
  | byteArray a =>
    rw [execLSE2_of_cellAt hcell rfl] at hx
    cases hx
    exact absurd rfl (hf _)
  | zeros n =>
    rw [execLSE2_of_cellAt hcell rfl] at hx
    cases hx
    exact absurd rfl (hf _)

section Abi

open Scc.Sem Scc.Sem.A64

variable {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive} {sz : Nat}

/-- **The kernel's view commutes with relabelling** at a cell both
executables hold: the system call, its number, arguments, return and the
states the kernel may resume in. -/
theorem abi_relab (h : CellAt s d sz) (h' : CellAt (relab exe endPc s) d sz) :
    abi.atSys (relab exe endPc s) = abi.atSys s ∧ abi.nr (relab exe endPc s) = abi.nr s ∧
      abi.arg (relab exe endPc s) = abi.arg s ∧
      (∀ x, abi.ret (relab exe endPc s) x = relab exe endPc (abi.ret s x)) ∧
      (∀ call, Kernel.certSuccs abi (relab exe endPc s) call = (Kernel.certSuccs abi s call).map (relab exe endPc)) := by
  have hn : nextPc (relab exe endPc s) = nextPc s := by
    rw [Scc.Sem.A64.nextPc_of_cellAt h', Scc.Sem.A64.nextPc_of_cellAt h]; rfl
  have hr : ∀ x, abi.ret (relab exe endPc s) x = relab exe endPc (abi.ret s x) := by
    intro x
    simp only [abi, hn]; rfl
  have hr' : ∀ a x, abi.ret (abi.setTp (relab exe endPc s) a) x = relab exe endPc (abi.ret (abi.setTp s a) x) := by
    intro a x
    have hn' : nextPc (abi.setTp (relab exe endPc s) a) = nextPc (abi.setTp s a) := hn
    simp only [abi] at hn' ⊢
    rw [hn']; rfl
  refine ⟨?_, rfl, rfl, hr, fun call => ?_⟩
  · show atSvc _ = atSvc _
    unfold atSvc; rw [Kraken.Promising.Lower.A64.CellAt.directive h, Kraken.Promising.Lower.A64.CellAt.directive h']
  · have hm : ∀ l : List (BitVec 64), l.map (abi.ret (relab exe endPc s)) = (l.map (abi.ret s)).map (relab exe endPc) :=
      fun l => by
        induction l with
        | nil => rfl
        | cons x l ih => exact (congrArg (· :: _) (hr x)).trans (congrArg (_ :: ·) ih)
    cases call <;> first
      | exact hm _
      | (show [_] = [_]; rw [hr'])

end Abi

open Spike.Lib.A64ConsumerS (InvS TakePathS) in
open Spike.Lib.A64ConsumerA (NodesA) in
/-- **Every pair of the node obligations is at an instruction cell**, in a
validly laid-out executable: at a system call the `svc` (`NodesA.svc`), at
the take site its `nop` (`TakePathS.site`), elsewhere the row's
instruction, which does not fault (`OutS.exec_ne_fault`). -/
theorem instr_of_nodes {Λ : Scc.Sem.Layout} {p : CoreTerm.Prog} {μ : Scc.Sem.Marks}
    {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : Spike.Lib.A64ConsumerS.OwnS}
    {ar : Spike.Lib.Arena} {I : InvS} {ab : Option (State → Prop)} {rS : Scc.Sem.Range} {Tk : State → Prop}
    (hN : NodesA Λ p μ rd G own ar I ab) (hT : TakePathS Λ p μ I rS Tk) {lbl lsize s c fs}
    (hI : I lbl lsize s c fs) (hv : Kraken.Executable.ValidLayout s.exe) : ∃ i z, CellAt s (.instr i) z := by
  cases hs : Scc.Sem.A64.abi.atSys s
  · by_cases ht : ∃ a, μ.site .take = some a ∧ Scc.Sem.A64.pcOf s = a
    · obtain ⟨a, ha, hpc⟩ := ht
      obtain ⟨-, ⟨z, hz⟩, -⟩ := hT.site lbl lsize s c fs hI a ha hpc
      exact ⟨_, z, hz⟩
    · have hO := hN.out lbl lsize s c fs hI (fun a ha hpc => ht ⟨a, ha, hpc⟩) (by simp [hs])
      have hK : ∀ fs₁, (Spike.Lib.A64ConsumerA.msOfAX Λ μ p rd G own ar I ab lbl lsize fs₁).K =
          some Scc.Sem.A64.abi := by
        intro fs₁; cases ab <;> rfl
      have hnsys : ∀ fs₁ K, (Spike.Lib.A64ConsumerA.msOfAX Λ μ p rd G own ar I ab lbl lsize fs₁).K = some K →
          K.atSys s = true → False := by
        intro fs₁ K hK' hK''
        rw [hK] at hK'; cases hK'
        exact absurd hK'' (by simp [hs])
      obtain ⟨t, ht⟩ : ∃ t, execLSE2 s = some t := by
        rcases Spike.Lib.RestTail.OutS.exec_or_sys hO with h | ⟨fs₁, K, h1, h2⟩
        · exact Option.isSome_iff_exists.mp h
        · exact (hnsys fs₁ K h1 h2).elim
      refine instr_of_execLSE2 hv ht fun m hm => ?_
      rcases Spike.Lib.RestTail.OutS.exec_ne_fault hO m with h | ⟨fs₁, K, h1, h2⟩
      · exact h (hm ▸ ht)
      · exact hnsys fs₁ K h1 h2
  · obtain ⟨imm, z, hz⟩ := hN.svc lbl lsize s c fs hI hs
    exact ⟨_, z, hz⟩

/-- **The register dependencies commute with relabelling** at a shared cell
naming no moved label: both read the cell, and `depsLSE2`'s 16-byte `STP`
test the cell's address. -/
theorem depsLSE2_relab {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} {B : List _root_.Label} (h : CellAt s d sz) (h' : CellAt (relab exe endPc s) d sz)
    (hL : ∀ l, l ∉ B → (_root_.Executable.labels exe).label l = (_root_.Executable.labels s.exe).label l)
    (hf : Directive.Free B d) :
    depsLSE2 (relab exe endPc s) = depsLSE2 s := by
  obtain ⟨-, -, r, hc⟩ := h
  obtain ⟨-, -, r', hc'⟩ := h'
  have hd := EnvG.directive_of_codeAt hc
  have hd' := EnvG.directive_of_codeAt hc'
  have hdeps : deps (relab exe endPc s) = deps s := by
    unfold deps; rw [hd, hd']; rfl
  unfold depsLSE2
  rw [hdeps, hd, hd']
  obtain ⟨exe0, e0, ⟨m, pc⟩, sp, ds⟩ := s
  dsimp only [relab] at hL ⊢
  split
  · rename_i heq
    cases heq
    rename_i dst
    have he : ∀ s p, @AddrExpr.eval (relab exe endPc
        { exe := exe0, endPc := e0, st := (m, pc), showPc := sp, decls := ds }).exe.labels dst s p =
        @AddrExpr.eval exe0.labels dst s p :=
      Spike.Lib.A64LabelCongr.addrEval_congr _ _ hL dst hf
    simp only [he]
  · rfl

open Spike.Lib.StepOneMap (stepOne_map) in
open Kraken.Promising.Live.RunnerSim (mapT mapO) in
/-- **One instruction of a relabelled thread is the instruction, relabelled**,
at a cell both executables hold that names no moved label. -/
theorem stepOne_relab (A : Arch) {exe : _root_.Executable} {endPc : Int64} {t : Thread isaLSE2}
    {d : Directive} {sz : Nat} {B : List _root_.Label} (h : CellAt t.st d sz)
    (h' : CellAt (relab exe endPc t.st) d sz)
    (hL : ∀ l, l ∉ B → (_root_.Executable.labels exe).label l = (_root_.Executable.labels t.st.exe).label l)
    (hf : Directive.Free B d) (tid : Nat) (mem : Memory) :
    stepOne A (mapT (relab exe endPc) t) tid mem =
      (stepOne A t tid mem).map (List.map (Except.map (mapO (relab exe endPc)))) :=
  stepOne_map A (execLSE2_relab h h' hL hf) (depsLSE2_relab h h' hL hf) rfl tid mem

end Spike.Lib.A64RestTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64RestTail.execLSE2_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64RestTail.execLSE2_relab

/-- info: 'Spike.Lib.A64RestTail.stepOne_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64RestTail.stepOne_relab

/-- info: 'Spike.Lib.A64RestTail.instr_of_execLSE2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64RestTail.instr_of_execLSE2

/-- info: 'Spike.Lib.A64RestTail.instr_of_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64RestTail.instr_of_nodes

/-- info: 'Spike.Lib.A64RestTail.abi_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64RestTail.abi_relab

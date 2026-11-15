/-
**An x86-64 thread state under another executable and end** (for moving
the consumer obligations from a text to the same text with a tail
appended): `relab exe endPc s` keeps the machine state, and its step is the
step of `s` with every leaf relabelled where the pc is at the same cell in
both executables and the two label tables agree at the labels the cell
names (`Spike/Lib/X64LabelCongr.lean`).

- `relab`: the state with another executable and end;
- `evTree_map_map`: mapping a tree twice;
- `exec_relab`: the step under another executable, from the step's equality;
- `exec_relab_cell`: the same at a cell both executables have
  (`Kraken.Promising.Lower.X64.exec_of_cellAt`), the label tables agreeing
  off the labels the cell does not name;
- `directive_of_cellAt`, `deps_relab_cell`: the directive and the register
  dependencies at such a cell;
- `stepOne_relab`: one instruction of the relabelled thread is the
  instruction, relabelled (`Spike/Lib/StepOneMap.lean`).
-/
import Kraken.Promising.Lower.EventsX64
import Spike.Lib.X64LabelCongr
import Spike.Lib.StepOneMap

namespace Spike.Lib.X64RestTail

open Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.Lower.X64 (CellAt exec_of_cellAt)

/-- A thread state with another executable and end. -/
def relab (exe : _root_.Executable) (endPc : Int64) (s : State) : State := { s with exe, endPc }

@[simp] theorem relab_st (exe : _root_.Executable) (endPc : Int64) (s : State) :
    (relab exe endPc s).st = s.st := rfl

/-- Mapping a tree twice is mapping it once by the composite. -/
theorem evTree_map_map {σ τ υ : Type} (f : σ → τ) (g : τ → υ) :
    ∀ t : EvTree σ, EvTree.map g (EvTree.map f t) = EvTree.map (g ∘ f) t
  | .done _ => rfl
  | .fault _ => rfl
  | .choose _ k => by simp only [EvTree.map]; congr 1; funext i; exact evTree_map_map f g (k i)
  | .load _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map f g (ret v)
  | .store _ _ _ _ ret => by simp only [EvTree.map]; congr 1; funext b; exact evTree_map_map f g (ret b)
  | .rmw _ _ _ _ ret => by simp only [EvTree.map]; congr 1; funext v; exact evTree_map_map f g (ret v)
  | .fence _ ret => by simp only [EvTree.map]; congr 1; funext u; exact evTree_map_map f g (ret u)

/-- **The step of a state under another executable and end**: where the pc
is at neither end, the directive under both executables exists or not alike,
and the instruction's step is the same, the tree is the old one with every
leaf relabelled. -/
theorem exec_relab {exe : _root_.Executable} {endPc : Int64} {s : State}
    (hne : (s.st.2 == endPc) = false) (hne0 : (s.st.2 == s.endPc) = false)
    (hdir : (relab exe endPc s).directive.isNone = s.directive.isNone)
    (hstep : _root_.Executable.step exe s.st (fun s' => .done s') =
      _root_.Executable.step s.exe s.st (fun s' => .done s')) :
    exec (relab exe endPc s) = (exec s).map (EvTree.map (relab exe endPc)) := by
  have he : (relab exe endPc s).endPc = endPc := rfl
  have hx : (relab exe endPc s).exe = exe := rfl
  have hd : (relab exe endPc s).decls = s.decls := rfl
  unfold exec
  rw [he, relab_st, hne, hne0, hdir, hx, hd, hstep]
  cases s.directive.isNone
  · simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte, Option.map_some, evTree_map_map]
    rfl
  · rfl

/-- **The step at a cell under another executable and end**: the cell is
the same in both (`hE`, `hF`), the two label tables agree off `B`, and the
cell names no label of `B`; the tree is the old one with every leaf
relabelled. -/
theorem exec_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive} {sz : Nat}
    {B : List Label} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz)
    (hL : ∀ l, l ∉ B → (_root_.Executable.labels exe).label l = (_root_.Executable.labels s.exe).label l)
    (hf : Spike.Lib.X64LabelCongr.Directive.Free B d) :
    exec (relab exe endPc s) = (exec s).map (EvTree.map (relab exe endPc)) := by
  rw [exec_of_cellAt hF, exec_of_cellAt hE]
  simp only [Option.map_some, evTree_map_map]
  have hx : (relab exe endPc s).exe = exe := rfl
  rw [hx, Spike.Lib.X64LabelCongr.directive_congr hL hf]
  rfl

/-- The directive of a state at a cell is the cell's. -/
theorem directive_of_cellAt {s : State} {d : Directive} {sz : Nat} (h : CellAt s d sz) :
    s.directive = some d := by
  obtain ⟨-, -, rest, hcode⟩ := h
  unfold State.directive
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress s.exe s.st.2) =
      Kraken.Executable.codeAt s.exe s.st.2 from by
    unfold Kraken.Executable.codeAt
    congr 1, hcode]
  rfl

/-- **The register dependencies at a cell both executables have** are the
same: they read only the cell. -/
theorem deps_relab_cell {exe : _root_.Executable} {endPc : Int64} {s : State} {d : Directive}
    {sz : Nat} (hE : CellAt s d sz) (hF : CellAt (relab exe endPc s) d sz) :
    deps (relab exe endPc s) = deps s := by
  unfold deps
  rw [directive_of_cellAt hE, directive_of_cellAt hF]

open Spike.Lib.StepOneMap (stepOne_map) in
open Kraken.Promising.Live.RunnerSim (mapT mapO) in
/-- **One instruction of a relabelled thread is the instruction, relabelled**,
at a cell both executables hold that names no moved label. -/
theorem stepOne_relab (A : Arch) {exe : _root_.Executable} {endPc : Int64} {t : Thread isa}
    {d : Directive} {sz : Nat} {B : List Label} (h : CellAt t.st d sz)
    (h' : CellAt (relab exe endPc t.st) d sz)
    (hL : ∀ l, l ∉ B → (_root_.Executable.labels exe).label l = (_root_.Executable.labels t.st.exe).label l)
    (hf : Spike.Lib.X64LabelCongr.Directive.Free B d) (tid : Nat) (mem : Memory) :
    stepOne A (mapT (relab exe endPc) t) tid mem =
      (stepOne A t tid mem).map (List.map (Except.map (mapO (relab exe endPc)))) :=
  stepOne_map A (exec_relab_cell h h' hL hf) (deps_relab_cell h h') rfl tid mem

end Spike.Lib.X64RestTail

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64RestTail.exec_relab_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64RestTail.exec_relab_cell

/-- info: 'Spike.Lib.X64RestTail.stepOne_relab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64RestTail.stepOne_relab

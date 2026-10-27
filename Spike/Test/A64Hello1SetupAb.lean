/-
**`hello1`'s setup frame's aborts never end** (AArch64; `SetupOpenA.hab`
of `Spike/Test/A64Hello1HS.lean`; the twin of
`Spike/Test/X64Hello1SetupAb.lean`): the only aborts of a context's body
(`AbOf2`) are at its overflow label, whose source controls are at a
`let x = a + b` (`AbJ2`'s `OvfReady`) the walk reaches (`TailAt2`); the
setup block `rodata` of `hello1o` has none (`addFreeT`), so `AbOf2` is
empty there and a segment to any `Q` (`False` in `SetupOpenA.hab`). The
same holds for `main`, whose overflow label is the first half of its aborts'
fragment (`hello1_mainPreUA`).

- `abortN2_none_addFree`: at a compiled block whose body is `addFreeT`, no
  state is at its overflow label;
- `abOf2_seg_addFree`: the abort node's states there are a segment to
  anything;
- `hello1_rodata_addFree`, `hello1_main_addFree`: `hello1o`'s `rodata` and
  `main` are `addFreeT`;
- `hello1_setupHabA`: `SetupOpenA.hab`'s segment at `hello1o`, at every
  compiled index of `rodata`.
-/
import Spike.Lib.Src.AddFree
import Spike.Test.A64Hello1HS

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.LowerNode (compiled2 addFreeT tailOf_addFree TailAt2)

/-- **No state is at an addition-free block's overflow label**: its source
controls are at an addition (`OvfReady`) on the walk (`TailAt2`), and the
`j`th compiled block's body `addFreeT` (`hno`) has none. -/
theorem abortN2_none_addFree {p : Prog} {j : Nat} {d : Decl} (hno : addFreeT d.body = true)
    (hd : (compiled2 p)[j]? = some d) {i : Expr → String → Nat → Option Nat}
    {lbl : WeakMem.AllocLabel → Option Nat} {cx : Scc.Emit.A64.FnCtx} {lab : Label → Int64} {fp ra : BitVec 64}
    {c0 : Ctl} {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
    (s : State) (c : Ctl) :
    ¬ Spike.Lib.A64.Flow.At exe endPc R F (abortN2 i (TailAt2 p j) p lbl cx lab fp ra c0) s c := by
  rintro ⟨-, -, -, -, σ, -, -, ⟨⟨sv, lits, hAb, -, -, -, hT⟩, -⟩, -⟩
  obtain ⟨x, a, b, e, -, -, -, -, -, -, he, -⟩ := hAb.1
  exact tailOf_addFree (hT d hd) hno x a b e he

section Ctx

variable {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {p : Prog} {j : Nat} {d : Decl}

/-- **A context's aborts at an addition-free block never end**: at the
`j`th compiled block, its body `addFreeT` (`hno`), no state is at its
abort node (`abortN2_none_addFree`), so they are a segment to any `Q`. -/
theorem abOf2_seg_addFree (hno : addFreeT d.body = true)
    {c : FnCode2 exe prog endPc RaOk Cd i (TailAt2 p j) d} (hd : (compiled2 p)[j]? = some d)
    {W : FragS isaLSE2} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} {R : Spike.Lib.Region} {F : MachineData → Prop}
    {fs : List TermRun.Frame} {fp ra : BitVec 64} {G0 : Ctl → Prop} {Q : FragS isaLSE2} :
    SegWS W K p lbl ms (AbOf2 p lbl c R F fs fp ra G0) Q :=
  SegWS.empty fun s c' _ ⟨_, _, _, hA⟩ => abortN2_none_addFree hno hd s c' hA

end Ctx

/-- The program. -/
local notation "P1A" => Spike.Test.Hello1MainSrc.hello1o

/-- **`hello1o`'s setup block `rodata` is addition-free.** -/
theorem hello1_rodata_addFree : ∀ (j : Nat) (d : Decl), (compiled2 P1A)[j]? = some d → d.name = "rodata" →
    addFreeT d.body = true := by
  have hall : (compiled2 P1A).all (fun d => d.name != "rodata" || addFreeT d.body) = true := by decide
  intro j d hd hn
  have hm := List.all_eq_true.mp hall d (List.mem_of_getElem? hd)
  simpa [hn] using hm

/-- **`hello1o`'s `main` is addition-free** (the overflow half of its aborts'
fragment is empty: `abortN2_none_addFree`). -/
theorem hello1_main_addFree : addFreeT Spike.Test.Hello1MainSrc.mainD.body = true := by decide

/-- **`SetupOpenA.hab` at `hello1o`** (`abOf2_seg_addFree` at
`hello1_rodata_addFree`): at any compiled index `j` of `rodata` and any
code facts `c` at it, the abort node's states are a segment to `False`. -/
theorem hello1_setupHabA {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
    {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
    {i : Expr → String → Nat → Option Nat} {j : Nat} {d : Decl} (hd : (compiled2 P1A)[j]? = some d)
    (hn : d.name = "rodata") (c : FnCode2 exe prog endPc RaOk Cd i (TailAt2 P1A j) d)
    {W : FragS isaLSE2} {K : State → State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : List TermRun.Frame → MemSide isaLSE2} (R : Spike.Lib.Region) (F : MachineData → Prop)
    (fs : List TermRun.Frame) (fp ra : BitVec 64) (G0 : Ctl → Prop) :
    SegWS W K P1A lbl ms (AbOf2 P1A lbl c R F fs fp ra G0) (fun _ _ _ => False) :=
  abOf2_seg_addFree (hello1_rodata_addFree j d hd hn) hd

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.abortN2_none_addFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abortN2_none_addFree

/-- info: 'Spike.Lib.LowerA64.abOf2_seg_addFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms abOf2_seg_addFree

/-- info: 'Spike.Lib.LowerA64.hello1_rodata_addFree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms hello1_rodata_addFree

/-- info: 'Spike.Lib.LowerA64.hello1_main_addFree' depends on axioms: [propext] -/
#guard_msgs in #print axioms hello1_main_addFree

/-- info: 'Spike.Lib.LowerA64.hello1_setupHabA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_setupHabA

end Spike.Lib.LowerA64

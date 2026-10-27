/-
**The allocation premises at a walk with no allocation** (x86-64): at a
walk predicate `T` holding at no allocation's `let` (e.g. plan b1's
restriction `T ∧ Tr` to the points after a program's only allocation),
`CxLB`'s two fields reading the walk hold vacuously: the allocator's `W2`
instance `AllocW2At` (its premise `T (.let_ x (.newBuf cn τ) e)`) and the
heap aborts' states (a heap abort exit carries a control of its call node,
whose term `NbJcOf` makes an allocation's `let`, at `T`).

- `allocW2At_noNb`: `AllocW2At` at a walk with no allocation;
- `nbAb_noNb`: no heap abort exit from a call node whose controls are at a
  walk with no allocation.
-/
import Spike.Lib.LowerX64.NewBufC2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64.Flow.NewBuf (nbX)

/-- **`AllocW2At` at a walk with no allocation** (`CxLB.hAW` at such a walk). -/
theorem allocW2At_noNb {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    {W₀ : (WeakMem.AllocLabel → Option Nat) → (WeakMem.AllocLabel → Nat) → Frag isa}
    {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {ms : MemSide isa} {fp ra : BitVec 64} {tp : UInt64} {G0 : Ctl → Prop}
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}
    (hT : ∀ x cn τ e, ¬ T (.let_ x (.newBuf cn τ) e)) :
    AllocW2At p lbl lsize lcx fr Cd Bl W₀ K exe endPc R F ms fp ra tp G0 i T Lk :=
  fun _ _ _ x cn τ e _ _ _ _ _ _ _ _ _ _ _ hTe => (hT x cn τ e hTe).elim

/-- **No heap abort exit from a call node at a walk with no allocation**
(`CxLB.hAb` at such a walk): the exit's call node has a control of `Jc`
(`nbX`'s abort node), whose term is an allocation's `let` (`NbJcOf`) at `T`
(`hJT`). -/
theorem nbAb_noNb {i : Expr → String → Nat → Option Nat} {lbl : WeakMem.AllocLabel → Option Nat}
    {fr : Scc.Emit.X64.Frame} {T : Expr → Prop} (hT : ∀ x cn τ e, ¬ T (.let_ x (.newBuf cn τ) e))
    {Jc : Spike.Lib.X64.AS → Ctl → Prop} {ms : MemSide isa} {lab : Label → Int64} {R : Region} {fz : Int}
    {pcR : Int64} {exe : _root_.Executable} {endPc : Int64} {F : MachineData → Prop} {s : State} {c : Ctl}
    (hJ : NbJcOf i lbl fr Jc) (hJT : ∀ σ c', Jc σ c' → T c'.term)
    (hA : Spike.Lib.X64.At exe endPc R F (nbX ms lab lbl R fz pcR Jc .abort) s c) : False := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, σC, hJc, _⟩ := hA
  obtain ⟨-, x, cn, τ, e, he, -⟩ := hJ _ _ hJc
  exact hT x cn τ e (he ▸ hJT _ _ hJc)

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.allocW2At_noNb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.allocW2At_noNb

/-- info: 'Spike.Lib.LowerX64.nbAb_noNb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.nbAb_noNb

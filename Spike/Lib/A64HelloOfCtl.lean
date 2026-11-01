/-
**Node obligations of a fragment that holds at the node's controls** (AArch64; Flow-only): a block, a node and a
stack-checked prologue are inside a predicate `X` that every control of their invariant satisfies at every state,
with no outside moves. The start chain (`WeS`, `HrdS`) and the worker side (`FlagObl`) read the same three facts;
this leaf states them once below both (it imports only `A64Prologue`).

- `blk_ofCtl`: a block node (`BlkW`, so `NodeZA`).
- `nodeW_ofCtl`: a node (`NodeW`).
- `proW_ofCtl`: a prologue (`ProW`), its four parts by the two above.
-/
import Spike.Lib.A64Prologue

namespace Spike.Lib.A64.HelloPh.OfCtl

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (Frag Ctl Region MemSide)
open Spike.Lib.A64.Flow (ND AS BlkW NodeW ProW)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {X : Frag isaLSE2}

/-- **A block node inside a fragment holding at its controls.** -/
theorem blk_ofCtl {n : ND} {blk : List Directive} (h : ∀ σ c, n.J σ c → ∀ s, X s c) :
    BlkW X (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ _, fun _ h => h⟩

/-- **A node inside a fragment holding at its controls.** -/
theorem nodeW_ofCtl {n : ND} (h : ∀ σ c, n.J σ c → ∀ s, X s c) : NodeW X (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨by obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA; exact h σ c hJ s, fun _ h => h⟩

/-- **A prologue inside a fragment holding at its entry's controls.** -/
theorem proW_ofCtl {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)}
    {J : AS → Ctl → Prop} (h : ∀ σ c, J σ c → ∀ s, X s c) :
    ProW X (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J :=
  ⟨blk_ofCtl h, nodeW_ofCtl fun _ c ⟨σ0, hJ, _⟩ => h σ0 c hJ, blk_ofCtl fun _ c ⟨σ0, _, hJ, _⟩ => h σ0 c hJ,
    blk_ofCtl fun _ c ⟨σ0, _, hJ, _⟩ => h σ0 c hJ⟩

/-- Non-vacuity: the trivial predicate holds at every control, so every prologue is inside it (`ProW.triv`'s
statement through `proW_ofCtl`). -/
example {ms : MemSide isaLSE2} {pc0 Z lim : Int64} {L : Label} {ps : List (XReg × Int64)} {J : AS → Ctl → Prop} :
    ProW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms pc0 Z lim L ps J :=
  proW_ofCtl fun _ _ _ _ => trivial

end Spike.Lib.A64.HelloPh.OfCtl

/-- info: 'Spike.Lib.A64.HelloPh.OfCtl.blk_ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.OfCtl.blk_ofCtl

/-- info: 'Spike.Lib.A64.HelloPh.OfCtl.nodeW_ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.OfCtl.nodeW_ofCtl

/-- info: 'Spike.Lib.A64.HelloPh.OfCtl.proW_ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.OfCtl.proW_ofCtl

/-
**Node obligations of a fragment that holds at the node's controls** (x86-64; the twin of
`Spike/Lib/A64HelloOfCtl.lean`; Flow-only): a block, a node and a stack-checked prologue are inside a predicate
`X` that every control of their invariant satisfies at every state, with no outside moves. The start chain and
the worker side read the same three facts; this leaf states them once below both (it imports only
`X64CodeSegs`).

- `blk_ofCtl`: a block node (`BlkW`, so `NodeZA`).
- `nodeW_ofCtl`: a node (`NodeW`).
- `proW_ofCtl`: a prologue (`XProW`), its five parts by the two above.

## Differences from the AArch64 version

- The prologue is an `XProW` of five parts (the head, the check's address, its node, the limit's load and
  compare, the frame; AArch64 `ProW`'s four), with x86-64's size and spill parameters.
- Blocks carry their instructions' sizes (`List (Directive × Nat)`).
-/
import Spike.Lib.X64CodeSegs

namespace Spike.Lib.X64.HelloPh.OfCtl

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Frag Ctl Region MemSide)
open Spike.Lib.X64 (ND AS BlkW NodeW)
open Spike.Lib.X64.Flow (XProW)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {X : Frag isa}

/-- **A block node inside a fragment holding at its controls.** -/
theorem blk_ofCtl {n : ND} {blk : List (Directive × Nat)} (h : ∀ σ c, n.J σ c → ∀ s, X s c) :
    BlkW X (fun _ _ => False) exe endPc R F n blk :=
  fun _ σ c _ _ _ _ _ _ hJ _ _ _ _ _ => ⟨h σ c hJ _, fun _ h => h⟩

/-- **A node inside a fragment holding at its controls.** -/
theorem nodeW_ofCtl {n : ND} (h : ∀ σ c, n.J σ c → ∀ s, X s c) : NodeW X (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨by obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA; exact h σ c hJ s, fun _ h => h⟩

/-- **A prologue inside a fragment holding at its entry's controls.** -/
theorem proW_ofCtl {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop} (h : ∀ σ c, J σ c → ∀ s, X s c) :
    XProW X (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  ⟨blk_ofCtl h, blk_ofCtl fun _ c ⟨σ0, hJ, _⟩ => h σ0 c hJ, nodeW_ofCtl fun _ c ⟨σ0, hJ, _⟩ => h σ0 c hJ,
    blk_ofCtl fun _ c ⟨σ0, _, hJ, _⟩ => h σ0 c hJ, blk_ofCtl fun _ c ⟨σ0, _, hJ, _⟩ => h σ0 c hJ⟩

/-- Non-vacuity: the trivial predicate holds at every control, so every prologue is inside it. -/
example {ms : MemSide isa} {pc0 Z lim : Int64} {L : String} {zl zf z1 z2 zs : Nat}
    {ps : List (Reg64 × Int64 × Nat)} {J : AS → Ctl → Prop} :
    XProW (fun _ _ => True) (fun _ _ => False) exe endPc R F ms pc0 Z lim L zl zf z1 z2 zs ps J :=
  proW_ofCtl fun _ _ _ _ => trivial

end Spike.Lib.X64.HelloPh.OfCtl

/-- info: 'Spike.Lib.X64.HelloPh.OfCtl.blk_ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OfCtl.blk_ofCtl

/-- info: 'Spike.Lib.X64.HelloPh.OfCtl.nodeW_ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OfCtl.nodeW_ofCtl

/-- info: 'Spike.Lib.X64.HelloPh.OfCtl.proW_ofCtl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OfCtl.proW_ofCtl

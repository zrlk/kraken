/-
**hello.w's global owned-words map agrees with an instance at a node**
(AArch64; twin of `A64WakeOwnGNode`): the pointwise
agreement `SFactsSt2.congr` asks (`ownGH` the instance's owned words at the
state and at each `StSucc` successor) at a non-block node, from where
`ownGH` picks that instance (`Good2aH`, `Good2bH`, `GoodWH`) at the state
and at every state with its `sp` and `x30` past the cell. The successor
facts (`WakePh.Keep`, `keep_svc`, `keep_nop`, `keep_take`) are wake's,
program independent.

- `agree_node2aH`, `agree_node2bH`, `agree_nodeWH`: the agreement at a node.
-/
import Spike.Lib.A64HelloOwnGEq
import Spike.Lib.A64WakeOwnGNode

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc)
open Spike.Lib.A64.WakePh (Keep)

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Scc.Sem.Marks} {s : State}

/-- **`ownGH` agrees with `own2aH` at a node** where it picks `own2aH` at
the state and past its cell. -/
theorem agree_node2aH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : Good2aH L s) (hn : ∀ s', Keep s s' → Good2aH L s') :
    ownGH L a s = own2aH L a (ph2aH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = own2aH L a (ph2aH (pcOf s')) :=
  ⟨ownGH_2a hlab hs, fun s' h => ownGH_2a hlab (hn s' (hk s' h))⟩

/-- **`ownGH` agrees with `own2bH` at a node** where it picks `own2bH` at
the state and past its cell. -/
theorem agree_node2bH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : Good2bH L s) (hn : ∀ s', Keep s s' → Good2bH L s') :
    ownGH L a s = own2bH L a (ph2bH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = own2bH L a (ph2bH (pcOf s')) :=
  ⟨ownGH_2b hlab hs, fun s' h => ownGH_2b hlab (hn s' (hk s' h))⟩

/-- **`ownGH` agrees with `ownH` at a node** where it picks `ownH` at the
state and past its cell. -/
theorem agree_nodeWH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : GoodWH L s) (hn : ∀ s', Keep s s' → GoodWH L s') :
    ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s')) :=
  ⟨ownGH_W hlab hs, fun s' h => ownGH_W hlab (hn s' (hk s' h))⟩

/-- info: 'Spike.Lib.A64.HelloPh.agree_node2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.agree_node2aH

end Spike.Lib.A64.HelloPh

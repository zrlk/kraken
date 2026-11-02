/-
**hello.w's global owned-words map agrees with an instance at a node**
(x86-64; the twin of `Spike/Lib/A64HelloOwnGNode.lean`): the pointwise
agreement `SFactsSt2.congr` asks (`ownGH` the instance's owned words at the
state and at each `StSucc` successor) at a non-block node, from where
`ownGH` picks that instance at the state and at every state with its `%rsp`
and `%rbp` past the cell (wake's x86-64 `WakePh.Keep`, with its
`keep_syscall`, `keep_nop`, `keep_take`, program independent).

- `agree_nodeWH`: the agreement at a node where `ownGH` picks `ownH`.

## Differences from the AArch64 version

- `Keep` is wake's x86-64 one (`%rsp`, `%rbp` kept, for A64's `sp`, `x30`).
- `hlab` resolves labels by `Scc.Sem.X64.codeLabel lo helloCells`.
- A64's `agree_node2aH`, `agree_node2bH` (dead) are not twinned.
-/
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64WakeOwnGNode

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc)
open Spike.Lib.X64.WakePh (Keep)

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Scc.Sem.Marks} {s : State}

/-- **`ownGH` agrees with `ownH` at a node** where it picks `ownH` at the
state and past its cell. -/
theorem agree_nodeWH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : GoodWH L s) (hn : ∀ s', Keep s s' → GoodWH L s') :
    ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s')) :=
  ⟨ownGH_W hlab hs, fun s' h => ownGH_W hlab (hn s' (hk s' h))⟩

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.agree_nodeWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.agree_nodeWH

/-
**wake.w's worker fragment on x86-64: the definitions** (the x64 twin of
the head of `Spike/Lib/A64WakeAbOffW.lean`): the worker's fragment
`wakeZ lab` (the store point agrees on both sides, `wakePass`, and the pc is
off the abort exits and transfer sites, `AbOffL lab`), and the combination
of facts at the nodes.

- `wakeZ lab`: `wakePass ∧ AbOffL lab`; `wakeZ_pass`, `wakeZ_ab` its halves.
- `wakeZE exe kp`: `wakePass ∧ EndOff exe kp` (AArch64: in
  `A64WakeEndOff.lean`; here `EndOff` is `X64WakeEndOff`'s, and its
  node lemmas target this `wakeZE`).
- `nodeZ_and`, `thrZ_and`: the facts at the nodes combine.
- `nodeZ_wakeZ`, `thrZ_wakeZ`: `wakeZ` at the nodes from its halves.

**Unlike AArch64** (forced by the x64 shape): only the definitions and the
combination are here; the per-node `AbOffL` facts (AArch64's `nodeZ_ab` ..
`cZW` in the same file) are over the byte runs of
`Spike/Lib/X64AbOffLDef.lean` and the block-indexed `NodeZ`
(`Spike/Lib/X64WakeNN.lean`), and live with the x64 per-node `AbOff`
proofs; `ThrZ`'s prologue fields are at byte offsets `k ≤ 35` (AArch64:
the instructions after the stack check).
-/
import Spike.Lib.X64WakePass
import Spike.Lib.X64AbOffLDef
import Spike.Lib.X64WakeEndOff

namespace Spike.Lib.X64.Flow.Worker.Wake.AbOffZ

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker (NodeZ)
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZ)
open Spike.Lib.X64.Flow.Worker.Wake.Pass (wakePass)
open Spike.Lib.X64AbOffL (AbOffL)
open Spike.Lib.X64.Flow.Worker.Wake.EndOff (EndOff)

/-- **The worker's fragment**: the store point on both sides agrees
(`wakePass`) and the pc is off the abort exits and transfer sites. -/
def wakeZ (lab : Label → Int64) : Frag isa := fun s c => wakePass s c ∧ AbOffL lab s c

/-- **The worker's fragment with the end**: `wakePass` and off the end. -/
def wakeZE (exe : _root_.Executable) (kp : Nat) : Frag isa := fun s c => wakePass s c ∧ EndOff exe kp s c

theorem wakeZ_pass {lab : Label → Int64} {s : State} {c : Ctl} (h : wakeZ lab s c) : wakePass s c := h.1

theorem wakeZ_ab {lab : Label → Int64} {s : State} {c : Ctl} (h : wakeZ lab s c) : AbOffL lab s c := h.2

/-- Facts at a node combine. -/
theorem nodeZ_and {Z Z' : Frag isa} {exe : _root_.Executable} {n : ND} {blk : List (Directive × Nat)}
    (h : NodeZ Z exe n blk) (h' : NodeZ Z' exe n blk) : NodeZ (fun s c => Z s c ∧ Z' s c) exe n blk :=
  fun s σ c k hk he hs hJ => ⟨h s σ c k hk he hs hJ, h' s σ c k hk he hs hJ⟩

/-- Facts at the thread worker's nodes combine. -/
theorem thrZ_and {Z Z' : Frag isa} {exe : _root_.Executable} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZ Z exe c0 c1 c2 c3 A B tp sp0) (h' : ThrZ Z' exe c0 c1 c2 c3 A B tp sp0) :
    ThrZ (fun s c => Z s c ∧ Z' s c) exe c0 c1 c2 c3 A B tp sp0 where
  pro s σ c k hk he hs hJ := ⟨h.pro s σ c k hk he hs hJ, h'.pro s σ c k hk he hs hJ⟩
  head i := nodeZ_and (h.head i) (h'.head i)
  wpro rbp0 ra s σ c k hk he hs hJ := ⟨h.wpro rbp0 ra s σ c k hk he hs hJ, h'.wpro rbp0 ra s σ c k hk he hs hJ⟩
  wk rbp0 ra sp i := nodeZ_and (h.wk rbp0 ra sp i) (h'.wk rbp0 ra sp i)
  unpk rbp1 ra1 i := nodeZ_and (h.unpk rbp1 ra1 i) (h'.unpk rbp1 ra1 i)
  tail i := nodeZ_and (h.tail i) (h'.tail i)

/-- **`wakeZ` at a node** from `wakePass` and `AbOffL` there. -/
theorem nodeZ_wakeZ {lab : Label → Int64} {exe : _root_.Executable} {n : ND} {blk : List (Directive × Nat)}
    (h : NodeZ wakePass exe n blk) (h' : NodeZ (AbOffL lab) exe n blk) : NodeZ (wakeZ lab) exe n blk :=
  nodeZ_and h h'

/-- **`wakeZ` at the thread worker's nodes** from `wakePass` and `AbOffL`
there. -/
theorem thrZ_wakeZ {lab : Label → Int64} {exe : _root_.Executable} {c0 c1 c2 c3 : Ctl} {A B tp sp0 : BitVec 64}
    (h : ThrZ wakePass exe c0 c1 c2 c3 A B tp sp0) (h' : ThrZ (AbOffL lab) exe c0 c1 c2 c3 A B tp sp0) :
    ThrZ (wakeZ lab) exe c0 c1 c2 c3 A B tp sp0 :=
  thrZ_and h h'

/-- info: 'Spike.Lib.X64.Flow.Worker.Wake.AbOffZ.thrZ_wakeZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms thrZ_wakeZ

end Spike.Lib.X64.Flow.Worker.Wake.AbOffZ

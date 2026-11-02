/-
**hello.w's global owned-words map agrees with an instance on a block**
(x86-64; the twin of `Spike/Lib/A64HelloOwnGAgree.lean`): the agreement
`hag` of `BlkW.ownCongr2` for `ownGH` and one instance's owned words, from
where `ownGH` picks that instance (`Good2bH`, `GoodWH`) at the block's
states and their next states (`BlkW.leaf`). The pieces those are decided
from (`WakePh.inPc_iff`, `spPool_of`, `not_spPool_of`) are wake's x86-64
ones, program independent.

- `hag2bH`, `hagWH`: the agreement on a covered block.

## Differences from the AArch64 version

- Blocks are sized cells (the `k`-th pc `n.pc + cellOff blk k`), and
  `BlkW.leaf` takes no alignment `hal`, as in `X64WakeOwnGAgree`.
- `hlab` resolves labels by `Scc.Sem.X64.codeLabel lo helloCells`.
- A64's `hag2aH` (dead) is not twinned.
-/
import Spike.Lib.X64HelloOwnGEq
import Spike.Lib.X64WakeOwnGAgree

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64
open Spike.Lib.X64ConsumerA (StSucc)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

section Hag

variable {μ : Scc.Sem.Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}

/-- **`ownGH` agrees with `own2bH` on a covered block** where it picks `own2bH`
at every state and next state of the block's run. -/
theorem hag2bH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → Good2bH L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      Good2bH L s) :
    BlkW (fun s _ => ownGH L a s = own2bH L a (ph2bH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = own2bH L a (ph2bH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownGH_2b hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownGH_2b hlab (hP σ c hJ k hk s m hA he hn hs))

/-- **`ownGH` agrees with `ownH` on a covered block** where it picks `ownH`
at every state and next state of the block's run. -/
theorem hagWH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → GoodWH L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s) :
    BlkW (fun s _ => ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownGH_W hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownGH_W hlab (hP σ c hJ k hk s m hA he hn hs))

end Hag

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.hag2bH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hag2bH

/-- info: 'Spike.Lib.X64.HelloPh.hagWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hagWH

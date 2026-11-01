/-
**hello.w's global owned-words map agrees with an instance on a block**
(AArch64; twin of `A64WakeOwnGAgree`): the agreement `hag`
of `BlkW.ownCongr2` for `ownGH` and one instance's owned words, from where
`ownGH` picks that instance (`Good2aH`, `Good2bH`, `GoodWH`) at the block's
states and their next states (`BlkW.leaf`). The pieces those are decided
from (`WakePh.inPc_iff`, `spPool_of`, `not_spPool_of`) are wake's, program
independent.

- `hag2aH`, `hag2bH`, `hagWH`: the agreement on a covered block.
-/
import Spike.Lib.A64HelloOwnGEq
import Spike.Lib.A64WakeOwnGAgree

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow
open Spike.Lib.A64ConsumerA (StSucc)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

section Hag

variable {μ : Scc.Sem.Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List Directive} {blo bhi : Int}

/-- **`ownGH` agrees with `own2aH` on a covered block** where it picks `own2aH`
at every state and next state of the block's run. -/
theorem hag2aH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → Good2aH L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      Good2aH L s) :
    BlkW (fun s _ => ownGH L a s = own2aH L a (ph2aH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = own2aH L a (ph2aH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64ConsumerA.BlkW.leaf hcode hok hR hal hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownGH_2a hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownGH_2a hlab (hP σ c hJ k hk s m hA he hn hs))

/-- **`ownGH` agrees with `own2bH` on a covered block** where it picks `own2bH`
at every state and next state of the block's run. -/
theorem hag2bH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → Good2bH L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      Good2bH L s) :
    BlkW (fun s _ => ownGH L a s = own2bH L a (ph2bH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = own2bH L a (ph2bH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64ConsumerA.BlkW.leaf hcode hok hR hal hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownGH_2b hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownGH_2b hlab (hP σ c hJ k hk s m hA he hn hs))

/-- **`ownGH` agrees with `ownH` on a covered block** where it picks `ownH`
at every state and next state of the block's run. -/
theorem hagWH (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → GoodWH L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      GoodWH L s) :
    BlkW (fun s _ => ownGH L a s = ownH L a (phH (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownGH L a s' = ownH L a (phH (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.A64ConsumerA.BlkW.leaf hcode hok hR hal hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownGH_W hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownGH_W hlab (hP σ c hJ k hk s m hA he hn hs))

end Hag

/-- info: 'Spike.Lib.A64.HelloPh.hag2aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.hag2aH

end Spike.Lib.A64.HelloPh

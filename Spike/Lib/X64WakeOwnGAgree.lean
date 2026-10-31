/-
**wake.w's global owned-words map agrees with an instance on a block**
(x86-64; the twin of `Spike/Lib/A64WakeOwnGAgree.lean`): the agreement `hag`
of `BlkW.ownCongr2` for `ownG` and one instance's owned words, from where
`ownG` picks that instance (`Good2a`, `Good2b`, `GoodW`) at the block's
states and their next states (`BlkW.leaf`), and the pieces those are
decided from.

- `inPc_iff`: the pc range by the resolved labels.
- `spPool_of`, `not_spPool_of`: `%rsp` at a region address on or off the pool.
- `hag2a`, `hag2b`, `hagW`: the agreement on a covered block.

Where x86-64 differs from AArch64: blocks are sized cells (the `k`-th pc
`n.pc + cellOff blk k`), and `BlkW.leaf` takes no alignment `hal`.
-/
import Spike.Lib.X64WakeOwnGEq
import Spike.Lib.X64SpAgree

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64
open Spike.Lib.X64ConsumerA (StSucc)

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

/-- **The pc range by the resolved labels.** -/
theorem inPc_iff {l₁ l₂ : Label} {x₁ x₂ : Nat} (h₁ : (L.lab l₁).toBitVec.toNat = x₁)
    (h₂ : (L.lab l₂).toBitVec.toNat = x₂) : inPc L l₁ l₂ s ↔ x₁ ≤ pcOf s ∧ pcOf s < x₂ := by
  rw [inPc, h₁, h₂]

private theorem addr_toNat' {R : Region} {k : Int} (h0 : 0 ≤ (R.base.toNat : Int) + k)
    (h1 : (R.base.toNat : Int) + k < 2 ^ 64) : ((R.addr k).toNat : Int) = R.base.toNat + k := by
  have he : R.addr k = BitVec.ofInt 64 ((R.base.toNat : Int) + k) := by
    rw [Region.addr, BitVec.ofInt_add, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [he, BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide)),
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- **`%rsp` at a region address inside the pool's band is on a pool stack.** -/
theorem spPool_of {R : Region} {k : Int} (hsp : s.st.1.regs.rsp.toBitVec = R.addr k)
    (h0 : 0 ≤ (R.base.toNat : Int) + k) (h1 : (R.base.toNat : Int) + k < 2 ^ 64)
    (hlo : (L.Λ.stackPool.lo : Int) < R.base.toNat + k)
    (hhi : (R.base.toNat : Int) + k ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size) : spPool L s := by
  have := addr_toNat' h0 h1
  unfold spPool; rw [hsp]; omega

/-- **`%rsp` at a region address off the pool's band is not on a pool
stack.** -/
theorem not_spPool_of {R : Region} {k : Int} (hsp : s.st.1.regs.rsp.toBitVec = R.addr k)
    (h0 : 0 ≤ (R.base.toNat : Int) + k) (h1 : (R.base.toNat : Int) + k < 2 ^ 64)
    (hout : (R.base.toNat : Int) + k ≤ L.Λ.stackPool.lo ∨
      (L.Λ.stackPool.lo : Int) + L.Λ.stackPool.size < R.base.toNat + k) : ¬ spPool L s := by
  have := addr_toNat' h0 h1
  unfold spPool; rw [hsp]; omega

section Hag

variable {μ : Scc.Sem.Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {n : ND} {blk : List (Directive × Nat)} {blo bhi : Int}

/-- **`ownG` agrees with `own2a` on a covered block** where it picks `own2a`
at every state and next state of the block's run. -/
theorem hag2a (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → Good2a L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      Good2a L s) :
    BlkW (fun s _ => ownG L a s = own2a L a (ph2a (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = own2a L a (ph2a (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownG_2a hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownG_2a hlab (hP σ c hJ k hk s m hA he hn hs))

/-- **`ownG` agrees with `own2b` on a covered block** where it picks `own2b`
at every state and next state of the block's run. -/
theorem hag2b (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → Good2b L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      Good2b L s) :
    BlkW (fun s _ => ownG L a s = own2b L a (ph2b (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = own2b L a (ph2b (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownG_2b hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownG_2b hlab (hP σ c hJ k hk s m hA he hn hs))

/-- **`ownG` agrees with `ownW` on a covered block** where it picks `ownW`
at every state and next state of the block's run. -/
theorem hagW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo)
    (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → GoodW L s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      GoodW L s) :
    BlkW (fun s _ => ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s'))) (fun _ _ => False) exe endPc R F n blk :=
  Spike.Lib.X64ConsumerA.BlkW.leaf hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs => ownG_W hlab (hQ σ c hJ k hk s m hA he hn hs))
    (fun σ c hJ k hk s m hA he hn hs => ownG_W hlab (hP σ c hJ k hk s m hA he hn hs))

end Hag

/-- info: 'Spike.Lib.X64.WakePh.hag2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hag2a

/-- info: 'Spike.Lib.X64.WakePh.inPc_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.inPc_iff

/-- info: 'Spike.Lib.X64.WakePh.spPool_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.spPool_of

/-- info: 'Spike.Lib.X64.WakePh.not_spPool_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.not_spPool_of

/-- info: 'Spike.Lib.X64.WakePh.hag2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hag2b

/-- info: 'Spike.Lib.X64.WakePh.hagW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hagW

end Spike.Lib.X64.WakePh

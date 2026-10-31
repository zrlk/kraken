/-
**wake.w's global owned-words map agrees with an instance at a node**
(x86-64; the twin of `Spike/Lib/A64WakeOwnGNode.lean`): the pointwise
agreement `SFactsSt2.congr` asks (`ownG` the instance's owned words at the
state and at each `StSucc` successor) at a non-block node, from where `ownG`
picks that instance (`Good2a`, `Good2b`, `GoodW`) at the state and at every
state with its `%rsp` and `%rbp` past the cell.

The successors of a `syscall` (the kernel's resumptions, `abi.ret`) and of a
`nop` (its step, or the take's `setDmem` and `skip` at the take site) keep
`%rsp` and `%rbp` and move the pc to `nextPc` (`Keep`); so does the take at a
`syscall` state.

- `Keep`: `%rsp`, `%rbp` kept, the pc `nextPc`.
- `keep_pc`: `Keep`'s pc at a cell of size `sz`.
- `keep_take`: the take's successor.
- `keep_syscall`, `keep_nop`: a `syscall` state's and a `nop` cell's
  successors.
- `agree_node2a`, `agree_node2b`, `agree_nodeW`: the agreement at a node.

**Unlike AArch64**: `Keep` keeps `%rsp` and `%rbp` (the registers `raAddr`
reads) where A64 keeps `sp` and `x30`; the return address is a private word,
not a register, so `Keep` says nothing of it and the abort path's nodes are
`X64WakeOwnGAb`'s. `arch_prctl`'s resumption (it sets the `%fs` base) keeps
both registers too, so `keep_syscall` needs no `archSetFs` exclusion
(`keep_svc` on A64 excludes it by decoding).
-/
import Spike.Lib.X64WakeOwnGEq
import Spike.Lib.X64OwnCongr

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel pcOf nextPc abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc)

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Scc.Sem.Marks} {s : State}

/-- **`s'` is past `s`'s cell with `%rsp` and `%rbp` kept.** -/
def Keep (s s' : State) : Prop :=
  s'.st.1.regs.rsp = s.st.1.regs.rsp ∧ s'.st.1.regs.rbp = s.st.1.regs.rbp ∧ s'.st.2 = nextPc s

/-- **`Keep`'s pc at a cell** of size `sz`. -/
theorem keep_pc {d : Directive} {sz : Nat} {s' : State} (hc : Kraken.Promising.Lower.X64.CellAt s d sz)
    (h : Keep s s') : s'.st.2 = s.st.2 + Int64.ofNat sz := by
  rw [h.2.2, Scc.Sem.X64.nextPc_of_cellAt hc]

/-- **The take keeps `%rsp` and `%rbp`** and moves past the cell. -/
theorem keep_take (m : _root_.Mem 64) : Keep s (abi.skip (abi.setDmem s m)) :=
  ⟨rfl, rfl, rfl⟩

/-- **A `syscall` state's successors keep `%rsp` and `%rbp`**: the kernel's
resumptions write only `%rax`, `%rcx`, `%r11` (and `arch_prctl` the `%fs`
base), the take writes only memory. -/
theorem keep_syscall (hs : abi.atSys s = true) {s' : State} (h : StSucc μ s s') : Keep s s' := by
  rcases h with ⟨hs', -⟩ | ⟨-, call, -, hm⟩ | ⟨-, -, -, m, rfl⟩
  · rw [hs] at hs'; cases hs'
  · cases call with
    | archSetFs x =>
      simp only [Scc.Sem.Kernel.certSuccs] at hm
      rw [List.mem_singleton.mp hm]; exact ⟨rfl, rfl, rfl⟩
    | _ =>
      simp only [Scc.Sem.Kernel.certSuccs] at hm
      obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
      exact ⟨rfl, rfl, rfl⟩
  · exact keep_take m

/-- **A `nop` cell's successors keep `%rsp` and `%rbp`**: its step changes
only the pc, the take only memory. -/
theorem keep_nop {sz n : Nat} (hc : Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 (.nop n)) sz) {s' : State}
    (h : StSucc μ s s') : Keep s s' := by
  have hn : Scc.Sem.X64.atNop s = true := Scc.Sem.X64.atNop_of_cellAt hc
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs, -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_nop hc] at htr
    cases htr; cases hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · have := Scc.Sem.X64.not_atSys_of_atNop hn
    exact absurd hs (by rw [show abi.atSys s = Scc.Sem.X64.atSyscall s from rfl, this]; decide)
  · exact keep_take m

/-- **`ownG` agrees with `own2a` at a node** where it picks `own2a` at the
state and past its cell. -/
theorem agree_node2a (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : Good2a L s) (hn : ∀ s', Keep s s' → Good2a L s') :
    ownG L a s = own2a L a (ph2a (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = own2a L a (ph2a (pcOf s')) :=
  ⟨ownG_2a hlab hs, fun s' h => ownG_2a hlab (hn s' (hk s' h))⟩

/-- **`ownG` agrees with `own2b` at a node** where it picks `own2b` at the
state and past its cell. -/
theorem agree_node2b (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : Good2b L s) (hn : ∀ s', Keep s s' → Good2b L s') :
    ownG L a s = own2b L a (ph2b (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = own2b L a (ph2b (pcOf s')) :=
  ⟨ownG_2b hlab hs, fun s' h => ownG_2b hlab (hn s' (hk s' h))⟩

/-- **`ownG` agrees with `ownW` at a node** where it picks `ownW` at the
state and past its cell. -/
theorem agree_nodeW (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : GoodW L s) (hn : ∀ s', Keep s s' → GoodW L s') :
    ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s')) :=
  ⟨ownG_W hlab hs, fun s' h => ownG_W hlab (hn s' (hk s' h))⟩

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.keep_pc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keep_pc

/-- info: 'Spike.Lib.X64.WakePh.keep_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keep_take

/-- info: 'Spike.Lib.X64.WakePh.keep_syscall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keep_syscall

/-- info: 'Spike.Lib.X64.WakePh.keep_nop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.keep_nop

/-- info: 'Spike.Lib.X64.WakePh.agree_node2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.agree_node2a

/-- info: 'Spike.Lib.X64.WakePh.agree_node2b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.agree_node2b

/-- info: 'Spike.Lib.X64.WakePh.agree_nodeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.agree_nodeW

/-
**wake.w's global owned-words map agrees with an instance at a node**
(AArch64): the pointwise agreement `SFactsSt2.congr` asks (`ownG` the
instance's owned words at the state and at each `StSucc` successor) at a
non-block node, from where `ownG` picks that instance (`Good2a`, `Good2b`,
`GoodW`) at the state and at every state with its `sp` and `x30` past the
cell.

The successors of an `svc` (the kernel's resumptions, `abi.ret`) and of a
`nop` (its step, or the take's `setDmem` and `skip` at the take site) keep
`sp` and `x30` and move the pc to `nextPc` (`Keep`); so does the take at an
`svc` state.

- `Keep`: `sp`, `x30` kept, the pc `nextPc`.
- `keep_pc`: `Keep`'s pc at a cell of size `sz`.
- `keep_svc`, `keep_nop`: an `svc` state's and a `nop` cell's successors.
- `agree_node2a`, `agree_node2b`, `agree_nodeW`: the agreement at a node.
-/
import Spike.Lib.A64WakeOwnGEq
import Spike.Lib.A64OwnCongr

namespace Spike.Lib.A64.WakePh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf nextPc abi)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc)

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Scc.Sem.Marks} {s : State}

/-- **`s'` is past `s`'s cell with `sp` and `x30` kept.** -/
def Keep (s s' : State) : Prop :=
  s'.st.1.regs.SP = s.st.1.regs.SP ∧ s'.st.1.regs.X30 = s.st.1.regs.X30 ∧ s'.st.2 = nextPc s

/-- **`Keep`'s pc at a cell** of size `sz`. -/
theorem keep_pc {d : Directive} {sz : Nat} {s' : State} (hc : Kraken.Promising.Lower.A64.CellAt s d sz)
    (h : Keep s s') : s'.st.2 = s.st.2 + Int64.ofNat sz := by
  rw [h.2.2, Scc.Sem.A64.nextPc_of_cellAt hc]

/-- **The take keeps `sp` and `x30`** and moves past the cell. -/
theorem keep_take (m : _root_.Mem 64) : Keep s (abi.skip (abi.setDmem s m)) :=
  ⟨rfl, rfl, rfl⟩

/-- **An `svc` state's successors keep `sp` and `x30`**: the kernel's
resumptions write only `x0` (`archSetFs` is not an AArch64 call), the take
writes only memory. -/
theorem keep_svc (hs : abi.atSys s = true) {s' : State} (h : StSucc μ s s') : Keep s s' := by
  rcases h with ⟨hs', -⟩ | ⟨-, call, hd, hm⟩ | ⟨-, -, -, m, rfl⟩
  · rw [hs] at hs'; cases hs'
  · have heq : Scc.Sem.Kernel.certSuccs abi s call = (Scc.Sem.Kernel.results call).map (abi.ret s) := by
      cases call with
      | archSetFs x => exact absurd hd (Scc.Sem.A64.decode_a64_ne_archSetFs _ _ x)
      | _ => rfl
    rw [heq] at hm
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hm
    exact ⟨rfl, rfl, rfl⟩
  · exact keep_take m

/-- **A `nop` cell's successors keep `sp` and `x30`**: its step changes only
the pc, the take only memory. -/
theorem keep_nop {sz : Nat} (hc : Kraken.Promising.Lower.A64.CellAt s (.instr ⟨.W64, .NOP⟩) sz) {s' : State}
    (h : StSucc μ s s') : Keep s s' := by
  have hn : Scc.Sem.A64.atNop s = true := Scc.Sem.A64.atNop_of_cellAt hc
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs, -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.A64.exec_nop hc] at htr
    cases htr; cases hl
    exact ⟨rfl, rfl, (Scc.Sem.A64.nextPc_of_cellAt hc).symm⟩
  · have := Scc.Sem.A64.not_atSys_of_atNop hn
    exact absurd hs (by rw [show abi.atSys s = Scc.Sem.A64.atSvc s from rfl, this]; decide)
  · exact keep_take m

/-- **`ownG` agrees with `own2a` at a node** where it picks `own2a` at the
state and past its cell. -/
theorem agree_node2a (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : Good2a L s) (hn : ∀ s', Keep s s' → Good2a L s') :
    ownG L a s = own2a L a (ph2a (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = own2a L a (ph2a (pcOf s')) :=
  ⟨ownG_2a hlab hs, fun s' h => ownG_2a hlab (hn s' (hk s' h))⟩

/-- **`ownG` agrees with `own2b` at a node** where it picks `own2b` at the
state and past its cell. -/
theorem agree_node2b (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : Good2b L s) (hn : ∀ s', Keep s s' → Good2b L s') :
    ownG L a s = own2b L a (ph2b (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = own2b L a (ph2b (pcOf s')) :=
  ⟨ownG_2b hlab hs, fun s' h => ownG_2b hlab (hn s' (hk s' h))⟩

/-- **`ownG` agrees with `ownW` at a node** where it picks `ownW` at the
state and past its cell. -/
theorem agree_nodeW (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
    (hk : ∀ s', StSucc μ s s' → Keep s s') (hs : GoodW L s) (hn : ∀ s', Keep s s' → GoodW L s') :
    ownG L a s = ownW L a (phW (pcOf s)) ∧
      ∀ s', StSucc μ s s' → ownG L a s' = ownW L a (phW (pcOf s')) :=
  ⟨ownG_W hlab hs, fun s' h => ownG_W hlab (hn s' (hk s' h))⟩

/-- info: 'Spike.Lib.A64.WakePh.keep_svc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.keep_svc

/-- info: 'Spike.Lib.A64.WakePh.keep_nop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.keep_nop

/-- info: 'Spike.Lib.A64.WakePh.agree_node2a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.agree_node2a

end Spike.Lib.A64.WakePh

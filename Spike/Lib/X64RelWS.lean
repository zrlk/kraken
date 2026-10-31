/-
**A state's instruction runs and writes at most once, a release write**
(x86-64): `RelWS s`, `isa.exec s` gives a tree (the per-state form of
`hhalt0`) and every event tree it gives is `EvTree.RelW1 Arch.tso`
(`Spike/Lib/RelW1.lean`, the per-state form of `WCompat0.relW0`). It holds at
a covered block's internal states (they run to `.done`, `blk_exec_done`) and
at a system call (a fault, no write). The x86-64 twin of
`Spike/Lib/A64RelWS.lean`.

- `RelWS`; `relWS_of`, `relWS_done`, `relWS_syscall`: per instruction.
- `blkW_relW`, `nodeW_relW`: the `BlkW`/`NodeW` obligations of `RelWS` from
  the code.
- `BlkW.and`, `NodeW.and`: node obligations of two predicates combine.

**Deviations from the A64 file.** The namespace is `Spike.Lib.X64` (where
x86-64's `BlkW`/`NodeW` live, so `BlkW.and` resolves as A64's does in
`Spike.Lib.A64.Flow`). `blkW_relW` has no alignment premise (`hal`: x86-64's
`blk_exec_done` needs none) and `nodeW_relW`'s cell has its size `z`. The
A64 `relWS_ldr`, `relWS_ldar`, `relWS_swp` (and `access_noW`,
`access_relW1`) are not twinned: their only users are in `A64WakeMainR`; the
x86-64 analogs belong with that file's twin.
-/
import Spike.Lib.RelW1
import Spike.Lib.X64CfgLW

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64

/-- **The state's instruction runs and writes at most once, a release
write**: `exec` gives a tree (the state is not halted), and every tree it
gives is `RelW1 tso`. -/
def RelWS (s : State) : Prop :=
  (isa.exec s).isSome ∧ ∀ e, isa.exec s = some e → EvTree.RelW1 Arch.tso e

/-- **A state whose `exec` is one `RelW1` tree.** -/
theorem relWS_of {s : State} {t : EvTree State} (h : isa.exec s = some t) (ht : EvTree.RelW1 Arch.tso t) :
    RelWS s :=
  ⟨by rw [h]; rfl, fun e he => by rw [h] at he; cases he; exact ht⟩

/-- **An instruction that runs to `.done`.** -/
theorem relWS_done {s : State} (h : ∃ s', isa.exec s = some (.done s')) : RelWS s := by
  obtain ⟨s', h⟩ := h
  exact relWS_of h (.noW (.done _))

/-- **`syscall`**: a fault. -/
theorem relWS_syscall {s : State} {sz : Nat} (hc : CellAt s (op64 .syscall) sz) : RelWS s :=
  relWS_of (exec_syscall hc) (.noW (.fault _))

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A covered block's internal states are in `RelWS`** (`blk_exec_done`). -/
theorem blkW_relW {n : ND} {lo hi : Int} {blk : List (Directive × Nat)} (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA _
  subst he
  exact ⟨relWS_done (blk_exec_done hok hR hlo hhi (hcode s rfl hn) hk hA), fun _ h => h⟩

/-- **A one-instruction node is in `RelWS`** if its instruction is (`hd`). -/
theorem nodeW_relW {n : ND} {d : Directive} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(d, z)])
    (hd : ∀ s : State, CellAt s d z → RelWS s) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, hn, -, hpc, -⟩
  exact ⟨hd s ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp [cellOff])), fun _ h => h⟩

/-- **Two predicates' block obligations combine.** -/
theorem BlkW.and {W₁ W₂ : Frag isa} {K : State → State → Prop} {n : ND} {blk : List (Directive × Nat)}
    (h₁ : BlkW W₁ K exe endPc R F n blk) (h₂ : BlkW W₂ K exe endPc R F n blk) :
    BlkW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n blk :=
  fun s σ c a b d e f g hJ k hk m hA hD =>
    ⟨⟨(h₁ s σ c a b d e f g hJ k hk m hA hD).1, (h₂ s σ c a b d e f g hJ k hk m hA hD).1⟩,
      (h₁ s σ c a b d e f g hJ k hk m hA hD).2⟩

/-- **Two predicates' node obligations combine.** -/
theorem NodeW.and {W₁ W₂ : Frag isa} {K : State → State → Prop} {n : ND}
    (h₁ : NodeW W₁ K exe endPc R F n) (h₂ : NodeW W₂ K exe endPc R F n) :
    NodeW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n :=
  fun s c h => ⟨⟨(h₁ s c h).1, (h₂ s c h).1⟩, (h₁ s c h).2⟩

end W

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.relWS_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.relWS_of

/-- info: 'Spike.Lib.X64.relWS_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.relWS_done

/-- info: 'Spike.Lib.X64.relWS_syscall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.relWS_syscall

/-- info: 'Spike.Lib.X64.blkW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.blkW_relW

/-- info: 'Spike.Lib.X64.nodeW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.nodeW_relW

/-- info: 'Spike.Lib.X64.BlkW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.BlkW.and

/-- info: 'Spike.Lib.X64.NodeW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.NodeW.and

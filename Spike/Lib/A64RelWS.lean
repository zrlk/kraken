/-
**A state's instruction runs and writes at most once, a release write**
(AArch64): `RelWS s`, `isaLSE2.exec s` gives a tree (the
per-state form of `hhalt0`) and every event tree it gives is
`EvTree.RelW1 Arch.armv8` (`Spike/Lib/RelW1.lean`, the per-state form of
`WCompat0.relW0`). It holds at a covered block's internal states (they run
to `.done`, `blk_exec_done`), at a plain or acquire load and at a system
call (no write on any path), and at an `swp` whose write is a release
(`swpal`).

- `RelWS`; `relWS_of`, `relWS_done`, `relWS_ldr`, `relWS_ldar`, `relWS_swp`,
  `relWS_svc`: per instruction.
- `blkW_relW`, `nodeW_relW`: the `BlkW`/`NodeW` obligations of `RelWS` from
  the code.
- `BlkW.and`, `NodeW.and`: node obligations of two predicates combine.
-/
import Spike.Lib.RelW1
import Spike.Lib.A64CfgLW

namespace Spike.Lib.A64.Flow

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

/-- **The state's instruction runs and writes at most once, a release
write**: `exec` gives a tree (the state is not halted), and every tree it
gives is `RelW1 armv8`. -/
def RelWS (s : State) : Prop :=
  (isaLSE2.exec s).isSome ∧ ∀ e, isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e

/-- An access whose every event writes nothing writes nothing. -/
theorem access_noW {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, EvTree.NoW (k l)) : EvTree.NoW (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · exact .fault _

/-- An access whose every event writes once, a release write, does so. -/
theorem access_relW1 {σ : Type} {A : Arch} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, EvTree.RelW1 A (k l)) : EvTree.RelW1 A (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · exact .noW (.fault _)

/-- **A state whose `exec` is one `RelW1` tree.** -/
theorem relWS_of {s : State} {t : EvTree State} (h : isaLSE2.exec s = some t) (ht : EvTree.RelW1 Arch.armv8 t) :
    RelWS s :=
  ⟨by rw [h]; rfl, fun e he => by rw [h] at he; cases he; exact ht⟩

/-- **An instruction that runs to `.done`.** -/
theorem relWS_done {s : State} (h : ∃ s', isaLSE2.exec s = some (.done s')) : RelWS s := by
  obtain ⟨s', h⟩ := h
  exact relWS_of h (.noW (.done _))

/-- **`ldr Xt, [Xn, #i]`**: a plain load, or no event. -/
theorem relWS_ldr {s : State} {sz : Nat} {dst : RegOrZr .W64} {n : XReg} {i : Int64}
    (hc : CellAt s (.instr ⟨.W64, .LDR dst (.addr ⟨.low (.reg n) .W64, .imm ⟨.int64 i, none⟩⟩)⟩) sz) :
    RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (BitVec.ofInt 64 ((s.st.1.regs.getXReg n).toBitVec.toInt + i.toInt)) 8 with
  | none => exact relWS_of (exec_ldr hc rfl hm) (.noW (access_noW fun _ => .load fun _ => .done _))
  | some j => exact relWS_of (exec_ldr_mapped hc rfl hm) (.noW (.done _))

/-- **`ldar Xt, [Xn]`**: a load, or no event. -/
theorem relWS_ldar {s : State} {sz : Nat} {dst : RegOrZr .W64} {n : XReg} {k : LoadKind} {xcl : Bool}
    (hc : CellAt s (.instr ⟨.W64, .LDAR k xcl .W64 dst (.low (.reg n) .W64)⟩) sz) : RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg n).toBitVec 8 with
  | none => exact relWS_of (exec_ldar hc hm) (.noW (access_noW fun _ => .load fun _ => .done _))
  | some j => exact relWS_of (exec_ldar_mapped hc hm) (.noW (.done _))

/-- **`swp Xs, Xt, [Xn]` with a release write** (`swpal`): one release RMW,
or no event. -/
theorem relWS_swp {s : State} {sz : Nat} {rs rt : RegOrZr .W64} {n : XReg} {k : RmwKind}
    (hk : Arch.armv8.storeKind (Arch.armv8.rmwKind k).storeKind = .rel)
    (hc : CellAt s (.instr ⟨.W64, .SWP k .W64 rs rt (.low (.reg n) .W64)⟩) sz) : RelWS s := by
  cases hm : Mem.loadInt s.st.1.dmem (s.st.1.regs.getXReg n).toBitVec 8 with
  | none => exact relWS_of (exec_swp hc hm) (access_relW1 fun _ => .rmw hk fun _ => .done _)
  | some j =>
    obtain ⟨s', h'⟩ := exec_swp_mapped hc hm
    exact relWS_done ⟨_, h'⟩

/-- **`svc #imm`**: a fault. -/
theorem relWS_svc {s : State} {sz imm : Nat} (hc : CellAt s (.instr ⟨.W64, .SVC imm⟩) sz) : RelWS s :=
  relWS_of (exec_svc hc) (.noW (.fault _))

section W

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A covered block's internal states are in `RelWS`** (`blk_exec_done`). -/
theorem blkW_relW {n : ND} {lo hi : Int} {blk : List Directive} (hok : okBlk lo hi n.o blk = true) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ _ k hk m hA _
  subst he
  exact ⟨relWS_done (blk_exec_done hok hR hal hlo hhi (hcode s rfl hn) hk hA), fun _ h => h⟩

/-- **A one-instruction node is in `RelWS`** if its instruction is (`hd`). -/
theorem nodeW_relW {n : ND} {d : Directive} (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [d])
    (hd : ∀ s : State, CellAt s d 4 → RelWS s) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨he, hn, -, hpc, -⟩
  exact ⟨hd s ((hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)), fun _ h => h⟩

/-- **Two predicates' block obligations combine.** -/
theorem BlkW.and {W₁ W₂ : Frag isaLSE2} {K : State → State → Prop} {n : ND} {blk : List Directive}
    (h₁ : BlkW W₁ K exe endPc R F n blk) (h₂ : BlkW W₂ K exe endPc R F n blk) :
    BlkW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n blk :=
  fun s σ c a b d e f g hJ k hk m hA hD =>
    ⟨⟨(h₁ s σ c a b d e f g hJ k hk m hA hD).1, (h₂ s σ c a b d e f g hJ k hk m hA hD).1⟩,
      (h₁ s σ c a b d e f g hJ k hk m hA hD).2⟩

/-- **Two predicates' node obligations combine.** -/
theorem NodeW.and {W₁ W₂ : Frag isaLSE2} {K : State → State → Prop} {n : ND}
    (h₁ : NodeW W₁ K exe endPc R F n) (h₂ : NodeW W₂ K exe endPc R F n) :
    NodeW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n :=
  fun s c h => ⟨⟨(h₁ s c h).1, (h₂ s c h).1⟩, (h₁ s c h).2⟩

end W

/-- info: 'Spike.Lib.A64.Flow.relWS_swp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms relWS_swp

end Spike.Lib.A64.Flow

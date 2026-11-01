/-
**`wc_rodata`'s buffer words at `.sp0`** (AArch64; `RdWfS.rdPostW_WSH`'s `hbuf`; NOT
row 4c's `BufAtSpawn` hbuf): at every `.sp0` state whose `x0` is an allocation's base (`CellX0`: some
allocator's call `q`, some counter value `old` its block fits at), the buffer's two words `x0 + 0`, `x0 + 8` are
box cells (`BoxOkH`): heap words, so mapped for writing (`mapped_K0_of_heap`); unmapped in private memory under
`WordsNone` (`Alloc.hbuf_of_wordsNone`); off the owned words when the five owned words are off the arena's heap and
counter (`WcWfR.not_ownW`, its `hoff` the root's, as wake's `offW_own`).

Both kinds of `.sp0` states `hello_start_wc_segW` hands `Jp` have `CellX0`: the allocator's return exit
(`rX .sp0`, `cellX0_ret`) and the fresh-label landing left to `wc_rodata`'s region (`cellX0_land`).

- `CellX0`, `cellX0_ret`, `cellX0_land`;
- `boxOkH_cellX0`: the two words' `BoxOkH` at a `CellX0` state.
-/
import Spike.Lib.A64HelloRdPostWfS
import Spike.Lib.A64HelloMain
import Spike.Lib.A64WakeWcWfR
import Spike.Lib.A64Hello1RodataSetup

namespace Spike.Lib.A64.HelloPh.RdBuf

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib (MemSide Region)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (leave)
open Spike.Lib.A64.Flow.Hello1 (AG aR mR)
open Spike.Lib.A64.Flow.HelloRd (rX)
open Spike.Lib.A64.Alloc (Ea)
open Spike.Lib.DmemPriv (WordsNone)
open Spike.Lib.A64.HelloPh.WcW (BoxOkH)

/-- `Flow`'s abstract state (`AS` alone is ambiguous here). -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **`x0` is an allocation's base**: some allocator's call `q` and counter value `old` its block fits at. -/
def CellX0 (ms : MemSide isaLSE2) (lab : Label → Int64) (σ : FAS) : Prop :=
  ∃ q : AG ms lab, ∃ old : Nat, σ.regs.X0.toNat = ms.heap + 16 * old + ms.off q.1.n q.1.τ ∧
    old + ms.units q.1.n q.1.τ ≤ ms.cells ∧ ms.lo old

/-- **At the allocator's return exit** `x0` is the allocation's base. -/
theorem cellX0_ret {ms : MemSide isaLSE2} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J1 : FAS → Spike.Lib.Ctl → Prop} {σ : FAS} {c : Spike.Lib.Ctl} (h : (rX ms lab lbl J1 .sp0).J σ c) :
    CellX0 ms lab σ := by
  obtain ⟨q, -, _, _, _, -, -, hx, hle, hlo, -⟩ := h
  exact ⟨q, _, hx, hle, hlo⟩

/-- **At the fresh-label landing** left to `wc_rodata`'s region (`leave` keeps the callee's registers) `x0` is the
allocation's base. -/
theorem cellX0_land {ms : MemSide isaLSE2} {lab : Label → Int64} {R : Region} {q : AG ms lab}
    {l : WeakMem.AllocLabel} {b w : Nat} {σ σx : FAS} {c : Spike.Lib.Ctl} (h : (Ea ms q.1 l b w).J σx c) :
    CellX0 ms lab (leave (aR (mR R)) (-48) σ σx) := by
  obtain ⟨_, old, -, hx, hb, hle, hlo, -⟩ := h
  exact ⟨q, old, hx.trans hb, hle, hlo⟩

/-- **The buffer's two words are box cells** at a `CellX0` state: in the heap (the arena inside it, `hH`, `hHi`,
`hroom`; the block's words past its header inside its cells, `ho`), unmapped in private memory under `WordsNone`
(`hwn`), off the owned words (the five owned words off the arena's heap and counter, `hoffO`). -/
theorem boxOkH_cellX0 {L : RuntimeLayout} {a : BitVec 64} {F : MachineData → Prop} {ms : MemSide isaLSE2}
    {lab : Label → Int64}
    (hwn : ∀ m, F m → WordsNone L.Λ m.dmem) (hH : L.Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size) (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64)
    (ho : ∀ q : AG ms lab, ms.off q.1.n q.1.τ + 16 ≤ 16 * ms.units q.1.n q.1.τ)
    (hoffO : ∀ w', (w' = L.pnA ∨ w' = L.lockA ∨ w' = L.freeNA ∨ w' = L.nextA ∨ w' = a) →
      ¬ (ms.heap ≤ w'.toNat ∧ w'.toNat < ms.heap + 16 * ms.cells) ∧ w' ≠ BitVec.ofNat 64 ms.ctr)
    {σ : FAS} (h : CellX0 ms lab σ) :
    ∀ i : Int64, (i = 0 ∨ i = 8) → BoxOkH L.Λ L a F (Spike.Lib.A64.Flow.rAddr σ.regs .X0 i) := by
  obtain ⟨q, old, hx, hle, -⟩ := h
  have ho' := ho q
  have hX : σ.regs.X0.toBitVec = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hx
  have key : ∀ j : Nat, (j = 0 ∨ j = 8) →
      BoxOkH L.Λ L a F (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j)) := by
    intro j hj
    have e : (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + j)).toNat =
        ms.heap + 16 * old + ms.off q.1.n q.1.τ + j := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨Spike.Lib.LowerA64.mapped_K0_of_heap fun k hk => ?_,
      Spike.Lib.A64.Alloc.hbuf_of_wordsNone hwn hH hHi hroom ho' old hle j hj,
      Spike.Lib.A64.WakePh.WcWfR.not_ownW hoffO (.inr ?_)⟩
    · rw [e]; unfold Scc.Sem.Range.contains; omega
    · rw [e]; omega
  rintro i (rfl | rfl)
  · rw [Spike.Lib.A64.Flow.Hello1.rAddr_x0_0, hX]
    exact key 0 (.inl rfl)
  · rw [Spike.Lib.A64.Flow.Hello1.rAddr_x0_8, hX]
    have : BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + 0) + 8#64 =
        BitVec.ofNat 64 (ms.heap + 16 * old + ms.off q.1.n q.1.τ + 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    rw [this]
    exact key 8 (.inr rfl)

end Spike.Lib.A64.HelloPh.RdBuf

/-- info: 'Spike.Lib.A64.HelloPh.RdBuf.cellX0_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdBuf.cellX0_ret

/-- info: 'Spike.Lib.A64.HelloPh.RdBuf.cellX0_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdBuf.cellX0_land

/-- info: 'Spike.Lib.A64.HelloPh.RdBuf.boxOkH_cellX0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RdBuf.boxOkH_cellX0

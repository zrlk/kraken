/-
**wake.w's `scc_rt_thread_init` call: no outside moves, and its memory
instructions keep `%rsp` and `%rbp`** (x86-64; twin of
`Spike/Lib/A64WakeStartTiK0.lean` and `Spike/Lib/A64WakeStartTiK.lean`).

The node obligations of `TiW` / `TakeW` weaken in the outside move `K`
(each node only asks no state of it moved by `K`), so `startTi_WS` /
`takeW_WS` hold at `K = False`; and the successors of the take's lock
`xchgq`, its loads and the TCB fields' stores step to the next pc writing
neither `%rsp` nor `%rbp` (as `Tcb2W.keep_rmw` / `keep_hdr`); at the take
site the take writes only memory (`keep_take`).

- `nodeW_kMono`, `blkW_kMono`, `TakeW.kMono`, `TiW.kMono`: the obligations
  at a smaller outside move.
- `keep_xchg`, `keep_ld`, `keep_st`: an `xchgq %rax, (%rcx)`, a load
  `movq i(%b), %r` and a store `movq %r, i(%b)` of an unmapped word keep
  `%rsp` and `%rbp`.

**Unlike AArch64**: `TakeW` / `TiW` have no `P` argument; AArch64's swap
(`keep_swp`) is `keep_xchg`, its release store `keep_stlr` a plain store
(`keep_st`, A64's `keep_str`), its `keep_ldr` is `keep_ld` (any destination
register, A64's `x9`); every cell has size `z` (A64's `4`) and the address
is the effective address `eaddr s z (mB b i)` (A64's `rAddr`); `Keep` is
`%rsp`/`%rbp` (A64's `sp`/`x30`). The two A64 files are merged (both
short).
-/
import Spike.Lib.X64WakeStartTiL2

namespace Spike.Lib.X64.Flow.Ret0

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 (BlkW NodeW ND)

variable {W : Frag isa} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F M : MachineData → Prop}

/-- A node obligation at a smaller outside move. -/
theorem nodeW_kMono {n : ND} (h : NodeW W K exe endPc R F n) (hK : ∀ s s', K' s s' → K s s') :
    NodeW W K' exe endPc R F n :=
  fun s c hA => ⟨(h s c hA).1, fun s' hk => (h s c hA).2 s' (hK _ _ hk)⟩

/-- A block obligation at a smaller outside move. -/
theorem blkW_kMono {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk)
    (hK : ∀ s s', K' s s' → K s s') : BlkW W K' exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hF hJ k hk m hA' hD =>
    ⟨(h s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).1,
      fun s' hk' => (h s σ c he hn hdc hpc hA hF hJ k hk m hA' hD).2 s' (hK _ _ hk')⟩

/-- **`TakeW` at a smaller outside move.** -/
theorem TakeW.kMono {q : TakeG} {i : TK} (h : TakeW W K exe endPc R F M q i) (hK : ∀ s s', K' s s' → K s s') :
    TakeW W K' exe endPc R F M q i := by
  cases i <;> dsimp only [TakeW] at h ⊢
  all_goals first
    | exact blkW_kMono h hK
    | exact nodeW_kMono h hK
    | exact ⟨nodeW_kMono h.1 hK, nodeW_kMono h.2 hK⟩
    | exact h

/-- **`TiW` at a smaller outside move.** -/
theorem TiW.kMono {q : TiG} {i : TI} (h : TiW W K exe endPc R F M q i) (hK : ∀ s s', K' s s' → K s s') :
    TiW W K' exe endPc R F M q i := by
  cases i <;> dsimp only [TiW] at h ⊢
  all_goals first
    | exact blkW_kMono h hK
    | exact nodeW_kMono h hK
    | exact fun g hg i => (h g hg i).kMono hK

end Spike.Lib.X64.Flow.Ret0

namespace Spike.Lib.X64.WakePh.StartTi

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (abi)
open Spike.Lib.X64ConsumerA (StSucc)
open Spike.Lib.X64 (xchgDir ldDir stDir mB)
open Kraken.Promising.Lower.X64 (CellAt eaddr)

variable {μ : Scc.Sem.Marks} {s s' : State} {z : Nat}

/-- **The lock's swap `xchgq %rax, i(%b)`** of an unmapped word keeps
`%rsp` and `%rbp`. -/
theorem keep_xchg {b : Reg64} {i : Int64} (hc : CellAt s (xchgDir b i .rax) z) (hdc : s.decls = {})
    {a : BitVec 64} (ha : eaddr s z (mB b i) = a) (hdm : Mem.loadInt s.st.1.dmem a 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_xchg hc ha hdm] at htr
    cases htr
    rw [hdc, EvTree.access_empty] at hl
    obtain ⟨v, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **A load `movq i(%b), %r`** of an unmapped word keeps `%rsp` and `%rbp`
(`%r` neither). -/
theorem keep_ld {b r : Reg64} {i : Int64} (hr : r ≠ .rsp ∧ r ≠ .rbp) (hc : CellAt s (ldDir b i r) z)
    (hdc : s.decls = {}) {a : BitVec 64} (ha : eaddr s z (mB b i) = a) (hdm : Mem.loadInt s.st.1.dmem a 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_load_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls hdc _ _)] at htr
    cases htr
    obtain ⟨v, rfl⟩ := hl
    obtain ⟨h1, h2⟩ := hr
    refine ⟨?_, ?_, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩ <;> cases r <;>
      first | rfl | exact (h1 rfl).elim | exact (h2 rfl).elim
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

/-- **A store `movq %r, i(%b)`** of an unmapped word keeps `%rsp` and
`%rbp`. -/
theorem keep_st {b r : Reg64} {i : Int64} (hc : CellAt s (stDir b i r) z) (hdc : s.decls = {})
    {a : BitVec 64} (ha : eaddr s z (mB b i) = a) (hdm : Mem.loadInt s.st.1.dmem a 8 = none)
    (h : StSucc μ s s') : Keep s s' := by
  have hs : abi.atSys s = false :=
    Scc.Sem.X64.atSyscall_false_of_cellAt hc (by intro w w' h; cases h)
  rcases h with ⟨-, tree, htr, hl⟩ | ⟨hs', -⟩ | ⟨-, -, -, m, rfl⟩
  · rw [Kraken.Promising.Lower.X64.exec_store_agrees hc ha hdm (Spike.Lib.X64.agrees_of_decls hdc _ _)] at htr
    cases htr
    obtain ⟨b, rfl⟩ := hl
    exact ⟨rfl, rfl, (Scc.Sem.X64.nextPc_of_cellAt hc).symm⟩
  · rw [hs] at hs'; cases hs'
  · exact keep_take m

end Spike.Lib.X64.WakePh.StartTi

/-- info: 'Spike.Lib.X64.Flow.Ret0.nodeW_kMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.nodeW_kMono

/-- info: 'Spike.Lib.X64.Flow.Ret0.blkW_kMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.blkW_kMono

/-- info: 'Spike.Lib.X64.Flow.Ret0.TakeW.kMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.TakeW.kMono

/-- info: 'Spike.Lib.X64.Flow.Ret0.TiW.kMono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Ret0.TiW.kMono

/-- info: 'Spike.Lib.X64.WakePh.StartTi.keep_xchg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.keep_xchg

/-- info: 'Spike.Lib.X64.WakePh.StartTi.keep_ld' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.keep_ld

/-- info: 'Spike.Lib.X64.WakePh.StartTi.keep_st' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.StartTi.keep_st

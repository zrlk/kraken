/-
**The thread pointer's alignment** (AArch64, wake): main's `TPIDR_EL0` is its
TCB (`scc_rt_start`'s `msr tpidr_el0, x10`), 8-aligned, and kept to the
clone; the park/unpark futex word `tp + 16` is then 4-aligned (`htp4`).

- `TpAl`: `TPIDR_EL0` 8-aligned at a state.
- `htp4_of`: the futex word's alignment from `TpAl`.
- `htp4_pin`: the same for main's `tp = scc_rt_pinned + 0 + 8`.
- `clonePre_tpAl`: `TpAl` of `ClonePre`'s thread when `X` carries it.
-/
import Spike.Lib.WakePreA

namespace Spike.Lib.WakeTpAl

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel

/-- **`TPIDR_EL0` 8-aligned** at `s`. -/
def TpAl (s : State) : Prop := s.st.1.regs.TPIDR_EL0.toBitVec.toNat % 8 = 0

/-- **The futex word is 4-aligned**: `tp + 16` for an 8-aligned `tp`. -/
theorem htp4_of {s : State} (h : TpAl s) :
    (s.st.1.regs.TPIDR_EL0.toBitVec + 16#64).toNat % 4 = 0 := by
  unfold TpAl at h
  rw [BitVec.toNat_add]
  have : (16#64 : BitVec 64).toNat = 16 := rfl
  rw [this]
  have h64 : (2 : Nat) ^ 64 % 4 = 0 := by decide
  omega

/-- **The futex word of main's TCB is 4-aligned**: main's `tp` is the first
TCB, `scc_rt_pinned + 0 + 8`, for an 8-aligned `scc_rt_pinned`. -/
theorem htp4_pin {p : BitVec 64} (hp : p.toNat % 8 = 0) : (p + 0#64 + 8#64 + 16#64).toNat % 4 = 0 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h64 : (2 : Nat) ^ 64 % 4 = 0 := by decide
  omega

/-- **`ClonePre`'s thread has `TpAl`** when its runtime facts `X` imply it. -/
theorem clonePre_tpAl {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfx Λ r0 r1 X lbl t s) (hX : ∀ st, X st → TpAl st) :
    ∀ th, t.1.threads = #[th] → TpAl th.st := by
  obtain ⟨th, -, -, -, -, -, ht, -, -, -, -, -, -, -, -, -, -, -, -, -, hx, -⟩ := h
  intro th' ht'
  rw [ht] at ht'
  cases Array.mk.inj ht' |> List.cons.inj |>.1
  exact hX _ hx

/-- info: 'Spike.Lib.WakeTpAl.htp4_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeTpAl.htp4_of

/-- info: 'Spike.Lib.WakeTpAl.htp4_pin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeTpAl.htp4_pin

/-- info: 'Spike.Lib.WakeTpAl.clonePre_tpAl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.WakeTpAl.clonePre_tpAl

end Spike.Lib.WakeTpAl

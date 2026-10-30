/-
**The second take's caller-side pre-take fact** (wake.w, AArch64): `Pz r`, no word loads at the child's stack's first address. It cannot
be a consequence of `Box`'s frame condition `F`: `Box`'s `hFt` keeps `F`
across `takeMem r1`, after which `r1` is in private memory
(`Ret0.stackM_takeMem`), so `F → ¬ StackM r1` would make `F` empty. It comes
instead from `Box`'s `Pz r1` conjunct, outside `F`, and is threaded
through the segments after the box (no take there) beside `F`.

- `Pz` is `A64Consumer.Pz` (`A64OwnedPz`, with `pz_of_unowned`): word-level,
  so kept by `DFrame`, unlike `Unowned`.
- `pz_not_stackM`: `Pz r` refutes `StackM r` (`r.lo` word-aligned).
- `pz_fstable`: `FStable R (Pz r)` for a region whose top is at most `r.lo`;
  `pz_fstable_box` at `Box`'s geometry (`R.base + 48 = r.lo`, `R.hi ≤ 48`);
  `pz_fstable_callee` at any callee region below such an `R`.
- `r1Of_lo_al`, `r1Of_fit`: the child's stack's first address is
  word-aligned and its word fits the address space.
- `un_box`, `pz_box`: `U r1` and `Pz r1` at a `Box` state.
-/
import Spike.Lib.A64WakeBox
import Spike.Lib.A64OwnedPz

namespace Spike.Lib.A64.WakePh.Pz

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64.Flow (FStable DFrame)

open Spike.Lib.A64Consumer (Pz)

/-- **`Pz r` refutes `StackM r`** at a word-aligned range of a word or more. -/
theorem pz_not_stackM {r : Range} {m : MachineData} (hal : r.lo % 8 = 0) (h8 : 8 ≤ r.size) (h : Pz r m) :
    ¬ Spike.Lib.A64.Flow.Ret0.StackM r m := fun hs => by
  have := hs r.lo hal ⟨Nat.le_refl _, by omega⟩ ⟨by omega, by omega⟩
  rw [show Mem.loadInt m.dmem (BitVec.ofNat 64 r.lo) 8 = none from h] at this
  cases this

/-- **`Pz r` is kept by the frames of a region whose top is at most `r.lo`.** -/
theorem pz_fstable {r : Range} {R : Region} (hfit : r.lo + 8 ≤ 2 ^ 64)
    (htop : (R.base.toNat : Int) + R.hi ≤ r.lo) : FStable R (Pz r) := by
  intro m m' h hd
  have hn : (BitVec.ofNat 64 r.lo).toNat = r.lo := by rw [BitVec.toNat_ofNat]; omega
  unfold Pz
  rw [hd _ (by rw [hn]; exact hfit) (.inr (by rw [hn]; exact htop))]
  exact h

/-- **`Pz r` at `Box`'s geometry**: the region's base `48` below `r.lo`,
its top at most `48`. -/
theorem pz_fstable_box {r : Range} {R : Region} (hfit : r.lo + 8 ≤ 2 ^ 64) (hb : R.base.toNat + 48 = r.lo)
    (hhi : R.hi ≤ 48) : FStable R (Pz r) :=
  pz_fstable hfit (by omega)

/-- **`Pz r` at a callee region below `R`** (`R.callee kc lo' hi'`, its top
`kc + hi'` inside `R`'s): its top is at most `R`'s. -/
theorem pz_fstable_callee {r : Range} {R : Region} (hR : R.OK) (hfit : r.lo + 8 ≤ 2 ^ 64)
    (htop : (R.base.toNat : Int) + R.hi ≤ r.lo) {kc lo' hi' : Int} (hlo : R.lo ≤ kc) (hkc : kc < R.hi)
    (hh : kc + hi' ≤ R.hi) : FStable (R.callee kc lo' hi') (Pz r) := by
  have ha := Spike.Lib.Region.addr_toNat_of hR hlo hkc
  exact pz_fstable hfit (by simp only [Spike.Lib.Region.callee]; omega)

/-- **The child's stack's first address is word-aligned** (`stacksA`
16-aligned). -/
theorem r1Of_lo_al (L : Spike.Lib.A64.Rt.RuntimeLayout) :
    (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label).lo % 8 = 0 := by
  have h := L.stacks_al
  unfold Spike.Lib.A64.Rt.PreChild.r1Of
  rw [L.lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  show (L.stacksA.toNat + 16384 % 2 ^ 64) % 2 ^ 64 % 8 = 0
  omega

/-- **The child's stack's first word fits the address space.** -/
theorem r1Of_fit (L : Spike.Lib.A64.Rt.RuntimeLayout) :
    (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label).lo + 8 ≤ 2 ^ 64 := by
  have h := r1Of_lo_al L
  have hl : (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label).lo < 2 ^ 64 :=
    BitVec.isLt _
  omega

/-- **`U r1` at a `Box` state** (its conjunct). -/
theorem un_box {L : Spike.Lib.A64.Rt.RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.A64.Flow.WakeWc.Box L ms0 F0 l b n s c) :
    Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) s := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨-, hU⟩, -⟩ := h
  exact hU

/-- **`Pz r1` at a `Box` state** (`pz_of_unowned` at `un_box`). -/
theorem pz_box {L : Spike.Lib.A64.Rt.RuntimeLayout} {ms0 : MemSide isaLSE2} {F0 : MachineData → Prop}
    {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Spike.Lib.Ctl}
    (h : Spike.Lib.A64.Flow.WakeWc.Box L ms0 F0 l b n s c) :
    Pz (Spike.Lib.A64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) s.st.1 := by
  exact Spike.Lib.A64Consumer.pz_of_unowned (by exact (by decide : (0 : Nat) < 16384)) (un_box h).2

end Spike.Lib.A64.WakePh.Pz

/-- info: 'Spike.Lib.A64.WakePh.Pz.pz_not_stackM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Pz.pz_not_stackM

/-- info: 'Spike.Lib.A64.WakePh.Pz.pz_fstable_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Pz.pz_fstable_callee

/-- info: 'Spike.Lib.A64.WakePh.Pz.r1Of_lo_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Pz.r1Of_lo_al

/-- info: 'Spike.Lib.A64.WakePh.Pz.pz_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Pz.pz_box

/-- info: 'Spike.Lib.A64.WakePh.Pz.un_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Pz.un_box

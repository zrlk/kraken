/-
**The second take's caller-side pre-take fact** (wake.w, x86-64; twin of
`Spike/Lib/A64WakePz.lean`): `Pz r`, no word loads at the child's stack's
first address. It cannot be a consequence of `Box`'s frame condition `F`:
`Box`'s `hFt` keeps `F` across `takeMem r1`, after which `r1` is in private
memory (`Ret0.stackM_takeMem`), so `F → ¬ StackM r1` would make `F` empty.
It comes instead from `Box`'s `Pz r1` conjunct (from `KeepUn.U r1`),
outside `F`, and is threaded through the segments after the box (no take
there) beside `F`.

- `Pz` is `X64Consumer.Pz` (`X64OwnedPz`, with `pz_of_unowned`):
  word-level, so kept by `DFrame`, unlike `Unowned`.
- `pz_not_stackM`: `Pz r` refutes `StackM r` (`r.lo` word-aligned).
- `pz_fstable`: `FStable R (Pz r)` for a region whose top is at most `r.lo`;
  `pz_fstable_box` at the box's geometry (`R.base + 56 = r.lo`,
  `R.hi ≤ 56`); `pz_fstable_callee` at any callee region below such an `R`.
- `r1Of_lo_al`, `r1Of_fit`: the child's stack's first address is
  word-aligned and its word fits the address space.
- `pz_of_U`: `Pz r1` from `KeepUn.U r1` (A64's `pz_box` without the `Box`
  projection).

**Unlike AArch64**: the box's geometry is `R.base + 56 = r.lo`,
`R.hi ≤ 56` (`wc_main` entered at `v - 56`, `X64WakeTi2Box.hb`; A64's
`48`); A64's `un_box` / `pz_box` project `WakeWc.Box`, whose x86-64 twin
(`A64WakeBox`) does not exist yet: `pz_of_U` is `pz_box` on the
`KeepUn.U r1` conjunct, and `un_box` is the projection to add with that
twin.
-/
import Spike.Lib.X64OwnedPz
import Spike.Lib.X64KeepUn
import Spike.Lib.Rt.X64RtPreChild

namespace Spike.Lib.X64.WakePh.Pz

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64 (FStable DFrame)

open Spike.Lib.X64Consumer (Pz)

/-- **`Pz r` refutes `StackM r`** at a word-aligned range of a word or more. -/
theorem pz_not_stackM {r : Range} {m : MachineData} (hal : r.lo % 8 = 0) (h8 : 8 ≤ r.size) (h : Pz r m) :
    ¬ Spike.Lib.X64.Flow.Ret0.StackM r m := fun hs => by
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

/-- **`Pz r` at the box's geometry**: the region's base `56` below `r.lo`,
its top at most `56`. -/
theorem pz_fstable_box {r : Range} {R : Region} (hfit : r.lo + 8 ≤ 2 ^ 64) (hb : R.base.toNat + 56 = r.lo)
    (hhi : R.hi ≤ 56) : FStable R (Pz r) :=
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
theorem r1Of_lo_al (L : Spike.Lib.X64.Rt.RuntimeLayout) :
    (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label).lo % 8 = 0 := by
  have h := L.stacks_al
  unfold Spike.Lib.X64.Rt.PreChild.r1Of
  rw [L.lab_stacks, BitVec.toNat_add, BitVec.toNat_ofNat]
  show (L.stacksA.toNat + 16384 % 2 ^ 64) % 2 ^ 64 % 8 = 0
  omega

/-- **The child's stack's first word fits the address space.** -/
theorem r1Of_fit (L : Spike.Lib.X64.Rt.RuntimeLayout) :
    (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label).lo + 8 ≤ 2 ^ 64 := by
  have h := r1Of_lo_al L
  have hl : (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label).lo < 2 ^ 64 :=
    BitVec.isLt _
  omega

/-- **`Pz r1` from `KeepUn.U r1`** (`pz_of_unowned`; A64's `pz_box` at the
box's `U r1` conjunct). -/
theorem pz_of_U {L : Spike.Lib.X64.Rt.RuntimeLayout} {s : State}
    (h : Spike.Lib.X64.KeepUn.U (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) s) :
    Pz (Spike.Lib.X64.Rt.PreChild.r1Of (_root_.Executable.labels L.exe).label) s.st.1 :=
  Spike.Lib.X64Consumer.pz_of_unowned (by exact (by decide : (0 : Nat) < 16384)) h.2

end Spike.Lib.X64.WakePh.Pz

/-- info: 'Spike.Lib.X64.WakePh.Pz.pz_not_stackM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.pz_not_stackM

/-- info: 'Spike.Lib.X64.WakePh.Pz.pz_fstable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.pz_fstable

/-- info: 'Spike.Lib.X64.WakePh.Pz.pz_fstable_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.pz_fstable_box

/-- info: 'Spike.Lib.X64.WakePh.Pz.pz_fstable_callee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.pz_fstable_callee

/-- info: 'Spike.Lib.X64.WakePh.Pz.r1Of_lo_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.r1Of_lo_al

/-- info: 'Spike.Lib.X64.WakePh.Pz.r1Of_fit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.r1Of_fit

/-- info: 'Spike.Lib.X64.WakePh.Pz.pz_of_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Pz.pz_of_U

/-
**Main's slots at the second `scc_rt_thread_init` call's nodes** (AArch64;
`hti_W`'s placement): `wc_main`'s frame slots `-72` (the box's cell) and
`-80` (main's `ThreadId`) lie above the callee's region `R.callee (-80)
(-256) 0`, so every state of the callee's nodes (and of the take's, inside
it) reads them as at the call, where they hold `cA` and `m` (`FrW`). With
`cA` the box's address `b` and `m` main's id, they are the places
`PlacedSE` at `SpawnSrc l` needs (`PlacedCal.hti_placed`).

- `SlotP`: the two slots read `b` and `t0`.
- `slotP_place`: `SlotP` as the two `placeVal`s.
- `slotP_keep`: `SlotP` at every state the callee's frame keeps, from the
  call's abstract state (`hFm`, `hti_W`'s frame premise) and the box's base.

No absolute address appears in this file.
-/
import Spike.Lib.A64WakeTi2Box
import Spike.Lib.A64WakeSrcCtl
import Spike.Lib.A64WakeTcb2Call

namespace Spike.Lib.A64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh.Tcb2Call (oW)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **Main's slots read `b` and `t0`** at the machine data `m`: slot `-72`
the box's cell, slot `-80` main's id. -/
def SlotP (R : Spike.Lib.Region) (b t0 : Nat) (m : MachineData) : Prop :=
  ∃ j72 j80, Mem.loadInt m.dmem (R.addr (-72)) 8 = some j72 ∧ (BitVec.ofInt 64 j72).toNat = b ∧
    Mem.loadInt m.dmem (R.addr (-80)) 8 = some j80 ∧ (BitVec.ofInt 64 j80).toNat = t0

/-- **`SlotP` as places**: the slots' `placeVal`s. -/
theorem slotP_place {b t0 : Nat} {s : State} (h : SlotP R b t0 s.st.1) :
    placeVal (machine (kernel 1)) s (.slot (R.addr (-72)).toNat) = some b ∧
      placeVal (machine (kernel 1)) s (.slot (R.addr (-80)).toNat) = some t0 := by
  obtain ⟨j72, j80, e72, v72, e80, v80⟩ := h
  constructor
  · show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr (-72)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.A64.privLoad, e72, v72]
  · show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr (-80)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.A64.privLoad, e80, v80]

/-- **`SlotP` at every state the callee's frame keeps**: at the call the
slots hold `cA` and `mw` (`hFm`: an abstract state of `R` at `oW` whose
cells off the callee's region the frame keeps), `cA` the box's `b` and `mw`
main's `t0`; the slots off the callee's region by the box's base (`hb`),
inside `R` (`hRs`). -/
theorem slotP_keep (hb : R.base.toNat + 48 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -80 ∧ 0 ≤ R.hi)
    {b t0 : Nat} {cA mw : BitVec 64} (hcA : cA.toNat = b) (hm : mw.toNat = t0) {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.A64.Flow.Abs R oW mC σC ∧ σC.slot (-72) = cA ∧
      σC.slot (-80) = mw ∧ ∀ k, R.Off k → ¬ (R.callee (-80) (-256) 0).Off (k - -80) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.A64.Flow.DFrame (R.callee (-80) (-256) 0) m m' → SlotP R b t0 m' := by
  intro m m' hm0 hd
  obtain ⟨mC, σC, hA, h72, h80, hk⟩ := hFm m hm0
  have hB := R.base.isLt
  have o72 : R.Off (-72) := ⟨by decide, by omega, by omega⟩
  have o80 : R.Off (-80) := ⟨by decide, by omega, by omega⟩
  have n72 : ¬ (R.callee (-80) (-256) 0).Off (-72 - -80) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have n80 : ¬ (R.callee (-80) (-256) 0).Off (-80 - -80) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have a72 := addr_box (L := L) hb (k := -72) (by omega) (by omega)
  have a80 := addr_box (L := L) hb (k := -80) (by omega) (by omega)
  have d72 : Mem.loadInt m'.dmem (R.addr (-72)) 8 = Mem.loadInt m.dmem (R.addr (-72)) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-80)).toNat : Int) + 0 ≤ ((R.addr (-72)).toNat : Int); omega))
  have d80 : Mem.loadInt m'.dmem (R.addr (-80)) 8 = Mem.loadInt m.dmem (R.addr (-80)) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-80)).toNat : Int) + 0 ≤ ((R.addr (-80)).toNat : Int); omega))
  obtain ⟨j72, e72, v72⟩ := hA.slot _ o72
  obtain ⟨j80, e80, v80⟩ := hA.slot _ o80
  refine ⟨j72, j80, by rw [d72, hk _ o72 n72, e72], by rw [v72, h72, hcA], by rw [d80, hk _ o80 n80, e80],
    by rw [v80, h80, hm]⟩

end Spike.Lib.A64.WakePh.Ti2

/-- info: 'Spike.Lib.A64.WakePh.Ti2.slotP_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.slotP_place

/-- info: 'Spike.Lib.A64.WakePh.Ti2.slotP_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.Ti2.slotP_keep

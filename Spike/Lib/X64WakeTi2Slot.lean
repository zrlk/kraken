/-
**Main's slots at the second `scc_rt_thread_init` call's nodes** (x86-64;
twin of `Spike/Lib/A64WakeTi2Slot.lean`, `hti_W`'s placement): `wc_main`'s
frame slots `-16` (the box's cell, `movq %rax, -16(%rbp)` at `.x18`) and
`-8` (main's `ThreadId`, `movq %rdi, -8(%rbp)` in the prologue) lie above
the callee's region `R.callee (-80) (-248) 8`, so every state of the
callee's nodes (and of the take's, inside it) reads them as at the call,
where they hold `cA` and `m` (`WcClone.FrW`). With `cA` the box's address
`b` and `m` main's id, they are the places `PlacedSE` at `SpawnSrc l` needs.

- `SlotP`: the two slots read `b` and `t0`.
- `slotP_place`: `SlotP` as the two `placeVal`s.
- `slotP_keep`: `SlotP` at every state the callee's frame keeps, from the
  call's abstract state (`hFm`, `hti_W`'s frame premise) and the box's base.

**Unlike AArch64**: the slots are `-16` and `-8` (A64's `-72`, `-80`;
x86-64's `wc_main` keeps the cell and main's word at the top of its frame,
`WcClone.FrW`); the callee's region is `R.callee (-80) (-248) 8` (A64's
`R.callee (-80) (-256) 0`), the box's base `v - 56` (`hb`'s `+ 56`, A64's
`+ 48`); `hRs` asks `R.lo ≤ -16` (A64's `-80`). The A64 file's import of
`A64WakeSrcCtl` is not needed here (nothing of it is used).

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeTi2Box
import Spike.Lib.X64WakeTcb2Call

namespace Spike.Lib.X64.WakePh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.Tcb2Call (oW)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **Main's slots read `b` and `t0`** at the machine data `m`: slot `-16`
the box's cell, slot `-8` main's id. -/
def SlotP (R : Spike.Lib.Region) (b t0 : Nat) (m : MachineData) : Prop :=
  ∃ j16 j8, Mem.loadInt m.dmem (R.addr (-16)) 8 = some j16 ∧ (BitVec.ofInt 64 j16).toNat = b ∧
    Mem.loadInt m.dmem (R.addr (-8)) 8 = some j8 ∧ (BitVec.ofInt 64 j8).toNat = t0

/-- **`SlotP` as places**: the slots' `placeVal`s. -/
theorem slotP_place {b t0 : Nat} {s : State} (h : SlotP R b t0 s.st.1) :
    placeVal (machine (kernel 1)) s (.slot (R.addr (-16)).toNat) = some b ∧
      placeVal (machine (kernel 1)) s (.slot (R.addr (-8)).toNat) = some t0 := by
  obtain ⟨j16, j8, e16, v16, e8, v8⟩ := h
  constructor
  · show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr (-16)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.X64.privLoad, e16, v16]
  · show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr (-8)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.X64.privLoad, e8, v8]

/-- **`SlotP` at every state the callee's frame keeps**: at the call the
slots hold `cA` and `mw` (`hFm`: an abstract state of `R` at `oW` whose
cells off the callee's region the frame keeps), `cA` the box's `b` and `mw`
main's `t0`; the slots off the callee's region by the box's base (`hb`),
inside `R` (`hRs`). -/
theorem slotP_keep (hb : R.base.toNat + 56 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -16 ∧ 0 ≤ R.hi)
    {b t0 : Nat} {cA mw : BitVec 64} (hcA : cA.toNat = b) (hm : mw.toNat = t0) {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.X64.Abs R oW mC σC ∧ σC.slot (-16) = cA ∧
      σC.slot (-8) = mw ∧ ∀ k, R.Off k → ¬ (R.callee (-80) (-248) 8).Off (k - -80) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.X64.DFrame (R.callee (-80) (-248) 8) m m' → SlotP R b t0 m' := by
  intro m m' hm0 hd
  obtain ⟨mC, σC, hA, h16, h8, hk⟩ := hFm m hm0
  have hB := R.base.isLt
  have o16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have o8 : R.Off (-8) := ⟨by decide, by omega, by omega⟩
  have n16 : ¬ (R.callee (-80) (-248) 8).Off (-16 - -80) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have n8 : ¬ (R.callee (-80) (-248) 8).Off (-8 - -80) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have a16 := addr_box (L := L) hb (k := -16) (by omega) (by omega)
  have a8 := addr_box (L := L) hb (k := -8) (by omega) (by omega)
  have a80 := addr_box (L := L) hb (k := -80) (by omega) (by omega)
  have d16 : Mem.loadInt m'.dmem (R.addr (-16)) 8 = Mem.loadInt m.dmem (R.addr (-16)) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-80)).toNat : Int) + 8 ≤ ((R.addr (-16)).toNat : Int); omega))
  have d8 : Mem.loadInt m'.dmem (R.addr (-8)) 8 = Mem.loadInt m.dmem (R.addr (-8)) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-80)).toNat : Int) + 8 ≤ ((R.addr (-8)).toNat : Int); omega))
  obtain ⟨j16, e16, v16⟩ := hA.slot _ o16
  obtain ⟨j8, e8, v8⟩ := hA.slot _ o8
  refine ⟨j16, j8, by rw [d16, hk _ o16 n16, e16], by rw [v16, h16, hcA], by rw [d8, hk _ o8 n8, e8],
    by rw [v8, h8, hm]⟩

end Spike.Lib.X64.WakePh.Ti2

/-- info: 'Spike.Lib.X64.WakePh.Ti2.slotP_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.slotP_place

/-- info: 'Spike.Lib.X64.WakePh.Ti2.slotP_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2.slotP_keep

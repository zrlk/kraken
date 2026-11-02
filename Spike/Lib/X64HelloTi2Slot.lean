/-
**Main's slots at the second `scc_rt_thread_init` call's nodes** (x86-64; the twin of
`Spike/Lib/A64HelloTi2Slot.lean`, wake's x86-64 version `Spike/Lib/X64WakeTi2Slot.lean`): `wc_main`'s frame
slots in `[-128, -8]` lie above the callee's region `R.callee (-136) (-248) 8`, so every state of the callee's
nodes (and of the take's, inside it) reads them as at the call. At hello's call node (`HelloWc.wcNIH`, its
`FrWH`) slot `-48` holds the box's cell `cA` and slot `-40` main's `ThreadId` word `me` (the slice's words at
`-8 .. -32`).

- `slotH_keep`: one slot `k ∈ [-128, -8]` read as at the call, at every state the callee's frame keeps
  (layout-generic in the slot; the slice's slots use it directly).
- `SlotPH`: slots `-48` and `-40` read `b` and `t0`.
- `slotPH_place`: `SlotPH` as the two `placeVal`s.
- `slotPH_keep`: `SlotPH` at every state the callee's frame keeps, from the call's abstract state (`hFm`) and
  the box's base (`Ti2Box`'s `R.base + 96 = stacksA + 16384`).

No absolute address appears in this file.

## Differences from the AArch64 version

- The slots are `-48` (the cell) and `-40` (main's word), `FrWH`'s (A64's `-104`, `-112`); `slotH_keep`'s range
  is `[-128, -8]` (`wc_main`'s 128 bytes below `%rbp`; A64's `[-144, -8]`) and `hRs` asks `R.lo ≤ -128`
  (A64's `-144`).
- The callee's region is `R.callee (-136) (-248) 8` (A64's `R.callee (-144) (-256) 0`), the box's base `+ 96`
  (A64's `+ 80`), as in `X64HelloTi2Box`; a slot is off the callee's region when it is at or above `-128`, the
  region's top (`-136 + 8`).
- `hFm`'s abstract state is at any offsets `o` (`HelloWc.oCH` at the call, `%rsp` at `-136`; A64's fix `oWH`): the
  slots are read off `Abs.slot`, which does not depend on them.
-/
import Spike.Lib.X64HelloTi2Box
import Spike.Lib.X64HelloWcSp6

namespace Spike.Lib.X64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {R : Spike.Lib.Region} {o : Spike.Lib.X64.SO}

/-- **A slot of `wc_main`'s at or above the call is kept** by the callee's frame: at the call the slot `k`
reads `σC.slot k` (`hFm`: an abstract state of `R` at any offsets `o`, the call's `oCH`, whose cells off the
callee's region the frame keeps); it is off the callee's region by the box's base (`hb`), inside `R` (`hRs`). -/
theorem slotH_keep (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -128 ∧ 0 ≤ R.hi)
    {k : Int} (hk8 : k % 8 = 0) (hk1 : -128 ≤ k) (hk2 : k ≤ -8) {v : BitVec 64} {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.X64.Abs R o mC σC ∧ σC.slot k = v ∧
      ∀ k, R.Off k → ¬ (R.callee (-136) (-248) 8).Off (k - -136) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.X64.DFrame (R.callee (-136) (-248) 8) m m' →
      ∃ j, Mem.loadInt m'.dmem (R.addr k) 8 = some j ∧ BitVec.ofInt 64 j = v := by
  intro m m' hm0 hd
  obtain ⟨mC, σC, hA, hv, hkp⟩ := hFm m hm0
  have hB := R.base.isLt
  have ok : R.Off k := ⟨hk8, by omega, by omega⟩
  have nk : ¬ (R.callee (-136) (-248) 8).Off (k - -136) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have ak := addr_boxH (L := L) hb (k := k) (by omega) (by omega)
  have a136 := addr_boxH (L := L) hb (k := -136) (by omega) (by omega)
  have dk : Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-136)).toNat : Int) + 8 ≤ ((R.addr k).toNat : Int); omega))
  obtain ⟨j, ej, vj⟩ := hA.slot _ ok
  exact ⟨j, by rw [dk, hkp _ ok nk, ej], by rw [vj, hv]⟩

/-- **Main's slots read `b` and `t0`** at the machine data `m`: slot `-48` the box's cell, slot `-40` main's
id. -/
def SlotPH (R : Spike.Lib.Region) (b t0 : Nat) (m : MachineData) : Prop :=
  ∃ j48 j40, Mem.loadInt m.dmem (R.addr (-48)) 8 = some j48 ∧ (BitVec.ofInt 64 j48).toNat = b ∧
    Mem.loadInt m.dmem (R.addr (-40)) 8 = some j40 ∧ (BitVec.ofInt 64 j40).toNat = t0

/-- **`SlotPH` as places**: the slots' `placeVal`s. -/
theorem slotPH_place {b t0 : Nat} {s : State} (h : SlotPH R b t0 s.st.1) :
    placeVal (machine (kernel 1)) s (.slot (R.addr (-48)).toNat) = some b ∧
      placeVal (machine (kernel 1)) s (.slot (R.addr (-40)).toNat) = some t0 := by
  obtain ⟨j48, j40, e48, v48, e40, v40⟩ := h
  constructor
  · show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr (-48)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.X64.privLoad, e48, v48]
  · show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr (-40)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.X64.privLoad, e40, v40]

/-- **`SlotPH` at every state the callee's frame keeps**: at the call the slots hold `cA` and `mw` (`hFm`),
`cA` the box's `b` and `mw` main's `t0` (`slotH_keep` at `-48`, `-40`). -/
theorem slotPH_keep (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -128 ∧ 0 ≤ R.hi)
    {b t0 : Nat} {cA mw : BitVec 64} (hcA : cA.toNat = b) (hm : mw.toNat = t0) {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.X64.Abs R o mC σC ∧ σC.slot (-48) = cA ∧
      σC.slot (-40) = mw ∧ ∀ k, R.Off k → ¬ (R.callee (-136) (-248) 8).Off (k - -136) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.X64.DFrame (R.callee (-136) (-248) 8) m m' → SlotPH R b t0 m' := by
  intro m m' hm0 hd
  obtain ⟨j48, e48, v48⟩ := slotH_keep (L := L) hb hRs (k := -48) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, h1, _, hk⟩ => ⟨σC, hA, h1, hk⟩) m m' hm0 hd
  obtain ⟨j40, e40, v40⟩ := slotH_keep (L := L) hb hRs (k := -40) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, _, h2, hk⟩ => ⟨σC, hA, h2, hk⟩) m m' hm0 hd
  exact ⟨j48, j40, e48, by rw [v48, hcA], e40, by rw [v40, hm]⟩

end Spike.Lib.X64.HelloPh.Ti2

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.slotH_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.slotH_keep

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.slotPH_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.slotPH_place

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.slotPH_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.slotPH_keep

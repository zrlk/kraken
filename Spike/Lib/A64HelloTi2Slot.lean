/-
**Main's slots at the second `scc_rt_thread_init` call's nodes** (AArch64;
the hello twin of `Spike/Lib/A64WakeTi2Slot.lean`): `wc_main`'s frame slots
at or above `-144` lie above the callee's region `R.callee (-144) (-256) 0`,
so every state of the callee's nodes (and of the take's, inside it) reads
them as at the call. At hello's call node (`HelloWc.wcNIH`, its `FrWH`) slot
`-104` holds the box's cell `cA` and slot `-112` main's `ThreadId` word `me`
(the slice's words at `-144 .. -120`).

- `slotH_keep`: one slot `k ∈ [-144, -8]` read as at the call, at every
  state the callee's frame keeps (layout-generic in the slot; the slice's
  slots use it directly).
- `SlotPH`: slots `-104` and `-112` read `b` and `t0` (wake's `SlotP` at
  `-72`, `-80`).
- `slotPH_place`: `SlotPH` as the two `placeVal`s.
- `slotPH_keep`: `SlotPH` at every state the callee's frame keeps, from the
  call's abstract state (`hFm`) and the box's base (`BoxPureH`'s).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloTi2Box
import Spike.Lib.A64HelloWcSp6

namespace Spike.Lib.A64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.HelloPh.WcSp6 (oWH)

variable {L : RuntimeLayout} {R : Spike.Lib.Region}

/-- **A slot of `wc_main`'s at or above the call is kept** by the callee's
frame: at the call the slot `k` reads `σC.slot k` (`hFm`: an abstract state
of `R` at `oWH` whose cells off the callee's region the frame keeps); it is
off the callee's region by the box's base (`hb`), inside `R` (`hRs`). -/
theorem slotH_keep (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -144 ∧ 0 ≤ R.hi)
    {k : Int} (hk8 : k % 8 = 0) (hk1 : -144 ≤ k) (hk2 : k ≤ -8) {v : BitVec 64} {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.A64.Flow.Abs R oWH mC σC ∧ σC.slot k = v ∧
      ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.A64.Flow.DFrame (R.callee (-144) (-256) 0) m m' →
      ∃ j, Mem.loadInt m'.dmem (R.addr k) 8 = some j ∧ BitVec.ofInt 64 j = v := by
  intro m m' hm0 hd
  obtain ⟨mC, σC, hA, hv, hkp⟩ := hFm m hm0
  have hB := R.base.isLt
  have ok : R.Off k := ⟨hk8, by omega, by omega⟩
  have nk : ¬ (R.callee (-144) (-256) 0).Off (k - -144) := fun ⟨_, _, h⟩ => by
    simp only [Spike.Lib.Region.callee] at h; omega
  have ak := addr_boxH (L := L) hb (k := k) (by omega) (by omega)
  have a144 := addr_boxH (L := L) hb (k := -144) (by omega) (by omega)
  have dk : Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt m.dmem (R.addr k) 8 :=
    hd _ (by omega) (.inr (by show ((R.addr (-144)).toNat : Int) + 0 ≤ ((R.addr k).toNat : Int); omega))
  obtain ⟨j, ej, vj⟩ := hA.slot _ ok
  exact ⟨j, by rw [dk, hkp _ ok nk, ej], by rw [vj, hv]⟩

/-- **Main's slots read `b` and `t0`** at the machine data `m`: slot `-104`
the box's cell, slot `-112` main's id. -/
def SlotPH (R : Spike.Lib.Region) (b t0 : Nat) (m : MachineData) : Prop :=
  ∃ j104 j112, Mem.loadInt m.dmem (R.addr (-104)) 8 = some j104 ∧ (BitVec.ofInt 64 j104).toNat = b ∧
    Mem.loadInt m.dmem (R.addr (-112)) 8 = some j112 ∧ (BitVec.ofInt 64 j112).toNat = t0

/-- **`SlotPH` as places**: the slots' `placeVal`s. -/
theorem slotPH_place {b t0 : Nat} {s : State} (h : SlotPH R b t0 s.st.1) :
    placeVal (machine (kernel 1)) s (.slot (R.addr (-104)).toNat) = some b ∧
      placeVal (machine (kernel 1)) s (.slot (R.addr (-112)).toNat) = some t0 := by
  obtain ⟨j104, j112, e104, v104, e112, v112⟩ := h
  constructor
  · show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr (-104)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.A64.privLoad, e104, v104]
  · show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr (-112)).toNat)).map (·.toNat) = _
    simp [Scc.Sem.A64.privLoad, e112, v112]

/-- **`SlotPH` at every state the callee's frame keeps**: at the call the
slots hold `cA` and `mw` (`hFm`), `cA` the box's `b` and `mw` main's `t0`
(`slotH_keep` at `-104`, `-112`). -/
theorem slotPH_keep (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -144 ∧ 0 ≤ R.hi)
    {b t0 : Nat} {cA mw : BitVec 64} (hcA : cA.toNat = b) (hm : mw.toNat = t0) {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.A64.Flow.Abs R oWH mC σC ∧ σC.slot (-104) = cA ∧
      σC.slot (-112) = mw ∧ ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.A64.Flow.DFrame (R.callee (-144) (-256) 0) m m' → SlotPH R b t0 m' := by
  intro m m' hm0 hd
  obtain ⟨j104, e104, v104⟩ := slotH_keep (L := L) hb hRs (k := -104) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, h1, _, hk⟩ => ⟨σC, hA, h1, hk⟩) m m' hm0 hd
  obtain ⟨j112, e112, v112⟩ := slotH_keep (L := L) hb hRs (k := -112) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, _, h2, hk⟩ => ⟨σC, hA, h2, hk⟩) m m' hm0 hd
  exact ⟨j104, j112, e104, by rw [v104, hcA], e112, by rw [v112, hm]⟩

end Spike.Lib.A64.HelloPh.Ti2

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.slotH_keep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.slotH_keep

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.slotPH_place' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.slotPH_place

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.slotPH_keep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.slotPH_keep

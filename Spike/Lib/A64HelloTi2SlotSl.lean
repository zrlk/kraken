/-
**The slice's slots at the second `scc_rt_thread_init` call's nodes**
(AArch64; beside `A64HelloTi2Slot`): `wc_main` spills the slice's `x0`, `x2`,
`x3` at `-144`, `-128`, `-120` (`WcSp6.FrWH`); every state of the callee's
nodes reads them as at the call (`slotH_keep`). Hello's spawn packet carries
the slice's words, so `Ti2Hat.hti_H`'s `hpl` takes these slots besides
`SlotPH`'s (`SpawnPl.placedSE_slotsH`).

- `SlotRdH`, `slotRdH_place`: one slot reads a word, as a `placeVal`.
- `SlotSlH`: the slice's slots `-144`, `-128`, `-120` read `w0`, `w2`, `w3`.
- `slotSlH_keep`: `SlotSlH` at every state the callee's frame keeps, from
  the call's abstract state (`hFm`).

No absolute address appears in this file.
-/
import Spike.Lib.A64HelloTi2Slot

namespace Spike.Lib.A64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64
open Spike.Lib (Region)
open Spike.Lib.A64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {R : Region}

/-- **Slot `k` of `R` reads `v`** at the machine data `m`. -/
def SlotRdH (R : Region) (k : Int) (v : Nat) (m : MachineData) : Prop :=
  ∃ j, Mem.loadInt m.dmem (R.addr k) 8 = some j ∧ (BitVec.ofInt 64 j).toNat = v

/-- **`SlotRdH` as a place**: the slot's `placeVal`. -/
theorem slotRdH_place {k : Int} {v : Nat} {s : State} (h : SlotRdH R k v s.st.1) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some v := by
  obtain ⟨j, e, hv⟩ := h
  show (Scc.Sem.A64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.A64.privLoad, e, hv]

/-- **The slice's slots read `w0`, `w2`, `w3`** at the machine data `m`:
`-144`, `-128`, `-120` (`x0`, `x2`, `x3` spilled; `x1`, the buffer's offset,
is not a word of the packet). -/
def SlotSlH (R : Region) (w0 w2 w3 : Nat) (m : MachineData) : Prop :=
  SlotRdH R (-144) w0 m ∧ SlotRdH R (-128) w2 m ∧ SlotRdH R (-120) w3 m

/-- **`SlotSlH` at every state the callee's frame keeps**: at the call the
slice's slots hold `sl`'s `x0`, `x2`, `x3` (`hFm`; `slotH_keep` at each). -/
theorem slotSlH_keep (hb : R.base.toNat + 80 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -144 ∧ 0 ≤ R.hi)
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.A64.Flow.Abs R WcSp6.oWH mC σC ∧ σC.slot (-144) = sl.1 ∧
      σC.slot (-128) = sl.2.2.1 ∧ σC.slot (-120) = sl.2.2.2 ∧
      ∀ k, R.Off k → ¬ (R.callee (-144) (-256) 0).Off (k - -144) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.A64.Flow.DFrame (R.callee (-144) (-256) 0) m m' →
      SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat m' := by
  intro m m' hm0 hd
  obtain ⟨j0, e0, v0⟩ := slotH_keep (L := L) hb hRs (k := -144) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, h0, _, _, hk⟩ => ⟨σC, hA, h0, hk⟩) m m' hm0 hd
  obtain ⟨j2, e2, v2⟩ := slotH_keep (L := L) hb hRs (k := -128) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, _, h2, _, hk⟩ => ⟨σC, hA, h2, hk⟩) m m' hm0 hd
  obtain ⟨j3, e3, v3⟩ := slotH_keep (L := L) hb hRs (k := -120) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, _, _, h3, hk⟩ => ⟨σC, hA, h3, hk⟩) m m' hm0 hd
  exact ⟨⟨j0, e0, by rw [v0]⟩, ⟨j2, e2, by rw [v2]⟩, ⟨j3, e3, by rw [v3]⟩⟩

end Spike.Lib.A64.HelloPh.Ti2

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.slotRdH_place' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.slotRdH_place

/-- info: 'Spike.Lib.A64.HelloPh.Ti2.slotSlH_keep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Ti2.slotSlH_keep

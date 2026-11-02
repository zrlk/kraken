/-
**The slice's slots at the second `scc_rt_thread_init` call's nodes** (x86-64; the twin of
`Spike/Lib/A64HelloTi2SlotSl.lean`, beside `X64HelloTi2Slot`): `wc_main` spills the slice's registers `sl` at
`-8`, `-16`, `-24`, `-32` (`WcSp6.FrWH`); every state of the callee's nodes reads the words at `-8`, `-24`,
`-32` as at the call (`slotH_keep`). Hello's spawn packet carries the slice's words, so the spawn's placement
takes these slots besides `SlotPH`'s.

- `SlotRdH`, `slotRdH_place`: one slot reads a word, as a `placeVal`.
- `SlotSlH`: the slice's slots `-8`, `-24`, `-32` read `w0`, `w2`, `w3`.
- `slotSlH_keep`: `SlotSlH` at every state the callee's frame keeps, from the call's abstract state (`hFm`).

No absolute address appears in this file.

## Differences from the AArch64 version

- The slice's words are at `-8`, `-24`, `-32` (`FrWH`'s `sl.1`, `sl.2.2.1`, `sl.2.2.2`; A64's `-144`, `-128`,
  `-120`); the callee's region is `R.callee (-136) (-248) 8`, the box's base `+ 96`, `hRs` asks `R.lo ≤ -128`
  (as `X64HelloTi2Slot.slotH_keep`).
-/
import Spike.Lib.X64HelloTi2Slot

namespace Spike.Lib.X64.HelloPh.Ti2

open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64
open Spike.Lib (Region)
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {L : RuntimeLayout} {R : Region} {o : Spike.Lib.X64.SO}

/-- **Slot `k` of `R` reads `v`** at the machine data `m`. -/
def SlotRdH (R : Region) (k : Int) (v : Nat) (m : MachineData) : Prop :=
  ∃ j, Mem.loadInt m.dmem (R.addr k) 8 = some j ∧ (BitVec.ofInt 64 j).toNat = v

/-- **`SlotRdH` as a place**: the slot's `placeVal`. -/
theorem slotRdH_place {k : Int} {v : Nat} {s : State} (h : SlotRdH R k v s.st.1) :
    placeVal (machine (kernel 1)) s (.slot (R.addr k).toNat) = some v := by
  obtain ⟨j, e, hv⟩ := h
  show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
  simp [Scc.Sem.X64.privLoad, e, hv]

/-- **The slice's slots read `w0`, `w2`, `w3`** at the machine data `m`: `-8`, `-24`, `-32` (`sl.1`,
`sl.2.2.1`, `sl.2.2.2` spilled; `sl.2.1`, the buffer's offset, is not a word of the packet). -/
def SlotSlH (R : Region) (w0 w2 w3 : Nat) (m : MachineData) : Prop :=
  SlotRdH R (-8) w0 m ∧ SlotRdH R (-24) w2 m ∧ SlotRdH R (-32) w3 m

/-- **`SlotSlH` at every state the callee's frame keeps**: at the call the slice's slots hold `sl`'s `sl.1`,
`sl.2.2.1`, `sl.2.2.2` (`hFm`; `slotH_keep` at each). -/
theorem slotSlH_keep (hb : R.base.toNat + 96 = L.stacksA.toNat + 16384) (hRs : R.lo ≤ -128 ∧ 0 ≤ R.hi)
    {sl : BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64} {F' : MachineData → Prop}
    (hFm : ∀ m', F' m' → ∃ mC σC, Spike.Lib.X64.Abs R o mC σC ∧ σC.slot (-8) = sl.1 ∧
      σC.slot (-24) = sl.2.2.1 ∧ σC.slot (-32) = sl.2.2.2 ∧
      ∀ k, R.Off k → ¬ (R.callee (-136) (-248) 8).Off (k - -136) →
        Mem.loadInt m'.dmem (R.addr k) 8 = Mem.loadInt mC.dmem (R.addr k) 8) :
    ∀ m m', F' m → Spike.Lib.X64.DFrame (R.callee (-136) (-248) 8) m m' →
      SlotSlH R sl.1.toNat sl.2.2.1.toNat sl.2.2.2.toNat m' := by
  intro m m' hm0 hd
  obtain ⟨j0, e0, v0⟩ := slotH_keep (L := L) hb hRs (k := -8) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, h0, _, _, hk⟩ => ⟨σC, hA, h0, hk⟩) m m' hm0 hd
  obtain ⟨j2, e2, v2⟩ := slotH_keep (L := L) hb hRs (k := -24) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, _, h2, _, hk⟩ => ⟨σC, hA, h2, hk⟩) m m' hm0 hd
  obtain ⟨j3, e3, v3⟩ := slotH_keep (L := L) hb hRs (k := -32) (by decide) (by decide) (by decide)
    (fun m' h => (hFm m' h).imp fun _ ⟨σC, hA, _, _, h3, hk⟩ => ⟨σC, hA, h3, hk⟩) m m' hm0 hd
  exact ⟨⟨j0, e0, by rw [v0]⟩, ⟨j2, e2, by rw [v2]⟩, ⟨j3, e3, by rw [v3]⟩⟩

end Spike.Lib.X64.HelloPh.Ti2

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.slotRdH_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.slotRdH_place

/-- info: 'Spike.Lib.X64.HelloPh.Ti2.slotSlH_keep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Ti2.slotSlH_keep

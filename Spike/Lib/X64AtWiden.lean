/-
**Widening a node's region** (x86-64): a state in `At` of a
node on region `R` is in `At` of the same node on a wider region `R'` with
the same base, provided

- the node's invariant reads only `R`'s slots (`SlotsOnly n.J R.Off`: two
  abstract states with the same registers, vector registers, flags and
  `R`-slots satisfy it alike), and
- every slot of `R'` outside `R` is mapped in the state's private memory
  (`hnew`: its 8-byte load is defined).

The abstract state of the wider region keeps `R`'s slots and takes each new
slot's value from memory, so nothing is claimed about the new slots beyond
their being mapped. Executable, end of text, declarations, pc, static
offsets (`SORel` depends on the base and the offsets only) and the frame
condition are unchanged.

- `SlotsOnly J S`: `J` reads only the slots in `S`.
- `At.widen`: the widening.
-/
import Spike.Lib.X64Cfg

namespace Spike.Lib.X64

open Kraken Kraken.Promising Kraken.Promising.X64

/-- **The invariant `J` reads only the slots in `S`**: abstract states with
the same registers, vector registers and flags and the same slots in `S`
satisfy it alike. -/
def SlotsOnly (J : AS → Ctl → Prop) (S : Int → Prop) : Prop :=
  ∀ σ σ' : AS, ∀ c, σ.regs = σ'.regs → σ.zmms = σ'.zmms → σ.status = σ'.status →
    (∀ k, S k → σ.slot k = σ'.slot k) → J σ c → J σ' c

/-- **A node's region widens** to `R'` (same base, `hb`) when the node's
invariant reads only `R`'s slots (`hS`) and every slot of `R'` outside `R`
is mapped in the state's memory (`hnew`). -/
theorem At.widen {exe : _root_.Executable} {endPc : Int64} {R R' : Region} {F : MachineData → Prop} {n : ND}
    {s : State} {c : Ctl} (h : At exe endPc R F n s c) (hb : R'.base = R.base) (hS : SlotsOnly n.J R.Off)
    (hnew : ∀ k, R'.Off k → ¬ R.Off k → (Mem.loadInt s.st.1.dmem (R'.addr k) 8).isSome) :
    At exe endPc R' F n s c := by
  classical
  obtain ⟨he, hn, hd, hpc, σ, hA, hF, hJ⟩ := h
  have haddr : ∀ k, R'.addr k = R.addr k := fun k => by simp only [Region.addr, hb]
  let σ' : AS := { σ with slot := fun k => if R.Off k then σ.slot k else
    ((Mem.loadInt s.st.1.dmem (R'.addr k) 8).map (BitVec.ofInt 64)).getD 0#64 }
  refine ⟨he, hn, hd, hpc, σ', ⟨hA.regs, hA.zmms, hA.status, fun r k hk => (hA.so r k hk).trans (haddr k).symm,
    fun k hk => ?_⟩, hF, hS σ σ' c rfl rfl rfl (fun k hk => by simp [σ', hk]) hJ⟩
  by_cases hR : R.Off k
  · rw [haddr]
    obtain ⟨j, hj, hjv⟩ := hA.slot k hR
    exact ⟨j, hj, by simp [σ', hR, hjv]⟩
  · obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (hnew k hk hR)
    exact ⟨j, hj, by simp [σ', hR, hj]⟩

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.At.widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.At.widen

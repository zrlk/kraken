/-
**The worker's own word off the child's shared writes, x86-64** (the hello counterpart of
`Spike/Lib/X64WakeOwnWSep.lean`): the premises `hA : w.w4 ≠ W`, `hB : w.w5 + 16 ≠ W` and `htp : tp + 24 ≠ W` of
`Flow.Worker.Hello.OwnZH.zObl_own` (`Spike/Lib/X64HelloOwnObl.lean`) from the child segment's premises
`ChildPrem` at a memory side `msXW ms O T W` (runtime writes off both self words) and the flag's placement.

- `ne_of_offTcb`: a word off the TCB word `W` is not at `W`.
- `ne_of_stOk_msXW`: a runtime store's word at `msXW ms O T W` is not `W` (`StOk.mp`).
- `ne_of_valRep_nlab`: the flag's word (`ValRep` of `cS` at offset `0`, `cS` inside its label) is not a word
  outside every placed label.
- `own_of_childPrem`: the three premises at once, at `ChildPrem … (fun _ => msXW ms O T W) …`.

Unlike wake's (`X64WakeOwnWSep`, at the real layout: heap disjoint from the runtime words, main's TCB word), the
facts here are from the memory side and the label placement alone: the park word and the exit word are runtime
stores of `msXW` (so off `W`), the flag's word is inside its label while `W` is outside every placed label.
-/
import Spike.Lib.X64HelloWorkerSegP
import Spike.Lib.X64WakeOwnXInst
import Spike.Lib.X64WakeOwnXW

namespace Spike.Lib.X64HelloOwnSep

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.Inv2Core
open Spike.Lib.X64WakeOwnX (OffTcb msXW)
open Spike.Lib.X64.Flow.Worker.Hello.SegR (ChildPrem)
open Spike.Lib.X64.Flow.Ret0 (StOk)

/-- **A word off the TCB word `W` is not at `W`.** -/
theorem ne_of_offTcb {W a : BitVec 64} (h : OffTcb W ⟨a, 8⟩) : a ≠ W := by
  rintro rfl
  rcases h with h | h <;> simp at h <;> omega

/-- **A runtime store's word at `msXW ms O T W` is not `W`**: `msXW`'s runtime writes are off both self words. -/
theorem ne_of_stOk_msXW {ms : MemSide isa} {O T W : BitVec 64} {F : MachineData → Prop} {a v : BitVec 64}
    (h : StOk (msXW ms O T W) F a v) : a ≠ W :=
  ne_of_offTcb (h.mp.2 rfl).2

/-- **The flag's word is not a word outside every placed label**: `ValRep` of `cS` at offset `0` puts the word
at `cS`'s address, inside its label when `cS`'s offset is below the label's size. -/
theorem ne_of_valRep_nlab {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {cS : WeakMem.Address} {a W : BitVec 64} (ho : cS.offset < lsize cS.label)
    (hv : Scc.Sem.ValRep lbl (.loc cS 0) a.toNat) (hW : ¬ InLabel lbl lsize ⟨W, 8⟩) : a ≠ W := by
  rintro rfl
  obtain ⟨-, x, hx, hax⟩ := hv
  simp only [Scc.Sem.wordAddr, Option.map_eq_some_iff] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have ho' : @LT.lt Nat _ cS.offset (lsize cS.label) := ho
  refine hW ⟨cS.label, b, hb, ?_⟩
  show b ≤ a.toNat ∧ a.toNat < b + 8 * lsize cS.label
  omega

/-- **The three premises of `zObl_own` from `ChildPrem`** at the memory side `msXW ms O T W` and a flag `cS`
inside its label, `W` outside every placed label: the flag's word, the park word and the exit word are not
`W`. -/
theorem own_of_childPrem {exe : _root_.Executable} {endPc : Int64} {kp : Nat}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isa}
    {O T W : BitVec 64} {F : MachineData → Prop} {w : Flow.Worker.Hello.Child.Words} {tp sp0 : BitVec 64}
    {w0 w1 w2 w3 w4 : TermRun.Word} {n m : Nat} {cS : WeakMem.Address}
    (h : ChildPrem exe endPc kp lbl (fun _ => msXW ms O T W) F w tp sp0 w0 w1 w2 w3 w4 n m)
    (hcS : w3.val = .loc cS 0) (ho : cS.offset < lsize cS.label) (hW : ¬ InLabel lbl lsize ⟨W, 8⟩) :
    w.w4 ≠ W ∧ w.w5 + 16#64 ≠ W ∧ tp + 24#64 ≠ W :=
  ⟨ne_of_valRep_nlab ho (hcS ▸ h.hv) hW, ne_of_stOk_msXW h.hS, ne_of_stOk_msXW h.hSx⟩

end Spike.Lib.X64HelloOwnSep

/-- info: 'Spike.Lib.X64HelloOwnSep.ne_of_valRep_nlab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnSep.ne_of_valRep_nlab

/-- info: 'Spike.Lib.X64HelloOwnSep.own_of_childPrem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnSep.own_of_childPrem

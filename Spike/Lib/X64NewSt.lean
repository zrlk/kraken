/-
**The box's initialising store at a node gives `NewStM`** (x86-64): the
premises of `Alloc.newStore_ndW` (`Spike/Lib/X64AllocBox.lean`) at a state
of the node give the store's premises at the pair (`NewStM`), the second
disjunct of the consumer's write obligation (`NodesA.arena`) at the box's
store, from the very facts the node's row (`Out.newStore`) is built from.
The x86-64 twin of `Spike/Lib/A64NewSt.lean` (same names).

- `Alloc.newStM_nd`: the rule.
-/
import Spike.Lib.X64AllocBox
import Spike.Lib.OutNew

namespace Spike.Lib.X64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`NewStM` at a state of a box's store node** `movq %r, k(%b)`, from
`newStore_ndW`'s premises (`hcode`, `hxa`, `hedge`; no segment premises). -/
theorem newStM_nd {n : ND} {b r : Reg64} {k : Int64} {z : Nat} (Eb : WeakMem.AllocLabel → Nat → ND)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [(stDir b k r, z)])
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (Eb l A) s c → ms.xa l A 1 s c)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.newOk ∧ ms.mp ⟨bAddr σ.regs b k, 8⟩ true ∧ Mem.loadInt m.dmem (bAddr σ.regs b k) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (ty : Ty) (e : Expr) (w wold : TermRun.Word) (old : Nat),
        (∃ T, c.term = .let_ x (.new a T) e) ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        TermRun.accs ty = some [.one] ∧
        Scc.Sem.ValRep lbl w.val (σ.regs.get64 r).toNat ∧
        c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        (bAddr σ.regs b k).toNat = ms.heap + 16 * old + ms.off 1 ty ∧ old + ms.units 1 ty ≤ ms.cells ∧
        ∀ l, lbl l = none → Hit (Eb l (bAddr σ.regs b k).toNat) ⟨n.pc + Int64.ofNat z, n.o, σ⟩
          ⟨e, (x, .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩)
    {s : State} {c : Ctl} (hAt : At exe endPc R F n s c) : NewStM p lbl ms s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (stDir b k r) z := (hcode s he hn).cell0 rfl rfl hpc
  obtain ⟨hN, hmp, hdm, x, a, ty, e, w, wold, old, ht, hev, hu, hv, hh, hold, hAeq, hcl, hX⟩ := hedge _ σ c hA hD hJ
  have ha : eaddr s z (mB b k) = bAddr σ.regs b k := (eaddr_mB s z b k).trans (by rw [hA.regs]; rfl)
  have hex := exec_store_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [Reg64s.get_low64, hA.regs] at hex
  have hs1 : after s z s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat z) } := by
    simp only [after, hpc]
  rw [hs1] at hex
  refine ⟨_, _, _, _, x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hu, ?_, hh, hold, hAeq, hcl, fun l hl =>
    hxa _ _ _ _ hl ((hX l hl).at he hn hdc hA hD)⟩
  rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))]

/-- info: 'Spike.Lib.X64.Alloc.newStM_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms newStM_nd

end Spike.Lib.X64.Alloc

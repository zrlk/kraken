/-
**The box's initialising store at a node gives `NewStM`** (AArch64): the
premises of `Alloc.newStore_ndW` (`Spike/Lib/A64AllocBox.lean`) at a state
of the node give the store's premises at the pair (`NewStM`), the second
disjunct of the consumer's write obligation (`NodesA.arena`) at the box's
store, from the very facts the node's row (`Out.newStore`) is built from.

- `Alloc.newStM_nd`: the rule.
-/
import Spike.Lib.A64AllocBox
import Spike.Lib.OutNew

namespace Spike.Lib.A64.Alloc

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64.Flow
open Kraken.Promising.Lower.A64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **`NewStM` at a state of a box's store node** `str Xt, [Xn, #i]`, from
`newStore_ndW`'s premises (`hcode`, `hxa`, `hedge`; no segment premises). -/
theorem newStM_nd {n : ND} {t b : XReg} {i : Int64} (Eb : WeakMem.AllocLabel → Nat → ND)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [strDir t b i])
    (hxa : ∀ l A s c, lbl l = none → At exe endPc R F (Eb l A) s c → ms.xa l A 1 s c)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      ms.newOk ∧ ms.mp ⟨rAddr σ.regs b i, 8⟩ true ∧ Mem.loadInt m.dmem (rAddr σ.regs b i) 8 = none ∧
      ∃ (x : String) (a : CoreTerm.At) (ty : Ty) (e : Expr) (w wold : TermRun.Word) (old : Nat),
        c.term = .let_ x (.new a) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        TermRun.accs ty = some [.one] ∧
        Scc.Sem.ValRep lbl w.val (σ.regs.getRegOrZr (.low (.reg t) .W64)).toNat ∧
        c.hold = some (ms.ctr, wold) ∧ TermRun.numOf [wold] = some old ∧
        (rAddr σ.regs b i).toNat = ms.heap + 16 * old + ms.off 1 ty ∧ old + ms.units 1 ty ≤ ms.cells ∧
        ∀ l, lbl l = none → Hit (Eb l (rAddr σ.regs b i).toNat) ⟨n.pc + Int64.ofNat 4, n.o, σ⟩
          ⟨e, (x, .ptr .own ty, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) :: c.env, none⟩)
    {s : State} {c : Ctl} (hAt : At exe endPc R F n s c) : NewStM p lbl ms s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  have hc : CellAt s (strDir t b i) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hN, hmp, hdm, x, a, ty, e, w, wold, old, ht, hev, hu, hv, hh, hold, hAeq, hcl, hX⟩ := hedge _ σ c hA hD hJ
  have ha : rAddr s.st.1.regs b i = rAddr σ.regs b i := by rw [hA.regs]
  have hex := exec_str_agrees hc ha (by exact hdm) (agrees_of_decls hdc _ _)
  rw [hA.regs] at hex
  have hs1 : after s 4 s.st.1 = { s with st := (s.st.1, n.pc + Int64.ofNat 4) } := by
    simp only [after, hpc]
  rw [hs1] at hex
  refine ⟨_, _, _, _, x, a, ty, e, w, wold, old, hN, hex, hmp, ht, hev, hu, ?_, hh, hold, hAeq, hcl, fun l hl =>
    hxa _ _ _ _ hl ((hX l hl).at he hn hdc hA hD)⟩
  rwa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (BitVec.isLt _) (by decide))]

/-- info: 'Spike.Lib.A64.Alloc.newStM_nd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms newStM_nd

end Spike.Lib.A64.Alloc

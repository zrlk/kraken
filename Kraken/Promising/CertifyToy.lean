/-
`ISA.LawfulState` for the Toy ISA (`PromiseSafe.lean`): `beqState` compares
the pc, the registers and the program, i.e. the whole state, so it is
equality and the static part can be trivial. The Toy ISA therefore gets the
original, cache-independent `CertifySound` as well (`certifySound_toy`).
-/
import Kraken.Promising.Toy
import Kraken.Promising.PromiseSafe

namespace Kraken.Promising.Toy

deriving instance ReflBEq, LawfulBEq for Kraken.LoadKind
deriving instance ReflBEq, LawfulBEq for Kraken.StoreKind
deriving instance ReflBEq, LawfulBEq for Kraken.RmwKind
deriving instance ReflBEq, LawfulBEq for Kraken.FenceKind
deriving instance ReflBEq, LawfulBEq for Opd
deriving instance ReflBEq, LawfulBEq for Instr

theorem beqState_iff (a b : State) : isa.beqState a b = true ↔ a = b := by
  show (a.pc == b.pc && a.regs == b.regs && a.prog == b.prog) = true ↔ a = b
  cases a
  cases b
  simp only [Bool.and_eq_true, beq_iff_eq, State.mk.injEq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h2, h3⟩, h1⟩

instance : ISA.LawfulState isa where
  static _ := { prog := #[] }
  beq_refl a := (beqState_iff a a).mpr rfl
  beq_symm a b h := (beqState_iff b a).mpr ((beqState_iff a b).mp h).symm
  beq_trans a b c h h' := (beqState_iff a c).mpr (((beqState_iff a b).mp h).trans ((beqState_iff b c).mp h'))
  hash_eq a b h := by rw [(beqState_iff a b).mp h]
  eq_of_beq a b h _ := (beqState_iff a b).mp h
  exec_static _ tree _ := EvTree.All.of_forall (fun _ => rfl) tree

/-- `CertifySound` for the Toy ISA: for every cache. -/
theorem certifySound_toy (A : Arch) : CertifySound A isa :=
  certifySound A fun a b h => (beqState_iff a b).mp h

end Kraken.Promising.Toy

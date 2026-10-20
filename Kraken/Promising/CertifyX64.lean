/-
`ISA.LawfulState` for the x64 instance (`PromiseSafe.lean`): `beqState`
compares the machine state (registers, flags, private memory, pc), and that
comparison is equality; the rest of a thread state (program, end address,
trace printer, declarations) is static, since an instruction only replaces
the machine state. So `succs_cases` and `write_invariant` hold for x64
programs with no hypothesis on `certify`.
-/
import Kraken.Promising.X64
import Kraken.Promising.PromiseSafe

namespace Kraken.Promising.X64

deriving instance ReflBEq, LawfulBEq for Reg64s
instance : LawfulBEq ZmmValue := inferInstanceAs (LawfulBEq (BitVec 512))
deriving instance ReflBEq, LawfulBEq for RegZmms
deriving instance ReflBEq, LawfulBEq for StatusFlags
deriving instance ReflBEq, LawfulBEq for MachineData

theorem beqState_iff (a b : State) : isa.beqState a b = true ↔ a.st = b.st :=
  beq_iff_eq

/-- The static part of a thread state: everything but the machine state. -/
def static (s : State) : State := { s with st := ({}, 0) }

instance : ISA.LawfulState isa where
  static := static
  beq_refl a := (beqState_iff a a).mpr rfl
  beq_symm a b h := (beqState_iff b a).mpr ((beqState_iff a b).mp h).symm
  beq_trans a b c h h' := (beqState_iff a c).mpr (((beqState_iff a b).mp h).trans ((beqState_iff b c).mp h'))
  hash_eq a b h := by
    have h := (beqState_iff a b).mp h
    show mixHash _ _ = mixHash _ _
    rw [h]
  eq_of_beq a b h hs := by
    have he := (beqState_iff a b).mp h
    cases a
    cases b
    simp only [static] at hs he
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
    subst he
    rfl
  exec_static a tree h := by
    change exec a = some tree at h
    unfold exec at h
    split at h
    · cases h
    · cases h
      exact EvTree.All.map (P := fun s => static s = static a) (fun st => { a with st }) (fun _ => rfl) _

/-- `succs_cases` for x64, unconditionally. -/
example (A : Arch) (fuel : Nat) (c c' : Config isa) (h : c' ∈ (succs A c fuel).1) : SuccKind A c c' :=
  succs_cases h

end Kraken.Promising.X64

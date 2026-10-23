/-
**The A64 rows under the typing guard** (`Spike.Lib.Typed`).

- `seg_add_typed`: the checked `+` (`seg_add`) without the hypothesis that
  its operands are numbers: in a typed control they are
  (`Scc.Sem.TypedAt.add_num`).
-/
import Spike.Lib.A64
import Spike.Lib.Typed

namespace Spike.Lib

open CoreLang CoreTerm

namespace A64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {F : Frame}
  {slot : String → Option Int64}

/-- **The checked `+` in a typed control** (`seg_add`): the operands are
numbers because the control is typed. -/
theorem seg_add_typed {pc : Int64} {x a b : String} {e : Expr} {oa ob : Int64} {L : String} {od lpc : Int64}
    {env0 : TermRun.Env} (ha : slot a = some oa) (hb : slot b = some ob) {ta tb : Ty} {wa wb : TermRun.Word}
    (hla : TermRun.lookupE env0 a = some (ta, [wa])) (hlb : TermRun.lookupE env0 b = some (tb, [wb]))
    (hod : F.Off od) (hfree : ∀ y, slot y = some od → y = x) :
    SegJ (Typed p) p lbl ms (AddIn lbl F slot pc x a b e oa ob L od lpc env0)
      (fun s c => AddOut lbl F slot pc x e oa ob L od lpc env0 (TermRun.addW wa wb) s c ∨
        AddAbort lbl F slot pc x a b e oa ob L od lpc env0 s c) := by
  refine SegJ.of_entry (Φ := (∃ n, wa.val = .num n) ∧ ∃ m, wb.val = .num m) ?_ fun ⟨⟨n, hna⟩, ⟨m, hnb⟩⟩ =>
    seg_add ha hb hla hlb hna hnb hod hfree
  rintro s c ⟨-, -, -, rfl, -⟩ hj
  exact ⟨Scc.Sem.TypedAt.add_num hj rfl (.inl rfl) (by simpa [TermRun.evalAt] using hla),
    Scc.Sem.TypedAt.add_num hj rfl (.inr rfl) (by simpa [TermRun.evalAt] using hlb)⟩

end A64

end Spike.Lib

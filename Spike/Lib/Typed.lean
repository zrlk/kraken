/-
**Segments under the typing guard**: `SegJ` with the guard that the source
control is well typed (`Scc.Sem.TypedAt`, one frame, no type arguments),
which the global proof supplies at every reachable related source
(`Scc.Sem.transfer_typedAt`).

- `Typed p`: the guard.
- `SegJ.of_entry`: a guard fact at the entry that a segment needs only as a
  hypothesis (a fact about the entry's source, such as its operands being
  numbers) is discharged by the guard.

The rows that use the guard are `Spike.Lib.A64Typed` and
`Spike.Lib.X64Typed`.
-/
import Spike.Lib.Seg
import Scc.Sem.TypingRows

namespace Spike.Lib

open CoreLang CoreTerm
open Kraken.Promising

/-- **The typing guard**: the source control is well typed, with no type
arguments. -/
def Typed (p : Prog) (c : Ctl) : Prop := Scc.Sem.TypedAt p [] c.term c.env

namespace SegJ

variable {I : ISA} {J : Ctl → Prop} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide I}
  {P Q : Frag I}

/-- **A fact the guard gives at the entry**: if every guarded entry pair
gives `Φ`, a segment under the hypothesis `Φ` is a guarded segment. -/
theorem of_entry {Φ : Prop} (hΦ : ∀ s c, P s c → J c → Φ) (h : Φ → Seg p lbl ms P Q) : SegJ J p lbl ms P Q := by
  refine ⟨fun s c => P s c ∨ ∃ hφ : Φ, (h hφ).choose s c, fun s c hp => .inl hp, ?_⟩
  rintro s c (hp | ⟨hφ, hi⟩) hj
  · have hφ := hΦ s c hp hj
    exact ((h hφ).choose_spec.2 s c ((h hφ).choose_spec.1 s c hp)).mono fun s c h =>
      h.imp_left fun h => .inr ⟨hφ, h⟩
  · exact ((h hφ).choose_spec.2 s c hi).mono fun s c h => h.imp_left fun h => .inr ⟨hφ, h⟩

end SegJ

end Spike.Lib

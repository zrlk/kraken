/-
**Closed tails of certification steps**, ISA-free. `ClosedC A cs tid D`
says a predicate `D` of thread states is closed under the certification steps
(`ThreadStepC`) and no step changes the promise set: the shape a dead tail
invariant needs (the `hDt` premise of the hello1 correctness theorems, fed to
`prom_nil_of_closed`). `StepsTo A cs tid D E` relaxes the landing to `D ∨ E`;
`ClosedC.rel` chains a tail piece `D` in front of an already closed `E`, so a
tail is proved back to front.
-/
import Scc.Sem.Ext

namespace Spike.Lib

open Kraken Kraken.Promising
open Scc.Sem (CertSem ThreadStepC)

/-- **`D` is closed under the certification steps, keeping the promises.** -/
def ClosedC {I : ISA} (A : Arch) (cs : CertSem I) (tid : Nat) (D : I.State → Prop) : Prop :=
  ∀ p q : Thread I × Memory, D p.1.st → ThreadStepC A cs tid p q → D q.1.st ∧ q.1.prom = p.1.prom

/-- **A step from `D` lands in `D` or `E`, keeping the promises.** -/
def StepsTo {I : ISA} (A : Arch) (cs : CertSem I) (tid : Nat) (D E : I.State → Prop) : Prop :=
  ∀ p q : Thread I × Memory, D p.1.st → ThreadStepC A cs tid p q → (D q.1.st ∨ E q.1.st) ∧ q.1.prom = p.1.prom

namespace ClosedC

variable {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}

/-- Closed predicates are closed under union. -/
theorem union {D E : I.State → Prop} (hD : ClosedC A cs tid D) (hE : ClosedC A cs tid E) :
    ClosedC A cs tid (fun s => D s ∨ E s) := by
  rintro p q (h | h) hs
  · exact (hD p q h hs).imp_left Or.inl
  · exact (hE p q h hs).imp_left Or.inr

/-- **Back to front**: a piece `D` stepping into `D ∨ E` in front of a
closed `E` gives a closed `D ∨ E`. -/
theorem rel {D E : I.State → Prop} (h : StepsTo A cs tid D E) (hE : ClosedC A cs tid E) :
    ClosedC A cs tid (fun s => D s ∨ E s) := by
  rintro p q (hd | he) hs
  · exact h p q hd hs
  · exact (hE p q he hs).imp_left Or.inr

/-- Equivalent predicates are closed together. -/
theorem congr {D E : I.State → Prop} (hDE : ∀ s, D s ↔ E s) (hD : ClosedC A cs tid D) :
    ClosedC A cs tid E := by
  intro p q he hs
  obtain ⟨h1, h2⟩ := hD p q ((hDE _).mpr he) hs
  exact ⟨(hDE _).mp h1, h2⟩

/-- The empty predicate is closed. -/
theorem bot : ClosedC A cs tid (fun _ : I.State => False) := by
  intro _ _ h; exact h.elim

end ClosedC

namespace StepsTo

variable {I : ISA} {A : Arch} {cs : CertSem I} {tid : Nat}

/-- Widen the target. -/
theorem mono {D E E' : I.State → Prop} (h : StepsTo A cs tid D E) (hE : ∀ s, E s → E' s) :
    StepsTo A cs tid D E' := by
  intro p q hd hs
  obtain ⟨h1, h2⟩ := h p q hd hs
  exact ⟨h1.imp_right (hE _), h2⟩

/-- Pieces stepping into the same target combine. -/
theorem union {D D' E : I.State → Prop} (h : StepsTo A cs tid D E) (h' : StepsTo A cs tid D' E) :
    StepsTo A cs tid (fun s => D s ∨ D' s) E := by
  rintro p q (hd | hd) hs
  · obtain ⟨h1, h2⟩ := h p q hd hs
    exact ⟨h1.elim (fun x => Or.inl (Or.inl x)) Or.inr, h2⟩
  · obtain ⟨h1, h2⟩ := h' p q hd hs
    exact ⟨h1.elim (fun x => Or.inl (Or.inr x)) Or.inr, h2⟩

/-- A step that always lands in `E` (no self loop). -/
theorem of_into {D E : I.State → Prop}
    (h : ∀ p q : Thread I × Memory, D p.1.st → ThreadStepC A cs tid p q → E q.1.st ∧ q.1.prom = p.1.prom) :
    StepsTo A cs tid D E := fun p q hd hs => (h p q hd hs).imp_left Or.inr

end StepsTo

end Spike.Lib

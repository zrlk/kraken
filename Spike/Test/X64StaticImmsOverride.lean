import Spike.Test.Ret0ReleaseX64
import Scc.Test.ElfTest

/-!
# The release layout's override of `static` and `imms` is invisible to the target

`ret0_correct` concludes `CorrectE` at `{ Λ with static := fun _ => none, imms := immsOf main }`,
not at `Λ` itself. This file checks that the override changes nothing the
target (or the parts of `Correct` it fixes) reads: the loader, label
resolution, the code marks, `InLayout`, `Entry.Ok`, well-formedness and the
placement check are all the same at both layouts. The overridden fields are
read only by `Components` (the witness's `lbl_static` and `env_imm`), which
is existentially witnessed by the proof.
-/

namespace Spike.Test.X64StaticImmsOverride

open Scc.Sem

variable (Λ : Scc.Sem.Layout) (s : WeakMem.AllocLabel → Option Nat) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- The loader (with the kernel model's hooks, whose `init` sees the layout) reads neither field. -/
example (n : Nat) (E : Entry) (a : X64.Asm) :
    (X64.target (X64.kernel n) E).load a { Λ with static := s, imms := i } =
      (X64.target (X64.kernel n) E).load a Λ := rfl

/-- Nor does label resolution. -/
example (n : Nat) (E : Entry) (a : X64.Asm) (l : String) :
    (X64.target (X64.kernel n) E).resolve a { Λ with static := s, imms := i } l =
      (X64.target (X64.kernel n) E).resolve a Λ l := rfl

/-- So the code marks (sites and abort labels) are the same. -/
example (T : Target) (a : T.Asm) (hr : ∀ l, T.resolve a { Λ with static := s, imms := i } l = T.resolve a Λ l) :
    T.marks a { Λ with static := s, imms := i } = T.marks a Λ := by
  simp only [Target.marks, hr]

/-- No access outside the layout: the same regions. -/
example {M : ExtMachine} (t : M.Cfg) : InLayout { Λ with static := s, imms := i } t ↔ InLayout Λ t := Iff.rfl

/-- The admissible entry states are the same. -/
example (E : Entry) : E.Ok { Λ with static := s, imms := i } ↔ E.Ok Λ := Iff.rfl

/-- Well-formedness is the same. -/
example : Scc.Sem.Layout.WF { Λ with static := s, imms := i } ↔ Scc.Sem.Layout.WF Λ :=
  ⟨fun h => { h with }, fun h => { h with }⟩

/-- The placement check is the same (`placeOKAt_static`). -/
example (cfg : Scc.Cert.PlaceOK.Config) (o : Scc.Cert.PlaceOK.X64.Out) :
    Scc.Cert.PlaceOK.X64.placeOKAt cfg { Λ with static := s, imms := i } o =
      Scc.Cert.PlaceOK.X64.placeOKAt cfg Λ o := rfl

/-- The ELF reader already places no static label: `static := none` is the identity on its layouts. -/
example : { Scc.Test.Elf.x64.1 with static := fun _ => none } = Scc.Test.Elf.x64.1 := rfl

end Spike.Test.X64StaticImmsOverride

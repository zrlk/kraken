/-
**The Linux platform on x64** and `CorrectP` (scaffolding, see
`Scc/Sem/Platform.lean`).

- `linuxPlatform`: the kernel model's hooks (`kernel`), the target's load
  as boot, `Entry.Ok` as the admissible environments. Its `routines` is
  `[]`: **`linuxPlatform` makes no §3 claim yet**, and no theorem
  here presents an obligation as holding for it.
- `CorrectP P n`: `Correct` at `target (P.hooks n) E` for every admissible
  `E`.
- `correctE_eq_correctP`: `CorrectE n = CorrectP linuxPlatform n` by `rfl`
  (so `CorrectP` at the Linux platform is the release statement, not a
  weaker one); `CorrectE.toP` turns a `CorrectE` theorem into `CorrectP`
  form.
-/
import Scc.Sem.Platform
import Scc.Sem.CorrectEX64

namespace Scc.Sem.X64

open Kraken.Promising Kraken.Promising.X64

/-- **The Linux platform** (x64): the kernel model's hooks, the target's
load with `n` slots as boot, `Entry.Ok`; no routine specification yet (no
§3 claim). -/
def linuxPlatform : Platform isa Asm where
  X := Kernel.KState
  boot n E Λ a := (target (kernel n) E).load a Λ
  EnvOk := Entry.Ok
  routines := []
  hooks := kernel
  hooksX _ := rfl

/-- **Correctness on a platform** (x64): for every environment `E` the
platform admits for `Λ`, `Correct` at the target with the platform's hooks
(`n` slots) and entry state `E`. -/
def CorrectP (P : Platform isa Asm) (n : Nat) (S : SrcSem) (Λ : Layout) (B : Budget) (asm : Asm) : Prop :=
  ∀ E : Entry, P.EnvOk E Λ → Correct (target (P.hooks n) E) S Λ B asm

/-- **`CorrectE` is `CorrectP` at the Linux platform** (x64). -/
theorem correctE_eq_correctP (n : Nat) : CorrectE n = CorrectP linuxPlatform n := rfl

/-- A `CorrectE` statement in `CorrectP` form (x64). -/
theorem CorrectE.toP {n : Nat} {S : SrcSem} {Λ : Layout} {B : Budget} {asm : Asm} (h : CorrectE n S Λ B asm) :
    CorrectP linuxPlatform n S Λ B asm := h

/-- The Linux platform's boot is the target's load. -/
theorem linuxPlatform_boot (n : Nat) (E : Entry) (Λ : Layout) (a : Asm) :
    linuxPlatform.boot n E Λ a = (target (kernel n) E).load a Λ := rfl

end Scc.Sem.X64

/-- info: 'Scc.Sem.X64.correctE_eq_correctP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Scc.Sem.X64.correctE_eq_correctP

/-- info: 'Scc.Sem.X64.CorrectE.toP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Scc.Sem.X64.CorrectE.toP

/-- info: 'Scc.Sem.X64.linuxPlatform_boot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Scc.Sem.X64.linuxPlatform_boot

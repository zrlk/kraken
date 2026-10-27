/-
**The landings' segments with no landings** (AArch64; the twin of
`Spike/Lib/LowerX64/H1InNone.lean`): `H1InA` at the empty landing family
`El := fun … => False` holds at every instance and entry state, the
segment's invariant `False` (`h1InA_none`); so `In2A` follows from the
start's segment `H0InA` at that family alone (`in2A_ofH0None`).

The program's allocations need not be absent for `h1InA_none`: `H1InA`'s
hypotheses (`Reach`, a fresh label, `AllocLand`) never mention the program,
and only `El` is the segment's precondition. Absence matters for the start's
side: at `El := False` the starts `StartsSA … El` are `S0A`'s and the pairs
carrying their own segment over them alone,
so the start's segment `H0InA` gets nothing about the frame invariant at a
landing, and its allocator calls' `xa` (`landStk_hxa`) has no landing to
supply. A program with no `newBuf` makes no such call, and `H0InA` at the
empty family is its whole obligation.
-/
import Spike.Lib.LowerA64.Closed2AtA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

/-- **No landings, no landing segments**: `H1InA` at the empty landing
family, for every entry state `E` and write tail `Dt` (each segment's
invariant `False`). -/
theorem h1InA_none (E : Entry) (Dt : State → Prop) : H1InA h E (fun _ _ _ _ _ _ _ _ => False) Dt :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => ⟨fun _ _ _ => False, fun _ _ _ h => h, fun _ _ _ h => h.elim,
    fun _ _ _ h => h.elim⟩⟩

/-- **`In2A` from the start's segment at no landings** (`h1InA_none`): the
obligation of a program whose start's segment needs no landing (no
`newBuf`; see the module docstring). -/
theorem in2A_ofH0None {E : Entry} {Dt : State → Prop} (H0 : H0InA h E (fun _ _ _ _ _ _ _ _ => False) Dt) :
    In2A h E :=
  ⟨_, Dt, H0, h1InA_none h E Dt⟩

/-- info: 'Spike.Lib.LowerA64.h1InA_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h1InA_none

/-- info: 'Spike.Lib.LowerA64.in2A_ofH0None' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2A_ofH0None

end Spike.Lib.LowerA64

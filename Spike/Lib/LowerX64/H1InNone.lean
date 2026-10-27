/-
**The landings' segments with no landings** (x86-64): `H1In` at the
empty landing family `El := fun … => False` holds at every instance and
entry state, the segment's invariant `False` (`h1In_none`); so `In2X`
follows from the start's segment `H0In` at that family alone
(`in2X_ofH0None`).

The program's allocations need not be absent for `h1In_none`: `H1In`'s
hypotheses (`Reach`, a fresh label, `AllocLand`) never mention the program,
and only `El` is the segment's precondition. Absence matters for the start's
side: at `El := False` the starts `StartsSX … El` are `S0X`'s and the pairs
carrying their own segment over them alone,
so the start's segment `H0In` gets nothing about the frame invariant at a
landing, and its allocator calls' `xa` (`landStk_hxa`) has no landing to
supply. A program with no `newBuf` makes no such call, and `H0In` at the
empty family is its whole obligation.
-/
import Spike.Lib.LowerX64.Closed2At

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out} {p : Prog}
  (h : placeOKAt pcfg (lay2 Λ p) o = true)

/-- **No landings, no landing segments**: `H1In` at the empty landing
family, for every entry state `E` and write tail `Dt` (each segment's
invariant `False`). -/
theorem h1In_none (E : Entry) (Dt : State → Prop) : H1In h E (fun _ _ _ _ _ _ _ _ => False) Dt :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => ⟨fun _ _ _ => False, fun _ _ _ h => h, fun _ _ _ h => h.elim,
    fun _ _ _ h => h.elim⟩⟩

/-- **`In2X` from the start's segment at no landings** (`h1In_none`): the
obligation of a program whose start's segment needs no landing (no
`newBuf`; see the module docstring). -/
theorem in2X_ofH0None {E : Entry} {Dt : State → Prop} (H0 : H0In h E (fun _ _ _ _ _ _ _ _ => False) Dt) :
    In2X h E :=
  ⟨_, Dt, H0, h1In_none h E Dt⟩

/-- info: 'Spike.Lib.LowerX64.h1In_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms h1In_none

/-- info: 'Spike.Lib.LowerX64.in2X_ofH0None' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms in2X_ofH0None

end Spike.Lib.LowerX64

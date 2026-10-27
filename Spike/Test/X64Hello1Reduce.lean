/-
**`hello1`'s holes reduced** (x86-64): `Hello1Holes`
(`Spike/Test/X64Hello1Final.lean`) from the setup call's open premises
alone (`OpenP`: the fields `hwn`, `hAW`, `habA` of `SetupPre`). `main`'s
side is closed: `MainOpenU` by `hello1_mainPreUT`
(`Spike/Test/X64Hello1Main.lean`) at the write tail `fun _ => True` (so the
print and write aborts' tails hold trivially), its targets' check `MainTg` by
`hTg_of_tgOkB` at the decided `hello1_tgOkB`
(`Spike/Test/X64Hello1TgOk.lean`).

- `hello1_mainTg`: `MainTg` at every placement;
- `hello1_mainOpenU`: `MainOpenU` at every entry and placement;
- `hello1_holes_of`: `Hello1Holes` from `OpenP` at every entry and placement
  (the setup side by `openS_of_openP`, `Spike/Test/X64Hello1SetupOpenOf.lean`).
-/
import Spike.Test.X64Hello1Final
import Spike.Test.X64Hello1Main
import Spike.Test.X64Hello1TgOk
import Spike.Test.X64Hello1SetupOpenOf

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib (FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

/-- The program. -/
local notation "P1" => Spike.Test.Hello1MainSrc.hello1o

/-- `ld`'s layout of the linked executable. -/
local notation "Le" => Spike.Test.Hello1LinkedX64.Λe

variable {Λx : Scc.Sem.Layout}

set_option hygiene false in
/-- The layout of the generic lemmas: any layout at which the placement check passes (`h`). -/
local notation "Lg" => Λx

/-- The compiler's output for the program at the certificate's sizes and label offsets. -/
local notation "OX" =>
  Out.ofEmitted (Scc.Lower.X64.lowerAll SccCertificate.config P1) SccCertificate.sizes SccCertificate.labelOffs

/-- **`main`'s targets' check at every placement** (`hTg_of_tgOkB` at
`hello1_tgOkB`, the code predicate `CdCLE` itself). -/
theorem hello1_mainTg (h : placeOKAt SccCertificate.placeCfg (lay2 Lg P1) OX = true) : MainTg h :=
  hTg_of_tgOkB hello1_tgOkB (fun _ _ hc => hc) _

/-- **`main`'s call's open premises at every placement** (`hello1_mainPreUT`
at each choice of the bounds; the aborts' tails `fun _ => True`). -/
theorem hello1_mainOpenU (h : placeOKAt SccCertificate.placeCfg (lay2 Lg P1) OX = true) (E : Entry)
    (El : Lbl → Lsize → WeakMem.AllocLabel → Nat → Nat → FragS isa) : MainOpenU h E El (fun _ => True) :=
  fun _ _ _ _ _ _ _ _ _ hB J _ =>
    hello1_mainPreUT h hB J (fun _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) (hello1_mainTg h)

/-- **`hello1`'s holes from the setup call's remaining premises** (`OpenP`:
at every choice of the bounds and invariant, `SetupPre`'s `hwn`, `hAW`,
`habA`; the setup side by `openS_of_openP`, `main`'s by `hello1_mainOpenU`). -/
theorem hello1_holes_of
    (hP : ∀ E : Entry, E.Ok (lay2 Le P1) → ∀ h' : placeOKAt SccCertificate.placeCfg (lay2 Le P1) OX = true,
      OpenP h' Spike.Lib.LowerNode.hello1o_accepted2 E (fun _ _ _ _ _ _ _ _ => False) (fun _ => True)) :
    Hello1Holes :=
  fun E hE h' => ⟨openS_of_openP h' (hP E hE h'), hello1_mainOpenU h' E _⟩

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_mainTg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_mainTg

/-- info: 'Spike.Lib.LowerX64.hello1_mainOpenU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_mainOpenU

/-- info: 'Spike.Lib.LowerX64.hello1_holes_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hello1_holes_of

import Spike.Test.A64SccCorrect
import Spike.Test.A64Ret0Negative

/-!
# Release checks of the AArch64 compiler theorem at `ret0`'s certificate

`a64_scc_correct`/`a64_scc_correct_text` (`Spike/Lib/LowerA64/Correct.lean`)
instantiated at `ret0`'s generated certificate (`Spike/Test/A64SccCorrect.lean`)
is not vacuous, and does not apply to a corrupted listing.

**Positive witness** (release criterion 3(a); executed): the canonical
target loads the certificate's text `asm` at the theorem's layout
(`{ linkOf out.prog out.secs with imms := immsOf d }`), and the executed run
of the load exits with `42`, `main`'s result.

**Corrupted listing** (release criterion 3(b)): `asm'`, the certificate's
text with `wc_main`'s `movz x9, #40` made `movz x9, #41` (one instruction):
- executed: `asm'` does not parse to the certificate's program
  (`parsesTo asm' out.prog out.secs` is false), so `a64_scc_correct_text`'s
  parse premise fails on it; it parses to `corruptProg`
  (`Spike/Test/A64Ret0Negative.lean`) instead, and the run of its load exits
  with `43`;
- proved (kernel): the output with `corruptProg` in place of the program
  fails the placement check (`corrupt_not_placeOK`, by A9: the body no longer
  is the IR's), so `a64_scc_correct` has no instance at it.

The proved non-vacuity of the obligation itself (no `main` exit with `43`;
the corrupted program's `exit_group` reaches `SysOk (.exitGroup 43)`) is
`Spike/Test/A64Ret0Negative.lean`'s, at the hand instance. These run
witnesses rest on the executed parser and runner, of which no soundness
against the target's machine is proved.
-/

namespace Spike.Test.A64SccNegative

open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64Consumer (T)
open Spike.Lib.A64.Flow.Ret0.Inst (μ0)
open Spike.Test.A64Ret0Negative (corruptProg)

/-- The theorem's layout at `ret0`'s certificate. -/
def Λc : Scc.Sem.Layout :=
  { Scc.Cert.Link.A64.linkOf SccCertificate.out.prog SccCertificate.out.secs with
    imms := match SccCertificate.prog_src with
      | [d] => Spike.Lib.LowerNode.immsOf d
      | _ => fun _ _ _ => none }

/-- The executed run of a text's load at `Λc`. -/
def runAt (asm : String) : String :=
  match T.load asm Λc with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.run abi Arch.armv8 pcOf μ 400 0 { cfg := c }
    s!"out={repr r.outText} events={r.other} stop={r.stop}"
  | none => "load refused"

/-! ## The positive witness -/

-- The certificate's text parses to its program (`a64_scc_correct_text`'s premise holds).
#guard Scc.Cert.Link.A64.parsesTo SccCertificate.asm SccCertificate.out.prog SccCertificate.out.secs

-- The canonical target loads it at the theorem's layout.
#guard (T.load SccCertificate.asm Λc).isSome

/-- info: "out=\"\" events=[exit 42] stop=exited" -/
#guard_msgs in
#eval runAt SccCertificate.asm

/-! ## The corrupted listing -/

/-- The certificate's text with `wc_main`'s `movz x9, #40` made `movz x9, #41`. -/
def asm' : String := SccCertificate.asm.replace "movz x9, #40" "movz x9, #41"

-- Exactly one occurrence is changed.
#guard (SccCertificate.asm.splitOn "movz x9, #40").length == 2

-- **The parse premise fails**: `asm'` is not the certificate's program.
#guard !Scc.Cert.Link.A64.parsesTo asm' SccCertificate.out.prog SccCertificate.out.secs

-- It is `corruptProg`, the certificate's program with that one instruction changed.
#guard SccCertificate.out.prog == SccCode.ret0Prog
#guard Scc.Cert.Link.A64.parsesTo asm' corruptProg SccCertificate.out.secs

/-- info: "out=\"\" events=[exit 43] stop=exited" -/
#guard_msgs in
#eval runAt asm'

/-- The certificate's output with `corruptProg` as its program. -/
def corruptOut : Scc.Cert.PlaceOK.A64.Out := { SccCertificate.outLit with prog := corruptProg }

/-- A9 fails on the corrupted output: `wc_main`'s body is not the IR's. -/
theorem corrupt_a9 :
    Scc.Cert.PlaceOK.A64.a9 corruptOut (Scc.Cert.PlaceOK.A64.tablesOf Scc.Cert.PlaceOK.Config.canonical corruptOut) =
      false := by
  decide +kernel

/-- **The corrupted output fails the placement check**, so
`a64_scc_correct` (whose premise is `placeOK Config.canonical`) has no
instance at it. -/
theorem corrupt_not_placeOK : Scc.Cert.PlaceOK.A64.placeOK Scc.Cert.PlaceOK.Config.canonical corruptOut = false :=
  Scc.Cert.PlaceOK.A64.placeOK_eq_false_of_a9 corrupt_a9

/-- The certificate's own literal output passes A9 (the negative is the corruption's). -/
theorem cert_a9 :
    Scc.Cert.PlaceOK.A64.a9 SccCertificate.outLit
      (Scc.Cert.PlaceOK.A64.tablesOf Scc.Cert.PlaceOK.Config.canonical SccCertificate.outLit) = true := by
  decide +kernel

/--
info: 'Spike.Test.A64SccNegative.corrupt_not_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms corrupt_not_placeOK

end Spike.Test.A64SccNegative

import Spike.Test.X64SccCorrect
import Spike.Test.X64Ret0Negative
import Spike.Lib.LowerEnvImm

/-!
# Release checks of the x86-64 compiler theorem at `ret0`'s certificate

The x86-64 twin of `Spike/Test/A64SccNegative.lean`: the compiler theorem
(`x64_scc_correct`, `Spike/Lib/LowerX64/Correct.lean`) at `ret0`'s
generated certificate is not vacuous, and does not apply to a corrupted
listing.

**Positive witness** (release criterion 3(a); executed): the canonical
target loads the certificate's text (`⟨asm, sizes, labelOffs⟩`) at the
theorem's layout (`{ linkOf out.prog out.secs with imms := immsOf d }`), and
the executed run of the load exits with `42`, `main`'s result.

**Corrupted listing** (release criterion 3(b)): `asm'`, the certificate's
text with `wc_main`'s `movq $40, %rax` made `movq $41, %rax` (one
instruction of the same length):
- executed: `asm'` does not parse to the certificate's program
  (`parsesTo asm' out.prog out.secs` is false), so the text form's parse
  premise fails on it; it parses to `corruptCells`
  (`Spike/Test/X64Ret0Negative.lean`) instead, and the run of its load
  exits with `43`;
- proved (kernel): the output with `corruptCells` in place of the program
  fails the placement check (`corrupt_not_placeOK`, by A9: the body no
  longer is the IR's), so `x64_scc_correct` has no instance at it.

The proved non-vacuity of the obligation itself (no `main` exit with `43`;
the corrupted program's `exit_group` reaches `SysOk (.exitGroup 43)`) is
`Spike/Test/X64Ret0Negative.lean`'s, at the hand instance. These run
witnesses rest on the executed parser and runner, of which no soundness
against the target's machine is proved.
-/

namespace Spike.Test.X64SccNegative

open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.X64Consumer (T)
open Spike.Lib.X64.Flow.Ret0.Inst (μ0)
open Spike.Test.X64Ret0Negative (corruptCells)

/-- The certificate's text with its sizes and label offsets. -/
def asmC : Scc.Sem.X64.Asm := ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩

/-- The theorem's layout at `ret0`'s certificate. -/
def Λc : Scc.Sem.Layout :=
  { Scc.Cert.Link.X64.linkOf SccCertificate.out.prog SccCertificate.out.secs with
    imms := match SccCertificate.prog_src with
      | [d] => Spike.Lib.LowerNode.immsOf d
      | _ => fun _ _ _ => none }

/-- The executed run of a text's load at `Λc`. -/
def runAt (a : Scc.Sem.X64.Asm) : String :=
  match T.load a Λc with
  | some c =>
    let μ := Scc.Sem.Test.RunMarks.mk (μ0.site .take) (μ0.site .release) μ0.abortAt false
    let r := Scc.Sem.Test.run abi Arch.tso pcOf μ 400 0 { cfg := c }
    s!"out={repr r.outText} events={r.other} stop={r.stop}"
  | none => "load refused"

/-! ## The positive witness -/

-- The certificate's text parses to its program (the text form's premise holds).
#guard Scc.Cert.Link.X64.parsesTo asmC SccCertificate.out.prog SccCertificate.out.secs

-- The canonical target loads it at the theorem's layout.
#guard (T.load asmC Λc).isSome

/-- info: "out=\"\" events=[exit 42] stop=exited" -/
#guard_msgs in
#eval runAt asmC

/-! ## The corrupted listing -/

/-- The certificate's text with `wc_main`'s `movq $40, %rax` made `movq $41, %rax`. -/
def asm' : Scc.Sem.X64.Asm := { asmC with text := SccCertificate.asm.replace "movq $40, %rax" "movq $41, %rax" }

-- Exactly one occurrence is changed.
#guard (SccCertificate.asm.splitOn "movq $40, %rax").length == 2

-- **The parse premise fails**: `asm'` is not the certificate's program.
#guard !Scc.Cert.Link.X64.parsesTo asm' SccCertificate.out.prog SccCertificate.out.secs

-- It is `corruptCells`, the certificate's program with that one instruction changed.
#guard SccCertificate.out.prog == SccCode.ret0Cells
#guard Scc.Cert.Link.X64.parsesTo asm' corruptCells SccCertificate.out.secs

/-- info: "out=\"\" events=[exit 43] stop=exited" -/
#guard_msgs in
#eval runAt asm'

/-- The certificate's output with `corruptCells` as its program. -/
def corruptOut : Scc.Cert.PlaceOK.X64.Out := { SccCertificate.outLit with prog := corruptCells }

/-- A9 fails on the corrupted output: `wc_main`'s body is not the IR's. -/
theorem corrupt_a9 :
    Scc.Cert.PlaceOK.X64.a9 corruptOut (Scc.Cert.PlaceOK.X64.tablesOf Scc.Cert.PlaceOK.Config.canonical corruptOut) =
      false := by
  decide +kernel

/-- **The corrupted output fails the placement check**, so
`x64_scc_correct` (whose premise is `placeOK Config.canonical`) has no
instance at it. -/
theorem corrupt_not_placeOK : Scc.Cert.PlaceOK.X64.placeOK Scc.Cert.PlaceOK.Config.canonical corruptOut = false :=
  Scc.Cert.PlaceOK.X64.placeOK_eq_false_of_a9 corrupt_a9

/-- The certificate's own literal output passes A9 (the negative is the corruption's). -/
theorem cert_a9 :
    Scc.Cert.PlaceOK.X64.a9 SccCertificate.outLit
      (Scc.Cert.PlaceOK.X64.tablesOf Scc.Cert.PlaceOK.Config.canonical SccCertificate.outLit) = true := by
  decide +kernel

/--
info: 'Spike.Test.X64SccNegative.corrupt_not_placeOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms corrupt_not_placeOK

end Spike.Test.X64SccNegative

/-
Release-kind RMW smoke test: the per-directive phase-1 check with release-kind RMWs
(`dirs_phase1R`, `EnvG/A64LinkR.lean`) on code whose releases are RMWs
(`swpl`, `ldaddl`), which the plain `Phase1Tree` rejects. This checks shape only:
release-only RMWs cannot discharge `RmwOk` (`KNOWN_GAPS.md`, release-RMW limit 2).
-/
import Kraken.Promising.SLR.EnvG.A64LinkR
import Kraken.AArch64.Parser

namespace Kraken.Promising.AArch64.EnvG.RmwRelSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG
open Kraken.AArch64.Parser

/-- An unlock by release swap, then a release fetch-add. -/
def relRmws : Program := parseAArch64("
    mov w3, #0
    swpl w3, w2, [x0]
    mov w4, #1
    ldaddl w4, w5, [x1]
")

example [layout : _root_.Layout] (A : Arch) : DirsPhase1R A (layout relRmws) := by dirs_phase1R relRmws

/-- A release CAS (phase-1 limit 1: its operation fails when the comparison
fails). -/
def relCas : Program := parseAArch64("
    casal w3, w2, [x0]
")

set_option linter.unusedVariables false in
/-- `dirs_phase1R` rejects the release CAS. -/
example [layout : _root_.Layout] (A : Arch) : True := by
  fail_if_success have _h : DirsPhase1R A (layout relCas) := by dirs_phase1R relCas
  trivial

end Kraken.Promising.AArch64.EnvG.RmwRelSmoke

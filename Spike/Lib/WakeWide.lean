/-
**wake's program is in the one-word fragment** (`WakeObligations.hwide`):
the program the canonical loader parses from the listing (`textProgram`,
the parse being the trust boundary, `hpa`) is in `Scc.Cert.WideA64.wideIn`.

- `hwide_of`: from the parse (`hpa`) and the parsed program's `wideIn`;
- `hwide_of_placeOKAt`: the same from an output passing `placeOKAt`
  (its A4, `PlaceW.wideIn_of_placeW`), at the output's program;
- `hwide_code`: at the generated program data (`SccCode.wakeProg` of
  `SccCode.wakeAsm`, `SccCode.wake_wide`).
-/
import Scc.Cert.PlaceOKA64
import Spike.Lib.A64WakeCode
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeWide

open Kraken.Promising.AArch64 Scc.Sem.A64

/-- **`hwide` from the parse**: the listing parses to `prog0` (`hpa`), in
the one-word fragment. -/
theorem hwide_of {asm : String} {prog0 : Program} (hpa : textProgram asm = .ok prog0)
    (hw : Scc.Cert.WideA64.wideIn prog0 = true) :
    ∀ prog, (textProgram asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true := by
  intro prog h
  rw [hpa] at h
  cases h
  exact hw

/-- **`hwide` from `placeOKAt`**: the listing parses to the output's
program, which A4 puts in the one-word fragment. -/
theorem hwide_of_placeOKAt {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.A64.Out}
    (hp : PlaceW cfg Λ o) {asm : String} (hpa : textProgram asm = .ok o.prog) :
    ∀ prog, (textProgram asm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true :=
  hwide_of hpa (PlaceW.wideIn_of_placeW hp)

/-- **`hwide` at wake's generated program data**, given the loader's parse
of its listing (the trust boundary, checked by `#guard` there). -/
theorem hwide_code (hpa : textProgram SccCode.wakeAsm = .ok SccCode.wakeProg) :
    ∀ prog, (textProgram SccCode.wakeAsm).toOption = some prog → Scc.Cert.WideA64.wideIn prog = true :=
  hwide_of hpa SccCode.wake_wide

/-- info: 'Spike.Lib.WakeWide.hwide_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwide_code

/-- info: 'Spike.Lib.WakeWide.hwide_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwide_of_placeOKAt

end Spike.Lib.WakeWide

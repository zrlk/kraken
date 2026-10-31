/-
**wake's program is in the one-word fragment on x86-64**
(`X64WakeA64.WakeObligations.hwide`): the code cells the canonical x86-64
loader lays out from the listing (`cellsOf`, the parse being the trust
boundary, `hpa`) are in `Scc.Cert.WideX64.wideIn`. The x86-64 twin of
`Spike/Lib/WakeWide.lean` (same names, in `Spike.Lib.X64WakeWide`); `hwide` is stated on `cellsOf`
(texts are `Asm` records).

- `hwide_of`: from the parse (`hpa`) and the cells' `wideIn`;
- `hwide_of_placeOKAt`: the same from an output passing x86-64's
  `placeOKAt` A4 (`PlaceWX.wideIn_of_placeWX`), at the output's cells;
- `hwide_code`: at the generated data (`SccCode.wakeCells` of
  `SccCode.wakeAsm`, `SccCode.wake_wide`).
-/
import Spike.Lib.X64WakeCode
import Spike.Lib.X64PlaceW

namespace Spike.Lib.X64WakeWide

open Kraken.Promising.X64 Scc.Sem.X64

/-- **`hwide` from the parse**: the listing lays out to `cells0` (`hpa`), in
the one-word fragment. -/
theorem hwide_of {asm : Asm} {cells0 : List (Directive × Nat)} (hpa : cellsOf asm = some cells0)
    (hw : Scc.Cert.WideX64.wideIn (cells0.map (·.1)) = true) :
    ∀ cells, cellsOf asm = some cells → Scc.Cert.WideX64.wideIn (cells.map (·.1)) = true := by
  intro cells h
  rw [hpa] at h
  cases h
  exact hw

/-- **`hwide` from `placeOKAt`**: the listing lays out to the output's
cells, which A4 puts in the one-word fragment. -/
theorem hwide_of_placeOKAt {cfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {o : Scc.Cert.PlaceOK.X64.Out}
    (hp : Spike.Lib.PlaceWX cfg Λ o) {asm : Asm} (hpa : cellsOf asm = some o.prog) :
    ∀ cells, cellsOf asm = some cells → Scc.Cert.WideX64.wideIn (cells.map (·.1)) = true :=
  hwide_of hpa (Spike.Lib.PlaceWX.wideIn_of_placeWX hp)

/-- **`hwide` at wake's generated data**, given the loader's layout of its
listing (the trust boundary, checked by `#guard parsesTo` there). -/
theorem hwide_code (hpa : cellsOf SccCode.wakeAsm = some SccCode.wakeCells) :
    ∀ cells, cellsOf SccCode.wakeAsm = some cells → Scc.Cert.WideX64.wideIn (cells.map (·.1)) = true :=
  hwide_of hpa SccCode.wake_wide

/-- info: 'Spike.Lib.X64WakeWide.hwide_code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwide_code

/-- info: 'Spike.Lib.X64WakeWide.hwide_of_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hwide_of_placeOKAt

end Spike.Lib.X64WakeWide

/-
**A one-block `Accepted1` program's output has a bare tail**: its `main`
takes `Unit` (no setup block), so the placement data names `scc_rt_main`
without one (`placeDataOf`: `.bare` unless the entry is `EntryArg.setupTid`).
The tail depends only on the checked entry, so the twin for programs whose
`main` calls earlier functions follows the same way from their checked
program.

- `tail_bare_of_accepted1main`: the output of a successful lowering of a
  one-block `Accepted1` program has the tail `.bare`.
-/
import Spike.Lib.LowerA64.TailBare
import Scc.Lower.InvProg1

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK.A64

/-- **The output of a one-block `Accepted1` program has a bare tail**:
`main` takes `Unit`, so no setup block runs before it. -/
theorem tail_bare_of_accepted1main {cfg : Scc.Config} {d : Decl}
    (hd : Scc.Lower.Accepted1 [d] = true)
    {em : Scc.Lower.A64.Emitted} (hlow : Scc.Lower.A64.lowerAll? cfg [d] = .ok em) :
    (Out.ofEmitted (Scc.Lower.A64.lowerAll cfg [d])).place.tail = .bare := by
  have he : Scc.Lower.A64.lowerAll cfg [d] = em := by simp [Scc.Lower.A64.lowerAll, hlow]
  rw [he]
  unfold Scc.Lower.A64.lowerAll? at hlow
  cases hl : Scc.Lower.lowerIR cfg [d] with
  | error e => rw [hl] at hlow; cases hlow
  | ok l =>
    rw [hl] at hlow
    have hlow : Scc.Lower.A64.emitAll l = .ok em := hlow
    have hlo := (Scc.Lower.A64.emitAll_frames hlow).1
    have hc := lowerIR_checked hl
    rw [Scc.Lower.Inv.checkedOf_accepted1main hd] at hc
    have hc' := (Except.ok.inj hc).symm
    simp only [Out.ofEmitted, placeDataOf, hlo, hc']
    rfl

end Spike.Lib.LowerA64

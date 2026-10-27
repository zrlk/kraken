/-
**An `Accepted0` program's output has a bare tail**: its `main` takes
`Unit` (no setup block), so the placement data names `scc_rt_main` without
one (`placeDataOf`: `.bare` unless the entry is `EntryArg.setupTid`), and
A11 checks it at `bareMC` (`rtCodeOk_bare_of_placeOKAt`).

- `lowerIR_checked`: a lowering's checked program is `checkedOf`'s.
- `tail_bare_of_accepted0`: the output of a successful lowering of an
  `Accepted0` program has the tail `.bare`.
-/
import Scc.Cert.PlaceDataA64
import Scc.Lower.InvProg

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK.A64

/-- **A lowering's checked program** is `checkedOf`'s. -/
theorem lowerIR_checked {cfg : Scc.Config} {p : Prog} {l : Scc.Lower.Lowered}
    (h : Scc.Lower.lowerIR cfg p = .ok l) : Scc.Lower.checkedOf p = .ok l.checked := by
  unfold Scc.Lower.lowerIR at h
  cases hc : Scc.Lower.checkedOf p with
  | error e => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

/-- **The output of an `Accepted0` program has a bare tail**: `main` takes
`Unit`, so no setup block runs before it. -/
theorem tail_bare_of_accepted0 {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
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
    rw [Scc.Lower.Inv.checkedOf_accepted0 hd] at hc
    have hc' := (Except.ok.inj hc).symm
    simp only [Out.ofEmitted, placeDataOf, hlo, hc']
    rfl

end Spike.Lib.LowerA64

/-
**An `Accepted0` program's x86-64 output has a bare tail** (the twin of
`Spike/Lib/LowerA64/TailBare.lean`): its `main` takes `Unit` (no setup
block), so the placement data names `scc_rt_main` without one
(`placeDataOf`: `.bare` unless the entry is `EntryArg.setupTid`), at every
assembler's sizes and label offsets, and A11 checks it at `bareMC`
(`rtCodeOk_bare_of_placeOKAt`).

- `lowerIR_checked`: a lowering's checked program is `checkedOf`'s.
- `emitAll_low`: the x86-64 emission keeps the lowering.
- `tail_bare_of_checked`: the output of a successful lowering whose checked
  program's entry takes `Unit` has the tail `.bare`.
- `tail_bare_of_accepted0`: so does that of an `Accepted0` program.
-/
import Scc.Cert.PlaceDataX64
import Scc.Lower.InvProg

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.Cert.PlaceOK.X64

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

/-- **The x86-64 emission keeps the lowering.** -/
theorem emitAll_low {l : Scc.Lower.Lowered} {e : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.emitAll l = .ok e) :
    e.low = l := by
  unfold Scc.Lower.X64.emitAll at h
  cases hm : Scc.Emit.X64.emitItemsMaps l.ir with
  | error _ => rw [hm] at h; cases h
  | ok r =>
    rw [hm] at h
    cases h
    rfl

/-- The tail of a successful lowering's output is `.bare` when its checked
program's entry takes `Unit`. -/
theorem tail_bare_of_checked {cfg : Scc.Config} {p : Prog} {em : Scc.Lower.X64.Emitted}
    (hc : Scc.Lower.checkedOf p = .ok { prog := p, entry := ⟨.unit, true⟩, externs := [], adds := [] })
    (hlow : Scc.Lower.X64.lowerAll? cfg p = .ok em) (sizes : List Nat) (labelOffs : List (String × Nat)) :
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).place.tail = .bare := by
  have he : Scc.Lower.X64.lowerAll cfg p = em := by simp [Scc.Lower.X64.lowerAll, hlow]
  rw [he]
  unfold Scc.Lower.X64.lowerAll? at hlow
  cases hl : Scc.Lower.lowerIR cfg p with
  | error e => rw [hl] at hlow; cases hlow
  | ok l =>
    rw [hl] at hlow
    have hlow : Scc.Lower.X64.emitAll l = .ok em := hlow
    have hlo := emitAll_low hlow
    have hc' := lowerIR_checked hl
    rw [hc] at hc'
    have hc'' := (Except.ok.inj hc').symm
    simp only [Out.ofEmitted, placeDataOf, hlo, hc'']
    rfl

/-- **The x86-64 output of an `Accepted0` program has a bare tail**: `main`
takes `Unit`, so no setup block runs before it. -/
theorem tail_bare_of_accepted0 {cfg : Scc.Config} {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true)
    {em : Scc.Lower.X64.Emitted} (hlow : Scc.Lower.X64.lowerAll? cfg [d] = .ok em) (sizes : List Nat)
    (labelOffs : List (String × Nat)) :
    (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg [d]) sizes labelOffs).place.tail = .bare :=
  tail_bare_of_checked (Scc.Lower.Inv.checkedOf_accepted0 hd) hlow sizes labelOffs

end Spike.Lib.LowerX64

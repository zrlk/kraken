/-
**The counter's zeroed item of scc's output** (x86-64): `CtrZ`, a premise
of `Spike/Lib/Rt/X64ArenaOfPlaceOK.lean`, holds of every successful
lowering's output and so of every output passing `placeOKAt`. No layout
constant is involved.

- `secs_ofEmitted`: a successful emission's data sections are
  `Secs.ofProgram` of the lowered IR's data (`emitAll_secs`);
- `ctrZ_ofEmitted`: `lowerAll? cfg p = .ok e` gives `CtrZ (Out.ofEmitted e sizes labelOffs)`
  (`lowerIR_data`, `ctr_secs`);
- `ctrZ_ofPlaceOK`: an output `Out.ofEmitted (lowerAll cfg p) sizes labelOffs` passing
  `placeOKAt` satisfies `CtrZ`. Where `lowerAll?` fails, the output is empty
  and fails A11.
-/
import Spike.Lib.Rt.CtrZSecs
import Spike.Lib.Rt.X64ArenaOfPlaceOK
import Scc.Cert.PlaceDataX64

namespace Spike.Lib.X64.Rt

open Scc.Cert.PlaceOK.X64 (placeOKAt Out placeOKAt_eq_false_of_a11)

/-- **A successful emission's data sections** are `Secs.ofProgram` of its
IR's data. -/
theorem secs_ofEmitted {l : Scc.Lower.Lowered} {e : Scc.Lower.X64.Emitted} (h : Scc.Lower.X64.emitAll l = .ok e) :
    ∃ maps, e.secs = Scc.Emit.Data.Secs.ofProgram l.ir.data maps := by
  have hs := Scc.Lower.X64.emitAll_secs h
  unfold Scc.Emit.X64.dataSecs at hs
  simp only [bind, Except.bind, pure, Except.pure] at hs
  split at hs
  · cases hs
  · exact ⟨_, (Except.ok.inj hs).symm⟩

/-- **The counter's item is a zeroed word in every successful output**. -/
theorem ctrZ_ofEmitted {cfg : Scc.Config} {p : CoreTerm.Prog} {e : Scc.Lower.X64.Emitted} {sizes : List Nat}
    {labelOffs : List (String × Nat)}
    (h : Scc.Lower.X64.lowerAll? cfg p = .ok e) : CtrZ (Out.ofEmitted e sizes labelOffs) := by
  unfold Scc.Lower.X64.lowerAll? at h
  cases hl : Scc.Lower.lowerIR cfg p with
  | error _ => rw [hl] at h; cases h
  | ok l =>
    rw [hl] at h
    obtain ⟨maps, hs⟩ := secs_ofEmitted h
    have hd := Spike.Lib.Rt.lowerIR_data hl
    unfold CtrZ
    show ∃ its, (_, its) ∈ Scc.Cert.Link.symItems (e.secs.bss ++ e.secs.data) ∧ _
    rw [hs, hd]
    exact Spike.Lib.Rt.ctr_secs cfg.layout maps

set_option maxRecDepth 100000 in
/-- **The counter's item is a zeroed word in an output passing
`placeOKAt`**: the lowering succeeded (A11 fails on the empty output), so
`ctrZ_ofEmitted` applies. -/
theorem ctrZ_ofPlaceOK {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {cfg : Scc.Config}
    {p : CoreTerm.Prog} {sizes : List Nat} {labelOffs : List (String × Nat)}
    (h : placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true) :
    CtrZ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) := by
  cases he : Scc.Lower.X64.lowerAll? cfg p with
  | ok em =>
    have : Scc.Lower.X64.lowerAll cfg p = em := by simp [Scc.Lower.X64.lowerAll, he]
    rw [this]
    exact ctrZ_ofEmitted he
  | error _ =>
    unfold Scc.Lower.X64.lowerAll at h
    rw [he] at h
    have h0 : placeOKAt pcfg Λ (Out.ofEmitted (default : Scc.Lower.X64.Emitted) sizes labelOffs) = false :=
      placeOKAt_eq_false_of_a11 rfl
    exact absurd h (by rw [h0]; decide)

end Spike.Lib.X64.Rt

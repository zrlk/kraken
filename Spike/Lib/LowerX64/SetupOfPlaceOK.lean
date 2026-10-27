/-
**`scc_rt_main` after a setup block from `PlaceOK`** (x86-64): the twin of
`Spike/Lib/LowerA64/SetupOfPlaceOK.lean`. A11 at a `.setup` tail
(`setupOk_of_placeOKAt`) is unpacked to a number of setup words `sw < 6`
at which the runtime's code holds with `scc_rt_main` at `setupMC sw`
(`rtCodeOkS`), together with its phase facts (`rtPhOk` at `mainPhTabS`).
-/
import Scc.Cert.PlaceOKX64

namespace Scc.Cert.PlaceOK.X64

open Kraken
open Spike.Lib.X64.Rt (setupOk rtCodeOkS setupMC mainPhTabS)

/-- **The parts of `setupOk`**: some `sw < 6` with the runtime's code at
`setupMC sw` and `scc_rt_main`'s phase facts there. -/
theorem setupOk_parts {cells : List (Directive × Nat)} {lo : Nat} {Λ : Scc.Sem.Layout}
    (h : setupOk cells lo Λ = true) :
    ∃ sw < 6, rtCodeOkS cells (setupMC sw) = true ∧
      Rt.X64.rtPhOk lo cells Λ (mainPhTabS (setupMC sw)) = true := by
  unfold setupOk at h
  obtain ⟨sw, hsw, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at h
  exact ⟨sw, List.mem_range.mp hsw, h.1, h.2⟩

/-- **A11 at a `.setup` tail, unpacked**: for an output that passes
`placeOKAt` and whose tail has a setup block, there is some `sw < 6` with
the runtime's code at `setupMC sw` (`rtCodeOkS`) and `scc_rt_main`'s phase
facts at `mainPhTabS`, the code at `Λ.code.lo`. -/
theorem setupIn_of_placeOKAt {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out} (h : placeOKAt cfg Λ o = true)
    (hs : o.place.tail = .setup) :
    ∃ sw < 6, rtCodeOkS o.prog (setupMC sw) = true ∧
      Rt.X64.rtPhOk Λ.code.lo o.prog Λ (mainPhTabS (setupMC sw)) = true :=
  setupOk_parts (setupOk_of_placeOKAt h hs)

end Scc.Cert.PlaceOK.X64

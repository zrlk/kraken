/-
**`scc_rt_main` after a setup block from `PlaceOK`** (AArch64): A11 at a
`.setup` tail (`setupOk_of_placeOKAt`) unpacked to the number of setup words
`sw < 8` at which the runtime's code holds with `scc_rt_main` at
`setupMC sw` (`rtCodeOkS`) and its phase facts (`rtPhOk` at `mainPhTabS`).
-/
import Scc.Cert.PlaceOKA64

namespace Scc.Cert.PlaceOK.A64

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64.Rt (setupOk rtCodeOkS setupMC mainPhTabS)

/-- **The parts of `setupOk`**: some `sw < 8` with the runtime's code at
`setupMC sw` and `scc_rt_main`'s phase facts there. -/
theorem setupOk_parts {prog : List Directive} {lo : Nat} {Λ : Scc.Sem.Layout}
    (h : setupOk prog lo Λ = true) :
    ∃ sw < 8, rtCodeOkS prog (setupMC sw) = true ∧ Rt.A64.rtPhOk lo prog Λ (mainPhTabS (setupMC sw)) = true := by
  unfold setupOk at h
  obtain ⟨sw, hsw, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at h
  exact ⟨sw, List.mem_range.mp hsw, h.1, h.2⟩

/-- **A11 at a `.setup` tail, unpacked**: on an output passing `placeOKAt`
whose tail has a setup block, some `sw < 8` with the runtime's code at
`setupMC sw` (`rtCodeOkS`) and `scc_rt_main`'s phase facts at `mainPhTabS`,
the code at `Λ.code.lo`. -/
theorem setupIn_of_placeOKAt {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out} (h : placeOKAt cfg Λ o = true)
    (hs : o.place.tail = .setup) :
    ∃ sw < 8, rtCodeOkS o.prog (setupMC sw) = true ∧
      Rt.A64.rtPhOk Λ.code.lo o.prog Λ (mainPhTabS (setupMC sw)) = true :=
  setupOk_parts (setupOk_of_placeOKAt h hs)

end Scc.Cert.PlaceOK.A64

import Spike.Test.A64Hello1PlaceOKE
import Spike.Lib.LowerA64.SetupOfPlaceOK

/-!
# `hello1.w`'s `scc_rt_main` after its setup block, from `PlaceOK`

`setupIn_of_placeOKAt` (`Spike/Lib/LowerA64/SetupOfPlaceOK.lean`) applied to
`hello1_placeOK` (`Spike/Test/A64Hello1PlaceOKE.lean`): the runtime's code
at `setupMC sw` (`rtCodeOkS`) and `scc_rt_main`'s phase facts
(`mainPhTabS`) for some `sw < 8`, read off `PlaceOK` and not decided again.
The only decisions here are about the shape: the output's tail is `.setup`,
and `sw = 4` is the one count whose setup pass holds. Together they give
`hello1.w`'s facts at `setupMC 4`. The direct decisions
(`Spike/Test/A64Hello1PlaceOK.lean`, `Spike/Test/Hello1LinkedA64.lean`)
stay.
-/

namespace Spike.Test.A64Hello1SetupIn

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Test.A64Hello1PlaceOKE
open Spike.Lib.A64.Rt (rtCodeOkS setupMC mainPhTabS)

/-- `hello1.w`'s output has a setup block. -/
theorem hello1_tail : hello1O.place.tail = .setup := by
  rw [hello1_out_eq]; decide +kernel

/-- **`hello1.w`'s setup facts from `PlaceOK`**: some `sw < 8` with the
runtime's code at `setupMC sw` and `scc_rt_main`'s phase facts there, at
the static link. -/
theorem hello1_setupIn :
    ∃ sw < 8, rtCodeOkS hello1O.prog (setupMC sw) = true ∧
      Scc.Cert.Rt.A64.rtPhOk (tablesOf Config.canonical hello1O).Λ.code.lo hello1O.prog
        (tablesOf Config.canonical hello1O).Λ (mainPhTabS (setupMC sw)) = true :=
  setupOk_parts (setupOk_of_placeOK hello1_placeOK hello1_tail)

/-- Only four setup words pass the setup pass on `hello1.w`'s output. -/
theorem hello1_sw : ∀ sw < 8, rtCodeOkS hello1O.prog (setupMC sw) = true → sw = 4 := by
  rw [hello1_out_eq]; decide +kernel

/-- **`hello1.w`'s facts at `setupMC 4`**, from `PlaceOK`. -/
theorem hello1_setup4 :
    rtCodeOkS hello1O.prog (setupMC 4) = true ∧
      Scc.Cert.Rt.A64.rtPhOk (tablesOf Config.canonical hello1O).Λ.code.lo hello1O.prog
        (tablesOf Config.canonical hello1O).Λ (mainPhTabS (setupMC 4)) = true := by
  obtain ⟨sw, hsw, hc, hp⟩ := hello1_setupIn
  obtain rfl := hello1_sw sw hsw hc
  exact ⟨hc, hp⟩

/-- info: 'Spike.Test.A64Hello1SetupIn.hello1_setup4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello1_setup4

end Spike.Test.A64Hello1SetupIn

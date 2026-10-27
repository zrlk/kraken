/-
**The setup words `rtCodeOkS` fixes** (AArch64): the runtime's code after a
setup block holds at one `setupMC sw` at most (`rtCodeOkS_sw_unique`: the
marshalling block's label gap `2 sw + 2` to `.sp1`), so A11 at a `.setup`
tail holds at any `sw` the code passes (`setupIn_sw_eq`): a per-output
premise at the lowering's `setupWords2` (`valWords_setupWords2`) closes by
`decide` on a concrete output.
-/
import Spike.Lib.LowerA64.SetupOfPlaceOK
import Spike.Lib.SetupWords2

namespace Spike.Lib.A64.Rt

open Kraken Kraken.AArch64.Parser
open Scc.Cert.Rt.A64 (RtAll GapAt rtIn_sound labelGap)

/-- **At most one `sw` passes `rtCodeOkS`**: `scc_rt_main`'s `.sp0` group
puts `.sp1` after `2 sw + 2` instructions. -/
theorem rtCodeOkS_sw_unique {prog : List Directive} {a b : Nat} (ha : rtCodeOkS prog (setupMC a) = true)
    (hb : rtCodeOkS prog (setupMC b) = true) : a = b := by
  have gap : ∀ {n}, rtCodeOkS prog (setupMC n) = true →
      labelGap prog ".L1_scc_rt_main.sp0" ".L1_scc_rt_main.sp1" (2 * n + 2) = true := fun h => by
    have h := rtIn_sound h
    unfold rtCodeTabS at h
    exact (RtAll.append (RtAll.append (RtAll.append (RtAll.append h).1).1).1).2.2.2.2.2.2.2.2.1
  have ga := gap ha
  have gb := gap hb
  unfold labelGap at ga gb
  split at ga
  next i j hi hj =>
    rw [hi, hj] at gb
    simp only [Bool.and_eq_true, beq_iff_eq] at ga gb
    omega
  next => simp at ga

end Spike.Lib.A64.Rt

namespace Scc.Cert.PlaceOK.A64

open Kraken Kraken.AArch64.Parser
open Spike.Lib.A64.Rt (rtCodeOkS setupMC mainPhTabS rtCodeOkS_sw_unique)

/-- **A11 at a `.setup` tail at a given `sw`**: on an output passing
`placeOKAt` whose tail has a setup block, at any `n` with the runtime's code
at `setupMC n`, `n < 8` and `scc_rt_main`'s phase facts at `setupMC n`. -/
theorem setupIn_sw_eq {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out} (h : placeOKAt cfg Λ o = true)
    (hs : o.place.tail = .setup) {n : Nat} (hn : rtCodeOkS o.prog (setupMC n) = true) :
    n < 8 ∧ Rt.A64.rtPhOk Λ.code.lo o.prog Λ (mainPhTabS (setupMC n)) = true := by
  obtain ⟨sw, hsw, hc, hp⟩ := setupIn_of_placeOKAt h hs
  obtain rfl := rtCodeOkS_sw_unique hc hn
  exact ⟨hsw, hp⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.Rt.rtCodeOkS_sw_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtCodeOkS_sw_unique

/-- info: 'Scc.Cert.PlaceOK.A64.setupIn_sw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupIn_sw_eq

end Scc.Cert.PlaceOK.A64

/-
**The setup words `rtCodeOkS` fixes** (x86-64): the twin of
`Spike/Lib/LowerA64/SetupSw.lean`. The runtime's code after a setup block
holds at one `setupMC sw` at most (`rtCodeOkS_sw_unique`: the marshalling
block's label gap of `marshalSz sw` bytes to `.x3`), so A11 at a `.setup`
tail holds at any `sw` the code passes (`setupIn_sw_eq`).
-/
import Spike.Lib.LowerX64.SetupOfPlaceOK

namespace Spike.Lib.X64.Rt

open Kraken
open Scc.Cert.Rt.X64 (RtAll GapAt rtIn_sound labelGap labelGapB)

/-- **At most one `sw` passes `rtCodeOkS`**: `scc_rt_main`'s `.x2` group
puts `.x3` `marshalSz sw` bytes after it. -/
theorem rtCodeOkS_sw_unique {cells : List (Directive × Nat)} {a b : Nat}
    (ha : rtCodeOkS cells (setupMC a) = true) (hb : rtCodeOkS cells (setupMC b) = true) : a = b := by
  have gap : ∀ {n}, rtCodeOkS cells (setupMC n) = true →
      labelGapB cells ".Lscc_rt_main.x2" ".Lscc_rt_main.x3" (marshalSz n) = true := fun h => by
    have h := rtIn_sound h
    unfold rtCodeTabS at h
    exact (RtAll.append (RtAll.append (RtAll.append (RtAll.append h).1).1).1).2.2.2.2.2.2.2.2.1
  have ga := gap ha
  have gb := gap hb
  unfold labelGapB labelGap at ga gb
  split at ga
  next i j hi hj =>
    rw [hi, hj] at gb
    simp only [Bool.and_eq_true, beq_iff_eq] at ga gb
    have := ga.2.symm.trans gb.2
    simp only [marshalSz] at this
    omega
  next => simp at ga

end Spike.Lib.X64.Rt

namespace Scc.Cert.PlaceOK.X64

open Kraken
open Spike.Lib.X64.Rt (rtCodeOkS setupMC mainPhTabS rtCodeOkS_sw_unique)

/-- **A11 at a `.setup` tail at a given `sw`**: on an output passing
`placeOKAt` whose tail has a setup block, at any `n` with the runtime's code
at `setupMC n`, `n < 6` and `scc_rt_main`'s phase facts at `setupMC n`. -/
theorem setupIn_sw_eq {cfg : Config} {Λ : Scc.Sem.Layout} {o : Out} (h : placeOKAt cfg Λ o = true)
    (hs : o.place.tail = .setup) {n : Nat} (hn : rtCodeOkS o.prog (setupMC n) = true) :
    n < 6 ∧ Rt.X64.rtPhOk Λ.code.lo o.prog Λ (mainPhTabS (setupMC n)) = true := by
  obtain ⟨sw, hsw, hc, hp⟩ := setupIn_of_placeOKAt h hs
  obtain rfl := rtCodeOkS_sw_unique hc hn
  exact ⟨hsw, hp⟩

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.Rt.rtCodeOkS_sw_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rtCodeOkS_sw_unique

/-- info: 'Scc.Cert.PlaceOK.X64.setupIn_sw_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms setupIn_sw_eq

end Scc.Cert.PlaceOK.X64

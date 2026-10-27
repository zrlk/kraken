/-
**The setup block's tail and A11's code at the lowering's words** (AArch64;
the twin of `Spike/Lib/LowerX64/SetupTailOf.lean`): for an `Accepted2`
program with a setup block whose output passes `placeOKAt`, the placement
data names `scc_rt_main` after a setup block, and the runtime's code is at
`setupMC (setupWords2 p)`: `h0InA_of_setupFNP`'s `hs` and `hc` from the
placement check alone.

- `tail_setup_of_accepted2A`: the output's tail is `.setup` (`placeDataOf`:
  the checked entry `entry2 p` takes the setup block's result);
- `rtCodeOkS_setupWords2A`: A11's `sw` (`setupIn_of_placeOKAt`) is
  `setupWords2 p` (`sw_eq_setupWords2A`).
-/
import Spike.Lib.LowerA64.SetupSwA12A
import Spike.Lib.LowerA64.SetupOfPlaceOK

namespace Spike.Lib.LowerA64

open Spike.Lib.A64.Rt (rtCodeOkS setupMC)

/-- **The output of an `Accepted2` program with a setup block has a
`.setup` tail**: its checked entry is `entry2 p`, which takes the setup
block's result. -/
theorem tail_setup_of_accepted2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
      = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) :
    (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).place.tail = .setup := by
  obtain ⟨em, hem⟩ := lowerAll?_ok_of_placeOKC h
  obtain ⟨-, -, -, -, hc, -, -⟩ := Spike.Lib.LowerNode.lowerAll_accepted2_a64 cfg hp hem
  have he : Spike.Lib.LowerNode.entry2 p = ⟨.setupTid, true⟩ := by simp [Spike.Lib.LowerNode.entry2, hs]
  simp only [Scc.Cert.PlaceOK.A64.Out.ofEmitted, Scc.Cert.PlaceOK.A64.placeDataOf, hc,
    Spike.Lib.LowerNode.checked2, he]
  rfl

/-- **A11's code at the lowering's setup words**: the runtime's code is at
`setupMC (setupWords2 p)` (A11 at the `.setup` tail gives some `sw`, which
is `setupWords2 p`). -/
theorem rtCodeOkS_setupWords2A {cfg : Scc.Config} {pcfg : Scc.Cert.PlaceOK.Config} {p : CoreTerm.Prog}
    {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.PlaceOK.A64.placeOKAt pcfg Λ (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p))
      = true)
    (hp : Scc.Lower.Accepted2 p = true) (hs : (Scc.Lower.setupOf p).isSome = true) :
    rtCodeOkS (Scc.Cert.PlaceOK.A64.Out.ofEmitted (Scc.Lower.A64.lowerAll cfg p)).prog
      (setupMC (Spike.Lib.LowerNode.setupWords2 p)) = true := by
  obtain ⟨sw, -, hc, -⟩ := Scc.Cert.PlaceOK.A64.setupIn_of_placeOKAt h (tail_setup_of_accepted2A h hp hs)
  rwa [sw_eq_setupWords2A h hp hs hc]

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.tail_setup_of_accepted2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.tail_setup_of_accepted2A

/-- info: 'Spike.Lib.LowerA64.rtCodeOkS_setupWords2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.rtCodeOkS_setupWords2A

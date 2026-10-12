import Kraken.X64.Examples.Sbr.Dsp.NegOdd64
import Kraken.X64.Examples.Sbr.Dsp.Sum64x5
import Kraken.X64.Examples.Sbr.Dsp.SumSquare
import Kraken.X64.Examples.Sbr.Dsp.QmfPreShuffle
import Kraken.X64.Examples.Sbr.Dsp.QmfPostShuffle
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintNeg
import Kraken.X64.Examples.Sbr.Dsp.QmfDeintBfly
import Kraken.X64.Examples.Sbr.Dsp.Autocorrelate
import Kraken.X64.Examples.Sbr.Dsp.HfGen
import Kraken.X64.Examples.Sbr.Dsp.HfGFilt
import Kraken.X64.Examples.Sbr.Dsp.HfApplyNoise

/-!
# `ff_aac_sbr_apply`: the `SBRDSPContext` routines together

`SbrDspSpecs` (`Spec.lean`) from the eleven leaf proofs in `Dsp/`. Each proof
assumes its routine's code is placed in the ambient code; `SbrDspPlaced`
collects those assumptions, which linking discharges from the layout of the
object (`libavcodec/x86/sbrdsp.asm`).
-/

open Kraken

namespace Kraken.Examples.Sbr

variable [CodeEnv]

/-- The code of every routine, as its proof states it, placed in the ambient
code. `hf_apply_noise_k`'s four entries and `apply_noise_main` are one
program, as in the object. -/
def SbrDspPlaced : Prop :=
  Program.PlacedIn NegOdd64.body ∧ Program.PlacedIn Sum64x5.body
    ∧ Program.PlacedIn SumSquare.body ∧ Program.PlacedIn QmfPreShuffle.body
    ∧ Program.PlacedIn QmfPostShuffle.body ∧ Program.PlacedIn QmfDeintNeg.body
    ∧ Program.PlacedIn QmfDeintBfly.body ∧ Program.PlacedIn Autocorrelate.body
    ∧ Program.PlacedIn Autocorrelate.body3 ∧ Program.PlacedIn HfGen.body
    ∧ Program.PlacedIn HfGFilt.body ∧ Program.PlacedIn HfApplyNoise.body

theorem sbrDspSpecs (h : SbrDspPlaced) : SbrDspSpecs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  exact ⟨NegOdd64.spec h1, Sum64x5.spec h2, SumSquare.spec h3, QmfPreShuffle.spec h4,
    QmfPostShuffle.spec h5, QmfDeintNeg.spec h6, QmfDeintBfly.spec h7,
    Autocorrelate.spec_sse h8, Autocorrelate.spec_sse3 h9, HfGen.spec h10, HfGFilt.spec h11,
    HfApplyNoise.spec h12⟩

end Kraken.Examples.Sbr

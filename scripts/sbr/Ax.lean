-- #print axioms of the final theorem, every ProcSpec theorem and the witnesses (run by ci.sh;
-- the output must equal baseline/axioms.txt).
import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.Witness
import Kraken.X64.Examples.Sbr.Linked
open Kraken.Examples.Sbr
#print axioms ff_aac_sbr_apply_linked
#print axioms applyCallees_of_link
#print axioms abortSpec_holds
#print axioms sbrDspSpecs
#print axioms vectorFmulSpec_of
#print axioms vectorFmulAddSpec_of
#print axioms vectorFmulRevSpec_of
#print axioms VectorFmul.specSse
#print axioms VectorFmul.specAvx
#print axioms VectorFmulAdd.specSse
#print axioms VectorFmulAdd.specAvx
#print axioms VectorFmulAdd.specFma3
#print axioms VectorFmulRev.specSse
#print axioms VectorFmulRev.specAvx
#print axioms VectorFmulRev.specAvx2
#print axioms Apply.spec
#print axioms LfGen.spec
#print axioms XGen.spec
#print axioms HfInverseFilter.spec
#print axioms HfAssemble.spec
#print axioms QmfSynthesis.spec
#print axioms NegOdd64.spec
#print axioms Sum64x5.spec
#print axioms SumSquare.spec
#print axioms QmfPreShuffle.spec
#print axioms QmfPostShuffle.spec
#print axioms QmfDeintNeg.spec
#print axioms QmfDeintBfly.spec
#print axioms Autocorrelate.spec_sse
#print axioms Autocorrelate.spec_sse3
#print axioms HfGen.spec
#print axioms HfGFilt.spec
#print axioms HfApplyNoise.spec
#print axioms Kraken.F32.dequantFloatModel_holds
#print axioms Kraken.Examples.Sbr.Witness.apply_pre_sat_sce
#print axioms Kraken.Examples.Sbr.Witness.apply_pre_sat_ps
#print axioms Kraken.Examples.Sbr.Witness.apply_pre_sat_cpe
#print axioms Kraken.Examples.Sbr.Witness.apply_pre_sat_a3
#print axioms Kraken.Examples.Sbr.Linked.linked_hyps_sat_sce
#print axioms Kraken.Examples.Sbr.Linked.linked_hyps_sat_ps
#print axioms Kraken.Examples.Sbr.Linked.linked_hyps_sat_cpe
#print axioms Kraken.Examples.Sbr.Linked.linked_hyps_sat_a3

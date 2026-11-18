-- #print axioms of the final theorems, every ProcSpec theorem, the witnesses and the
-- per-procedure theorems of SessionBin/Api.lean with their satisfiability witnesses (run by ci.sh;
-- the output must equal baseline/axioms.txt).
import Kraken.X64.Examples.Sbr.Link
import Kraken.X64.Examples.Sbr.Witness
import Kraken.X64.Examples.Sbr.Linked
import Kraken.X64.Examples.Sbr.Parse.GridAsm
import Kraken.X64.Examples.Sbr.Parse.HdrProc
import Kraken.X64.Examples.Sbr.Parse.InvfProc
import Kraken.X64.Examples.Sbr.Parse.DtdfProc
import Kraken.X64.Examples.Sbr.Parse.NoiseProc
import Kraken.X64.Examples.Sbr.Parse.EnvProc
import Kraken.X64.Examples.Sbr.Parse.TlimProc
import Kraken.X64.Examples.Sbr.Parse.PsEntry
import Kraken.X64.Examples.Sbr.Parse.ResetProc
import Kraken.X64.Examples.Sbr.Parse.UsacAsm
import Kraken.X64.Examples.Sbr.Parse.DecExtAll
import Kraken.X64.Examples.Sbr.SessionBin.Main
import Kraken.X64.Examples.Sbr.Parse.VlcWit
import Kraken.X64.Examples.Sbr.Parse.GridJtWit
import Kraken.X64.Examples.Sbr.SessionBin.SInit
import Kraken.X64.Examples.Sbr.SessionBin.InitSafe
import Kraken.X64.Examples.Sbr.SessionBin.Top
import Kraken.X64.Examples.Sbr.SessionBin.Api
import Kraken.X64.Examples.Sbr.SessionBin.Witness
import Kraken.X64.Examples.Sbr.SessionBin.WitAnother
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
#print axioms Kraken.Examples.Sbr.Grid.spec
#print axioms Kraken.Examples.Sbr.Hdr.spec
#print axioms Kraken.Examples.Sbr.Invf.spec
#print axioms Kraken.Examples.Sbr.Dtdf.dtdf_spec
#print axioms Kraken.Examples.Sbr.Noise.spec
#print axioms Kraken.Examples.Sbr.Env.read_sbr_envelope_spec
#print axioms Kraken.Examples.Sbr.Tlim.spec
#print axioms Kraken.Examples.Sbr.Ps.spec
#print axioms Kraken.Examples.Sbr.Reset.spec
#print axioms Kraken.Examples.Sbr.Usac.usacSpec_holds
#print axioms Kraken.Examples.Sbr.Usac.configSpec_holds
#print axioms Kraken.Examples.Sbr.DecExt.decExtSpec_holds
#print axioms Kraken.Examples.Sbr.SessionBin.sreach_init_inv
#print axioms Kraken.Examples.Sbr.SessionBin.sreach_wf
#print axioms Kraken.Examples.Sbr.SessionBin.session_dec
#print axioms Kraken.Examples.Sbr.SessionBin.session_config
#print axioms Kraken.Examples.Sbr.SessionBin.session_apply
#print axioms Kraken.Examples.Sbr.SessionBin.session_usac
#print axioms Kraken.Examples.Sbr.VlcWit.vlcC_sbr
#print axioms Kraken.Examples.Sbr.VlcWit.vlcC_ps
#print axioms Kraken.Examples.Sbr.GridJtWit.grid_layout_sat
#print axioms Kraken.Examples.Sbr.Init.spec
#print axioms Kraken.Examples.Sbr.Init.init_sessW
#print axioms Kraken.Examples.Sbr.Init.sbrSlots_envOf
#print axioms Kraken.Examples.Sbr.SessionBin.session_init
#print axioms Kraken.Examples.Sbr.SessionBin.init_safe
#print axioms Kraken.Examples.Sbr.SessionBin.sbr_session_safe
#print axioms Kraken.Examples.Sbr.SessionBin.SbrReady.initialized
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_ctx_alloc_init_spec
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_decode_extension_spec
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_decode_usac_data_spec
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_config_usac_spec
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_apply_spec
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_apply_only_its_regions
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_apply_keeps_the_rest
#print axioms Kraken.Examples.Sbr.SessionBin.sbrInitialized_split
#print axioms Kraken.Examples.Sbr.SessionBin.sbrReady_split
#print axioms Kraken.Examples.Sbr.SessionBin.sbr_switch_element
#print axioms Kraken.Examples.Sbr.SessionBin.sbr_switch_element_ready
#print axioms Kraken.Examples.Sbr.SessionBin.sbr_switch_ready
#print axioms Kraken.Examples.Sbr.SessionBin.sbr_switch_from_ready
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_ctx_alloc_init_another_spec
#print axioms Kraken.Examples.Sbr.SessionBin.ff_aac_sbr_ctx_alloc_init_another_ready_spec
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_init
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_decode
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_usac
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_config
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_apply
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_session
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_init_success
#print axioms Kraken.Examples.Sbr.SessionBin.Wit.wit_init_another

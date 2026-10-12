import Kraken.X64.PrintIntel
import Kraken.X64.Examples.Sbr.Dsp
import Kraken.X64.Examples.Sbr.FloatDsp
import Kraken.X64.Examples.Sbr.QmfSynthesis
import Kraken.X64.Examples.Sbr.LfGen
import Kraken.X64.Examples.Sbr.HfInverseFilter
import Kraken.X64.Examples.Sbr.XGen
import Kraken.X64.Examples.Sbr.HfAssemble
import Kraken.X64.Examples.Sbr.ApplyTable

/-! Translation validation, step 1: print the elaborated `Program` terms that the
final theorems mention (one directive per line, Intel syntax via
`Kraken/X64/PrintIntel.lean`). Also prints Lean's `Repr` of each directive on the
same line after ` ;; ` so that the comparison script can see the term structure
(widths, address size). Output dir: `$SBR_TV_LEANDIR` (set by `tv.sh`). -/

open Kraken.Examples.Sbr

def progs : List (String × Program) :=
  [ ("ff_sbr_neg_odd_64_sse", NegOdd64.body)
  , ("ff_sbr_sum64x5_sse", Sum64x5.body)
  , ("ff_sbr_sum_square_sse", SumSquare.body)
  , ("ff_sbr_qmf_pre_shuffle_sse2", QmfPreShuffle.body)
  , ("ff_sbr_qmf_post_shuffle_sse", QmfPostShuffle.body)
  , ("ff_sbr_qmf_deint_neg_sse", QmfDeintNeg.body)
  , ("ff_sbr_qmf_deint_bfly_sse2", QmfDeintBfly.body)
  , ("ff_sbr_autocorrelate_sse", Autocorrelate.body)
  , ("ff_sbr_autocorrelate_sse3", Autocorrelate.body3)
  , ("ff_sbr_hf_gen_sse", HfGen.body)
  , ("ff_sbr_hf_g_filt_sse", HfGFilt.body)
  , ("ff_sbr_hf_apply_noise", HfApplyNoise.body)
  , ("ff_vector_fmul_sse", VectorFmul.bodySse)
  , ("ff_vector_fmul_avx", VectorFmul.bodyAvx)
  , ("ff_vector_fmul_add_sse", VectorFmulAdd.bodySse)
  , ("ff_vector_fmul_add_avx", VectorFmulAdd.bodyAvx)
  , ("ff_vector_fmul_add_fma3", VectorFmulAdd.bodyFma3)
  , ("ff_vector_fmul_reverse_sse", VectorFmulRev.bodySse)
  , ("ff_vector_fmul_reverse_avx", VectorFmulRev.bodyAvx)
  , ("ff_vector_fmul_reverse_avx2", VectorFmulRev.bodyAvx2)
  , ("sbr_qmf_synthesis", QmfSynthesis.body)
  , ("sbr_lf_gen", LfGen.body)
  , ("sbr_hf_inverse_filter", HfInverseFilter.body)
  , ("sbr_x_gen", XGen.body)
  , ("sbr_hf_assemble", HfAssemble.body)
  , ("ff_aac_sbr_apply", Apply.body) ]

def dirLine (d : Directive) : String :=
  match d with
  | .label l => s!"{l}:"
  | .instr i =>
    let (aw, ow) : String × String := match i with
      | .regular a o _ => (toString a, toString o)
      | .avx a o _ => (toString a, toString o)
    s!"    {toString d} ;; aw={aw} ow={ow}"
  | .byteArray _ => s!"    {toString d}"

def main : IO Unit := do
  let some dir ← IO.getEnv "SBR_TV_LEANDIR"
    | throw (IO.userError "Export.lean: SBR_TV_LEANDIR is not set (run it through tv.sh)")
  IO.FS.createDirAll dir
  for (n, p) in progs do
    let txt := "\n".intercalate (p.map dirLine) ++ "\n"
    IO.FS.writeFile s!"{dir}/{n}.txt" txt
    IO.println s!"{n}: {p.length} directives"

#eval main

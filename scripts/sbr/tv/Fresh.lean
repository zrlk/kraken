import Lake
/-! Was each olean built from the current source text? Compares the source hash
recorded in the module's Lake trace with Lake's hash of the file now. Prints
`FRESH <file>` or `STALE <file>`. -/

def files : List String :=
  [ "Kraken/X64/Syntax.lean", "Kraken/X64/Parser.lean", "Kraken/X64/PrintIntel.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/NegOdd64.lean", "Kraken/X64/Examples/Sbr/Dsp/Sum64x5.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/SumSquare.lean", "Kraken/X64/Examples/Sbr/Dsp/QmfPreShuffle.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/QmfPostShuffle.lean", "Kraken/X64/Examples/Sbr/Dsp/QmfDeintNeg.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/QmfDeintBfly.lean", "Kraken/X64/Examples/Sbr/Dsp/Autocorrelate.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/HfGen.lean", "Kraken/X64/Examples/Sbr/Dsp/HfGFilt.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/HfApplyNoise.lean", "Kraken/X64/Examples/Sbr/Dsp.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/FloatDspCommon.lean", "Kraken/X64/Examples/Sbr/Dsp/VectorFmul.lean"
  , "Kraken/X64/Examples/Sbr/Dsp/VectorFmulAdd.lean", "Kraken/X64/Examples/Sbr/Dsp/VectorFmulRev.lean"
  , "Kraken/X64/Examples/Sbr/FloatDsp.lean"
  , "Kraken/X64/Examples/Sbr/QmfSynthesis.lean", "Kraken/X64/Examples/Sbr/LfGen.lean"
  , "Kraken/X64/Examples/Sbr/HfInverseFilter.lean", "Kraken/X64/Examples/Sbr/XGen.lean"
  , "Kraken/X64/Examples/Sbr/HfAssemble/Cells.lean"
  , "Kraken/X64/Examples/Sbr/HfAssemble/Base.lean", "Kraken/X64/Examples/Sbr/HfAssemble/Part1.lean"
  , "Kraken/X64/Examples/Sbr/HfAssemble/Part2.lean"
  , "Kraken/X64/Examples/Sbr/HfAssemble.lean", "Kraken/X64/Examples/Sbr/ApplySpec.lean"
  , "Kraken/X64/Examples/Sbr/ApplyTable.lean"
  , "Kraken/X64/Examples/Sbr/Apply.lean" ]

def main : IO Unit := do
  let root ← IO.currentDir
  for f in files do
    let trace := s!".lake/build/lib/lean/{(f.splitOn ".lean").head!}.trace"
    let h ← Lake.computeTextFileHash f
    let t ← IO.FS.readFile trace
    -- the trace lists `["<abs path of source>", "<hash>"]`
    let key := s!"\"{h}\""
    -- (the recorded absolute path may be another checkout's)
    let _ := root
    if (t.splitOn key).length > 1 && (t.splitOn s!"/{f}\"").length > 1 then IO.println s!"FRESH {f} {h}"
    else IO.println s!"STALE {f} (source hash now {h})"

#eval main

import Scc.Cert.PlaceDataA64
import Scc.Test.Src
import Spike.Lib.Ret0Src
import Spike.Lib.A64Ret0Code
import Spike.Lib.A64Hello1Code
import Spike.Test.A64Ret0Offs

/-!
# The computed AArch64 placement data against `scc --code`'s

`Scc.Cert.PlaceOK.A64.placeDataOf` on `lowerAll`'s output for `ret0.w` and
`hello1.w`: its block table is the one `scc --code` writes (`ret0T`,
`hello1T`) with the offsets `Scc.Cert.Blocks.offsA64` gives its blocks
(`ret0Offs`, `hello1Offs`), row by row, with the single instructions
`ret0Evs` (`hello1Evs`) checked by A3's coverage; its stack need table is
`ret0Need` (`hello1Need`); `scc_rt_main`'s tail is bare for `ret0.w` and
after a setup block for `hello1.w`.
-/

namespace Spike.Test.A64PlaceData

open Scc.Cert.PlaceOK.A64 Scc.Cert.Rt.A64

/-- Two tables with their offsets are the same: labels, rows (place,
region, offsets, instructions), single instructions, group by group. -/
def sameGrps : List OGrp → List OGrp → Bool
  | [], [] => true
  | g :: gs, h :: hs =>
    g.l == h.l && g.ev == h.ev && g.bs.length == h.bs.length && (g.bs.zip h.bs).all (fun p => p.1.eqb p.2) &&
      sameGrps gs hs
  | _, _ => false

/-- `hello1.w` as the frontend reads it. -/
def hello1Src : CoreTerm.Prog :=
  match Scc.Frontend.run (w_src% "Scc/Test/hello1.w") with
  | .ok c => c.prog
  | .error _ => []

/-- The placement data of `ret0.w`. -/
def ret0D : PlaceData := placeDataOf (Scc.Lower.A64.lowerAll { arch := .arm } Spike.Lib.Ret0Src.ret0Src)

/-- The placement data of `hello1.w`. -/
def hello1D : PlaceData := placeDataOf (Scc.Lower.A64.lowerAll { arch := .arm } hello1Src)

#guard !hello1Src.isEmpty

#guard sameGrps ret0D.blocks (withEvs (ofGrps SccCode.ret0T SccCode.ret0Offs) SccCode.ret0Evs)
#guard ret0D.blocks.length == 141
#guard ret0D.need == SccCode.ret0Need
#guard decide (ret0D.tail = .bare)

#guard sameGrps hello1D.blocks (withEvs (ofGrps SccCode.hello1T SccCode.hello1Offs) SccCode.hello1Evs)
#guard hello1D.blocks.length == 146
#guard hello1D.need == SccCode.hello1Need
#guard decide (hello1D.tail = .setup)

end Spike.Test.A64PlaceData

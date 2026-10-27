import Scc.Cert.PlaceDataX64
import Spike.Lib.Ret0Src
import Spike.Lib.X64Ret0Code
import Spike.Lib.X64Hello1Code
import Spike.Test.X64Ret0Offs
import Spike.Lib.Hello1Src

/-!
# The computed x86-64 placement data against `scc --code`'s

The x86-64 twin of `Spike/Test/A64PlaceData.lean`.
`Scc.Cert.PlaceOK.X64.Out.ofEmitted` on `lowerAll`'s output for `ret0.w` and
`hello1.w`, at the assembler's sizes and label offsets of `scc --code`'s
listings (`ret0Asm`, `hello1Asm`): its code cells are the canonical
loader's (`ret0Cells`, `hello1Cells`), its data sections the loader's; its
block table is the one `scc --code` writes (`ret0T`, `hello1T`) with the
offsets `Scc.Cert.Blocks.offsX64` gives its blocks (`ret0Offs`,
`hello1Offs`), row by row, with the single instructions `ret0Evs`
(`hello1Evs`) checked by A3's coverage; its stack need table is `ret0Need`
(`hello1Need`); `scc_rt_main`'s tail is bare for `ret0.w` and after a setup
block for `hello1.w`. `hello1.w`'s source program is the term
`Spike.Lib.Hello1Src.hello1Src` (checked there against the frontend).
-/

namespace Spike.Test.X64PlaceData

open Scc.Cert.PlaceOK.X64 Scc.Cert.Rt.X64

/-- Two tables with their offsets are the same: labels, rows (place,
region, offsets, cells), single instructions, group by group. -/
def sameGrps : List OGrp → List OGrp → Bool
  | [], [] => true
  | g :: gs, h :: hs =>
    g.l == h.l && g.ev == h.ev && g.bs.length == h.bs.length &&
      (g.bs.zip h.bs).all (fun (a, b) =>
        a.k == b.k && a.off == b.off && a.lo == b.lo && a.hi == b.hi && a.o.sp == b.o.sp &&
          a.o.regs == b.o.regs && a.blk == b.blk) &&
      sameGrps gs hs
  | _, _ => false

/-- scc's x86-64 output for `ret0.w` at `ret0Asm`'s sizes. -/
def ret0O : Out :=
  Out.ofEmitted (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Ret0Src.ret0Src)
    SccCode.ret0Asm.sizes SccCode.ret0Asm.labelOffs

/-- scc's x86-64 output for `hello1.w` at `hello1Asm`'s sizes. -/
def hello1O : Out :=
  Out.ofEmitted (Scc.Lower.X64.lowerAll { arch := .x64 } Spike.Lib.Hello1Src.hello1Src)
    SccCode.hello1Asm.sizes SccCode.hello1Asm.labelOffs

#guard ret0O.prog == SccCode.ret0Cells
#guard ret0O.secs == SccCode.ret0Secs
#guard sameGrps ret0O.place.blocks (withEvs (ofGrps SccCode.ret0T SccCode.ret0Offs) SccCode.ret0Evs)
#guard ret0O.place.need == SccCode.ret0Need
#guard decide (ret0O.place.tail = .bare)

#guard hello1O.prog == SccCode.hello1Cells
#guard hello1O.secs == SccCode.hello1Secs
#guard sameGrps hello1O.place.blocks (withEvs (ofGrps SccCode.hello1T SccCode.hello1Offs) SccCode.hello1Evs)
#guard hello1O.place.need == SccCode.hello1Need
#guard decide (hello1O.place.tail = .setup)

-- The computed placement data passes `PlaceOK` on `ret0.w` and on `hello1.w`
-- (A11 through its setup tail)
-- (evaluated; the kernel's decisions are `Spike/Test/X64Ret0PlaceOKE.lean`
-- and `Spike/Test/X64Hello1PlaceOKE.lean`).
#guard placeOK Scc.Cert.PlaceOK.Config.canonical ret0O
#guard placeOK Scc.Cert.PlaceOK.Config.canonical hello1O
#guard a11 hello1O (tablesOf Scc.Cert.PlaceOK.Config.canonical hello1O)

end Spike.Test.X64PlaceData

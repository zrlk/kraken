import Scc.Cert.X64
import Scc.Cert.OutStageX64
import Scc.Cert.SpawnX64
import Spike.Lib.X64HelloCode
import Spike.Lib.X64HelloSrc

/-!
# hello.w on x86-64: the output the placement checks read

`pcfgH` is hello's placement configuration (the canonical one with `helloNeed`'s budget and
the two thread entries) and `oH` hello's output as the placement checks read it: the program
is the listing's cells `SccCode.helloCells` and its sections `SccCode.helloSecs`
(`Spike/Lib/X64HelloCode.lean`, the loader's parse, the trust boundary), with the label
offsets `as` reported and the placement data (block table, tails, IR) of scc's lowering of
`helloSrc`, computed at elaboration time (`scc_lit%`, untrusted: every placement component
is decided on `oH` itself, so a wrong table only makes a check fail).

`oH.prog = SccCode.helloCells` and `oH.secs = SccCode.helloSecs` hold by `rfl`; that the
lowering's own cells are the listing's is checked by evaluation (`#guard`, documentation
only: no proof reads it).

Unlike AArch64 (`Spike.Lib.A64.HelloPh.RootLit.oH`, whose block table is empty because its
`PlaceW` drops A3/A5/A7/A9), the x86-64 placement facts `PlaceWX` carry all of A1–A9, so `oH`
carries the lowering's placement data. Unlike x86-64 wake (`SccCertificate.outLit`), `oH`
is not the certificate's: the root does not import `Spike.Test.Cert.X64HelloCert`.
-/

namespace Spike.Lib.X64.HelloPh.RootLit

set_option maxRecDepth 100000

/-- **hello's placement configuration**: the canonical one with `helloNeed`'s budget and the
thread entries (the certificate's `placeCfg`). -/
def pcfgH : Scc.Cert.PlaceOK.Config :=
  { Scc.Cert.PlaceOK.Config.canonical with needBudget := 12288, entries := ["scc_rt_main", "scc_rt_thr_worker"] }

/-- scc's configuration for hello.w on x86-64 (the certificate's `config`). -/
def configH : Scc.Config := ({ arch := .x64, host := .linux, gc := .none } : Scc.Config)

/-- scc's lowering of `helloSrc` as the placement checks read it, with the listing's sizes
and label offsets. -/
def outH : Scc.Cert.PlaceOK.X64.Out :=
  Scc.Cert.PlaceOK.X64.Out.ofEmitted (Scc.Lower.X64.lowerAll configH Spike.Lib.X64HelloSrc.helloSrc)
    SccCode.helloAsm.sizes SccCode.helloAsm.labelOffs

/-- `outH` as a literal (`scc_lit%`, computed at elaboration time, untrusted). -/
def outHLit : Scc.Cert.PlaceOK.X64.Out := scc_lit% outH

/-- **hello's output** as the placement checks read it: the listing's cells and sections, the
label offsets, and the lowering's placement data. -/
def oH : Scc.Cert.PlaceOK.X64.Out :=
  { prog := SccCode.helloCells, secs := SccCode.helloSecs, labelOffs := SccCode.helloAsm.labelOffs,
    place := outHLit.place }

-- The lowering's cells and sections are the listing's (evaluation, documentation only).
#guard outHLit.prog == SccCode.helloCells
#guard outHLit.secs.data == SccCode.helloSecs.data && outHLit.secs.bss == SccCode.helloSecs.bss &&
  outHLit.secs.rodata == SccCode.helloSecs.rodata

theorem oH_prog : oH.prog = SccCode.helloCells := rfl

theorem oH_secs : oH.secs = SccCode.helloSecs := rfl

end Spike.Lib.X64.HelloPh.RootLit

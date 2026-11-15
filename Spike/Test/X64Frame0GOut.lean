/-
**`frame0.w`'s output after the granule pass** (x86-64; untrusted, no new literal in a trusted
file): `Spike.Lib.X64GranuleOut` on the certificate's literals
(`Spike/Test/Cert/X64Frame0Cert.lean`), with the stage facts the post-pass compiler theorems take
(only the placement check at the post-pass layout is proved for this program).

The values are computed at elaboration time as literals (`scc_lit%`, untrusted). The pass's
items `finalLit` and the post-pass sizes and label offsets `sizesFLit`, `offsFLit` have no
kernel equation to the pass (the kernel does not reduce the pass's string handling): as in a
certificate, the items are tied to the certificate's by the pass check `hcF` (they need not be
the pass's output: "`granuleX64 ir items = .ok final` is tested, not proved",
`Scc/Cert/GranuleOutX64.lean`), and the sizes and offsets by the loader's check (A2) and the
parse of the text. The rest have kernel-checked equations:

- `csLit`, `blksLit`: the post-pass cells and block table, `hzF`, `hbF`;
- `hcF`: the pass check on the certificate's items;
- `oFLit` (`oF_eq`): the post-pass output.
-/
import Spike.Test.Cert.X64Frame0Cert
import Spike.Lib.X64GranuleOut

namespace Spike.Test.X64Frame0GOut

set_option maxRecDepth 100000

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64GranuleOut
open SccCertificate (loweredLit emittedLit tblLit titsLit)

/-- The pass's items on the certificate's emitted items. -/
def final : List Scc.Emit.X64.Item := postItems loweredLit.1 emittedLit.1
def finalLit : List Scc.Emit.X64.Item := scc_lit% final

def sizesF : List Nat := postSizes finalLit
def sizesFLit : List Nat := scc_lit% sizesF
def offsF : List (String × Nat) := postOffs finalLit
def offsFLit : List (String × Nat) := scc_lit% offsF

/-- The post-pass text. -/
def textF : String := postText finalLit titsLit

-- The literal items render as the pass's output does (evaluation, not a proof fact).
#guard textF == postText final titsLit

def cs : List (Directive × Nat) := postCells finalLit sizesFLit
def csLit : List (Directive × Nat) := scc_lit% cs

theorem hzF : (Scc.Cert.Granule.X64.textCells finalLit).bind (Kraken.Promising.X64.sizedCells · sizesFLit) =
    some csLit := by kernel_rfl

def blks : List Scc.Cert.Rt.X64.OGrp := postBlocks sizesFLit loweredLit.1 finalLit
def blksLit : List Scc.Cert.Rt.X64.OGrp := scc_lit% blks

theorem hbF : Scc.Cert.Granule.X64.blocksOfFinal sizesFLit loweredLit.1 finalLit = some blksLit := by
  kernel_rfl

/-- The pass check: the post-pass items expand the certificate's. -/
theorem hcF : Scc.Cert.Granule.X64.check finalLit emittedLit.1 = true := by kernel_rfl

/-- The stage `ofFinal` reads. -/
def stF : Stage := stageOf loweredLit emittedLit tblLit

/-- The post-pass output. -/
def oF : Out := Scc.Cert.Granule.X64.ofFinal sizesFLit offsFLit stF finalLit
def oFLit : Out := scc_lit% oF

theorem oF_eq : oF = oFLit := by
  have h : oF = Scc.Cert.Granule.X64.ofFinalB sizesFLit offsFLit stF finalLit blksLit :=
    Scc.Cert.Granule.X64.ofFinal_eq_B (sizes := sizesFLit) (labelOffs := offsFLit) (st := stF)
      (final := finalLit) hbF
  rw [h]
  kernel_rfl

end Spike.Test.X64Frame0GOut

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64Frame0GOut.oF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Frame0GOut.oF_eq

/-- info: 'Spike.Test.X64Frame0GOut.hcF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Frame0GOut.hcF


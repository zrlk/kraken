/-
**`ret0.w`'s output after the granule pass** (x86-64; untrusted, no new literal in a trusted
file): `Spike.Lib.X64GranuleOut` on the certificate's literals (`Spike/Test/Cert/X64Ret0Cert.lean`,
which both the default and the `lld` link use), with the stage facts the post-pass compiler
theorem takes (`x64_scc_correctE_text_closedAt_final`), and that theorem at the post-pass text,
`ret0_correctG`, at any layout at which the post-pass output passes the placement check.

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
import Spike.Test.Ret0ReleaseX64
import Spike.Lib.X64GranuleOut
import Spike.Lib.LowerX64.CorrectFinal

namespace Spike.Test.X64Ret0GOut

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

/-- **`ret0.w`'s text after the granule pass, compiled for x86-64, is correct at every
admissible entry state**, at any layout `Λ` at which the post-pass output passes the placement
check, given the loader's parse of the text, for every budget `B` and memory model `arch`. -/
theorem ret0_correctG (Λ : Scc.Sem.Layout) (B : Scc.Sem.Budget) (arch : WeakMem.Arch)
    (h : placeOKAt SccCertificate.placeCfg Λ oFLit = true)
    (hpa : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs = true) :
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Spike.Lib.srcP1 arch) SccCertificate.prog_src)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.immsOf Spike.Test.Ret0ReleaseX64.main }
      B ⟨textF, sizesFLit, offsFLit⟩ := by
  have hF : placeOKAt SccCertificate.placeCfg Λ oF = true := oF_eq ▸ h
  have hpF : Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oF.prog oF.secs = true := oF_eq ▸ hpa
  exact Spike.Lib.LowerX64.x64_scc_correctE_text_closedAt_final (cfg := SccCertificate.configW)
    (d := Spike.Test.Ret0ReleaseX64.main) (sizes := sizesFLit) (labelOffs := offsFLit)
    (pcfg := SccCertificate.placeCfg) Λ SccCertificate.prog_accepted SccCertificate.lowered_eq
    SccCertificate.emitted_eq SccCertificate.tables_eq hcF hzF hbF hF hpF

end Spike.Test.X64Ret0GOut

-- No axioms beyond Lean's.

/-- info: 'Spike.Test.X64Ret0GOut.oF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Ret0GOut.oF_eq

/-- info: 'Spike.Test.X64Ret0GOut.hcF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Ret0GOut.hcF

/-- info: 'Spike.Test.X64Ret0GOut.ret0_correctG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.X64Ret0GOut.ret0_correctG

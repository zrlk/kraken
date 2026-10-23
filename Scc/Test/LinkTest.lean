import Scc.Cert.LinkImage
import Scc.Cert.Arm
import Scc.Sem.Test.Run
import Scc.Sem.TargetA64
import Scc.Test.Src

/-!
# The kernel's static link agrees with the test model's

`Scc.Cert.Link.link` (over the data items the loader reads) gives the
layout of the test model's line walk `Scc.Sem.Test.layoutOf` at the same
bases (`Scc/Sem/Test/RunA64.lean`'s), but for the `.rodata` labels among the
symbols (`agree`), on the AArch64 listings of the test programs, and that
layout is well formed (`wfB`) with every data symbol's item in its image
(`imageOk`). Checked by evaluation.
-/

namespace Scc.Test.LinkTest

open Scc.Sem Scc.Sem.A64 Scc.Cert Kraken.Promising.AArch64

/-- `Λ` agrees with the test model's `Λ'` on every field but `static` (no
source labels here); its symbols are those of `Λ'` but the `.rodata` labels
`ro` (which the loader places the same either way, `loadSyms`). -/
def agree (ro : List Kraken.DataImage.Item) (Λ Λ' : Scc.Sem.Layout) : Bool :=
  Λ.code == Λ'.code && Λ.data == Λ'.data && Λ.rodata == Λ'.rodata && Λ.heap == Λ'.heap &&
  Λ.stackPool == Λ'.stackPool && Λ.pinned == Λ'.pinned && Λ.image == Λ'.image &&
  Λ.symbols == Λ'.symbols.filter (fun p => (Kraken.DataImage.dataLabel Λ'.rodata.lo ro p.1).isNone) &&
  loadSyms Λ ro == loadSyms Λ' ro &&
  Link.kinds.all (fun k => Λ.abortLbl k == Λ'.abortLbl k) &&
  Λ.colourMask == Λ'.colourMask && Λ.relocates == Λ'.relocates

/-- The check on one listing: it parses, its data sections read, every
`.quad` resolves, the test model's walk has no complaint, the two layouts
agree, and the link is well formed. -/
def check (asm : String) : Bool :=
  match textProgram asm, dataSections asm with
  | .ok prog, some secs =>
    let B := Link.canonical
    let code := fun l => labelAddr labelName Directive.fakeSize B.codeLo l prog
    let (Λt, errs) := Test.layoutOf asm B.codeLo B.codeSize B.roLo B.dataLo B.heapLo B.poolLo B.pinnedLo code
    let Λ := Link.link B secs code
    errs.isEmpty && Link.quadsOk secs code && agree secs.rodata Λ Λt && Link.wfB Λ &&
      Link.imageOk Λ secs code
  | _, _ => false

/-- The AArch64 listing of a source. -/
def arm (src : String) : String :=
  match Scc.Cert.Arm.compile { arch := .arm } src with
  | .ok s => s
  | .error _ => ""

#guard check (arm (w_src% "Scc/Test/hello.w"))
#guard check (arm (w_src% "Scc/Test/hello1.w"))
#guard check (arm (w_src% "Scc/Test/arith.w"))
#guard check (arm (w_src% "Scc/Test/deeprec.w"))
#guard check (arm (w_src% "Scc/Test/growmany.w"))
#guard check (arm (w_src% "Scc/Test/handoff.w"))
#guard check (arm (w_src% "Scc/Test/layout.w"))
#guard check (arm (w_src% "Scc/Test/overflow.w"))
#guard check (arm (w_src% "Scc/Test/spill.w"))
#guard check (arm (w_src% "Scc/Test/stackcap.w"))
#guard check (arm (w_src% "Scc/Test/tailloop.w"))
#guard check (arm (w_src% "Scc/Test/tailwide.w"))
#guard check (arm (w_src% "Scc/Test/threadcap.w"))

end Scc.Test.LinkTest

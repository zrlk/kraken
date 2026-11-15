import Spike.Test.X64Frame0GOut
import Scc.Test.ElfTest
import Scc.Cert.E2EX64

/-!
`frame0.w` after the granule pass at its linked post-pass executable's layout
(`Scc/Test/elf/frame0x64g/frame0`): the listing scc's pass renders is the approved
`Scc/Test/elf/frame0x64g/frame0.s` byte for byte and parses to the post-pass output, and the
post-pass output passes the placement check there (`frame0G_placeOKAt`; one `decide +kernel` per
component, combined by `placeOKAt_of`).
-/

namespace Spike.Test.Frame0LinkedX64G

set_option maxRecDepth 100000

open Scc.Cert.PlaceOK
open SccCertificate (placeCfg)
open Spike.Test.X64Frame0GOut (oFLit textF sizesFLit offsFLit)

def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/frame0x64g/frame0"

#guard elf.2 == "8b9d54b28339fa1d5e186c68325c7ba957eeefc705bb3ed381ea6ab3f2a70ef2"

abbrev ΛF : Scc.Sem.Layout := elf.1

/-- info: true -/
#guard_msgs in
#eval return (← IO.FS.readFile "Scc/Test/elf/frame0x64g/frame0.s") == textF

#guard Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs

#guard Scc.Cert.E2E.X64.e2eOk placeCfg ΛF oFLit

theorem post_a1 : X64.a1 oFLit ⟨ΛF⟩ = true := by decide +kernel
/-- A2's code sizes against the assembler's label offsets. -/
theorem post_a2w : Scc.Cert.Link.X64.sizeOkW (Int64.ofNat ΛF.code.lo) oFLit.prog oFLit.labelOffs = true := by
  decide +kernel
/-- A2's code labels, each once. -/
theorem post_a2l : Scc.Cert.Link.X64.labelsNodupL (Int64.ofNat ΛF.code.lo) oFLit.prog = true := by
  decide +kernel
/-- A2's `.quad` labels resolve, the code labels keyed (`Scc.Cert.Rt.X64.codeT_eq`). -/
theorem post_a2q : Scc.Sem.quadsResolve ΛF oFLit.secs.rodata (Scc.Sem.X64.codeLabel ΛF.code.lo oFLit.prog) = true := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel
/-- A2's `.rodata` and data symbols against the layout and the code. -/
theorem post_a2r : (Scc.Sem.rodataFits ΛF oFLit.secs.rodata && Scc.Sem.symsAgree ΛF oFLit.secs.rodata &&
    Scc.Sem.symsAbove ΛF.code.lo (Scc.Sem.X64.codeEnd ΛF.code.lo oFLit.prog) (Scc.Sem.loadSyms ΛF oFLit.secs.rodata) &&
    Scc.Cert.Link.X64.symsAround ΛF.code.lo oFLit.prog (Scc.Sem.loadSyms ΛF oFLit.secs.rodata) &&
    Scc.Cert.Link.X64.noClash ΛF.code.lo oFLit.prog (Scc.Sem.loadSyms ΛF oFLit.secs.rodata) &&
    decide (Scc.Sem.X64.codeEnd ΛF.code.lo oFLit.prog < 2 ^ 64)) = true := by
  decide +kernel
/-- A2's abort labels in the cells. -/
theorem post_a2a : Scc.Cert.Link.X64.abortsIn oFLit.prog ΛF = true := by decide +kernel
/-- A2's image. -/
theorem post_a2i : Scc.Cert.Link.X64.imageIn oFLit.prog oFLit.secs ΛF = true := by decide +kernel
/-- A2, from its parts (the certificates' split; deciding `a2` whole keeps all its terms alive). -/
theorem post_a2 : X64.a2 oFLit ⟨ΛF⟩ = true :=
  X64.a2_of_partsAt (Scc.Cert.Link.X64.loadOk_ofR post_a2w post_a2l post_a2q post_a2r) post_a2a post_a2i
theorem post_a3 : X64.a3 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a4 : X64.a4 placeCfg oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a5 : X64.a5 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a6 : X64.a6 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a7 : X64.a7 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a8 : X64.a8 oFLit ⟨ΛF⟩ = true := by decide +kernel
/-- A9, by its keyed form. -/
theorem post_a9 : X64.a9 oFLit ⟨ΛF⟩ = true := X64.a9_of_fast (by decide +kernel)
theorem post_a11 : X64.a11 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a12c : X64.a12code oFLit = true := by decide +kernel
theorem post_a12p : X64.a12ph oFLit ⟨ΛF⟩ = true := by decide +kernel

/-- **The post-pass output passes the placement check at the post-pass layout.** -/
theorem frame0G_placeOKAt : X64.placeOKAt placeCfg ΛF oFLit = true :=
  X64.placeOKAt_of post_a1 post_a2 post_a3 post_a4 post_a5 post_a6 post_a7 post_a8 post_a9
    post_a11 (X64.a12_of_split post_a12c post_a12p)

end Spike.Test.Frame0LinkedX64G

/-- info: 'Spike.Test.Frame0LinkedX64G.frame0G_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.Frame0LinkedX64G.frame0G_placeOKAt

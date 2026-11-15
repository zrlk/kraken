import Spike.Test.Hello1LinkedX64G
import Spike.Test.X64Hello1GOut

/-!
The placement check of `hello1.w`'s output after the granule pass
(`Spike.Test.X64Hello1GOut.oFLit`) at the post-pass executable's layout, one
`decide +kernel` per component. The listing that pass renders is checked byte
for byte against the approved `Scc/Test/elf/hello1x64g/hello1.s`, and it parses
to the output's program at the post-pass sizes and label offsets.
-/

namespace Spike.Test.Hello1LinkedX64GPost

open Scc.Cert.PlaceOK
open SccCertificate (placeCfg)
open Spike.Test.Hello1LinkedX64G (ΛF)
open Spike.Test.X64Hello1GOut (oFLit textF sizesFLit offsFLit)

/-- info: true -/
#guard_msgs in
#eval return (← IO.FS.readFile "Scc/Test/elf/hello1x64g/hello1.s") == textF

#guard Scc.Cert.Link.X64.parsesTo ⟨textF, sizesFLit, offsFLit⟩ oFLit.prog oFLit.secs

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
theorem post_a9 : X64.a9 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a11 : X64.a11 oFLit ⟨ΛF⟩ = true := by decide +kernel
theorem post_a12c : X64.a12code oFLit = true := by decide +kernel
theorem post_a12p : X64.a12ph oFLit ⟨ΛF⟩ = true := by decide +kernel

/-- The output after the granule pass passes the placement check at the post-pass layout. -/
theorem post_placeOKAt : X64.placeOKAt placeCfg ΛF oFLit = true :=
  X64.placeOKAt_of post_a1 post_a2 post_a3 post_a4 post_a5 post_a6 post_a7 post_a8 post_a9
    post_a11 (X64.a12_of_split post_a12c post_a12p)

end Spike.Test.Hello1LinkedX64GPost

/-- info: 'Spike.Test.Hello1LinkedX64GPost.post_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.Hello1LinkedX64GPost.post_placeOKAt

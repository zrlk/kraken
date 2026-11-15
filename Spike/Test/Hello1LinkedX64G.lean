import Spike.Test.Hello1LinkedX64

/-!
The placement check of `hello1.w`'s pre-pass output at the post-pass
(`scc --granule`) executable's layout (`Scc/Test/elf/hello1x64g/hello1`), one
`decide +kernel` per component, as `Spike/Test/Hello1LinkedX64.lean` does at
the pre-pass layout. The code-fill guard is false there and not used.
-/

namespace Spike.Test.Hello1LinkedX64G

open Scc.Cert.PlaceOK
open SccCertificate (out outLit out_eq placeCfg)

def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/hello1x64g/hello1"

#guard elf.2 == "a071e6a4364f1a10e0975ee5efe5205eda1a07491559d489bf1b94dba512ee25"

abbrev ΛF : Scc.Sem.Layout := elf.1

theorem pre_a1 : X64.a1 outLit ⟨ΛF⟩ = true := by decide +kernel
/-- A2's code sizes against the assembler's label offsets. -/
theorem pre_a2w : Scc.Cert.Link.X64.sizeOkW (Int64.ofNat ΛF.code.lo) outLit.prog outLit.labelOffs = true := by
  decide +kernel
/-- A2's code labels, each once. -/
theorem pre_a2l : Scc.Cert.Link.X64.labelsNodupL (Int64.ofNat ΛF.code.lo) outLit.prog = true := by
  decide +kernel
/-- A2's `.quad` labels resolve, the code labels keyed (`Scc.Cert.Rt.X64.codeT_eq`). -/
theorem pre_a2q : Scc.Sem.quadsResolve ΛF outLit.secs.rodata (Scc.Sem.X64.codeLabel ΛF.code.lo outLit.prog) = true := by
  rw [← Scc.Cert.Rt.X64.codeT_eq]; decide +kernel
/-- A2's `.rodata` and data symbols against the layout and the code. -/
theorem pre_a2r : (Scc.Sem.rodataFits ΛF outLit.secs.rodata && Scc.Sem.symsAgree ΛF outLit.secs.rodata &&
    Scc.Sem.symsAbove ΛF.code.lo (Scc.Sem.X64.codeEnd ΛF.code.lo outLit.prog) (Scc.Sem.loadSyms ΛF outLit.secs.rodata) &&
    Scc.Cert.Link.X64.symsAround ΛF.code.lo outLit.prog (Scc.Sem.loadSyms ΛF outLit.secs.rodata) &&
    Scc.Cert.Link.X64.noClash ΛF.code.lo outLit.prog (Scc.Sem.loadSyms ΛF outLit.secs.rodata) &&
    decide (Scc.Sem.X64.codeEnd ΛF.code.lo outLit.prog < 2 ^ 64)) = true := by
  decide +kernel
/-- A2's abort labels in the cells. -/
theorem pre_a2a : Scc.Cert.Link.X64.abortsIn outLit.prog ΛF = true := by decide +kernel
/-- A2's image. -/
theorem pre_a2i : Scc.Cert.Link.X64.imageIn outLit.prog outLit.secs ΛF = true := by decide +kernel
/-- A2, from its parts (the certificates' split; deciding `a2` whole keeps all its terms alive). -/
theorem pre_a2 : X64.a2 outLit ⟨ΛF⟩ = true :=
  X64.a2_of_partsAt (Scc.Cert.Link.X64.loadOk_ofR pre_a2w pre_a2l pre_a2q pre_a2r) pre_a2a pre_a2i
theorem pre_a3 : X64.a3 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a4 : X64.a4 placeCfg outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a5 : X64.a5 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a6 : X64.a6 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a7 : X64.a7 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a8 : X64.a8 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a9 : X64.a9 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a11 : X64.a11 outLit ⟨ΛF⟩ = true := by decide +kernel
theorem pre_a12p : X64.a12ph outLit ⟨ΛF⟩ = true := by decide +kernel

theorem pre_a12 : X64.a12 outLit ⟨ΛF⟩ = true :=
  X64.a12_of_split Spike.Test.Hello1LinkedX64.hello1_a12c pre_a12p

/-- The pre-pass output passes the placement check at the post-pass layout. -/
theorem pre_placeOKAt : X64.placeOKAt placeCfg ΛF out = true := by
  rw [out_eq]
  exact X64.placeOKAt_of pre_a1 pre_a2 pre_a3 pre_a4 pre_a5 pre_a6 pre_a7 pre_a8 pre_a9 pre_a11 pre_a12

end Spike.Test.Hello1LinkedX64G

/-- info: 'Spike.Test.Hello1LinkedX64G.pre_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.Hello1LinkedX64G.pre_placeOKAt

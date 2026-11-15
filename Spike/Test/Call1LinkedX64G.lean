import Spike.Test.X64Call1GOut
import Scc.Test.ElfTest
import Scc.Cert.E2EX64

/-!
`call1.w` after the granule pass at its linked post-pass executable's layout
(`Scc/Test/elf/call1x64g/call1`): the listing scc's pass renders is the approved
`Scc/Test/elf/call1x64g/call1.s` byte for byte and parses to the post-pass output, and the
post-pass output passes the placement check there (`call1G_placeOKAt`; one `decide +kernel` per
component, combined by `placeOKAt_of`). One instruction of `pick` perturbed
fails it, by A12 (`perturbed_not_placeOKAt`), while A9 still passes (`perturbed_a9`).
-/

namespace Spike.Test.Call1LinkedX64G

set_option maxRecDepth 100000

open Scc.Cert.PlaceOK
open SccCertificate (placeCfg)
open Spike.Test.X64Call1GOut (oFLit textF sizesFLit offsFLit)

def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/call1x64g/call1"

#guard elf.2 == "057c98a2146ab99cd6577cddb5900fdc0f6a2b1a364d74d18846565f118aee25"

abbrev ΛF : Scc.Sem.Layout := elf.1

/-- info: true -/
#guard_msgs in
#eval return (← IO.FS.readFile "Scc/Test/elf/call1x64g/call1.s") == textF

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
theorem call1G_placeOKAt : X64.placeOKAt placeCfg ΛF oFLit = true :=
  X64.placeOKAt_of post_a1 post_a2 post_a3 post_a4 post_a5 post_a6 post_a7 post_a8 post_a9
    post_a11 (X64.a12_of_split post_a12c post_a12p)

/-! ### One instruction of `pick` perturbed -/

/-- The position of `pick`'s `then` block's label in the post-pass cells. -/
def thenAt : Nat := (oFLit.prog.map (·.1)).idxOf (.label ".Lwc_pick.then0")

-- The block starts with two different instructions (evaluation).
#guard thenAt < oFLit.prog.length
#guard (oFLit.prog[thenAt + 1]?.map (·.1)) != (oFLit.prog[thenAt + 2]?.map (·.1))

/-- The post-pass output with `pick`'s first `then` instruction replaced by the cell after it. -/
def outBad : X64.Out :=
  { oFLit with prog := oFLit.prog.set (thenAt + 1) (oFLit.prog[thenAt + 2]?.getD (.label "", 0)) }

/-- **A12 catches the perturbed instruction** (kernel-checked). -/
theorem perturbed_a12 : X64.a12 outBad ⟨ΛF⟩ = false :=
  X64.a12fast_eq outBad ⟨ΛF⟩ ▸ (by decide +kernel : X64.a12fast outBad ⟨ΛF⟩ = false)

/-- **`placeOKAt` of the perturbed output is `false`**, by A12. -/
theorem perturbed_not_placeOKAt : X64.placeOKAt placeCfg ΛF outBad = false :=
  X64.placeOKAt_eq_false_of_a12 perturbed_a12

/-- A9 alone does not see it: it checks only `Accepted0`-shaped code blocks
(kernel-checked). -/
theorem perturbed_a9 : X64.a9 outBad ⟨ΛF⟩ = true :=
  X64.a9_of_fast (by decide +kernel)

end Spike.Test.Call1LinkedX64G

/-- info: 'Spike.Test.Call1LinkedX64G.call1G_placeOKAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.Call1LinkedX64G.call1G_placeOKAt

import Spike.Test.Cert.A64Call1Cert
import Scc.Test.ElfTest
import Scc.Cert.E2EA64

/-!
# `call1.w` on AArch64 at the linked executable's layout (placement only)

`call1.w` has two code blocks, `pick(n : Int)` (an `if` and a saturating
`-`) and `main`, which calls it: it is in the fragment `Accepted1`
(`Scc/Lower/Spec1.lean`), not in `Accepted0` (`SccCertificate.prog_not_accepted`).
No correctness theorem is stated for it here: this file tests the placement
check on a program with several code blocks, calls and branches.

`Scc/Test/elf/call1a64/call1` is `call1.w`'s certificate text
(`SccCertificate.asm`, written verbatim to `call1.s` next to it, checked
below), assembled and linked as `Scc/Test/run.sh` links AArch64 binaries
(`clang --target=aarch64-linux-gnu -march=armv8.4-a -nostdlib -static
-fuse-ld=lld`). It runs (`qemu-aarch64`) and exits with 42. At its layout
`Λe` (`scc_elf_layout%`), each by `decide +kernel`:

* the code fills `.text` exactly (`call1_codeFills`);
* every component of `placeOKAt` holds, A12 (the code of every user
  function: `pick`'s blocks, its branch targets, `main`'s call and return
  label, the frames within the stack need) included, so `placeOKAt` holds
  (`call1_placeOKAt`).

With one instruction of `pick`'s `then` block replaced (`movz x9, #50` by
the next one, `movz x10, #8`), A12 fails, and so does `placeOKAt`
(`perturbed_not_placeOKAt`), while A9, which checks only code blocks of the
`Accepted0` shape, still passes (`perturbed_a9`).
-/

namespace Spike.Test.Call1LinkedA64

open Scc.Cert.PlaceOK
open SccCertificate (asm out outLit out_eq placeCfg)

-- The executable is the one linked (evaluation, not a proof).
/-- info: 25e189f4ec9348fcae467617d0dd3ecfe87551af66f7270cc4d1b72d76c76261 -/
#guard_msgs in
#eval do IO.println (Scc.Cert.Sha256.ofBytes (← IO.FS.readBinFile "Scc/Test/elf/call1a64/call1"))

-- The text linked is the certificate's `asm`, verbatim (evaluation).
/-- info: true -/
#guard_msgs in
#eval do IO.println ((← IO.FS.readFile "Scc/Test/elf/call1a64/call1.s") == asm)

/-- The layout of the linked executable and its SHA-256 (`scc_elf_layout%`). -/
def elf : Scc.Sem.Layout × String := scc_elf_layout% "Scc/Test/elf/call1a64/call1"

-- The file read is the executable linked (evaluation, not a proof).
#guard elf.2 == "25e189f4ec9348fcae467617d0dd3ecfe87551af66f7270cc4d1b72d76c76261"

/-- The linked executable's layout. -/
abbrev Λe : Scc.Sem.Layout := elf.1

/-- **The code fills `.text`** at `Λe` (kernel-checked). -/
theorem call1_codeFills : Scc.Cert.E2E.A64.codeFills outLit Λe = true := by
  decide +kernel

/-- A1, A2 (by its keyed form, `Scc/Cert/A2StageA64.lean`), A4 and A7 of
`outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_1 : (A64.a1 outLit ⟨Λe⟩ && A64.a2fast outLit ⟨Λe⟩ &&
    A64.a4 placeCfg outLit ⟨Λe⟩ && A64.a7 outLit ⟨Λe⟩) = true := by
  decide +kernel

/-- A3 of `outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_3 : A64.a3 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A5 of `outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_5 : A64.a5 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A6 of `outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_6 : A64.a6 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A8 of `outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_8 : A64.a8 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A9 of `outLit` at `Λe`, by its keyed form (kernel-checked). -/
theorem call1_placeOKAt_9 : A64.a9 outLit ⟨Λe⟩ = true := A64.a9_of_fast (by decide +kernel)

/-- A11 of `outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_11 : A64.a11 outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12's code part of `outLit` (kernel-checked; `Scc/Cert/A12StageA64.lean`). -/
theorem call1_placeOKAt_12c : A64.a12code outLit = true := by
  decide +kernel

/-- A12's phase part of `outLit` at `Λe` (kernel-checked). -/
theorem call1_placeOKAt_12p : A64.a12ph outLit ⟨Λe⟩ = true := by
  decide +kernel

/-- A12 of `outLit` at `Λe`: the code of `pick` and `main`. -/
theorem call1_placeOKAt_12 : A64.a12 outLit ⟨Λe⟩ = true :=
  A64.a12_of_split call1_placeOKAt_12c call1_placeOKAt_12p

/-- **`placeOKAt` of `scc`'s output for `call1.w` at the executable's
layout**, from its components (`placeOKAt_of`). -/
theorem call1_placeOKAt : A64.placeOKAt placeCfg Λe out = true := by
  have h1 := call1_placeOKAt_1
  simp only [Bool.and_eq_true] at h1
  rw [out_eq]
  exact A64.placeOKAt_of h1.1.1.1 (A64.a2_of_fast h1.1.1.2) call1_placeOKAt_3 h1.1.2 call1_placeOKAt_5
    call1_placeOKAt_6 h1.2 call1_placeOKAt_8 call1_placeOKAt_9 call1_placeOKAt_11 call1_placeOKAt_12

/-! ### One instruction of `pick` perturbed -/

/-- The position of `pick`'s `then` block's label in the program. -/
def thenAt : Nat := outLit.prog.idxOf (.label ".L18_wc_pick.1_then0")

-- The block starts `movz x9, #50; movz x10, #8` (evaluation).
#guard thenAt < outLit.prog.length
#guard outLit.prog[thenAt + 1]? != outLit.prog[thenAt + 2]?

/-- `outLit` with `pick`'s `movz x9, #50` replaced by the instruction after
it (`movz x10, #8`). -/
def outBad : A64.Out := { outLit with prog := outLit.prog.set (thenAt + 1) (outLit.prog[thenAt + 2]?.getD (.label "")) }

/-- **A12 catches the perturbed instruction** (kernel-checked). -/
theorem perturbed_a12 : A64.a12 outBad ⟨Λe⟩ = false :=
  A64.a12fast_eq outBad ⟨Λe⟩ ▸ (by decide +kernel : A64.a12fast outBad ⟨Λe⟩ = false)

/-- **`placeOKAt` of the perturbed output is `false`**, by A12. -/
theorem perturbed_not_placeOKAt : A64.placeOKAt placeCfg Λe outBad = false :=
  A64.placeOKAt_eq_false_of_a12 perturbed_a12

/-- A9 alone does not see it: it checks only `Accepted0`-shaped code blocks
(kernel-checked). -/
theorem perturbed_a9 : A64.a9 outBad ⟨Λe⟩ = true :=
  A64.a9_of_fast (by decide +kernel)

end Spike.Test.Call1LinkedA64

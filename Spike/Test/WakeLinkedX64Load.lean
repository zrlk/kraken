/-
**Non-vacuity of the x86-64 wake load's parsed form at the linked layout**: the load premises of
`Spike.Lib.X64WakePreAsm.wake_init` and
`Spike.Lib.X64WakeLoadT.wake_initT` (`cellsOf asm = some tcells`,
`dataSections asm.text = some secs`, `wideIn (tcells.map (·.1))`, the
`loadParsed … offs` instance) at the certificate's listing `asmX` and the
linked executable's layout `Λe` (`WakeLinkedX64Elf`).

- `asmX`: the certificate's text, sizes, label offsets.
- `parsesTo asmX outLit.prog outLit.secs`: by evaluation (`#guard`; the
  kernel cannot run the parsers, the trust boundary every generated file
  has); `wake_parsedX` turns it into the two equations.
- `wake_wideX`, `wake_clearX`, `wake_loadOkX`: decided (`decide +kernel`).
- `wake_loadParsedX`: the `loadParsed` instance is `some` at `Λe`.
-/
import Spike.Test.WakeLinkedX64Elf

namespace Spike.Test.WakeLinkedX64

open Scc.Sem Scc.Sem.X64
open SccCertificate (outLit)

/-- The certificate's listing. -/
def asmX : Asm := ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩

#guard Scc.Cert.Link.X64.parsesTo asmX outLit.prog outLit.secs

/-- The parse equations from `parsesTo` (the trust boundary, `#guard` above). -/
theorem wake_parsedX (h : Scc.Cert.Link.X64.parsesTo asmX outLit.prog outLit.secs = true) :
    cellsOf asmX = some outLit.prog ∧ dataSections asmX.text = some outLit.secs :=
  Scc.Cert.Link.X64.parsed_of_parsesTo h

/-- The listing's cells are one-word. -/
theorem wake_wideX : Scc.Cert.WideX64.wideIn (outLit.prog.map (·.1)) = true := by decide +kernel

/-- The Linux entry state is clear at `Λe`. -/
theorem wake_clearX : Entry.linux.clear Λe = true := by decide +kernel

/-- The loader's checks pass at `Λe`. -/
theorem wake_loadOkX : Scc.Cert.Link.X64.loadOk Λe outLit.prog outLit.secs asmX.labelOffs = true := by
  decide +kernel

/-- **The parsed load is defined** at `Λe`. -/
theorem wake_loadParsedX (H : Hooks Kraken.Promising.X64.isa) :
    ∃ t, loadParsed H Entry.linux Λe outLit.prog outLit.secs asmX.labelOffs = some t :=
  ⟨_, Scc.Cert.Link.X64.loadParsed_of_loadOk wake_loadOkX wake_clearX⟩

end Spike.Test.WakeLinkedX64

/-- info: 'Spike.Test.WakeLinkedX64.wake_parsedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.wake_parsedX

/-- info: 'Spike.Test.WakeLinkedX64.wake_wideX' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.wake_wideX

/-- info: 'Spike.Test.WakeLinkedX64.wake_clearX' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.wake_clearX

/-- info: 'Spike.Test.WakeLinkedX64.wake_loadOkX' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.wake_loadOkX

/-- info: 'Spike.Test.WakeLinkedX64.wake_loadParsedX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedX64.wake_loadParsedX

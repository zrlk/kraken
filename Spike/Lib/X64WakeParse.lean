/-
**The loader's parses of x86-64 wake's certificate from one check**
(X64-trust-params; the twin of `WakeSpawnRP`'s `outLit_prog` and
`parsed_outLit`): the obligations' trust-boundary premises `hpa`, `hwp`,
`hd`, `hoffs` (`X64WakeAssemblyR.wake_obligations_R`,
`X64WakeSpawnR.wake_obligations_RE`/`RS`) at the certificate's text with GNU
`as`'s sizes and label offsets (`certAsm`) and its output `outLit`, from the
single loader check `hP : parsesTo certAsm outLit.prog outLit.secs` (the
certificate's `#guard`, the trust boundary; the shape of
`X64Hello1FinalC`'s `hpa`).

- `certAsm`: `⟨SccCertificate.asm, sizes, labelOffs⟩`.
- `outLit_prog`: `outLit.prog = wakeCells` (both the loader's cells of the
  same text, elaborated to the same literal; `kernel_rfl`).
- `outLit_secs`: `outLit.secs = wakeSecs` (`kernel_rfl`).
- `outLit_offs`: `certAsm.labelOffs = outLit.labelOffs` (`hoffs`; `kernel_rfl`).
- `parsed_outLit`: `hpa`, `hwp`, `hd`, `hoffs` from `hP`.

**Where this differs from AArch64**: the certificate is a text with GNU
`as`'s instruction sizes and label offsets (`Scc.Sem.X64.Asm`), not a bare
text, and the loader also reads the label offsets, so there is a fourth
parse, `hoffs`, closed here by evaluation (on AArch64 `labelOffs = []`). The
cells are `cellsOf`'s (`Option`), not `textProgram`'s (`Except`).
-/
import Spike.Lib.X64WakeCode
import Spike.Test.Cert.X64WakeCert

namespace Spike.Lib.X64WakeParse

open Scc.Sem.X64 (Asm cellsOf)
open SccCertificate (outLit)

/-- **The certificate as the loader reads it**: its text with GNU `as`'s
instruction sizes and label offsets. -/
def certAsm : Asm := ⟨SccCertificate.asm, SccCertificate.sizes, SccCertificate.labelOffs⟩

/-- **The certificate's cells are `wakeCells`**: both are the loader's
cells of the same text, elaborated to the same literal. -/
theorem outLit_prog : outLit.prog = SccCode.wakeCells := by kernel_rfl

/-- **The certificate's data sections are `wakeSecs`.** -/
theorem outLit_secs : outLit.secs = SccCode.wakeSecs := by kernel_rfl

/-- **`hoffs` at the certificate**: its label offsets are the output's. -/
theorem outLit_offs : certAsm.labelOffs = outLit.labelOffs := by kernel_rfl

/-- **The four parse equations from the single loader check.** -/
theorem parsed_outLit (h : Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs = true) :
    cellsOf certAsm = some outLit.prog ∧ cellsOf certAsm = some SccCode.wakeCells ∧
      Scc.Sem.dataSections certAsm.text = some outLit.secs ∧ certAsm.labelOffs = outLit.labelOffs :=
  let hp := Scc.Cert.Link.X64.parsed_of_parsesTo h
  ⟨hp.1, outLit_prog ▸ hp.1, hp.2, outLit_offs⟩

-- The check holds at the certificate (by evaluation, as the certificate's
-- `#guard`; not a proof).
#guard Scc.Cert.Link.X64.parsesTo certAsm outLit.prog outLit.secs

end Spike.Lib.X64WakeParse

/-- info: 'Spike.Lib.X64WakeParse.outLit_prog' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64WakeParse.outLit_prog

/-- info: 'Spike.Lib.X64WakeParse.outLit_secs' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64WakeParse.outLit_secs

/-- info: 'Spike.Lib.X64WakeParse.outLit_offs' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64WakeParse.outLit_offs

/-- info: 'Spike.Lib.X64WakeParse.parsed_outLit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeParse.parsed_outLit

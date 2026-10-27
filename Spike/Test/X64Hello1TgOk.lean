/-
**`hello1o`'s x86-64 output passes the user runs' jump check** (`tgOkB`,
`Spike/Lib/LowerX64/UserTgt.lean`): every `jmp` or `jcc` in a user
function's run goes to a labelled, nonempty run none of the write abort's
labels, at the certificate's sizes and label offsets (one kernel decision).
`hTg_of_tgOkB` turns it into `cxBlk2_ofW2`'s `hTg` (`SetupOpen.hTg`, the
main block's).

- `hello1_tgOkB`: the check at `hello1o`'s output.
-/
import Spike.Lib.LowerX64.UserTgt
import Spike.Test.Cert.X64Hello1Cert
import Spike.Test.Hello1MainSrc

namespace Spike.Lib.LowerX64

/-- **`hello1o`'s output passes `tgOkB`** (decided by the kernel). -/
theorem hello1_tgOkB : tgOkB (Scc.Cert.PlaceOK.Out.prog (Scc.Cert.PlaceOK.X64.Out.ofEmitted
    (Scc.Lower.X64.lowerAll SccCertificate.config Spike.Test.Hello1MainSrc.hello1o)
    SccCertificate.sizes SccCertificate.labelOffs)) = true := by
  decide +kernel

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.hello1_tgOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hello1_tgOkB

end Spike.Lib.LowerX64

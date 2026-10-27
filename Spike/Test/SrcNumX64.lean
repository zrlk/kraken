/-
**The source's printed cells hold numbers, and the source safety** (X64): for
`hello1o` (`Spike/Lib/Src/SrcNum2.lean`, `Spike/Lib/Src/SrcSafe2X.lean`), in the
consumer's shape at WeakCore's output hook, resting on the standard axioms only.
-/
import Spike.Lib.Src.SrcNumWX
import Spike.Lib.Src.SrcSafe2X

namespace Spike.Lib.LowerNode.TestX64

open CoreLang CoreTerm Scc.Sem Spike.Lib.LowerNode

/-- The consumer's `SrcNumS` for `hello1o` under WeakCore's output hook. -/
example {P : SrcSem.SrcParams} {I : X64ConsumerS.InvS}
    (hinit : ∀ c, P.init c → ∃ meW, c = SrcSem.setupStart P.cap meW)
    (hU : SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o) :
    X64ConsumerS.SrcNumS P Spike.Test.Hello1MainSrc.hello1o I PrintLd :=
  srcNumS_x64 (srcNumS_hello1 hinit (.inr hU))

/-- The consumer's `SrcSafeS` for `hello1o` under WeakCore's output hook. -/
example {P : SrcSem.SrcParams} (I : X64ConsumerS.InvS)
    (hinit : ∀ c, P.init c → ∃ meW, c = SrcSem.setupStart P.cap meW)
    (hU : SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o) :
    X64ConsumerS.SrcSafeS P Spike.Test.Hello1MainSrc.hello1o I :=
  hello1o_srcSafeSX (.inr hU) hinit I

/-- info: 'Spike.Lib.LowerNode.srcNumS_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srcNumS_hello1

/-- info: 'Spike.Lib.LowerNode.printLd_loadC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms printLd_loadC

/-- info: 'Spike.Lib.LowerNode.srcNumS_x64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srcNumS_x64

/-- info: 'Spike.Lib.LowerNode.hello1o_srcSafeSX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello1o_srcSafeSX

end Spike.Lib.LowerNode.TestX64

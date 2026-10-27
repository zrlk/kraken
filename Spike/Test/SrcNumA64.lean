/-
**The source's printed cells hold numbers, and the source safety** (A64): for
`hello1o` (`Spike/Lib/Src/SrcNum2.lean`, `Spike/Lib/Src/SrcSafe2A.lean`), in the
consumer's shape at WeakCore's output hook, resting on the standard axioms only.
-/
import Spike.Lib.Src.SrcNumWA
import Spike.Lib.Src.SrcSafe2A
import Spike.Lib.Src.Hello1Out

namespace Spike.Lib.LowerNode.TestA64

open CoreLang CoreTerm Scc.Sem Spike.Lib.LowerNode

/-- The consumer's `SrcNumS` for `hello1o` under WeakCore's output hook. -/
example {P : SrcSem.SrcParams} {I : A64ConsumerS.InvS}
    (hinit : ∀ c, P.init c → ∃ meW, c = SrcSem.setupStart P.cap meW)
    (hU : SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o) :
    A64ConsumerS.SrcNumS P Spike.Test.Hello1MainSrc.hello1o I PrintLd :=
  srcNumS_a64 (srcNumS_hello1 hinit (.inr hU))

/-- The consumer's `SrcSafeS` for `hello1o` under WeakCore's output hook. -/
example {P : SrcSem.SrcParams} (I : A64ConsumerS.InvS)
    (hinit : ∀ c, P.init c → ∃ meW, c = SrcSem.setupStart P.cap meW)
    (hU : SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o) :
    A64ConsumerS.SrcSafeS P Spike.Test.Hello1MainSrc.hello1o I :=
  hello1o_srcSafeS (.inr hU) hinit I

/-- info: 'Spike.Lib.LowerNode.srcNumS_hello1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srcNumS_hello1

/-- info: 'Spike.Lib.LowerNode.printLd_loadC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms printLd_loadC

/-- info: 'Spike.Lib.LowerNode.srcNumS_a64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms srcNumS_a64

/-- info: 'Spike.Lib.LowerNode.hello1o_srcSafeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello1o_srcSafeS

/-- info: 'Spike.Lib.LowerNode.hello1o_noExit_hook' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hello1o_noExit_hook

end Spike.Lib.LowerNode.TestA64

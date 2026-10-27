/-
**The statement of the x86-64 compiler theorem for an `Accepted2` program**
(`Closed2Stmt`), stated before it is proved: for every program `p` that
`scc` accepts in the `Accepted2` fragment (setup block, `newBuf`, lane
stores, `print`) whose `main` ends on every path in a call returning its result or a literal
(`mainRetOk`), whose output passes the
placement check at a layout `Λ` at a configuration with `CfgNeedOk`, and every
text that parses to that output, the text is `Correct` over the kernel-model target at every
admissible entry state, against the source with WeakCore's output hooks
(`srcP1o arch p`), at `Λ` with no static label and the immediates
`imms2Me Λ p` (`imms2Of p`, and the first TCB for `me` at the setup start),
for every budget whose cell count is the allocator's
(`hB`). `x64_scc_correctE_text_closedAt2` will prove it.

- `Closed2Stmt`: the statement, a `Prop`.

`Spike/Test/X64Hello1Closed2.lean` instantiates it at `hello1`.
-/
import Spike.Lib.LowerX64.MainNeed
import Scc.Sem.CorrectEX64
import Scc.Sem.SrcOut
import Scc.Lower.Spec2
import Spike.Lib.Src.ImmsMe
import Scc.Cert.LinkX64

namespace Spike.Lib.LowerX64

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64

/-- **The x86-64 compiler theorem for an `Accepted2` program, at any
layout** (the statement): for a program `p` that `scc` accepts (`hp`)
and whose `main` ends, on every path, in a call returning its result or a
literal (`mainRetOk`, a proof-coverage condition, not a semantic one, `hR`),
whose output passes the placement check at a layout `Λ`
(`h`) at a configuration with `CfgNeedOk` (`hcfg`), and a text that parses to that
output (`hpa`), the text is `Correct` over the kernel-model target at
every entry state that `Entry.Ok` admits, against the source with
WeakCore's output hooks (`srcP1o arch p`), at `Λ` with no static label and
the lowering's immediates `imms2Of p` with the first TCB `Λ.pinned.lo + 8`
for `me` at the setup start (`imms2Me Λ p`), for every budget `B` whose cell
count is the allocator's (`hB`, the arena consumer's). -/
def Closed2Stmt : Prop :=
  ∀ (cfg : Scc.Config) (pcfg : Scc.Cert.PlaceOK.Config) (p : CoreTerm.Prog) (sizes : List Nat)
    (labelOffs : List (String × Nat)) (Λ : Scc.Sem.Layout), Scc.Lower.Accepted2 p = true →
    Scc.Lower.mainRetOk p = true →
    placeOKAt pcfg Λ (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs) = true →
    CfgNeedOk pcfg = true →
    ∀ {text : String}, Scc.Cert.Link.X64.parsesTo ⟨text, sizes, labelOffs⟩
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).prog
      (Out.ofEmitted (Scc.Lower.X64.lowerAll cfg p) sizes labelOffs).secs = true →
    ∀ {B : Scc.Sem.Budget}, B.cells = Scc.Cert.PlaceOK.allocCells → ∀ {arch : WeakMem.Arch},
    Scc.Sem.X64.CorrectE 1 (Scc.Sem.SrcSem.source (Scc.Sem.SrcSem.srcP1o arch p) p)
      { Λ with static := fun _ => none, imms := Spike.Lib.LowerNode.imms2Me Λ p } B ⟨text, sizes, labelOffs⟩

end Spike.Lib.LowerX64

import Spike.Lib.LowerX64.Body2
import Spike.Lib.Src.Walk2Of

/-!
**`RetOk` of an `Accepted2` block from `Accepted2`** (x86-64): at
every point of the lowering's walk of a compiled block of result `Int`, a
`ret` is of one word placed as one (`retOne_ofAccepted2`), so `RetOk`
(`RetOne.toOk`).
-/

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Scc.IR
open Spike.Lib.LowerNode

/-- **`RetOk` at every point of an `Accepted2` block's walk** of result
`Int`. -/
theorem retOk_ofAccepted2 {p : Prog} (hp : Scc.Lower.Accepted2 p = true) {cx : Scc.Lower.Ctx}
    (hprog : cx.prog = p)
    (hext : ∀ d ∈ p, (cx.externs.find? (·.1 == d.name)).isSome = true → d.retTy = .unit)
    {d : Decl} (hd : d ∈ p) (hne : Scc.Lower.isPrintExt d = false)
    (hnl : ¬(Scc.Lower.hasPrint p = true ∧ d.name = "printL")) (hint : d.retTy = .int)
    {ps : List Operand} (hps : ∀ o ∈ ps, IsReg o) (hpl : Scc.Obj.valWords d.argTy = some ps.length) (n : Nat) :
    ∀ q ∈ lowerEnvs2 cx [(d.arg, d.argTy, ps)] n d.body, RetOk q := by
  intro q hq
  have h := retOne_ofAccepted2 hp hprog hext hd hne hnl hint hps hpl n q hq
  refine RetOne.toOk (fun a ha => ?_) (fun a t w ha hw => ?_)
  · obtain ⟨t, w, hw, -⟩ := h a ha
    exact ⟨t, w, hw⟩
  · obtain ⟨t', w', hw', hg⟩ := h a ha
    rw [hw] at hw'
    cases hw'
    exact hg

end Spike.Lib.LowerX64

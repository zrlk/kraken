import Spike.Lib.Src.SrcNum2
import Spike.Lib.A64ConsumerS

/-!
**`SrcNumSP` as the A64 consumer's `SrcNumS`**: both assume thread 0's
promises empty; `SrcNumSP` gives `SrcNumS` at any fragment invariant (its
frame-run premise unused).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm Scc.Sem

/-- **`SrcNumSP` is the A64 consumer's `SrcNumS`**, premise-free. -/
theorem srcNumS_a64 {P : SrcSem.SrcParams} {p : Prog} {I : A64ConsumerS.InvS}
    {Ld : Ctl → WeakMem.AllocLabel → Nat → Prop} (h : SrcNumSP P p Ld) :
    A64ConsumerS.SrcNumS P p I Ld :=
  fun tr s th hr hth hp _ _ _ c1 ht he _ c' l j hl hld => h tr s th hr hth hp c1 ht he c' l j hl hld

end Spike.Lib.LowerNode

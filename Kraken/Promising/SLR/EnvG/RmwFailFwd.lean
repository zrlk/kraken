/-
**A failed RMW leaves the forwarding items alone, for every ISA**
.

`envG_rmw_fail_getFwd`: an `EnvG I A tid pl` step of `.rmw k addr n op`
whose operation fails at the value read (`op old = none`) leaves
`vs.getFwd` unchanged (the outcome's views are the read's, after the optional
fence; neither touches the forwarding items). ISA-neutral form of the two
copies `CasSmoke.rmw_fail_getFwd` (`EnvG/CasVC.lean`, AArch64) and
`Cmpx.rmw_fail_getFwd` (`EnvG/X64CmpxVC.lean`, x64), which keep their names
and statements and are proved from it.
-/
import Kraken.Promising.SLR.EnvG.Env
import Kraken.Promising.SLR.SpinAcquire

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR.SpinCommon

variable {I : ISA}

/-- **A failed RMW leaves the forwarding items alone** (any ISA): its views
are the read's, after the optional fence. -/
theorem envG_rmw_fail_getFwd {A : Arch} {tid : Nat} {pl : Plan} {σ σ' : State I} {k : RmwKind}
    {addr : BitVec 64} {n : Nat} {op : Val → Option Val} {old : Val}
    (h : (Kraken.Promising.SLR.EnvG I A tid pl).step (.rmw k addr n op) σ old σ') (hop : op old = none)
    (l : Loc) : σ'.vs.getFwd l = σ.vs.getFwd l := by
  obtain ⟨c, x, -, hx, -, -, -, -, -, hbr⟩ := (h : RmwOut A tid pl σ σ' k ⟨addr, n⟩ op old)
  rcases hbr with ⟨-, -, hvs, -⟩ | ⟨new, -, -, hop', -⟩
  · have h5 := readSuccs_fwdb A _ hx
    have e : x.2.2.views.getFwd l = (fenceOptCtx A (envCtx tid σ.vs c)).views.getFwd l := by
      simp only [Views.getFwd, h5]
    rw [hvs, fenceOptCtx_getFwd, e, fenceOptCtx_getFwd]
    rfl
  · rw [hop] at hop'; cases hop'

end Kraken.Promising.SLR.EnvG

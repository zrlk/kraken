/-
**The overflow abort's source facts from the lowering's**: the node
invariant at the abort label (`AbSrc`, `Spike/Lib/LowerNode.lean`) gives the
consumer's (`AbortPath.at_`'s overflow case, `Spike/Lib/OvfAbort.lean`).

* `envSmall_of_envNum`: every bound word a number below `2^64` makes the
  environment small.
* `ovfReady_of_abSrc`, `envSmall_of_abSrc`: the two source facts of `AbSrc`.
* `lo_room`: the stack room of the abort path: a region reaching down to the
  stack's base, whose frame passed the prologue's check against the limit
  (`stackBase + headroom`), has room for `d ≤ headroom` bytes below the frame
  (the call into `scc_rt_abort`: 48 bytes on AArch64, 40 on x64).
-/
import Spike.Lib.OvfAbort
import Spike.Lib.LowerNode

namespace Spike.Lib.AbortSrc

open CoreLang CoreTerm
open Spike.Lib Spike.Lib.LowerNode

/-- **A numeric environment is small.** -/
theorem envSmall_of_envNum {env : TermRun.Env} (h : EnvNum env) : EnvSmall env := by
  intro b hb w hw n hn
  obtain ⟨m, hm, hlt⟩ := h b hb w hw
  rw [hm] at hn
  cases hn
  exact hlt

/-- The control at the abort label is about to overflow. -/
theorem ovfReady_of_abSrc {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
    {s : Spike.Lib.Form.SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : AbSrc lbl rs s sl c) : OvfReady c :=
  h.1

/-- The environment at the abort label is small. -/
theorem envSmall_of_abSrc {lbl : WeakMem.AllocLabel → Option Nat} {rs : Scc.IR.Reg → Option Int}
    {s : Spike.Lib.Form.SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : AbSrc lbl rs s sl c) : EnvSmall c.env :=
  envSmall_of_envNum h.2.1

/-- **The abort path's stack room**: a region based at `R.base` whose low end
is at or below the stack's base (`hlo`), with a frame of `fr` bytes whose
low end is at or above the stack limit (`hchk`, the prologue's check),
extends `d` bytes below the frame for any `d` within the headroom. -/
theorem lo_room {R : Region} {fr d stackBase : Int} (hlo : (R.base.toNat : Int) + R.lo ≤ stackBase)
    (hchk : stackBase + Scc.IR.Tcb.headroom ≤ (R.base.toNat : Int) - fr) (hd : d ≤ Scc.IR.Tcb.headroom) :
    R.lo ≤ -fr - d := by
  omega

end Spike.Lib.AbortSrc

/-
**Small additions to the width-generic AArch64 rows**
(`Lower/EventsA64W.lean`).

- `instrSemInf_ldopG`: `ldadd` and the other `ld<op>` (+`a`/`l`/`al`,
  +`b`/`h`, any register width) on the fuel-free machine, from the generic
  row `exec_ldopG_agrees`. The operation always writes, so the RMW is one
  read and one paired write (no `op old = none` branch).

## `ldar` (`.acq`) against `ldapr` (`.acqPc`) on `Arch.armv8` (note, no proof)

The two loads differ by the same term as on TSO (`Lower/TsoCollapse.lean`,
`readSuccs_acq_eq`): an `.acq` load's pre-view joins the thread's `vRel`
(`readPre`: `if A.loadKind k == .acq then vRel`), an `.acqPc` load's does not.
So `stlr; ldar` is ordered (RCsc) and `stlr; ldapr` is not (RCpc). The lowering litmus suite
found the observable consequence: `SB+polqs` (store-release then load,
both threads) is *Sometimes* with `ldapr` and *Never* with `ldar`. Hence a
lowering of a source `load acq` to `ldapr` simulates backward only if the
source `load acq` is RCpc; if it is RCsc, the lowering must emit `ldar`.
-/
import Kraken.Promising.Lower.EventsA64W

namespace Kraken.Promising.Lower.A64

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Live Kraken.Promising.Live.Inf Kraken.Promising.Live.TicketStep

section Inf

variable (A : Arch) (tid : Nat) {c c' : Config isaLSE2} {t : Thread isaLSE2}
  (ht : c.threads[tid]? = some t) {sz : Nat}
include ht

/-- **`ldadd` and the other `ld<op>` (+`a`/`l`/`al`, +`b`/`h`) `Ws|Xs, Wt|Xt,
[Xn]`**, any `Arch`: one atomic read of `⟨Xn, m.bytes⟩` (plain if the
destination is the zero register), then one paired write of
`op(old, Rs)` (`instrSemInf_rmw_at` at `exec_ldopG_agrees`; the operation
never fails). -/
theorem instrSemInf_ldopG {w : RegWidth} {m : MemWidth} {rs rt : RegOrZr w} {n : XReg} {op : AtomicOp}
    {k : RmwKind} (hc : CellAt (stOf t) (.instr ⟨w, .LDOP op k m rs rt (.low (.reg n) .W64)⟩) sz)
    (hdm : Mem.loadInt (stOf t).st.1.dmem (baseAddr (stOf t) n) m.bytes = none)
    (hag : (stOf t).decls.AgreesAt (baseAddr (stOf t) n) m.bytes) :
    InstrSemInf A tid c c' ↔ ∃ tr old c1 c2 th,
      (tr, old, c1) ∈ readSuccs A (ivOf t) (rmwFenceOpt A (ctx0 tid t c.mem))
          (if rt.isZr then .plain else (A.rmwKind k).loadKind) false ⟨baseAddr (stOf t) n, m.bytes⟩ rt.isZr ∧
      c2 ∈ writeSuccs A tid (ivOf t) c1 (A.rmwKind k).storeKind true ⟨baseAddr (stOf t) n, m.bytes⟩
        ((op.apply (old.setWidth m.bits) (((stOf t).st.1.regs.getRegOrZr rs).take m.bits)).setWidth 128)
        (some tr) (c1.loadViews.getLastD 0) ∧
      th ∈ finishInstr t (isaLSE2.deps t.st) (ivOf t)
        (after (stOf t) sz { (stOf t).st.1 with
          regs := (stOf t).st.1.regs.setRegOrZr rt ((old.setWidth m.bits).zeroExtend w.bits) })
        (rmwFenceOpt A (rmwBump (A.rmwKind k) rt.isZr ⟨baseAddr (stOf t) n, m.bytes⟩ { c2 with rmwWrote := true })) ∧
      CertOk A tid th (rmwFenceOpt A (rmwBump (A.rmwKind k) rt.isZr ⟨baseAddr (stOf t) n, m.bytes⟩
        { c2 with rmwWrote := true })).mem ∧
      c' = c.withThread tid th (rmwFenceOpt A (rmwBump (A.rmwKind k) rt.isZr ⟨baseAddr (stOf t) n, m.bytes⟩
        { c2 with rmwWrote := true })).mem := by
  rw [instrSemInf_rmw_at A tid ht (exec_ldopG_agrees hc hdm hag)]
  constructor
  · rintro ⟨tr, old, c1, cf, th, hx, (⟨h, -⟩ | ⟨new, c2, hnew, hw, rfl⟩), hth, hcert, rfl⟩
    · cases h
    · cases hnew
      exact ⟨tr, old, c1, c2, th, hx, hw, hth, hcert, rfl⟩
  · rintro ⟨tr, old, c1, c2, th, hx, hw, hth, hcert, rfl⟩
    exact ⟨tr, old, c1, _, th, hx, .inr ⟨_, c2, rfl, hw, rfl⟩, hth, hcert, rfl⟩

end Inf

end Kraken.Promising.Lower.A64

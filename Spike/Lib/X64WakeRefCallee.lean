/-
**The refusal path's callee region** (x86-64, wake.w): the facts the
refusal path's pieces (`X64WakeRefStub`'s `RefAC` … `RefAbW`) share about
`TObl`'s region. A64 keeps `callee_of_pre` in `A64WakeRefAbW`; here it has
its own file so that both halves of the pieces import it.

- `callee_of_pre`: `TObl`'s region `R.callee (-72 - 8) (-24) 16` is `OK`
  under `Pre`, its bounds `-24` and `16`.

**Unlike AArch64**: the region is `R.callee (-72 - 8) (-24) 16` with no
alignment (A64's `R.callee (-80) (-48) 0`, 16-aligned).
-/
import Spike.Lib.X64WakeRefStub

namespace Spike.Lib.X64.WakeRefStub

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region PlaceWX)
open Spike.Lib.X64.Rt (RuntimeLayout)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`TObl`'s region under `Pre`**: `OK`, its bounds `-24` and `16`. -/
theorem callee_of_pre {l : WeakMem.AllocLabel} {b : Nat} {R : Region} {cP : Ctl} {cA mT : BitVec 64}
    (h : Pre hp i l b R cP cA mT) :
    (R.callee (-72 - 8) (-24) 16).OK ∧ (R.callee (-72 - 8) (-24) 16).lo = -24 ∧
      (R.callee (-72 - 8) (-24) 16).hi = 16 := by
  obtain ⟨-, -, -, hR, hlo, hhi, -⟩ := h
  exact ⟨Region.callee_ok hR (by omega) (by decide) (by omega) (by omega), rfl, rfl⟩

end Spike.Lib.X64.WakeRefStub

/-- info: 'Spike.Lib.X64.WakeRefStub.callee_of_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeRefStub.callee_of_pre

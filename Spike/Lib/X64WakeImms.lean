/-
**wake's immediate table on x86-64** (data only): the twin of
`Spike.Lib.WakeImmsW.immsW`, `Spike.Lib.WakeImmsC0.meAt`/`immsW2` and
`Spike.Lib.WakeFinalCAW.iW` over x86-64's `SccCode.wakeImms`
(`Spike/Lib/X64WakeCode.lean`). Main's `ThreadId` word `me` is
the immediate `tcb0 Λ0 = Λ0.pinned.lo + 8` at the start's term `startT` and
at the box's term `wakeImm_t1`; elsewhere the certificate's table.

The AArch64 modules import AArch64's consumer (`A64PlacedSE`, `A64WakeC0`),
so they cannot be imported on x86-64; the placement lemmas (`placedSE_start`,
`placedSE_c0W`) are retargeted separately. The definitions
below are those modules' token for token, at `SccCode.wakeImms` of x86-64.
-/
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.WakeImms

open CoreTerm

/-- The start's term: `main` on its `ThreadId` (`WakeImmsW.startT`). -/
def startT : Expr := .tail "main" [] (.var "me")

/-- Main's control block at the placement input `Λ0` (`WakeLoadT.tcb0`). -/
def tcb0 (Λ : Scc.Sem.Layout) : Nat := Λ.pinned.lo + 8

open Classical in
/-- **wake's immediate table** at `Λ0`, at the start (`WakeImmsW.immsW`). -/
noncomputable def immsW (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) (e : Expr) (x : String)
    (k : Nat) : Option Nat :=
  if e = startT ∧ x = "me" ∧ k = 0 then some (Λ0.pinned.lo + 8) else i0 e x k

open Classical in
/-- **The base table with `me` at the box** (`WakeImmsC0.meAt`). -/
noncomputable def meAt (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) (e : Expr) (x : String)
    (k : Nat) : Option Nat :=
  if e = SccCode.wakeImm_t1 ∧ x = "me" ∧ k = 0 then some (tcb0 Λ0) else i0 e x k

/-- **The table with `me` at the start and at the box** (`WakeImmsC0.immsW2`). -/
noncomputable abbrev immsW2 (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    Expr → String → Nat → Option Nat :=
  immsW Λ0 (meAt Λ0 i0)

/-- **The root's immediate table** at the placement input `Λ0` (`WakeFinalCAW.iW`). -/
noncomputable abbrev iW (Λ0 : Scc.Sem.Layout) : Expr → String → Nat → Option Nat :=
  immsW2 Λ0 SccCode.wakeImms

/-- The box's term is not the start's. -/
theorem t1_ne_startT : SccCode.wakeImm_t1 ≠ startT := by
  simp [SccCode.wakeImm_t1, startT]

/-- At the start's term, word 0 of `me` is main's control block. -/
theorem immsW_start (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    immsW Λ0 i0 startT "me" 0 = some (tcb0 Λ0) := by
  simp [immsW, tcb0]

/-- At the box's term, word 0 of `me` is main's control block. -/
theorem immsW2_c0 (Λ0 : Scc.Sem.Layout) (i0 : Expr → String → Nat → Option Nat) :
    immsW2 Λ0 i0 SccCode.wakeImm_t1 "me" 0 = some (tcb0 Λ0) := by
  simp [immsW2, immsW, meAt, t1_ne_startT]

/-- **`wakeImms` has no entry at the start's `me`**: `iW` overrides nothing. -/
theorem wakeImms_startT : SccCode.wakeImms startT "me" 0 = none := by
  simp [SccCode.wakeImms, startT, SccCode.wakeImm_t1, SccCode.wakeImm_t0]

end Spike.Lib.X64.WakeImms

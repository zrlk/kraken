/-
**The loaded thread at `_start`'s node, any source control** (AArch64):
`Spike/Lib/LowerA64/Correct.lean`'s `entry_atE` with the node's control
(`Ret0.entryN`'s `c0`) generic, for a start other than `main`'s (an
`Accepted2` program's setup block).

- `entry_atEC`.
-/
import Spike.Lib.LowerA64.Correct

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64.Rt (RuntimeLayout rtF entryR)
open Scc.Sem Scc.Sem.A64

section Entry

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node with the control `c`** on the
entry stack (`entryR E`) of an admissible entry state `E` (`hE`), the
runtime's words unloaded (`rtF_stackMem`), given the loaded pc is
`_start`'s (`hpc`): `entry_atE` for any control. -/
theorem entry_atEC (c : Ctl) {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (rtF (RuntimeLayout.ofPlaceOK h i)) (Ret0.entryN (RuntimeLayout.ofPlaceOK h i).lab c)
      (Scc.Sem.A64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) c := by
  refine ⟨rfl, Scc.Cert.Rt.A64.endPc_threadAt_below _ _ _ _, rfl, hpc,
    ⟨{ SP := UInt64.ofNat E.sp }, _, fun k =>
    BitVec.ofInt 64 ((Mem.loadInt E.stackMem ((entryR E).addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, ?_, ?_⟩, Spike.Lib.A64.Rt.rtF_stackMem _ hE rfl, rfl⟩
  · intro r k hr
    rcases r with x | _
    · simp [Ret0.entryN, A64.Abort.oE, SO.get, lk] at hr
    · simp only [Ret0.entryN, A64.Abort.oE, SO.get, Option.some.injEq] at hr
      subst hr
      dsimp only
      show (UInt64.ofNat E.sp).toBitVec = BitVec.ofNat 64 E.sp + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.A64.Rt.stack_wordE hE hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt E.stackMem _ 8).getD 0)
    rw [hj]; rfl

end Entry

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.entry_atEC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms entry_atEC

end Spike.Lib.LowerA64

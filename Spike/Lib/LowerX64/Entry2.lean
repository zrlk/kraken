/-
**The loaded thread at `_start`'s node, any source control** (x86-64):
`Spike/Lib/LowerX64/Correct.lean`'s `entry_atXE` with the node's control
(`entryN0`'s `c0`) generic, for a start other than `main`'s (an
`Accepted2` program's setup block).

- `entry_atXEC`.
-/
import Spike.Lib.LowerX64.Correct

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64.Rt (RuntimeLayout rtF entryR)
open Scc.Sem Scc.Sem.X64

section Entry

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option maxRecDepth 100000 in
/-- **The loaded thread is at `_start`'s node with the control `c`** on the
entry stack (`entryR E`) of an admissible entry state `E` (`hE`), the
runtime's words unloaded (`rtF_stackMem`), given the loaded pc is
`_start`'s (`hpc`): `entry_atXE` for any control. -/
theorem entry_atXEC (c : Ctl) {E : Entry} (hE : E.Ok (RuntimeLayout.ofPlaceOK h i).Λ)
    (hpc : (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
      (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)).st.2 =
      (RuntimeLayout.ofPlaceOK h i).lab "_start") :
    At (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc (entryR E)
      (rtF (RuntimeLayout.ofPlaceOK h i))
      (Spike.Lib.X64.Rt.entryN0 (RuntimeLayout.ofPlaceOK h i).lab c)
      (Scc.Sem.X64.threadAt E (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog
        (Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)) c := by
  refine ⟨rfl, Scc.Cert.Link.X64.endPc_threadAt_below _ _ _ _, rfl, hpc,
    ⟨{ rsp := UInt64.ofNat E.sp }, _, _, fun k =>
      BitVec.ofInt 64 ((Mem.loadInt E.stackMem ((entryR E).addr k) 8).getD 0)⟩,
    ⟨rfl, rfl, rfl, ?_, ?_⟩, Spike.Lib.X64.Rt.rtF_stackMem _ hE rfl, rfl⟩
  · intro r k hr
    simp only [Spike.Lib.X64.Rt.entryN0, SO.get] at hr
    split at hr
    · rename_i he
      subst he
      cases hr
      dsimp only
      show (UInt64.ofNat E.sp).toBitVec = BitVec.ofNat 64 E.sp + BitVec.ofInt 64 0
      rw [show BitVec.ofInt 64 0 = 0#64 from rfl, BitVec.add_zero]; rfl
    · simp [lk] at hr
  · intro k hk
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (Spike.Lib.X64.Rt.stack_wordE hE hk)
    refine ⟨j, hj, ?_⟩
    show _ = BitVec.ofInt 64 ((Mem.loadInt E.stackMem _ 8).getD 0)
    rw [hj]; rfl

end Entry

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.entry_atXEC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms entry_atXEC

end Spike.Lib.LowerX64

/-
**The return-value contract at `main`'s exit** (`Spike/Lib/LowerA64/StartU.lean`):
`RetV` holds at a `ret` of a number represented by `v` and fails at a `ret`
of `null` (whose exit code, `0`, the register need not match) and at a
mismatched value. `MainUW.dt` lifts `ret0.w`'s `scc_rt_main` obligations to a
live write tail, and `swUW_gen_dt` holds at `ret0.w`'s instance (its
premises satisfiable there, the user function's interface given).
-/
import Spike.Lib.LowerA64.StartU
import Spike.Test.A64RtMainU

namespace Spike.Test.LowerA64StartU

open Spike.Lib.LowerA64
open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The control at `ret y`, `y` bound to the word `w`. -/
def retC (w : TermRun.Word) : Spike.Lib.Ctl := ⟨.ret (.var "y"), [("y", .int, [w])], none⟩

/-- **`RetV` at `ret 300`, valued `300`** (exit code `300 mod 256`). -/
example {lbl : WeakMem.AllocLabel → Option Nat} : RetV lbl (retC (TermRun.cst (.num 300))) 300#64 :=
  ⟨.var "y", .int, _, rfl, rfl, rfl, ⟨300, rfl⟩, by decide, rfl⟩

/-- `RetV` fails at a `null` word, though `ValRep` would accept `0`. -/
example {lbl : WeakMem.AllocLabel → Option Nat} : ¬ RetV lbl (retC (TermRun.cst .null)) 0#64 := by
  rintro ⟨a, t, w, ha, -, he, ⟨n, hn⟩, -⟩
  cases ha
  simp only [retC, TermRun.evalAt, TermRun.lookupE, List.find?, Option.map] at he
  obtain ⟨-, rfl⟩ := he
  cases hn

/-- `RetV` fails at another value. -/
example {lbl : WeakMem.AllocLabel → Option Nat} : ¬ RetV lbl (retC (TermRun.cst (.num 300))) 44#64 := by
  rintro ⟨a, t, w, ha, -, he, -, hv⟩
  cases ha
  simp only [retC, TermRun.evalAt, TermRun.lookupE, List.find?, Option.map] at he
  obtain ⟨-, rfl⟩ := he
  exact absurd hv.2 (by decide)

open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.Test Spike.Lib.A64.Flow.Ret0.Inst in
/-- **`swUW_gen_dt` at `ret0.w`'s instance**, any write tail `Dt`. -/
example {rS : Scc.Sem.Range} {c0 : Spike.Lib.Ctl} {ms : Spike.Lib.MemSide isaLSE2}
    {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {Dt : State → Prop}
    (hC0 : Spike.Lib.A64Consumer.CFacts SccCode.ret0Λ SccCode.ret0Λ.static c0) {R : Spike.Lib.Region}
    {F : MachineData → Prop} {top : BitVec 64} (h16 : top.toNat % 16 = 0)
    (hok : (Spike.Lib.A64.Flow.swR top (-80) 0).OK) (hsub : rS.Sub SccCode.ret0Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hU : ∀ v, UserCallW (fun s c =>
        Spike.Lib.A64Consumer.SFacts SccCode.ret0Λ μ0 own rS Tk SccCode.ret0Λ.static s c Dt)
      (Kr rS) p lbl ms Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe Spike.Lib.A64.Flow.Ret0.Mem.ret0End
      (Spike.Lib.A64.Flow.swR v (-80) 0)
      (swFSL 80 rS top (Spike.Lib.A64.Flow.Ret0.limA (UInt64.ofBitVec 134217736#64)) v)
      ret0MC.fn ret0MC.Z 32 32 (ret0Post c0)
      ((_root_.Executable.labels Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe).label ret0MC.e0 + 4).toBitVec c0
      (UInt64.ofBitVec 134217736#64)) :
    SwUW (fun s c => Spike.Lib.A64Consumer.SFacts SccCode.ret0Λ μ0 own rS Tk SccCode.ret0Λ.static s c Dt) (Kr rS) p lbl
      Spike.Lib.A64.Flow.Ret0.Mem.ret0Exe Spike.Lib.A64.Flow.Ret0.Mem.ret0End R
      (fun m => F m ∧ Spike.Lib.A64.Flow.Ret0.StackM rS m) ms rS 134217736#64 top c0 80 ret0MC 32 32 (ret0Post c0) :=
  swUW_gen_dt (Post := ret0Post c0) ret0_instOk Spike.Lib.A64.Flow.Ret0.ret0_startTailIn ret0_mainUIn hC0
    (fun _ _ h => h.1 ▸ hC0) ret0_mainPh ret0_swPh h16 hok (by decide) (by decide) (by decide) (by decide)
    (by decide) ret0_limMapped hsub hfit hU

end Spike.Test.LowerA64StartU

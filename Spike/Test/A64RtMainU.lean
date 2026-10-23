/-
**`mainUW_gen`/`swUW_gen` at `ret0.w`'s instance** (`Spike/Lib/Rt/A64RtMainU.lean`):
`ret0.w`'s `scc_rt_main` and switch have their phase facts at the hand
labels and phases (`ret0_mainPh`, `ret0_swPh`), and the generic theorems give
the `MainUW` and `SwUW` that the hand `mainW`/`swW` (`Spike/Lib/A64Ret0I.lean`)
give through `mainUW_ofW`/`swUW_ofW`, the user function's interface taken
from the hand one.
-/
import Spike.Lib.Rt.A64RtMainU
import Spike.Lib.Rt.A64SegsRet0
import Spike.Test.A64RtW

namespace Spike.Lib.A64.Rt.Test

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Range)
open Spike.Lib.A64Consumer Spike.Lib.A64
open Spike.Lib.A64.Rt Spike.Lib.A64.Rt.MainU Spike.Lib.A64.Flow.Ret0.Inst
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Ret0 (MainG StackM limA swFS)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0Words_mapped ret0_lays)
open SccCode (ret0Λ ret0Prog)

/-- **`ret0.w`'s `scc_rt_main` phase facts.** -/
theorem ret0_mainPh : MainPh okPc ph labT ret0MC where
  hd := by decide +kernel
  ld := by decide +kernel
  br := by decide +kernel
  fr := by decide +kernel
  call := by decide +kernel
  ex := by decide +kernel
  svc := by decide +kernel

/-- **`ret0.w`'s switch phase facts.** -/
theorem ret0_swPh : SwPh okPc ph labT where
  sw := by decide +kernel
  main := by decide +kernel

/-- The TCB's limit word at `n0 = 0` is mapped for reading. -/
theorem ret0_limMapped : Scc.Sem.Kernel.mapped (K0 ret0Λ) false ⟨limA (UInt64.ofBitVec 134217736#64), 8⟩ = true := by
  rw [Spike.Lib.A64.Flow.Ret0.Inst.limA_tcb0]; exact (ret0Words_mapped (by decide)).2.1

variable {rS : Range} {c0 : Ctl} {ms : MemSide isaLSE2}

/-- **The hand `mainW`'s `MainUW` from the generic one**: the same statement
as `mainUW_ofW (mainW hC0 h16 hok hsub hfit ms)`. -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {top : BitVec 64} (h16 : top.toNat % 16 = 0)
    (hok : (swR top (-80) 0).OK) (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    MainUW (Wr rS) (Kr rS) ret0Exe ret0End (swR top (-80) 0) (swFS rS top (limA (UInt64.ofBitVec 134217736#64)) top)
      ms ret0MC (ret0Post c0) ⟨top, UInt64.ofBitVec 134217736#64, c0⟩ :=
  mainUW_gen ret0_instOk ret0_mainUIn hC0 (fun _ _ h => h.1 ▸ hC0) ret0_mainPh hok h16 (by show (-80 : Int) ≤ _; decide)
    (by show (0 : Int) ≤ 0; decide) (by show (-80 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
    (by decide) (by decide) (by decide) ret0_limMapped (fun _ h => h.1.2) hsub hfit (fun _ h => h.2)

/-- **The hand `swW`'s `SwUW` from the generic one**, the user function's
interface the hand one's: the same statement as `swUW_ofW … (swW …)`. -/
example {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region}
    {F : MachineData → Prop} {top : BitVec 64} (h16 : top.toNat % 16 = 0) (hok : (swR top (-80) 0).OK)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    SwUW (Wr rS) (Kr rS) p lbl ret0Exe ret0End R (fun m => F m ∧ StackM rS m) ms rS 134217736#64 top c0 80 ret0MC 32
      32 (ret0Post c0) :=
  swUW_gen (Post := ret0Post c0) ret0_instOk Flow.Ret0.ret0_startTailIn ret0_mainUIn hC0 (fun _ _ h => h.1 ▸ hC0)
    ret0_mainPh ret0_swPh h16 hok (by decide) (by decide) (by decide) (by decide) (by decide) ret0_limMapped hsub
    hfit
    (swUW_ofW (R := R) (F := fun m => F m ∧ StackM rS m) ret0_lays rfl (swW (R := R) hC0 rfl h16 hok hsub hfit ms)).user

end Spike.Lib.A64.Rt.Test

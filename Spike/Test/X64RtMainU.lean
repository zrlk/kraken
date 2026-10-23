/-
**`mainUW_gen`/`swUW_gen` at `ret0.x`'s instance** (`Spike/Lib/Rt/X64RtMainU.lean`):
`ret0.x`'s `scc_rt_main` and switch have their phase facts at the hand
labels and phases (`ret0_mainPh`, `ret0_swPh`), and the generic theorems give
the `MainUW` and `SwUW` that the hand `mainW`/`swW` (`Spike/Lib/X64Ret0I.lean`)
give through `mainUW_ofW`/`swUW_ofW`, the user function's interface taken
from the hand one. The twin of `Spike/Test/A64RtMainU.lean`.
-/
import Spike.Lib.Rt.X64RtMainU
import Spike.Lib.Rt.X64SegsRet0
import Spike.Test.X64RtW

namespace Spike.Lib.X64.Rt.Test

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib.X64Consumer Spike.Lib.X64
open Spike.Lib.X64.Rt Spike.Lib.X64.Rt.MainU Spike.Lib.X64.Flow.Ret0.Inst
open Spike.Lib.X64.Flow.Ret0 (MainG StackM limA swFS CallerCells tpOf)
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End ret0Words_mapped ret0_lays)
open SccCode (ret0Λ ret0Cells)

/-- **`ret0.x`'s `scc_rt_main` phase facts.** -/
theorem ret0_mainPh : MainPh okPc ph labT ret0MC where
  hd := by decide +kernel
  lea := by decide +kernel
  ld := by decide +kernel
  cmp := by decide +kernel
  fr := by decide +kernel
  call := by decide +kernel
  ex := by decide +kernel
  svc := by decide +kernel

/-- **`ret0.x`'s switch phase facts.** -/
theorem ret0_swPh : SwPh okPc ph labT where
  sw := by decide +kernel
  xor := by decide +kernel
  main := by decide +kernel

/-- The TCB's limit word at `n0 = 0` is mapped for reading. -/
theorem ret0_limMapped : Scc.Sem.Kernel.mapped (K0 ret0Λ) false ⟨limA (tpOf 134217736#64), 8⟩ = true := by
  rw [Spike.Lib.X64.Flow.Ret0.Inst.limA_tcb0]; exact (ret0Words_mapped (by decide)).2.1

variable {rS : Range} {c0 : Ctl} {ms : MemSide isa}

/-- **The hand `mainW`'s `MainUW` from the generic one**: the same statement
as `mainUW_ofW (mainW hC0 h8 hok hsub hfit ms)`. -/
example (hC0 : CFacts ret0Λ ret0Λ.static c0) {top : BitVec 64} (h8 : top.toNat % 8 = 0)
    (hok : (swR top (-80) 0).OK) (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    MainUW (Wr rS) (Kr rS) ret0Exe ret0End ((swR top (-80) 0).callee (-8 - 0) (-72) 8)
      (fun m => swFS rS top (limA (tpOf 134217736#64)) top m ∧ CallerCells (swR top (-80) 0) (-8 - 0) (-72) 8 m)
      ms ret0MC (ret0Post c0) ⟨top - 8#64, tpOf 134217736#64, c0⟩ := by
  have hR := Region.callee_ok (kc := -8 - 0) (lo' := -72) (hi' := 8) hok (by show (-80 : Int) ≤ _; decide)
    (by decide) (by show _ < (0 : Int); decide) (by show _ ≤ (0 : Int); decide)
  have hb0 : (((swR top (-80) 0).callee (-8 - 0) (-72) 8).base.toNat : Int) = top.toNat + (-8 - 0) :=
    Region.callee_base hok (by show (-80 : Int) ≤ _; decide) (by decide) (by show _ < (0 : Int); decide)
  exact mainUW_gen ret0_instOk ret0_mainUIn hC0 (fun _ _ h => h.1 ▸ hC0) ret0_mainPh hR (by omega)
    (by show (-72 : Int) ≤ _; decide) (by show (0 : Int) ≤ 8; decide) (by show (-72 : Int) % 8 = 0; decide)
    (by show (8 : Int) % 8 = 0; decide) (by decide) (by decide) (by decide) (by decide) ret0_limMapped
    (fun _ h => h.1.1.2) hsub hfit
    (fun _ h => stackOff_callee hok h8 (by show (-80 : Int) % 8 = 0; decide) (by show (0 : Int) % 8 = 0; decide)
      (by show (-80 : Int) ≤ _; decide) (by decide) (by show _ < (0 : Int); decide) (by decide) h.1.2 h.2)

/-- **The hand `swW`'s `SwUW` from the generic one**, the user function's
interface the hand one's: the same statement as `swUW_ofW … (swW …)`. -/
example {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} (hC0 : CFacts ret0Λ ret0Λ.static c0) {R : Region}
    {F : MachineData → Prop} {top : BitVec 64} (h8 : top.toNat % 8 = 0) (hok : (swR top (-80) 0).OK)
    (hsub : rS.Sub ret0Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64) :
    SwUW (Wr rS) (Kr rS) p lbl ret0Exe ret0End R (fun m => F m ∧ StackM rS m) ms rS 134217736#64 top c0 80 ret0MC 24
      16 (ret0Post c0) :=
  swUW_gen (Post := ret0Post c0) ret0_instOk Flow.Ret0.ret0_startTailIn ret0_mainUIn hC0 (fun _ _ h => h.1 ▸ hC0)
    ret0_mainPh ret0_swPh h8 hok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ret0_limMapped hsub hfit
    (swUW_ofW (R := R) (F := fun m => F m ∧ StackM rS m) ret0_lays rfl
      (swW (R := R) hC0 rfl h8 hok hsub hfit ms)).user

end Spike.Lib.X64.Rt.Test

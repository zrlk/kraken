/-
**Oracle of `Spike/Lib/A64TailNoFul.lean` on `ret0`**: `ret0_correct_parsed`
(`Spike/Lib/A64Ret0Correct.lean`) restated through `correctA64P'` with
`WriteNoProm` by `writeNoProm_of_tail` from the tail `Dt` false
(`tailNoFul_of_noWrite`), from the fragment's `NoWrite`.
-/
import Spike.Lib.A64CorrectP
import Spike.Lib.A64TailNoFul
import Spike.Lib.A64Ret0Correct

namespace Spike.Test.A64Ret0Tail

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.Link Scc.Cert.Link.A64 Scc.Cert.WideA64
open Spike.Lib.A64Consumer
open Spike.Lib.Consumer1
open Spike.Lib (Frag)
open SccCode (ret0Λ ret0Prog ret0Secs)
open Spike.Lib.Ret0Src
open Spike.Lib.A64.Flow.Ret0.Correct
open Spike.Lib.A64.Flow.Ret0.Inst (μ0 own)
open Spike.Lib.A64.Flow.Ret0.Mem (ret0Exe ret0End ret0F)
open Spike.Lib.A64.Flow (At)

/-- **`ret0_correct_parsed` with `WriteNoProm` from the empty tail**. -/
theorem ret0_correct_parsed_tail {B : Budget} {arch : WeakMem.Arch} {ls0 : Lsize} {inv : Frag isaLSE2} {rS : Range}
    {Tk : State → Prop}
    (hE : ∀ s c, At ret0Exe ret0End R0 ret0F entry0 s c → inv s c)
    (hN : Nodes ret0Λ ret0Src μ0 (fun _ => True) ret0G own (IOf ret0Λ.static ls0 inv))
    (hT : TakePath ret0Λ ret0Src μ0 (IOf ret0Λ.static ls0 inv) rS Tk)
    (hA : AbortPath μ0 (IOf ret0Λ.static ls0 inv) (fun _ => False))
    (htk0 : ¬ Tk ret0S0)
    (hnw : NoWrite (IOf ret0Λ.static ls0 inv)) :
    Correct TPar (SrcSem.source (ret0P arch) ret0Src) ret0Λ B (ret0Prog, ret0Secs) := by
  rw [← ret0_marksP] at hN hT hA
  exact correctA64P' (lsize := ls0) (name := fun _ => "") SccCode.ret0Λ_image (ret0_ss ls0 _)
    SccCode.ret0_wide ⟨rfl, rfl, hE _ _ ret0_entry⟩ ⟨_, ret0_loadP⟩ (.none (ret0P_hooks arch)) (ret0P_init arch) hN
    (ret0_safe arch _) hT htk0 ret0_own0
    (writeNoProm_of_tail (tailNoFul_of_noWrite hnw)) (fun _ => trivial) SccCode.ret0Λ_wf ret0_G0
    ret0_Gpl hA (fun h => h)

/-- info: 'Spike.Test.A64Ret0Tail.ret0_correct_parsed_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ret0_correct_parsed_tail

end Spike.Test.A64Ret0Tail

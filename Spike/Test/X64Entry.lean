/-
**Oracle of the parametric x86-64 `_start` on `ret0`**
(`Spike/Lib/Rt/X64Entry.lean`): the hand `entry_segW`
(`Spike/Lib/X64Ret0I.lean`) is `entry_segW'` at `ret0Cells` with the code
check `entryIn` (by `decide`) and the hand nodes' obligations (`EntryW`
from `nodeW_fi_pre`, `nodeW_and_pre` and `blkW_pre`). The x86-64 twin of
ARM's `entry_segW'` oracle (`Spike/Lib/A64Ret0I.lean`).
-/
import Spike.Lib.Rt.X64Entry
import Spike.Lib.X64Ret0I

namespace Spike.Lib.X64.Rt.EntryTest

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0 Spike.Lib.X64.Flow.Ret0.Inst
open Spike.Lib.X64.Flow.Ret0.Mem (ret0Exe ret0End ret0_lays ret0F)
open SccCode (ret0Λ ret0Cells)
open Spike.Lib.X64Consumer
open Scc.Cert.Rt.X64 (blockAtB)
open Spike.Lib.X64.Rt (entryN0 entryN1 entryN2 EntryW entry_segW')

/-- `_start`'s code check holds on `ret0`. -/
theorem ret0_entryIn : Spike.Lib.X64.Rt.Code.Start.entryIn ret0Cells = true := by decide +kernel

/-- **The hand `entry_segW`, by the generic theorem.** -/
example {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} (c0 : Ctl)
    (hC0 : CFacts ret0Λ ret0Λ.static c0) {rS : Scc.Sem.Range} (hsub : rS.Sub ret0Λ.stackPool) {Q : Frag isa}
    (hS : ∀ F' : MachineData → Prop, FStable (Inst.entryR.callee (-8) (-296) 8) F' → KStable (Kr rS) F' →
      (∀ m, F' m → ret0F m) → ∀ Q' : Frag isa,
      SegW (Wr rS) (Kr rS) p lbl ms (At ret0Exe ret0End (Inst.entryR.callee (-8) (-296) 8) F' (startN0 labT c0)) Q') :
    SegW (Wr rS) (Kr rS) p lbl ms (At ret0Exe ret0End Inst.entryR ret0F (entry0N c0)) Q := by
  have hb0 : blockAtB ret0Cells "_start" 0 [(FI.toDir (.xor_rr32_self .rbp), 2)] = true := by decide +kernel
  have hb1 : blockAtB ret0Cells "_start" 2 [(andRsp (-16), 4)] = true := by decide +kernel
  have hb2 : blockAtB ret0Cells "_start" 6 startCallB = true := by decide +kernel
  have hW : EntryW (Wr rS) (Kr rS) ret0Exe ret0End Inst.entryR ret0F labT c0 :=
    ⟨nodeW_fi_pre hb0 (ofNat_zero' _) rfl (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel) (by decide +kernel)
        (by decide +kernel),
      nodeW_and_pre hb1 rfl rfl (fun _ _ hJ => hJ ▸ hC0) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      blkW_pre (n := entryN2 labT c0) (l := "_start") (off := 6) (dead := fun _ => false) (ra := 0) hb2
        (ofNat_add' _ 2 4) startCallB_ok Inst.entryR_ok (by decide) (by decide) (fun _ _ hJ => hJ ▸ hC0)
        (by decide +kernel) (fun _ _ _ k hk hr => (noRet_false (by decide +kernel) k hk hr).elim)
        (fun _ _ _ => rfl) (by decide +kernel)⟩
  have h := entry_segW' (p := p) (lbl := lbl) (ms := ms) (Q := Q) ret0_lays rfl ret0_entryIn ret0F_stable
    Inst.entryR_ok Inst.entryR_al (by decide) (by decide) (TakeK.kstable fun _ _ h => ret0F_takeMem hsub h)
    (fun _ _ hk _ k hk' => by obtain ⟨pm, he⟩ := hk.mem; rw [he]; exact loadInt_takeMem (Inst.rS_of_sub hsub k hk'))
    c0 (by rw [ret0_labT]; exact hW) (by rw [ret0_labT]; exact hS)
  rw [ret0_labT] at h
  exact h

end Spike.Lib.X64.Rt.EntryTest

import Scc.Cert.Rt.A64PrintLMs
import Spike.Lib.Rt.Seg.A64MorestackCall

/-!
# The segment theorems of `Scc.Cert.Rt.A64PrintLMs`

The theorems of `Scc/Cert/Rt/A64PrintLMs.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `hms_printL`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.A64PrintLMs`.
-/

namespace Scc.Cert.Rt.A64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64}

/-- **`wc_printL`'s `hms`**, given the calls to `scc_rt_grow` and
`scc_rt_stack_release` (`seg_ms_call`). -/
theorem hms_printL {γ : Sort _} {Rg : γ → Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}
    {prog : List Directive} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe prog kp)
    (hend : endPc = endOf exe prog kp) (hprog : morestackIn prog = true)
    (hR : ∀ g, (Rg g).OK) (hF : ∀ g, FStable (Rg g) (Fg g)) (hal : ∀ g, (Rg g).base.toNat % 16 = 0)
    (hlo : ∀ g, (Rg g).lo ≤ -128) (hhi : ∀ g, 0 ≤ (Rg g).hi)
    (hsp : (_root_.Executable.labels exe).label ".L21_wc_printL.sp_check" =
      Int64.ofBitVec (printLRet (_root_.Executable.labels exe).label))
    (hgrow : ∀ g need, Seg p lbl ms
      (At exe endPc (msR (Rg g) (-80)) (Fms (Fg g) (Rg g) (-80) (fp g) ra)
        (nGrow (_root_.Executable.labels exe).label (msR (Rg g) (-80)) c0
          (printLRet (_root_.Executable.labels exe).label) need))
      (fun s c => ∃ v ob osz, At exe endPc (msR (Rg g) (-80))
        (Moved (msR (Rg g) (-80)) (printLRet (_root_.Executable.labels exe).label)
          (F'ms Rg Fg fp (fun _ => ra) (msR (Rg g) (-80)) (-80)) v)
        (nG1 (_root_.Executable.labels exe).label (msR (Rg g) (-80)) c0 v ob osz) s c))
    (hrel : ∀ g v ob osz, Seg p lbl ms
      (At exe endPc (swR v 0 16) (F'ms Rg Fg fp (fun _ => ra) (msR (Rg g) (-80)) (-80) v)
        (nRel (_root_.Executable.labels exe).label c0 (printLRet (_root_.Executable.labels exe).label) ob osz))
      (At exe endPc (swR v 0 16) (F'ms Rg Fg fp (fun _ => ra) (msR (Rg g) (-80)) (-80) v)
        (nR1 (_root_.Executable.labels exe).label c0 (printLRet (_root_.Executable.labels exe).label))))
    (g : γ) :
    Seg p lbl ms (At exe endPc (Rg g) (Fg g) (PrintL.N (_root_.Executable.labels exe).label c0 (fp g) ra .ms))
      (fun s c => ∃ g', At exe endPc (Rg g') (Fg g')
        (PrintL.N (_root_.Executable.labels exe).label c0 (fp g') ra .spc) s c) :=
  seg_ms_call (a := fp) (b := fun _ => ra) (kc := -80)
    (nC := fun g => PrintL.N (_root_.Executable.labels exe).label c0 (fp g) ra .ms)
    (nX := fun g => PrintL.N (_root_.Executable.labels exe).label c0 (fp g) ra .spc) hp hend hprog hR hF
    (fun g => by have := hlo g; omega) hhi (by decide) (by decide) hal
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ ⟨⟨hc, h16, h8⟩, h30⟩ => ⟨hc, h16, h8, h30⟩)
    (fun _ => ⟨hsp, rfl⟩) (fun _ _ h16 h8 => ⟨rfl, h16, h8⟩) hgrow hrel g

end Scc.Cert.Rt.A64.Morestack

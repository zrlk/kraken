import Scc.Cert.Rt.X64PrintLMs
import Spike.Lib.Rt.Seg.X64MorestackCall

/-!
# The segment theorems of `Scc.Cert.Rt.X64PrintLMs`

The theorems of `Scc/Cert/Rt/X64PrintLMs.lean` whose statements are stated over the
untrusted segment predicate (`Spike.Lib.Seg`, `MemSide`), moved out of the
trusted tree unchanged (same namespace, names and statements; FENCE1
follow-up 2): `hms_printL`. The definitions, code
data and decided checks they use stay in `Scc.Cert.Rt.X64PrintLMs`.
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64
variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64}

/-- **`wc_printL`'s `hms`**, given the trampoline's code and the calls to
`scc_rt_grow` and `scc_rt_stack_release` (`seg_ms_call`). -/
theorem hms_printL {γ : Sort _} {Rg : γ → Region} {Fg : γ → MachineData → Prop} {rb : γ → BitVec 64}
    (hcode : Code exe endPc)
    (hR : ∀ g, (Rg g).OK) (hF : ∀ g, FStable (Rg g) (Fg g))
    (hlo : ∀ g, (Rg g).lo ≤ -120) (hhi : ∀ g, 16 ≤ (Rg g).hi)
    (hx18 : (_root_.Executable.labels exe).label ".Lwc_printL.x18" =
      (_root_.Executable.labels exe).label ".Lwc_printL.stk" + 18)
    (hgrow : ∀ g need, Seg p lbl ms
      (At exe endPc (msR (Rg g) (-56)) (Fms (Fg g) (Rg g) (-56) (rb g) ra)
        (nGrow (_root_.Executable.labels exe).label (msR (Rg g) (-56)) c0
          (printLRet (_root_.Executable.labels exe).label) need ((Rg g).addr 0)))
      (fun s c => ∃ v ob osz, At exe endPc (msR (Rg g) (-56))
        (Moved (msR (Rg g) (-56)) (printLRet (_root_.Executable.labels exe).label) ((Rg g).addr 0)
          (F'ms Rg Fg rb (fun _ => ra) (msR (Rg g) (-56)) (-56)) v)
        (nG1 (_root_.Executable.labels exe).label (msR (Rg g) (-56)) c0 v ob osz) s c))
    (hrel : ∀ g v ob osz, Seg p lbl ms
      (At exe endPc (rN v) (F'ms Rg Fg rb (fun _ => ra) (msR (Rg g) (-56)) (-56) v)
        (nRel (_root_.Executable.labels exe).label c0 (printLRet (_root_.Executable.labels exe).label)
          ((Rg g).addr 0 + (v - (msR (Rg g) (-56)).addr 0)) ob osz))
      (At exe endPc (rN v) (F'ms Rg Fg rb (fun _ => ra) (msR (Rg g) (-56)) (-56) v)
        (nR1 (_root_.Executable.labels exe).label c0 (printLRet (_root_.Executable.labels exe).label)
          ((Rg g).addr 0 + (v - (msR (Rg g) (-56)).addr 0)))))
    (g : γ) :
    Seg p lbl ms (At exe endPc (Rg g) (Fg g) (PrintL.N (_root_.Executable.labels exe).label c0 (rb g) ra .ms))
      (fun s c => ∃ g', At exe endPc (Rg g') (Fg g')
        (PrintL.N (_root_.Executable.labels exe).label c0 (rb g') ra .x18) s c) :=
  seg_ms_call (a := rb) (b := fun _ => ra) (kc := -56)
    (nC := fun g => PrintL.N (_root_.Executable.labels exe).label c0 (rb g) ra .ms)
    (nX := fun g => PrintL.N (_root_.Executable.labels exe).label c0 (rb g) ra .x18) hcode hR hF
    (fun g => by have := hlo g; omega) hhi (by decide) (by decide)
    (fun _ => ⟨rfl, rfl⟩) (fun _ _ _ ⟨⟨hc, h0, h8⟩, hra⟩ => ⟨hc, h0, h8, hra⟩)
    (fun _ => ⟨by simp [PrintL.N, hx18], rfl⟩) (fun _ _ h0 h8 => ⟨rfl, h0, h8⟩) hgrow hrel g

end Scc.Cert.Rt.X64.Morestack

import Scc.Cert.Rt.X64MorestackCall
import Spike.Lib.X64PrintL

/-!
# `wc_printL`'s call to `scc_rt_morestack` on x64

`hms_printL`: the given node `hms` of `Spike.Lib.X64.PrintL.seg_printL`
(the grow stub's call to `scc_rt_morestack`, from `.ms` to `.x18` at some
ghost), by `seg_ms_call`: the stub calls with the return address at offset
`-56`, the frame record `(rb g, ra)` at `0`, `8`, and the return address
`.stk + 18`, which is the label `.x18` (`hx18`).
-/

namespace Scc.Cert.Rt.X64.Morestack

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Spike.Lib Spike.Lib.X64

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {c0 : Ctl} {ra : BitVec 64}

/-- The grow stub's return address: `.stk` plus its three instructions. -/
abbrev printLRet (lab : Label → Int64) : BitVec 64 := (lab ".Lwc_printL.stk" + 18).toBitVec

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

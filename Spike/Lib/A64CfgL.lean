/-
**Whole functions with the load-or-stutter row on AArch64** (main's half): `Spike/Lib/A64Cfg.lean`'s moving-frame graph over `SegL`
(`Spike/Lib/SegLd.lean`), and the node at a spin-wait's acquire load.

- `seg_fixL`, `seg_movedL`, `fn_seg_gL`: `seg_fix`, `seg_moved`, `fn_seg_g`
  over `SegL`; a `Seg` node enters through `Seg.toL`.
- `ldarDir t b`: `ldar Xt, [Xn]`.
- `ldarSt_nd`: **the node at `ldar Xt, [Xn]` matched by the source's
  acquire load `let x = load acq a in e` with the load-or-stutter row**
  (`OutL.ldSt`): `Xn` holds the word's address `A`, which is not private
  memory under the frame condition (`hdm`); a value read whose low 64 bits
  are not `V` lands with the source unchanged (it stutters at its load), the
  value `V` lands with `x` bound to a word the relation lets the source read.
-/
import Spike.Lib.A64Ret0
import Spike.Lib.SegLd

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib.A64.Flow.Ret0 (land_ldStep)

/-! ## Functions whose frame moves, with the load-or-stutter row -/

section MovingL

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {γ ι κ : Sort _} {Rg : γ → Region} {Fg : γ → MachineData → Prop}
  {N : γ → ι → ND} {E : γ → κ → ND}

/-- **A node of a fixed frame**, with the load-or-stutter row. -/
theorem seg_fixL {P : Frag isaLSE2} (g : γ) (h : SegL p lbl ms P (Next exe endPc (Rg g) (Fg g) (N g) (E g))) :
    SegL p lbl ms P (NextG exe endPc Rg Fg N E) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨j, h⟩ => .inl ⟨g, j, h⟩) fun ⟨x, h⟩ => .inr ⟨g, x, h⟩

/-- **A given node that moves the frame**, with the load-or-stutter row. -/
theorem seg_movedL {P : Frag isaLSE2} (j : ι)
    (h : SegL p lbl ms P (fun s c => ∃ g, At exe endPc (Rg g) (Fg g) (N g j) s c)) :
    SegL p lbl ms P (NextG exe endPc Rg Fg N E) :=
  h.mono_post fun _ _ ⟨g, h⟩ => .inl ⟨g, j, h⟩

/-- **A whole function whose frame may move**, with the load-or-stutter
row. -/
theorem fn_seg_gL (h : ∀ g i, SegL p lbl ms (At exe endPc (Rg g) (Fg g) (N g i)) (NextG exe endPc Rg Fg N E))
    (g0 : γ) (i0 : ι) :
    SegL p lbl ms (At exe endPc (Rg g0) (Fg g0) (N g0 i0))
      (fun s c => ∃ g x, At exe endPc (Rg g) (Fg g) (E g x) s c) :=
  (SegL.cfg (fun gi : PProd γ ι => At exe endPc (Rg gi.1) (Fg gi.1) (N gi.1 gi.2)) fun gi =>
      (h gi.1 gi.2).mono_post fun _ _ h => h.elim (fun ⟨g, j, h⟩ => .inl ⟨⟨g, j⟩, h⟩) .inr).mono_pre
    fun _ _ h => ⟨⟨g0, i0⟩, h⟩

end MovingL

/-! ## The acquire load of a spin-wait -/

/-- `ldar Xt, [Xn]`. -/
def ldarDir (t b : XReg) : Directive :=
  .instr ⟨.W64, .LDAR .acq false .W64 (.low (.reg t) .W64) (.low (.reg b) .W64)⟩

section Ldar

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **The node at `ldar Xt, [Xn]` with the load-or-stutter row**: `Xn`
holds `A`, the address of the source's word (`ValRep`, an untagged
locative) at its acquire load `let x = load acq a in e`; `A` is not private
memory under `F` (`hdm`). A value read that is not `V` lands at the node
after the load with the source unchanged; `V` lands with the source's load
taken (`x` bound to any word `ms.rd` admits that represents `V`). -/
theorem ldarSt_nd {n : ND} {t b : XReg} {A : BitVec 64} {V : Nat} (hF : FStable R F)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc [ldarDir t b])
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hedge : ∀ m σ c, Abs R n.o m σ → F m → n.J σ c →
      (σ.regs.getXReg b).toBitVec = A ∧
      ∃ x a e ty w, c.term = .let_ x (.load true a) e ∧ TermRun.evalAt c.env a = some (ty, [w]) ∧
        ValRep lbl w.val A.toNat ∧ (∃ sa, w.val = .loc sa 0) ∧
        (∀ v : BitVec 64, v.toNat ≠ V → Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ c) ∧
        (∀ (v : BitVec 64) (w' : TermRun.Word), v.toNat = V → ms.rd w' → ValRep lbl w'.val V →
          Lands N E ⟨n.pc + Int64.ofNat 4, n.o.kill t, ldStep t v σ⟩ ⟨e, (x, loadTy ty, [w']) :: c.env, none⟩)) :
    SegL p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) := by
  refine SegL.step fun s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ => ?_
  have hc : CellAt s (ldarDir t b) 4 := (hcode s he hn).cell (j := 0) rfl rfl rfl (by rw [hpc]; simp)
  obtain ⟨hb, x, a, e, ty, w, ht, hev, hv, htag, hne, heq⟩ := hedge _ σ c hA hD hJ
  have hb' : (s.st.1.regs.getXReg b).toBitVec = A := by rw [hA.regs]; exact hb
  have hex := exec_ldar_agrees hc (by rw [hb']; exact hdm _ hD) (agrees_of_decls hdc _ _)
  rw [hb'] at hex
  refine .ldSt .acq A _ x a e ty w V hex ht hev hv (fun v hvV => ?_) (fun v w' hvV hr hr' => ?_) htag
  · exact land_ldStep hF he hn hdc hpc hA hD (hne _ hvV)
  · exact land_ldStep hF he hn hdc hpc hA hD (heq _ w' hvV hr hr')

end Ldar

end Spike.Lib.A64.Flow

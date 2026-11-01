/-
**hello's level 1 from rodata's landing at main's thread pointer** (AArch64): `Level1.land_segWS` with the landing's
thread pointer `t` (`StartH0H1.RdLandH`'s `TP` conjunct, kept
through level 0 by `HelloM.hello_main_pre_segWSTF`) carried into `wc_rodata`'s `.sp0` invariant, so that
`MainWcPS.hJpT` holds by construction.

`MainWcPS.hJpT` asks `Jp σ0 c → σ0.regs.TPIDR_EL0 = t` of the `.sp0` invariant; the landing's `Jp` (any `Jp` the
landings imply, e.g. `Level1.JpL`) says nothing about the thread pointer, which is a fact of the concrete state
(`TP t s`). At `.sp0` the abstract registers are the state's (`Abs.regs`), so `JpT Jp t` (`Jp` and the thread
pointer) holds there whenever `Jp` does and `TP t s`.

- `JpT`: `Jp` at thread pointer `t`.
- `at_s0_tp`: `wc_rodata`'s `.sp0` at `Jp` and `TP t s` is at `JpT Jp t`.
- `land_segWST`: from `LandF ∧ TP t` at `[fr]` to `wc_main`'s heap abort at `[]`, given `MainWcPS` at `JpT Jp t`
  (its `hJpT` is `jpT_tp`).
- `jpT_tp`: `MainWcPS.hJpT` at `JpT Jp t`.
-/
import Spike.Lib.A64HelloLevel1

namespace Spike.Lib.A64.HelloPh.Level1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (abi)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib (FragS Frag MemSide Region SegWS)
open Spike.Lib.A64.Flow (FStable At enter leave CKept)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN pN)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **`Jp` at thread pointer `t`**: `wc_rodata`'s `.sp0` invariant with `MainWcPS.hJpT`'s fact. -/
def JpT (Jp : FAS → Ctl → Prop) (t : UInt64) (σ : FAS) (c : Ctl) : Prop :=
  Jp σ c ∧ σ.regs.TPIDR_EL0 = t

/-- **`MainWcPS.hJpT` at `JpT Jp t`**. -/
theorem jpT_tp {Jp : FAS → Ctl → Prop} {t : UInt64} : ∀ σ0 c, JpT Jp t σ0 c → σ0.regs.TPIDR_EL0 = t :=
  fun _ _ h => h.2

section Gen

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {ms₀ : MemSide isaLSE2} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`wc_rodata`'s `.sp0` at `Jp` and thread pointer `t` is at `JpT Jp t`** (the abstract registers are the
state's, `Abs.regs`). -/
theorem at_s0_tp {lab : Label → Int64} {Jp Jp' J1 J2 J2' J3 J4 J5 Jp'' J1' J2'' J2''' J3' J4' J5' : FAS → Ctl → Prop}
    {t : UInt64} {s : State} {c : Ctl}
    (h : At exe endPc R F (pN lab Jp Jp' J1 J2 J2' J3 J4 J5 .s0) s c) (ht : TP t s) :
    At exe endPc R F (pN lab (JpT Jp t) Jp'' J1' J2'' J2''' J3' J4' J5' .s0) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hF, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hF, hJ, by rw [← hA.regs]; exact ht⟩

/-- **Level 1 from rodata's landing at thread pointer `t` to `wc_main`'s box allocation's heap abort**
(module doc): `land_segWS`'s route (`StartWcS.xa_post`, `MainGlueS.main_wc_segWS`) with `.sp0` at `JpT Jp t`
(`at_s0_tp`), so `MainWcPS`'s `hJpT` is `jpT_tp`. -/
theorem land_segWST (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hJp : ∀ (q : AG ms₀ (_root_.Executable.labels exe).label) σx σ c0 c, (Ea ms₀ q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label J0 J1 .call).J σ c0 →
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms₀ q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC (JpT Jp t) Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWS W K p lbl ms (Frag.at (fun s c => LandF ms₀ exe endPc R F J0 J1 m0 σC l b w s c ∧ TP t s) [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXH (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) .abort) s c ∧ TP t s) []) :=
  (Spike.Lib.A64.HelloPh.MainGlueS.main_wc_segWS hK hK' hp hend hD hD16 hF hR hal hlo hloD hhi hfr hP
    hmem0).mono_pre fun _ _ _ ⟨⟨⟨q, _, hFF, hkeep, hA⟩, ht⟩, hfs⟩ =>
      ⟨at_s0_tp (Spike.Lib.A64.HelloPh.StartWcS.xa_post (J0 := fun _ => J0) (J1 := fun _ => J1) (Jp' := Jp')
        (J1' := Jx1) (J2 := J2) (J2' := J2') (J3 := J3) (J4 := J4) (J5 := J5) hFF hkeep (hJp q) hA) ht, hfs⟩

/-- **`land_segWST` at the canonical `.sp0` invariant `JpL`** (`hJp` by `jpL_of`): only `MainWcPS` at
`JpT (JpL …) t` and `hmem0` are left. -/
theorem land_segWSL (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC
      (JpT (JpL (R := R) ms₀ (_root_.Executable.labels exe).label J0 J1 l b w) t) Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWS W K p lbl ms (Frag.at (fun s c => LandF ms₀ exe endPc R F J0 J1 m0 σC l b w s c ∧ TP t s) [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXH (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) .abort) s c ∧ TP t s) []) :=
  land_segWST hK hK' hp hend hD hD16 hF hR hal hlo hloD hhi hfr (fun q => jpL_of q) hP hmem0

end Gen

end Spike.Lib.A64.HelloPh.Level1

/-- info: 'Spike.Lib.A64.HelloPh.Level1.jpT_tp' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.jpT_tp

/-- info: 'Spike.Lib.A64.HelloPh.Level1.at_s0_tp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.at_s0_tp

/-- info: 'Spike.Lib.A64.HelloPh.Level1.land_segWST' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.land_segWST

/-- info: 'Spike.Lib.A64.HelloPh.Level1.land_segWSL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.land_segWSL

/-
**hello's level 1 to `wc_main`'s heap abort with its spills** (AArch64): the twins of
`MainGlueS.main_wc_segWS` and `Level1.land_segWST` / `Level1.land_segWSL` (`Spike/Lib/A64HelloLevel1T.lean`)
with the heap abort at `HelloWc.wXA` (`Spike/Lib/A64HelloWcPreA.lean`): the abort's abstract state keeps
`wc_main`'s spill slots `-144 … -112` (the call's entry witness's `X0 … X4`), so the abort-path placement of
`HabCtlHS` can be read off the abort state.

- `main_wc_segWSA`: `main_wc_segWS` through `HelloWc.hello_wc_entry_segJrA`.
- `land_segWSTA`, `land_segWSLA`: `land_segWST`, `land_segWSL` through `main_wc_segWSA`.

The premises are `main_wc_segWS`'s / `land_segWST`'s / `land_segWSL`'s, unchanged.
-/
import Spike.Lib.A64HelloLevel1T
import Spike.Lib.A64HelloWcPreA

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
open Spike.Lib.A64.Flow.HelloWc (wXA)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

section Gen

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {ms₀ : MemSide isaLSE2} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}

/-- **`MainGlueS.main_wc_segWS` with the heap abort at `wXA`** (`HelloWc.hello_wc_entry_segJrA`): from
`wc_rodata`'s `.sp0` under its frame to `wc_main`'s first allocation's heap abort with its spills at `[]`. -/
theorem main_wc_segWSA (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
    (hp : Lays exe SccCode.helloProg kp)
    (hend : endPc = endOf exe SccCode.helloProg kp) {D : Int} (hD : 304 ≤ D) (hD16 : D % 16 = 0)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 0 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWS W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 J5 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  Spike.Lib.A64.Flow.HelloM.hello_main_post_segWST hp hend hK' (by omega) hD16 hF hR hal hlo hloD hhi hfr
    hP.hJpT hP.hW hP.hra hP.hmem hP.hr0 hP.h1 hP.h2 hP.hr2 hP.h3 hP.h4 hP.hfen hP.hedge
    (Q := fun m1 σ1 s c => At exe endPc (wcR R D) (wcF R D F m1 σ1)
      (wXA (ms []) (_root_.Executable.labels exe).label
        (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s)
    fun m1 σ1 hR' hal' hF' =>
      Spike.Lib.A64.Flow.HelloWc.hello_wc_entry_segJrA hK hp hend hF' hR' hal' (show -D ≤ -304 by omega)
        (show (0 : Int) ≤ 0 by decide) (fun _ _ h => h.2.1) (hP.hWp m1 σ1) (hP.hWs m1 σ1) hP.hlim hP.hloc hP.hq
        hmem0 hP.hbox hP.hcell0 (hP.hxa m1 σ1)

/-- **`land_segWST` with the heap abort at `wXA`** (`main_wc_segWSA`). -/
theorem land_segWSTA (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
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
        (wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  (main_wc_segWSA hK hK' hp hend hD hD16 hF hR hal hlo hloD hhi hfr hP
    hmem0).mono_pre fun _ _ _ ⟨⟨⟨q, _, hFF, hkeep, hA⟩, ht⟩, hfs⟩ =>
      ⟨at_s0_tp (Spike.Lib.A64.HelloPh.StartWcS.xa_post (J0 := fun _ => J0) (J1 := fun _ => J1) (Jp' := Jp')
        (J1' := Jx1) (J2 := J2) (J2' := J2') (J3 := J3) (J4 := J4) (J5 := J5) hFF hkeep (hJp q) hA) ht, hfs⟩

/-- **`land_segWSL` with the heap abort at `wXA`** (`land_segWSTA` at `JpL`, `hJp` by `jpL_of`). -/
theorem land_segWSLA (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
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
        (wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  land_segWSTA hK hK' hp hend hD hD16 hF hR hal hlo hloD hhi hfr (fun q => jpL_of q) hP hmem0

end Gen

end Spike.Lib.A64.HelloPh.Level1

/-- info: 'Spike.Lib.A64.HelloPh.Level1.main_wc_segWSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.main_wc_segWSA

/-- info: 'Spike.Lib.A64.HelloPh.Level1.land_segWSTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.land_segWSTA

/-- info: 'Spike.Lib.A64.HelloPh.Level1.land_segWSLA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.land_segWSLA

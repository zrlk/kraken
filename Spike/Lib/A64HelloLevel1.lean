/-
**hello's level 1 from rodata's landing, generic part** (AArch64, row
`B8-H0R-h1GA`): the segment `H1Gfp.h1StmtHF_of_segWS`'s `hB` asks, from the allocator's landing `Ea`
under `wc_rodata`'s frame `fr` (level 0's hand-off, `StartH0H1.RdLandH`'s shape) to `wc_main`'s box allocation's
heap abort at `[]`.

The landing is the allocator's return past the source's `new` (`Ea ms₀ q l b w`, `ms₀` the memory side the
allocation was taken at, level 0's). Leaving the allocator's region (`StartWcS.xa_post`, `at_leave`), it is
`wc_rodata`'s `.sp0` (`pN … .s0`) at an invariant `Jp` the landings imply (`hJp`); from there
`MainGlueS.main_wc_segWS` (`wc_rodata`'s rest at `[fr]`, its return popping `fr`, `scc_rt_main`'s `.sp0` block,
`wc_main` to its box allocation) inside the level's `W` under the level's memory sides `ms`.

- `LandF`: the landing at the caller's state `m0`, `σC`, under `fr` (`RdLandH`'s body, any `ms₀`, `R`, `F`).
- `land_segWS`: from `LandF` to `wc_main`'s heap abort at `[]`, given `MainWcPS` and `hJp`.
- `JpL`, `jpL_of`: the canonical `Jp` (the landings' images at `.sp0`), for which `hJp` holds by definition.
-/
import Spike.Lib.A64HelloStartWcS

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

section Gen

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isaLSE2}
  {ms₀ : MemSide isaLSE2} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : FragS isaLSE2} {K : State → State → Prop} {fr : TermRun.Frame}

/-- **The allocator's landing under `wc_rodata`'s frame** at the caller's state `m0`, `σC` (`RdLandH`'s body):
some call `q` at `ms₀`, a frame condition `F'` inside `wc_rodata`'s and its call context's, the landing `Ea` at
the label `l`, base `b`, words `w`. -/
def LandF (ms₀ : MemSide isaLSE2) (exe : _root_.Executable) (endPc : Int64) (R : Region) (F : MachineData → Prop)
    (J0 J1 : FAS → Ctl → Prop) (m0 : MachineData) (σC : FAS) (l : WeakMem.AllocLabel) (b w : Nat)
    (s : State) (c : Ctl) : Prop :=
  ∃ q : AG ms₀ (_root_.Executable.labels exe).label, ∃ F' : MachineData → Prop,
    (∀ m, F' m → mF R F m0 σC m) ∧
    (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR R) ⟨-48, []⟩ mC σ ∧
      (rN (_root_.Executable.labels exe).label J0 J1 .call).J σ c ∧
      (Spike.Lib.A64.Alloc.N (_root_.Executable.labels exe).label ms₀ q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR R) (-48) (-160) 0 mC m) ∧
    At exe endPc (aR (mR R)) F' (Ea ms₀ q.1 l b w) s c

/-- **The landings' images at `.sp0`**: `wc_rodata`'s state after leaving the allocator at a landing of `q` at
`l`, `b`, `w` (`xa_post`'s `hJp` holds for it by definition, `jpL_of`). -/
def JpL (ms₀ : MemSide isaLSE2) (lab : Label → Int64) (J0 J1 : FAS → Ctl → Prop) (l : WeakMem.AllocLabel)
    (b w : Nat) (σ' : FAS) (c : Ctl) : Prop :=
  ∃ (q : AG ms₀ lab) (σx σ : FAS) (c0 : Ctl), (Ea ms₀ q.1 l b w).J σx c ∧ (rN lab J0 J1 .call).J σ c0 ∧
    (Spike.Lib.A64.Alloc.N lab ms₀ q.1 .e).J (enter (-48) σ) c0 ∧ σ' = leave (aR (mR R)) (-48) σ σx

/-- **`xa_post`'s `hJp` at `JpL`**. -/
theorem jpL_of {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    (q : AG ms₀ lab) :
    ∀ σx σ c0 c, (Ea ms₀ q.1 l b w).J σx c → (rN lab J0 J1 .call).J σ c0 →
      (Spike.Lib.A64.Alloc.N lab ms₀ q.1 .e).J (enter (-48) σ) c0 →
      JpL (R := R) ms₀ lab J0 J1 l b w (leave (aR (mR R)) (-48) σ σx) c :=
  fun σx σ c0 _ hx h1 h2 => ⟨q, σx, σ, c0, hx, h1, h2, rfl⟩

/-- **Level 1 from rodata's landing to `wc_main`'s box allocation's heap abort** (module doc): the landing
(`LandF` at `[fr]`) is `wc_rodata`'s `.sp0` at `Jp` (`StartWcS.xa_post`, `hJp`), then
`MainGlueS.main_wc_segWS`. -/
theorem land_segWS (hK : (ms []).K = some abi) (hK' : (ms [fr]).K = some abi) {kp : Nat}
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
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWS W K p lbl ms (Frag.at (LandF ms₀ exe endPc R F J0 J1 m0 σC l b w) [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXH (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1) .abort) s c ∧ TP t s) []) :=
  (Spike.Lib.A64.HelloPh.MainGlueS.main_wc_segWS hK hK' hp hend hD hD16 hF hR hal hlo hloD hhi hfr hP
    hmem0).mono_pre fun _ _ _ ⟨⟨q, _, hFF, hkeep, hA⟩, hfs⟩ =>
      ⟨Spike.Lib.A64.HelloPh.StartWcS.xa_post (J0 := fun _ => J0) (J1 := fun _ => J1) (Jp' := Jp')
        (J1' := Jx1) (J2 := J2) (J2' := J2') (J3 := J3) (J4 := J4) (J5 := J5) hFF hkeep (hJp q) hA, hfs⟩

end Gen

end Spike.Lib.A64.HelloPh.Level1

/-- info: 'Spike.Lib.A64.HelloPh.Level1.jpL_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.jpL_of

/-- info: 'Spike.Lib.A64.HelloPh.Level1.land_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Level1.land_segWS

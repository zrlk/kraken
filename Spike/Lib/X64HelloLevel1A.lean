/-
**hello's level 1 to `wc_main`'s heap abort with its spills** (x86-64; the twin of
`Spike/Lib/A64HelloLevel1A.lean`, same names): `MainGlueS.MainWcPS`'s fields composed from `wc_rodata`'s `.x15`
through `HelloWc.hello_wc_entry_segJrA` (`Spike/Lib/X64HelloWcPreA.lean`), the heap abort at `HelloWc.wXA` (its
abstract state keeps `wc_main`'s spill slots), and the same from rodata's landing `LandF`.

- `jpL_rbp`: at a landing image `JpL`, `%rbp` is `wc_rodata`'s saved-`%rbp` slot (`StartWcS.xa_post`'s `hbp`).
- `main_wc_segWSA`: from `wc_rodata`'s `.x15` under its frame to `wc_main`'s first allocation's heap abort at `[]`.
- `land_segWSTA`, `land_segWSLA`: the same from the landing `LandF` with `TP t`, at a `.x15` invariant `JpT Jp t`
  the landings imply (`hJp`), and at `JpT (JpL …) t`.

## Differences from the AArch64 version

- The composition is `HelloM.hello_main_post_segWST` at x86-64's `MainWcPS` (its `hbp`, `hsl`; the publication a
  source stutter before `wc_rodata`'s last block), so the segments are `SegWSP` (`Spike/Lib/X64SegWPub.lean`;
  AArch64: `SegWS`). The region premises are x86-64's: `D % 8 = 0`, `8 ≤ R.hi` and no alignment (AArch64:
  `D % 16 = 0`, `0 ≤ R.hi`, `R.base` 16-aligned).
- `.x15` has seven invariants `Jp Jp' J1 J2 J2' J3 J4` (AArch64: `.sp0`, eight, the fence's `J5` included); `J4x`
  (the publication's targets) and `J5` (past them) are `MainWcPS`'s.
- `StartWcS.xa_post` asks `%rbp` at the `.x15` invariant (`hbp`): `land_segWSTA` takes it of `Jp` (`hbpJ`), and
  `land_segWSLA` discharges it at `JpL` by `jpL_rbp` (the allocator's return keeps `%rbp`, `Alloc.Ea`'s `fp`, as at
  its entry, `HelloRd.rN`'s call node). AArch64 has no such premise.
-/
import Spike.Lib.X64HelloLevel1T
import Spike.Lib.X64HelloLevel1
import Spike.Lib.X64HelloMainGlueS

namespace Spike.Lib.X64.HelloPh.Level1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib (FragS Frag MemSide Region)
open Spike.Lib.X64 (FStable At enter leave)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF aR mWC)
open Spike.Lib.X64.Flow.HelloRd (rN pN)
open Spike.Lib.X64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.X64.Flow.HelloWc (wXA)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Alloc (Call Ea)
open Spike.Lib.X64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.X64SegWPub (SegWSP)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

section Gen

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {ms₀ : MemSide isa} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {W : FragS isa} {K : State → State → Prop} {fr : TermRun.Frame}

/-- **`%rbp` at a landing image**: the allocator's return keeps `%rbp` (`Ea`'s `fp`) as at its entry (`N .e`),
where `wc_rodata`'s call node has it at `mR R`'s saved-`%rbp` slot (`rN … .call`). -/
theorem jpL_rbp {lab : Label → Int64} {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {σ : FAS} {c : Ctl} (h : JpL (R := R) ms₀ lab J0 J1 l b w σ c) :
    σ.regs.get64 .rbp = (mR R).addr (-8) := by
  obtain ⟨q, σx, σ', c0, ⟨-, -, -, -, -, -, -, hfp, -⟩, ⟨-, hbp, -⟩, ⟨-, hfp', -⟩, rfl⟩ := h
  refine hbp ▸ ?_
  show σx.regs.get64 .rbp = σ'.regs.get64 .rbp
  have h1 : σx.regs.rbp.toBitVec = σ'.regs.rbp.toBitVec := hfp.trans hfp'.symm
  have h2 : σx.regs.rbp = σ'.regs.rbp := UInt64.toBitVec_inj.mp h1
  simp only [Reg64s.get64, h2]

/-- **`wc_rodata`'s rest and `wc_main` to its heap abort at `wXA`** (`HelloM.hello_main_post_segWST`, then at
every caller's state at `wc_main`'s call `HelloWc.hello_wc_entry_segJrA`): from `wc_rodata`'s `.x15` under its
frame to `wc_main`'s first allocation's heap abort with its spills at `[]`. -/
theorem main_wc_segWSA (hK : (ms []).K = some Scc.Sem.X64.abi) (hK' : (ms [fr]).K = some Scc.Sem.X64.abi)
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) {D : Int} (hD : 304 ≤ D) (hD8 : D % 8 = 0)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 8 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {Jp Jp' J1 J2 J2' J3 J4 J4x J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC Jp Jp' J1 J2 J2' J3 J4 J4x J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWSP W K p lbl ms
      ((At exe endPc (mR R) (mF R F m0 σC)
        (pN (_root_.Executable.labels exe).label Jp Jp' J1 J2 J2' J3 J4 .s0)).at [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  Spike.Lib.X64.Flow.HelloM.hello_main_post_segWST hp hend hK' (by omega) hD8 hF hR hlo hloD hhi hfr
    hP.hJpT hP.hW hP.hbp hP.hra hP.hmem hP.hr0 hP.h1 hP.h2 hP.hr2 hP.h3 hP.h4 hP.hfen hP.hpubx hP.hlocx hP.hedge hP.hsl
    fun m1 σ1 hR' hF' =>
      Spike.Lib.X64.Flow.HelloWc.hello_wc_entry_segJrA hK hp hend hF' hR' (show -D ≤ -304 by omega)
        (show (8 : Int) ≤ 8 by decide) (fun _ _ h => h.2.1) (hP.hWp m1 σ1) (hP.hWs m1 σ1) hP.hlim hP.hloc
        hP.hq hmem0 hP.hbox hP.hcell0 (hP.hxa m1 σ1)

/-- **`main_wc_segWSA` from rodata's landing** (`StartWcS.xa_post`, `at_s0_tp`): from `LandF` with `TP t` at
`[fr]`, at a `.x15` invariant `JpT Jp t` the landings imply (`hJp`) with `%rbp` at `mR R`'s slot (`hbpJ`). -/
theorem land_segWSTA (hK : (ms []).K = some Scc.Sem.X64.abi) (hK' : (ms [fr]).K = some Scc.Sem.X64.abi)
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) {D : Int} (hD : 304 ≤ D) (hD8 : D % 8 = 0)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 8 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {Jp Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hJp : ∀ (q : AG ms₀ (_root_.Executable.labels exe).label) σx σ c0 c, (Ea ms₀ q.1 l b w).J σx c →
      (rN (_root_.Executable.labels exe).label (mR R) J0 J1 .call).J σ c0 →
      (Spike.Lib.X64.Alloc.N (_root_.Executable.labels exe).label ms₀ q.1 .e).J (enter (-48) σ) c0 →
      Jp (leave (aR (mR R)) (-48) σ σx) c)
    (hbpJ : ∀ σ c, Jp σ c → σ.regs.get64 .rbp = (mR R).addr (-8))
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC (JpT Jp t) Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWSP W K p lbl ms (Frag.at (fun s c => LandF ms₀ exe endPc R F J0 J1 m0 σC l b w s c ∧ TP t s) [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  (main_wc_segWSA hK hK' hp hend hD hD8 hF hR hlo hloD hhi hfr hP
    hmem0).mono_pre fun _ _ _ ⟨⟨⟨q, _, hFF, hkeep, hA⟩, ht⟩, hfs⟩ =>
      ⟨at_s0_tp (Spike.Lib.X64.HelloPh.StartWcS.xa_post (J0 := fun _ => J0) (J1 := fun _ => J1) (Jp' := Jp')
        (J1' := Jx1) (J2 := J2) (J2' := J2') (J3 := J3) (J4 := J4) hFF hkeep (hJp q) hbpJ hA) ht, hfs⟩

/-- **`land_segWSTA` at `JpL`** (`hJp` by `jpL_of`, `hbpJ` by `jpL_rbp`). -/
theorem land_segWSLA (hK : (ms []).K = some Scc.Sem.X64.abi) (hK' : (ms [fr]).K = some Scc.Sem.X64.abi)
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) {D : Int} (hD : 304 ≤ D) (hD8 : D % 8 = 0)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hloD : R.lo ≤ -80 - D)
    (hhi : 8 ≤ R.hi) (hfr : fr.σs = []) {m0 : MachineData} {σC : FAS}
    {J0 J1 : FAS → Ctl → Prop} {l : WeakMem.AllocLabel} {b w : Nat}
    {Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr Jr1 : FAS → Ctl → Prop} {t : UInt64}
    (hP : MainWcPS W K p lbl ms exe endPc R D F fr m0 σC
      (JpT (JpL (R := R) ms₀ (_root_.Executable.labels exe).label J0 J1 l b w) t) Jp' Jx1 J2 J2' J3 J4 J4x J5 Jr Jr1 t)
    (hmem0 : ∀ q : Call, q.OKB (ms []) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms []).ctr ∨ ∃ o, o + (ms []).units q.n q.τ ≤ (ms []).cells ∧
        a.toNat = q.hdrAt (ms []) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    SegWSP W K p lbl ms (Frag.at (fun s c => LandF ms₀ exe endPc R F J0 J1 m0 σC l b w s c ∧ TP t s) [fr])
      (Frag.at (fun s c => ∃ m1 σ1, At exe endPc (wcR R D) (wcF R D F m1 σ1)
        (wXA (ms []) (_root_.Executable.labels exe).label
          (wcJ0 (mWC (_root_.Executable.labels exe).label σC Jr1).J σ1)) s c ∧ TP t s) []) :=
  land_segWSTA hK hK' hp hend hD hD8 hF hR hlo hloD hhi hfr (fun q => jpL_of q) (fun _ _ h => jpL_rbp h) hP
    hmem0

end Gen

end Spike.Lib.X64.HelloPh.Level1

/-- info: 'Spike.Lib.X64.HelloPh.Level1.jpL_rbp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.jpL_rbp

/-- info: 'Spike.Lib.X64.HelloPh.Level1.main_wc_segWSA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.main_wc_segWSA

/-- info: 'Spike.Lib.X64.HelloPh.Level1.land_segWSTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.land_segWSTA

/-- info: 'Spike.Lib.X64.HelloPh.Level1.land_segWSLA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1.land_segWSLA

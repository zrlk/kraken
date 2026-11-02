/-
**rodata's fresh-label landing in the root's allocation fragment, at any owned words** (x86-64; the hello
counterpart of `Spike/Lib/X64WakeHxa.lean`'s `hxa_R`): the start segment's `hxa` at the root's memory sides with
the child's stack unmapped (`StartH0U.msUHg own`, any own map `own`). The landing is one the arena hands out
(`AllocLand`, from `Ea`'s allocator facts at `arOf`: offset `8`, `units = n * nWords + 1`), and, with `r1Of`
unmapped, in the fragment `I` at the extended placement by `hRdU` (from level 1's statement:
`StartH0H1.hRdU_of_h1F`).

- `hxa_ofRdU`: the start segment's `hxa` at `msUHg own … fs` from `hRdU`, for any frames `fs` and source invariant
  `J'`.

## Differences from the AArch64 version

AArch64 discharges this step inline in its start segment at `msUH` (`A64HelloStartH0U0`). Here it is stated once,
generic in the owned words, so that the start segments at `ownGH` and at `ownGHXW` (main's and the worker's TCB
words appended) share it. Against x86-64 wake's `Hxa.hxa_R`: hello's level-0 landing is rodata's allocator return
`Ea` at `wc_rodata`'s call (wake: the box's store `bX`), `hRdU` is asked under `U r1Of` (so no open `hUn1`), and the
arena's offset and units are `LowerX64.arOf_off_eq`/`arOf_units_fit` (wake: its private `units_off`).
-/
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64HelloStartH0H1
import Spike.Lib.LowerX64.LandHu
import Spike.Lib.LowerX64.ArCallMs

namespace Spike.Lib.X64.HelloPh.HxaX

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64 (At enter CKept Abs)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (rN)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib.X64.Alloc (Ea)
open Spike.Lib.X64.HelloPh.StartH0U (msUHg)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- The root's memory sides at `invUH I`, owning `own`. -/
local notation "MSU" => msUHg (asm := asm) hpw i0 own E rd I ls

set_option hygiene false in
/-- `scc_rt_main`'s region at the new stack's base `v`. -/
local notation "RM" v => RS helloLsw v

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

/-- **The start segment's `hxa` at `msUHg own`, from `hRdU`**: a fresh label's landing at `wc_rodata`'s allocator
return `Ea` under main's thread pointer is one the arena hands out (`AllocLand`, at `arOf`'s offset and units), and
with the child's stack unmapped it is in `I` at the extended placement (`hRdU`). -/
theorem hxa_ofRdU (own : State → List (Loc × Val)) (E : Entry) {rd : TermRun.Word → Prop}
    {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize} {fs : List TermRun.Frame}
    {J' : BitVec 64 → FAS → Ctl → Prop} {J1 : FAS → FAS → Ctl → Prop}
    (hRdU : ∀ v m0 σC, ∀ q : AG ((MSU) fs) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR (RM v)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mR (RM v)) (mRdJ0 (J' v) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSU) fs) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (RM v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (RM v))) F' (Ea ((MSU) fs) q.1 l b w) s c →
        AllocLand (AR).heap (AR).cells b w → U (R1) s → TP (TV) s →
        I (fun l' => if l' = l then some b else (LB) l') (fun l' => if l' = l then w else ls0T ls l') s c fs) :
    ∀ v m0 σC, ∀ q : AG ((MSU) fs) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR (RM v)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mR (RM v)) (mRdJ0 (J' v) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSU) fs) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (RM v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (RM v))) F' (Ea ((MSU) fs) q.1 l b w) s c →
        TP (TV) s → ((MSU) fs).xa l b w s c := by
  intro v m0 σC q F' hF1 hF2 l b w s c hl hA ht
  have hcl : ((MSU) fs).cells = 4194304 := rfl
  have hAL : AllocLand (AR).heap (AR).cells b w := by
    obtain ⟨-, -, -, -, -, -, -, -, old, -, -, hb', hold, -, -, us, hus, hw⟩ := id hA
    have hf : ((MSU) fs).off q.1.n q.1.τ = 8 := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) q.2.accs
    have hu : ((MSU) fs).units q.1.n q.1.τ = q.1.n * TermRun.nWords us + 1 :=
      Spike.Lib.LowerX64.arOf_units_fit (Ly).Λ q.1.n q.1.τ us hus (Nat.le_trans (Nat.le_add_left _ old) hold)
    show ((MSU) fs).heap + 8 ≤ b ∧ b + 8 * w ≤ ((MSU) fs).heap + 16 * ((MSU) fs).cells ∧
      w + 1 ≤ ((MSU) fs).cells
    rw [hf] at hb'; rw [hu, hcl] at hold; rw [hcl]; subst hw
    omega
  exact ⟨hAL, fun hU => hRdU v m0 σC q F' hF1 hF2 l b w s c hl hA hAL hU ht⟩

end Spike.Lib.X64.HelloPh.HxaX

/-- info: 'Spike.Lib.X64.HelloPh.HxaX.hxa_ofRdU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.HxaX.hxa_ofRdU

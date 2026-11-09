/-
**`StartH0U`'s `hRdU` from `h1`'s statement** (x86-64; the twin of `Spike/Lib/A64HelloStartH0H1.lean`): at the
root's fragment `I3 arW L0T (ls0T ls) inv0 inv1 inv2`, rodata's fresh-label landing at the frame `[FR]` (`RdLandHg`:
the allocator's return `Ea` at `wc_rodata`'s call, the child's stack `r1Of` unmapped) is in `I3` at the extended
placement, from `h1 : H1StmtHF … (RdLandHg own …) inv1 [FR]` (`land_I3aHF`).

- `RdLandHg`: rodata's landing at the root's choices (the `Rd` of `h1`) at an own map `own` (`msUHg own`).
- `hRdU_of_h1Fg`: `hst0_ofHU_i0`'s `hRdU` at `I := I3 …` at an own map.

Both are generic in the own map (AArch64's `RdLandH`, `hRdU_of_h1F`: at `ownGH`); the root's are at `ownGHXW`.

## Differences from the AArch64 version

- `scc_rt_main` is entered by a `call`, so its region at the new stack's base `v` is `MainGlue.RS helloLsw v`
  (AArch64: `swR v (-helloLsw) 0`), and `wc_rodata`'s is `mR` of it. `StartWcS.rdJH` takes that region (its
  `mNC` records `%rbp`), so `RdLandHg`'s entry invariant is stated under the existential `v`.
- `HelloRd.rN` takes `wc_rodata`'s region; the allocator's call keeps `wc_rodata`'s frame outside the allocator's
  region up to `8` (`CKept (mR _) (-48) (-160) 8`; AArch64: `0`).
- The thread pointer is the `%fs` base at `tpOf (tcbS Ly)` (`MainGlue.tcbS = pinA + 0 + 8`, as AArch64's
  `TPIDR_EL0` value).
- `FS` carries `CallerCells` and takes the stack range `rS0`, as `MainGlue.FS` on x86-64.
-/
import Spike.Lib.X64HelloStartH0U
import Spike.Lib.X64HelloWcInv3F
import Spike.Lib.X64HelloStartWcS
import Spike.Lib.X64HelloFrameD
import Spike.Lib.X64HelloC0S

namespace Spike.Lib.X64.HelloPh.StartH0H1

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64ConsumerA (I3)
open Spike.Lib.X64.HelloPh.StartWcS (rdJH)
open Spike.Lib.X64 (At enter CKept Abs)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS)
open Spike.Lib.X64.Flow.Hello1 (AG mR mF mRdJ0 aR)
open Spike.Lib.X64.Flow.HelloRd (rN)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.KeepUn (U)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Alloc (Ea)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartH0U (msUHg)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS PlaceWX)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.HelloPh.C0S (c0S)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
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
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
/-- `scc_rt_main`'s region at the new stack's base `v`. -/
local notation "RM" v => RS helloLsw v

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
/-- Level 0's memory sides at an own map `own`. -/
local notation "MSUg" => fun own => msUHg (asm := asm) hpw i0 own E rd I ls

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

/-- **rodata's fresh-label landing at the root's choices at an own map `own`** (`h1`'s `Rd`): at `wc_rodata`'s
allocator return `Ea` for a call `q` under `ms [FR]` (at `msUHg own`), the frame condition `F'` `wc_rodata`'s call
context's, the child's stack `r1Of` unmapped, main's thread pointer `tpOf (tcbS Ly)` (`TP`). -/
def RdLandHg (own : Spike.Lib.X64Consumer.Own) (E : Entry) (rd : TermRun.Word → Prop)
    (I : Spike.Lib.X64ConsumerS.InvS) (ls : Lsize) (J1 : FAS → FAS → Ctl → Prop) (l : WeakMem.AllocLabel)
    (b w : Nat) (s : State) (c : Ctl) : Prop :=
  ∃ v m0 σC, ∃ q : AG ((MSUg) own [FR]) (Ly).lab, ∃ F' : MachineData → Prop,
    (∀ m, F' m → mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m) ∧
    (∀ m, F' m → ∃ mC σ c, Abs (mR (RM v)) ⟨-48, []⟩ mC σ ∧
      (rN (Ly).lab (mR (RM v)) (mRdJ0 (rdJH (Ly).lab (RM v) (JW)) σC) (J1 σC) .call).J σ c ∧
      (Spike.Lib.X64.Alloc.N (Ly).lab ((MSUg) own [FR]) q.1 .e).J (enter (-48) σ) c ∧
      CKept (mR (RM v)) (-48) (-160) 8 mC m) ∧
    At (Ly).exe (Ly).endPc (aR (mR (RM v))) F' (Ea ((MSUg) own [FR]) q.1 l b w) s c ∧ U R1 s ∧ TP (TV) s

/-- **`hst0_ofHU_i0`'s `hRdU` from `h1` at an own map `own`** at the root's fragment
`I := I3 arW L0T (ls0T ls) inv0 inv1 inv2`: the landing is `RdLandHg own`, so in `inv1` at `[FR]` (`h1`), so in
`I3` (`land_I3aHF`). -/
theorem hRdU_of_h1Fg {own : Spike.Lib.X64Consumer.Own} (E : Entry) {rd : TermRun.Word → Prop} {ls : Lsize}
    {J1 : FAS → FAS → Ctl → Prop}
    {inv0 : FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isa}
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isa} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isa}
    (h1 : Spike.Lib.X64HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandHg (asm := asm) hpw i0 own E rd (I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2) ls J1) inv1 [FR]) :
    let I := I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2
    ∀ v m0 σC, ∀ q : AG ((MSUg) own [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (RM v) (FS (Ly) (RS0) helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR (RM v)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mR (RM v)) (mRdJ0 (rdJH (Ly).lab (RM v) (JW)) σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.X64.Alloc.N (Ly).lab ((MSUg) own [FR]) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR (RM v)) (-48) (-160) 8 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (RM v))) F' (Ea ((MSUg) own [FR]) q.1 l b w) s c →
        AllocLand (AR).heap (AR).cells b w → U R1 s → TP (TV) s →
        I (fun l' => if l' = l then some b else (LB) l') (fun l' => if l' = l then w else ls0T ls l') s c [FR] :=
  fun v m0 σC q F' hF1 hF2 _ _ _ _ _ hl hA hAL hU ht =>
    Spike.Lib.X64HelloPreA.land_I3aHF h1 hl hAL ⟨v, m0, σC, q, F', hF1, hF2, hA, hU, ht⟩

end Spike.Lib.X64.HelloPh.StartH0H1

/--
info: 'Spike.Lib.X64.HelloPh.StartH0H1.hRdU_of_h1Fg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.StartH0H1.hRdU_of_h1Fg

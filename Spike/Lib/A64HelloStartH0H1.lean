/-
**`StartH0U`'s `hRdU` from `h1`'s statement** (AArch64; wake's
`StartH0U.hst0_ofU` `hxa` from `H1R` twin): at the root's fragment `I3 arW L0T (ls0T ls) inv0 inv1 inv2`, rodata's
fresh-label landing at the frame `[FR]` (`RdLandH`: the allocator's return `Ea` at `wc_rodata`'s call, the child's
stack `r1Of` unmapped) is in `I3` at the extended placement, from `h1 : H1StmtHF … RdLandH inv1 [FR]`
(`land_I3aHF`).

- `RdLandH`: rodata's landing at the root's choices (the `Rd` of `h1`).
- `hRdU_of_h1F`: `hst0_ofHU_i0`'s `hRdU` at `I := I3 …`.
-/
import Spike.Lib.A64HelloStartH0U
import Spike.Lib.A64HelloWcInv3F

namespace Spike.Lib.A64.HelloPh.StartH0H1

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (I3)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.Flow (swR At enter)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 aR)
open Spike.Lib.A64.Flow.HelloRd (rN)
open Spike.Lib.A64.KeepUn (U)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Ea)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib (FragS)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JW)

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls

/-- **rodata's fresh-label landing at the root's choices** (`h1`'s `Rd`): at `wc_rodata`'s allocator return `Ea`
for a call `q` under `ms [FR]` (at `msUH`), the frame condition `F'` `wc_rodata`'s call context's, the child's
stack `r1Of` unmapped, main's thread pointer `pinA + 8` (`TP`, kept through level 0 by
`HelloM.hello_main_pre_segWSTF`; level 1's `MainWcPS.hJpT`). -/
def RdLandH (E : Entry) (rd : TermRun.Word → Prop) (I : Spike.Lib.A64ConsumerS.InvS) (ls : Lsize)
    (J1 : FAS → FAS → Ctl → Prop) (l : WeakMem.AllocLabel) (b w : Nat) (s : State) (c : Ctl) : Prop :=
  ∃ v m0 σC, ∃ q : AG ((MSU) [FR]) (Ly).lab, ∃ F' : MachineData → Prop,
    (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) ∧
    (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
      (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
      (Spike.Lib.A64.Alloc.N (Ly).lab ((MSU) [FR]) q.1 .e).J (enter (-48) σ) c ∧
      Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) ∧
    At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSU) [FR]) q.1 l b w) s c ∧ U R1 s ∧
      TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s

/-- **`hst0_ofHU_i0`'s `hRdU` from `h1`** at the root's fragment `I := I3 arW L0T (ls0T ls) inv0 inv1 inv2`: the
landing is `RdLandH`, so in `inv1` at `[FR]` (`h1`), so in `I3` (`land_I3aHF`). -/
theorem hRdU_of_h1F (E : Entry) {rd : TermRun.Word → Prop} {ls : Lsize} {J1 : FAS → FAS → Ctl → Prop}
    {inv0 : FragS isaLSE2} {inv1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2}
    {W1 : WeakMem.AllocLabel → Nat → Nat → FragS isaLSE2} {K : State → State → Prop}
    {ms1 : WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame → MemSide isaLSE2}
    (h1 : Spike.Lib.HelloPreA.H1StmtHF W1 K (AR) (LB) ms1 (Ly)
      (RdLandH (asm := asm) hpw i0 E rd (I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2) ls J1) inv1 [FR]) :
    let I := I3 (AR) (LB) (ls0T ls) inv0 inv1 inv2
    ∀ v m0 σC, ∀ q : AG ((MSU) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSU) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSU) [FR]) q.1 l b w) s c →
        AllocLand (AR).heap (AR).cells b w → U R1 s →
        TP (UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)) s →
        I (fun l' => if l' = l then some b else (LB) l') (fun l' => if l' = l then w else ls0T ls l') s c [FR] :=
  fun v m0 σC q F' hF1 hF2 _ b w s c hl hA hAL hU ht =>
    Spike.Lib.HelloPreA.land_I3aHF h1 hl hAL ⟨v, m0, σC, q, F', hF1, hF2, hA, hU, ht⟩

end Spike.Lib.A64.HelloPh.StartH0H1

/--
info: 'Spike.Lib.A64.HelloPh.StartH0H1.hRdU_of_h1F' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0H1.hRdU_of_h1F

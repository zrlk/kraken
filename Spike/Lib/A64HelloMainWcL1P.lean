/-
**Non-vacuity of `Level1I.hP`'s `.sp0` invariant** (AArch64): `MainWcL1R.hW_L1` and the source facts are proved at
`wc_rodata`'s `.sp0` invariant `JpT (JpL …) TV` (and `MainWcL1R.rdPostW_of_inh` drops `RdPostW`'s premises at an
empty one). This file shows the invariant is not empty at the root's choices: every landing level 1 starts from
holds a `.sp0` state of it.

- `jpT_of_land`: at any landing `LandF … s c` at thread pointer `t` (`TP t s`), `wc_rodata`'s `.sp0` state after
  the allocator's return (`leave … σ σx`, the landing's registers) is at `JpT (JpL …) t` (`Level1.jpL_of`).
- `jpT_of_rdLandH`: at every state of `StartH0H1.RdLandH` at `J1 := mRdJ0 J'` (`Level1I.hB_land`'s precondition;
  level 0's landing, `StartH0U`'s `hRdU`), the region is the first stack's (`v = TOP`) and `JpT (JpL …) TV` at
  `Level1I`'s choices is inhabited, at `σC` the landing's caller. From it `RdSrcL1.hr0_rd` reaches `jP'`, and so
  on along `RdSrcL1`'s invariants.
-/
import Spike.Lib.A64HelloMainWcL1R

namespace Spike.Lib.A64.HelloPh.MainWcL1P

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib (MemSide Region Ctl)
open Spike.Lib.A64.Flow (swR)
open Spike.Lib.A64.Flow.Hello1 (mRdJ0)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.Level1 (LandF JpL JpT)
open Spike.Lib.A64.HelloPh.StartWcS (rdJH)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartH0U (msUH)
open Spike.Lib.A64.HelloPh.StartH0H1 (RdLandH)
open Spike.Lib.A64.HelloPh.C0S (c0S)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **A landing holds a `.sp0` state of `JpT (JpL …) t`**: the allocator's return to `wc_rodata`'s `.sp0` from the
landing's abstract state `σx` and the caller's `σ` at the call (module doc). -/
theorem jpT_of_land {ms₀ : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {J0 J1 : FAS → Ctl → Prop} {m0 : MachineData} {σC : FAS} {l : WeakMem.AllocLabel}
    {b w : Nat} {s : State} {c : Ctl} {t : UInt64}
    (h : LandF ms₀ exe endPc R F J0 J1 m0 σC l b w s c) (ht : TP t s) :
    ∃ σ c', JpT (JpL (R := R) ms₀ (_root_.Executable.labels exe).label J0 J1 l b w) t σ c' := by
  obtain ⟨q, F', -, hF2, -, -, -, -, σx, hA, hF', hJ⟩ := h
  obtain ⟨-, σ, c0, -, hcall, hNe, -⟩ := hF2 _ hF'
  refine ⟨_, c, Spike.Lib.A64.HelloPh.Level1.jpL_of (R := R) q σx σ c0 c hJ hcall hNe, ?_⟩
  show σx.regs.TPIDR_EL0 = t
  rw [← hA.regs]
  exact ht

section Root

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  {E : Entry} {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

set_option hygiene false in
local notation "TV" => UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "MSU" => msUH (asm := asm) hpw i0 E rd I ls [FR]

/-- **`Level1I.hP`'s `.sp0` invariant is inhabited at every landing level 1 starts from** (module doc): at the
first stack's top, the landing's caller `σC`, `J1 := mRdJ0 J'`. -/
theorem jpT_of_rdLandH {l : WeakMem.AllocLabel} {b n : Nat} {s : State} {c : Ctl}
    (h : RdLandH (asm := asm) hpw i0 E rd I ls (fun σC => mRdJ0 (J') σC) l b n s c) :
    ∃ σC σ c', JpT (JpL (R := swR (TOP) (-helloLsw) 0) (MSU) (Ly).lab (mRdJ0 (J') σC) (mRdJ0 (J') σC) l b n)
      (TV) σ c' := by
  obtain ⟨v, m0, σC, q, F', h1, h2, hA, -, ht⟩ := h
  have hv : v = TOP := by
    obtain ⟨-, -, -, -, -, -, hF', -⟩ := hA
    exact (h1 _ hF').1.2.1.1
  subst hv
  obtain ⟨σ, c', hj⟩ := jpT_of_land (R := swR (TOP) (-helloLsw) 0) ⟨q, F', h1, h2, hA⟩ ht
  exact ⟨σC, σ, c', hj⟩

end Root

end Spike.Lib.A64.HelloPh.MainWcL1P

/-- info: 'Spike.Lib.A64.HelloPh.MainWcL1P.jpT_of_land' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1P.jpT_of_land

/--
info: 'Spike.Lib.A64.HelloPh.MainWcL1P.jpT_of_rdLandH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.MainWcL1P.jpT_of_rdLandH

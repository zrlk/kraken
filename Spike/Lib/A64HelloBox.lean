/-
**hello.w's box landing** (AArch64; the hello twin of `A64WakeBox.lean`'s
`WakeWc.Box` and `A64WakeHxa.lean`'s `box_landing`): the predicate `BoxH` that `H2StmtH`'s `Box` is instantiated
with at level 1, and the proof that every landing of the box's store (`GsH1`) is a `BoxH`.

`BoxH` is lean on purpose. It carries what the landing gives and what level 2 is known to need: `wc_main`'s region
and frame condition, the entry invariant's shape, the landing itself under main's thread pointer, one cell, and the
child's stack unmapped. B8-h2-inst (the `H2StmtH` producer, also owned here) may add conjuncts as it needs them,
e.g. the pool band of the call's slots, `takeMem`/`StackOff` stability of the frame condition, the source term or
`Owned r0`.

- `BoxH`: the box's landing past its store.
- `box_regH`, `tv_toNat`: a landing's region facts (any caller's invariant); main's thread pointer as a number.
- `box_landingH`: a `GsH1` landing is a `BoxH`, given `wc_main`'s frame condition inside `F0` (`hF0`) and the
  child's stack unmapped (`hu`).
-/
import Spike.Lib.A64HelloLandR1
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.Box

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib (Region MemSide FragS)
open Spike.Lib.A64.Flow (swR At FStable)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.Hello1 (mWC)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (bXH)
open Spike.Lib.A64.WakePh.MainGlue (FS)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.Land (ref1H GsH1 fstable_FS)
open Spike.Lib.WakeLoadT (L0T ls0T)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

/-- **The box's landing past its store** at a reference memory side `ms0` (`WakeWc.Box`'s hello twin, lean): for
some region `R`, frame condition `F`, entry invariant `J0` and thread pointer `t`,
- `R` is `wc_main`'s region: OK, 16-aligned, `F` stable in it, at least `helloD` deep below its base, its base
  `80` under the first stack's top;
- `F` inside `F0`;
- `J0` is `wc_main`'s entry invariant from `scc_rt_main`'s call node (`wcJ0 (mWC …).J`);
- the state is at `bXH` (past the box's store, the label `l` at `b`) under main's thread pointer `t`;
- one cell (`n = 1`);
- the child's stack unmapped (`KeepUn.U r1`). -/
def BoxH (L : RuntimeLayout) (ms0 : MemSide isaLSE2) (F0 : MachineData → Prop)
    (l : WeakMem.AllocLabel) (b n : Nat) (s : State) (c : Spike.Lib.Ctl) : Prop :=
  ∃ (R : Region) (F : MachineData → Prop) (J0 : FAS → Spike.Lib.Ctl → Prop) (t : UInt64),
    (R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -helloD ∧ 0 ≤ R.hi ∧
      R.base.toNat + 80 = L.stacksA.toNat + 16384) ∧
    (∀ m, F m → F0 m) ∧
    (∃ (Jr1 : FAS → Spike.Lib.Ctl → Prop) (σC σ1 : FAS), J0 = wcJ0 (mWC L.lab σC Jr1).J σ1) ∧
    (At L.exe L.endPc R F (bXH ms0 L.lab J0 l b) s c ∧ TP t s ∧ t.toNat = L.pinA.toNat + 8) ∧
    n = 1 ∧
    Spike.Lib.A64.KeepUn.U (Spike.Lib.A64.Rt.PreChild.r1Of L.lab) s

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => UInt64.ofBitVec (pinA (Ly).lab + 0#64 + 8#64)

set_option hygiene false in
local notation "R1" => Spike.Lib.A64.Rt.PreChild.r1Of (Ly).lab

/-- **A box store's landing's region** at `ref1H l b n []` (`box_landingH`'s and `BoxM.boxMH_landingH`'s common
part): `wc_main`'s region `wcR (swR v (-helloLsw) 0) helloD`, `v` the first stack's top by the start's `FS`, is OK,
16-aligned, its frame condition stable in it and inside `F0` (`hF0`), at least `helloD` deep, its base `80` under
the first stack's top; for any caller's invariant `Jc`. -/
theorem box_regH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    {Jc : FAS → Spike.Lib.Ctl → Prop} {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (hA : At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jc).J σ1) l' A) s c) :
    ∃ (R : Region) (F : MachineData → Prop),
      (R.OK ∧ R.base.toNat % 16 = 0 ∧ FStable R F ∧ R.lo ≤ -helloD ∧ 0 ≤ R.hi ∧
        R.base.toNat + 80 = (Ly).stacksA.toNat + 16384) ∧ (∀ m, F m → F0 m) ∧
      At (Ly).exe (Ly).endPc R F (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab (wcJ0 (mWC (Ly).lab σC
          Jc).J σ1) l' A)
        s c := by
  have hA0 := hA
  obtain ⟨-, -, -, -, σ, -, hFm, -⟩ := hA
  have hv : v = Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64 := hFm.1.2.1.1
  subst hv
  obtain ⟨hok, hal, hF⟩ := fstable_FS hpw i0
  obtain ⟨hR, hRal, hRF⟩ := Spike.Lib.A64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hok hal hF
    (by show (-helloLsw : Int) ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 0; decide) m1 σ1
  have hT : (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat = (Ly).stacksA.toNat + 16384 := by
    rw [Spike.Lib.A64.Rt.stacksA_lab0]; exact Spike.Lib.A64.Rt.top0_toNat _
  have hb : ((wcR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0) helloD).base.toNat
      : Int) = (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64).toNat + -80 :=
    Spike.Lib.Region.callee_base (hi' := 0) hok (kc := -80) (lo' := -helloD)
      (by show (-helloLsw : Int) ≤ -80 + -helloD; decide) (by decide) (by simp [swR])
  rw [hT] at hb
  have hRlo : (wcR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0) helloD).lo =
    -helloD := rfl
  have hRhi : (wcR (swR (Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64) (-helloLsw) 0) helloD).hi =
    0 := rfl
  exact ⟨_, _, ⟨hR, hRal, hRF, by rw [hRlo]; exact Int.le_refl _, by rw [hRhi]; decide, by omega⟩, hF0 _ m1 σ1, hA0⟩

/-- main's thread pointer as a number: the first TCB, `pinA + 8`. -/
theorem tv_toNat : (pinA (Ly).lab + 0#64 + 8#64).toNat = (Ly).pinA.toNat + 8 := by
  have hpin : (Ly).pinA.toNat < 2 ^ 32 := (Ly).words_small _ (Ly).pin_mem
  rw [Spike.Lib.A64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **A box store's landing is a `BoxH`** at `ref1H l b n []` (`Hxa.box_landing`'s twin): `wc_main`'s region by
`box_regH` (its frame condition inside `F0`, `hF0`); the entry node at `mWC`; the thread pointer the first TCB; the
child's stack unmapped (`hu`). -/
theorem box_landingH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    {Jr1 : FAS → Spike.Lib.Ctl → Prop} {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (hA : At (Ly).exe (Ly).endPc (wcR (swR v (-helloLsw) 0) helloD)
      (wcF (swR v (-helloLsw) 0) helloD (FS (Ly) (RS) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) l' A) s c)
    (htp : TP (TV) s) (hu : Spike.Lib.A64.KeepUn.U (R1) s) :
    BoxH (Ly) (ref1H (asm := asm) hpw i0 E rd ls l b n []) F0 l' A 1 s c := by
  obtain ⟨R, F, hR, hF, hA'⟩ := box_regH hpw i0 E rd ls hF0 hA
  exact ⟨R, F, _, _, hR, hF, ⟨Jr1, σC, σ1, rfl⟩, ⟨hA', htp, tv_toNat hpw i0⟩, rfl, hu⟩

end Spike.Lib.A64.HelloPh.Box

/-- info: 'Spike.Lib.A64.HelloPh.Box.box_regH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Box.box_regH

/-- info: 'Spike.Lib.A64.HelloPh.Box.box_landingH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.Box.box_landingH

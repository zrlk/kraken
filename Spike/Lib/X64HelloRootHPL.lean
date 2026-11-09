/-
**hello.w's box landing at the pinned ghost** (x86-64; the `Land` section of `Spike/Lib/A64HelloRootHP.lean`):
at a box store's landing in level 1's context (`Land.GsH1`'s shape: `bXH` at `ref1H` on `wc_main`'s frame at the
saved `%rbp`, its frame condition over the start's `FS`), the region's facts, and the landing as `BoxMH` at the
pinned ghost `GJ1RH`.

- `box_regRH`: at such a landing `v` is the first stack's top, and the region `(wcR (RS helloLsw v) helloD).fp (-8)`
  is a region, 16-aligned, its frame condition stable in it and inside `F0`, its bounds `-392` and `16`, its base
  `96` under the first stack's top (`BoxPureH`'s region facts).
- `boxMH_landingRH`: a pinned box store's landing is `BoxMH` at `GJ1RH`; the ghost's witness `v`, `m1`, `σ1` is
  the landing's own (`GsH1`'s), produced, not assumed; the source facts `QBH` from `wc_main`'s entry at `Jr1LH`;
  `GJ1RH`'s `%rbp` pin `RbpPinH` from the caller's invariant `Jr1LH`'s (`Land.jr1LH_rbp`, at the first stack's
  top, the landing's `v` by its frame condition).
- `hland2_boxMRUg`: `LandR1U.hland2_ofUg` with `boxMH_landingRH` at `GJ1RH` (`h2`'s box clause at `GJ1RH`, with
  `r1Of` unmapped): every pinned landing with `r1Of` unmapped is in the level's allocation fragment, at any owned
  words `own`.
- An example: `GJ1RH` holds at the real run's region and frame condition.

## Unlike AArch64

- The landing is on `(wcR (RS helloLsw v) helloD).fp (-8)` (x86-64's frame at the saved `%rbp`; AArch64
  `wcR (swR v (-helloLsw) 0) helloD`), so the region's bounds are `-392`, `16` and its base `96` under the top
  (AArch64 `-400`, `0`, `80`). The region facts come from `Land.fstable_FS`'s `RS`, `HelloM.wcR_ok` and
  `FStable.fp` / `Region.fp_ok` (AArch64 `HelloM.wcR_ok` at `swR`, which also gives the alignment); the alignment
  is the top's (`stacks_al`) less `96`.
- `GJ1RH`'s `%rbp` pin is `Jr1LH`'s `%rbp` conjunct (`Land.jr1LH_rbp`, `scc_rt_main`'s saved `%rbp` as
  `HelloM.JrT` records it); AArch64's ghost has no such pin.
- The caller's slot holding main's TCB is `-16` (`mWC`'s `%r8`; AArch64 `-80`).
- The landing lemma is generic in the owned words (`hland2_boxMRUg`; AArch64: at `ownGH`).
- `BoxMH`'s source facts are `QBH` (the box at `.x25`'s `mfence`: `boxTermH` and the environment's `o`, `me`,
  `sl`), read off `wc_main`'s entry `Jr1LH` (`c0H` on rodata's slice) and the `new`'s step.
-/
import Spike.Lib.X64HelloRootHP
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64AtRebase
import Spike.Lib.X64HelloLandR1U

namespace Spike.Lib.X64.HelloPh.RootHP

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Region)
open Spike.Lib.X64 (At FStable)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.Flow.Ret0 (pinA tpOf)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.X64.Flow.HelloWc (bXH)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64HelloHMid (BoxMH slWsH)
open Spike.Lib.X64.HelloPh.Land (ref1H Jr1LH)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Scc.Sem.Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => Spike.Lib.X64WakeLoadT.L0T (Ly).Λ

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

/-- **The region and frame condition at a box store's landing**: at a landing of `bXH` at `ref1H` on `wc_main`'s
frame at the saved `%rbp` at `v` and frame condition over `FS` at `v`, `v` is the first stack's top, the region is
OK, 16-aligned, its frame condition stable in it and inside `F0`, its bounds `-392` and `16`, its base `96` under
the first stack's top. -/
theorem box_regRH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {m1 : MachineData} {σ1 : FAS}
    {J1 : FAS → Spike.Lib.Ctl → Prop} {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (hA : At (Ly).exe (Ly).endPc ((wcR (RS helloLsw v) helloD).fp (-8))
      (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab J1 l' A) s c) :
    (((wcR (RS helloLsw v) helloD).fp (-8)).OK ∧ ((wcR (RS helloLsw v) helloD).fp (-8)).base.toNat % 16 = 0 ∧
      FStable ((wcR (RS helloLsw v) helloD).fp (-8))
        (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1) ∧
      ((wcR (RS helloLsw v) helloD).fp (-8)).lo ≤ -384 ∧ 16 ≤ ((wcR (RS helloLsw v) helloD).fp (-8)).hi ∧
      ((wcR (RS helloLsw v) helloD).fp (-8)).base.toNat + 96 = (Ly).stacksA.toNat + 16384) ∧
      (∀ m, wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1 m → F0 m) := by
  obtain ⟨-, -, -, -, σ, -, hFm, -⟩ := hA
  have hv : v = topS (Ly) 0#64 := hFm.1.1.2.1.1
  subst hv
  obtain ⟨hok, hRS, hF⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hRw, hFw⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hRS hF
    (by show (8 : Int) - helloLsw ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
  have h1 : (wcR (RS helloLsw (topS (Ly) 0#64)) helloD).lo ≤ -8 := by show (-helloD : Int) ≤ -8; decide
  have h2 : (-8 : Int) < (wcR (RS helloLsw (topS (Ly) 0#64)) helloD).hi := by show (-8 : Int) < 8; decide
  have hRF := FStable.fp hRw h1 h2 hFw
  have hRok := Spike.Lib.Region.fp_ok hRw h1 h2
  -- the bases: `v - 8` (the call's push), `- 80` (`wc_main`'s callee), `- 8` (the saved `%rbp`)
  have hbS := Spike.Lib.Region.callee_base (hi' := 8) hok (kc := -8) (lo' := 8 - helloLsw)
    (by simp [Spike.Lib.X64.swR]; decide) (by decide) (by simp [Spike.Lib.X64.swR])
  have hbW := Spike.Lib.Region.callee_base (hi' := 8) hRS (kc := -80) (lo' := -helloD)
    (by show (8 : Int) - helloLsw ≤ -80 + -helloD; decide) (by decide) (by show (-80 : Int) < 8; decide)
  have hbF := Spike.Lib.Region.fp_base hRw h1 h2
  have hT : (topS (Ly) 0#64).toNat = (Ly).stacksA.toNat + 16384 := by
    show (Spike.Lib.X64.Flow.Ret0.stacksA (_root_.Executable.labels (Ly).exe).label + 0#64 + 16384#64).toNat = _
    rw [(Ly).lab_stacks]; exact Spike.Lib.X64.Rt.top0_toNat (Ly)
  have hsal := (Ly).stacks_al
  have hb0 : ((Spike.Lib.X64.swR (topS (Ly) 0#64) (-helloLsw) 0).base.toNat : Int) = (topS (Ly) 0#64).toNat :=
    rfl
  have hbS' : ((RS helloLsw (topS (Ly) 0#64)).base.toNat : Int) = (topS (Ly) 0#64).toNat + -8 := by
    rw [show RS helloLsw (topS (Ly) 0#64) =
      (Spike.Lib.X64.swR (topS (Ly) 0#64) (-helloLsw) 0).callee (-8) (8 - helloLsw) 8 from rfl, hbS, hb0]
  have hbW' : ((wcR (RS helloLsw (topS (Ly) 0#64)) helloD).base.toNat : Int) = (topS (Ly) 0#64).toNat + -88 := by
    rw [show wcR (RS helloLsw (topS (Ly) 0#64)) helloD =
      (RS helloLsw (topS (Ly) 0#64)).callee (-80) (-helloD) 8 from rfl, hbW, hbS']; omega
  have hlo : ((wcR (RS helloLsw (topS (Ly) 0#64)) helloD).fp (-8)).lo = -392 := by
    simp [Spike.Lib.Region.fp, Spike.Lib.Region.callee, helloD]
  have hhi : ((wcR (RS helloLsw (topS (Ly) 0#64)) helloD).fp (-8)).hi = 16 := by
    simp [Spike.Lib.Region.fp, Spike.Lib.Region.callee]
  rw [hbW'] at hbF
  exact ⟨⟨hRok, by omega, hRF, by rw [hlo]; decide, by rw [hhi]; decide, by omega⟩, hF0 _ m1 σ1⟩

/-- **A pinned box store's landing is `BoxMH` at the pinned ghost**: at a landing of `GsH1`'s shape (`bXH` at
`ref1H l b n []` under `wc_main`'s entry `mWC σC (Jr1LH l b)`, the caller's slot `-16` main's TCB) under main's
thread pointer, `BoxMH` at `GJ1RH` with rodata's slice `slWsH l`: the ghost's witness `v`, `m1`, `σ1` is the
landing's own, the source facts `QBH` from `Jr1LH`'s `c0H` past the box's `new`. -/
theorem boxMH_landingRH {F0 : MachineData → Prop}
    (hF0 : ∀ v m1 σ1 m, wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1 m → F0 m)
    {l : WeakMem.AllocLabel} {b n : Nat} {v : BitVec 64} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    {l' : WeakMem.AllocLabel} {A : Nat} {s : State} {c : Spike.Lib.Ctl}
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64)
    (hA : At (Ly).exe (Ly).endPc ((wcR (RS helloLsw v) helloD).fp (-8))
      (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
      (bXH (ref1H (asm := asm) hpw i0 E rd ls l b n []) (Ly).lab
        (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) l' A) s c)
    (htp : TP (TV) s) :
    BoxMH (Ly) (ref1H (asm := asm) hpw i0 E rd ls l b n []) F0
      (GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l) l' A (slWsH l) 1 s c := by
  have hv : v = topS (Ly) 0#64 := by
    obtain ⟨-, -, -, -, -, -, hFm, -⟩ := hA
    exact hFm.1.1.2.1.1
  subst hv
  obtain ⟨⟨hR, hRal, hRF, hlo, hhi, hbase⟩, hF⟩ := box_regRH hpw i0 E rd ls hF0 hA
  have hA0 := hA
  obtain ⟨-, -, -, -, σ, -, -, q, ⟨σe, ⟨-, σx, ⟨⟨hq0, -⟩, -⟩, -⟩, -⟩, -, hc, -⟩ := hA
  obtain ⟨T, ht⟩ := q.2.term
  rw [hq0] at ht
  obtain ⟨hx, ha, hee⟩ := Expr.let_.inj ht
  have ha' := (Op.new.inj ha).1
  have hev := q.2.ev
  rw [hq0, ← ha'] at hev
  have hτ : q.1.τ = .int := (Prod.mk.inj (Option.some.inj hev)).1.symm
  rw [← hx, ← hee, hτ, hq0] at hc
  subst hc
  -- the thread pointer: the first TCB
  have hpin : (Ly).pinA.toNat < 2 ^ 32 := (Ly).words_small _ (Ly).pin_mem
  have hpin8 : (tcbS (Ly)).toNat = (Ly).pinA.toNat + 8 := by
    show (pinA (Ly).lab + 0#64 + 8#64).toNat = _
    rw [Spike.Lib.X64.Rt.pinA_lab0, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have htp8 : (TV).toNat = (Ly).pinA.toNat + 8 := by
    show (UInt64.ofNat (tcbS (Ly)).toNat).toNat = _
    rw [UInt64.toNat_ofNat', hpin8]; omega
  exact ⟨_, _, _, TV, ⟨hR, hRal, hRF, hlo, hhi, hbase, htp8, rfl, hF⟩,
    ⟨⟨σC, σ1, Jr1LH hpw i0 l b, hslot, fun _ _ h => h.1.2, rfl⟩, _, m1, σ1, rfl, rfl, σC, σ1, _, rfl,
      fun _ _ h => Spike.Lib.X64.HelloPh.Land.jr1LH_rbp hpw i0 h⟩,
    ⟨hA0, htp⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Non-vacuity: `GJ1RH` holds at the real run's region and frame condition**: for `wc_main`'s frame at the
saved `%rbp` at the first stack's top and its frame condition from any caller's state `m1`, `σ1`, given a caller's
state `σC` whose slot `-16` holds main's TCB (as `GsH1` pins it), with `J1` the pinned entry invariant (`Jr1LH`,
whose `%rbp` is the pin, `Land.jr1LH_rbp`). `boxMH_landingRH` produces exactly this witness at every pinned
landing. -/
example {l : WeakMem.AllocLabel} {b : Nat} {σC : FAS} {m1 : MachineData} {σ1 : FAS}
    (hslot : σC.slot (-16) = pinA (Ly).lab + 0#64 + 8#64) :
    GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l ((wcR (RS helloLsw (topS (Ly) 0#64)) helloD).fp (-8))
      (wcF (RS helloLsw (topS (Ly) 0#64)) helloD (FS (Ly) (RS0) helloLsw 0#64 (topS (Ly) 0#64)) m1 σ1)
      (wcJ0 (mWC (Ly).lab σC (Jr1LH hpw i0 l b)).J σ1) (TV) :=
  ⟨⟨σC, σ1, Jr1LH hpw i0 l b, hslot, fun _ _ h => h.1.2, rfl⟩, _, m1, σ1, rfl, rfl, σC, σ1, _, rfl,
    fun _ _ h => Spike.Lib.X64.HelloPh.Land.jr1LH_rbp hpw i0 h⟩

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "R1" => Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab

/-- **The box's landings in `h2`'s fragment at the pinned ghosts, at any owned words `own`** (`LandR1U.hland2_ofUg`
with `boxMH_landingRH`): from `H2StmtH` at the root's box `BoxMH … (GJ1RH (Ly) (upd LB l b) l) … ∧ U r1`, every
pinned landing with `r1Of` unmapped is in the level's allocation fragment. -/
theorem hland2_boxMRUg {own : Spike.Lib.X64Consumer.Own}
    {W2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa}
    {K : State → State → Prop}
    {ms2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → List TermRun.Frame →
      Spike.Lib.MemSide isa}
    {L : RuntimeLayout} {endPc : Int64} {F0 : MachineData → Prop}
    {inv0 : Spike.Lib.FragS isa} {inv1 : WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa}
    {inv2 : WeakMem.AllocLabel → Nat → Nat → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.FragS isa}
    {l : WeakMem.AllocLabel} {b n : Nat}
    (h2 : Spike.Lib.X64HelloPreA.H2StmtH W2 K (AR) (LB) ms2 L endPc
      (fun l b n l' A n' s c => BoxMH (Ly) (ref1H (asm := asm) hpw i0 E rd ls l b n []) F0
        (GJ1RH (Ly) (Spike.Lib.X64ConsumerA.upd (LB) l b) l) l' A (slWsH l) n' s c ∧
        Spike.Lib.X64.KeepUn.U (R1) s) inv2)
    (hl : (LB) l = none) (hb : Spike.Lib.HeapLand.AllocLand (AR).heap (AR).cells b n)
    (hF0 : ∀ v m1 σ1 m, wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1 m → F0 m) :
    Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hpw i0 E rd ls l b n
      ((Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
        ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd
        (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
        (fun s _ => own s) (AR)
        (Spike.Lib.X64ConsumerA.I3 (AR) (LB) (Spike.Lib.X64WakeLoadT.ls0T ls) inv0 inv1 inv2)
        (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (Spike.Lib.X64WakeLoadT.ls0T ls) l n)
        []).xa) :=
  Spike.Lib.X64.HelloPh.LandR1U.hland2_ofUg hpw i0 E rd ls l b n h2 hl hb fun Lnd hG l' A s c _ hL hu => by
    obtain ⟨v, σC, m1, σ1, hslot, rfl⟩ := hG
    obtain ⟨-, hA, htp⟩ := hL
    exact ⟨boxMH_landingRH hpw i0 E rd ls hF0 hslot hA htp, hu⟩

end Spike.Lib.X64.HelloPh.RootHP

/-- info: 'Spike.Lib.X64.HelloPh.RootHP.box_regRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.box_regRH

/--
info: 'Spike.Lib.X64.HelloPh.RootHP.boxMH_landingRH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.boxMH_landingRH

/-- info: 'Spike.Lib.X64.HelloPh.RootHP.hland2_boxMRUg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootHP.hland2_boxMRUg

/-
**`MainWcPS.hWp`, `hWs` at `Level1I`'s choices: the shared facts** (x86-64; the twin of
`Spike/Lib/A64HelloMainWcL1Wp.lean`'s helpers): at any `PlaceWX` output's runtime layout
`Ly := RuntimeLayout.ofPlaceWX hpw (HelloImms.immsH Λ0 i0)`, at the first stack's top, the facts on `wc_main`'s
caller, its region and the arena that the statements discharge their premises from. The statements (AArch64
`hWp_L1G`, `hWs_L1G`) are at `ownGHXW` only, `X64HelloMainWcL1WpX`'s `hWp_L1GX`, `hWs_L1GX` (the root's level owns
main's and the worker's TCB words).

- `c1J_L1`, `hJ_L1`: `wc_main`'s caller's controls are `c0H`'s, with their control facts.
- `hoffQ_L1`: the arena's offset within its units at the level's memory side at `ownGH`, at a box call
  (`X64HelloMainWcL1WpX.hoffQ_L1X` at `ownGHXW`).
- `wcR_L1`: `wc_main`'s region at the first stack's top: `OK`, its frame condition stable, its base 8-aligned.

## Unlike AArch64

- `scc_rt_main`'s region at the first stack's top is `MainGlue.RS helloLsw TOP` (AArch64 `swR TOP (-helloLsw) 0`),
  so `wc_main`'s is `wcR (RS helloLsw TOP) helloD`.
- The thread pointer is `%fs`'s base `tpOf (tcbS Ly)` (AArch64 `TPIDR_EL0`).
- `wcR_ok` gives no alignment: `wc_main`'s region's base is 8-aligned as the first stack's top is
  (`Region.callee_base` twice; AArch64 `wcR_ok`'s 16-alignment). The regions' high ends are `8` (`call` pushes).
-/
import Spike.Lib.X64HelloMainWcL1Q
import Spike.Lib.X64HelloHrdArena
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64HelloLand1
import Spike.Lib.X64HelloW1H
import Spike.Lib.X64HelloWcEntry
import Spike.Lib.X64HelloWcWfR
import Spike.Lib.X64WakeStartGlue
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64HelloClH

namespace Spike.Lib.X64.HelloPh.MainWcL1Wp

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (FragS PlaceWX Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (tpXa)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)

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
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `scc_rt_main`'s region at the first stack's top. -/
local notation "RM" => RS helloLsw (TOP)

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (RM) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (RM) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1

set_option hygiene false in
/-- The level's memory side at no frame, under main's thread pointer. -/
local notation "MS" => tpXa (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ μ rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGH (Ly) (NT) s)
  (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

variable {μ : Scc.Sem.Marks} {rd : TermRun.Word → Prop} {I : Spike.Lib.X64ConsumerS.InvS} {ls lsW : Lsize}
  {l : WeakMem.AllocLabel} {b n : Nat} {Ctx1 : WeakMem.AllocLabel → Nat → Nat → FragS isa}
  {Jr : FAS → Spike.Lib.Ctl → Prop} {σC σ1 : FAS} {m1 : MachineData}

/-- `c0H`'s control facts at `wc_main`'s caller's invariant (`WakeSrcCtl.new_ctl`). -/
theorem c1J_L1 : ∀ σ c, J1 σ c → (∀ a, c.term ≠ .ret a) ∧ Spike.Lib.X64.WakeWf.RunWf helloSrc c [] :=
  Spike.Lib.X64.Flow.HelloWc.ctl_wcJ0 fun _ _ h =>
    Spike.Lib.X64.WakeSrcCtl.new_ctl (h.1.1 ▸ Spike.Lib.X64HelloMainPreSrc.c0H_term _ _ _ _)

/-- `wc_main`'s caller's controls are `c0H`'s. -/
theorem hJ_L1 : ∀ σ c, J1 σ c → ∃ w0 w1 w2 mw, c = Spike.Lib.X64HelloMainPreSrc.c0H w0 w1 w2 mw :=
  Spike.Lib.X64.Flow.HelloWc.ctl_wcJ0
    (P := fun c => ∃ w0 w1 w2 mw, c = Spike.Lib.X64HelloMainPreSrc.c0H w0 w1 w2 mw)
    fun _ _ h => ⟨_, _, _, _, h.1.1⟩

/-- The arena's offset is at most its units' room at every box call (`HrdArena.hoffQ_U` at the level). -/
theorem hoffQ_L1 : ∀ q : Call, q.OKB (MS) (Ly).lab → (MS).off q.n q.τ ≤ 16 * (MS).units q.n q.τ := by
  intro q hq
  have hu := Spike.Lib.LowerX64.arOf_units_pos (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  have hf := Spike.Lib.LowerX64.arOf_off_eq (Λ := (Ly).Λ) (n := 1) hq.toS.accs
  rw [hq.one]
  show (Spike.Lib.X64.Rt.arOf (Ly).Λ).off 1 q.τ ≤ 16 * (Spike.Lib.X64.Rt.arOf (Ly).Λ).units 1 q.τ
  rw [hf]; omega

/-- **`wc_main`'s region at the first stack's top**: a region, its frame condition stable, its base 8-aligned. -/
theorem wcR_L1 (m1 : MachineData) (σ1 : FAS) :
    (RW).OK ∧ FStable (RW) (FW) ∧ (RW).base.toNat % 8 = 0 := by
  obtain ⟨hok, hR0, hF0⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  obtain ⟨hR, hF⟩ := Spike.Lib.X64.Flow.HelloM.wcR_ok (D := helloD) (by decide) (by decide) hR0 hF0
    (by show (8 : Int) - helloLsw ≤ -80 - helloD; decide) (by show (0 : Int) ≤ 8; decide) m1 σ1
  have hbd : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 :=
    Spike.Lib.X64WakeHClC.hbd_W hpw IH
  have hal : (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat % 16 = 0 := by
    rw [(Ly).lab_stacks]; exact (Ly).stacks_al
  have hb0 : ((RM).base.toNat : Int) = (TOP).toNat + (-8 - 0) :=
    Region.callee_base hok (by show (-helloLsw : Int) ≤ -8 - 0 + (8 - helloLsw); decide) (by decide)
      (by show (-8 - 0 : Int) < 0; decide)
  have hb1 : ((RW).base.toNat : Int) = (RM).base.toNat + (-80) :=
    Region.callee_base hR0 (by show (8 : Int) - helloLsw ≤ -80 + -helloD; decide) (by decide)
      (by show (-80 : Int) < 8; decide)
  have htop : (TOP).toNat = (Spike.Lib.X64.Flow.Ret0.stacksA (Ly).lab).toNat + 16384 := by
    simp only [topS, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  exact ⟨hR, hF, by omega⟩

end Spike.Lib.X64.HelloPh.MainWcL1Wp

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.c1J_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.c1J_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hJ_L1

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wp.hoffQ_L1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wp.hoffQ_L1

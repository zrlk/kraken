/-
**hello's heap abort at `wXA` closed at `ownGHXW`** (x86-64 only; AArch64's
`A64HelloLevel1HA.hello_hab_closedLA` at `ownGHXW`): `Level1HA.hello_hab_closedLAg` at
`ownW := ownGHXW Ly (Reserve.ntA Ly.lab)`, the stub's path inside the level (`hP0`) by `HabLftX.hP0X`.

- `bandIn_wcAb`: the heap abort's dispatcher band below `wc_main`'s region at the first stack's top is on the
  stack pool (`HrdRootX.bandRS` at depth `424`, through `Region.callee_addr` twice).
- `hello_hab_closedLAX`: the heap-abort exit at `wXA` closes inside `StartWcS.WSg (ownGHXW Ly ntA)`; `hP0X`'s
  separation premises from A13's data part (`hA13`: `StartPlaceLy.wsep_W`, `tcbWH_notG_W`).

## Differences from the AArch64 version

AArch64 has no counterpart: its level owns `ownGH` (main owns no TCB word there), so `A64HelloLevel1HA`'s
`hello_hab_closedLA` is the only form. Against it: the level is at `ownGHXW`,
`hA13` is a new premise, and the abort path's band on the pool is proved here (`bandIn_wcAb`).
-/
import Spike.Lib.X64HelloLevel1HA
import Spike.Lib.X64HelloHabLftX
import Spike.Lib.X64HelloHrdRootX

namespace Spike.Lib.X64.HelloPh.Level1HAX

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem.X64 (codeLabel cellsOf)
open Spike.Lib (FragS Frag SegWS PlaceWX Region)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.X64.Flow.HelloWc (wXA)
open Spike.Lib.X64.WakePh (tcbM BandIn BandOnP)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.StartWcS (WSg)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64.HelloPh.HabCtlA (HabCtlHA)
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
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
/-- main's owned words before the spawn, at `scc_rt_nthreads`. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

/-- **The heap abort's band below `wc_main`'s region is on the pool**: the dispatcher band `[-32, 8]` of
`(wcR (RS helloLsw TOP) helloD).callee (-304 - 8) (-24) 16` is `scc_rt_main`'s region's `[-424, -384]`, on the
first stack (`HrdRootX.bandRS`). -/
theorem bandIn_wcAb :
    BandIn (Ly) ((wcR (RS helloLsw (TOP)) helloD).callee (-304 - 8) (-24) 16) := by
  obtain ⟨hok, -, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hB : BandOnP (Ly) (RS helloLsw (TOP)) (-424) 8 :=
    Spike.Lib.X64.HelloPh.HrdRootX.bandRS (show (8 - helloLsw : Int) ≤ -424 by decide)
      (show helloLsw < 16384 by decide) hok
  intro k h1 h2
  rw [Region.callee_addr, Region.callee_addr]
  exact hB _ (by omega) (by omega)

/-- **The heap-abort exit at `wXA` closes at `ownGHXW`** (module doc): `Level1HA.hello_hab_closedLAg` at
`ownW := OX`, `hP0` by `HabLftX.hP0X` (the band `bandIn_wcAb`, the separation from `hA13`). -/
theorem hello_hab_closedLAX {LB : Lbl} {E : Scc.Sem.Entry} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
    {own : Spike.Lib.X64ConsumerS.OwnS} {I : Spike.Lib.X64ConsumerS.InvS} {ls : Lsize}
    {Ctx : FragS isa} {ls0 : Lsize} {frM : TermRun.Frame} {t : UInt64}
    {σC : FAS} {Jr1 : FAS → Spike.Lib.Ctl → Prop}
    (hpa : cellsOf asm = some o.prog)
    (hhp : cellsOf asm = some SccCode.helloCells)
    (hlo0 : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    /- the controls' facts at `wXA` (`HabCtlA.habCtlHA_jr1L` at level 1) -/
    (hhabctl : ∀ v m1 σ1, HabCtlHA (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
        ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own (AR) I LB ls [])
      (Ly).lab helloSrc (Ly).Λ LB (AR)
      [] (wcJ0 (mWC (Ly).lab σC Jr1).J σ1) (wcR (RS helloLsw v) helloD)
      (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)) :
    SegWS (WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx LB ls0 frM (X0WH (Ly) (AX)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) helloSrc LB
      (fun fs => Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
        ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own (AR) I LB ls fs)
      (Frag.at (fun s c => ∃ v m1 σ1,
        At (Ly).exe (Ly).endPc (wcR (RS helloLsw v) helloD)
          (wcF (RS helloLsw v) helloD (FS (Ly) (RS0) helloLsw 0#64 v) m1 σ1)
          (wXA (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ
            ((Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ) rd G own (AR) I LB ls [])
            (Ly).lab (wcJ0 (mWC (Ly).lab σC Jr1).J σ1)) s c ∧ TP t s) [])
      (fun _ _ _ => False) := by
  have hp : o.prog = SccCode.helloCells := Option.some.inj (hpa.symm.trans hhp)
  have hprog : (Ly).prog = SccCode.helloCells := hp
  have hlo : (Ly).Λ.code.lo = lo := hlo0
  have hlab : ∀ l x, codeLabel lo SccCode.helloCells l = some x → (Ly).lab l = Int64.ofNat x :=
    fun l x h => Spike.Lib.PlaceWX.hlab_ofPlaceWX hpw IH l x (by rw [hlo, hp]; exact h)
  have hΛ : (Ly).Λ.abortLbl = Scc.Cert.Link.abortName :=
    Spike.Lib.PlaceWX.abortLbl_of_placeWX (Spike.Lib.PlaceWX.link IH hpw)
  -- `ownGHXW`'s separation, from A13's data part
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have ha : tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  -- `wc_main`'s region at the first stack's top
  obtain ⟨-, hR0, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hlo1 : (RS helloLsw (TOP)).lo ≤ -80 - helloD := by show (8 : Int) - helloLsw ≤ -80 - helloD; decide
  have hhi1 : (0 : Int) ≤ (RS helloLsw (TOP)).hi := by show (0 : Int) ≤ 8; decide
  have hD : (0 : Int) ≤ helloD := by decide
  have hRw : (wcR (RS helloLsw (TOP)) helloD).OK :=
    Region.callee_ok hR0 (by omega) (by omega) (by omega) (by omega)
  exact Spike.Lib.X64.HelloPh.Level1HA.hello_hab_closedLAg hpw i0 hpa hhp hlo0 hhabctl
    (Spike.Lib.X64.HelloPh.HabLftX.hP0X hprog hlo hlab (NT) hs.tcb ha hW (bandIn_wcAb hpw i0) hΛ hRw
      (by show (-helloD : Int) ≤ -336; decide) (by show (-296 : Int) ≤ 8; decide) (.inl rfl)
      Spike.Lib.X64.HelloPh.ClH.cl (Spike.Lib.X64.HelloPh.HAbStub.x0WH_abort hlab rfl))

end Spike.Lib.X64.HelloPh.Level1HAX

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.Level1HAX.bandIn_wcAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1HAX.bandIn_wcAb

/-- info: 'Spike.Lib.X64.HelloPh.Level1HAX.hello_hab_closedLAX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.Level1HAX.hello_hab_closedLAX

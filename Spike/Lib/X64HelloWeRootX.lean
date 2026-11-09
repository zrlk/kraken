/-
**`wc_rodata`'s entry states inside the start's level at the root, at `ownGHXW`** (x86-64; the counterpart of
`Spike/Lib/A64HelloWeRoot.lean`'s `hWe_root`, as `X64HelloWeSX` is `X64HelloWeS`'s at `ownGHXW`): at the root's
layout `ofPlaceWX hpw (HelloImms.immsH Λ0 i0)`,

- `hWe_rootX`: the root's `hWe` at `OX := ownGHXW Ly (Reserve.ntA Ly.lab)`, `WeSX.hWe_WSX` at the start's choices
  (`JS (Ly) 0#64 c0S`, `c0S`, main's thread pointer `tpOf (tcbS Ly)`), for every switch base `v` (the frame
  condition `FS` pins `v` at the first stack's top), at the root's context `LandRU.CtxRdHg … OX`, from the loader's
  `hpa`, `hhp`, `hlo` and A13's data part `hA13` (`ownGHXW`'s separation);
- `hWe_rootXg`: the same at any context `Ctx`.

`ownGHXW`'s separation (`hsep`, `ha`, `hW`) and the band of `wc_rodata`'s region on the pool (`hb`) are discharged
as `HrdRootX.hrd_RX` does: `StartPlaceLy.wsep_W`, `tcbWH_notG_W`, and `HrdRootX.bandRS` at `scc_rt_main`'s region
shifted to `wc_rodata`'s (`Region.callee_addr`).

## Differences from the AArch64 version

- main owns no TCB word on AArch64 (`A64HelloWeRoot.hWe_root` is at `ownGH`); here the level is at `ownGHXW`, and
  `hA13` is a premise (for `ownGHXW`'s separation).
- `scc_rt_main` is entered by a `call`, so `mNC`'s region is `MainGlue.RS helloLsw v` (AArch64:
  `swR v (-helloLsw) 0`), and `mNC` takes it (it records `%rbp`). The thread pointer is `tpOf (tcbS Ly)` (`fsBase`;
  AArch64 `TPIDR_EL0` at `pinA + 8`); `FS` pins `v` by its conjunct `1.2.1.1` (AArch64 `2.1.1`).
- The start's control facts are `HelloRdCf.start_ctl c0S.env` (AArch64 `C0S.c0S_ctl`), and the limit word's
  mapping is a runtime word's (`fld_mem` at `limA_tcb0`, as `X64HelloBoxRF`).
-/
import Spike.Lib.X64HelloWeRoot
import Spike.Lib.X64HelloWeSX
import Spike.Lib.X64HelloHrdRootX

namespace Spike.Lib.X64.HelloPh.WeRootX

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (FragS Region PlaceWX)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.WakePh (tcbM BandOnP)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.Flow.Hello1 (mNC mR)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartWcS (WSg)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)

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
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
/-- main's owned words before the spawn, at `scc_rt_nthreads`. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) NT

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "FR" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "TOP" => topS (Ly) 0#64

/-- **The root's `hWe` at `ownGHXW`, any context** (module doc): every state at `mNC` after the switch at base `v`
is inside the start's level `WSg OX … []` at the root's choices. -/
theorem hWe_rootXg (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true) (Ctx : FragS isa) (ls0 : Lsize) :
    ∀ v s c, At (Ly).exe (Ly).endPc (RS helloLsw v) (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 v)
        (mNC (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)) s c →
      WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) (ls0T ls0) (FR)
        (X0WH (Ly) (AX)) s c [] := by
  intro v s c h
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg =>
    obtain ⟨-, -, -, -, -, -, hF, -⟩ := h
    exact absurd hF.1.2.1.1 hv
  subst hv
  have hlab := Spike.Lib.X64.HelloPh.RootPlug.hlab_H hpw i0 hpa hhp hlo
  -- `ownGHXW`'s separation, from A13's data part
  have hs := Spike.Lib.X64.WakePh.StartPlaceLy.wsep_W hpw IH hA13
  have hsep : Spike.Lib.X64.PhRec.TcbSep (Ly) := hs.tcb
  have ha : tcbM (Ly) ≠ NT := hs.tcb_a 1 (by decide)
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hpw IH hA13
  -- the region's facts, and the band of `wc_rodata`'s region on the pool
  obtain ⟨hok, hR, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hpw i0
  have hbRS : BandOnP (Ly) (RS helloLsw (TOP)) (-288) 8 :=
    Spike.Lib.X64.HelloPh.HrdRootX.bandRS (show (8 - helloLsw : Int) ≤ -288 by decide)
      (show helloLsw < 16384 by decide) hok
  have hb : BandOnP (Ly) (mR (RS helloLsw (TOP))) (-208) 8 := fun k h1 h2 => by
    have e : (mR (RS helloLsw (TOP))).addr k = (RS helloLsw (TOP)).addr (-80 + k) :=
      Region.callee_addr _ (-80) (-208) 8 k
    rw [e]; exact hbRS _ (by omega) (by omega)
  refine Spike.Lib.X64.HelloPh.WeSX.hWe_WSX (c0 := c0S) (a := NT) (R := RS helloLsw (TOP))
    (Spike.Lib.X64.HelloPh.RootPlug.hp_H hpw i0 hpa hhp) (Spike.Lib.X64.HelloPh.RootPlug.hlo_H hpw i0 hlo)
    (Spike.Lib.X64.HelloPh.RootPlug.hΛ_H hpw i0) hlab (Spike.Lib.X64.HelloPh.RootPlug.hsite_H hpw i0 hpa hhp hlo)
    Spike.Lib.X64.HelloPh.ClH.cl (Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH hlab rfl)
    (Spike.Lib.X64HelloRdCf.start_ctl c0S.env)
    (Spike.Lib.X64.HelloPh.C0S.placedSE_c0S (Spike.Lib.X64.HelloImms.immsH_start Λ0 i0))
    hsep ha hW hb hR (show (8 - helloLsw : Int) ≤ -288 by decide) (show (8 : Int) ≤ 8 by decide)
    (tp := Spike.Lib.X64.Flow.Ret0.tpOf (tcbS (Ly)))
    (fun _ _ hJ => ⟨hJ.1.1, hJ.1.2.2⟩) ?_ Spike.Lib.X64.HelloPh.HrdR.hun_FS s c h
  have hw : Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (tcbS (Ly))) ∈ (Ly).rtWords := by
    show Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (Spike.Lib.X64.Flow.Ret0.pinA
      (_root_.Executable.labels (Ly).exe).label + 0#64 + 8#64)) ∈ _
    rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact (Ly).fld_mem (i := 1) (by decide)
  exact ((Ly).words_mapped _ hw).2.1

/-- **`hWe_rootXg` at the root's context `LandRU.CtxRdHg … OX`**: the shape of `StartH0XR.hst0_XRc`'s `hWe`. -/
theorem hWe_rootX (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo : Λ0.code.lo = lo)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (E : Entry) (rd : TermRun.Word → Prop) (ls ls0 : Lsize) :
    ∀ v s c, At (Ly).exe (Ly).endPc (RS helloLsw v) (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 v)
        (mNC (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)) s c →
      WSg (OX) (Ly) (AR) helloSrc DtW (Spike.Lib.X64.HelloPh.ClH (Ly))
        (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := asm) hpw i0 E rd ls (OX)) (L0T (Ly).Λ) (ls0T ls0) (FR)
        (X0WH (Ly) (AX)) s c [] :=
  hWe_rootXg hpw i0 hpa hhp hlo hA13 _ ls0

end Spike.Lib.X64.HelloPh.WeRootX

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.HelloPh.WeRootX.hWe_rootXg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRootX.hWe_rootXg

/-- info: 'Spike.Lib.X64.HelloPh.WeRootX.hWe_rootX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRootX.hWe_rootX

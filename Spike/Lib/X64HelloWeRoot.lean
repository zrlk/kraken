/-
**`wc_rodata`'s entry states inside the start's level at the root, and the root's immediates** (x86-64; the twin
of `Spike/Lib/A64HelloWeRoot.lean`): at the root's layout `ofPlaceWX hp (HelloImms.immsH Λ0 i0)`,

- `hWe_root`: the root's `hWe`, `WeS.hWe_WS` at the start's choices (`JS (Ly) 0#64 c0S`, `c0S`, main's thread
  pointer `tpOf (tcbS Ly)`), for every switch base `v` (the frame condition `FS` pins `v` at the first stack's top,
  `Land.fstable_FS` gives the region's facts there), generic in the context `Ctx`, from the loader's `hpa`, `hhp`,
  `hlo` only;
- `hWe_rootRdH`: `hWe_root` at `LandRU.CtxRdH` (rodata's word predicate `fun _ => True`);
- `rdImms_root`, `hme_root`, `hzI_root`, `hm_root`: the root's `hRdI`, `hme`, `hzI`, `hm` at the certificate's
  table `i0 := HelloImms.i0M Λ0` (`HelloImms.rdImms_iRdM`, `hmeC_iRdM`, `hm_iRdM`, `HabCtlA.hz_i0M`).

## Differences from the AArch64 version

- `scc_rt_main` is entered by a `call`, so `mNC`'s region is `MainGlue.RS helloLsw v` (AArch64:
  `swR v (-helloLsw) 0`), and `mNC` takes it (it records `%rbp`). The thread pointer is `tpOf (tcbS Ly)` (`fsBase`;
  AArch64 `TPIDR_EL0` at `pinA + 8`); `FS` pins `v` by its conjunct `1.2.1.1` (AArch64 `2.1.1`).
- The start's control facts are `HelloRdCf.start_ctl c0S.env` (AArch64 `C0S.c0S_ctl`), and the limit word's
  mapping is a runtime word's (`fld_mem` at `limA_tcb0`, as `X64HelloBoxRF`).
-/
import Spike.Lib.X64HelloWeS
import Spike.Lib.X64HelloRootPlug
import Spike.Lib.X64HelloHrdR
import Spike.Lib.X64HelloLand
import Spike.Lib.X64HelloHabCtlA
import Spike.Lib.X64HelloLandRU

namespace Spike.Lib.X64.HelloPh.WeRoot

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lsize)
open Spike.Lib (FragS)
open Spike.Lib.X64 (At)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.WakePh.MainGlue (FS JS RS tcbS topS)
open Spike.Lib.X64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.X64.HelloPh.StartWcS (WS)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : Spike.Lib.PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH0" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hp (IH0)

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

/-- **The root's `hWe` at any context** (module doc): every state at `mNC` after the switch at base `v` is inside
the start's level `StartWcS.WS … []` at the root's choices. -/
theorem hWe_root (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo : Λ0.code.lo = lo)
    (Ctx : FragS isa) (ls : Lsize) :
    ∀ v s c, At (Ly).exe (Ly).endPc (RS helloLsw v) (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 v)
        (Spike.Lib.X64.Flow.Hello1.mNC (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)) s c →
      WS (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp (IH0)) helloSrc DtW
        (Spike.Lib.X64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) (ls0T ls) (Spike.Lib.X64HelloRdCf.frH c0S.env)
        (X0WH (Ly) (AX)) s c [] := by
  intro v s c h
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = topS (Ly) 0#64
  case neg =>
    obtain ⟨-, -, -, -, -, -, hF, -⟩ := h
    exact absurd hF.1.2.1.1 hv
  subst hv
  have hlab := Spike.Lib.X64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo
  obtain ⟨-, hok, -⟩ := Spike.Lib.X64.HelloPh.Land.fstable_FS hp i0
  refine Spike.Lib.X64.HelloPh.WeS.hWe_WS (c0 := c0S)
    (Spike.Lib.X64.HelloPh.RootPlug.hp_H hp i0 hpa hhp) (Spike.Lib.X64.HelloPh.RootPlug.hlo_H hp i0 hlo)
    (Spike.Lib.X64.HelloPh.RootPlug.hΛ_H hp i0) hlab (Spike.Lib.X64.HelloPh.RootPlug.hsite_H hp i0 hpa hhp hlo)
    Spike.Lib.X64.HelloPh.ClH.cl (Spike.Lib.X64.HelloPh.StartGlue.x0WH_of_freeNH hlab rfl)
    (Spike.Lib.X64HelloRdCf.start_ctl c0S.env)
    (Spike.Lib.X64.HelloPh.C0S.placedSE_c0S (Spike.Lib.X64.HelloImms.immsH_start Λ0 i0))
    hok (show (8 - helloLsw : Int) ≤ -288 by decide) (show (8 : Int) ≤ 8 by decide)
    (tp := Spike.Lib.X64.Flow.Ret0.tpOf (tcbS (Ly)))
    (fun _ _ hJ => ⟨hJ.1.1, hJ.1.2.2⟩) ?_ Spike.Lib.X64.HelloPh.HrdR.hun_FS s c h
  have hw : Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (tcbS (Ly))) ∈ (Ly).rtWords := by
    show Spike.Lib.X64.Flow.Ret0.limA (Spike.Lib.X64.Flow.Ret0.tpOf (Spike.Lib.X64.Flow.Ret0.pinA
      (_root_.Executable.labels (Ly).exe).label + 0#64 + 8#64)) ∈ _
    rw [(Ly).lab_pin, Spike.Lib.X64.Rt.limA_tcb0]
    exact (Ly).fld_mem (i := 1) (by decide)
  exact ((Ly).words_mapped _ hw).2.1

/-- **`hWe_root` at `LandRU.CtxRdH`**: the root's `hWe` at the landing's context, verbatim. -/
theorem hWe_rootRdH (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo : Λ0.code.lo = lo)
    (E : Scc.Sem.Entry) (ls : Lsize) :
    ∀ v s c, At (Ly).exe (Ly).endPc (RS helloLsw v) (FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) helloLsw 0#64 v)
        (Spike.Lib.X64.Flow.Hello1.mNC (Ly).lab (RS helloLsw v) (JS (Ly) 0#64 c0S)) s c →
      WS (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.X64.WakeOD.arW hp (IH0)) helloSrc DtW
        (Spike.Lib.X64.HelloPh.ClH (Ly))
        (Spike.Lib.X64.HelloPh.LandRU.CtxRdH (asm := asm) hp i0 E (fun _ => True) ls) (L0T (Ly).Λ) (ls0T ls)
        (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) s c [] :=
  hWe_root hp i0 hpa hhp hlo _ ls

/-! ## The root's immediates at `i0 := HelloImms.i0M Λ0` -/

/-- **`hRdI`** at the root's table (`HelloImms.rdImms_iRdM`). -/
theorem rdImms_root :
    Spike.Lib.X64.HelloPh.RdPlS.RdImms
      (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ :=
  have h := Spike.Lib.X64.HelloImms.rdImms_iRdM hp
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **`hme`** at the root's table (`HelloImms.hmeC_iRdM`). -/
theorem hme_root :
    (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ.imms
      Spike.Lib.SrcCalls.setupCont "me" 0 =
      some (Spike.Lib.X64WakeLoadT.tcb0
        (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ) :=
  Spike.Lib.X64.HelloImms.hmeC_iRdM hp

/-- **`hzI`** at the root's table (`HabCtlA.hz_i0M`). -/
theorem hzI_root : Spike.Lib.X64.HelloImms.i0M Λ0 Spike.Lib.X64HelloMainPreSrc.newTerm "z" 0 = some 0 :=
  Spike.Lib.X64.HelloPh.HabCtlA.hz_i0M Λ0

/-- **`hm`** at the root's table (`HelloImms.hm_iRdM`). -/
theorem hm_root :
    (RuntimeLayout.ofPlaceWX hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))).Λ.imms
      Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2 :=
  Spike.Lib.X64.HelloImms.hm_iRdM hp

end Spike.Lib.X64.HelloPh.WeRoot

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hWe_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hWe_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hWe_rootRdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hWe_rootRdH

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.rdImms_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.rdImms_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hme_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hme_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hzI_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hzI_root

/-- info: 'Spike.Lib.X64.HelloPh.WeRoot.hm_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.WeRoot.hm_root

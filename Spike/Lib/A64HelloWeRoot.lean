/-
**`wc_rodata`'s entry states inside the start's level at the root, and the root's immediates** (AArch64): at the
root's layout `ofPlaceW hp (C0S.immsH Λ0 i0)`,

- `hWe_root`: `RootInv.hello_root_inv`'s `hWe`, `WeS.hWe_WS` at the start's choices (`JS (Ly) 0#64 c0S`, `c0S`,
  main's thread pointer `pinA + 8`), for every switch base `v` (the frame condition `FS` pins `v` at the first
  stack's top, `Land.fstable_FS` gives the region's facts there), generic in the context `Ctx` (so in particular
  at `LandRU.CtxRdH`), from the loader's `hpa`, `hhp`, `hlo` only;
- `rdImms_root`, `hme_root`, `hzI_root`, `hm_root`: the root's `hRdI`, `hme`, `hzI`, `hm` at the certificate's
  table `i0 := ImmsMe.i0M Λ0` (`ImmsMe.rdImms_iRdM`, `hmeC_iRdM`, `hm_iRdM`, `HabCtlA.hz_i0M`).
-/
import Spike.Lib.A64HelloWeS
import Spike.Lib.A64HelloRootPlug
import Spike.Lib.A64HelloHrdR
import Spike.Lib.A64HelloLand
import Spike.Lib.A64HelloHabCtlA
import Spike.Lib.A64HelloLandRU

namespace Spike.Lib.A64.HelloPh.WeRoot

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64Consumer (Lsize)
open Spike.Lib (FragS)
open Spike.Lib.A64.Flow (At swR)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.HelloPh.StartH0G (helloLsw)
open Spike.Lib.A64.HelloPh.StartWcS (WS)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.HelloSrc (helloSrc)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : Spike.Lib.PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0`. -/
local notation "IH0" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hp (IH0)

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The first stack's top. -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA (Ly).lab + 0#64 + 16384#64

/-- **`hello_root_inv`'s `hWe` at any context** (module doc): every state at `mNC` after the switch at base `v`
is inside the start's level `StartWcS.WS … []` at the root's choices. -/
theorem hWe_root (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo)
    (Ctx : FragS isaLSE2) (ls : Lsize) :
    ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) helloLsw 0#64 v)
        (Spike.Lib.A64.Flow.Hello1.mNC (Ly).lab (JS (Ly) 0#64 c0S)) s c →
      WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp (IH0)) helloSrc DtW
        (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (L0T (Ly).Λ) (ls0T ls) (Spike.Lib.HelloRdCf.frH c0S.env)
        (X0WH (Ly) (AX)) s c [] := by
  intro v s c h
  -- the frame condition pins `v` at the first stack's top
  by_cases hv : v = TOP
  case neg =>
    obtain ⟨-, -, -, -, -, -, hF, -⟩ := h
    exact absurd hF.2.1.1 hv
  subst hv
  have hlab := Spike.Lib.A64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo
  obtain ⟨hok, hal, -⟩ := Spike.Lib.A64.HelloPh.Land.fstable_FS hp i0
  refine Spike.Lib.A64.HelloPh.WeS.hWe_WS (c0 := c0S)
    (Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp) (Spike.Lib.A64.HelloPh.RootPlug.hlo_H hp i0 hlo)
    (Spike.Lib.A64.HelloPh.RootPlug.hΛ_H hp i0) hlab (Spike.Lib.A64.HelloPh.RootPlug.hsite_H hp i0 hpa hhp hlo)
    Spike.Lib.A64.HelloPh.ClH.cl (Spike.Lib.A64.HelloPh.StartGlue.x0WH_of_freeNH hlab rfl)
    Spike.Lib.A64.HelloPh.C0S.c0S_ctl
    (Spike.Lib.A64.HelloPh.C0S.placedSE_c0S (Spike.Lib.A64.HelloPh.C0S.immsH_start Λ0 i0))
    hok hal (show (-helloLsw : Int) ≤ -288 by decide) (show (0 : Int) ≤ 0 by decide)
    (tp := UInt64.ofBitVec (Spike.Lib.A64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64))
    (fun _ _ hJ => ⟨hJ.1.1, hJ.1.2.2⟩) ?_ Spike.Lib.A64.HelloPh.HrdR.hun_FS s c h
  rw [Spike.Lib.A64.Rt.pinA_lab0, Spike.Lib.A64.Rt.limA_tcb0]
  exact ((Ly).words_mapped _ ((Ly).fld_mem (by decide))).2.1

/-- **`hWe_root` at `LandRU.CtxRdH`**: `hello_root_inv`'s `hWe` verbatim. -/
theorem hWe_rootRdH (hpa : Scc.Sem.A64.textProgram asm = .ok o.prog)
    (hhp : Scc.Sem.A64.textProgram asm = .ok SccCode.helloProg) (hlo : Λ0.code.lo = lo)
    (E : Scc.Sem.Entry) (ls : Lsize) :
    ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) helloLsw 0#64 v)
        (Spike.Lib.A64.Flow.Hello1.mNC (Ly).lab (JS (Ly) 0#64 c0S)) s c →
      WS (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) (Spike.Lib.WakeOD.arW hp (IH0)) helloSrc DtW
        (Spike.Lib.A64.HelloPh.ClH (Ly))
        (Spike.Lib.A64.HelloPh.LandRU.CtxRdH (asm := asm) hp i0 E (fun _ => True) ls) (L0T (Ly).Λ) (ls0T ls)
        (Spike.Lib.HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) s c [] :=
  hWe_root hp i0 hpa hhp hlo _ ls

/-! ## The root's immediates at `i0 := ImmsMe.i0M Λ0` -/

/-- **`hRdI`** at the root's table (`ImmsMe.rdImms_iRdM`). -/
theorem rdImms_root :
    Spike.Lib.A64.HelloPh.RdPlS.RdImms
      (RuntimeLayout.ofPlaceW hp (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0))).Λ :=
  have h := Spike.Lib.A64.HelloPh.ImmsMe.rdImms_iRdM hp
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **`hme`** at the root's table (`ImmsMe.hmeC_iRdM`). -/
theorem hme_root :
    (RuntimeLayout.ofPlaceW hp (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0))).Λ.imms
      Spike.Lib.SrcCalls.setupCont "me" 0 =
      some (Spike.Lib.WakeLoadT.tcb0
        (RuntimeLayout.ofPlaceW hp (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0))).Λ) :=
  Spike.Lib.A64.HelloPh.ImmsMe.hmeC_iRdM hp

/-- **`hzI`** at the root's table (`HabCtlA.hz_i0M`). -/
theorem hzI_root : Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0 :=
  Spike.Lib.A64.HelloPh.HabCtlA.hz_i0M Λ0

/-- **`hm`** at the root's table (`ImmsMe.hm_iRdM`). -/
theorem hm_root :
    (RuntimeLayout.ofPlaceW hp (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0))).Λ.imms
      Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2 :=
  Spike.Lib.A64.HelloPh.ImmsMe.hm_iRdM hp

end Spike.Lib.A64.HelloPh.WeRoot

/-- info: 'Spike.Lib.A64.HelloPh.WeRoot.hWe_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeRoot.hWe_root

/-- info: 'Spike.Lib.A64.HelloPh.WeRoot.hWe_rootRdH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeRoot.hWe_rootRdH

/-- info: 'Spike.Lib.A64.HelloPh.WeRoot.rdImms_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeRoot.rdImms_root

/-- info: 'Spike.Lib.A64.HelloPh.WeRoot.hme_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeRoot.hme_root

/-- info: 'Spike.Lib.A64.HelloPh.WeRoot.hzI_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeRoot.hzI_root

/-- info: 'Spike.Lib.A64.HelloPh.WeRoot.hm_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.WeRoot.hm_root

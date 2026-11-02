/-
**`MainWcPS.hWp`, `hWs` at the root's context at `ownGHXW` with the placement discharged** (x86-64 only; the
`ownGHXW` counterpart of `X64HelloMainWcL1Wj`): `MainWcL1Wi.hWp_L1X`/`hWs_L1X` at `Level1I`'s `Jr` and `Jr1`, their
`hpl` by `WcPlS.hplP_S`/`hplS_S` (the entry controls placed, `MainWcL1Wj.plE_J0`/`plE_J1`; the region,
`MainWcL1Wj.wcR_L1`). The placement does not read the owned words, so these are `X64HelloMainWcL1Wj`'s.

- `hWp_L1PX`, `hWs_L1PX`: the statements, at the level `Level1I.W1Rg … (ownGHXW Ly ntA)` and the level's memory
  side at `ownGHXW`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there, so its level is at `ownGH` only. Against
`X64HelloMainWcL1Wj`: the level and the memory side are at `ownGHXW` (`MainWcL1Wi.hWp_L1X`/`hWs_L1X`).
-/
import Spike.Lib.X64HelloMainWcL1Wj
import Spike.Lib.X64HelloMainWcL1WiX

namespace Spike.Lib.X64.HelloPh.MainWcL1Wj

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Entry ValRep)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64Consumer (Lbl Lsize)
open Spike.Lib (PlaceWX)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.HelloPh (lo)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcR wcF JrT)
open Spike.Lib.X64.Flow.HelloWc (WcPreWH WcSp0WH)
open Spike.Lib.X64.WakeTP (tpG)
open Spike.Lib.X64.KeepTP (tpXa)
open Spike.Lib.X64.HelloPh.StartGlue (X0WH)
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64.Flow.HelloJr1 (JrRL)
open Spike.Lib.X64.WakePh.MainGlue (FS RS tcbS topS)
open Spike.Lib.X64.Flow.Ret0 (tpOf)
open Spike.Lib.X64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64WakeSrcDefs (mainTidLbl)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open Spike.Lib.X64HelloMainPreSrc (newTerm)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.X64.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)
  (E : Entry) (rd : TermRun.Word → Prop) (ls : Lsize)

set_option hygiene false in
local notation "IH" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX hpw IH

set_option hygiene false in
local notation "RS0" => Spike.Lib.X64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AR" => Spike.Lib.X64.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- main's thread pointer. -/
local notation "TV" => tpOf (tcbS (Ly))

set_option hygiene false in
/-- The first stack's top (the start's `v`). -/
local notation "TOP" => topS (Ly) 0#64

set_option hygiene false in
/-- `wc_main`'s region at the call. -/
local notation "RW" => wcR (RS helloLsw (TOP)) helloD

set_option hygiene false in
/-- `wc_main`'s frame condition at the caller's state `m1`, `σ1`. -/
local notation "FW" => wcF (RS helloLsw (TOP)) helloD (FS (Ly) (RS0) helloLsw 0#64 (TOP)) m1 σ1

set_option hygiene false in
/-- The level's marks (`E`'s at `asm`). -/
local notation "MU" => (Scc.Sem.X64.target (Scc.Sem.X64.kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
/-- The level's memory side at no frame, under main's thread pointer, at `ownGHXW`. -/
local notation "MS" => tpXa (Spike.Lib.X64ConsumerA.msOfA (Ly).Λ (MU) rd
  (Spike.Lib.X64HelloGOf2H.gWH hpw IH (Spike.Lib.X64WakeHG.cTW hpw IH))
  (fun s _ => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT) s)
  (AR) I (Spike.Lib.X64ConsumerA.upd (LB) l b) (Spike.Lib.X64ConsumerA.updN (ls0T ls) l n) []) (TV)

set_option hygiene false in
/-- The level at the root's context, no frame, at `ownGHXW`. -/
local notation "WL" => fun s c => Spike.Lib.X64.HelloWf.W1Hg (Spike.Lib.X64.HelloPh.ownGHXW (Ly) (NT)) (Ly) (AR)
  helloSrc DtW
  (Spike.Lib.X64.HelloPh.ClH (Ly)) (Spike.Lib.X64.HelloPh.Land.CtxR1H (asm := asm) hpw i0 E rd ls) (LB) (ls0T ls)
  (Spike.Lib.X64HelloRdCf.frH c0S.env) (X0WH (Ly) (AX)) l b n s c []

set_option hygiene false in
/-- `wc_main`'s entry invariant at `Level1I`'s `Jr` (`wc_rodata`'s return on the slice at `l`). -/
local notation "J0" => wcJ0 (mWC (Ly).lab σC (JrT (JrRL (Spike.Lib.X64ConsumerA.upd (LB) l b) c0S.env l) (TV)
  (RS helloLsw (TOP)))).J σ1

set_option hygiene false in
/-- `wc_main`'s caller's invariant at the box's `new` (`Land.Jr1LH`). -/
local notation "J1" => wcJ0 (mWC (Ly).lab σC (Spike.Lib.X64.HelloPh.Land.Jr1LH hpw i0 l b)).J σ1

variable {I : Spike.Lib.X64ConsumerS.InvS} {l : WeakMem.AllocLabel} {b n : Nat} {σC σ1 : FAS} {m1 : MachineData}

/-- **`hWp` at `CtxR1H` at `ownGHXW`, placed** (`hWp_L1P` at `ownGHXW`): `MainWcL1Wi.hWp_L1X` at `Level1I`'s
`Jr`, `hpl` by `WcPlS.hplP_S`. -/
theorem hWp_L1PX (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : (Ly).Λ.imms newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    WcPreWH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J0) (J1) :=
  have hR := wcR_L1 hpw i0 m1 σ1
  Spike.Lib.X64.HelloPh.MainWcL1Wi.hWp_L1X hpw i0 E rd ls hp hpa hhp hlo0 hc hA13 hslot
    (Spike.Lib.X64.HelloPh.WcPlS.hplP_S hR.1 hR.2.1 hR.2.2 (plE_J0 hpw i0 hl hslot) (plE_J1 hpw i0 hz hl hslot))

/-- **`hWs` at `CtxR1H` at `ownGHXW`, placed** (`hWs_L1P` at `ownGHXW`): `MainWcL1Wi.hWs_L1X`, `hpl` by
`WcPlS.hplS_S`. -/
theorem hWs_L1PX (hp : o.prog = SccCode.helloCells) (hpa : Scc.Sem.X64.cellsOf asm = some o.prog)
    (hhp : Scc.Sem.X64.cellsOf asm = some SccCode.helloCells) (hlo0 : Λ0.code.lo = lo)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    (hz : (Ly).Λ.imms newTerm "z" 0 = some 0) (hl : (LB) l = none)
    (hslot : σC.slot (-16) = Spike.Lib.X64.Flow.Ret0.pinA (Ly).lab + 0#64 + 8#64) :
    WcSp0WH (Spike.Lib.X64.NoSetFsW (tpG (TV) (WL)) (Spike.Lib.X64.PhRec.K (Ly) (RS0)))
      (Spike.Lib.X64.PhRec.K (Ly) (RS0)) (Ly).exe (Ly).endPc (RW) (FW) (MS) (J1) :=
  have hR := wcR_L1 hpw i0 m1 σ1
  Spike.Lib.X64.HelloPh.MainWcL1Wi.hWs_L1X hpw i0 E rd ls hp hpa hhp hlo0 hc hA13 hslot
    (Spike.Lib.X64.HelloPh.WcPlS.hplS_S (by have := hR.2.1; omega) hR.2.2 (plE_J1 hpw i0 hz hl hslot))

end Spike.Lib.X64.HelloPh.MainWcL1Wj

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.hWp_L1PX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.hWp_L1PX

/-- info: 'Spike.Lib.X64.HelloPh.MainWcL1Wj.hWs_L1PX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.MainWcL1Wj.hWs_L1PX

/-
**hello's start segment at the root's immediate table** (AArch64; the twin of
`A64WakeStartH0R`'s `hst0_ofW`): `StartH0B.hst0_ofH` at `i := C0S.immsH Λ0 i0` for any certificate table `i0`
(`ImmsH.iH Λ0 = immsH Λ0 helloImms`, `ImmsRd.iRd Λ0 = immsH Λ0 i0Rd`; the twin of
`WakeFinalCAW.iW`), its start segment `hG` from `StartH0G.hello_start_wc_h0G` at the root's choices (`L0T`,
`ls0T ls0`, `DtW`, `Ctx`, `frM`, `helloSrc`, the entry's marks, `ownGH`, `gW … cTW`), its heap abort's segment
`hC` from `StartH0C.hello_hab_closed`:

- `hme` by `C0S.immsH_start` (`ImmsH.hme_iH`);
- hello's depths, concrete: `helloD = 400`, `helloLsw = 480` (`StartH0G.helloD_bounds`: `304 ≤ 400`,
  `400 % 16 = 0`, `80 + 400 ≤ 480`, `480 % 8 = 0`, `480 ≤ 12288`, so `hD`/`hLD`/`hLmax` hold together within the
  new stack of `16384` bytes; `wc_main`'s region bottom `-400` covers the heap abort stub's `R.lo ≤ -352` and
  the hat's `R.lo ≤ -400`).

Left as premises:
- the loader's facts `hpa`, `hhp`, `hlo0`, `hstat`, `hA13`, `hctr2`, `hc`;
- `wc_main`'s source and frame premises at these choices `hWe`, `hrd`, `hloc`, `hq`, `hret`, `hPw`;
- `hxa` (the allocator's fresh-label landing in `ms [FR]`'s allocation fragment; wake's `StartH0U`
  `hxa` twin);
- `hhabctl` (`HabCtl.HabCtlH`);
- `hhabctlRd` (`HabCtlRd.HabCtlRdH`: the controls' facts at `wc_rodata`'s heap abort).

`wc_rodata`'s heap abort exit (`StartH0B`'s `hCrd`) closes by `RdHAb.hello_rd_hab_closed`,
at the root's frame `frM := FR`.

- `hst0_ofH_i0`: the statement; `hst0_ofH_iH`: at `i0 := helloImms`.

Superseded: level 0 ends at rodata's landing, so the root uses
`StartH0R0.hst0_ofH0_i0` (no `hret`, `hPw`, `hhabctl`; those move to level 1's segment from rodata's landing).
This file is kept frozen.
-/
import Spike.Lib.A64HelloStartH0B
import Spike.Lib.A64HelloImmsH
import Spike.Lib.A64HelloRdHAb
import Spike.Lib.HelloGOf2H

namespace Spike.Lib.A64.HelloPh.StartH0R

variable {asm : String}

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Entry)
open Scc.Sem.A64 (textProgram)
open Spike.Lib.A64.Rt (RuntimeLayout entryR rtF)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64ConsumerA (TakeCKS)
open Spike.Lib.A64.WakePh (lo)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartGlue (X0WH)
open Spike.Lib.A64.HelloPh.StartWcS (WS rdJH)
open Spike.Lib.A64.Flow (swR At enter leave)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow.Hello1 (AG mR mF mRdJ0 mNC aR mWC)
open Spike.Lib.A64.Flow.HelloRd (rN rX pN RdPreW)
open Spike.Lib.A64.Flow.HelloM (wcR wcF wcJ0)
open Spike.Lib.A64.Flow.HelloWc (wXH)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.HelloPh.MainGlueS (MainWcPS)
open Spike.Lib.A64.HelloPh.StartH0G (helloD helloLsw)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.HabCtl (HabCtlH)
open Spike.Lib (FragS Frag SegWS LocalRun)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.HelloPh.C0S (c0S)
open Spike.Lib.HelloSrc (helloSrc)

/-- `Flow`'s abstract state. -/
local notation "FAS" => Spike.Lib.A64.Flow.AS

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hpw : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table at the certificate's table `i0` (`C0S.immsH Λ0 i0`; `ImmsH.iH` at
`i0 := helloImms`, `ImmsRd.iRd` at `i0 := i0Rd`; wake's `WakeFinalCAW.iW`). -/
local notation "IH" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceW hpw IH

set_option hygiene false in
local notation "AR" => Spike.Lib.WakeOD.arW hpw IH

set_option hygiene false in
local notation "NT" => Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 (Ly)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The root's memory sides at the frames `fs`, the entry's marks. -/
local notation "MSF" => fun fs : List TermRun.Frame => Spike.Lib.A64ConsumerA.msOfA (Ly).Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm (Ly).Λ) rd
  (Spike.Lib.HelloGOf2H.gWH hpw IH (Spike.Lib.WakeHG.cTW hpw IH)) (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) NT s)
  (AR) I (LB) (ls0T ls) fs

set_option hygiene false in
local notation "FR" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- The start's level at the root's choices. -/
local notation "WP" => WS (Ly) NT (AR) helloSrc DtW (Spike.Lib.A64.HelloPh.ClH (Ly)) Ctx (LB) (ls0T ls0) (FR)
  (X0WH (Ly) (AX))

set_option hygiene false in
local notation "KR" => Spike.Lib.A64.PhRec.K (Ly) RS

set_option hygiene false in
local notation "JW" => JS (Ly) 0#64 c0S

set_option hygiene false in
local notation "J'" => rdJH (Ly).lab (JW)


/-- **hello's start segment at `iH`** (`RootOpen.hst0`'s twin): `hst0_ofH` with `hG` by `hello_start_wc_h0G` at
the root's choices (`hme` by `immsH_start`), `hC` by `hello_hab_closed`, `hCrd` by `hello_rd_hab_closed` (at
`frM := FR`), and the source premises carried (module doc). -/
theorem hst0_ofH_i0 (E : Entry) (hE : E.Ok (Ly).Λ)
    {Ctx : FragS isaLSE2} {ls0 : Lsize}
    {rd : TermRun.Word → Prop} {I : Spike.Lib.A64ConsumerS.InvS} {ls : Lsize}
    (hpa : textProgram asm = .ok o.prog)
    (hhp : textProgram asm = .ok SccCode.helloProg)
    (hlo0 : Λ0.code.lo = lo) (hstat : Λ0.static = fun _ => none)
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    (hctr2 : ∀ a ∈ [(Ly).pnA, (Ly).lockA, (Ly).freeNA, (Ly).nextA], a ≠ Spike.Lib.HelloGOf2H.lim2AH (Ly))
    (hc : Spike.Lib.A64.Rt.CtrZ o)
    {J1 : FAS → FAS → Ctl → Prop}
    (hWe : ∀ v s c, At (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) (mNC (Ly).lab (JW))
      s c → WP s c [])
    (hrd : ∀ v m0 σC, RdPreW (fun s c => WP s c [FR]) KR (Ly).exe (Ly).endPc (mR (swR v (-helloLsw) 0))
      (mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC) ((MSF) [FR]) (mRdJ0 (J') σC) (J1 σC))
    (hloc : ∀ σC σ c, mRdJ0 (J') σC σ c → ∃ c', LocalRun helloSrc c c' ∧ J1 σC σ c')
    (hq : ∀ σC σ c, J1 σC σ c → ∃ q : Call, q.OK ((MSF) [FR]) (Ly).lab ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u ((MSF) [FR]) = 3#64)
    {t : UInt64} {Jp Jp' Jx1 J2 J2' J3 J4 J5 Jr Jr1 : BitVec 64 → MachineData → FAS → FAS → Ctl → Prop}
    (hxa : ∀ v m0 σC, ∀ q : AG ((MSF) [FR]) (Ly).lab, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF (swR v (-helloLsw) 0) (FS (Ly) RS helloLsw 0#64 v) m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Spike.Lib.A64.Flow.Abs (mR (swR v (-helloLsw) 0)) ⟨-48, []⟩ mC σ ∧
        (rN (Ly).lab (mRdJ0 (J') σC) (J1 σC) .call).J σ c ∧
        (Spike.Lib.A64.Alloc.N (Ly).lab ((MSF) [FR]) q.1 .e).J (enter (-48) σ) c ∧
        Spike.Lib.A64.Flow.CKept (mR (swR v (-helloLsw) 0)) (-48) (-160) 0 mC m) →
      ∀ l b w s c, (LB) l = none →
        At (Ly).exe (Ly).endPc (aR (mR (swR v (-helloLsw) 0))) F' (Ea ((MSF) [FR]) q.1 l b w) s c →
        ((MSF) [FR]).xa l b w s c)
    (hret : ∀ v m0 σC σ c, (rX ((MSF) [FR]) (Ly).lab (LB) (J1 σC) .sp0).J σ c → Jp v m0 σC σ c)
    (hPw : ∀ v m0 σC, MainWcPS (WP) KR helloSrc (LB) (MSF) (Ly).exe (Ly).endPc (swR v (-helloLsw) 0) helloD
      (FS (Ly) RS helloLsw 0#64 v) (FR) m0 σC (Jp v m0 σC) (Jp' v m0 σC) (Jx1 v m0 σC) (J2 v m0 σC) (J2' v m0 σC)
      (J3 v m0 σC) (J4 v m0 σC) (J5 v m0 σC) (Jr v m0 σC) (Jr1 v m0 σC) t)
    /- named premise -/
    (hhabctl : ∀ v m0 σC σ1, HabCtlH ((MSF) []) (Ly).lab helloSrc (Ly).Λ (LB) (AR) []
      (wcJ0 (mWC (Ly).lab σC (Jr1 v m0 σC)).J σ1))
    /- named premise (`HabCtlRdH`): the controls' facts at `rX .abort` -/
    (hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH ((MSF) [FR]) (Ly).lab helloSrc (Ly).Λ (LB) (AR)
      [FR] (J1 σC)) :
    SegWS (W0H (asm := asm) hpw IH E DtW Ctx (ls0T ls0) (FR)) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH
        (Ly))) helloSrc (LB)
      (MSF) (StartPH hpw IH E) (fun _ _ _ => False) :=
  Spike.Lib.A64.HelloPh.StartH0B.hst0_ofH hpw IH E hE hpa hhp
    (Spike.Lib.A64.HelloPh.StartH0G.hello_start_wc_h0G hpw IH hE hpa hhp hlo0 hstat hA13 hctr2 hc
      (Spike.Lib.A64.HelloPh.C0S.immsH_start Λ0 _) hWe hrd hloc hq hxa hret hPw)
    (Spike.Lib.A64.HelloPh.StartH0C.hello_hab_closed hpw IH hpa hhp hlo0 hhabctl)
    (Spike.Lib.A64.HelloPh.RdHAb.hello_rd_hab_closed hpw IH (Ctx := Ctx) (ls0 := ls0) hpa hhp hlo0 hhabctlRd)

/-- **`hst0_ofH_i0` at the certificate's table** (`i0 := helloImms`, the root's table `ImmsH.iH`). -/
theorem hst0_ofH_iH : type_of% (hst0_ofH_i0 (asm := asm) hpw SccCode.helloImms) := hst0_ofH_i0 (asm :=
    asm) hpw SccCode.helloImms

end Spike.Lib.A64.HelloPh.StartH0R

/-- info: 'Spike.Lib.A64.HelloPh.StartH0R.hst0_ofH_i0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0R.hst0_ofH_i0

/-- info: 'Spike.Lib.A64.HelloPh.StartH0R.hst0_ofH_iH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.StartH0R.hst0_ofH_iH

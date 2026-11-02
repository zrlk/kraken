/-
**hello's root premise inventory** (AArch64; the non-vacuity checklist): hello's
obligations `WakeObligationsR` at the root, generic in the certificate text `asm`, with every choice the h1/h2
chains fix made (`Dt := DtW`, `Ctx := Land.CtxRH`, `frM := frH c0S.env`, the third level `W2I` at `DtW`, `h2`'s
invariant `inv2H`), every derived premise derived, and every remaining one an explicit, named hypothesis.

- derived: `hpin2` (`ChildRoot.hpin2_H` from the pinned `.zero`, `hz`/`hn`); the base (`RootPlug.RootRest.toBase`
  of the explicit fields, `Dt := DtW`); `toPrem` (`RootInstW`, its `H1GAH0V` `CalRootI.h0V_I`:
  `WcRootI.wcWf_I`/`wcl_I`, `CalRootI.res_I`/`tcb_I`); `h2` (`H2Root.h2Stmt_root`'s first conjunct at
  `toPrem`); `hW2` (`hW2_I` at `PhRec.μ`, the entry's marks by `resolve_of_parsed`); `pass`
  (`HelloPassI.passH_root`, with `passT` fixed to `A64HelloPass.helloPassT`, as wake fixes its own).
- `hello_root_inv`: the statement; its hypotheses are listed in the table at the end of the file. `refObl`'s
  `hDt` is `fun _ h => h` at `Dt := DtW` (`RefRootI`, which discharges `hobl` on hello-b4).

The listing is instantiated, without the certificate, in `A64HelloRootLit` (`asm := SccCode.helloAsm`):
`hpa`/`hhp`/`hd` become its one parse premise `hparse`, `hz`/`hn`/`hc` are decided there, and the layout facts
wait for the linked executable (row hello-elf).
-/
import Spike.Lib.HelloAssemblyRS
import Spike.Lib.A64HelloRootInstW
import Spike.Lib.A64HelloRootPlug
import Spike.Lib.A64HelloH2Root
import Spike.Lib.A64HelloChildRoot
import Spike.Lib.A64HelloRootHG
import Spike.Lib.A64HelloZR
import Spike.Lib.HelloPassI
import Spike.Lib.A64HelloSegEnd
import Spike.Lib.A64HelloSegEndX2
import Spike.Lib.A64HelloHClWR
import Spike.Lib.A64HelloH0Stmt
import Spike.Lib.A64WakeHClW
import Spike.Lib.A64HelloRootOkb
import Spike.Lib.A64HelloRootL1F
import Spike.Lib.A64HelloRootL1U
import Spike.Lib.A64HelloMainWcL1A
import Spike.Lib.HelloXOk
import Spike.Lib.HelloHcl
import Spike.Lib.A64HelloRefRootI
import Spike.Lib.HelloHaltMapW
import Spike.Lib.HelloWorkerRW1
import Spike.Lib.HelloCtxRdU
import Spike.Lib.A64HelloHabCtlRdI
import Spike.Lib.A64HelloCtr2
import Spike.Lib.A64HelloHq0
import Spike.Lib.A64HelloWeRoot
import Spike.Lib.A64HelloLandM1U
import Spike.Lib.HelloRootCP
import Spike.Lib.HelloRootDHF
import Spike.Lib.HelloMarksL

namespace Spike.Lib.A64.HelloPh.RootInv

variable {asm : String}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakePreTi Spike.Lib.Inv2Core Spike.Lib.WakeInst
open Spike.Lib.WakeT1 (srcPo)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1Store (ZStoreOk)
open Spike.Lib.HelloSegTCS (SegTCS)
open Spike.Lib.A64.Flow.Worker (NNH AbW)
open Spike.Lib.HelloO (ODataH IH R1OH)
open Spike.Lib.HelloOLift (XH)
open Spike.Lib.HelloPreA (ClonePreH)
open Spike.Lib.HelloSpawnR (PreRH HWiH)
open Spike.Lib.HelloMainHRD (MainSegH)
open Spike.Lib.WakeSpawn (SpawnPrem)
open Spike.Lib.WakePrivR (VPriv)
open Spike.Lib.HelloAssembly (HelloRowsW)
open Spike.Lib.HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH hcwH hemH μH)
open Spike.Lib.HelloAssemblyIM (G0H)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.A64.WakeWf (DtW)
open Spike.Lib.A64.HelloPh.StartH0B (StartPH W0H)
open Spike.Lib.A64.HelloPh.RootH0 (msBotH)
open Spike.Lib.HelloRootO (helloDR oPremH_R)
open Spike.Lib.A64.Rt (RuntimeLayout)
open SccCode (helloProg)
open Spike.Lib.A64.Flow.Worker.Hello.Pass (helloPassT)
open Spike.Lib.HelloAssemblyR (hello_obligations_R)
open Spike.Lib.HelloSrcOPrem (hello_hookOK hello_srcSafeS)
open Spike.Lib.HelloOAb (AbH AcH hti0_H)
open Spike.Lib.HelloAssemblyRP (hello_obligations_RP)
open Spike.Lib.HelloPostAb (TwH AbFacts)
open Spike.Lib.HelloAssemblyRV (hello_obligations_RV)
open Spike.Lib.HelloAssemblyI (PI ZI XI hsegI hsegXI hWiH_I r1c_facts)
open Spike.Lib.HelloOkW (lBH)
open Spike.Lib.Handover (childAfter)
open Spike.Lib.WakeW1 (mainTidW)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.A64.Flow.Worker.Hello.SegR (ChildPrem)
open Spike.Lib.A64.HelloPh.Land (CtxRH)
open Spike.Lib.A64.HelloPh.C0S (c0S)


variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The root's immediate table. -/
local notation "IH0" => Spike.Lib.A64.HelloPh.C0S.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => LH hp (IH0)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.WakeOD.arW hp (IH0)

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
/-- The start level's contexts (`LandRU.CtxRdU`: rodata's add with `r1Of` unmapped; `hello_obligations_RSU`'s). -/
local notation "CR" => Spike.Lib.A64.HelloPh.LandRU.CtxRdU (asm := asm) hp i0 E (fun _ => True) ls

set_option hygiene false in
/-- main's frame. -/
local notation "FM" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- `h2`'s memory side. -/
local notation "MS2" => Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hp (IH0) E ls

set_option hygiene false in
/-- The third level at `DtW`. -/
local notation "W2R" => Spike.Lib.A64.HelloPh.W2I (Ly) (AW) DtW (CR) (LB) (ls0T ls)

set_option hygiene false in
/-- `h2`'s invariant. -/
local notation "inv2R" => Spike.Lib.HelloH2Inv.inv2H (W2R) (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (MS2)
  (Ly) (AX) (Ly).endPc (LB) (ls0T ls)

set_option hygiene false in
/-- Level 1's fragment (`RootL1F.I0H`: level 0's and level 1's slots empty, `inv0H`/`inv1G` depend on `IH D`). -/
local notation "I0R" => Spike.Lib.A64.HelloPh.RootL1F.I0H (AW) (LB) (ls0T ls) (inv2R)

set_option hygiene false in
/-- Level 1's memory sides at `I0R` (`MainWcL1A`'s `MS1` at `rd := True`). -/
local notation "MS1R" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
    (Spike.Lib.HelloGOf2H.gWH hp (IH0) (Spike.Lib.WakeHG.cTW hp (IH0)))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AW) (I0R)
    (A64ConsumerA.upd (LB) l b) (A64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- Level 1's invariant before `U r1Of` (`inv1G` over `MS1R`, `MainWcL1A.h1_level1P`'s). -/
local notation "inv1GR" => Spike.Lib.HelloPreA.H1Gfp.inv1G
  (Spike.Lib.A64.HelloPh.Level1I.W1R (asm := asm) hp i0 E (fun _ => True) ls) (Spike.Lib.A64.HelloPh.Level1I.XR hp i0)
  (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB) (MS1R)

set_option hygiene false in
/-- The root's level 1 (`RootL1U.W1RU`). -/
local notation "W1R'" => Spike.Lib.A64.HelloPh.RootL1U.W1RU (asm := asm) hp i0 E ls (FM)

set_option hygiene false in
/-- The root's level-1 invariant (`RootL1U.inv1RU`: `inv1GR` with `r1Of` unmapped). -/
local notation "inv1R" => Spike.Lib.A64.HelloPh.RootL1U.inv1RU hp i0 (inv1GR)

set_option hygiene false in
/-- rodata's call invariant (`StartWcS.rdJH` at main's start). -/
local notation "J'R" => Spike.Lib.A64.HelloPh.StartWcS.rdJH (Ly).lab
  (Spike.Lib.A64.WakePh.MainGlue.JS (Ly) 0#64 Spike.Lib.A64.HelloPh.C0S.c0S)

set_option hygiene false in
/-- Level 0's landing fragment (`hst0_RdU`'s `IB`: level 0's slot empty). -/
local notation "IBR" => I3 (AW) (LB) (ls0T ls) (fun _ _ _ => False) (inv1R) (inv2R)

set_option hygiene false in
local notation "D" => helloDR (asm := asm) hp (IH0) E (CR) ls (FM) (W1R') (inv1R) (W2R) (inv2R)

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
local notation "R1R" => fun d s => R1OH arch (Ly).Λ (μH hp (IH0) E asm) (D) XH d s ∧ VPriv (Ly).Λ E d

set_option hygiene false in
local notation "r1R" => Spike.Lib.WakeOSide.r1W hp (IH0)

set_option hygiene false in
/-- The switch's worker fragments (`HelloWorkerDHF`; the DH := helloDRF switch). -/
local notation "PS" => Spike.Lib.HelloWorkerDHF.PF hp (IH0) (G0H hp (IH0))

set_option hygiene false in
local notation "ZS" => Spike.Lib.HelloWorkerDHF.ZF hp (IH0) (μE)

set_option hygiene false in
local notation "XS" => Spike.Lib.HelloWorkerDHF.XF hp (IH0) (μE)

set_option hygiene false in
/-- `hsegFH`'s labels at `lo` (`HelloOInit.hlab_H`). -/
local notation "HLB" => Spike.Lib.HelloOInit.hlab_H hp (IH0) hpa hhp hlo

set_option hygiene false in
/-- `hsegFH`'s marks at `μE` (`HelloAssemblyI.marksL_HE`). -/
local notation "HMU" => Spike.Lib.HelloAssemblyI.marksL_HE hp (IH0) hpa hhp hlo (H := kernel 2) (E := E)

set_option hygiene false in
local notation "hS" => Spike.Lib.HelloWorkerDHF.hsegFH hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)

set_option hygiene false in
local notation "QQ" => QH hp (IH0) (G0H hp (IH0)) (PS) (ZS) (XS) (hS) arch (R1R) E hpa helloPassT (D) (r1R)

/-! ## The root's premise inventory (`hello_root_inv`'s hypotheses)

| hypothesis | note |
|---|---|
| `hpa`, `hhp`, `hd` | carried by `RootLit.hello_root_lit` as `hparse` |
| `hlo`, `hstat`, `hnz`, `hA13`, `hp` | at `Λe` (`.text` linked at `0x210550`) |
| `hc` | DONE: `RootLit.hc_H` |
| `hB` | `B.cells`, as wake's `wake_linked` |
| `hz`, `hn` | DONE: `RootLit.hz_H` (`131072`), `hn` by `decide` |
| `hE` | `E.Ok` at the layout (`hello_correctE_clear`'s); `hE.1` the old `.clear` |
| (`msB`, `hokb`, `hg`) | DONE: derived, `RootOkb.msBH`/`hokb_H`/`hg_H` |
| (`res`, `tcb`) | DONE: derived, `CalRootI.res_I`/`tcb_I` in `RootInstW.h0V_I` |
| (`hoffTi`) | REMOVED (unprovable as stated); `HelloTi2HatO.hti_HO` instead |
| (`hobl`) | DONE: derived, `RefO.refOblH_root` (as `RefRootI.hobl_I`, `hDt := fun _ h => h`) |
| (`hst0`) | DONE: derived, `CtxRdU.hst0_RdU` at `CR := LandRU.CtxRdU` |
| `hm` | the table's `m` at rodata (`ImmsMe` at `iRdM`) |
| (`hctrD`) | DONE: replaced by `hctr2 := HelloCtr2.hctr2_H` |
| (`hWe`) | DONE: `WeRoot.hWe_rootRdH hp i0 hpa hhp hlo E ls` |
| (`hq`) | DONE: `Hq0.hq0_H hp i0 hstat hc hpin2` |
| (`hW0`) | DONE: `CtxRdU.hW0_RdU'` (`hhabctlRd`: `HabCtlRdI.habCtlRdH_rdCN`) |
| (`h1`, `hW1`) | DONE: `W1`/`inv1` pinned (`W1RU`, `inv1RU` of `inv1G` at `I0R`) |
|---|---|
| `hRdI`, `hme`, `hzI` | `ImmsMe.rdImms_iRdM`/`hmeC_iRdM`, `HabCtlA.hz_i0M` (`hzI` at `i0`) |
| (`hhabctl`) | DONE: inside `h1_level1P` (`HabCtlA.habCtlHA_jr1L`) |
| (`hM`) | DONE: `LandM1U.hLandM1U_I` + `HLandM1U.mono`/`inv1_I3` |
| (`F0`, `hF0`) | DONE: `F0` pinned to `wc_main`'s frame condition; `hF0` by construction |
| (`h0t`, `h0o`) | DONE: derived, `StartGlue.h0TakeH_of`/`h0TakeOwnH_of` (`RootH0.h0H`) |
| (`h1t`) | DONE: `Take1X.h1TakeXH_and`/`h1TakeXH_inv1G` (consumer `H1TakeXH`) |
| (`h2t`, `h2o`) | DONE: derived, `HelloH2Inv.take2_of` |
| (`hCl`) | DONE: derived, `HelloHClW.hClH_ofRI` at `D` |
| (`hG`) | DONE: derived, `RootHG.hG_H` (from `hpin2`) |
| (`pT0`) | DONE: any word; fixed to `WakeHG.cTW` |
| (`pass`) | DONE: derived, `HelloRootDHF.DHF_pass` at `passT := helloPassT` (`DHF_zhr`) |
| (`hZ`) | DONE: derived, `HelloRootDHF.DHF_hZ` (`ZF`'s `ZHR`, `Z.zStoreOk_ZHR`) |
| (`hpc`) | DONE: derived, `HelloSegEnd.hpc_ofR` at `D` (`hseg_X2`) |
| (`hnc1`) | DONE: `h1_level1P`'s clone clause (`hL1`'s third conjunct) |
| (`hX`) | DONE: derived, `HelloXOk.hX_ofR` at `D` |
| (`hCP`) | DONE: `HelloRootCP.hCP_root`, `hx3 := x3_2_of`; `hn3`, `hinit2` |
| (`hhalt1`) | DONE: derived, `HelloRootDHF.DHF_hhalt1` (`DHF_zhr`) |
| (`hmapW`) | DONE: `HelloRootDHF.DHF_hmapW` (`DHF_flag`, as `HelloMapWF.hmapW_DRF_H`) |
| (`hRW1`) | DONE: derived, `HelloRootDHF.DHF_hRW1` (`DHF_zhr`) |
| (`hab1W`) | DONE: `HelloWorkerDHF.DHF_ab` (`AbH` is `Ab (Ly).lab`) |
| (`hcl`) | DONE: derived, `HelloHcl.hcl_ofR` at `D`, `AbT := AbH` |
| (`hplW`) | DONE: `HelloWorkerDHF.DHF_hplW` |
| (`hcall`) | DONE: `HelloWorkerDHF.DHF_hcall` |

No phase-chain fact hard-wires a `.rodata`/`.data`/`.bss` address: every number of `Spike/Lib` in
`0x200000`–`0x240000` is a code pc (scan; address audit is the independent second check), so
linking `.text` at `0x210550` moves only `Λe`'s data regions.

Derived here: `hpin2` (`ChildRoot.hpin2_H`), the base (`Dt := DtW`, `RootRest.W1 := True`, unused by `h2`),
`toPrem` (`hP` from `CalRootI.h0V_I`), `h2` (`h2Stmt_root.1`), `hW2` (`hW2_I`); the fragment's nodes and take
site (`inst_of_segWA3CH` at `oPremH_R`'s premises), the levels' statements (`H0Stmt.h0Stmt_root`, `h1` with
its clone clause, `h2Stmt_root`), and from them `hCl` (`HelloHClW.hClH_ofRI`) and `hpc` (`HelloSegEnd.hpc_ofR`,
`hseg_X2`).
-/

/-- **The base's frame condition at the root** (`RootRest.F0`; wake's `wake_h1` `F0`): `wc_main`'s frame condition
over the start's `FS` at some `v`, from some caller state `m1`, `σ1`, so `hW1_rootU`'s and `hland2_boxMRU`'s `hF0`
hold by construction. -/
def F0H : MachineData → Prop := fun m => ∃ v m1 σ1, Spike.Lib.A64.Flow.HelloM.wcF
  (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0) Spike.Lib.A64.HelloPh.StartH0G.helloD
  (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) Spike.Lib.A64.HelloPh.StartH0G.helloLsw 0#64 v)
  m1 σ1 m

/-- `F0H` is not vacuous: every state of the real run under `wc_main`'s frame condition (an `At` node at it, as the
box store's state in `RootHP.boxMH_landingRH`'s `hA`) has its memory in `F0H`. -/
example {v : BitVec 64} {m1 : MachineData} {σ1 : Spike.Lib.A64.Flow.AS} {R : Region} {n : Spike.Lib.A64.Flow.ND}
    {s : State} {c : Spike.Lib.Ctl}
    (hA : Spike.Lib.A64.Flow.At (Ly).exe (Ly).endPc R (Spike.Lib.A64.Flow.HelloM.wcF
      (Spike.Lib.A64.Flow.swR v (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0) Spike.Lib.A64.HelloPh.StartH0G.helloD
      (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) Spike.Lib.A64.HelloPh.StartH0G.helloLsw 0#64 v)
      m1 σ1) n s c) :
    F0H hp i0 s.st.1 := by
  obtain ⟨-, -, -, -, _, -, hF, -⟩ := hA
  exact ⟨v, m1, σ1, hF⟩

/-- **hello's obligations at the root, every remaining premise named** (see the module doc and the table). -/
theorem hello_root_inv {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {ls : Lsize}
    /- the loader's parses (the trust boundary) -/
    (hpa : textProgram asm = .ok o.prog) (hhp : textProgram asm = .ok helloProg)
    (hd : dataSections asm = some o.secs)
    /- instance facts (as `HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hc : Spike.Lib.A64.Rt.CtrZ o) (hnz : Spike.Lib.WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- row: 5j-start (`hello_correctE_clear`'s `E.Ok`). The entry is admissible at the layout. -/
    (hE : E.Ok (Ly).Λ)
    /- row: 5j-hsub1 (closed): A13's data part; the second stack in the pool is `StartPlaceLy.hsub1_W`. -/
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ o.prog o.secs = true)
    /- loader: the pinned region's `.zero` (`ChildRoot.hpin2_H`; at the certificate `CertFacts.pinZ_helloCert`) -/
    {nZ : Nat} (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some nZ)
    (hn3 : 176 ≤ nZ)
    /- row: imms-m (the table's `m` at rodata's `newBuf`; `ImmsMe` at `iRdM`). `HrdRoot.hrd_RdH`'s, rodata's
    placement's (`HabCtlRdI.placedS_rdCN`). -/
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    /- row: imms (the root table's immediates; at the certificate's table `ImmsMe.rdImms_iRdM`, `ImmsMe.hmeC_iRdM`,
    `HabCtlA.hz_i0M`). `MainWcL1A.h1_level1P`'s `hI`, `himm`, `hz` (`hz` at the table `i0`). -/
    (hRdI : Spike.Lib.A64.HelloPh.RdPlS.RdImms (Ly).Λ)
    (hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.WakeLoadT.tcb0 (Ly).Λ))
    (hzI : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    /- layout: the second limit word starts at `0` (`HelloRootCP.hCP_root`'s; as wake's root `hinit2`) -/
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.HelloGOf2H.lim2AH (Ly), 8⟩ = 0)
    /- row: switch-hI (`ImmsMe.kid_root`, `wcall_root`). No immediate at the child's and the worker call's
    controls (`HelloWorkerDHF.hsegFH`'s `hI`). -/
    (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (Ly).Λ) :
    WakeObligationsR arch (Ly).Λ B asm (QQ) E
      (fun t tr => TiPre (AbH hp (IH0)) (AcH hp (IH0)) t tr ∧ TwH (Ly).Λ E (AbH hp (IH0)) t tr) helloSrc := by
  have hn : 168 ≤ nZ := by omega
  have hpin2 := Spike.Lib.A64.HelloPh.ChildRoot.hpin2_H hp (IH0) hz hn
  have hWe := Spike.Lib.A64.HelloPh.WeRoot.hWe_rootRdH hp i0 hpa hhp hlo E ls
  -- the base's frame condition (`F0H`; `hF0` by construction)
  let F0 : MachineData → Prop := F0H hp i0
  have hF0 : ∀ v m1 σ1 m, Spike.Lib.A64.Flow.HelloM.wcF (Spike.Lib.A64.Flow.swR v
      (-Spike.Lib.A64.HelloPh.StartH0G.helloLsw) 0) Spike.Lib.A64.HelloPh.StartH0G.helloD
      (Spike.Lib.A64.WakePh.MainGlue.FS (Ly) (Spike.Lib.A64.Rt.rS0 (Ly)) Spike.Lib.A64.HelloPh.StartH0G.helloLsw
        0#64 v) m1 σ1 m → F0 m :=
    fun v m1 σ1 _ h => ⟨v, m1, σ1, h⟩
  -- root-wire-5: the refusal path, level 0's take facts, the worker's halt and release facts
  have hobl : ∀ l b n l' b' n', Fresh2H (AW) (LB) l b n l' b' n' →
      Spike.Lib.A64.HelloPh.RefH.RefOblH (Ly) F0
        (Spike.Lib.A64.HelloPh.RootHP.GJ1RH (Ly) (A64ConsumerA.upd (LB) l b) l) l' b' (Spike.Lib.HelloHMid.slWsH l) n'
        (fun s c fs => W2R l b n l' b' n' s c fs ∧
          Spike.Lib.A64.HelloPh.X2I (Ly) (LB) (ls0T ls) l b n l' b' n' s c fs)
        (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (Spike.Lib.A64.HelloPh.lbl2H (LB) l b l' b')
        (MS2 l b n l' b' n') :=
    fun l b n l' b' n' hf => Spike.Lib.A64.HelloPh.RefO.refOblH_root
      (Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp) (Spike.Lib.A64.HelloPh.RootPlug.hlo_H hp i0 hlo)
      (Spike.Lib.A64.HelloPh.RootPlug.hΛ_H hp i0) (Spike.Lib.A64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo)
      (Spike.Lib.A64.HelloPh.RootPlug.hsite_H hp i0 hpa hhp hlo) hf.2.2.1 (Spike.Lib.A64.HelloPh.Box.hmt_H hp i0 hf.1)
      (fun _ h => h) (Spike.Lib.A64.HelloPh.RootPlug.hK2_H (asm := asm) hp (IH0) E ls l b n l' b' n' hf)
      (Spike.Lib.A64.HelloPh.RefO.refExH (asm := asm) (Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp)
        (Spike.Lib.A64.HelloPh.RootPlug.hlo_H hp i0 hlo) (Spike.Lib.A64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo)
        (Spike.Lib.A64.HelloPh.RootPlug.hΛ_H hp i0)
        (by rw [Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp]; exact hhp) _ _ _ _ _ _ _)
  have h0t : Spike.Lib.HelloPreA.H0TakeH (Ly) (AX) (D).inv0 :=
    Spike.Lib.A64.HelloPh.StartGlue.h0TakeH_of
      (Spike.Lib.A64.HelloPh.RootH0.h0H (asm := asm) hp (IH0) E _ _ _ _ _ _ _)
  have h0o : Spike.Lib.HelloPreA.H0TakeOwnH (Ly) (AX) (D).inv0 :=
    Spike.Lib.A64.HelloPh.StartGlue.h0TakeOwnH_of
      (Spike.Lib.A64.HelloPh.RootH0.h0H (asm := asm) hp (IH0) E _ _ _ _ _ _ _)
  -- the worker side's rows at the switch's instance (`HelloWorkerDHF`, `HelloRootDHF`)
  have hhalt1 := Spike.Lib.HelloRootDHF.DHF_hhalt1 hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)
  have hRW1 := Spike.Lib.HelloRootDHF.DHF_hRW1 hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)
  have hmapW := Spike.Lib.HelloRootDHF.DHF_hmapW hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)
  have hab1W := Spike.Lib.HelloWorkerDHF.DHF_ab hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)
  have hplW := Spike.Lib.HelloWorkerDHF.DHF_hplW hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)
  have hcall := Spike.Lib.HelloWorkerDHF.DHF_hcall hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU)
  let R : Spike.Lib.A64.HelloPh.RootPlug.RootRest (Ly) (LB) (AW)
      (Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := asm) hp (IH0) E) :=
    { W1 := fun _ _ _ => True, Dt := DtW, Ctx := CR, ls := ls, frM := FM, F0 := F0,
      msB := Spike.Lib.A64.HelloPh.RootOkb.msBH (asm := asm) hp i0 E ls,
      hokb := Spike.Lib.A64.HelloPh.RootOkb.hokb_H (asm := asm) hp i0 E ls hc,
      hg := Spike.Lib.A64.HelloPh.RootOkb.hg_H (asm := asm) hp i0 E ls }
  let Bs := R.toBase hp i0 E hpa hhp hlo hA13 hc
  let P := Bs.toPrem hp i0 E hA13 hpin2 hstat
  have h2S := Spike.Lib.A64.HelloPh.H2Root.h2Stmt_root hp i0 P (ls0 := ls0T ls)
    (Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_X2 Bs hA13 hpin2 hstat)
    (Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_G Bs hA13 hpin2 hstat)
    (Spike.Lib.A64.HelloPh.HelloRootBase.toPrem_Wc Bs hA13 hpin2 hstat) hobl
  have hμ : (μE) = Spike.Lib.A64.PhRec.μ (Ly) := by
    have hr := Scc.Sem.A64.resolve_of_parsed (Scc.Sem.A64.kernel 2) E (Ly).Λ (prog := (Ly).prog) hpa
    unfold Scc.Sem.Target.marks Spike.Lib.A64.PhRec.μ
    congr 1
    · funext k; exact hr _
    · funext k; exact hr _
  -- level 1 at `I0R` (`MainWcL1A.h1_level1P`, the box's landing `RootHP.hland2_boxMRU`), with `r1Of` unmapped
  -- (`RootL1U.h1StmtHF_U`), lifted to `IH D` (`RootL1F.h1_bridge`)
  have hL1 := Spike.Lib.A64.HelloPh.RootL1U.h1StmtHF_U hp i0 hA13 (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ h => Spike.Lib.A64.HelloPh.RootL1U.rdLand_U hp i0 h)
    (Spike.Lib.A64.HelloPh.MainWcL1A.h1_level1P hp i0 E (fun _ => True) (I0R) ls hpa hhp hlo hstat hc hA13 hpin2
      hRdI hme hzI
      (fun _ _ _ hl hb => Spike.Lib.A64.HelloPh.RootHP.hland2_boxMRU hp i0 E (fun _ => True) ls h2S hl hb hF0))
  -- level 1's take fact at its use (`Take1X.H1TakeXH`: `XR`'s `X0WH` at `inv1G`'s states)
  have h1t' : Spike.Lib.HelloPreA.Take1X.H1TakeXH (Ly) (AX) (inv1R) := Spike.Lib.HelloPreA.Take1X.h1TakeXH_and
    (Spike.Lib.HelloPreA.Take1X.h1TakeXH_inv1G fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h.1)
  -- level 2's take facts (`HelloH2Inv.take2_of`)
  have h2t : Spike.Lib.HelloPreA.H2TakeH (Ly) (AX) (inv2R) :=
    fun _ _ _ _ _ _ _ _ _ h hpc => (Spike.Lib.HelloH2Inv.take2_of h hpc).1
  have h2o : Spike.Lib.HelloPreA.H2TakeOwnH (Ly) (AX) (inv2R) :=
    fun _ _ _ _ _ _ _ _ _ h hpc => (Spike.Lib.HelloH2Inv.take2_of h hpc).2
  -- level 0 at `CR := CtxRdU` (`HelloCtxRdU`): the start segment and `hW0`, from `hL1` and rodata's abort
  -- controls (`HabCtlRdI.habCtlRdH_rdCN`, placed by `placedS_rdCN`)
  have hhabctlRd : ∀ σC, Spike.Lib.A64.HelloPh.HabCtlRd.HabCtlRdH
      (msBotH (asm := asm) hp (IH0) E (fun _ => True) ls (inv1R) (inv2R) [FM]) (Ly).lab helloSrc (Ly).Λ (LB) (AW) [FM]
      (Spike.Lib.A64.Flow.Hello1.mRdJ0 (J'R) σC) := fun _ =>
    Spike.Lib.A64.HelloPh.HabCtlRdI.habCtlRdH_rdCN (fun _ _ h => h.2.1) rfl rfl rfl
      fun s => .inl (Spike.Lib.A64.HelloPh.HabCtlRdI.placedS_rdCN hm hme s)
  have hst0 := Spike.Lib.A64.HelloPh.CtxRdU.hst0_RdU hp i0 E (fun _ => True) ls hE hpa hhp hlo hstat hA13
    (Spike.Lib.HelloCtr2.hctr2_H hp (IH0) hA13) hc hm hWe
    (Spike.Lib.A64.HelloPh.Hq0.hq0_H hp i0 hstat hc hpin2) hL1 hhabctlRd
  have hW0 := Spike.Lib.A64.HelloPh.CtxRdU.hW0_RdU' (W1' := W1R') (W2 := W2R) hp i0 E ls hpa hhp hlo hc hA13 hm hL1
    hhabctlRd
  have h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      SegInvS ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (A64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (A64ConsumerA.upd (D).L0 l b)
          (A64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n) :=
    fun l b n hl hb => Spike.Lib.A64.HelloPh.RootL1F.h1_bridge Spike.Lib.A64.HelloPh.RootL1F.I0H_le (hL1 l b n hl hb).1
  have hM : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      Spike.Lib.A64.HelloPh.LandR1U.HLandM1U (asm := asm) hp i0 E (fun _ => True) ls l b n
        (IH (D) (A64ConsumerA.upd (D).L0 l b) (A64ConsumerA.updN (D).ls0 l n)) := fun l b n hl hb =>
    Spike.Lib.A64.HelloPh.LandM1U.HLandM1U.mono
      (Spike.Lib.A64.HelloPh.LandM1U.hLandM1U_I hp i0 E (fun _ => True) (I0R) ls hpa hhp hlo hc hA13 hzI
        (fun _ _ _ hl hb => Spike.Lib.A64.HelloPh.RootHP.hland2_boxMRU hp i0 E (fun _ => True) ls h2S hl hb hF0)
        l b n hl hb)
      (Spike.Lib.A64.HelloPh.LandM1U.inv1_I3 (inv0 := (D).inv0) (inv1 := (D).inv1) (inv2 := (D).inv2) hl hb)
  have hW1 := Spike.Lib.A64.HelloPh.RootL1U.hW1_rootU hp i0 E (CR) ls (FM) (inv1GR) (W2R) (inv2R) hpa hhp hc hM h2S
    hF0
  -- the fragment's nodes and take site (`inst_of_segWA3CH` at `oPremH_R`'s, as `hello_obligations_R` builds it)
  have hO := oPremH_R hp (IH0) hpa hhp hd hlo hstat hpin2
    (Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp (IH0) hA13) hc hnz arch hB hE.1 hst0
    (fun l b n l' b' n' hl hb hl' hb' => (h2S l b n l' b' n' hl hb hl' hb').1) h1 hW0 hW1
    (fun l b n l' b' n' s c fs _ _ _ _ h => hμ ▸ Spike.Lib.A64.HelloPh.hW2_I l b n l' b' n' s c fs h)
    h0t h0o h1t' h2t h2o (hello_hookOK arch) (hello_srcSafeS arch _) (hti0_H hp (IH0) hpa hd hhp hlo E)
  obtain ⟨hN, hT, -⟩ := Spike.Lib.A64ConsumerA.inst_of_segWA3CH hO.h2 hO.h1 hO.h0 hO.ha hO.hW0 hO.hW1 hO.hW2
  -- the levels' statements: level 0 (`h0Stmt_root`), level 1 (`h1` and `hL1`'s clone clause), level 2 (`h2S`)
  have h0S := Spike.Lib.A64.HelloPh.H0Stmt.h0Stmt_root hp (IH0) E (fun _ => True) (CR) ls ls (FM) (inv1R) (inv2R) hst0
  have h1S : Spike.Lib.HelloPreA.H1StmtHF (D).W1 (TakeCKS (D).a (D).Cl) (D).ar (D).L0
      (fun l b n => msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (A64ConsumerA.upd (D).L0 l b)
        (A64ConsumerA.updN (D).ls0 l n)) (Ly) (fun _ _ _ _ _ => False) (D).inv1 [] :=
    fun l b n hl hb => ⟨h1 l b n hl hb, fun _ _ h => h.elim, (hL1 l b n hl hb).2.2⟩
  have hsub1 := Spike.Lib.A64.WakePh.StartPlaceLy.hsub1_W hp (IH0) hA13
  -- `hCl` (`hClH_ofRI`) and `hpc` (`hpc_ofR`, `hseg` by `hseg_X2`) inline, at the expected types
  refine Spike.Lib.HelloAssemblyRS.hello_obligations_RSU hp i0 hpa hhp hd hlo hI hstat hpin2 hc hnz hB hE.1 hA13 hst0
    (fun l b n l' b' n' hl hb hl' hb' => (h2S l b n l' b' n' hl hb hl' hb').1) h1 hW0 hW1
    (fun l b n l' b' n' s c fs _ _ _ _ h => hμ ▸ Spike.Lib.A64.HelloPh.hW2_I l b n l' b' n' s c fs h)
    h0t h0o h1t' h2t h2o
    (Spike.Lib.HelloHClW.hClH_ofRI (Dd := D) (L := Ly) (fun _ _ h => h.1) hN hT (fun _ h => h.1) h0S h1S h2S rfl rfl
      (Spike.Lib.WakeHClW.hbd_W hp (IH0) hsub1) rfl)
    (Spike.Lib.A64.HelloPh.RootHG.hG_H hp (IH0) hpin2)
    (Spike.Lib.WakeHG.cTW hp (IH0)) (Spike.Lib.HelloRootDHF.DHF_pass hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLB) (HMU))
    (Spike.Lib.HelloRootDHF.DHF_hZ hp (IH0))
    (Spike.Lib.HelloSegEnd.hpc_ofR (Dd := D) (L := Ly) (Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp) hN hT
      (fun _ h => h.1) h0S h1S rfl Spike.Lib.HelloSegEndX2.hseg_X2)
    (Spike.Lib.HelloXOk.hX_ofR (Dd := D) (L := Ly) (Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp) hN hT
      (fun _ h => h.1) h0S h1S rfl)
    (Spike.Lib.HelloRootCP.hCP_root hp (IH0) hpa hhp hA13 hz hn3 hinit2 (fun _ _ h => h.1) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) rfl hN hT (fun _ h => h.1) h0S h1S rfl
      fun _ _ _ _ _ _ _ _ _ h hpc => Spike.Lib.HelloH2Inv.x3_2_of h hpc)
    hhalt1 hmapW hRW1 hab1W
    (Spike.Lib.HelloHcl.hcl_ofR (Dd := D) (L := Ly) (Spike.Lib.A64.HelloPh.RootPlug.hp_H hp i0 hpa hhp)
      (Spike.Lib.A64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo) (fun _ _ h => h.1) hN hT (fun _ h => h.1) h0S h1S rfl)
    hplW hcall

end Spike.Lib.A64.HelloPh.RootInv

/-- info: 'Spike.Lib.A64.HelloPh.RootInv.hello_root_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootInv.hello_root_inv

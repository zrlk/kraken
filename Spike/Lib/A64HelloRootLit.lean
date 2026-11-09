/-
**hello's root at its listing** (AArch64): `RootInv.hello_root_inv` at the cert-free
literal `SccCode.helloAsm` (`Spike/Lib/A64HelloCode.lean`; `Spike/Test/HelloCodeChk.lean` checks it against the
certificate), its output `oH` (`helloProg`, `helloSecs`, `helloNeed`) and placement configuration `pcfgH`,
generic in the layout `Λ0` and the immediates `i0`.

- `pcfgH`, `oH`: the placement configuration (the certificate's `placeCfg`: the canonical one, `helloNeed`'s
  budget and entries) and the output. `PlaceW` reads neither the block table nor the main tail's shape, so `oH`
  carries none (`blocks := []`).
- `hz_H`, `hc_H`: the pinned region's `.zero` (`163840` bytes) and the counter's zeroed item, by `decide +kernel`
  on `helloSecs` (the twins of `CertFacts.pinZ_helloCert`/`ctrZ_helloCert`, without the certificate).
- `hello_root_lit`: `hello_root_inv` at `asm := helloAsm`, `o := oH`, `pcfg := pcfgH`. Discharged here: `hz`/`hn`
  (`hz_H`, `decide`), `hc` (`hc_H`); `hpa`/`hhp`/`hd` are the one parse premise `hparse` (the trust boundary,
  `#guard parsesTo` in `A64HelloCode`; the kernel does not reduce the parser). Every other premise is
  `hello_root_inv`'s, with its table.

**The layout.** The layout facts `hp`, `hlo`, `hstat`, `hnz`,
`hA13` are decidable only at a concrete `Λ0`, and `hlo` (`Λ0.code.lo = 0x210550`, the base of hello's phase
chain, `A64HelloPh.lo`) only at a linked executable's layout: the static link `helloΛ` has its code at
`0x400000` (`hlo_helloΛ_false` in `Spike/Test/A64HelloRootLitSmoke.lean`). They are decided at the checked-in
executable's layout `Λe`: `Scc/Test/a64link.sh` links hello with `.text` pinned at `0x210550`,
`Spike/Test/HelloLinkedA64Elf.lean` reads `Λe` off the file (path, SHA-256, `Λe.code.lo` guard), one
`decide +kernel` module per placement component decides the facts there (`Spike/Test/HelloLinkedA64*.lean`), as
at wake, and `Spike/Test/HelloLinkedA64Root.lean` instantiates the root at `Λe` (`hello_linkedA`).
-/
import Spike.Lib.A64HelloWeRoot
import Spike.Lib.A64HelloCode
import Spike.Lib.A64HelloRootInv
import Spike.Lib.HelloRootDHF
import Spike.Lib.A64HelloImmsKid

namespace Spike.Lib.A64.HelloPh.RootLit

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
open SccCode (helloProg helloAsm)
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


open Spike.Lib.A64.HelloPh.RootInv (hello_root_inv)
open Scc.Cert.Link.A64 (parsesTo parsed_of_parsesTo)

/-- **hello's placement configuration**: the canonical one with `helloNeed`'s budget and thread entries (the
certificate's `placeCfg`, guarded in `HelloCodeChk`). -/
def pcfgH : Scc.Cert.PlaceOK.Config :=
  { Scc.Cert.PlaceOK.Config.canonical with needBudget := 12288, entries := ["scc_rt_main", "scc_rt_thr_worker"] }

/-- **hello's output** as `PlaceW` reads it: the listing's program and sections and the stack need table; no
block table (`PlaceW` drops A3/A5/A7/A9, the readers of `blocks`, `tail` and `ir`). -/
def oH : Scc.Cert.PlaceOK.A64.Out :=
  { prog := helloProg, secs := SccCode.helloSecs,
    place := { blocks := [], need := SccCode.helloNeed, tail := .setup } }

/-- **The pinned region's `.zero`** after `scc_rt_pinned` has `163840` bytes (`ChildRoot.hpin2_H`'s `hz`). -/
theorem hz_H :
    Scc.Cert.PlaceOK.zeroAfter (oH.secs.bss ++ oH.secs.data) Scc.Cert.Link.pinnedSym = some 163840 := by
  decide +kernel

private theorem lookup_mem {β : Type} : ∀ {l : List (String × β)} {k : String} {b : β},
    l.lookup k = some b → (k, b) ∈ l
  | [], _, _, h => by simp at h
  | (k', b') :: l, k, b, h => by
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h; subst h; simp
    · have hne : (k == k') = false := by simpa using hk
      simp [List.lookup, hne] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **The counter's zeroed item** (`Rt.CtrZ`, `HelloRootBase.har_W`'s premise): `scc_rt_heap_use` labels an
all-zero item of 8 bytes in `helloSecs` (`CertFacts.ctrZ_helloCert`'s proof). -/
theorem hc_H : Spike.Lib.A64.Rt.CtrZ oH := by
  cases h : (Scc.Cert.Link.symItems (oH.secs.bss ++ oH.secs.data)).lookup Scc.Cert.PlaceOK.heapUseSym with
  | none => exact absurd h (by decide +kernel)
  | some its =>
    refine ⟨its, lookup_mem h, ?_, ?_⟩
    · have : ((Scc.Cert.Link.symItems (oH.secs.bss ++ oH.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map Scc.Cert.Link.allZero = some true := by decide +kernel
      rw [h] at this; simpa using this
    · have : ((Scc.Cert.Link.symItems (oH.secs.bss ++ oH.secs.data)).lookup
        Scc.Cert.PlaceOK.heapUseSym).map (fun its => decide (8 ≤ Scc.Cert.Link.itemLen its)) = some true := by
        decide +kernel
      rw [h] at this; simpa using this

variable {Λ0 : Scc.Sem.Layout} (hp : PlaceW pcfgH Λ0 oH) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The listing's parse, from `hparse`. -/
local notation "hpaH" => (parsed_of_parsesTo hparse).1

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
local notation "CR" => Spike.Lib.A64.HelloPh.LandRU.CtxRdU (asm := helloAsm) hp i0 E (fun _ => True) ls

set_option hygiene false in
/-- main's frame. -/
local notation "FM" => Spike.Lib.HelloRdCf.frH c0S.env

set_option hygiene false in
/-- `h2`'s memory side. -/
local notation "MS2" => Spike.Lib.A64.HelloPh.H2Rt.ms2H (asm := helloAsm) hp (IH0) E ls

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
  msOfA (Ly).Λ ((target (kernel 2) E).marks helloAsm (Ly).Λ) (fun _ => True)
    (Spike.Lib.HelloGOf2H.gWH hp (IH0) (Spike.Lib.WakeHG.cTW hp (IH0)))
    (fun s _ => Spike.Lib.A64.HelloPh.ownGH (Ly) (Spike.Lib.A64.Rt.Reserve.ntA (Ly).lab) s) (AW) (I0R)
    (A64ConsumerA.upd (LB) l b) (A64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
/-- Level 1's invariant before `U r1Of` (`inv1G` over `MS1R`, `MainWcL1A.h1_level1P`'s). -/
local notation "inv1GR" => Spike.Lib.HelloPreA.H1Gfp.inv1G
  (Spike.Lib.A64.HelloPh.Level1I.W1R (asm := helloAsm) hp i0 E (fun _ => True) ls)
  (Spike.Lib.A64.HelloPh.Level1I.XR hp i0)
  (TakeCKS (AX) (Spike.Lib.A64.HelloPh.ClH (Ly))) (LB) (MS1R)

set_option hygiene false in
/-- The root's level 1 (`RootL1U.W1RU`). -/
local notation "W1R'" => Spike.Lib.A64.HelloPh.RootL1U.W1RU (asm := helloAsm) hp i0 E ls (FM)

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
local notation "D" => helloDR (asm := helloAsm) hp (IH0) E (CR) ls (FM) (W1R') (inv1R) (W2R) (inv2R)

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks helloAsm (Ly).Λ

set_option hygiene false in
local notation "R1R" => fun d s => R1OH arch (Ly).Λ (μH hp (IH0) E helloAsm) (D) XH d s ∧ VPriv (Ly).Λ E d

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
local notation "hS" => Spike.Lib.HelloWorkerDHF.hsegFH hp (IH0) (G0H hp (IH0)) hI (hpaH) (hpaH)
  (Spike.Lib.HelloOInit.hlab_H hp (IH0) (hpaH) (hpaH) hlo)
  (Spike.Lib.HelloAssemblyI.marksL_HE hp (IH0) (hpaH) (hpaH) hlo (H := kernel 2) (E := E))

set_option hygiene false in
local notation "QQ" => QH hp (IH0) (G0H hp (IH0)) (PS) (ZS) (XS) (hS) arch (R1R) E (hpaH) helloPassT (D) (r1R)

/-- **The root's relation** (`QQ`, `hello_root_lit`'s): `HelloAssemblyI.QH` at the root's table `i0`, the
switch's worker side (`HelloWorkerDHF`'s `PF`, `ZF`, `XF`, `hsegFH`, from the listing's parse `hparse`, `hlo` and
the immediates' `ImmsKid` `hI`), the pre-spawn relation `R1R`, `passT := helloPassT`, the root's data `helloDR`
and the handed stack `r1W`. Named so the final statement (`RootFinal.hello_root_final`) reads without unfolding. -/
noncomputable abbrev QRoot {arch : WeakMem.Arch} {E : Entry} {ls : Lsize}
    (hparse : parsesTo helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (Ly).Λ) : WakeRel :=
  QQ

theorem hello_root_lit {arch : WeakMem.Arch} {B : Budget} {E : Entry}
    {ls : Lsize}
    /- the loader's parse of the listing (the trust boundary; `#guard`-checked in `A64HelloCode`) -/
    (hparse : parsesTo helloAsm SccCode.helloProg SccCode.helloSecs = true)
    /- instance facts (as `HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hnz : Spike.Lib.WakeOInit.NtZ Λ0 oH = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- row: 5j-start (`hello_correctE_clear`'s `E.Ok`). The entry is admissible at the layout. -/
    (hE : E.Ok (Ly).Λ)
    /- row: 5j-hsub1 (closed): A13's data part; the second stack in the pool is `StartPlaceLy.hsub1_W`. -/
    (hA13 : Scc.Cert.Spawn.A64.a13data (Ly).Λ oH.prog oH.secs = true)
    /- row: imms-m (the table's `m` at rodata's `newBuf`; `ImmsMe` at `iRdM`). `HrdRoot.hrd_RdH`'s, rodata's
    placement's (`HabCtlRdI.placedS_rdCN`). -/
    (hm : (Ly).Λ.imms Spike.Lib.HelloRodataSrc.eB "m" 0 = some 2)
    /- row: imms (the root table's immediates; at the certificate's table `ImmsMe.rdImms_iRdM`, `ImmsMe.hmeC_iRdM`,
    `HabCtlA.hz_i0M`). `MainWcL1A.h1_level1P`'s `hI`, `himm`, `hz` (`hz` at the table `i0`). -/
    (hRdI : Spike.Lib.A64.HelloPh.RdPlS.RdImms (Ly).Λ)
    (hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.WakeLoadT.tcb0 (Ly).Λ))
    (hzI : i0 Spike.Lib.HelloMainPreSrc.newTerm "z" 0 = some 0)
    /- layout: the second limit word starts at `0` (`HelloRootCP.hCP_root`'s; as wake's root `hinit2`) -/
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (Ly).Λ oH.prog oH.secs).initVal ⟨Spike.Lib.HelloGOf2H.lim2AH (Ly), 8⟩ = 0)
    /- row: switch-hI (`ImmsMe.kid_root`, `wcall_root`). No immediate at the child's and the worker call's
    controls (`HelloWorkerDHF.hsegFH`'s `hI`). -/
    (hI : Spike.Lib.A64.HelloPh.XHFSeg.ImmsKid (Ly).Λ) :
    WakeObligationsR arch (Ly).Λ B helloAsm (QQ) E
      (fun t tr => TiPre (AbH hp (IH0)) (AcH hp (IH0)) t tr ∧ TwH (Ly).Λ E (AbH hp (IH0)) t tr) helloSrc :=
  hello_root_inv (asm := helloAsm) (o := oH) (nZ := 163840) (arch := arch) (B := B) (E := E)
    (ls := ls) hp i0 (hpaH) (hpaH) (parsed_of_parsesTo hparse).2 hlo hstat
    hc_H hnz hB hE hA13 hz_H (by decide)
    hm hRdI hme hzI hinit2 hI

set_option hygiene false in
/-- The placed layout at the certificate's immediates table `i0 := ImmsMe.i0M Λ0` (`ImmsMe.iRdM Λ0`). -/
local notation "LyM" => LH hp (Spike.Lib.A64.HelloPh.C0S.immsH Λ0 (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0))

/-- **`hello_root_lit` at the certificate's immediates table** `i0 := ImmsMe.i0M Λ0`: the table's facts `hm`,
`hRdI`, `hme`, `hzI` discharged by `WeRoot.hm_root`, `rdImms_root`, `hme_root`, `hzI_root` (rows imms-m, imms) and
the switch's `hI` by `ImmsMe.immsKid_root` (row switch-hI). The premises left are the boundary: the listing's parse
`hparse`, the layout facts `hlo`, `hstat`, `hnz`, `hA13`, `hinit2`, the budget's `hB` and the entry's `hE`. The
statement is `hello_root_lit`'s conclusion at that table (the switch's worker side `HelloWorkerDHF`'s `PF`, `ZF`,
`XF`, `hsegFH`). -/
theorem hello_root_litM {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    /- the loader's parse of the listing (the trust boundary; `#guard`-checked in `A64HelloCode`) -/
    (hparse : parsesTo helloAsm SccCode.helloProg SccCode.helloSecs = true)
    /- instance facts (as `HelloRootO.oPremH_R`) -/
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hnz : Spike.Lib.WakeOInit.NtZ Λ0 oH = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    /- row: 5j-start (`hello_correctE_clear`'s `E.Ok`). The entry is admissible at the layout. -/
    (hE : E.Ok (LyM).Λ)
    /- row: 5j-hsub1 (closed): A13's data part; the second stack in the pool is `StartPlaceLy.hsub1_W`. -/
    (hA13 : Scc.Cert.Spawn.A64.a13data (LyM).Λ oH.prog oH.secs = true)
    /- layout: the second limit word starts at `0` (`HelloRootCP.hCP_root`'s; as wake's root `hinit2`) -/
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (LyM).Λ oH.prog oH.secs).initVal
      ⟨Spike.Lib.HelloGOf2H.lim2AH (LyM), 8⟩ = 0) :
    type_of% (hello_root_lit (arch := arch) (B := B) (E := E) (ls := ls) hp (Spike.Lib.A64.HelloPh.ImmsMe.i0M Λ0)
      hparse hlo hstat hnz hB hE hA13 (Spike.Lib.A64.HelloPh.WeRoot.hm_root hp)
      (Spike.Lib.A64.HelloPh.WeRoot.rdImms_root hp) (Spike.Lib.A64.HelloPh.WeRoot.hme_root hp)
      Spike.Lib.A64.HelloPh.WeRoot.hzI_root hinit2 (Spike.Lib.A64.HelloPh.ImmsMe.immsKid_root hp)) :=
  hello_root_lit hp _ hparse hlo hstat hnz hB hE hA13 (Spike.Lib.A64.HelloPh.WeRoot.hm_root hp)
    (Spike.Lib.A64.HelloPh.WeRoot.rdImms_root hp) (Spike.Lib.A64.HelloPh.WeRoot.hme_root hp)
    Spike.Lib.A64.HelloPh.WeRoot.hzI_root hinit2 (Spike.Lib.A64.HelloPh.ImmsMe.immsKid_root hp)

/-! ### The switch's instance

`hello_root_litM` at the DH := helloDRF switch's worker side (`HelloWorkerDHF`'s `PF`, `ZF`, `XF`, `hsegFH`): every
premise below the loader's trust boundary is discharged; no open rows (the switch's `hI` by `ImmsMe.immsKid_root`).
The premises are the boundary: the listing's parse `hparse`, the layout facts `hlo`, `hstat`, `hnz`, `hA13`,
`hinit2`, the budget's `hB` and the entry's `hE`. -/

example {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    (hparse : parsesTo helloAsm SccCode.helloProg SccCode.helloSecs = true)
    (hlo : Λ0.code.lo = Spike.Lib.A64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hnz : Spike.Lib.WakeOInit.NtZ Λ0 oH = true) (hB : B.cells = Scc.Cert.PlaceOK.allocCells) (hE : E.Ok (LyM).Λ)
    (hA13 : Scc.Cert.Spawn.A64.a13data (LyM).Λ oH.prog oH.secs = true)
    (hinit2 : (Spike.Lib.A64.PhRec.m0Of (LyM).Λ oH.prog oH.secs).initVal
      ⟨Spike.Lib.HelloGOf2H.lim2AH (LyM), 8⟩ = 0) :=
  hello_root_litM (arch := arch) (ls := ls) hp hparse hlo hstat hnz hB hE hA13 hinit2

end Spike.Lib.A64.HelloPh.RootLit

/-- info: 'Spike.Lib.A64.HelloPh.RootLit.hz_H' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootLit.hz_H

/-- info: 'Spike.Lib.A64.HelloPh.RootLit.hc_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootLit.hc_H

/-- info: 'Spike.Lib.A64.HelloPh.RootLit.hello_root_lit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootLit.hello_root_lit

/-- info: 'Spike.Lib.A64.HelloPh.RootLit.hello_root_litM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.RootLit.hello_root_litM

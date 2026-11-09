/-
**hello.w's root obligations on x86-64 at main's owned words with the self words** (the twin of
`Spike/Lib/A64HelloRootInv.lean`): `WakeObligationsR` at hello's root data `helloDRg ownGHXW`, from the three
levels' statements and `X64HelloAssemblyRS.hello_obligations_RSg`.

- `rootInvX_of`: the obligations, given `CstOkH` at the refusal path's four blocks (`hcblk`) and along its threads
  abort path (`hcst`). Level 0 is `RootL0X.hst0_rootX`/`hW0_rootX`. Level 1 is `MainWcL1A.h1_level1PX` (wrapped by
  `RootL1U.h1StmtHF_Ug`), with `LandM1U.hLandM1U_IX` and `RootL1U.hW1_rootUg`. Level 2 is `H2Root.h2Stmt_rootX` at
  `HelloRootBase.toPremX` of `RootPlugX.toBaseX`, its refusal obligations by `RefO.refOblH_rootX`. The clone,
  child, worker and pc facts are `hClH_ofRI`, `hCP_root`, `hpc_ofR`, `hX_ofR`, `hexe_of`, `hcl_ofR` and the root's
  `DHF_*`.
- `rootInvX_ofB`: `rootInvX_of` with `hcst` discharged by `RefO.refCstH`.
- `hello_root_inv`: the obligations outright, `rootInvX_ofB` with `hcblk` discharged by `RefO.refCstBlkH`.

## Unlike AArch64

- main owns its own and the worker's TCB words up to the clone (`ownGHXW`), so every level is stated at those owned
  words: level 0's context is `CtxU (CtxRdHg … ownGHXW)`, level 2's side `H2RtX.ms2HX`, the root premises
  `HelloRootPremX` (start level `WSHX`), and the refusal path needs `CstOkH` (AArch64: `ownGH` throughout).
- The program is a parsed `Scc.Sem.X64.Asm` with hello's cells; the layout `PlaceWX`'s.
-/
import Spike.Lib.X64HelloAssemblyRV
import Spike.Lib.X64HelloAssemblyRS
import Spike.Lib.X64HelloRootInstW
import Spike.Lib.X64HelloRootPlug
import Spike.Lib.X64HelloRootPlugX
import Spike.Lib.X64HelloH2RtX
import Spike.Lib.X64HelloRootL0X
import Spike.Lib.X64HelloMainWcL1AX
import Spike.Lib.X64HelloH2Root
import Spike.Lib.X64HelloChildRoot
import Spike.Lib.X64HelloRootHG
import Spike.Lib.X64HelloZR
import Spike.Lib.X64HelloSegEnd
import Spike.Lib.X64HelloSegEndX2
import Spike.Lib.X64HelloHClWR
import Spike.Lib.X64HelloH0Stmt
import Spike.Lib.X64WakeHClW
import Spike.Lib.X64HelloRootOkb
import Spike.Lib.X64HelloRootL1F
import Spike.Lib.X64HelloRootL1U
import Spike.Lib.X64HelloMainWcL1A
import Spike.Lib.X64HelloXOk
import Spike.Lib.X64HelloHcl
import Spike.Lib.X64HelloRefRoot
import Spike.Lib.X64HelloRefAbX
import Spike.Lib.X64HelloRefBlkX
import Spike.Lib.X64HelloHaltMapW
import Spike.Lib.X64HelloHabCtlRdI
import Spike.Lib.X64HelloCtr2
import Spike.Lib.X64HelloHq0
import Spike.Lib.X64HelloWeRoot
import Spike.Lib.X64HelloLandM1U
import Spike.Lib.X64HelloRootCP
import Spike.Lib.X64HelloRootDHF
import Spike.Lib.X64HelloMarksL
import Spike.Lib.X64HelloRootHPL
import Spike.Lib.X64HelloLandRU
import Spike.Lib.X64HelloRootH0
import Spike.Lib.X64HelloWorkerDHF
import Spike.Lib.X64HelloHrdRoot
import Spike.Lib.X64HelloRootUL
import Spike.Lib.X64WakeHClC
import Spike.Lib.X64HelloHfp

namespace Spike.Lib.X64.HelloPh.RootInv

variable {asm : Scc.Sem.X64.Asm}

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Inv2Core Spike.Lib.X64WakeInst
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.HeapLand (AllocLand)
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloO (ODataH IH R1OH)
open Spike.Lib.X64HelloOLift (XH)
open Spike.Lib.X64WakePrivR (VPriv)
open Spike.Lib.X64HelloAssemblyI (LH ιH endH SRH GH PaH DH MH QH hcwH hemH μH)
open Spike.Lib.X64HelloAssemblyIM (G0H)
open Spike.Lib.X64WakeLoadT (L0T ls0T)
open Spike.Lib.X64.WakeWf (DtW)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64HelloSrcOPrem (hello_hookOK hello_srcSafeS)
open Spike.Lib.X64HelloOAb (AbH AcH hti0_H)
open Spike.Lib.X64HelloPostAb (TwH AbFacts)
open Spike.Lib.X64.HelloPh.C0S (c0S)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
local notation "IH0" => Spike.Lib.X64.HelloImms.immsH Λ0 i0

set_option hygiene false in
local notation "Ly" => LH hp (IH0)

set_option hygiene false in
local notation "LB" => L0T (Ly).Λ

set_option hygiene false in
local notation "AW" => Spike.Lib.X64.WakeOD.arW hp (IH0)

set_option hygiene false in
local notation "AX" => (Ly).lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL

set_option hygiene false in
local notation "OW" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
local notation "CR" => Spike.Lib.X64.HelloPh.RootUL.CtxU hp i0
  (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := asm) hp i0 E (fun _ => True) ls (OW))

set_option hygiene false in
local notation "FM" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "MS2" => Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hp (IH0) E ls

set_option hygiene false in
local notation "W2R" => Spike.Lib.X64.HelloPh.W2Ig (OW) (Ly) (AW) DtW (CR) (LB) (ls0T ls)

set_option hygiene false in
local notation "inv2R" => Spike.Lib.X64HelloH2Inv.inv2H (W2R) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (MS2)
  (Ly) (AX) (Ly).endPc (LB) (ls0T ls)

set_option hygiene false in
local notation "I0R" => Spike.Lib.X64.HelloPh.RootL1F.I0H (AW) (LB) (ls0T ls) (inv2R)

set_option hygiene false in
local notation "MS1R" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  msOfA (Ly).Λ ((target (kernel 2) E).marks asm (Ly).Λ) (fun _ => True)
    (Spike.Lib.X64HelloGOf2H.gWH hp (IH0) (Spike.Lib.X64WakeHG.cTW hp (IH0)))
    (fun s _ => (OW) s) (AW) (I0R)
    (X64ConsumerA.upd (LB) l b) (X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
local notation "inv1GR" => Spike.Lib.X64HelloPreA.H1Gfp.inv1G
  (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := asm) hp i0 E (fun _ => True) ls (OW))
  (Spike.Lib.X64.HelloPh.Level1I.XR hp i0)
  (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (LB) (MS1R)

set_option hygiene false in
local notation "W1R'" => Spike.Lib.X64.HelloPh.RootL1U.W1RUg (asm := asm) hp i0 (OW) E ls (FM)

set_option hygiene false in
local notation "inv1R" => Spike.Lib.X64.HelloPh.RootL1U.inv1RU hp i0 (inv1GR)

set_option hygiene false in
local notation "D" => Spike.Lib.X64HelloRootO.helloDRg (asm := asm) hp (IH0) (OW) E (CR) ls (FM) (W1R') (inv1R)
  (W2R) (inv2R)

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks asm (Ly).Λ

set_option hygiene false in
local notation "F0R" => fun m => ∃ v m1 σ1, Spike.Lib.X64.Flow.HelloM.wcF
  (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v) Spike.Lib.X64.HelloPh.StartH0G.helloD
  (Spike.Lib.X64.WakePh.MainGlue.FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) Spike.Lib.X64.HelloPh.StartH0G.helloLsw 0#64 v)
  m1 σ1 m

set_option hygiene false in
local notation "TOPR" => Spike.Lib.X64.WakePh.MainGlue.topS (Ly) 0#64

set_option hygiene false in
local notation "J'R" => Spike.Lib.X64.HelloPh.StartWcS.rdJH (Ly).lab
  (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw (TOPR))
  (Spike.Lib.X64.WakePh.MainGlue.JS (Ly) 0#64 c0S)

set_option hygiene false in
local notation "R1R" => fun d s => Spike.Lib.X64HelloO.R1OH arch (Ly).Λ (μH hp (IH0) E asm) (D) XH d s ∧
  VPriv (Ly).Λ E d

set_option hygiene false in
local notation "r1R" => Spike.Lib.X64WakeOSide.r1W hp (IH0)

set_option hygiene false in
local notation "PS" => Spike.Lib.X64HelloWorkerDHF.PF hp (IH0) (G0H hp (IH0))

set_option hygiene false in
local notation "ZS" => Spike.Lib.X64HelloWorkerDHF.ZF hp (IH0) (μE)

set_option hygiene false in
local notation "XS" => Spike.Lib.X64HelloWorkerDHF.XF hp (IH0) (μE)

set_option hygiene false in
local notation "HLBn" => Spike.Lib.X64HelloOInit.hlab_H hp (IH0) hpa hhp hlo

set_option hygiene false in
local notation "HMUn" => Spike.Lib.X64HelloAssemblyI.marksL_HE hp (IH0) hpa hhp hlo (H := kernel 2) (E := E)

set_option hygiene false in
local notation "hS" => Spike.Lib.X64HelloWorkerDHF.hsegFH hp (IH0) (G0H hp (IH0)) hI hpa hhp (HLBn) (HMUn)

set_option hygiene false in
local notation "QQ" => QH hp (IH0) (G0H hp (IH0)) (PS) (ZS) (XS) (hS) arch (R1R) E hpa
  Spike.Lib.X64.Flow.Worker.Hello.Pass.helloPassT (D) (r1R)

/-- **hello's root obligations at `ownGHXW`** (see the module doc), given `CstOkH` at the refusal path's blocks
(`hcblk`) and along its threads abort path (`hcst`). -/
theorem rootInvX_of {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hE : E.Ok (Ly).Λ)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {nZ : Nat} (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some nZ)
    (hn3 : 208 ≤ nZ)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hRdI : Spike.Lib.X64.HelloPh.RdPlS.RdImms (Ly).Λ)
    (hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ))
    (hzI : i0 Spike.Lib.X64HelloMainPreSrc.newTerm "z" 0 = some 0)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.X64HelloGOf2H.lim2AH (Ly), 8⟩ = 0)
    (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (Ly).Λ)
    (hcblk : ∀ (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word),
      Spike.Lib.X64.HelloPh.RefO.BlkH (Ly) lbl l ws
        (fun s _ => Spike.Lib.X64.HelloPh.CstOkH (Spike.Lib.X64.PhRec.μ (Ly)) (Ly)
          (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (fun _ _ => False))
    (hcst : ∀ (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word),
      Spike.Lib.X64.HelloPh.RefO.TOblH (Ly) lbl l ws
        (fun _ s _ => Spike.Lib.X64.HelloPh.CstOkH (Spike.Lib.X64.PhRec.μ (Ly)) (Ly)
          (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (fun _ _ => False)) :
    WakeObligationsR arch (Ly).Λ B asm (QQ) E
      (fun t tr => TiPre (AbH hp (IH0)) (AcH hp (IH0)) t tr ∧ TwH (Ly).Λ E (AbH hp (IH0)) t tr) helloSrc := by
  have hn : 200 ≤ nZ := by omega
  have hpin2 := Spike.Lib.X64.HelloPh.ChildRoot.hpin2_H hp (IH0) hz hn
  have hF0 : ∀ v m1 σ1 m, Spike.Lib.X64.Flow.HelloM.wcF
      (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw v)
      Spike.Lib.X64.HelloPh.StartH0G.helloD
      (Spike.Lib.X64.WakePh.MainGlue.FS (Ly) (Spike.Lib.X64.Rt.rS0 (Ly)) Spike.Lib.X64.HelloPh.StartH0G.helloLsw
        0#64 v) m1 σ1 m → (F0R) m :=
    fun v m1 σ1 _ h => ⟨v, m1, σ1, h⟩
  have hpL := Spike.Lib.X64.HelloPh.RootPlug.hp_H hp i0 hpa hhp
  have hloL := Spike.Lib.X64.HelloPh.RootPlug.hlo_H hp i0 hlo
  have hΛL := Spike.Lib.X64.HelloPh.RootPlug.hΛ_H hp i0
  have hlabL := Spike.Lib.X64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo
  have hW := Spike.Lib.X64.HelloPh.tcbWH_notG_W hp (IH0) hA13
  have hobl : ∀ l b n l' b' n', Spike.Lib.X64.HelloPh.Fresh2H (AW) (LB) l b n l' b' n' →
      Spike.Lib.X64.HelloPh.RefH.RefOblH (Ly) (F0R)
        (Spike.Lib.X64.HelloPh.RootHP.GJ1RH (Ly) (X64ConsumerA.upd (LB) l b) l) l' b'
        (Spike.Lib.X64HelloHMid.slWsH l) n'
        (fun s c fs => W2R l b n l' b' n' s c fs ∧
          Spike.Lib.X64.HelloPh.X2I (Ly) (LB) (ls0T ls) l b n l' b' n' s c fs)
        (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (Spike.Lib.X64.HelloPh.lbl2H (LB) l b l' b')
        (MS2 l b n l' b' n') :=
    fun l b n l' b' n' hf => Spike.Lib.X64.HelloPh.RefO.refOblH_rootX hpL hloL hΛL hlabL hf.2.2.1
      (Spike.Lib.X64.HelloPh.Box.hmt_H hp i0 hf.1) (fun _ h => h)
      (Spike.Lib.X64.HelloPh.RootPlugX.hK2_HX hp i0 asm E ls l b n l' b' n' hf)
      (Spike.Lib.X64.HelloPh.RefO.refExH hpL hloL hlabL hΛL (by rw [hpL]; exact hhp) _ _ _ _ _ _ _)
      (fun ws => hcblk _ _ ws) (fun ws => hcst _ _ ws)
  let R : Spike.Lib.X64.HelloPh.RootPlug.RootRest (Ly) (LB) (AW) (Spike.Lib.X64.HelloPh.H2RtX.ms2HX asm hp (IH0) E) :=
    { Dt := DtW, Ctx := CR, ls := ls, frM := FM, F0 := F0R,
      msB := Spike.Lib.X64.HelloPh.RootOkb.msBH (asm := asm) hp i0 E ls,
      hokb := Spike.Lib.X64.HelloPh.RootPlugX.hokb_HX hp i0 E ls hc,
      hg := Spike.Lib.X64.HelloPh.RootPlugX.hg_HX hp i0 E ls }
  let Bs := Spike.Lib.X64.HelloPh.RootPlugX.toBaseX hp i0 asm E R hpa hhp hlo hA13 hc
  let P := Bs.toPremX hp i0 E hA13 hpin2 hstat
  have h2S := Spike.Lib.X64.HelloPh.H2Root.h2Stmt_rootX hp i0 P (ls0 := ls0T ls) hW
    (Spike.Lib.X64.HelloPh.HelloRootBase.toPremX_X2 Bs hA13 hpin2 hstat)
    (Spike.Lib.X64.HelloPh.HelloRootBase.toPremX_G Bs hA13 hpin2 hstat)
    (Spike.Lib.X64.HelloPh.HelloRootBase.toPremX_Wc Bs hA13 hpin2 hstat) hobl
  have hX1 : ∀ l b n, (LB) l = none → AllocLand (AW).heap (AW).cells b n →
      Spike.Lib.X64.HelloPh.LandR1U.HLand2U (asm := asm) hp i0 E (fun _ => True) ls l b n
        ((MS1R) l b n []).xa :=
    fun _ _ _ hl hb => Spike.Lib.X64.HelloPh.RootHP.hland2_boxMRUg (own := OW) hp i0 E (fun _ => True) ls h2S hl hb
      hF0
  have hL1 := Spike.Lib.X64.HelloPh.RootL1U.h1StmtHF_Ug hp i0 (fun _ _ _ _ => rfl)
    (fun _ _ _ _ _ h => Spike.Lib.X64.HelloPh.RootL1U.rdLand_Ug hp i0 h)
    (Spike.Lib.X64.HelloPh.MainWcL1A.h1_level1PX hp i0 E (fun _ => True) (I0R) ls hpa hhp hlo hstat hc hA13 hpin2
      hRdI hme hzI hX1)
  have h1 : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      Spike.Lib.X64SegWPub.SegInvSP ((D).W1 l b n) (TakeCKS (D).a (D).Cl) helloSrc (X64ConsumerA.upd (D).L0 l b)
        (msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (X64ConsumerA.upd (D).L0 l b)
          (X64ConsumerA.updN (D).ls0 l n)) ((D).inv1 l b n) :=
    fun l b n hl hb => Spike.Lib.X64SegWPub.SegInvSP.mono_xa (hL1 l b n hl hb).1
      (fun fs => Spike.Lib.X64GfpS.msOfA_with_xa fs)
      fun fs _ _ _ _ _ hx => Spike.Lib.X64GfpS.msOfA_xa_mono Spike.Lib.X64.HelloPh.RootL1F.I0H_le fs hx
  have hM : ∀ l b n, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      Spike.Lib.X64.HelloPh.LandR1U.HLandM1U (asm := asm) hp i0 E (fun _ => True) ls l b n
        (IH (D) (X64ConsumerA.upd (D).L0 l b) (X64ConsumerA.updN (D).ls0 l n)) := fun l b n hl hb =>
    Spike.Lib.X64.HelloPh.LandM1U.HLandM1U.mono
      (Spike.Lib.X64.HelloPh.LandM1U.hLandM1U_IX hp i0 E (fun _ => True) (I0R) ls hpa hhp hlo hc hA13 hzI hX1
        l b n hl hb)
      (Spike.Lib.X64.HelloPh.LandM1U.inv1_I3 (inv0 := (D).inv0) (inv1 := (D).inv1) (inv2 := (D).inv2) hl hb)
  have hW1 := Spike.Lib.X64.HelloPh.RootL1U.hW1_rootUg (own := OW) hp i0 E (CR) ls (FM) (inv1GR) (W2R) (inv2R)
    hpa hhp hc (fun _ _ h => List.mem_append_left _ (List.mem_append_left _ h)) hM h2S hF0
  have hhabctlRd : ∀ σC, Spike.Lib.X64.HelloPh.HabCtlRd.HabCtlRdH
      (Spike.Lib.X64.HelloPh.RootH0.msBotHg (asm := asm) hp (IH0) E (fun _ => True) ls (inv1R) (inv2R) (OW) [FM])
      (Ly).lab helloSrc (Ly).Λ (LB)
      (Spike.Lib.X64.Flow.Hello1.mR
        (Spike.Lib.X64.WakePh.MainGlue.RS Spike.Lib.X64.HelloPh.StartH0G.helloLsw (TOPR))) (AW) [FM]
      (Spike.Lib.X64.Flow.Hello1.mRdJ0 (J'R) σC) := fun _ =>
    Spike.Lib.X64.HelloPh.HabCtlRdI.habCtlRdH_rdCN (fun _ _ h => h.2.1) rfl rfl rfl
      fun s => .inl (Spike.Lib.X64.HelloPh.HabCtlRdI.placedS_rdCN hm hme s)
  have hst0 := Spike.Lib.X64.HelloPh.RootL0X.hst0_rootX hp i0 E ls (inv1R) (inv2R) hE hpa hhp hlo hstat hA13 hc hm
    hpin2 hL1 hhabctlRd
  have hW0 := Spike.Lib.X64.HelloPh.RootL0X.hW0_rootX (W1 := W1R') (W2 := W2R) hp i0 E ls (inv1R) (inv2R) hpa hhp
    hlo hc hA13 hm hL1 hhabctlRd
  have hμ : (μE) = Spike.Lib.X64.PhRec.μ (Ly) :=
    Spike.Lib.X64.Flow.Worker.Wake.AbOffW.marks_target (Ly) (by rw [hpL]; exact hhp)
  have h0t : Spike.Lib.X64HelloPreA.H0TakeH (Ly) (AX) (D).inv0 :=
    Spike.Lib.X64.HelloPh.StartGlue.h0TakeH_of
      (Spike.Lib.X64.HelloPh.RootH0.h0Hg (asm := asm) hp (IH0) E (fun _ => True) (CR) ls ls (FM) (inv1R) (inv2R)
        (OW))
  have h0o : Spike.Lib.X64HelloPreA.H0TakeOwnH (Ly) (AX) (D).inv0 :=
    Spike.Lib.X64.HelloPh.StartGlue.h0TakeOwnH_of
      (Spike.Lib.X64.HelloPh.RootH0.h0Hg (asm := asm) hp (IH0) E (fun _ => True) (CR) ls ls (FM) (inv1R) (inv2R)
        (OW))
  have h1t' : Spike.Lib.X64HelloPreA.Take1X.H1TakeXH (Ly) (AX) (inv1R) := Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_and
    (Spike.Lib.X64HelloPreA.Take1X.h1TakeXH_inv1G fun _ _ _ _ _ _ h => h) (fun _ _ _ _ _ _ h => h.1)
  have h2t : Spike.Lib.X64HelloPreA.H2TakeH (Ly) (AX) (inv2R) :=
    fun _ _ _ _ _ _ _ _ _ h hpc => (Spike.Lib.X64HelloH2Inv.take2_of h hpc).1
  have h2o : Spike.Lib.X64HelloPreA.H2TakeOwnH (Ly) (AX) (inv2R) :=
    fun _ _ _ _ _ _ _ _ _ h hpc => (Spike.Lib.X64HelloH2Inv.take2_of h hpc).2
  have h2seg := fun l b n l' b' n' hl hb hl' hb' => (h2S l b n l' b' n' hl hb hl' hb').1
  have hW2 : ∀ l b n l' b' n' s c fs, (D).L0 l = none → AllocLand (D).ar.heap (D).ar.cells b n →
      X64ConsumerA.upd (D).L0 l b l' = none → AllocLand (D).ar.heap (D).ar.cells b' n' →
      (D).W2 l b n l' b' n' s c fs →
      SFactsACH (Ly).Λ μE helloSrc (D).rd (D).G (D).own (D).ar (IH (D))
        (X64ConsumerA.upd (X64ConsumerA.upd (D).L0 l b) l' b')
        (X64ConsumerA.updN (X64ConsumerA.updN (D).ls0 l n) l' n') s c fs (D).Dt (AbH hp (IH0)) (D).Cl
        (AcH hp (IH0)) :=
    fun l b n l' b' n' s c fs _ _ _ _ h => hμ ▸ Spike.Lib.X64.HelloPh.hW2_I l b n l' b' n' s c fs h
  have hsub1 := Spike.Lib.X64.WakePh.StartPlaceLy.hsub1_W hp (IH0) hA13
  have hO := Spike.Lib.X64HelloRootO.oPremH_RX hp (IH0) hpa hhp hd hoffs hlo hstat hpin2 hsub1 hc hnz arch hB hE.1
    hst0 h2seg h1 hW0 hW1 hW2 h0t h0o h1t' h2t h2o (hello_hookOK arch) (hello_srcSafeS arch _)
    (hti0_H hp (IH0) hpa hd hhp hlo E)
  obtain ⟨hN, hT, -⟩ := Spike.Lib.X64ConsumerA.inst_of_segWA3CH
    (fun l b n l' b' n' hl hb hl' hb' => (hO.h2 l b n l' b' n' hl hb hl' hb').toP) hO.h1 hO.h0.toP hO.ha
    hO.hW0 hO.hW1 hO.hW2
  have h0S := Spike.Lib.X64.HelloPh.H0Stmt.h0Stmt_rootg (own := OW) hp (IH0) E (fun _ => True) (CR) ls ls (FM)
    (inv1R) (inv2R) hst0
  have h1S : Spike.Lib.X64HelloPreA.H1StmtHF (D).W1 (TakeCKS (D).a (D).Cl) (D).ar (D).L0
      (fun l b n => msOfA (Ly).Λ μE (D).rd (D).G (D).own (D).ar (IH (D)) (X64ConsumerA.upd (D).L0 l b)
        (X64ConsumerA.updN (D).ls0 l n)) (Ly) (fun _ _ _ _ _ => False) (D).inv1 [] :=
    fun l b n hl hb => ⟨h1 l b n hl hb, fun _ _ h => h.elim, (hL1 l b n hl hb).2.2⟩
  have hinv2 : (D).inv2 = Spike.Lib.X64HelloH2Inv.inv2H (W2R) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (MS2)
      (Ly) (AX) (Ly).endPc (D).L0 (ls0T ls) := rfl
  have hCl' : ∀ s, Spike.Lib.X64.HelloPh.ClH (Ly) s → pcOf s = Spike.Lib.X64HelloPreA.clonePcH (Ly) :=
    fun _ h => Spike.Lib.X64.HelloPh.ClH.pc h
  have hbd : (Ly).stacksA.toNat + 32768 < 2 ^ 64 := by
    have := Spike.Lib.X64WakeHClC.hbd_W hp (IH0)
    rwa [(Ly).lab_stacks] at this
  have HLB := Spike.Lib.X64HelloOInit.hlab_H hp (IH0) hpa hhp hlo
  have HMU := Spike.Lib.X64HelloAssemblyI.marksL_HE hp (IH0) hpa hhp hlo (H := kernel 2) (E := E)
  have hR1 : ∀ d s, (R1R) d s → Spike.Lib.X64HelloO.R1OH arch (Ly).Λ (μH hp (IH0) E asm) (D) XH d s :=
    fun _ _ h => h.1
  exact @Spike.Lib.X64HelloAssemblyRS.hello_obligations_RSg asm pcfg o Λ0 hp (IH0) (OW) arch B E
    Spike.Lib.X64.Flow.Worker.Hello.Pass.helloPassT (AbH hp (IH0)) (CR) ls (FM) (W1R') (inv1R) (W2R) (inv2R)
    hpa hhp hd hoffs hlo hI hstat hpin2 hc hnz hB hE.1 hA13 hst0
    (Spike.Lib.X64HelloOInitX.hown0_HX hp (IH0) hpa hhp hlo (Spike.Lib.X64WakeOInit.hnt_of hp (IH0) hnz) E)
    h2seg h1 hW0 hW1 hW2 h0t h0o h1t' h2t h2o
    (Spike.Lib.X64HelloHClW.hClH_ofRI hR1 hN hT hCl' h0S h1S h2S rfl rfl hbd hinv2)
    (Spike.Lib.X64.HelloPh.RootHG.hG_H hp (IH0) hpin2) ⟨0#64, 8⟩
    (Spike.Lib.X64HelloRootDHF.DHF_pass hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)
    (Spike.Lib.X64HelloRootDHF.DHF_hZ hp (IH0) (μ := μE))
    (Spike.Lib.X64HelloWorkerDHF.DHF_hZW hp (IH0)) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) (fun _ _ => rfl)
    (Spike.Lib.X64HelloXOk.hexe_of (fun _ _ h => h.1.1) hN hT hCl' h0S h1S hinv2)
    (Spike.Lib.X64HelloSegEnd.hpc_ofR hpL hN hT hCl' h0S h1S hinv2 Spike.Lib.X64HelloSegEndX2.hseg_X2
      (Spike.Lib.X64HelloHfp.hfp_W (Dd := D) (L := Ly) hinv2))
    (Spike.Lib.X64HelloXOk.hX_ofR hpL hN hT hCl' h0S h1S hinv2)
    (Spike.Lib.X64HelloRootCP.hCP_root hp (IH0) hpa hhp hA13 hz hn3 hinit2 hR1 (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) rfl hN hT hCl' h0S h1S hinv2)
    (Spike.Lib.X64HelloRootDHF.DHF_hhalt1 hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)
    (Spike.Lib.X64HelloRootDHF.DHF_hmapW hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)
    (Spike.Lib.X64HelloRootDHF.DHF_hRW1 hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)
    (Spike.Lib.X64HelloWorkerDHF.DHF_ab hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)
    (Spike.Lib.X64HelloHcl.hcl_ofR hpL hlabL hR1 hN hT hCl' h0S h1S hinv2)
    (Spike.Lib.X64HelloWorkerDHF.DHF_hplW hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)
    (Spike.Lib.X64HelloWorkerDHF.DHF_hcall hp (IH0) (G0H hp (IH0)) hI hpa hhp HLB HMU)

/-- **hello's root obligations at `ownGHXW`, given `CstOkH` at the refusal path's blocks** (`hcblk`): `rootInvX_of`
with the abort path's `CstOkH` by `RefO.refCstH`. -/
theorem rootInvX_ofB {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hE : E.Ok (Ly).Λ)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {nZ : Nat} (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some nZ)
    (hn3 : 208 ≤ nZ)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hRdI : Spike.Lib.X64.HelloPh.RdPlS.RdImms (Ly).Λ)
    (hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ))
    (hzI : i0 Spike.Lib.X64HelloMainPreSrc.newTerm "z" 0 = some 0)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.X64HelloGOf2H.lim2AH (Ly), 8⟩ = 0)
    (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (Ly).Λ)
    (hcblk : ∀ (lbl : Lbl) (l : WeakMem.AllocLabel) (ws : List TermRun.Word),
      Spike.Lib.X64.HelloPh.RefO.BlkH (Ly) lbl l ws
        (fun s _ => Spike.Lib.X64.HelloPh.CstOkH (Spike.Lib.X64.PhRec.μ (Ly)) (Ly)
          (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab) s) (fun _ _ => False)) :
    WakeObligationsR arch (Ly).Λ B asm (QQ) E
      (fun t tr => TiPre (AbH hp (IH0)) (AcH hp (IH0)) t tr ∧ TwH (Ly).Λ E (AbH hp (IH0)) t tr) helloSrc :=
  rootInvX_of hp i0 hpa hhp hd hoffs hlo hstat hc hnz hB hE hA13 hz hn3 hm hRdI hme hzI hinit2 hI hcblk
    fun lbl l ws => Spike.Lib.X64.HelloPh.RefO.refCstH (Spike.Lib.X64.HelloPh.RootPlug.hp_H hp i0 hpa hhp)
      (Spike.Lib.X64.HelloPh.RootPlug.hlo_H hp i0 hlo) (Spike.Lib.X64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo)
      (Spike.Lib.X64.WakePh.tcbSep_W hp (IH0)) (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp (IH0) hA13)
      (Spike.Lib.X64.HelloPh.tcbWH_notG_W hp (IH0) hA13) lbl l ws

/-- **hello's root obligations at `ownGHXW`** (see the module doc): `rootInvX_ofB` with the refusal path's
blocks' `CstOkH` by `RefO.refCstBlkH`. -/
theorem hello_root_inv {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    (hpa : cellsOf asm = some o.prog) (hhp : cellsOf asm = some SccCode.helloCells)
    (hd : dataSections asm.text = some o.secs) (hoffs : asm.labelOffs = o.labelOffs)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hc : Spike.Lib.X64.Rt.CtrZ o) (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 o = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hE : E.Ok (Ly).Λ)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {nZ : Nat} (hz : Scc.Cert.PlaceOK.zeroAfter (o.secs.bss ++ o.secs.data) Scc.Cert.Link.pinnedSym = some nZ)
    (hn3 : 208 ≤ nZ)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hRdI : Spike.Lib.X64.HelloPh.RdPlS.RdImms (Ly).Λ)
    (hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ))
    (hzI : i0 Spike.Lib.X64HelloMainPreSrc.newTerm "z" 0 = some 0)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ o.prog o.secs).initVal ⟨Spike.Lib.X64HelloGOf2H.lim2AH (Ly), 8⟩ = 0)
    (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (Ly).Λ) :
    WakeObligationsR arch (Ly).Λ B asm (QQ) E
      (fun t tr => TiPre (AbH hp (IH0)) (AcH hp (IH0)) t tr ∧ TwH (Ly).Λ E (AbH hp (IH0)) t tr) helloSrc :=
  rootInvX_ofB hp i0 hpa hhp hd hoffs hlo hstat hc hnz hB hE hA13 hz hn3 hm hRdI hme hzI hinit2 hI
    fun lbl l ws => Spike.Lib.X64.HelloPh.RefO.refCstBlkH
      (Spike.Lib.X64.HelloPh.RootPlug.hlab_H hp i0 hpa hhp hlo) (Spike.Lib.X64.HelloPh.RootPlug.hp_H hp i0 hpa hhp)
      (Spike.Lib.X64.HelloPh.RootPlug.hlo_H hp i0 hlo) (Spike.Lib.X64.WakePh.tcbSep_W hp (IH0))
      (Spike.Lib.X64.WakePh.tcbM_ne_ntA_W hp (IH0) hA13) (Spike.Lib.X64.HelloPh.tcbWH_notG_W hp (IH0) hA13) lbl l ws

end Spike.Lib.X64.HelloPh.RootInv

/-- info: 'Spike.Lib.X64.HelloPh.RootInv.rootInvX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootInv.rootInvX_of

/-- info: 'Spike.Lib.X64.HelloPh.RootInv.rootInvX_ofB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootInv.rootInvX_ofB

/-- info: 'Spike.Lib.X64.HelloPh.RootInv.hello_root_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootInv.hello_root_inv

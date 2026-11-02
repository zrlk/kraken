/-
**hello's root at its listing** (the twin of `Spike/Lib/A64HelloRootLit.lean`): `RootInv.hello_root_inv` at the
literal `SccCode.helloAsm` (`Spike/Lib/X64HelloCode.lean`), its output `oH` and placement configuration `pcfgH`
(`Spike/Lib/X64HelloOut.lean`), generic in the layout `Λ0` and the immediates `i0`.

- `hz_H`, `hc_H`: the pinned region's `.zero` (`131072` bytes) and the counter's zeroed item, by `decide +kernel`
  on `helloSecs`.
- `QRoot`: the root's relation (`hello_root_inv`'s `QQ` at the listing), named so the final statement reads without
  unfolding.
- `hello_root_lit`: `hello_root_inv` at `asm := helloAsm`, `o := oH`, `pcfg := pcfgH`. Discharged here: `hz`/`hn3`
  (`hz_H`, `decide`), `hc` (`hc_H`), `hoffs` (`rfl`: `oH` carries the listing's label offsets); `hpa`/`hhp`/`hd`
  are the one parse premise `hparse` (the trust boundary, `#guard`-checked in `X64HelloCode`; the kernel does not
  reduce the parser). Every other premise is `hello_root_inv`'s, with its table.
- `hello_root_litM`: `hello_root_lit` at the root's table `i0 := X64.HelloImms.i0M Λ0`, the table's facts by
  `X64HelloWeRoot` and `ImmsKid` by `X64HelloImmsKid`. The premises left are the boundary (`hparse`, the layout
  facts `hlo`, `hstat`, `hnz`, `hA13`, `hinit2`, the budget's `hB`, the entry's `hE`).

**Where this differs from AArch64** (forced by the x86-64 shape):
- `pcfgH` and `oH` are `X64HelloOut`'s (not redefined here): `oH` carries the listing's label offsets and the
  lowering's placement data, since `PlaceWX` reads all of A1–A9 (AArch64: `blocks := []`).
- The parse is `Scc.Cert.Link.X64.parsesTo helloAsm helloCells helloSecs` (an `Asm` and code cells), so the root's
  `hoffs` is a premise, discharged by `rfl`.
- Every notation is at main's owned words with the self words (`ownGHXW`): `CtxRdHg`, `W1RUg`, `W2Ig`,
  `H2RtX.ms2HX`, `helloDRg` (AArch64: `ownGH` throughout).
- `ImmsKid` at the root's table is the pair `⟨kid_root hp, wcall_root hp⟩` (AArch64: `ImmsMe.immsKid_root`).
-/
import Spike.Lib.X64HelloWeRoot
import Spike.Lib.X64HelloCode
import Spike.Lib.X64HelloOut
import Spike.Lib.X64HelloRootInv
import Spike.Lib.X64HelloRootDHF
import Spike.Lib.X64HelloImmsKid
import Scc.Cert.LinkX64

namespace Spike.Lib.X64.HelloPh.RootLit

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
open Spike.Lib.X64HelloOAb (AbH AcH)
open Spike.Lib.X64HelloPostAb (TwH)
open Spike.Lib.X64.HelloPh.C0S (c0S)
open SccCode (helloAsm)
open Spike.Lib.X64.HelloPh.RootInv (hello_root_inv)
open Scc.Cert.Link.X64 (parsesTo parsed_of_parsesTo)

/-- **The pinned region's `.zero`** after `scc_rt_pinned` has `131072` bytes (the root's `hz`). -/
theorem hz_H :
    Scc.Cert.PlaceOK.zeroAfter (oH.secs.bss ++ oH.secs.data) Scc.Cert.Link.pinnedSym = some 131072 := by
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

/-- **The counter's zeroed item** (`Rt.CtrZ`, the root's `hc`): `scc_rt_heap_use` labels an all-zero item of 8
bytes in `helloSecs`. -/
theorem hc_H : Spike.Lib.X64.Rt.CtrZ oH := by
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

variable {Λ0 : Scc.Sem.Layout} (hp : PlaceWX pcfgH Λ0 oH) (i0 : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The listing's parse, from `hparse`. -/
local notation "hpaH" => (parsed_of_parsesTo hparse).1

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
  (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := helloAsm) hp i0 E (fun _ => True) ls (OW))

set_option hygiene false in
local notation "FM" => Spike.Lib.X64HelloRdCf.frH c0S.env

set_option hygiene false in
local notation "MS2" => Spike.Lib.X64.HelloPh.H2RtX.ms2HX helloAsm hp (IH0) E ls

set_option hygiene false in
local notation "W2R" => Spike.Lib.X64.HelloPh.W2Ig (OW) (Ly) (AW) DtW (CR) (LB) (ls0T ls)

set_option hygiene false in
local notation "inv2R" => Spike.Lib.X64HelloH2Inv.inv2H (W2R) (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (MS2)
  (Ly) (AX) (Ly).endPc (LB) (ls0T ls)

set_option hygiene false in
local notation "I0R" => Spike.Lib.X64.HelloPh.RootL1F.I0H (AW) (LB) (ls0T ls) (inv2R)

set_option hygiene false in
local notation "MS1R" => fun (l : WeakMem.AllocLabel) (b n : Nat) (fs : List TermRun.Frame) =>
  msOfA (Ly).Λ ((target (kernel 2) E).marks helloAsm (Ly).Λ) (fun _ => True)
    (Spike.Lib.X64HelloGOf2H.gWH hp (IH0) (Spike.Lib.X64WakeHG.cTW hp (IH0)))
    (fun s _ => (OW) s) (AW) (I0R)
    (X64ConsumerA.upd (LB) l b) (X64ConsumerA.updN (ls0T ls) l n) fs

set_option hygiene false in
local notation "inv1GR" => Spike.Lib.X64HelloPreA.H1Gfp.inv1G
  (Spike.Lib.X64.HelloPh.Level1I.W1Rg (asm := helloAsm) hp i0 E (fun _ => True) ls (OW))
  (Spike.Lib.X64.HelloPh.Level1I.XR hp i0)
  (TakeCKS (AX) (Spike.Lib.X64.HelloPh.ClH (Ly))) (LB) (MS1R)

set_option hygiene false in
local notation "W1R'" => Spike.Lib.X64.HelloPh.RootL1U.W1RUg (asm := helloAsm) hp i0 (OW) E ls (FM)

set_option hygiene false in
local notation "inv1R" => Spike.Lib.X64.HelloPh.RootL1U.inv1RU hp i0 (inv1GR)

set_option hygiene false in
local notation "D" => Spike.Lib.X64HelloRootO.helloDRg (asm := helloAsm) hp (IH0) (OW) E (CR) ls (FM) (W1R') (inv1R)
  (W2R) (inv2R)

set_option hygiene false in
local notation "μE" => (target (kernel 2) E).marks helloAsm (Ly).Λ

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
local notation "R1R" => fun d s => Spike.Lib.X64HelloO.R1OH arch (Ly).Λ (μH hp (IH0) E helloAsm) (D) XH d s ∧
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
local notation "HLBn" => Spike.Lib.X64HelloOInit.hlab_H hp (IH0) (hpaH) (hpaH) hlo

set_option hygiene false in
local notation "HMUn" => Spike.Lib.X64HelloAssemblyI.marksL_HE hp (IH0) (hpaH) (hpaH) hlo (H := kernel 2) (E := E)

set_option hygiene false in
local notation "hS" => Spike.Lib.X64HelloWorkerDHF.hsegFH hp (IH0) (G0H hp (IH0)) hI (hpaH) (hpaH) (HLBn) (HMUn)

set_option hygiene false in
local notation "QQ" => QH hp (IH0) (G0H hp (IH0)) (PS) (ZS) (XS) (hS) arch (R1R) E (hpaH)
  Spike.Lib.X64.Flow.Worker.Hello.Pass.helloPassT (D) (r1R)

/-- **The root's relation** (`QQ`, `hello_root_lit`'s): `HelloAssemblyI.QH` at the root's table `i0`, the worker
side `X64HelloWorkerDHF`'s `PF`, `ZF`, `XF`, `hsegFH` (from the listing's parse `hparse`, `hlo` and `ImmsKid` `hI`),
the pre-spawn relation `R1R`, `passT := helloPassT`, the root's data `helloDRg` at `ownGHXW` and the handed stack
`r1W`. -/
noncomputable abbrev QRoot {arch : WeakMem.Arch} {E : Entry} {ls : Lsize}
    (hparse : parsesTo helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (Ly).Λ) : WakeRel :=
  QQ

/-- **The root at the listing** (module doc): `hello_root_inv` at `helloAsm`, `oH`, `pcfgH`. -/
theorem hello_root_lit {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    /- the loader's parse of the listing (the trust boundary; `#guard`-checked in `X64HelloCode`) -/
    (hparse : parsesTo helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 oH = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hE : E.Ok (Ly).Λ)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ oH.prog oH.secs = true)
    (hm : (Ly).Λ.imms Spike.Lib.X64HelloRodataSrc.eB "m" 0 = some 2)
    (hRdI : Spike.Lib.X64.HelloPh.RdPlS.RdImms (Ly).Λ)
    (hme : (Ly).Λ.imms Spike.Lib.SrcCalls.setupCont "me" 0 = some (Spike.Lib.X64WakeLoadT.tcb0 (Ly).Λ))
    (hzI : i0 Spike.Lib.X64HelloMainPreSrc.newTerm "z" 0 = some 0)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (Ly).Λ oH.prog oH.secs).initVal ⟨Spike.Lib.X64HelloGOf2H.lim2AH (Ly), 8⟩ = 0)
    (hI : Spike.Lib.X64.HelloPh.XHFSeg.ImmsKid (Ly).Λ) :
    WakeObligationsR arch (Ly).Λ B helloAsm (QQ) E
      (fun t tr => TiPre (AbH hp (IH0)) (AcH hp (IH0)) t tr ∧ TwH (Ly).Λ E (AbH hp (IH0)) t tr) helloSrc :=
  hello_root_inv (asm := helloAsm) (o := oH) (nZ := 131072) (arch := arch) (B := B) (E := E)
    (ls := ls) hp i0 (hpaH) (hpaH) (parsed_of_parsesTo hparse).2 rfl hlo hstat
    hc_H hnz hB hE hA13 hz_H (by decide) hm hRdI hme hzI hinit2 hI

set_option hygiene false in
/-- The placed layout at the root's table `i0 := X64.HelloImms.i0M Λ0`. -/
local notation "LyM" => LH hp (Spike.Lib.X64.HelloImms.immsH Λ0 (Spike.Lib.X64.HelloImms.i0M Λ0))

/-- **`hello_root_lit` at the root's table** `i0 := X64.HelloImms.i0M Λ0`: `hm`, `hRdI`, `hme`, `hzI` by
`WeRoot.hm_root`, `rdImms_root`, `hme_root`, `hzI_root`, and `hI` by `⟨kid_root hp, wcall_root hp⟩`. The premises
left are the boundary (`hparse`, `hlo`, `hstat`, `hnz`, `hA13`, `hinit2`, `hB`, `hE`). -/
theorem hello_root_litM {arch : WeakMem.Arch} {B : Budget} {E : Entry} {ls : Lsize}
    (hparse : parsesTo helloAsm SccCode.helloCells SccCode.helloSecs = true)
    (hlo : Λ0.code.lo = Spike.Lib.X64.WakePh.lo) (hstat : Λ0.static = fun _ => none)
    (hnz : Spike.Lib.X64WakeOInit.NtZ Λ0 oH = true)
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells)
    (hE : E.Ok (LyM).Λ)
    (hA13 : Scc.Cert.Spawn.X64.a13data (LyM).Λ oH.prog oH.secs = true)
    (hinit2 : (Spike.Lib.X64.PhRec.m0Of (LyM).Λ oH.prog oH.secs).initVal
      ⟨Spike.Lib.X64HelloGOf2H.lim2AH (LyM), 8⟩ = 0) :
    type_of% (hello_root_lit (arch := arch) (B := B) (E := E) (ls := ls) hp (Spike.Lib.X64.HelloImms.i0M Λ0)
      hparse hlo hstat hnz hB hE hA13 (Spike.Lib.X64.HelloPh.WeRoot.hm_root hp)
      (Spike.Lib.X64.HelloPh.WeRoot.rdImms_root hp) (Spike.Lib.X64.HelloPh.WeRoot.hme_root hp)
      Spike.Lib.X64.HelloPh.WeRoot.hzI_root hinit2
      ⟨Spike.Lib.X64.HelloImms.kid_root hp, Spike.Lib.X64.HelloImms.wcall_root hp⟩) :=
  hello_root_lit hp _ hparse hlo hstat hnz hB hE hA13 (Spike.Lib.X64.HelloPh.WeRoot.hm_root hp)
    (Spike.Lib.X64.HelloPh.WeRoot.rdImms_root hp) (Spike.Lib.X64.HelloPh.WeRoot.hme_root hp)
    Spike.Lib.X64.HelloPh.WeRoot.hzI_root hinit2
    ⟨Spike.Lib.X64.HelloImms.kid_root hp, Spike.Lib.X64.HelloImms.wcall_root hp⟩

end Spike.Lib.X64.HelloPh.RootLit

/-- info: 'Spike.Lib.X64.HelloPh.RootLit.hz_H' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootLit.hz_H

/-- info: 'Spike.Lib.X64.HelloPh.RootLit.hc_H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootLit.hc_H

/-- info: 'Spike.Lib.X64.HelloPh.RootLit.hello_root_lit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootLit.hello_root_lit

/-- info: 'Spike.Lib.X64.HelloPh.RootLit.hello_root_litM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.RootLit.hello_root_litM

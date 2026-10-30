import Spike.Test.WakeLinkedA64Ctr
import Spike.Lib.A64WakeRootU
import Spike.Lib.A64WakeLand2
import Spike.Lib.A64WakeWcWfS
import Spike.Lib.A64WakeH1GOf
import Spike.Lib.A64WakeH1Rt
import Spike.Lib.A64WakeWcWfR
import Spike.Lib.A64WakeHun
import Spike.Lib.A64WakeLand4
import Spike.Lib.A64WakeRootA
import Spike.Lib.A64WakeTiA
import Spike.Lib.A64WakeRefAg
import Spike.Lib.A64WakeRefAbW
import Spike.Lib.A64WakeRefAbSt
import Spike.Lib.A64WakeRefEx
import Spike.Lib.A64WakeRefNoWr
import Spike.Lib.A64WakeRefAC
import Spike.Lib.A64WakeRefMap
import Spike.Lib.A64WakeRefBlk
import Spike.Lib.A64WakeLandU
import Spike.Lib.WakeSrc

/-!
# `wake.w` on AArch64 at `Λe`: the root `wake_rootU`'s assembly

`wake_linkedU` is `CorrectE 2` at `Le.Λ`, from the root `RootU.wake_rootU`'s proof
(`WakeRootA.wake_rootPA`, i.e. `WakeRoot.wake_rootP` with `h1` from `WakeH1A.wake_h1A`, the
callee's take; `RootOpen.hst0` by `StartH0U.hst0_ofU`) at `hp := placeW_e`,
`i := ie` (`= WakeImmsC0.immsW2 Λe SccCode.wakeImms`, the root's `IW`), `Ctx := RootUL.CtxRU`,
`F0 := Spike.Lib.A64.WakePh.RootU.wFU`, `fs0 := []`.

Discharged here:

* the layout facts `hlo`, `hstat`, `hnz`, `hpin2`, `hinit2`, `hwide`, `hA13_e`, `hctrD_e`
  (`WakeLinkedA64`, `WakeLinkedA64Ctr`), and `hc` (`WakeFinalCAO.ctrZ_cert`);
* `hF0` at `F0 := wFU`;
* `wake_rootPA`'s `hG` (`H1GA`; `wcWf`, `res`, `tcb` in `WakeH1A.hMidPA_of`): `H1GA.resA`,
  `hdrA`, `tcbA`, `tid` by `H1Rt.resA_W`, `hdrA_W`, `tcbA_W`, `tid_W`, their unmapped words
  (`hunN`, `hunP`, `hunH`, `hunT`) by `Hun.hunN_W` … `hunT_W` through `BoxPure`'s `F ⊆ wFU`;
  `H1GA.ti` by `WakeTiA.tiA_of` (`WakeTi2Hat.hti_W`; its `hFr`, `hunF` through `F ⊆ wFU`, its
  pre's `Pz r1W` carried from `Box` by `WakeHatA.hmid_boxA`); `HMidPA.wcl` by `WakeWcl.wcl_W1` (in `WakeH1A.hMidPA_of`);
* `wake_rootPA`'s `hobl` by `WakeRefStub.refObl_of`, its `RefAg`, `RefAbW`, `RefAbSt`, `RefEx`, `RefNoWr`, `RefAC`, `RefMap`, `RefBlk` by
  `refAg`, `WakeRefAbW.refAbW`, `WakeRefAbSt.refAbSt`, `WakeRefEx.refEx`, `WakeRefNoWr.refNoWr`, `refAC`,
  `refMap` (`hDt` the identity at `DtW`), `refBlk`;
* `hWp`/`hWs` by `WcWfR.hWp_W`/`hWs_W` (both guarded by the thread pointer): every base but the top
  of the first stack vacuous; the top's cases by `WcWfR.hTopP_R`/`hTopS_R`;
* `RootOpen` by `RootUL.rootOpen_U` at `Ctx := CtxRU`, its land by `RootUL.hland_RU` (its
  `hWp`/`hWs` the ones above), its start by `StartH0U.hst0_ofU` (at `CtxR`).

The source `wakeS` is about, `WakeT1.wakeSrc`, is the frontend's reading of `Scc/Test/wake.w`
(`WakeSrc.wakeSrcOk`, `#guard`ed in the imported `Spike.Lib.WakeSrc`).
The remaining premises are the loader's check `hP` and the budget `hB`.
This file states no absolute address.
-/

namespace Spike.Test.WakeLinkedA64

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open SccCertificate (asm outLit placeCfg)
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.WakePh.MainGlue (FS JS)
open Spike.Lib.A64.Flow (swR At)
open Spike.Lib.A64.Flow.Ret0 (pinA)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W bX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.WakeLoadT (L0T ls0T)
open Spike.Lib.WakeC0 (c0W)
open Spike.Lib.HeapLand (AllocLand)

set_option hygiene false in
/-- The root's context at `Λe`. -/
local notation "CR" => Spike.Lib.A64.WakePh.Land.CtxR placeW_e ie ls0

set_option hygiene false in
local notation "RS" => Spike.Lib.A64.Rt.rS0 Le

set_option hygiene false in
local notation "KL" => Spike.Lib.A64.PhRec.K Le RS

set_option hygiene false in
local notation "TPA" => UInt64.ofBitVec (pinA Le.lab + 0#64 + 8#64)

set_option hygiene false in
/-- The top of the first stack (`swF`'s base). -/
local notation "TOP" => Spike.Lib.A64.Flow.Ret0.stacksA Le.lab + 0#64 + 16384#64

set_option hygiene false in
local notation "JW" => fun σC => wJ0 (wNC Le.lab (JS Le 0#64 c0W)).J σC

set_option hygiene false in
/-- The start's fragment (`hst0_ofU`'s `WSE`) at `Ctx := CtxR`. -/
local notation "WSE" => Spike.Lib.A64.WakePh.StartWf.WS Le (Spike.Lib.A64.Rt.Reserve.ntA Le.lab)
  (WakeOD.arW placeW_e ie) wakeSrc Spike.Lib.A64.WakeWf.DtW (WakeOD.ClW placeW_e ie) (CR E) (L0T Le.Λ)
  (ls0T (ls0 E)) (frM E) (Spike.Lib.A64.WakeWf.X0W Le (WakeOSide.aW placeW_e ie E))

set_option hygiene false in
local notation "MU" => Spike.Lib.A64.WakePh.StartH0U.msU placeW_e ls0 CR E []

set_option hygiene false in
/-- The start's memory side at any fragment `I` (`msU`'s and `msBot`'s). -/
local notation "MI" I => Spike.Lib.A64ConsumerA.msOfA Le.Λ
  ((Scc.Sem.A64.target (Scc.Sem.A64.kernel 2) E).marks asm Le.Λ) (fun _ => True)
  (WakeOG.gW placeW_e ie (WakeHG.cTW placeW_e ie))
  (fun s _ => Spike.Lib.A64.WakePh.ownG Le (Spike.Lib.A64.Rt.Reserve.ntA Le.lab) s) (WakeOD.arW placeW_e ie) I
  (L0T Le.Λ) (ls0T (ls0 E)) []

/-- **Per ghost of `Box`** at `Λe`: `P` at every entry, fresh label `l` of `n` bytes at `b` and
`BoxPure` ghost `R`, `F`, `J0`, `t` (`wake_rootPA`'s `hG` binders). -/
abbrev PerG (P : Entry → WeakMem.AllocLabel → Nat → Nat → Spike.Lib.Region → (MachineData → Prop) →
    (Spike.Lib.A64.Flow.AS → Ctl → Prop) → UInt64 → Prop) : Prop :=
  ∀ E : Entry, E.Ok Le.Λ → ∀ l b n, L0T Le.Λ l = none →
    AllocLand (WakeOD.arW placeW_e ie).heap (WakeOD.arW placeW_e ie).cells b n →
    ∀ R F J0 t, WakeHMid.BoxPure Le (Spike.Lib.A64.WakePh.RootU.wFU placeW_e) n R F J0 t → P E l b n R F J0 t

set_option linter.unusedVariables false in
/-- **wake.w's AArch64 statement at `Λe` through the root `wake_rootU`**: every layout
fact decided, `RootOpen` at `CtxRU`; the named hypotheses below are what remains. -/
theorem wake_linkedU {arch : WeakMem.Arch} {B : Budget} (ls0 : Entry → Lsize) (frM : Entry → TermRun.Frame)
    /- the loader's check (the trust boundary; `#guard`-checked in `WakeLinkedA64`) -/
    (hP : Scc.Cert.Link.A64.parsesTo asm outLit.prog outLit.secs = true)
    /- the budget: the caller's choice -/
    (hB : B.cells = Scc.Cert.PlaceOK.allocCells) :
    CorrectE 2 (wakeS arch) Le.Λ B asm := by
  have hpa := (WakeSpawnRP.parsed_outLit hP).1
  have hwp := (WakeSpawnRP.parsed_outLit hP).2.1
  have hF0 : ∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS Le RS 384 0#64 v) m0 σC m → Spike.Lib.A64.WakePh.RootU.wFU placeW_e m :=
    fun v m0 σC _ h => ⟨v, m0, σC, h⟩
  refine WakeRootA.wake_rootPA ie ls0 (Spike.Lib.A64.WakePh.RootUL.CtxRU placeW_e ls0) frM placeW_e (fun _ => []) (fun _ => Spike.Lib.A64.WakePh.RootU.wFU placeW_e) hP hlo hstat
    hA13_e hpin2 hinit2 hwide hnz hB
    (fun E hE l b n hl hA R F J0 t hBx =>
      have hF : ∀ {a : BitVec 64}, (∀ v m0 σC m, wF (swR v (-384) 0) 336 (FS Le RS 384 0#64 v) m0 σC m →
          Mem.loadInt m.dmem a 8 = none) → ∀ m, F m → Mem.loadInt m.dmem a 8 = none :=
        fun h m hm => let ⟨v, m0, σC, hw⟩ := hBx.2.2.1 m hm; h v m0 σC m hw
      have hN := hF (Spike.Lib.A64.WakePh.Hun.hunN_W placeW_e ie hA13_e)
      have hP' := hF (Spike.Lib.A64.WakePh.Hun.hunP_W placeW_e ie)
      have hH := hF (Spike.Lib.A64.WakePh.Hun.hunH_W placeW_e ie hA13_e)
      ⟨hN, hP', hH, Spike.Lib.A64.WakePh.H1Rt.resA_W placeW_e ie E _ (ls0 E) hpa hwp hlo hstat hA13_e hA hN,
      Spike.Lib.A64.WakePh.H1Rt.hdrA_W placeW_e ie E _ (ls0 E) hstat hA13_e hA hH,
      Spike.Lib.A64.WakePh.H1Rt.tcbA_W placeW_e ie E _ (ls0 E) hpa hwp hlo hstat hA13_e hA
        (Spike.Lib.WakeWcW1I.bands_of_box hBx).1 hP',
      Spike.Lib.A64.WakePh.H1Rt.tid_W placeW_e ie E _ (ls0 E) hstat hA13_e hA
        (hF (Spike.Lib.A64.WakePh.Hun.hunT_W placeW_e ie hA13_e)),
      Spike.Lib.WakeTiA.tiA_of placeW_e ie E _ _ _ (ls0 E) hpa hwp hlo hstat hA13_e hpin2 WakeFinalCAO.ctrZ_cert
        hctrD_e hBx hl hA (fun m hm a ha => hF (Spike.Lib.A64.WakePh.Hun.hun_W placeW_e ie (Le.words_mapped a ha).2.2) m hm)
        (fun a ha => hF (Spike.Lib.A64.WakePh.Hun.hun_W placeW_e ie fun j hj =>
          let ⟨_, hk, e⟩ := Spike.Lib.A64.WakePh.Ti2Fld.tcb_word placeW_e ie ha
          e ▸ .inr (Spike.Lib.A64.WakePh.Ti2Fld.tcb_bytes placeW_e ie hpin2 hk j hj)))⟩)
    (fun E _ l b n hl _ => WakeRefStub.refObl_of placeW_e ie E _ _ _ (ls0 E) hpa hwp
      (WakeRefStub.refBlk placeW_e ie E _ _ (ls0 E) hpa hwp hlo hl)
      (WakeRefStub.refAC placeW_e ie hpa hwp hlo (ls0 E) n hl)
      (WakeRefStub.refAg placeW_e ie hpa hwp hlo l b) (WakeRefAbSt.refAbSt placeW_e ie hpa hwp hlo l b)
      (WakeRefNoWr.refNoWr placeW_e ie hpa hwp hlo (ls0 E) l b n) (WakeRefAbW.refAbW placeW_e ie hpa hwp hlo l b) (WakeRefStub.refMap placeW_e ie E _ _ (ls0 E) hpa hwp hlo (fun _ h => h) l b n)
      (WakeRefEx.refEx placeW_e ie hpa hwp hlo E _ (ls0 E) l b n))
    fun E hE h1 => Spike.Lib.A64.WakePh.RootUL.rootOpen_U placeW_e ls0 frM E hE hpa hwp WakeFinalCAO.ctrZ_cert hA13_e
      (Spike.Lib.A64.WakePh.StartH0U.hst0_ofU placeW_e ls0 CR frM E hE hpa hwp hlo hstat hA13_e hpin2
        hctrD_e WakeFinalCAO.ctrZ_cert h1 hF0 (Spike.Lib.A64.WakePh.WcWfR.hWp_W placeW_e E (Spike.Lib.A64.WakePh.WcWfR.hTopP_R placeW_e ls0 hpa hwp hlo WakeFinalCAO.ctrZ_cert hA13_e E _))
        (Spike.Lib.A64.WakePh.WcWfR.hWs_W placeW_e E (Spike.Lib.A64.WakePh.WcWfR.hTopS_R placeW_e ls0 hpa hwp hlo WakeFinalCAO.ctrZ_cert hA13_e E _)))
      (Spike.Lib.A64.WakePh.RootUL.hland_RU placeW_e ls0 frM E hpa hwp hlo WakeFinalCAO.ctrZ_cert hA13_e h1 hF0
        (Spike.Lib.A64.WakePh.WcWfR.hWp_W placeW_e E (Spike.Lib.A64.WakePh.WcWfR.hTopP_R placeW_e ls0 hpa hwp hlo WakeFinalCAO.ctrZ_cert hA13_e E _))
        (Spike.Lib.A64.WakePh.WcWfR.hWs_W placeW_e E (Spike.Lib.A64.WakePh.WcWfR.hTopS_R placeW_e ls0 hpa hwp hlo WakeFinalCAO.ctrZ_cert hA13_e E _))) h1 hF0

end Spike.Test.WakeLinkedA64

/-- info: 'Spike.Test.WakeLinkedA64.wake_linkedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.WakeLinkedA64.wake_linkedU

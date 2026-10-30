/-
**From `_start` to `wc_main`'s heap abort inside `W0`** (AArch64): `Rt.startEF_segWA` at the start's level `StartWf.WS` (its blocks by
`StartWf.startEW_W0S`, the frame after the switch strengthened by
`DmemPriv.WordsNone`), then, at each base of the new stack,
`WakeM.wake_main_pre_segW` (`scc_rt_main` up to `bl wc_main` by
`MainWf.mainPreWW_W0S`) and `WakeWc.wake_wc_entry_segJm` (`wc_main` from its
entry to its heap abort).

- `gS`, `FS`, `JS`: `scc_rt_main`'s entry ghosts, frame condition and
  invariant after the switch.
- `wake_start_wc_segW`: the composed segment, from `_start` at the frame
  `F ∧ P` (`P` stable, `hP`: an entry fact carried to the thread init's take
  site, where `htiW` may assume it). The premises left are the
  memory side's (the start's words, the limit word, the box's call and
  cells), the two callees' states (`htcbW`, `htiW`), the region facts and
  `wc_main`'s own states inside `W` (`hWp`, `hWs`, `hbox`, `hxa`). The
  counter's and the take's words are owned at their nodes' states only
  (`htcbO`, `htk`: `Rt.TcbOkA`, `Rt.TakeOkA`; `tcbOkA_ownG`, `takeOkA_ownG`
  give them at `ownG`).
-/
import Spike.Lib.A64WakeStartGlue
import Spike.Lib.Rt.A64WordsNoneP

namespace Spike.Lib.A64.WakePh.MainGlue

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem.A64 (pcOf abi)
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Spike.Lib.A64.Rt (RuntimeLayout mainE0 swFSL)
open Spike.Lib.A64Consumer (Lbl Lsize)
open Spike.Lib.A64.WakeWf (RunWf)
open Spike.Lib.A64.WakePh.WcW (freeN)
open Spike.Lib.A64.WakePh.StartWf (WS)
open Spike.Lib.A64.Flow (swR FStable NoMsrW)
open Spike.Lib.A64.Flow.Ret0 (pinA stacksA limA LimOk StOk TcbOk TakeOk entryN MainG)
open Spike.Lib.A64.Flow.WakeM (wR wF wJ0 wNC)
open Spike.Lib.A64.Flow.WakeWc (WcPreW WcSp0W AGB BoxW bX wX)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.DmemPriv (WordsNone WordsNoneP WordIn)
open Spike.Lib (Arena FragS SegW)

/-- `scc_rt_main`'s entry ghosts after the switch: the first stack's top
less `k0`'s offset, the first TCB, the source control. -/
abbrev gS (L : RuntimeLayout) (k0 : BitVec 64) (c0 : Ctl) : MainG :=
  ⟨stacksA L.lab + k0 + 16384#64, UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64), c0⟩

/-- The frame condition after the switch at the base `v`, of depth `Lsw`. -/
abbrev FS (L : RuntimeLayout) (rS : Scc.Sem.Range) (Lsw : Int) (k0 v : BitVec 64) : MachineData → Prop :=
  fun m => WordsNoneP L.Λ m.dmem ∧
    swFSL Lsw rS (stacksA L.lab + k0 + 16384#64) (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))) v m

/-- `scc_rt_main`'s entry invariant after the switch. -/
abbrev JS (L : RuntimeLayout) (k0 : BitVec 64) (c0 : Ctl) : Spike.Lib.A64.Flow.AS → Ctl → Prop := (mainE0 L.lab (gS L k0 c0)).J

section Gen

variable {L : RuntimeLayout} {a : BitVec 64} {rS : Scc.Sem.Range} {Tk : State → Prop} {lbl' : Lbl}
  {R : Spike.Lib.Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isaLSE2} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop} {c0 : Ctl}
  (hp : L.prog = wakeProg) (hlo : L.Λ.code.lo = lo)
  (hlab : ∀ l x, codeOf lo wakeProg l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hcl : ∀ s, Cl s → abi.atSys s = true ∧
    ∃ st tl, Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
  (hc0 : (∀ a, c0.term ≠ .ret a) ∧ RunWf p c0 []) (hpl0 : ∀ s, Spike.Lib.A64ConsumerS.PlacedSE L.Λ lbl s c0 [])
  (hX0 : ∀ s, freeN (pcOf s) = true → X0 s)

include hp hlo hlab hsite hcl hc0 hpl0 hX0

/-- **From `_start` to `wc_main`'s heap abort inside the start's level**:
the start up to the switch (`startEW_W0S`), at each base `v` of the new
stack of depth `Lsw` `scc_rt_main` up to `bl wc_main` (`mainPreWW_W0S`) and
`wc_main` into a region `D` deep (`wake_wc_entry_segJm`). -/
theorem wake_start_wc_segW (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hs : Spike.Lib.A64.WakePh.WSep L a) (hro : L.Λ.rodata.Disjoint L.Λ.stackPool) {k0 : BitVec 64}
    {Lsw D : Int} {ms : Spike.Lib.MemSide isaLSE2} {pS : Prog} {lblS : Lbl}
    (hK : ms.K = some abi) (hwf : L.Λ.WF) (hC0 : Spike.Lib.A64Consumer.CFacts L.Λ lbl' c0)
    (hF : FStable R F) {P : MachineData → Prop} (hP : FStable R P) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hRlo : R.lo ≤ -304) (hhi : 0 ≤ R.hi) (hFr : ∀ m, F m → Spike.Lib.A64.Rt.rtF L m) (hFw : ∀ m, F m → WordsNoneP L.Λ m.dmem)
    (hrS : rS = ⟨(stacksA L.lab + k0).toNat, 16384⟩) (hsub : rS.Sub L.Λ.stackPool)
    (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hSM : FStable R (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hSMi : FStable (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hSMt : FStable ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee
      Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) (Spike.Lib.A64.Flow.Ret0.StackM rS))
    (hD16 : D % 16 = 0) (hD : 240 ≤ D) (hLsw : 48 + D ≤ Lsw) (hL8 : Lsw % 8 = 0)
    (hk : k0.toNat + 16384 ≤ 536870912) (h16 : (stacksA L.lab + k0 + 16384#64).toNat % 16 = 0)
    (hok : (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).OK)
    (hsubS : ∀ k, (swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).Off k →
      ((swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).addr k).toNat % 8 = 0 ∧
      rS.contains ((swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).addr k).toNat ∧
      rS.contains (((swR (stacksA L.lab + k0 + 16384#64) (-Lsw) 0).addr k).toNat + 7))
    (hfitL : (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))).toNat + 8 ≤ 2 ^ 64)
    (houtL : ((limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))).toNat : Int) + 8 ≤
        (stacksA L.lab + k0 + 16384#64).toNat + -Lsw ∨
      ((stacksA L.lab + k0 + 16384#64).toNat : Int) + 0 ≤ (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))).toNat)
    (hRS : ∀ k, R.Off k → ∀ i < 8, R.addr k + BitVec.ofNat 64 i ∉ Scc.Sem.Kernel.addrs rS)
    (houtS : ∀ a, a % 8 = 0 → rS.contains a → rS.contains (a + 7) →
      (a : Int) + 8 ≤ R.base.toNat + R.lo ∨ (R.base.toNat : Int) + R.hi ≤ a)
    (hFt : ∀ m pm, F m → F (Spike.Lib.A64.Flow.Ret0.takeMem pm rS m))
    (hoffP : ¬ (L.Λ.stackPool.lo < (R.addr (-48)).toNat ∧
      (R.addr (-48)).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size))
    (htcbW : ∀ g, g.ra = (L.lab ".L0_scc_rt_start.sp2").toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TcbW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F ⟨g, 0#64, c0⟩ i)
    (htiW : ∀ g, g.ra = (L.lab Spike.Lib.A64.Flow.Ret0.sp3L).toBitVec → ∀ i,
      Spike.Lib.A64.Flow.Ret0.TiW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) L.exe
        L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0) F (Spike.Lib.A64.Flow.Ret0.StackM rS)
        ⟨g, pinA L.lab + 0#64 + 8#64, k0, c0⟩ i P)
    (hhdr : StOk ms F L.exe L.endPc (pinA L.lab + 0#64) (Spike.Lib.A64.Flow.Ret0.AllocTcb.hdr0 ||| 1#64 <<< 36))
    (htcbO : ∀ g, Spike.Lib.A64.Rt.TcbOkA ms F L.exe L.endPc (R.callee Spike.Lib.A64.Abort.oI.sp (-192) 0) F
      ⟨g, 0#64, c0⟩)
    (hfld : ∀ e ∈ Spike.Lib.A64.Flow.Ret0.ThreadInit.fields (pinA L.lab + 0#64 + 8#64) (stacksA L.lab + k0),
      StOk ms F L.exe L.endPc (pinA L.lab + 0#64 + 8#64 + BitVec.ofNat 64 e.1) e.2)
    (htk : ∀ g, Spike.Lib.A64.Rt.TakeOkA ms F L.exe L.endPc ((R.callee Spike.Lib.A64.Abort.oI.sp (-256) 0).callee
      Spike.Lib.A64.Flow.Ret0.ThreadInit.oI.sp (-208) 0) F ⟨g, k0, c0⟩)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))) 8 = none)
    (hmr : Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 L.Λ) false
      ⟨limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)), 8⟩ = true)
    (hlim48 : LimOk ms F L.exe L.endPc (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (stacksA L.lab + k0 + 16384#64 - (48 : Int64).toBitVec))
    (hlim128 : LimOk ms F L.exe L.endPc (limA (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (stacksA L.lab + k0 + 16384#64 - (128 : Int64).toBitVec))
    (hq0 : ∃ q : Call, q.OKB ms L.lab ∧ q.c0 = c0 ∧ q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hH : L.Λ.heap.lo ≤ ms.heap) (hHi : ms.heap + 16 * ms.cells ≤ L.Λ.heap.lo + L.Λ.heap.size)
    (hroom : ms.heap + 16 * ms.cells ≤ 2 ^ 64)
    (hctr : WordIn L.Λ.heap ms.ctr ∨ WordIn L.Λ.data ms.ctr)
    (hoff : ∀ q : Call, q.OKB ms L.lab → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hoB : ∀ q : AGB ms L.lab, q.1.c0 = c0 → ms.off 1 q.1.τ + 16 ≤ 16 * ms.units 1 q.1.τ)
    (hmp : ∀ q : AGB ms L.lab, q.1.c0 = c0 → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true)
    (hbox : ∀ q : AGB ms L.lab, q.1.c0 = c0 → BoxW lblS q.1)
    (hWp : ∀ v m0 σC, WcPreW (NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) (WS L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS))
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (wR (swR v (-Lsw) 0) D) (wF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m0 σC)
      (tpXa ms (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)))
      (wJ0 (wNC L.lab (JS L k0 c0)).J σC) (wJ0 (wNC L.lab (JS L k0 c0)).J σC))
    (hWs : ∀ v m0 σC, WcSp0W (NoMsrW (Spike.Lib.A64.Flow.WakeWc.tpG (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) (WS L a ar p Dt Cl Ctx lbl lsize frM X0)) (Spike.Lib.A64.PhRec.K L rS))
      (Spike.Lib.A64.PhRec.K L rS) L.exe L.endPc (wR (swR v (-Lsw) 0) D) (wF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m0 σC)
      (tpXa ms (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64))) (wJ0 (wNC L.lab (JS L k0 c0)).J σC))
    (hxa : ∀ v m0 σC l A s c, lblS l = none →
      Spike.Lib.A64.Flow.At L.exe L.endPc (wR (swR v (-Lsw) 0) D) (wF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m0 σC)
        (bX ms L.lab (wJ0 (wNC L.lab (JS L k0 c0)).J σC) l A) s c →
      TP (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) s → ms.xa l A 1 s c) :
    SegW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.A64.PhRec.K L rS) pS lblS ms
      (Spike.Lib.A64.Flow.At L.exe L.endPc R (fun m => F m ∧ P m) (entryN L.lab c0))
      (fun s c => ∃ v m0 σC,
        Spike.Lib.A64.Flow.At L.exe L.endPc (wR (swR v (-Lsw) 0) D) (wF (swR v (-Lsw) 0) D (FS L rS Lsw k0 v) m0 σC)
          (wX ms L.lab (wJ0 (wNC L.lab (JS L k0 c0)).J σC) .abort) s c ∧
        TP (UInt64.ofBitVec (pinA L.lab + 0#64 + 8#64)) s) := by
  have e : SccCode.wakeProg = wakeProg := by decide +kernel
  have hpW : Lays L.exe wakeProg L.pfx := hp ▸ L.lays
  have hpS : Lays L.exe SccCode.wakeProg L.pfx := e ▸ hpW
  have hendW : L.endPc = endOf L.exe wakeProg L.pfx := by show endOf L.exe L.prog L.pfx = _; rw [hp]
  have hendS : L.endPc = endOf L.exe SccCode.wakeProg L.pfx := by rw [e]; exact hendW
  have hFwS := fun v => Spike.Lib.A64.Rt.wordsNoneP_swFSL_fstable (v := v) hwf hsub hok (by omega) hL8 hsubS
    hfitL houtL hfit
  refine (Spike.Lib.A64.Rt.startEF_segWA (Fw := WordsNoneP L.Λ) hpW hendW wake_rtCodeIn0 hK hF hR hal hRlo hhi
    0#64 k0 c0 (by decide) hhdr htcbO hk hfld htk h16 hok hsubS hun hFw hFwS hRS hfit houtS hFt hP
    (StartGlue.StartEW.toF (StartWf.startEW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ hs hro hC0 hR hal hRlo hhi
      hFr rfl hrS hsub hSM hSMi hSMt hfit h16 hok hL8 hoffP htcbW htiW))).seq ?_
  refine (SegW.exists_pre (P := fun g : {v : BitVec 64 // v.toNat % 16 = 0 ∧ (swR v (-Lsw) 0).OK} =>
      Spike.Lib.A64.Flow.At L.exe L.endPc (swR g.1 (-Lsw) 0) (FS L rS Lsw k0 g.1) (mainE0 L.lab (gS L k0 c0)))
    fun g => ?_).mono_pre fun _ _ ⟨v, h1, h2, hA⟩ => ⟨⟨v, h1, h2⟩, hA⟩
  obtain ⟨v, hv, hR'⟩ := g
  refine (Spike.Lib.A64.Flow.WakeM.wake_main_pre_segW hpS hendS (by omega) hD16 (hFwS v) hR' hv
    (show -Lsw ≤ -48 - D by omega) (Int.le_refl 0)
    (MainWf.mainPreWW_W0S hp hlo hlab hsite hcl hc0 hpl0 hX0 hΛ (fun _ _ h => ⟨h.1.1, h.1.2.2⟩) hC0 hR' hv
      (show -Lsw ≤ -48 by omega) (Int.le_refl 0) (show (-Lsw) % 8 = 0 by omega) (show (0 : Int) % 8 = 0 by decide) hsub hfit
      (fun _ h => h.2.2) hmr (fun _ h => h.2.1.2))
    (MainWf.limOk_mainE0 ⟨hlim48.rt, hlim48.mp, fun _ h => h.2.1.2, hlim48.room⟩)
    fun m0 σC hok' hal' hFS' => Spike.Lib.A64.Flow.WakeWc.wake_wc_entry_segJm hK hpS hendS hFS' hok' hal'
      (show -D ≤ -240 by omega) (Int.le_refl 0) (fun _ _ h => Spike.Lib.A64.Flow.WakeHtp.mainJ_tp h)
      (hWp v m0 σC) (hWs v m0 σC) (MainWf.limOk_mainE0 ⟨hlim128.rt, hlim128.mp, fun _ h => h.2.1.2, hlim128.room⟩)
      (MainWf.ctl_mainE0 (P := fun c => ∃ q : Call, q.OKB ms L.lab ∧ q.c0 = c ∧ q.h = 256#64 ∧ q.k = 1#64 ∧
        q.u ms = 2#64) hq0)
      (StartGlue.hmemB_of_wordsNone hwf (fun _ h => h.1.wn) hH hHi hctr hoff)
      (fun q ⟨σ, h⟩ => hbox q (MainWf.ctl_mainE0 (P := fun c => c = c0) rfl σ _ h))
      (fun q ⟨σ, h⟩ => StartGlue.hcellB_of_wordsNone (P := fun q => q.c0 = c0) (fun _ h => h.1.wn) hH hHi hroom hoB hmp
        q (MainWf.ctl_mainE0 (P := fun c => c = c0) rfl σ _ h)) (hxa v m0 σC)).mono_post
    fun _ _ ⟨m0, σC, h⟩ => ⟨v, m0, σC, h⟩

end Gen

end Spike.Lib.A64.WakePh.MainGlue

/-- info: 'Spike.Lib.A64.WakePh.MainGlue.wake_start_wc_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.WakePh.MainGlue.wake_start_wc_segW

/-
**`hello1_mainS_segGW` in the switched stack** (AArch64; the H7c wiring of
the frame): `hello1_mainS_segGW_priv` at the region and frame the producers
run `scc_rt_main` in after `scc_rt_start`'s switch (`startSwitchU_segW`,
`SwUW.main`): `swR v (-L) 0` under `WordsNone Λ ∧ swFSL L rS top a v`. Its
`hF` and `hwn` are discharged: `FStable` by `wordsNone_swFSL_fstable`
(`Spike/Lib/Rt/A64SwWordsNone.lean`) from the switch's own premises and the
taken range in the stack pool, `hwn` the first conjunct. A reachable thread's
`At … swFSL …` carries the `WordsNone` conjunct by `hello1_at_wordsNone`
(`Spike/Test/A64FrameHello1.lean`).
-/
import Spike.Test.A64MainSHello1GPriv
import Spike.Lib.Rt.A64SwWordsNone

namespace Spike.Test.A64MainSHello1G

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow Spike.Lib.A64.Rt
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.A64.Flow.Ret0 (MainG WcG LimOk limA)
open Spike.Lib.A64.Alloc (Call Ea Jfull)
open Spike.Lib.A64.Flow.Hello1 (rdQ sJ0 sJ1 sJp sJp' sJh1 sJ2 sJ2' sJh2 sJ4 rNL RdPreW RdPostLW AG aR
  hello1_rodata_setupGW)
open Spike.Lib.SetupRet (SetupPostS hello1Pl)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN τ8)
open Spike.Lib.DmemPriv (WordsNone WordIn)

open Spike.Lib.A64.Rt (swFSL wordsNone_swFSL_fstable)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}

/-- The switched stack's region of depth `L` at `v`. -/
abbrev swRg (v : BitVec 64) (L : Int) : Region := swR v (-L) 0

/-- Its frame: `WordsNone` and the switch's `swFSL`. -/
abbrev swWF (Λ : Scc.Sem.Layout) (L : Int) (rS : Scc.Sem.Range) (top a v : BitVec 64) : MachineData → Prop :=
  fun m => WordsNone Λ m.dmem ∧ swFSL L rS top a v m

/-- **`hello1_mainS_segGW` in the switched stack, the frame `WordsNone ∧ swFSL`.** -/
theorem hello1_mainS_segGW_sw {Λ : Scc.Sem.Layout} {sv stop sa : BitVec 64} {sL : Int}
    {srS : Scc.Sem.Range} (hrS : srS.Sub Λ.stackPool) (hok : (swR stop (-sL) 0).OK) (hL8 : sL % 8 = 0)
    (hsub : ∀ k, (swR stop (-sL) 0).Off k → ((swR stop (-sL) 0).addr k).toNat % 8 = 0 ∧
      srS.contains ((swR stop (-sL) 0).addr k).toNat ∧ srS.contains (((swR stop (-sL) 0).addr k).toNat + 7))
    (hfit : sa.toNat + 8 ≤ 2 ^ 64)
    (hout : (sa.toNat : Int) + 8 ≤ stop.toNat + -sL ∨ (stop.toNat : Int) + 0 ≤ sa.toNat)
    (hfitS : srS.lo + srS.size ≤ 2 ^ 64)
    {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hR : (swRg sv sL).OK) (hal : (swRg sv sL).base.toNat % 16 = 0)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hlo : (swRg sv sL).lo ≤ -336) (hlo2 : (swRg sv sL).lo ≤ -80 - D2) (hhi : 0 ≤ (swRg sv sL).hi)
    (g : MainG) (x0 : BitVec 64) (hc0 : g.c0 = rdC0)
    (hlimM : LimOk ms (swWF Λ sL srS stop sa sv) exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec))
    (hlimS : LimOk ms (swWF Λ sL srS stop sa sv) exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec - (48 :
      Int64).toBitVec))
    (hlimU : LimOk ms (swWF Λ sL srS stop sa sv) exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec -
      ZU2.toBitVec))
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hwf : Λ.WF) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoffU : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hxa : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → (swWF Λ sL srS stop sa sv) m) → ∀ g' : WcG,
      g'.tp = g.tp →
      ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F'' : MachineData → Prop, (∀ m, F'' m → F' m) →
      (∀ m, F'' m → ∃ mC σC c, Abs R' ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms (swWF Λ sL srS stop
          sa sv) exe endPc g')
          (sJ1 (sJ0 (_root_.Executable.labels exe).label ms (swWF Λ sL srS stop sa sv) exe endPc g')) .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R' (-48) (-160) 0 mC
          m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R') F'' (Ea ms q.1 l b w) s c → TP g'.tp s → ms.xa l b w s c)
    (hWpre : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → (swWF Λ sL srS stop sa sv) m) → ∀ g' : WcG,
      g'.tp = g.tp →
      RdPreW W K exe endPc R' F' ms (sJ0 (_root_.Executable.labels exe).label ms (swWF Λ sL srS stop sa sv) exe
        endPc g') (sJ1 (sJ0 (_root_.Executable.labels exe).label ms (swWF Λ sL srS stop sa sv) exe endPc g')))
    (hWpost : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → (swWF Λ sL srS stop sa sv) m) → ∀ g' : WcG,
      g'.tp = g.tp →
      RdPostLW W K exe endPc R' F' (sJp lbl ms g') (sJp' lbl ms g') (sJh1 lbl ms g') (sJ2 lbl ms g')
        (sJ2' lbl ms g') (sJh2 lbl ms g') (sJ4 lbl ms g'))
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → (swWF Λ sL srS stop sa sv) m) → ∀ g' : WcG,
      g'.tp = g.tp →
      ∀ m0 σC c0, σC.regs.X0 = 2 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R'.callee (-208) (-48) 0)
        (fun m => F' m ∧ CKept R' (-208) (-48) 0 m0 m ∧ Abs R' ⟨-208, []⟩ m0 σC) c0)
    (hU : MainCallW W K p lbl ms exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) (setupMC 4).fn (setupMC 4).Z D2 ZU2
      (SetupArgs (SetupPostS lbl rdA64 hello1Pl) (setupMC 4).sw x0) Post
      ((_root_.Executable.labels exe).label (setupMC 4).sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) ⟨(_root_.Executable.labels exe).label (setupMC 4).sp1 +
        4 + 4 + 4,
        ⟨-(setupMC 4).Z.toInt, []⟩, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s →
        MainExit p ms s c v.toNat)
    (hW : MainSW W K exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) ms (setupMC 4) (SetupPostS lbl rdA64
      hello1Pl) Post g x0)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) (mainSN0 (_root_.Executable.labels
      exe).label g x0)) Q :=
  hello1_mainS_segGW_priv hp hend hK
    (wordsNone_swFSL_fstable hwf hrS hok (by simp [swRg, swR] at hlo; omega) hL8 hsub hfit hout hfitS) hR hal hD20
    hD28 hlo hlo2 hhi g x0 hc0 hlimM hlimS hlimU hQ hu hwf (fun _ h => h.1) hH hHi hctr hoffU hxa hWpre hWpost hstub
    hU hexit hW

end Spike.Test.A64MainSHello1G

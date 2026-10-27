/-
**`hello1_mainS_segGW` in the switched stack** (x86-64; the H7c wiring of
the frame): `hello1_mainS_segGW_priv` at the region and frame the producers
run `scc_rt_main` in after `scc_rt_start`'s switch (`startSwitchU_segW`,
`SwUW.main`): `swR v (-L) 0` under `WordsNone Λ ∧ swFSL L rS top a v`. Its
`hF` and `hwn` are discharged: `FStable` by `wordsNone_swFSL_fstable`
(`Spike/Lib/Rt/X64SwWordsNone.lean`) from the switch's own premises and the
taken range in the stack pool, `hwn` the first conjunct. A reachable thread's
`At … swFSL …` carries the `WordsNone` conjunct by `hello1_at_wordsNone`
(`Spike/Test/X64FrameHello1.lean`).
-/
import Spike.Test.X64MainSHello1GPriv
import Spike.Lib.Rt.X64SwWordsNone

namespace Spike.Test.X64MainSHello1G

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Rt
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (TP)
open Spike.Lib.X64.Flow.Ret0 (MainG WcG LimOk limA)
open Spike.Lib.X64.Alloc (Call Ea Jfull)
open Spike.Lib.X64.Flow.NewBuf (nbJc)
open Spike.Lib.X64.Flow.Hello1 (rdQ sJ1 sJE RdGW AG rdE oR hello1_rodata_setupGW_ret)
open Spike.Lib.SetupRet (SetupPostS hello1Pl)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN τ8)
open Spike.Lib.DmemPriv (WordsNone WordIn)

open Spike.Lib.X64.Rt (swFSL wordsNone_swFSL_fstable)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
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
    {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hR : (swRg sv sL).OK)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hlo : (swRg sv sL).lo ≤ -320) (hlo2 : (swRg sv sL).lo ≤ -8 - 64 - 8 - D2) (hhi : 0 ≤ (swRg sv sL).hi)
    (g : MainG) (x0 : BitVec 64) (hc0 : g.c0 = rdC0)
    (hlimM : LimOk ms (swWF Λ sL srS stop sa sv) (limA g.tp) (g.sp0 - 8#64 - (setupMC 4).Z.toBitVec))
    (hlimS : LimOk ms (swWF Λ sL srS stop sa sv) (limA g.tp) (g.sp0 - 8#64 - (setupMC 4).Z.toBitVec - 8#64 - 8#64 -
      (32 : Int64).toBitVec))
    (hlimU : LimOk ms (swWF Λ sL srS stop sa sv) (limA g.tp) (g.sp0 - 8#64 - (setupMC 4).Z.toBitVec - 8#64 - 8#64 -
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
        nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
          (sJ1 (sJE (_root_.Executable.labels exe).label ms (swWF Λ sL srS stop sa sv) g' R')) σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R' (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R'.callee (-48) (-160) 8) F'' (Ea ms q.1 l b w) s c →
        TP g'.tp s → ms.xa l b w s c)
    (hWR : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → (swWF Λ sL srS stop sa sv) m) → ∀ g' : WcG,
      g'.tp = g.tp →
      RdGW W K exe endPc R' F' ms lbl (swWF Λ sL srS stop sa sv) g')
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → (swWF Λ sL srS stop sa sv) m) → ∀ g' : WcG,
      g'.tp = g.tp →
      ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R'.callee (-216) (-24) 16)
        (fun m => F' m ∧ CKept R' (-216) (-24) 16 m0 m ∧ Abs R' ⟨-208, []⟩ m0 σC) c0)
    (hU : MainCallW W K p lbl ms exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) (setupMC 4).fn (setupMC 4).Z D2 ZU2
      (SetupArgs (SetupPostS lbl rdX64 hello1Pl) (setupMC 4).sw x0) Post
      ((_root_.Executable.labels exe).label (setupMC 4).sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) ⟨(_root_.Executable.labels exe).label (setupMC 4).sp1 +
        Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU (setupMC 4).Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : MainSW W K exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) ms (setupMC 4) (SetupPostS lbl rdX64
      hello1Pl) Post g x0)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc (swRg sv sL) (swWF Λ sL srS stop sa sv) (mainSN0 (_root_.Executable.labels
      exe).label g x0)) Q :=
  hello1_mainS_segGW_priv hp hend hK
    (wordsNone_swFSL_fstable hwf hrS hok (by simp [swRg, swR] at hlo; omega) hL8 hsub hfit hout hfitS) hR hD20 hD28
    hlo hlo2 hhi g x0 hc0 hlimM hlimS hlimU hQ hu hwf (fun _ h => h.1) hH hHi hctr hoffU hxa hWR hstub hU hexit hW

end Spike.Test.X64MainSHello1G

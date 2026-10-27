/-
**`hello1_mainS_segGW` with `hmem`, `hbuf` from `WordsNone`** (AArch64): the
setup's word premises discharged as in `hello1_rodata_setupGW_priv`
(`Spike/Lib/A64Hello1SetupPriv.lean`): a frame loading no word of the
heap or the image (`hwn`; `FStable` for a region off them,
`Alloc.wordsNone_fstable`; every reachable hello1 thread's,
`hello1_wordsNone`), the counter in the heap or the image, the arena inside
the heap, and every allocation's offset inside its units.
-/
import Spike.Test.A64MainSHello1G
import Spike.Lib.A64Hello1SetupPriv

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

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1_mainS_segGW` with `hmem`, `hbuf` from `WordsNone`.** -/
theorem hello1_mainS_segGW_priv {Λ : Scc.Sem.Layout}
    {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hlo : R.lo ≤ -336) (hlo2 : R.lo ≤ -80 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64) (hc0 : g.c0 = rdC0)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec))
    (hlimS : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec - (48 : Int64).toBitVec))
    (hlimU : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec - ZU2.toBitVec))
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hwf : Λ.WF) (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoffU : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hxa : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F'' : MachineData → Prop, (∀ m, F'' m → F' m) →
      (∀ m, F'' m → ∃ mC σC c, Abs R' ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms F exe endPc g')
          (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F exe endPc g')) .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R' (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R') F'' (Ea ms q.1 l b w) s c → TP g'.tp s → ms.xa l b w s c)
    (hWpre : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      RdPreW W K exe endPc R' F' ms (sJ0 (_root_.Executable.labels exe).label ms F exe endPc g')
        (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F exe endPc g')))
    (hWpost : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      RdPostLW W K exe endPc R' F' (sJp lbl ms g') (sJp' lbl ms g') (sJh1 lbl ms g') (sJ2 lbl ms g')
        (sJ2' lbl ms g') (sJh2 lbl ms g') (sJ4 lbl ms g'))
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      ∀ m0 σC c0, σC.regs.X0 = 2 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R'.callee (-208) (-48) 0)
        (fun m => F' m ∧ CKept R' (-208) (-48) 0 m0 m ∧ Abs R' ⟨-208, []⟩ m0 σC) c0)
    (hU : MainCallW W K p lbl ms exe endPc R F (setupMC 4).fn (setupMC 4).Z D2 ZU2
      (SetupArgs (SetupPostS lbl rdA64 hello1Pl) (setupMC 4).sw x0) Post
      ((_root_.Executable.labels exe).label (setupMC 4).sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label (setupMC 4).sp1 + 4 + 4 + 4,
        ⟨-(setupMC 4).Z.toInt, []⟩, fun σ _ => σ.regs.X0.toBitVec = v⟩ s c → ¬ ms.abortAt s →
        MainExit p ms s c v.toNat)
    (hW : MainSW W K exe endPc R F ms (setupMC 4) (SetupPostS lbl rdA64 hello1Pl) Post g x0)
    {Q : Frag isaLSE2} :
    SegW W K p lbl ms (At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)) Q := by
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hroom := hQ.room
  have hcells := hQ.cells
  exact
    hello1_mainS_segGW hp hend hK hF hR hal hD20 hD28 hlo hlo2 hhi g x0 hc0 hlimM hlimS hlimU hQ hu
      (Alloc.hmem_of_wordsNone hwf hwn hH hHi hctr hoffU) (Alloc.hbuf_of_wordsNone hwn hH hHi (by omega) (by omega))
      hxa hWpre hWpost hstub hU hexit hW

end Spike.Test.A64MainSHello1G

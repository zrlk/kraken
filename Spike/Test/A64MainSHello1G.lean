/-
**`scc_rt_main` on `hello1.w` (AArch64) through the parametric composition**
(a non-vacuity regression of `Spike/Lib/Rt/A64MainS.lean` with
`Spike/Lib/A64Hello1RodataSetupG.lean`): `Rt.mainS_segW` at `setupMC 4`
(`hello1Prog` passes `mainSIn` there), its setup interface `SetupCallW` for
`wc_rodata` given by `hello1_rodata_setupGW` in every callee region the call
hands it (depth `D1 = 256` below `main`'s frame), the post read as
`SetupPostS` at `hello1Pl`, the user function `wc_main` an interface
(`MainCallW`, as `mainS_segW` takes it).

The region reaches `336` below `scc_rt_main`'s entry `sp` (`hlo`: the frame
of `80` and `wc_rodata`'s `256`); `wc_main`'s depth `D2` is its interface's
(`hlo2`). As for the setup block, the runtime's frames (the allocator's and
the heap abort's) are not in the need table: the bound must come from
`stackLimit - Tcb.headroom`.
-/
import Spike.Lib.A64Hello1RodataSetupG
import Spike.Lib.Rt.A64MainS
import Spike.Test.A64SetupRetHello1

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

/-- `hello1Prog` passes `mainSIn` at four setup words. -/
theorem hello1_mainSIn : mainSIn SccCode.hello1Prog (setupMC 4) = true := by decide +kernel

/-- `setupMC 4`'s frame is `80` bytes. -/
theorem setupMC4_Z : (setupMC 4).Z.toInt = 80 := by decide

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` on `hello1.w` does not return, inside `W`**: `mainS_segW`
at `setupMC 4` with `wc_rodata`'s interface from `hello1_rodata_setupGW`
(its premises asked in every callee region `R'` and frame condition `F'`
under `F` the call hands it, for every ghost at `main`'s thread pointer),
`wc_main`'s interface `hU` and the exit `hexit` as `mainS_segW` asks them.
The source at the setup call is `rodata`'s body (`hc0`). -/
theorem hello1_mainS_segGW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hlo : R.lo ≤ -336) (hlo2 : R.lo ≤ -80 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64) (hc0 : g.c0 = rdC0)
    (hlimM : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec))
    (hlimS : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec - (48 : Int64).toBitVec))
    (hlimU : LimOk ms F exe endPc (limA g.tp) (g.sp0 - (setupMC 4).Z.toBitVec - ZU2.toBitVec))
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
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
  have hZ := setupMC4_Z
  have hS : SetupCallW W K p lbl ms exe endPc R F (setupMC 4).setup (setupMC 4).Z 256 48
      (SetupPostS lbl rdA64 hello1Pl) ((_root_.Executable.labels exe).label (setupMC 4).e0 + 4).toBitVec g.c0
      g.tp := by
    intro F' hR' hal' hF' hFF g' _ hc htp
    have hF0 : ∀ m, F' m → F m := fun m h => (hFF m h).1
    refine (hello1_rodata_setupGW hp hend hK hF' hR' hal' (by show (-256 : Int) ≤ -256; decide)
      (by show (0 : Int) ≤ 0; decide) hF0 g' (hc.trans hc0) hQ hu
      (fun q hq a ha m hm => hmem q hq a ha m (hF0 m hm)) (fun old ho i hi m hm => hbuf old ho i hi m (hF0 m hm))
      (hxa _ F' hF0 g' htp) (hWpre _ F' hF0 g' htp) (hWpost _ F' hF0 g' htp)
      (hstub _ F' hF0 g' htp)).mono_post fun _ _ ⟨he, hn, hdc, hpc, σ, hA, hD, hP, hrest⟩ =>
        ⟨he, hn, hdc, hpc, σ, hA, hD, Spike.Test.A64SetupRetHello1.rdPostS_setupPostS hP, hrest⟩
  exact mainS_segW hp hend hello1_mainSIn (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) hD20 hD28 hK hF hR hal (by rw [hZ]; omega) (by rw [hZ]; omega) hhi g x0
    hlimM hlimS hlimU hS hU hexit hW

end Spike.Test.A64MainSHello1G

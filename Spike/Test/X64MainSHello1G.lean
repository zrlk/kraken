/-
**`scc_rt_main` on `hello1.w` (x86-64) through the parametric composition**
(a non-vacuity regression of `Spike/Lib/Rt/X64MainS.lean` with
`Spike/Lib/X64Hello1RodataSetupG.lean`): `Rt.mainS_segW` at `setupMC 4`,
its setup interface `SetupCallW` for `wc_rodata` given by
`hello1_rodata_setupGW_ret` in every callee region the call hands it
(depth `D1 = 240` below the pushed return address), the user function
`wc_main` an interface (`MainCallW`, as `mainS_segW` takes it).

The region reaches `320` below `scc_rt_main`'s entry `%rsp` (`hlo`: the
saved `%rbp`, the frame of `64`, the return address and `wc_rodata`'s
`240`); `wc_main`'s depth `D2` is its interface's (`hlo2`). As for the setup
block, the runtime's frames (the allocator's and the heap abort's) are not
in the need table: the bound must come from `stackLimit - Tcb.headroom`.
-/
import Spike.Lib.X64Hello1RodataSetupG
import Spike.Test.X64MainSHello1

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

/-- `setupMC 4`'s frame is `64` bytes. -/
theorem setupMC4_Z : (setupMC 4).Z.toInt = 64 := by decide

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` on `hello1.w` does not return, inside `W`**: `mainS_segW`
at `setupMC 4` with `wc_rodata`'s interface from `hello1_rodata_setupGW_ret`
(its premises asked in every callee region `R'` and frame condition `F'`
under `F` the call hands it, for every ghost at `main`'s thread pointer),
`wc_main`'s interface `hU` and the exit `hexit` as `mainS_segW` asks them.
The source at the setup call is `rodata`'s body (`hc0`). -/
theorem hello1_mainS_segGW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    {D2 : Int} (hD20 : 0 ≤ D2) (hD28 : D2 % 8 = 0) {ZU2 : Int64} {Post : Ctl → BitVec 64 → Prop}
    (hlo : R.lo ≤ -320) (hlo2 : R.lo ≤ -8 - 64 - 8 - D2) (hhi : 0 ≤ R.hi)
    (g : MainG) (x0 : BitVec 64) (hc0 : g.c0 = rdC0)
    (hlimM : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (setupMC 4).Z.toBitVec))
    (hlimS : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (setupMC 4).Z.toBitVec - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hlimU : LimOk ms F (limA g.tp) (g.sp0 - 8#64 - (setupMC 4).Z.toBitVec - 8#64 - 8#64 - ZU2.toBitVec))
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hxa : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F'' : MachineData → Prop, (∀ m, F'' m → F' m) →
      (∀ m, F'' m → ∃ mC σC c, Abs R' ⟨-48, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
          (sJ1 (sJE (_root_.Executable.labels exe).label ms F g' R')) σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R' (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R'.callee (-48) (-160) 8) F'' (Ea ms q.1 l b w) s c →
        TP g'.tp s → ms.xa l b w s c)
    (hWR : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      RdGW W K exe endPc R' F' ms lbl F g')
    (hstub : ∀ (R' : Region) (F' : MachineData → Prop), (∀ m, F' m → F m) → ∀ g' : WcG, g'.tp = g.tp →
      ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R'.callee (-216) (-24) 16)
        (fun m => F' m ∧ CKept R' (-216) (-24) 16 m0 m ∧ Abs R' ⟨-208, []⟩ m0 σC) c0)
    (hU : MainCallW W K p lbl ms exe endPc R F (setupMC 4).fn (setupMC 4).Z D2 ZU2
      (SetupArgs (SetupPostS lbl rdX64 hello1Pl) (setupMC 4).sw x0) Post
      ((_root_.Executable.labels exe).label (setupMC 4).sp1).toBitVec g.tp)
    (hexit : ∀ s c (v : BitVec 64), Post c v →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label (setupMC 4).sp1 + Int64.ofNat 4 + Int64.ofNat 4 +
        Int64.ofNat 5, oU (setupMC 4).Z, fun σ _ => σ.regs.rdi.toBitVec = v⟩ s c →
        ¬ ms.abortAt s → MainExit p ms s c v.toNat)
    (hW : MainSW W K exe endPc R F ms (setupMC 4) (SetupPostS lbl rdX64 hello1Pl) Post g x0)
    {Q : Frag isa} :
    SegW W K p lbl ms (At exe endPc R F (mainSN0 (_root_.Executable.labels exe).label g x0)) Q := by
  have hZ := setupMC4_Z
  have hS : SetupCallW W K p lbl ms exe endPc R F (setupMC 4).setup (setupMC 4).Z 240 32
      (SetupPostS lbl rdX64 hello1Pl) ((_root_.Executable.labels exe).label (setupMC 4).sp0).toBitVec g.c0 g.tp := by
    intro F' hR' hF' hFF g' _ hc htp
    have hF0 : ∀ m, F' m → F m := fun m h => (hFF m h).1
    exact hello1_rodata_setupGW_ret hp hend hK hF' hR' (by show (-240 : Int) ≤ -240; decide)
      (by show (8 : Int) ≤ 8; decide) hF0 g' (hc.trans hc0) hQ hu
      (fun q hq a ha m hm => hmem q hq a ha m (hF0 m hm)) (fun old ho i hi m hm => hbuf old ho i hi m (hF0 m hm))
      (hxa _ F' hF0 g' htp) (hWR _ F' hF0 g' htp) (hstub _ F' hF0 g' htp)
  exact mainS_segW hp hend Spike.Test.X64MainSHello1.hello1_mainSIn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hD20 hD28 hK hF hR (by rw [hZ]; omega) (by rw [hZ]; omega) hhi g x0
    hlimM hlimS hlimU hS hU hexit hW

end Spike.Test.X64MainSHello1G

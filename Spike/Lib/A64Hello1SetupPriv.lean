/-
**The hello1 setup's `hmem` and `hbuf` from `WordsNone`** (AArch64):
`hello1_rodata_setupGW`'s word premises discharged by `Alloc.hmem_of_wordsNone`,
`Alloc.hbuf_of_wordsNone` (`Spike/Lib/A64WordsNone.lean`): a frame loading no
word of the heap or the image (`hwn`; every reachable hello1 thread's,
`Spike/Test/A64DmemPrivHello1.lean`, and `FStable` with another frame,
`Spike/Test/A64FrameHello1.lean`).

- `hello1_rodata_setupGW_priv`: `hello1_rodata_setupGW` with them so.
-/
import Spike.Lib.A64WordsNone
import Spike.Lib.A64Hello1RodataSetupG

namespace Spike.Lib.A64.Flow

namespace Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk WcG limA tcbA_limA)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull mOf)
open Spike.Lib.A64.Flow.NewBuf (allocAbortDepth allocAbortDepth_48 nbX nbJc NBX)
open Spike.Lib.A64.Flow.Setup (entJ sEn sRet sAb chainW alloc_stepW setup_callW)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 τ8 rdK1 rdK2 rdC0_run rdCN_newBuf
  rdCA_store rdC2_store rdC1_next rdC3_next rdC4_run)

open Spike.Lib.DmemPriv (WordsNone WordIn)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1_rodata_setupGW` with `hmem`, `hbuf` from `WordsNone`**
(`Alloc.hmem_of_wordsNone`, `Alloc.hbuf_of_wordsNone`): the frame loads no
word of the heap or the image (`hwn`), the counter is in the heap or the
image, the arena inside the heap, and every allocation's offset inside its
units (`hoffU`). -/
theorem hello1_rodata_setupGW_priv {Λ : Scc.Sem.Layout}
    {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hwf : Λ.WF) (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoffU : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
          (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)) .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → TP g.tp s → ms.xa l b w s c)
    (hWpre : RdPreW W K exe endPc R F ms (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
      (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)))
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g) (sJp' lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g)
      (sJ2' lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g))
    (hstub : ∀ m0 σC c0, σC.regs.X0 = 2 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-208) (-48) 0)
        (fun m => F m ∧ CKept R (-208) (-48) 0 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label ms F0 exe endPc "wc_rodata" 48 g))
      (At exe endPc R F (sXf lbl ms g)) :=
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hroom := hQ.room
  have hcells := hQ.cells
  hello1_rodata_setupGW hp hend hK hF hR hal hlo hhi hFF g hc0 hQ hu
    (Alloc.hmem_of_wordsNone hwf hwn hH hHi hctr hoffU)
    (Alloc.hbuf_of_wordsNone hwn hH hHi (by omega) (by omega)) hxa hWpre hWpost hstub

end Hello1

end Spike.Lib.A64.Flow

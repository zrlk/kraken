/-
**The hello1 setup's `hmem` and `hbuf` from `WordsNone`** (x86-64):
`hello1_rodata_setupGW`'s word premises discharged by `Alloc.hmem_of_wordsNone`,
`Alloc.hbuf_of_wordsNone` (`Spike/Lib/X64WordsNone.lean`): a frame loading no
word of the heap or the image (`hwn`; every reachable hello1 thread's,
`Spike/Test/X64DmemPrivHello1.lean`, and `FStable` with another frame,
`Spike/Test/X64FrameHello1.lean`).

- `hello1_rodata_setupGW_priv`, `hello1_rodata_setupGW_ret_priv`: `hello1_rodata_setupGW`
  and `hello1_rodata_setupGW_ret` with them so.
-/
import Spike.Lib.X64WordsNone
import Spike.Lib.X64Hello1RodataSetupG

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Flow.Ret0 (CallerCells LimOk WcG limA)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.X64.Flow.NewBuf (allocAbortDepth allocAbortDepth_40 nbX nbJc NBX)
open Spike.Lib.X64.Flow.Setup (entJ sEn sRet sAb chainW alloc_stepW lane_stepW ret_stepW setup_callW
  callOK_tp callOK_untp limOk_tp)
open Spike.Lib.X64.Rt (uN0 uNxS rdX64)
open Spike.Lib.SetupRet (SetupPostS hello1Pl)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 eW1 eN τ8 rdK1 rdK2 rdC0_run
  rdCN_newBuf rdC4_run bufElem_b evalAt_b3 rdK1_lt rdK2_lt)

open Spike.Lib.DmemPriv (WordsNone WordIn)

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`hello1_rodata_setupGW` with `hmem`, `hbuf` from `WordsNone`**
(`Alloc.hmem_of_wordsNone`, `Alloc.hbuf_of_wordsNone`): the frame loads no
word of the heap or the image (`hwn`), the counter is in the heap or the
image, the arena inside the heap, and every allocation's offset inside its
units (`hoffU`). -/
theorem hello1_rodata_setupGW_priv {Λ : Scc.Sem.Layout}
    {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hwf : Λ.WF) (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoffU : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
          (sJ1 (sJE (_root_.Executable.labels exe).label ms F0 g R)) σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-48) (-160) 8) F' (Ea ms q.1 l b w) s c →
        TP g.tp s → ms.xa l b w s c)
    (hW : RdGW W K exe endPc R F ms lbl F0 g)
    (hstub : ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-216) (-24) 16)
        (fun m => F m ∧ CKept R (-216) (-24) 16 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (uN0 (_root_.Executable.labels exe).label ms F0 "wc_rodata" 32 g))
      (At exe endPc R F (uNxS (rdPostS lbl ms) g)) :=
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hroom := hQ.room
  have hcells := hQ.cells
  hello1_rodata_setupGW hp hend hK hF hR hlo hhi hFF g hc0 hQ hu
    (Alloc.hmem_of_wordsNone hwf hwn hH hHi hctr hoffU)
    (Alloc.hbuf_of_wordsNone hwn hH hHi (by omega) (by omega)) hxa hW hstub

/-- **`hello1_rodata_setupGW_ret` with `hmem`, `hbuf` from `WordsNone`**
(`Alloc.hmem_of_wordsNone`, `Alloc.hbuf_of_wordsNone`): the frame loads no
word of the heap or the image (`hwn`), the counter is in the heap or the
image, the arena inside the heap, and every allocation's offset inside its
units (`hoffU`). -/
theorem hello1_rodata_setupGW_ret_priv {Λ : Scc.Sem.Layout}
    {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hwf : Λ.WF) (hwn : ∀ m, F m → WordsNone Λ m.dmem) (hH : Λ.heap.lo ≤ ms.heap)
    (hHi : ms.heap + 16 * ms.cells ≤ Λ.heap.lo + Λ.heap.size)
    (hctr : WordIn Λ.heap ms.ctr ∨ WordIn Λ.data ms.ctr)
    (hoffU : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ms.off q.n q.τ ≤ 16 * ms.units q.n q.τ)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        nbJc (_root_.Executable.labels exe).label rdE ((_root_.Executable.labels exe).label ".Lwc_rodata.entry") oR
          (sJ1 (sJE (_root_.Executable.labels exe).label ms F0 g R)) σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧
        CKept R (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-48) (-160) 8) F' (Ea ms q.1 l b w) s c →
        TP g.tp s → ms.xa l b w s c)
    (hW : RdGW W K exe endPc R F ms lbl F0 g)
    (hstub : ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-216) (-24) 16)
        (fun m => F m ∧ CKept R (-216) (-24) 16 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (uN0 (_root_.Executable.labels exe).label ms F0 "wc_rodata" 32 g))
      (At exe endPc R F (uNxS (SetupPostS lbl rdX64 hello1Pl) g)) :=
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hroom := hQ.room
  have hcells := hQ.cells
  hello1_rodata_setupGW_ret hp hend hK hF hR hlo hhi hFF g hc0 hQ hu
    (Alloc.hmem_of_wordsNone hwf hwn hH hHi hctr hoffU)
    (Alloc.hbuf_of_wordsNone hwn hH hHi (by omega) (by omega)) hxa hW hstub

end Spike.Lib.X64.Flow.Hello1

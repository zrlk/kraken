/-
**hello.w's worker segment's control fact with `RelZ`** (AArch64): the fragment `ZHR exe kp` (`ZH`
and wake's
`RelZ`, `Spike/Lib/A64RelW1Nodes.lean`), so that `helloDR`'s invariant at
`Z := fun _ => ZHR exe kp` gives the worker's `hW1` (every instruction's
tree writes at most once, a release write), and the segments' premises at
`Z0 ∧ RelZ` (`ZR`): `Z0`'s (`Spike/Lib/A64HelloZ.lean`) and `RelZ`'s
(`Spike/Lib/A64HelloRelZ.lean`) combined per node.

- `ZR`, `ZHR`; `passZ_ZHR`, `zStoreOk_ZHR` (the consumers' premises).
- `relW1_of_pend`: `RelZ` reads no control, so a pending frame run into a
  fragment inside `RelZ` gives the state's `RelW1`.
- `wcR_entry`: non-vacuity, `NNH ∧ ZHR` at every entry state of the
  worker segment.
- `wcR_hz`, `wcR_hZE`, `wcR_hZC`, `wcR_hZP`, `wcR_hZA`, `wcR_hZu`, `wcR_hZW`,
  `wcR_hZU`: `seg_wcWorkerS`'s premises at `Z := ZR exe kp`.
- `thrR_hz`, `thrR_hZE`, `thrR_hZT`, `childR_hZc`: `seg_thrWorkerH`'s and
  `seg_childStubH`'s at `Z := fun s c => ZR exe kp s c []`.
-/
import Spike.Lib.A64HelloZ
import Spike.Lib.A64HelloRelZ
import Spike.Lib.A64WakeZX

namespace Spike.Lib.A64.Flow.Worker.Hello.Z

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Spike.Lib Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.RelZ (RelZ)
open Spike.Lib.A64.Flow.Worker.Hello.Child (Words wcJE thrJE thrJ cN cBlk cLen pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Wk (wkJ wcPs)
open Spike.Lib.A64.Flow.Worker.Hello.Pass (HPassC helloPassT)
open SccCode (helloProg)

/-- **`Z0` and `RelZ`**: the segments' control fact. -/
def ZR (exe : _root_.Executable) (kp : Nat) : FragS isaLSE2 := fun s c fs => Z0 exe kp s c fs ∧ RelZ s c

/-- **The worker segment's control fact with `RelZ`**: `ZH` and `RelZ`. -/
def ZHR (exe : _root_.Executable) (kp : Nat) : FragS isaLSE2 := fun s c fs => ZH exe kp s c fs ∧ RelZ s c

/-- The segment's fragment (`seg_wcWorkerS`'s, at `ZR`) is inside `ZHR`. -/
theorem ZR.toZHR {exe : _root_.Executable} {kp : Nat} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (h : ZR exe kp s c fs) (hs : fs = [] → SysSafe s) : ZHR exe kp s c fs :=
  ⟨⟨h.1, hs⟩, h.2⟩

/-- **Row 5j-k: `PassZ` at `ZHR`.** -/
theorem passZ_ZHR {exe : _root_.Executable} {kp : Nat} : HelloPassH.PassZ helloPassT (ZHR exe kp) :=
  fun s c fs h => passZ_ZH s c fs h.1

/-- **Row C4: `ZStoreOk` at `ZHR`.** -/
theorem zStoreOk_ZHR {ι : Type} {exe : _root_.Executable} {kp : Nat} :
    HelloW1Store.ZStoreOk exe (fun _ : ι => ZHR exe kp) :=
  fun w s c h => zStoreOk_ZH (ι := ι) w s c h.1

/-- **`hW1` from a pending run**: `RelZ` reads no control, so a pending
frame run into a fragment inside `RelZ` gives the state's `RelW1`. -/
theorem relW1_of_pend {p : Prog} {Zf : FragS isaLSE2} (hZ : ∀ s c fs, Zf s c fs → RelZ s c) {s : State}
    {c : Ctl} {fs : List TermRun.Frame} (h : Pend p Zf s c fs) :
    ∀ e, isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e :=
  let ⟨_, _, _, h⟩ := h; hZ _ _ _ h

section Inst

variable {exe : _root_.Executable} [hv : Kraken.Executable.ValidLayout exe] {kp : Nat} {endPc : Int64}
  (hp : Lays exe helloProg kp)
include hp

/-- **The abort path** (`hZA`). -/
theorem wcR_hZA {fr : TermRun.Frame} {c' : Ctl} (hu : NotUnpk c') {s : State} (he : s.exe = exe)
    (h : Spike.Lib.A64.PcRuns.PcIn abortRuns s) (hr : RelZ s c') : ZR exe kp s c' [fr] :=
  ⟨wc_hZA hp hu he h, hr⟩

omit hv hp in
/-- **On a frame no `unpark` binding** (`hZu`). -/
theorem wcR_hZu : ∀ fr s c, ZR exe kp s c [fr] → ∀ x a e, c.term ≠ .let_ x (.ext .unpark a) e :=
  fun _ _ _ h => h.1.2.2.1 (List.cons_ne_nil _ _)

variable (hend : endPc = endOf exe helloProg kp)
include hend

/-- **`wc_worker`'s prologue** (`hz`). -/
theorem wcR_hz {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {c0 : Ctl} {w : Words}
    {x29 ra tp : BitVec 64} {X : AS → Prop} (h0 : ¬ HPassC c0) :
    ProW (fun s c => ZR exe kp s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "wc_worker") 96 8 ".L20_wc_worker.stack_grow" wcPs
      (fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ) :=
  Wake.ZX.ProW.and (ProW.ofPcs fun s σ c k hk he hs hJ =>
      wc_hz hp h0 s σ c k (Nat.lt_of_lt_of_eq hk (by decide)) he hs hJ.1)
    (Wk.wcPro_relH hp hend hR hal hlo hhi)

/-- **Non-vacuity: `ZHR` at `wc_worker`'s entry.** Every state of the
worker segment's entry (`seg_wcWorkerS`'s, `helloDR`'s `P`) is off the
transfer sites and inside `ZHR` on no frame, so `helloDR`'s invariant at
`Z := ZHR` holds of its entry states (`helloDR_entry`). -/
theorem wcR_entry {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {c0 : Ctl} {w : Words}
    {x29 ra tp : BitVec 64} {X : AS → Prop} (h0 : ¬ HPassC c0) {s : State} {c : Ctl}
    (hs : At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩ s c) :
    NNH exe endPc s ∧ ZHR exe kp s c [] := by
  have hin := Wk.hello_wcPro
  simp only [Wk.wcPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, -⟩ := hin
  have e0 := label_labelGap hp g0
  rw [ofNat4_zero] at e0
  have hnn := blkW_nn (R := R) (F := F) (n := ⟨(_root_.Executable.labels exe).label "wc_worker", ⟨0, []⟩,
      fun σ c => wcJE c0 w x29 ra tp σ c ∧ X σ⟩) (code_of hp hend b0 (by rw [e0, ofNat4_zero]))
    (by simp [chkHead, notNop])
  have h := Wk.NodeZA.toW0 (NodeZA.and hnn (wcR_hz (ms := ms) hp hend hR hal hlo hhi h0).w0) s c hs
  exact ⟨h.1.1.toH, h.1.2.toZHR fun _ => h.1.1.2.2.2⟩

/-- **`wc_worker`'s `.0_entry` block** (`hZE`). -/
theorem wcR_hZE {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) {c0 : Ctl} {w : Words} {x29 ra tp : BitVec 64}
    {Pr : AS → Nat → Ctl → Prop} (h0 : ¬ HPassC c0) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (Body.wN (_root_.Executable.labels exe).label (wkJ c0 w x29 ra tp) Pr .e) Body.wkE :=
  NodeZA.and (wc_hZE hp h0).toA (Wk.wE_relH hp hend hR hal hlo hhi)

/-- **`wc_worker`'s call node** (`hZC`). -/
theorem wcR_hZC {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -192) (hhi : 0 ≤ R.hi) {J Kc : AS → Ctl → Prop} (hK : ∀ σ c, Kc σ c → ¬ HPassC c) :
    NodeW (fun s c => ZR exe kp s c []) (fun _ _ => False) exe endPc R F
      (Body.wCall (_root_.Executable.labels exe).label J Kc) :=
  Wake.ZX.NodeW.and (NodeZ.toA (blk := [ldrDir .X10 .X10 0]) (wc_hZC hp hK)).toW
    (Wk.wCall_relH hp hend hR hal hlo hhi)

/-- **`print`'s nodes** (`hZP`), its predicates' controls at no `unpark`
binding. -/
theorem wcR_hZP {fr : TermRun.Frame} {R : Region} {F : MachineData → Prop} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {Pc Qc : AS → Nat → Ctl → Prop} {σC : AS}
    (hP : ∀ k c, Pc σC k c → NotUnpk c) (hQ : ∀ k c, Qc σC k c → NotUnpk c) (i : PrintF.PN) :
    NodeZA (fun s c => ZR exe kp s c [fr]) exe endPc R F (PrintF.cN (_root_.Executable.labels exe).label Pc Qc σC i)
      (PrintF.FA.blkN i) :=
  NodeZA.and ((wc_hZP hp hP hQ i).toAOf (PrintF.FA.lenN_eq i)) (Wk.print_relH hp hend hR hal hlo hhi i)

/-- **`wc_worker`'s tail** (`hZW`). -/
theorem wcR_hZW {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -96) (hhi : 0 ≤ R.hi) {cw c1 c2 : Ctl} {A B x29 ra tp : BitVec 64} (hw : ¬ HPassC cw)
    (h1 : HPassC c1) (h2 : HPassC c2) (i : HelloTail.PN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (HelloTail.N (_root_.Executable.labels exe).label cw c1 c2 A B x29 ra tp i) (HelloTail.blkN i) :=
  NodeZA.and ((wc_hZW hp hw h1 h2 i).toAOf (HelloTail.lenN_eq i)) (Wk.tail_relH hp hend hR hal hlo hhi i)

/-- **`scc_rt_unpark`'s nodes** (`hZU`). -/
theorem wcR_hZU {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {c1 c2 : Ctl} {B x29 ra tp : BitVec 64} (h1 : HPassC c1)
    (h2 : HPassC c2) (i : Unpark.PN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (Unpark.N (_root_.Executable.labels exe).label c1 c2 B x29 ra tp i) (Unpark.blkN i) :=
  NodeZA.and ((wc_hZU hp h1 h2 i).toAOf (by cases i <;> rfl)) (Wk.unpk_relH hp hend hR hal hlo hhi i)

/-- **`scc_rt_thr_worker`'s prologue** (`hz`). -/
theorem thrR_hz {R : Region} {F : MachineData → Prop} {ms : MemSide isaLSE2} (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {c0 : Ctl} {w : Words}
    {tp sp0 : BitVec 64} (h0 : ¬ HPassC c0) :
    ProW (fun s c => ZR exe kp s c []) (fun _ _ => False) exe endPc R F ms
      ((_root_.Executable.labels exe).label "scc_rt_thr_worker") 80 8 (HThrTail.pfx0 ++ ".stack_grow") thrPs
      (thrJE c0 w tp sp0) :=
  Wake.ZX.ProW.and (ProW.ofPcs fun s σ c k hk he hs hJ =>
      thr_hz hp h0 s σ c k (Nat.lt_of_lt_of_eq hk (by decide)) he hs hJ)
    (Wk.thrPro_relH hp hend hR hal hlo hhi)

/-- **`scc_rt_thr_worker`'s head** (`hZE`). -/
theorem thrR_hZE {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {c0 : Ctl} {w : Words} {tp sp0 : BitVec 64} {L : Ctl → Ctl → Prop}
    (h0 : ¬ HPassC c0) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (HThrHead.tN HThrTail.pfx0 (_root_.Executable.labels exe).label (thrJ c0 w tp sp0) L .e) HThrHead.thE :=
  NodeZA.and (thr_hZE hp h0).toA (Wk.thrHead_relH hp hend hR hal hlo hhi .e)

/-- **`scc_rt_thr_worker`'s tail** (`hZT`). -/
theorem thrR_hZT {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -80) (hhi : 0 ≤ R.hi) {c3 : Ctl} {tp : BitVec 64} (h3 : HPassC c3) (i : HThrTail.PN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F
      (HThrTail.N HThrTail.pfx0 (_root_.Executable.labels exe).label c3 tp i) (HThrTail.blkN i) :=
  NodeZA.and ((thr_hZT hp h3 i).toAOf (HThrTail.lenN_eq i)) (Wk.thrTail_relH hp hend hR hal hlo hhi i)

/-- **The child's stub** (`hZc`). -/
theorem childR_hZc {R : Region} {F : MachineData → Prop} (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -224) (hhi : 0 ≤ R.hi) {cW : Ctl} {w : Words} {tp sp0 : BitVec 64} (h0 : ¬ HPassC cW)
    (i : Child.CN) :
    NodeZA (fun s c => ZR exe kp s c []) exe endPc R F (cN pfxM (_root_.Executable.labels exe).label cW w tp sp0 i)
      (cBlk i) :=
  NodeZA.and ((child_hZc hp h0 i).toAOf (Child.cLen_eq i)) (Wk.child_relH hp hend hR hal hlo hhi i)

end Inst

end Spike.Lib.A64.Flow.Worker.Hello.Z

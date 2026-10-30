/-
**wake.w's worker side at the instance, its states inside `wakeZX`**
(AArch64): the worker's `WSide` (`WorkerSide.side`) at the instance data (`WakeInst`: the ghost record `Gh`, both threads' memory side
`wakeMs`), whose pairs are those of any segment keeping
`ZX.wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf exe kp` under the
record's placement and memory side, and `WakeAssemblyI.wake_obligations_IWP`'s
worker premises `hW`, `hmp` at it. The spawned child's segment
(`Child.seg_childPreNNA'` with `ZX.childThrZA_X'`, `ZX.cZA_X'`) is one of
them (`childSeg_X`), so its entry is a pair of the side (`wkP_of`; with the
entry wide, `WorkerSide.side_entry` puts it in the invariant). The listing is
wake.w's certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `segTC_iUnion`: segments from each of a family of preconditions are one
  from their union.
- `wkP`, `wkP_seg`: the union of the preconditions of the segments keeping
  `wakeZX` (from which the worker's states never leave it), its segment.
- `wakeD`: the worker's side at the instance (`lbl w := w.1.lbl`,
  `ms w := wakeMs hp i w.1`, `cw w := w.1.cwW`, `S w := w.1.S`).
- `hW_I`, `hmp_I`: `wake_obligations_IWP`'s `hW` and `hmp` at `wakeD`.
- `childSeg_X`: `seg_childPreNNA'` with its `Z` premises discharged at
  `Z := wakeZX`; `wkP_of`: a segment's precondition's pairs (the child's
  entry, by `childSeg_X` at `p := wakeSrc`, `lbl := w.1.lbl`,
  `ms := wakeMs hp i w.1`, `Λw := (RuntimeLayout.ofPlaceW hp i).Λ`) are
  pairs of `wkP`.
-/
import Spike.Lib.WakeInst
import Spike.Lib.A64WakeZXA
import Spike.Lib.WakeWorkerSide
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeWorkerX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Child
open Spike.Lib.A64.Flow.Worker.Wake.Labels (ThrZA)
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy wc1)
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.WakeInst (Gh wakeMs)
open Spike.Lib.WakeW1.WorkerSide (side side_inv)

/-! ## Unions of segments -/

/-- **Segments from a family of preconditions are one from their union**
(the invariant: the union of theirs). -/
theorem segTC_iUnion {S : Frag isaLSE2} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {Q : Frag isaLSE2} {κ : Sort _} {P : κ → Frag isaLSE2} (h : ∀ j, SegTC S p lbl ms (P j) Q) :
    SegTC S p lbl ms (fun s c => ∃ j, P j s c) Q := by
  refine ⟨fun s c => ∃ j, Classical.choose (h j) s c, fun s c ⟨j, hj⟩ => ⟨j, (Classical.choose_spec (h j)).1 s c hj⟩,
    fun s c ⟨j, hj⟩ => (Classical.choose_spec (h j)).2.1 s c hj, ?_⟩
  rintro s c ⟨j, hj⟩
  exact ((Classical.choose_spec (h j)).2.2 s c hj).mono fun s c h => h.imp_left fun h => ⟨j, h⟩

/-! ## The worker's side at the instance -/

section Side

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
  (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat)
  (lbl' : WeakMem.AllocLabel → Option Nat) (cSf : WeakMem.Address)

/-- **The worker's pairs**: those of the precondition of some segment
keeping `wakeZX` (at the instance's layout, labels `lbl'`, flag `cSf`)
under the record's placement and memory side, to the empty fragment. -/
def wkP (w : {g : Gh // ok g}) : Frag isaLSE2 := fun s c =>
  ∃ Pj : Frag isaLSE2, SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf exe kp)) wakeSrc
    w.1.lbl (wakeMs hp i w.1) Pj (fun _ _ => False) ∧ Pj s c

/-- **A segment's precondition's pairs are the worker's.** -/
theorem wkP_of {w : {g : Gh // ok g}} {Pj : Frag isaLSE2}
    (h : SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf exe kp)) wakeSrc w.1.lbl
      (wakeMs hp i w.1) Pj (fun _ _ => False)) {s : State} {c : Ctl} (hP : Pj s c) :
    wkP hp i ok exe endPc kp lbl' cSf w s c :=
  ⟨Pj, h, hP⟩

/-- `wkP`'s segment. -/
theorem wkP_seg (w : {g : Gh // ok g}) :
    SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf exe kp)) wakeSrc w.1.lbl
      (wakeMs hp i w.1) (wkP hp i ok exe endPc kp lbl' cSf w) (fun _ _ => False) :=
  (segTC_iUnion (κ := {Pj : Frag isaLSE2 // SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf
      exe kp)) wakeSrc w.1.lbl (wakeMs hp i w.1) Pj (fun _ _ => False)}) fun j => j.2).mono_pre
    fun _ _ ⟨Pj, h, hP⟩ => ⟨⟨Pj, h⟩, hP⟩

/-- `wakeMs`' kernel model. -/
theorem wakeMs_K (g : Gh) : (wakeMs hp i g).K = some Scc.Sem.A64.abi := rfl

/-- **The worker's side at the instance**: `WorkerSide.side` of `wkP_seg`,
the record's placement, memory side, pointer word and spawn size. -/
noncomputable def wakeD : WakeW1.WSide {g : Gh // ok g} :=
  side (fun w => w.1.lbl) (fun w => wakeMs hp i w.1) (wkP hp i ok exe endPc kp lbl' cSf)
    (fun w => wakeMs_K hp i w.1) (wkP_seg hp i ok exe endPc kp lbl' cSf) (fun w => w.1.cwW) (fun w => w.1.S)

/-- **`wake_obligations_IWP`'s `hW`** at `wakeD`. -/
theorem hW_I : ∀ w s c, (wakeD hp i ok exe endPc kp lbl' cSf).Wi w s c →
    NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceW hp i).Λ lbl' cSf exe kp) s c :=
  fun w s c h => (side_inv w s c h).1

/-- **`wake_obligations_IWP`'s `hmp`** at `wakeD`: `wakeMs`' runtime
accesses are to words mapped in the loaded kernel state. -/
theorem hmp_I : ∀ w L wr, ((wakeD hp i ok exe endPc kp lbl' cSf).ms w).mp L wr →
    Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (RuntimeLayout.ofPlaceW hp i).Λ) wr L = true :=
  fun _ _ _ h => h.1

end Side

/-! ## The spawned child's segment keeps `wakeZX` -/

section Child

open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerBody)
open Spike.Lib.A64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.A64.Flow.Ret0 (stacksA)
open Spike.Lib.A64.Rt (TcbGG tcbOf)
open Spike.Lib.A64Consumer (Own)

/-- **`seg_childPreNNA'` at `Z := wakeZX Λw lbl' cSf exe kp`**, its `ThrZA`
and stub premises discharged (`ZX.childThrZA_X'`, `ZX.cZA_X'`): for each
pair of words, given `seg_childPreNNA'`'s premises, `w1` the flag's
locative `cSf` (`hw`) and the words' `ValRep` under `lbl'` (`hv1'`,
`hv2'`), the child's segment to the empty fragment. -/
theorem childSeg_X {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    {r0 r1 : Range} {X : State → Prop} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {lab : Label → Int64} {q : TcbGG} (hPC : ∀ st, X st → PreChild ms own lab q st)
    (hr1 : r1 = r1Of lab) (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64) (hal : (stacksA lab).toNat % 16 = 0)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hpw : ∃ d, p.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧ d.argTy = workerTy)
    (T : Ty) :
    ∃ (th : Thread isaLSE2) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.getXReg .X9).toNat = cA ∧ (th.st.st.1.regs.getXReg .X10).toNat = meW ∧
      callOf abi th = some (.clone (r1.lo + r1.size) (tcbOf lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR (r1.lo + r1.size) (-16384))
          (DFrame (childR (r1.lo + r1.size) (-16384))
            (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
          (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size)))
          (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          cA + 8 ≤ 2 ^ 64 → (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) exe endPc
            (BitVec.ofNat 64 (tcbOf lab q).toNat + 24#64) 1#64 →
          w1.val = .loc cSf 0 → ValRep lbl' w1.val cA → ValRep lbl' w2.val meW →
          SegTC (NNZ exe endPc (wakeZX Λw lbl' cSf exe kp)) p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf lab q).toNat) (BitVec.ofNat 64 (r1.lo + r1.size))))
            (fun _ _ => False)) := by
  obtain ⟨th, cA, meW, hcA, hmW, hth, h9, h10, hcall, hk⟩ :=
    seg_childPreNNA' (Z := wakeZX Λw lbl' cSf exe kp) (Q := fun _ _ => False) hp hend h hX hPC hr1 hbd hal htls
      hout hK hpw T
  have hr1e : r1Of lab = ⟨(stacksA lab).toNat + 16384, 16384⟩ := by
    have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
      show (stacksA lab + 16384#64).toNat = _
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
    rw [show r1Of lab = ⟨(r1Of lab).lo, 16384⟩ from rfl, hlo1]
  obtain ⟨-, -, -, hR, hal', hlo', hhi'⟩ := Spike.Lib.A64.Rt.childStub_region_stk hr1e hal hbd
  subst hr1
  refine ⟨th, cA, meW, hcA, hmW, hth, h9, h10, hcall, fun w1 w2 => ⟨(hk w1 w2).1,
    fun hv1 htag hv2 hc8 hcout hS htp4 hSx hw hv1' hv2' => (hk w1 w2).2 hv1 htag hv2 hc8 hcout hS htp4 hSx
      (ZX.childThrZA_X' hp hend hR hal' hlo' hhi' hcA hmW hw hv1' hv2')
      (ZX.cZA_X' hp hend hR hal' hlo' hhi' hcA hmW hv1' hv2')⟩⟩

end Child

/-- info: 'Spike.Lib.WakeWorkerX.hW_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hW_I

/-- info: 'Spike.Lib.WakeWorkerX.childSeg_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms childSeg_X

end Spike.Lib.WakeWorkerX

/-
**wake.w's worker side at the x86-64 instance, its states inside `wakeZX`**
(in the manner of `Spike/Lib/WakeWorkerX.lean`): the worker's `WSide`
(`WorkerSide.side`) at the instance data (`X64WakeInst`: the ghost record
`Gh`, the worker's memory side `msW`), whose pairs are those of any segment
keeping `ZX.wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf W exe kp`
under the record's placement and the worker's memory side, and the worker
premises `hW`, `hmp` at it. The spawned child's segment
(`Child.seg_childPreNNA'` with `ZX.childThrZA_X'`, `ZX.cZA_X'`) is one of
them (`childSeg_X`), so its entry is a pair of the side (`wkP_of`; with the
entry wide, `WorkerSide.side_entry` puts it in the invariant).

- `segTC_iUnion`: segments from each of a family of preconditions are one
  from their union.
- `wkP`, `wkP_seg`: the union of the preconditions of the segments keeping
  `wakeZX` (from which the worker's states never leave it), its segment.
- `msW_K`: the worker's memory side's kernel model.
- `wakeD`: the worker's side at the instance (`lbl w := w.1.lbl`,
  `ms w := msW hp i T W w.1`, `cw w := w.1.cwW`, `S w := w.1.S`).
- `hW_I`, `hmp_I`: the worker premises `hW` and `hmp` at `wakeD`.
- `childSeg_X`: `seg_childPreNNA'` with its `Z` premises discharged at
  `Z := wakeZX … W …`; `wkP_of`: a segment's precondition's pairs (the
  child's entry, by `childSeg_X` at `p := wakeSrc`, `lbl := w.1.lbl`,
  `ms := msW hp i T W w.1`, `Λw := (RuntimeLayout.ofPlaceWX hp i).Λ`) are
  pairs of `wkP`.

**Unlike AArch64** (forced by the x64 shape):
- The worker owns its TCB self word `⟨W, 8⟩`, so its memory side is
  `msW hp i T W g` (AArch64: `wakeMs hp i g`), `wakeZX` carries `W`, and the
  ghost record's sides take `T W`.
- `ZX.childThrZA_X'` separates the flag's cell and the `unpark` word from
  `W` through the layout, so `childSeg_X` takes the placement (`hpl`, `i`,
  `hA13`), the worker's TCB word `W` the clone's `tcbOf lab q` (`htpW`) and
  `tcb2` (`hW2`; `ZX.tcbOf_tcb2` at the spawn's `tcb2Q`), and, per pair of
  words, the flag's cell in the heap and `me` main's TCB (antecedents
  `hheap`, `hme`; both from the consumer invariant on the spawn's labels at
  the spawn site, `WakeSpawnR`'s twin).
- The child's nodes off the end and the abort stubs (`ZX.childThrZA_X'`'s
  `hE`, `hAb`, `ZX.cZA_X'`'s `hEc`, `hAbc`) come from the listing's node
  checks (`EndOff.thrZ_end`, `cZ_end`, `AbOffW.thrZ_ab`, `cZ_ab`); on
  AArch64 `ZX.childThrZA_X'` proves them itself.
- The x86-64 `seg_childPreNNA'` has no alignment premise (`hal`); the
  thread's region `thrR (childR …)` is re-based by `8`, its bounds from the
  stub's (`thrR_ok`).
-/
import Spike.Lib.X64WakeInst
import Spike.Lib.X64WakeZXA
import Spike.Lib.X64WakeWorkerSide
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeAbOffWN

namespace Spike.Lib.X64WakeWorkerX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep)
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Worker (NNZ NodeZ NodeZA)
open Spike.Lib.X64.Flow.Worker.Wake.ZX (wakeZX)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64WakeInst (Gh msW)
open Spike.Lib.X64WakeW1.WorkerSide (side side_inv)

/-! ## Unions of segments -/

/-- **Segments from a family of preconditions are one from their union**
(the invariant: the union of theirs). -/
theorem segTC_iUnion {S : Frag isa} {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {Q : Frag isa} {κ : Sort _} {P : κ → Frag isa} (h : ∀ j, SegTC S p lbl ms (P j) Q) :
    SegTC S p lbl ms (fun s c => ∃ j, P j s c) Q := by
  refine ⟨fun s c => ∃ j, Classical.choose (h j) s c, fun s c ⟨j, hj⟩ => ⟨j, (Classical.choose_spec (h j)).1 s c hj⟩,
    fun s c ⟨j, hj⟩ => (Classical.choose_spec (h j)).2.1 s c hj, ?_⟩
  rintro s c ⟨j, hj⟩
  exact ((Classical.choose_spec (h j)).2.2 s c hj).mono fun s c h => h.imp_left fun h => ⟨j, h⟩

/-! ## The worker's side at the instance -/

section Side

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) (T W : BitVec 64)
  (ok : Gh → Prop) (exe : _root_.Executable) (endPc : Int64) (kp : Nat)
  (lbl' : WeakMem.AllocLabel → Option Nat) (cSf : WeakMem.Address)

/-- **The worker's pairs**: those of the precondition of some segment
keeping `wakeZX` (at the instance's layout, labels `lbl'`, flag `cSf`, the
worker's TCB word `W`) under the record's placement and the worker's memory
side, to the empty fragment. -/
def wkP (w : {g : Gh // ok g}) : Frag isa := fun s c =>
  ∃ Pj : Frag isa, SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf W exe kp)) wakeSrc
    w.1.lbl (msW hp i T W w.1) Pj (fun _ _ => False) ∧ Pj s c

/-- **A segment's precondition's pairs are the worker's.** -/
theorem wkP_of {w : {g : Gh // ok g}} {Pj : Frag isa}
    (h : SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf W exe kp)) wakeSrc w.1.lbl
      (msW hp i T W w.1) Pj (fun _ _ => False)) {s : State} {c : Ctl} (hP : Pj s c) :
    wkP hp i T W ok exe endPc kp lbl' cSf w s c :=
  ⟨Pj, h, hP⟩

/-- `wkP`'s segment. -/
theorem wkP_seg (w : {g : Gh // ok g}) :
    SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf W exe kp)) wakeSrc w.1.lbl
      (msW hp i T W w.1) (wkP hp i T W ok exe endPc kp lbl' cSf w) (fun _ _ => False) :=
  (segTC_iUnion (κ := {Pj : Frag isa // SegTC (NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf
      W exe kp)) wakeSrc w.1.lbl (msW hp i T W w.1) Pj (fun _ _ => False)}) fun j => j.2).mono_pre
    fun _ _ ⟨Pj, h, hP⟩ => ⟨⟨Pj, h⟩, hP⟩

/-- `msW`'s kernel model. -/
theorem msW_K (g : Gh) : (msW hp i T W g).K = some Scc.Sem.X64.abi := rfl

/-- **The worker's side at the instance**: `WorkerSide.side` of `wkP_seg`,
the record's placement, the worker's memory side, pointer word and spawn
size. -/
noncomputable def wakeD : X64WakeW1.WSide {g : Gh // ok g} :=
  side (fun w => w.1.lbl) (fun w => msW hp i T W w.1) (wkP hp i T W ok exe endPc kp lbl' cSf)
    (fun w => msW_K hp i T W w.1) (wkP_seg hp i T W ok exe endPc kp lbl' cSf) (fun w => w.1.cwW) (fun w => w.1.S)

/-- **The worker premise `hW`** at `wakeD`: its invariant lies inside
`NNZ … wakeZX`. -/
theorem hW_I : ∀ w s c, (wakeD hp i T W ok exe endPc kp lbl' cSf).Wi w s c →
    NNZ exe endPc (wakeZX (RuntimeLayout.ofPlaceWX hp i).Λ lbl' cSf W exe kp) s c :=
  fun w s c h => (side_inv w s c h).1

/-- **The worker premise `hmp`** at `wakeD`: `msW`'s runtime accesses are to
words mapped in the loaded kernel state. -/
theorem hmp_I : ∀ w L wr, ((wakeD hp i T W ok exe endPc kp lbl' cSf).ms w).mp L wr →
    Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 (RuntimeLayout.ofPlaceWX hp i).Λ) wr L = true :=
  fun _ _ _ h => h.1.1

end Side

/-! ## The spawned child's segment keeps `wakeZX` -/

section Child

open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.X64
open Spike.Lib.X64.Flow.Worker.Wake
open Spike.Lib.X64.Flow.Worker.Wake.Child
open Spike.Lib.X64.Flow.Worker.Wake.Labels (ThrZA)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerBody workerTy wc1)
open Spike.Lib.X64.WakePh.Child (childN childR cN)
open Spike.Lib.X64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.X64.Flow.Ret0 (stacksA StOk LdOk)
open Spike.Lib.X64.Rt (TcbGG tcbOf)
open Spike.Lib.X64.WakePh (tcb2 tcbM)
open Spike.Lib.X64Consumer (Own)

/-- **`seg_childPreNNA'` at `Z := wakeZX Λw lbl' cSf W exe kp`**, its `ThrZA`
and stub premises discharged (`ZX.childThrZA_X'`, `ZX.cZA_X'`): for each
pair of words, given `seg_childPreNNA'`'s premises, `w1` the flag's
locative `cSf` (`hw`), the words' `ValRep` under `lbl'` (`hv1'`, `hv2'`),
the flag's cell in the heap (`hheap`) and `me` main's TCB (`hme`), the
child's segment to the empty fragment (the nodes off the end and the abort
stubs by `EndOff.thrZ_end`/`cZ_end`, `AbOffW.thrZ_ab`/`cZ_ab`); `W` is the clone's TCB (`htpW`) and `tcb2` (`hW2`). -/
theorem childSeg_X {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hpl : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (hA13 : Scc.Cert.Spawn.X64.a13data (RuntimeLayout.ofPlaceWX hpl i).Λ o.prog o.secs = true)
    {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address} {W : BitVec 64}
    {r0 r1 : Range} {X : State → Prop} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {lab : Label → Int64} {q : TcbGG} {ms0 : MemSide isa}
    (hPC : ∀ st, X st → PreChild ms0 own lab q st)
    (hrt0 : ∀ a, ms0.rt a → ms.rt a) (hmp0 : ∀ L, ms0.mp L false → ms.mp L false)
    (hG0 : ∀ L v, ms.G L v → ms0.G L v)
    (hr1 : r1 = r1Of lab) (hbd : (stacksA lab).toNat + 32768 < 2 ^ 64)
    (htls : (tcbOf lab q).toNat + 16 ≤ 2 ^ 64)
    (hout : (tcbOf lab q).toNat + 16 ≤ (stacksA lab).toNat + 16384 ∨
      (stacksA lab).toNat + 32768 ≤ (tcbOf lab q).toNat + 8)
    (hK : ms.K = some Scc.Sem.X64.abi)
    (hpw : ∃ d, p.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧ d.argTy = workerTy)
    (htpW : BitVec.ofNat 64 (tcbOf lab q).toNat = W) (hW2 : W = tcb2 (RuntimeLayout.ofPlaceWX hpl i))
    (T : Ty) :
    ∃ (th : Thread isa) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.get64 .r12).toNat = cA ∧ (th.st.st.1.regs.get64 .rbx).toNat = meW ∧
      callOf abi th = some (.clone (r1.lo + r1.size) (tcbOf lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR (r1.lo + r1.size) (-16384))
          (DFrame (childR (r1.lo + r1.size) (-16384))
            (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
          (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) W (BitVec.ofNat 64 (r1.lo + r1.size)))
          (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          cA + 8 ≤ 2 ^ 64 → (cA + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ cA) →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          LdOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1) W →
          OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x0") W W →
          StOk ms (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (W + 24#64) 1#64 →
          w1.val = .loc cSf 0 → ValRep lbl' w1.val cA → ValRep lbl' w2.val meW →
          (RuntimeLayout.ofPlaceWX hpl i).Λ.heap.contains cA →
          BitVec.ofNat 64 meW = tcbM (RuntimeLayout.ofPlaceWX hpl i) →
          SegTC (NNZ exe endPc (wakeZX Λw lbl' cSf W exe kp)) p lbl ms (At exe endPc (childR (r1.lo + r1.size) (-16384))
            (DFrame (childR (r1.lo + r1.size) (-16384))
              (childAfter abi t.2 0 th (r1.lo + r1.size) (tcbOf lab q).toNat).st.st.1)
            (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
              (BitVec.ofNat 64 meW) W (BitVec.ofNat 64 (r1.lo + r1.size))))
            (fun _ _ => False)) := by
  subst htpW
  obtain ⟨th, cA, meW, hcA, hmW, hth, h12, hbx, hcall, hk⟩ :=
    seg_childPreNNA'M (Z := wakeZX Λw lbl' cSf (BitVec.ofNat 64 (tcbOf lab q).toNat) exe kp)
      (Q := fun _ _ => False) hp hend h hX hPC hrt0 hmp0 hG0 hr1 hbd htls hout hK hpw T
  have hr1e : r1Of lab = ⟨(stacksA lab).toNat + 16384, 16384⟩ := by
    have hlo1 : (r1Of lab).lo = (stacksA lab).toNat + 16384 := by
      show (stacksA lab + 16384#64).toNat = _
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
    rw [show r1Of lab = ⟨(r1Of lab).lo, 16384⟩ from rfl, hlo1]
  obtain ⟨-, -, -, hR, hlo', hhi'⟩ := Spike.Lib.X64.Rt.childStub_region_stk hr1e hbd
  subst hr1
  refine ⟨th, cA, meW, hcA, hmW, hth, h12, hbx, hcall, fun w1 w2 => ⟨(hk w1 w2).1,
    fun hv1 htag hv2 hc8 hcout hS htp4 hT hown hSx hw hv1' hv2' hheap hme => (hk w1 w2).2 hv1 htag hv2 hc8
      hcout hS htp4 hT hown hSx
      (ZX.childThrZA_X' hpl i hp hend hA13
        (thrR_ok hR (by show (-16384 : Int) ≤ -8; omega) (by show (-8 : Int) < 0; omega))
        (by show (-16384 : Int) + 8 ≤ -120; omega) (by show (8 : Int) ≤ 0 + 8; omega) hcA hmW hw hv1' hv2'
        hheap hme hW2 (EndOff.thrZ_end hp) (AbOffW.thrZ_ab hp))
      (ZX.cZA_X' hp hend hR hlo' hhi' hcA hmW hv1' hv2' (EndOff.cZ_end hp) (AbOffW.cZ_ab hp))⟩⟩

end Child

/-- info: 'Spike.Lib.X64WakeWorkerX.hW_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms hW_I

/-- info: 'Spike.Lib.X64WakeWorkerX.childSeg_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms childSeg_X

end Spike.Lib.X64WakeWorkerX

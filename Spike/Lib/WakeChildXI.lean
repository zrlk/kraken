/-
**wake.w's spawned child's segment at the instance** (AArch64): `WakeWorkerX.childSeg_X` with its layout premises discharged at
`RuntimeLayout.ofPlaceW hpl i` (`lab := L.lab`, `r1 := r1Of L.lab`,
`p := wakeSrc`, `ms := wakeMs hpl i g`). The listing is wake.w's
certificate (`Spike/Test/Cert/A64WakeCert.s`).

- `hpw_wake`: `wakeSrc`'s `worker` declaration is `workerBody`'s.
- `below32_L`, `notPool`, `shared_lt`, `word_out`: a word the layout shares
  ends below `2 ^ 32` and is off the stack pool.
- `childSeg_XL`: at any runtime layout `L` (well formed, below `2 ^ 32`)
  and memory side whose runtime writes are to shared words: the stack
  bound and alignment from `L`'s first stack and `ClonePre`'s second take
  (in the pool), the TLS bounds from the second TCB's first two words
  (`TcbArea.mp`, shared so off the pool), each pair's flag bounds from the
  flag's word being shared (`hflag`).
- `childSeg_XI`: `childSeg_XL` at `RuntimeLayout.ofPlaceW hpl i`,
  `wakeMs hpl i g`.

Open per pair (main's pre-spawn words): `hS`/`htp4` (main's permit
word `meW + 16`, `StOk` at value 1 and 4-aligned) and `hSx` (the second
TCB's word `tcb + 24`, `StOk` at value 1; its `G` asks the word off
`L.pinA + 16`, `wakeG`'s exception).
-/
import Spike.Lib.WakeWorkerX
import Spike.Lib.WakeQ
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeChildXI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep Range)
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow.Worker
open Spike.Lib.A64.Flow.Worker.Wake
open Spike.Lib.A64.Flow.Worker.Wake.Child
open Spike.Lib.A64.Flow.Worker.Wake.Split (workerTy workerBody)
open Spike.Lib.A64.Flow.Worker.Wake.ZX (wakeZX)
open Spike.Lib.A64.Flow.Ret0 (StOk stacksA)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.WakeInst (Gh wakeMs)
open Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.A64.Rt (TcbGG tcbOf)
open Spike.Lib.A64Consumer (Own)

/-- **`wakeSrc`'s `worker`** is `workerBody` at argument `a : workerTy`
(`seg_childPreNNA`'s `hpw`). -/
theorem hpw_wake : ∃ d, wakeSrc.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧
    d.argTy = workerTy :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## Shared words are off the stack pool -/

section Layout

variable {L : RuntimeLayout} (hwf : L.Λ.WF) (hb : ∀ r ∈ L.Λ.regions, r.lo + r.size ≤ 2 ^ 32)

/-- A placed layout's regions end at or below `2 ^ 32`. -/
theorem below32_L {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpl : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ∀ r ∈ (RuntimeLayout.ofPlaceW hpl i).Λ.regions, r.lo + r.size ≤ 2 ^ 32 :=
  fun r hr => PlaceW.below32_of_placeW hpl r (List.mem_cons_of_mem _ hr)

include hwf in
/-- A shared address is off the stack pool. -/
theorem notPool {x : Nat} (hx : L.Λ.shared x) : ¬ L.Λ.stackPool.contains x := fun hp => by
  have hd := hwf.disjoint
  rcases hx with hx | hx | hx
  · exact hd.2.2.2.2.1.not_both hx hp
  · exact hd.2.2.2.2.2.1.not_both hx hp
  · exact hd.2.2.2.2.2.2.2.2.2.not_both hp hx

include hb in
/-- A shared address is below `2 ^ 32`. -/
theorem shared_lt {x : Nat} (hx : L.Λ.shared x) : x < 2 ^ 32 := by
  rcases hx with hx | hx | hx
  · have := hb L.Λ.data (by simp [Scc.Sem.Layout.regions]); unfold Range.contains at hx; omega
  · have := hb L.Λ.heap (by simp [Scc.Sem.Layout.regions]); unfold Range.contains at hx; omega
  · have := hb L.Λ.pinned (by simp [Scc.Sem.Layout.regions]); unfold Range.contains at hx; omega

include hwf hb in
/-- **A shared word** ends at or below `2 ^ 32` and is off the (nonempty)
stack pool. -/
theorem word_out (hpos : 0 < L.Λ.stackPool.size) {a : BitVec 64}
    (h : Consumer1.LocIn L.Λ.shared ⟨a, 8⟩) :
    a.toNat + 8 ≤ 2 ^ 32 ∧
      (a.toNat + 8 ≤ L.Λ.stackPool.lo ∨ L.Λ.stackPool.lo + L.Λ.stackPool.size ≤ a.toNat) := by
  have hj : ∀ j < 8, L.Λ.shared (a.toNat + j) := fun j hj => h j (by simp [Scc.Sem.Kernel.locBytes]; omega)
  have h7 := shared_lt hb (hj 7 (by omega))
  refine ⟨by omega, ?_⟩
  rcases Nat.lt_or_ge (a.toNat + 7) L.Λ.stackPool.lo with h1 | h1
  · left; omega
  rcases Nat.lt_or_ge a.toNat (L.Λ.stackPool.lo + L.Λ.stackPool.size) with h2 | h2
  · exfalso
    rcases Nat.lt_or_ge a.toNat L.Λ.stackPool.lo with h3 | h3
    · exact notPool hwf (hj (L.Λ.stackPool.lo - a.toNat) (by omega)) (by unfold Range.contains; omega)
    · exact notPool hwf (hj 0 (by omega)) (by unfold Range.contains; omega)
  · right; exact h2

end Layout

/-! ## The child's segment -/

/-- **`childSeg_X` at a runtime layout `L`**, `lab := L.lab`,
`r1 := r1Of L.lab`, `p := wakeSrc`, its layout premises discharged: the
stack's from `L`'s first stack and the second take in the pool
(`ClonePre`), the TLS's from the second TCB's first two words (shared,
`hmpS`), each pair's flag's from the flag's word shared (`hflag`). -/
theorem childSeg_XL {L : RuntimeLayout} (hwf : L.Λ.WF) (hb : ∀ r ∈ L.Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} (hK : ms.K = some Scc.Sem.A64.abi)
    (hmpS : ∀ l, ms.mp l true → Consumer1.LocIn L.Λ.shared l)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    {r0 : Range} {X : State → Prop} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfxM L.Λ r0 (r1Of L.lab) X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {q : TcbGG} (hPC : ∀ st, X st → PreChild ms own L.lab q st)
    (hflag : ∀ x, Scc.Sem.wordAddr lbl cSf = some x → Consumer1.LocIn L.Λ.shared (Scc.Sem.wordLoc x))
    (T : Ty) :
    ∃ (th : Thread isaLSE2) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.getXReg .X9).toNat = cA ∧ (th.st.st.1.regs.getXReg .X10).toNat = meW ∧
      callOf abi th = some (.clone ((r1Of L.lab).lo + (r1Of L.lab).size) (tcbOf L.lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR ((r1Of L.lab).lo + (r1Of L.lab).size) (-16384))
          (DFrame (childR ((r1Of L.lab).lo + (r1Of L.lab).size) (-16384))
            (childAfter abi t.2 0 th ((r1Of L.lab).lo + (r1Of L.lab).size) (tcbOf L.lab q).toNat).st.st.1)
          (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf L.lab q).toNat)
            (BitVec.ofNat 64 ((r1Of L.lab).lo + (r1Of L.lab).size)))
          (childAfter abi t.2 0 th ((r1Of L.lab).lo + (r1Of L.lab).size) (tcbOf L.lab q).toNat).st
          (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          StOk ms (DFrame (childR ((r1Of L.lab).lo + (r1Of L.lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of L.lab).lo + (r1Of L.lab).size) (tcbOf L.lab q).toNat).st.st.1)
            exe endPc (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          StOk ms (DFrame (childR ((r1Of L.lab).lo + (r1Of L.lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of L.lab).lo + (r1Of L.lab).size) (tcbOf L.lab q).toNat).st.st.1)
            exe endPc (BitVec.ofNat 64 (tcbOf L.lab q).toNat + 24#64) 1#64 →
          w1.val = .loc cSf 0 → ValRep lbl' w1.val cA → ValRep lbl' w2.val meW →
          SegTC (NNZ exe endPc (wakeZX Λw lbl' cSf exe kp)) wakeSrc lbl ms
            (At exe endPc (childR ((r1Of L.lab).lo + (r1Of L.lab).size) (-16384))
              (DFrame (childR ((r1Of L.lab).lo + (r1Of L.lab).size) (-16384))
                (childAfter abi t.2 0 th ((r1Of L.lab).lo + (r1Of L.lab).size) (tcbOf L.lab q).toNat).st.st.1)
              (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
                (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf L.lab q).toNat)
                (BitVec.ofNat 64 ((r1Of L.lab).lo + (r1Of L.lab).size))))
            (fun _ _ => False)) := by
  have h' := h
  obtain ⟨th0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hO1, hXs, -⟩ := h'
  have hA := (hPC _ hXs).2.2.2
  have hpe : L.Λ.stackPool.lo + L.Λ.stackPool.size ≤ 2 ^ 32 := hb L.Λ.stackPool (by simp [Scc.Sem.Layout.regions])
  obtain ⟨hs1, hs2⟩ := L.stacks_sub
  dsimp only at hs1 hs2
  have hls := L.lab_stacks
  have hpos : 0 < L.Λ.stackPool.size := by omega
  have hlo1 : (r1Of L.lab).lo = L.stacksA.toNat + 16384 := by
    show (stacksA L.lab + 16384#64).toNat = _
    rw [hls, BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz1 : (r1Of L.lab).size = 16384 := rfl
  obtain ⟨hr1a, hr1b⟩ := hO1.1
  have hbd : (stacksA L.lab).toNat + 32768 < 2 ^ 64 := by rw [hls]; omega
  have hal : (stacksA L.lab).toNat % 16 = 0 := by rw [hls]; exact L.stacks_al
  have hw0 := hmpS _ (hA.mp (tcbOf L.lab q + BitVec.ofNat 64 (8 * 0)) (by simp [Spike.Lib.A64.Rt.Ti.tiAddrs]))
  have hw1 := hmpS _ (hA.mp (tcbOf L.lab q + BitVec.ofNat 64 (8 * 1)) (by simp [Spike.Lib.A64.Rt.Ti.tiAddrs]))
  rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero] at hw0
  obtain ⟨o0a, -⟩ := word_out hwf hb hpos hw0
  obtain ⟨o1a, o1b⟩ := word_out hwf hb hpos hw1
  have e8 : (tcbOf L.lab q + BitVec.ofNat 64 (8 * 1)).toNat = (tcbOf L.lab q).toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  rw [e8] at o1a o1b
  have htls : (tcbOf L.lab q).toNat + 16 ≤ 2 ^ 64 := by omega
  have hout : (tcbOf L.lab q).toNat + 16 ≤ (stacksA L.lab).toNat + 16384 ∨
      (stacksA L.lab).toNat + 32768 ≤ (tcbOf L.lab q).toNat + 8 := by rw [hls]; omega
  obtain ⟨th, cA, meW, hcA, hmW, hth, h9, h10, hcall, hk⟩ :=
    WakeWorkerX.childSeg_X (Λw := Λw) (lbl' := lbl') (cSf := cSf) hp hend h hX hPC rfl hbd hal htls hout hK
      hpw_wake T
  refine ⟨th, cA, meW, hcA, hmW, hth, h9, h10, hcall, fun w1 w2 => ⟨(hk w1 w2).1,
    fun hv1 htag hv2 hS htp4 hSx hw hv1' hv2' => ?_⟩⟩
  have hv := hv1
  rw [hw] at hv
  obtain ⟨-, x, hx, hcx⟩ := hv
  obtain ⟨c1, c2⟩ := word_out hwf hb hpos (a := BitVec.ofNat 64 x) (hflag x hx)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at c1 c2
  exact (hk w1 w2).2 hv1 htag hv2 (by omega) (by omega) hS htp4 hSx hw hv1' hv2'

/-- **The child's segment at the instance**: `childSeg_XL` at
`L := RuntimeLayout.ofPlaceW hpl i`, `ms := wakeMs hpl i g`,
`lbl := g.lbl`. -/
theorem childSeg_XI {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ0 : Scc.Sem.Layout}
    (hpl : PlaceW pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    (g : Gh)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address}
    {r0 : Range} {X : State → Prop} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfxM (RuntimeLayout.ofPlaceW hpl i).Λ r0
      (r1Of (RuntimeLayout.ofPlaceW hpl i).lab) X g.lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {q : TcbGG} (hPC : ∀ st, X st → PreChild (wakeMs hpl i g) own (RuntimeLayout.ofPlaceW hpl i).lab q st)
    (hflag : ∀ x, Scc.Sem.wordAddr g.lbl cSf = some x →
      Consumer1.LocIn (RuntimeLayout.ofPlaceW hpl i).Λ.shared (Scc.Sem.wordLoc x))
    (T : Ty) :
    ∃ (th : Thread isaLSE2) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.getXReg .X9).toNat = cA ∧ (th.st.st.1.regs.getXReg .X10).toNat = meW ∧
      callOf abi th = some (.clone ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
        (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
            (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
          (DFrame (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
              (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
            (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
              (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)
              (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st.st.1)
          (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat)
            (BitVec.ofNat 64 ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
              (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)))
          (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
            (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st
          (kidC T w1 w2) ∧
        (ValRep g.lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep g.lbl w2.val meW →
          StOk (wakeMs hpl i g) (DFrame (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)
                (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st.st.1)
            exe endPc (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          StOk (wakeMs hpl i g) (DFrame (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)
                (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st.st.1)
            exe endPc (BitVec.ofNat 64 (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat + 24#64) 1#64 →
          w1.val = .loc cSf 0 → ValRep lbl' w1.val cA → ValRep lbl' w2.val meW →
          SegTC (NNZ exe endPc (wakeZX Λw lbl' cSf exe kp)) wakeSrc g.lbl (wakeMs hpl i g)
            (At exe endPc (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
              (DFrame (childR ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size) (-16384))
                (childAfter abi t.2 0 th ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size)
                  (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat).st.st.1)
              (childN pfxM (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
                (BitVec.ofNat 64 meW) (BitVec.ofNat 64 (tcbOf (RuntimeLayout.ofPlaceW hpl i).lab q).toNat)
                (BitVec.ofNat 64 ((r1Of (RuntimeLayout.ofPlaceW hpl i).lab).lo +
                  (r1Of (RuntimeLayout.ofPlaceW hpl i).lab).size))))
            (fun _ _ => False)) :=
  childSeg_XL (WakeQ.hwf_ofPlaceOK hpl i) (below32_L hpl i) (WakeWorkerX.wakeMs_K hpl i g)
    (fun _ hm => (hm.2 rfl).1) hp hend h hX hPC hflag T

/-- info: 'Spike.Lib.WakeChildXI.childSeg_XI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms childSeg_XI

end Spike.Lib.WakeChildXI

/-
**wake.w's spawned child's segment at the x86-64 instance** (in the manner
of `Spike/Lib/WakeChildXI.lean`): `X64WakeWorkerX.childSeg_X` with its layout
premises discharged at `L := RuntimeLayout.ofPlaceWX hpl i`
(`lab := L.lab`, `r1 := r1Of L.lab`, `p := wakeSrc`), at any memory side
whose runtime writes are to shared words (`childSeg_XL`) and at the
worker's `msW hpl i T W g` (`childSeg_XI`).

- `hpw_wake`: `wakeSrc`'s `worker` declaration is `workerBody`'s.
- `below32_L`, `notPool`, `shared_lt`, `word_out`: a word the layout shares
  ends below `2 ^ 32` and is off the stack pool.
- `childSeg_XL`: the stack bound from `L`'s first stack and `ClonePre`'s
  second take (in the pool), the TLS bounds from the second TCB's first two
  words (`TcbArea.mp` at main's memory side `ms0`, shared so off the pool),
  each pair's flag bounds from the flag's word being shared (`hflag`).
- `childSeg_XI`: `childSeg_XL` at the segment's `msW hpl i T W g`, main's
  `PreChild` at `wakeMs hpl i g`.

**Unlike AArch64** (forced by the x64 shape):
- The memory side is the worker's `msW hpl i T W g` (owning `⟨W, 8⟩`;
  AArch64: `wakeMs hpl i g`), and `wakeZX` carries `W`.
- `childSeg_X`'s separation premises stay: `hA13`, `W` the clone's TCB
  (`htpW`) and `tcb2` (`hW2`), and per pair the flag's cell in the heap
  (`hheap`) and `me` main's TCB (`hme`), discharged at the spawn.
- The child's own-word facts at the TCB (`LdOk` at `W`, `OwnAt` at
  `.Lscc_rt_thr_worker.x12`) are per-pair antecedents beside the `StOk`
  ones (the x86-64 child reads its TCB self word).
- There is no alignment premise (`hal`) to discharge.
- `PreChild` (`TcbArea`, which maps the TCB word for a write) is at main's
  base side `wakeMs hpl i g`, not at the segment's `msW` (whose runtime
  writes avoid that word); `msW` keeps `wakeMs`' runtime words, read
  mappings and values (`X64WakeWorkerX.childSeg_X`'s `hrt0`, `hmp0`,
  `hG0`).

Open per pair (main's pre-spawn words): `hS`/`htp4` (main's permit word
`meW + 16`, `StOk` at value 1 and 4-aligned), `hT`/`hown` (the TCB word)
and `hSx` (the second TCB's word `W + 24`, `StOk` at value 1).
-/
import Spike.Lib.X64WakeWorkerX
import Spike.Lib.X64WakeQ
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeChildXI

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem (ValRep Range)
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.Flow.Worker (NNZ)
open Spike.Lib.X64.Flow.Worker.Wake.Child (kidC)
open Spike.Lib.X64.Flow.Worker.Wake.Split (workerTy workerBody)
open Spike.Lib.X64.Flow.Worker.Wake.ZX (wakeZX)
open Spike.Lib.X64.WakePh.Child (childN childR)
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk stacksA)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64WakeInst (Gh wakeMs msW)
open Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.X64
open Spike.Lib.X64.Rt.PreChild (r1Of PreChild)
open Spike.Lib.X64.Rt (TcbGG tcbOf)
open Spike.Lib.X64.WakePh (tcb2 tcbM)
open Spike.Lib.X64Consumer (Own)

/-- **`wakeSrc`'s `worker`** is `workerBody` at argument `a : workerTy`
(`seg_childPreNNA'`'s `hpw`). -/
theorem hpw_wake : ∃ d, wakeSrc.find? (·.name == "worker") = some d ∧ d.body = workerBody ∧ d.arg = "a" ∧
    d.argTy = workerTy :=
  ⟨_, rfl, rfl, rfl, rfl⟩

/-! ## Shared words are off the stack pool -/

section Layout

variable {L : RuntimeLayout} (hwf : L.Λ.WF) (hb : ∀ r ∈ L.Λ.regions, r.lo + r.size ≤ 2 ^ 32)

/-- A placed layout's regions end at or below `2 ^ 32`. -/
theorem below32_L {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
    (hpl : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    ∀ r ∈ (RuntimeLayout.ofPlaceWX hpl i).Λ.regions, r.lo + r.size ≤ 2 ^ 32 :=
  fun r hr => PlaceWX.below32_of_placeWX hpl r (List.mem_cons_of_mem _ hr)

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

section Child

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hpl : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpl i

/-- **`childSeg_X` at `ofPlaceWX`**, `lab := (Ly).lab`, `r1 := r1Of (Ly).lab`,
`p := wakeSrc`, its layout premises discharged: the stack's from the
layout's first stack and the second take in the pool (`ClonePre`), the
TLS's from the second TCB's first two words (shared, `hmpS`), each pair's
flag's from the flag's word shared (`hflag`). -/
theorem childSeg_XL
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} (hK : ms.K = some Scc.Sem.X64.abi)
    {ms0 : MemSide isa} (hmpS : ∀ l, ms0.mp l true → Consumer1.LocIn (Ly).Λ.shared l)
    (hrt0 : ∀ a, ms0.rt a → ms.rt a) (hmp0 : ∀ L, ms0.mp L false → ms.mp L false)
    (hG0 : ∀ L v, ms.G L v → ms0.G L v)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address} {W : BitVec 64}
    {r0 : Range} {X : State → Prop} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre (Ly).Λ r0 (r1Of (Ly).lab) X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {q : TcbGG} (hPC : ∀ st, X st → PreChild ms0 own (Ly).lab q st)
    (hflag : ∀ x, Scc.Sem.wordAddr lbl cSf = some x → Consumer1.LocIn (Ly).Λ.shared (Scc.Sem.wordLoc x))
    (htpW : BitVec.ofNat 64 (tcbOf (Ly).lab q).toNat = W) (hW2 : W = tcb2 (Ly))
    (T : Ty) :
    ∃ (th : Thread isa) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.get64 .r12).toNat = cA ∧ (th.st.st.1.regs.get64 .rbx).toNat = meW ∧
      callOf abi th = some (.clone ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
          (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
            (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat).st.st.1)
          (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) W (BitVec.ofNat 64 ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)))
          (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat).st
          (kidC T w1 w2) ∧
        (ValRep lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep lbl w2.val meW →
          StOk ms (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                (tcbOf (Ly).lab q).toNat).st.st.1)
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          LdOk ms (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                (tcbOf (Ly).lab q).toNat).st.st.1) W →
          OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12") W W →
          StOk ms (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                (tcbOf (Ly).lab q).toNat).st.st.1)
            (W + 24#64) 1#64 →
          w1.val = .loc cSf 0 → ValRep lbl' w1.val cA → ValRep lbl' w2.val meW →
          (Ly).Λ.heap.contains cA → BitVec.ofNat 64 meW = tcbM (Ly) →
          SegTC (NNZ exe endPc (wakeZX Λw lbl' cSf W exe kp)) wakeSrc lbl ms
            (At exe endPc (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
                (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                  (tcbOf (Ly).lab q).toNat).st.st.1)
              (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
                (BitVec.ofNat 64 meW) W (BitVec.ofNat 64 ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size))))
            (fun _ _ => False)) := by
  have hwf : (Ly).Λ.WF := X64WakeQ.hwf_ofPlaceOK hpl i
  have hb := below32_L hpl i
  have h' := h
  obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, hO1, hXs, -⟩ := h'
  have hA := (hPC _ hXs).2.2.2
  have hpe : (Ly).Λ.stackPool.lo + (Ly).Λ.stackPool.size ≤ 2 ^ 32 :=
    hb (Ly).Λ.stackPool (by simp [Scc.Sem.Layout.regions])
  obtain ⟨hs1, hs2⟩ := (Ly).stacks_sub
  dsimp only at hs1 hs2
  have hls := (Ly).lab_stacks
  have hpos : 0 < (Ly).Λ.stackPool.size := by omega
  have hbd : (stacksA (Ly).lab).toNat + 32768 < 2 ^ 64 := by
    rw [congrArg BitVec.toNat hls]; omega
  have hlo1 : (r1Of (Ly).lab).lo = (Ly).stacksA.toNat + 16384 := by
    show (stacksA (Ly).lab + 16384#64).toNat = _
    rw [hls, BitVec.toNat_add, Nat.mod_eq_of_lt (by simp only [BitVec.toNat_ofNat]; omega)]; rfl
  have hsz1 : (r1Of (Ly).lab).size = 16384 := rfl
  obtain ⟨hr1a, hr1b⟩ := hO1.1
  have hw0 := hmpS _ (hA.mp (tcbOf (Ly).lab q + BitVec.ofNat 64 (8 * 0))
    (by simp [Spike.Lib.X64.Rt.Ti.tiAddrs]))
  have hw1 := hmpS _ (hA.mp (tcbOf (Ly).lab q + BitVec.ofNat 64 (8 * 1))
    (by simp [Spike.Lib.X64.Rt.Ti.tiAddrs]))
  rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero] at hw0
  obtain ⟨o0a, -⟩ := word_out hwf hb hpos hw0
  obtain ⟨o1a, o1b⟩ := word_out hwf hb hpos hw1
  have e8 : (tcbOf (Ly).lab q + BitVec.ofNat 64 (8 * 1)).toNat = (tcbOf (Ly).lab q).toNat + 8 := by
    rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega
  have hls' : (stacksA (Ly).lab).toNat = (Ly).stacksA.toNat := congrArg BitVec.toNat hls
  have htls : (tcbOf (Ly).lab q).toNat + 16 ≤ 2 ^ 64 := by omega
  have hout : (tcbOf (Ly).lab q).toNat + 16 ≤ (stacksA (Ly).lab).toNat + 16384 ∨
      (stacksA (Ly).lab).toNat + 32768 ≤ (tcbOf (Ly).lab q).toNat + 8 := by omega
  obtain ⟨th, cA, meW, hcA, hmW, hth, h12, hbx, hcall, hk⟩ :=
    X64WakeWorkerX.childSeg_X (Λw := Λw) (lbl' := lbl') (cSf := cSf) hpl i hA13 hp hend h hX hPC hrt0 hmp0 hG0 rfl
      hbd htls hout hK hpw_wake htpW hW2 T
  refine ⟨th, cA, meW, hcA, hmW, hth, h12, hbx, hcall, fun w1 w2 => ⟨(hk w1 w2).1,
    fun hv1 htag hv2 hS htp4 hT hown hSx hw hv1' hv2' hheap hme => ?_⟩⟩
  have hv := hv1
  rw [hw] at hv
  obtain ⟨-, x, hx, hcx⟩ := hv
  obtain ⟨c1, c2⟩ := word_out hwf hb hpos (a := BitVec.ofNat 64 x) (hflag x hx)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at c1 c2
  exact (hk w1 w2).2 hv1 htag hv2 (by omega) (by omega) hS htp4 hT hown hSx hw hv1' hv2' hheap hme

/-- **The child's segment at the instance**: `childSeg_XL` at the worker's
memory side `msW hpl i T' W g`, `lbl := g.lbl`. -/
theorem childSeg_XI (T' : BitVec 64) (g : Gh)
    (hA13 : Scc.Cert.Spawn.X64.a13data (Ly).Λ o.prog o.secs = true)
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λw : Scc.Sem.Layout} {lbl' : WeakMem.AllocLabel → Option Nat} {cSf : WeakMem.Address} {W : BitVec 64}
    {r0 : Range} {X : State → Prop} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre (Ly).Λ r0 (r1Of (Ly).lab) X g.lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    {own : Own} {q : TcbGG} (hPC : ∀ st, X st → PreChild (wakeMs hpl i g) own (Ly).lab q st)
    (hflag : ∀ x, Scc.Sem.wordAddr g.lbl cSf = some x → Consumer1.LocIn (Ly).Λ.shared (Scc.Sem.wordLoc x))
    (htpW : BitVec.ofNat 64 (tcbOf (Ly).lab q).toNat = W) (hW2 : W = tcb2 (Ly))
    (T : Ty) :
    ∃ (th : Thread isa) (cA meW : Nat), cA < 2 ^ 64 ∧ meW < 2 ^ 64 ∧ t.1.threads = #[th] ∧
      (th.st.st.1.regs.get64 .r12).toNat = cA ∧ (th.st.st.1.regs.get64 .rbx).toNat = meW ∧
      callOf abi th = some (.clone ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat) ∧
      ∀ w1 w2 : TermRun.Word,
        At exe endPc (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
          (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
            (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat).st.st.1)
          (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
            (BitVec.ofNat 64 meW) W (BitVec.ofNat 64 ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)))
          (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (tcbOf (Ly).lab q).toNat).st
          (kidC T w1 w2) ∧
        (ValRep g.lbl w1.val cA → (∃ sa, w1.val = .loc sa 0) → ValRep g.lbl w2.val meW →
          StOk (msW hpl i T' W g) (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                (tcbOf (Ly).lab q).toNat).st.st.1)
            (BitVec.ofNat 64 meW + 16#64) 1#64 →
          (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 →
          LdOk (msW hpl i T' W g) (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                (tcbOf (Ly).lab q).toNat).st.st.1) W →
          OwnAt (msW hpl i T' W g) exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_thr_worker.x12") W W →
          StOk (msW hpl i T' W g) (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                (tcbOf (Ly).lab q).toNat).st.st.1)
            (W + 24#64) 1#64 →
          w1.val = .loc cSf 0 → ValRep lbl' w1.val cA → ValRep lbl' w2.val meW →
          (Ly).Λ.heap.contains cA → BitVec.ofNat 64 meW = tcbM (Ly) →
          SegTC (NNZ exe endPc (wakeZX Λw lbl' cSf W exe kp)) wakeSrc g.lbl (msW hpl i T' W g)
            (At exe endPc (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
              (DFrame (childR ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size) (-16384))
                (childAfter abi t.2 0 th ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size)
                  (tcbOf (Ly).lab q).toNat).st.st.1)
              (childN (_root_.Executable.labels exe).label (kidC T w1 w2) (BitVec.ofNat 64 cA)
                (BitVec.ofNat 64 meW) W (BitVec.ofNat 64 ((r1Of (Ly).lab).lo + (r1Of (Ly).lab).size))))
            (fun _ _ => False)) :=
  childSeg_XL hpl i hA13 (ms := msW hpl i T' W g) (ms0 := wakeMs hpl i g)
    (X64WakeWorkerX.msW_K hpl i T' W g) (fun _ hm => (hm.2 rfl).1) (fun _ h => h)
    (fun _ h => ⟨h, nofun⟩) (fun _ _ h => h) hp hend h hX hPC hflag htpW hW2 T

end Child

/-- info: 'Spike.Lib.X64WakeChildXI.childSeg_XI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms childSeg_XI

end Spike.Lib.X64WakeChildXI

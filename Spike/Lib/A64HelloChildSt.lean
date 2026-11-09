/-
**hello.w's spawned child: its runtime stores and the packet's cell** (AArch64, `Hello.SegR.ChildPrem`'s
`hS`, `htp4`, `hSx`, `hdm`; the twin of `Spike.Lib.WakeChildSt` at hello's memory side `HelloMs.helloMs`,
any value invariant `G`, and the child's frame on the stub's region `childR top lo`, `-lo ≤ r1.size`).

- `unmapped_child`: a word off the handed range `r1` is unmapped in the child's first memory.
- `stOk_pinnedH`: a word whose 8 bytes lie in `pinned` is a runtime store under `helloMs` in the child's
  frame, given `G` at the word and value (as `WakeChildSt.stOk_pinned`).
- `childSt_IH`: main's permit word `pinA + 24` and the second TCB's word `pinA + 128` take the store of `1`
  (`hpin2`: the pinned region reaches `pinA + 200`; `hG`: `G` allows `1` there).
- `StOk.withBW`: a runtime store's facts do not read the byte or abort rows, so they hold at
  `ms.withBW bo we` (hello's `helloMsW`, the child segment's memory side).
- `hdm_placed`: a word inside a placed label (`MemRelP`'s placement: `.data` or the heap) is unmapped in
  the child's first memory.
-/
import Spike.Lib.WakeChildSt
import Spike.Lib.HelloMs
import Spike.Lib.MemSideBW

namespace Spike.Lib.HelloChildSt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP lrange Range)
open Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (DFrame)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.HelloMs (helloMs)

/-- **A word off the handed range is unmapped in the child's first memory** (on the stub's region below
`r1`'s top, inside `r1`). -/
theorem unmapped_child {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (htop : r1.lo + r1.size < 2 ^ 64)
    (hlo : -lo ≤ r1.size) {a : BitVec 64} (ha8 : a.toNat + 8 ≤ 2 ^ 64)
    (hoff : a.toNat + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ a.toNat) :
    ∀ m, DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1 m →
      Mem.loadInt m.dmem a 8 = none := by
  intro m hF
  have hb : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  rw [hF a (by omega) (by simp only [childR, hb]; omega), Spike.Lib.A64.Rt.childAfter_dmem hh]
  exact Spike.Lib.A64.Rt.loadInt_copyRange_none (by omega) (by simp only [Range.contains]; omega) (by decide)

/-- **A runtime store's facts at `ms.withBW bo we`** (they read `rt`, `mp`, `G` only). -/
theorem StOk.withBW {ms : MemSide isaLSE2} {F : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {a v : BitVec 64} (h : StOk ms F exe endPc a v)
    (bo : isaLSE2.State → Nat → Spike.Lib.Ctl → (Spike.Lib.Ctl → Prop) → Prop) (we : isaLSE2.State → Spike.Lib.Ctl → Prop) : StOk (ms.withBW bo we) F exe endPc a v :=
  ⟨h.rt, h.mp, h.G, h.unmapped⟩

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

/-- **A word in `pinned` is a runtime store in the child's frame** under `helloMs` (the child after a
`clone` that handed `r1`, in the stack pool), given `G` at the word and value. -/
theorem stOk_pinnedH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hpl i).Λ lbl lsize ts tm sm tp tq sp)
    {a v : BitVec 64} (ha : ∀ k < 8, (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.contains (a.toNat + k))
    (hG : G ⟨a, 8⟩ (v.setWidth 128))
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (RuntimeLayout.ofPlaceW hpl i).Λ.stackPool) (hlo : -lo ≤ r1.size)
    {exe : _root_.Executable} {endPc : Int64} :
    StOk (helloMs (RuntimeLayout.ofPlaceW hpl i) G lbl lsize) (DFrame (childR (r1.lo + r1.size) lo)
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) exe endPc a v := by
  have hwf := Spike.Lib.WakeQ.hwf_ofPlaceOK hpl i
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, hsp⟩ := hwf.disjoint
  have hpin := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hpl i).Λ.pinned ∈ (RuntimeLayout.ofPlaceW hpl i).Λ.regions)
  have hpf := (RuntimeLayout.ofPlaceW hpl i).pool_fit
  have h0 := ha 0 (by decide)
  have h7 := ha 7 (by decide)
  simp only [Range.contains, Range.Disjoint, Range.Sub, Range.InSpace] at h0 h7 hdp hhp hsp hpin hsub
  -- off every placed label (they lie in `.data` or the heap)
  have hoff : ∀ k < 8, ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains (a.toNat + k) := by
    rintro k hk ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
    have hk' := ha k hk
    simp only [Range.contains] at hs hk'
    omega
  refine ⟨fun ⟨l, b, hl, hx⟩ => hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩,
    ⟨WakeChildSt.stOk_pinned.mapped_K0_pinned hpl i ha, fun _ => ⟨fun k hk => ?_, ?_⟩⟩, hG,
    unmapped_child hh (by omega) hlo (by omega) (by omega)⟩
  · exact .inr (.inr (ha k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))
  · rintro ⟨l, b, hl, hx⟩
    exact hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩

/-- **`hS`/`hSx` at the instance**: main's permit word `pinA + 24` and the second TCB's word `pinA + 128`
take the store of `1` in the child's frame, given the pinned region through `pinA + 200` (`hpin2`) and `G`
allowing `1` at the word (`hG`). -/
theorem childSt_IH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hpl i).Λ lbl lsize ts tm sm tp tq sp)
    (hpin2 : (RuntimeLayout.ofPlaceW hpl i).pinA.toNat + 200 ≤
      (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.size)
    {a : BitVec 64} (ha : a = (RuntimeLayout.ofPlaceW hpl i).pinA + 24#64 ∨
      a = (RuntimeLayout.ofPlaceW hpl i).pinA + 160#64)
    (hG : G ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128))
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (RuntimeLayout.ofPlaceW hpl i).Λ.stackPool) (hlo : -lo ≤ r1.size)
    {exe : _root_.Executable} {endPc : Int64} :
    StOk (helloMs (RuntimeLayout.ofPlaceW hpl i) G lbl lsize) (DFrame (childR (r1.lo + r1.size) lo)
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) exe endPc a 1#64 := by
  have hlo' := WakeChildSt.pinned_lo_le hpl i
  rcases ha with rfl | rfl
  · refine stOk_pinnedH hpl i hm (fun k hk => ?_) hG hh hsub hlo
    have := WakeChildSt.tcb_pinned hpl i (j := 3) (by decide) (by decide) k hk
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, WakeChildSt.pinA_add hpl i (by decide)]
    exact this
  · refine stOk_pinnedH hpl i hm (fun k hk => ?_) hG hh hsub hlo
    rw [show (160#64 : BitVec 64) = BitVec.ofNat 64 160 from rfl, WakeChildSt.pinA_add hpl i (by decide)]
    simp only [Range.contains]; omega

/-- **`hdm` at a placed word**: a word whose 8 bytes lie in a placed label (in `.data` or the heap,
`MemRelP`) is unmapped in the child's first memory (the handed range is in the stack pool). -/
theorem hdm_placed {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hpl i).Λ lbl lsize ts tm sm tp tq sp)
    {a : BitVec 64} {l : WeakMem.AllocLabel} {b : Nat} (hl : lbl l = some b)
    (hin : ∀ k < 8, (lrange lsize l b).contains (a.toNat + k))
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (RuntimeLayout.ofPlaceW hpl i).Λ.stackPool) (hlo : -lo ≤ r1.size) (hsz0 : 0 < r1.size) :
    ∀ m, DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1 m →
      Mem.loadInt m.dmem a 8 = none := by
  have hwf := Spike.Lib.WakeQ.hwf_ofPlaceOK hpl i
  obtain ⟨-, -, -, -, hdp, hhp, -, -, -, -⟩ := hwf.disjoint
  have hpf := (RuntimeLayout.ofPlaceW hpl i).pool_fit
  have hd := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hpl i).Λ.data ∈ (RuntimeLayout.ofPlaceW hpl i).Λ.regions)
  have hhe := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] :
    (RuntimeLayout.ofPlaceW hpl i).Λ.heap ∈ (RuntimeLayout.ofPlaceW hpl i).Λ.regions)
  have hk : ∀ k < 8, (RuntimeLayout.ofPlaceW hpl i).Λ.heap.contains (a.toNat + k) ∨
      (RuntimeLayout.ofPlaceW hpl i).Λ.data.contains (a.toNat + k) := fun k hk' =>
    Spike.Lib.WakeGOf.heapData_of_placed hm hl (hin k hk')
  have h0 := hk 0 (by decide)
  have h7 := hk 7 (by decide)
  simp only [Range.contains, Range.Disjoint, Range.Sub, Range.InSpace] at h0 h7 hdp hhp hsub hd hhe
  -- the 8 bytes are all in the heap or `.data`, so none is in the pool, which holds `r1`
  have hno : ∀ k < 8, ¬ (r1.lo ≤ a.toNat + k ∧ a.toNat + k < r1.lo + r1.size) := by
    intro k hk' hk2
    have := hk k hk'
    simp only [Range.contains] at this
    omega
  refine unmapped_child hh (by omega) hlo (by omega) ?_
  by_cases h1 : a.toNat + 8 ≤ r1.lo
  · exact .inl h1
  by_cases h2 : r1.lo + r1.size ≤ a.toNat
  · exact .inr h2
  exfalso
  by_cases hlt : a.toNat < r1.lo
  · exact hno (r1.lo - a.toNat) (by omega) ⟨by omega, by omega⟩
  · exact hno 0 (by decide) ⟨by omega, by omega⟩

end Place

end Spike.Lib.HelloChildSt

/-- info: 'Spike.Lib.HelloChildSt.unmapped_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildSt.unmapped_child

/-- info: 'Spike.Lib.HelloChildSt.childSt_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildSt.childSt_IH

/-- info: 'Spike.Lib.HelloChildSt.hdm_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildSt.hdm_placed

/-- info: 'Spike.Lib.HelloChildSt.StOk.withBW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildSt.StOk.withBW

/-- info: 'Spike.Lib.HelloChildSt.stOk_pinnedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildSt.stOk_pinnedH

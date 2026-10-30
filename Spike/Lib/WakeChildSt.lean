/-
**The child's runtime stores into the pinned region** (AArch64): the per-pair `StOk` premises `hS`/`htp4`/`hSx` of
`WakeChildXI.childSeg_XI` (and `WakeSpawnW.spawn_workerPost`'s `hSt`) at
the instance (`L := RuntimeLayout.ofPlaceW hpl i`, `ms := wakeMs hpl i g`),
under the frame of the child's first memory after the `clone` that handed
`r1` (`r1` in the stack pool). The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `pinned_lo_le`: the pinned region starts at or below `pinA + 48` (the
  first TCB's word `6` is clear of `.data`, A8's `rtOffOk`, and its bytes are
  in `.data` or `pinned`).
- `stOk_pinned`: a word whose 8 bytes lie in `pinned` is a runtime store
  under `wakeMs` in the child's frame, given the value invariant there (off
  every placed label, which lie in `.data`/heap; mapped in `K0`, shared;
  off the child's handed range, which lies in the pool).
- `childSt_I`: at main's permit word `pinA + 24` (`meW + 16`, `meW` the
  first TCB `pinA + 8`) and the second TCB's word `pinA + 128`
  (`tcb2 + 24`, `tcb2 = pinA + 104`: the header `8390915` has `mOf = 2`),
  value `1`; the value invariant off the limit words (`gOf_ne`, or `WakeGOf2.gOf2_ne` once `wakeG'` is at `GOf2`).
- `childSt_al`: `pinA + 24` is 4-aligned (`htp4`).

Open (premises): `hpin2` (the pinned region reaches `pinA + 168`, through the tid word `tcb2 + 56`).
-/
import Spike.Lib.WakeInst
import Spike.Lib.WakeQ
import Spike.Lib.WakeGOf
import Spike.Lib.Rt.A64RtChildPrem
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeChildSt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP lrange Range)
open Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (DFrame)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.WakeInst (Gh wakeMs)
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- `pinA` lies below `2 ^ 32`. -/
theorem pinA_small : (RuntimeLayout.ofPlaceW hpl i).pinA.toNat < 2 ^ 32 :=
  (RuntimeLayout.ofPlaceW hpl i).words_small _ (RuntimeLayout.ofPlaceW hpl i).pin_mem

/-- `pinA + c` for a small `c` does not wrap. -/
theorem pinA_add {c : Nat} (hc : c < 2 ^ 32) :
    ((RuntimeLayout.ofPlaceW hpl i).pinA + BitVec.ofNat 64 c).toNat = (RuntimeLayout.ofPlaceW hpl i).pinA.toNat + c := by
  have := pinA_small hpl i
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- **A word of the first TCB clear of `.data` has its bytes in `pinned`.** -/
theorem tcb_pinned {j : Nat} (hj : j < 7) (hj0 : 0 < j) :
    ∀ k < 8, (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.contains
      ((RuntimeLayout.ofPlaceW hpl i).pinA.toNat + 8 * j + k) := by
  intro k hk
  have hc := Scc.Cert.Rt.A64.clear_of_rtOffOk (PlaceW.rtOff_of_placeW hpl) (j := j) hj
  change Scc.Cert.Rt.A64.clearB (RuntimeLayout.ofPlaceW hpl i).Λ.data
      ((RuntimeLayout.ofPlaceW hpl i).pinA + BitVec.ofNat 64 (8 * j)) = true ∧ _ at hc
  have hm := (RuntimeLayout.ofPlaceW hpl i).words_mapped _
    ((RuntimeLayout.ofPlaceW hpl i).fld_mem (i := j - 1) (by omega))
  rw [show j - 1 + 1 = j by omega] at hm
  have hb := hm.2.2 k hk
  rw [pinA_add hpl i (by omega)] at hb
  simp only [Scc.Cert.Rt.A64.clearB, Bool.or_eq_true, decide_eq_true_eq, pinA_add hpl i (by omega : 8 * j < 2 ^ 32)]
    at hc
  rcases hb with hb | hb
  · simp only [Range.contains] at hb; omega
  · exact hb

/-- **The pinned region starts at or below `pinA + 48`.** -/
theorem pinned_lo_le :
    (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.lo ≤ (RuntimeLayout.ofPlaceW hpl i).pinA.toNat + 48 :=
  (tcb_pinned hpl i (j := 6) (by decide) (by decide) 0 (by decide)).1

/-- **A word in `pinned` is a runtime store in the child's frame**: under
`wakeMs`, for the child after a `clone` that handed `r1` (in the stack
pool), given the value invariant at the word. -/
theorem stOk_pinned (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hpl i).Λ g.lbl g.lsize ts tm sm tp tq sp)
    {a v : BitVec 64} (ha : ∀ k < 8, (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.contains (a.toNat + k))
    (hG : (wakeMs hpl i g).G ⟨a, 8⟩ (v.setWidth 128))
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range} {tls : Nat}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (RuntimeLayout.ofPlaceW hpl i).Λ.stackPool) (hsz : r1.size = 16384)
    {exe : _root_.Executable} {endPc : Int64} :
    StOk (wakeMs hpl i g) (DFrame (childR (r1.lo + r1.size) (-16384))
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
  have hoff : ∀ k < 8, ¬ ∃ l b, g.lbl l = some b ∧ (lrange g.lsize l b).contains (a.toNat + k) := by
    rintro k hk ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.WakeGOf.heapData_of_placed hm hl hx
    have hk' := ha k hk
    simp only [Range.contains] at hs hk'
    omega
  refine ⟨fun ⟨l, b, hl, hx⟩ => hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩, ⟨mapped_K0_pinned ha, fun _ => ⟨fun k hk => ?_, ?_⟩⟩, hG, ?_⟩
  · exact .inr (.inr (ha k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))
  · rintro ⟨l, b, hl, hx⟩
    exact hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩
  · intro m hF
    have htop : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hF a (by omega) (by simp only [childR, htop]; omega), Spike.Lib.A64.Rt.childAfter_dmem hh]
    exact Spike.Lib.A64.Rt.loadInt_copyRange_none (by omega) (by simp only [Range.contains]; omega) (by decide)
where
  mapped_K0_pinned {a : BitVec 64} (ha : ∀ k < 8, (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.contains (a.toNat + k)) :
      Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 (RuntimeLayout.ofPlaceW hpl i).Λ) true ⟨a, 8⟩ = true :=
    Spike.Lib.A64Consumer.mapped_K0_of_mem fun k hk => .inr (ha k hk)

/-- **`hS`/`hSx` at the instance**: main's permit word `pinA + 24` and the
second TCB's word `pinA + 128` take the store of `1` in the child's frame. -/
theorem childSt_I (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (RuntimeLayout.ofPlaceW hpl i).Λ g.lbl g.lsize ts tm sm tp tq sp)
    (hpin2 : (RuntimeLayout.ofPlaceW hpl i).pinA.toNat + 168 ≤
      (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.lo + (RuntimeLayout.ofPlaceW hpl i).Λ.pinned.size)
    {a : BitVec 64} (ha : a = (RuntimeLayout.ofPlaceW hpl i).pinA + 24#64 ∨
      a = (RuntimeLayout.ofPlaceW hpl i).pinA + 128#64)
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range} {tls : Nat}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (RuntimeLayout.ofPlaceW hpl i).Λ.stackPool) (hsz : r1.size = 16384)
    {exe : _root_.Executable} {endPc : Int64} :
    StOk (wakeMs hpl i g) (DFrame (childR (r1.lo + r1.size) (-16384))
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) exe endPc a 1#64 := by
  have hlo := pinned_lo_le hpl i
  rcases ha with rfl | rfl
  · refine stOk_pinned hpl i g hm (fun k hk => ?_) (.inr ?_) hh hsub hsz
    · have := tcb_pinned hpl i (j := 3) (by decide) (by decide) k hk
      rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pinA_add hpl i (by decide)]
      exact this
    · first
        | exact Spike.Lib.A64.PhRec.gOf_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) _
        | exact Spike.Lib.WakeGOf2.gOf2_ne (Spike.Lib.A64.PhRec.pin_ne (by decide))
            (Spike.Lib.WakeGOf2.pin_ne2 (by decide)) _
  · refine stOk_pinned hpl i g hm (fun k hk => ?_) (.inr ?_) hh hsub hsz
    · rw [show (128#64 : BitVec 64) = BitVec.ofNat 64 128 from rfl, pinA_add hpl i (by decide)]
      simp only [Range.contains]; omega
    · first
        | exact Spike.Lib.A64.PhRec.gOf_ne (Spike.Lib.A64.PhRec.pin_ne (by decide)) _
        | exact Spike.Lib.WakeGOf2.gOf2_ne (Spike.Lib.A64.PhRec.pin_ne (by decide))
            (Spike.Lib.WakeGOf2.pin_ne2 (by decide)) _

/-- **`htp4` at the instance**: main's permit word is 4-aligned. -/
theorem childSt_al : ((RuntimeLayout.ofPlaceW hpl i).pinA + 24#64).toNat % 4 = 0 := by
  have hw := Scc.Cert.Rt.A64.wordsOk_of_rtWordsOk (PlaceW.rtWordsOk_link_of_placeW i hpl)
  have h8 := Scc.Cert.Rt.A64.words_al_of_wordsOk hw _ (RuntimeLayout.ofPlaceW hpl i).pin_mem
  change (RuntimeLayout.ofPlaceW hpl i).pinA.toNat % 8 = 0 at h8
  rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pinA_add hpl i (by decide)]
  omega

end Place

/-- info: 'Spike.Lib.WakeChildSt.childSt_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSt_I

/-- info: 'Spike.Lib.WakeChildSt.childSt_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSt_al

end Spike.Lib.WakeChildSt

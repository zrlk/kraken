/-
**The child's runtime accesses to the pinned region on x86-64** (in the
manner of `Spike/Lib/WakeChildSt.lean`): the per-pair premises `hS`/`htp4`,
`hT`/`hown` and `hSx` of `X64WakeChildXI.childSeg_XI` at the instance
(`L := RuntimeLayout.ofPlaceWX hpl i`, the worker's `msW hpl i T W g` with
`T` main's TCB `tcbM L = pinA + 8` and `W` the worker's `tcb2 L =
pinA + 136`), under the frame of the child's first memory after the
`clone` that handed `r1` (`r1` in the stack pool).

- `pinA_small`, `pinA_add`: `pinA` lies below `2 ^ 32`; `pinA + c` for a
  small `c` does not wrap.
- `pin_pinned`: a word `pinA + c` with `c + 8 ≤ 200` has its bytes in
  `pinned`, given that the region reaches `pinA + 200` (`hpin2`).
- `stOk_pinned`, `ldOk_pinned`: a word whose 8 bytes lie in `pinned` and
  off both TCB self words is a runtime store (given the value invariant)
  and load under `msW` in the child's frame (off every placed label, which
  lie in `.data`/heap; mapped in `K0`, shared; off the child's handed
  range, which lies in the pool).
- `childSt_I`: at main's permit word `pinA + 24` (`tcbM + 16`) and the
  second TCB's word `pinA + 160` (`tcb2 + 24`), value `1`; the value
  invariant off both limit words (`X64WakeGOf2.gOf2_ne`).
- `childLd_I`: the load of the worker's TCB word `tcb2` (`hT`).
- `childOwn_I`: `msW` owns `⟨W, 8⟩` with value `W` at every pc (`hown`).
- `childSt_al`: `pinA + 24` is 4-aligned (`htp4`).

**Unlike AArch64** (forced by the x64 shape):
- `pinned` starts at `pinA` (`PlaceWX.pinA_toNat_ofPlaceWX`), so the
  TCB words' bytes are in `pinned` from `hpin2` alone; AArch64 goes through
  A8's `rtOffOk` (`tcb_pinned`, `pinned_lo_le`).
- The worker's memory side is `msXW` (`msW`): its runtime writes must be off
  both TCB self words (`OffTcb T`, `OffTcb W`), hence the `T = tcbM L`,
  `W = tcb2 L` premises of `childSt_I`.
- The child reads its TCB self word (`childLd_I`) and owns it
  (`childOwn_I`); AArch64 has neither premise.
- `StOk` has no executable or end-pc arguments.

Open (premises): `hpin2` (the pinned region reaches `pinA + 200`, through
the tid word `tcb2 + 56`).
-/
import Spike.Lib.X64WakeInst
import Spike.Lib.X64WakeQ
import Spike.Lib.X64WakeGOf
import Spike.Lib.Rt.X64RtChildPrem
import Spike.Lib.X64PlaceWRt
import Spike.Lib.X64WakeOwnWSep

namespace Spike.Lib.X64WakeChildSt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (MemRelP lrange Range)
open Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Sem.X64 (abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (DFrame OwnAt)
open Spike.Lib.X64.Flow.Ret0 (StOk LdOk)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64.WakePh (tcb2 tcbM)
open Spike.Lib.X64WakeInst (Gh wakeMs msW)
open Spike.Lib.X64WakeOwnX (OffTcb)

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpl i

/-- `pinA` lies below `2 ^ 32`. -/
theorem pinA_small : (Ly).pinA.toNat < 2 ^ 32 :=
  (Ly).words_small _ (Ly).pin_mem

/-- `pinA + c` for a small `c` does not wrap. -/
theorem pinA_add {c : Nat} (hc : c < 2 ^ 32) :
    ((Ly).pinA + BitVec.ofNat 64 c).toNat = (Ly).pinA.toNat + c := by
  have := pinA_small hpl i
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- **A word `pinA + c` below `pinA + 200` has its bytes in `pinned`.** -/
theorem pin_pinned (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {c : Nat} (hc : c + 8 ≤ 200) :
    ∀ k < 8, (Ly).Λ.pinned.contains (((Ly).pinA + BitVec.ofNat 64 c).toNat + k) := by
  intro k hk
  have h0 := PlaceWX.pinA_toNat_ofPlaceWX hpl i
  rw [pinA_add hpl i (by omega)]
  simp only [Range.contains]; omega

/-- **A word in `pinned` off both TCB self words is a runtime store in the
child's frame**: under `msW`, for the child after a `clone` that handed
`r1` (in the stack pool), given the value invariant at the word. -/
theorem stOk_pinned (T W : BitVec 64) (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp)
    {a v : BitVec 64} (ha : ∀ k < 8, (Ly).Λ.pinned.contains (a.toNat + k))
    (hG : (wakeMs hpl i g).G ⟨a, 8⟩ (v.setWidth 128)) (hT : OffTcb T ⟨a, 8⟩) (hW : OffTcb W ⟨a, 8⟩)
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hsz : r1.size = 16384) :
    StOk (msW hpl i T W g) (DFrame (childR (r1.lo + r1.size) (-16384))
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) a v := by
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hpl i
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, hsp⟩ := hwf.disjoint
  have hpin := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] :
    (Ly).Λ.pinned ∈ (Ly).Λ.regions)
  have hpf := (Ly).pool_fit
  have h0 := ha 0 (by decide)
  have h7 := ha 7 (by decide)
  simp only [Range.contains, Range.Disjoint, Range.Sub, Range.InSpace] at h0 h7 hdp hhp hsp hpin hsub
  -- off every placed label (they lie in `.data` or the heap)
  have hoff : ∀ k < 8, ¬ ∃ l b, g.lbl l = some b ∧ (lrange g.lsize l b).contains (a.toNat + k) := by
    rintro k hk ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
    have hk' := ha k hk
    simp only [Range.contains] at hs hk'
    omega
  refine ⟨fun ⟨l, b, hl, hx⟩ => hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩,
    ⟨⟨Spike.Lib.X64Consumer.mapped_K0_of_mem fun k hk => .inr (ha k hk), fun _ => ⟨fun k hk => ?_, ?_⟩⟩,
      fun _ => ⟨hT, hW⟩⟩, hG, ?_⟩
  · exact .inr (.inr (ha k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))
  · rintro ⟨l, b, hl, hx⟩
    exact hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩
  · intro m hF
    have htop : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [hF a (by omega) (by simp only [childR, htop]; omega), Spike.Lib.X64.Rt.childAfter_dmem hh]
    exact Spike.Lib.X64.Rt.loadInt_copyRange_none (by omega) (by simp only [Range.contains]; omega) (by decide)

/-- **A word in `pinned` is a runtime load in the child's frame** under
`msW`. -/
theorem ldOk_pinned (T W : BitVec 64) (g : Gh) {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp)
    {a : BitVec 64} (ha : ∀ k < 8, (Ly).Λ.pinned.contains (a.toNat + k))
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hsz : r1.size = 16384) :
    LdOk (msW hpl i T W g) (DFrame (childR (r1.lo + r1.size) (-16384))
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) a := by
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hpl i
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, hsp⟩ := hwf.disjoint
  have hpin := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] :
    (Ly).Λ.pinned ∈ (Ly).Λ.regions)
  have hpf := (Ly).pool_fit
  have h0 := ha 0 (by decide)
  have h7 := ha 7 (by decide)
  simp only [Range.contains, Range.Disjoint, Range.Sub, Range.InSpace] at h0 h7 hdp hhp hsp hpin hsub
  have hoff : ∀ k < 8, ¬ ∃ l b, g.lbl l = some b ∧ (lrange g.lsize l b).contains (a.toNat + k) := by
    rintro k hk ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
    have hk' := ha k hk
    simp only [Range.contains] at hs hk'
    omega
  refine ⟨fun ⟨l, b, hl, hx⟩ => hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩,
    ⟨⟨Spike.Lib.X64Consumer.mapped_K0_of_mem fun k hk => .inr (ha k hk), nofun⟩, nofun⟩, ?_⟩
  intro m hF
  have htop : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hF a (by omega) (by simp only [childR, htop]; omega), Spike.Lib.X64.Rt.childAfter_dmem hh]
  exact Spike.Lib.X64.Rt.loadInt_copyRange_none (by omega) (by simp only [Range.contains]; omega) (by decide)

/-- **`hS`/`hSx` at the instance**: main's permit word `pinA + 24` and the
second TCB's word `pinA + 160` take the store of `1` in the child's frame,
for `T`, `W` the two TCB words. -/
theorem childSt_I {T W : BitVec 64} (hT : T = tcbM (Ly)) (hW : W = tcb2 (Ly)) (g : Gh)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {a : BitVec 64} (ha : a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 160#64)
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hsz : r1.size = 16384) :
    StOk (msW hpl i T W g) (DFrame (childR (r1.lo + r1.size) (-16384))
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) a 1#64 := by
  have hs := pinA_small hpl i
  have eT : T.toNat = (Ly).pinA.toNat + 8 := by
    rw [hT]; exact pinA_add hpl i (c := 8) (by decide)
  have eW : W.toNat = (Ly).pinA.toNat + 136 := by
    rw [hW]; exact pinA_add hpl i (c := 136) (by decide)
  rcases ha with rfl | rfl
  · have e : ((Ly).pinA + 24#64).toNat = (Ly).pinA.toNat + 24 := pinA_add hpl i (c := 24) (by decide)
    refine stOk_pinned hpl i T W g hm (pin_pinned hpl i hpin2 (c := 24) (by decide)) (.inr ?_)
      (.inr (by simp only [e, eT]; omega)) (.inl (by simp only [e, eW]; omega)) hh hsub hsz
    exact Spike.Lib.X64WakeGOf2.gOf2_ne (Spike.Lib.X64.PhRec.pin_ne (by decide))
      (Spike.Lib.X64WakeGOf2.pin_ne2 (by decide)) _
  · have e : ((Ly).pinA + 160#64).toNat = (Ly).pinA.toNat + 160 := pinA_add hpl i (c := 160) (by decide)
    refine stOk_pinned hpl i T W g hm (pin_pinned hpl i hpin2 (c := 160) (by decide)) (.inr ?_)
      (.inr (by simp only [e, eT]; omega)) (.inr (by simp only [e, eW]; omega)) hh hsub hsz
    exact Spike.Lib.X64WakeGOf2.gOf2_ne (Spike.Lib.X64.PhRec.pin_ne (by decide))
      (Spike.Lib.X64WakeGOf2.pin_ne2 (by decide)) _

/-- **`hT` at the instance**: the worker's TCB word `tcb2` is a runtime
load in the child's frame. -/
theorem childLd_I (T : BitVec 64) {W : BitVec 64} (hW : W = tcb2 (Ly)) (g : Gh)
    {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ g.lbl g.lsize ts tm sm tp tq sp)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hsz : r1.size = 16384) :
    LdOk (msW hpl i T W g) (DFrame (childR (r1.lo + r1.size) (-16384))
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) W := by
  subst hW
  exact ldOk_pinned hpl i T _ g hm (pin_pinned hpl i hpin2 (c := 136) (by decide)) hh hsub hsz

/-- **`hown` at the instance**: `msW` owns `⟨W, 8⟩` with value `W` at every
pc. -/
theorem childOwn_I (T W : BitVec 64) (g : Gh) (exe : _root_.Executable) (endPc pc : Int64) :
    OwnAt (msW hpl i T W g) exe endPc pc W W :=
  fun _ _ _ _ => List.mem_singleton_self _

/-- **`htp4` at the instance**: main's permit word is 4-aligned. -/
theorem childSt_al : ((Ly).pinA + 24#64).toNat % 4 = 0 := by
  have hw := Scc.Cert.Rt.X64.wordsOk_of_rtWordsOk (PlaceWX.rtWordsOk_link_of_placeWX i hpl)
  have h8 := Scc.Cert.Rt.X64.words_al_of_wordsOk hw _ (Ly).pin_mem
  change (Ly).pinA.toNat % 8 = 0 at h8
  rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, pinA_add hpl i (by decide)]
  omega

end Place

/-- info: 'Spike.Lib.X64WakeChildSt.childSt_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSt_I

/-- info: 'Spike.Lib.X64WakeChildSt.childLd_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childLd_I

/-- info: 'Spike.Lib.X64WakeChildSt.childSt_al' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms childSt_al

end Spike.Lib.X64WakeChildSt

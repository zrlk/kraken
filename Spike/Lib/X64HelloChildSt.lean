/-
**hello.w's spawned child: its runtime stores** (x86-64; the twin of `Spike/Lib/A64HelloChildSt.lean`,
`Hello.SegR.ChildPrem`'s `hS`, `hSx`; in the manner of `Spike.Lib.X64WakeChildSt` at hello's memory side
`X64HelloMs.helloMs`, any value invariant `G`, and the child's frame on the stub's region `childR top lo`,
`-lo ≤ r1.size`).

- `unmapped_child`: a word off the handed range `r1` is unmapped in the child's first memory.
- `stOk_pinnedH`: a word whose 8 bytes lie in `pinned` is a runtime store under `helloMs` in the child's
  frame, given `G` at the word and value (as `X64WakeChildSt.stOk_pinned`).
- `childSt_IH`: main's permit word `pinA + 24` and the second TCB's word `pinA + 160` take the store of `1`
  (`hpin2`: the pinned region reaches `pinA + 200`; `hG`: `G` allows `1` there).
- `StOk.withBW`: a runtime store's facts do not read the byte or abort rows, so they hold at
  `ms.withBW bo we` (hello's `helloMsW`, the child segment's memory side).

## Differences from the AArch64 version

- `pinned` starts at `pinA` (`PlaceWX.pinA_toNat_ofPlaceWX`), so `childSt_IH` places both words' bytes in
  `pinned` from `hpin2` alone (`X64WakeChildSt.pin_pinned`); AArch64 goes through A8's offsets
  (`WakeChildSt.tcb_pinned`, `pinned_lo_le`).
- `helloMs`'s runtime writes need no TCB side conditions (unlike wake's `msW`), so `stOk_pinnedH` has none.
- `StOk` has no executable or end-pc arguments.
- AArch64's `hdm_placed` is not used by the hello proof and is not restated.
-/
import Spike.Lib.X64WakeChildSt
import Spike.Lib.X64HelloMs
import Spike.Lib.MemSideBW

namespace Spike.Lib.X64HelloChildSt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (MemRelP lrange Range)
open Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Sem.X64 (abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (DFrame)
open Spike.Lib.X64.Flow.Ret0 (StOk)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64HelloMs (helloMs)

/-- **A word off the handed range is unmapped in the child's first memory** (on the stub's region below
`r1`'s top, inside `r1`). -/
theorem unmapped_child {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (htop : r1.lo + r1.size < 2 ^ 64)
    (hlo : -lo ≤ r1.size) {a : BitVec 64} (ha8 : a.toNat + 8 ≤ 2 ^ 64)
    (hoff : a.toNat + 8 ≤ r1.lo ∨ r1.lo + r1.size ≤ a.toNat) :
    ∀ m, DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1 m →
      Mem.loadInt m.dmem a 8 = none := by
  intro m hF
  have hb : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  rw [hF a (by omega) (by simp only [childR, hb]; omega), Spike.Lib.X64.Rt.childAfter_dmem hh]
  exact Spike.Lib.X64.Rt.loadInt_copyRange_none (by omega) (by simp only [Range.contains]; omega) (by decide)

/-- **A runtime store's facts at `ms.withBW bo we`** (they read `rt`, `mp`, `G` only). -/
theorem StOk.withBW {ms : MemSide isa} {F : MachineData → Prop} {a v : BitVec 64} (h : StOk ms F a v)
    (bo : isa.State → Nat → Spike.Lib.Ctl → (Spike.Lib.Ctl → Prop) → Prop)
    (we : isa.State → Spike.Lib.Ctl → Prop) : StOk (ms.withBW bo we) F a v :=
  ⟨h.rt, h.mp, h.G, h.unmapped⟩

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpl i

/-- **A word in `pinned` is a runtime store in the child's frame** under `helloMs` (the child after a
`clone` that handed `r1`, in the stack pool), given `G` at the word and value. -/
theorem stOk_pinnedH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tp tq sp)
    {a v : BitVec 64} (ha : ∀ k < 8, (Ly).Λ.pinned.contains (a.toNat + k))
    (hG : G ⟨a, 8⟩ (v.setWidth 128))
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hlo : -lo ≤ r1.size) :
    StOk (helloMs (Ly) G lbl lsize) (DFrame (childR (r1.lo + r1.size) lo)
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) a v := by
  have hwf := Spike.Lib.X64WakeQ.hwf_ofPlaceOK hpl i
  obtain ⟨-, -, -, -, -, -, -, hdp, hhp, hsp⟩ := hwf.disjoint
  have hpin := hwf.inSpace _ (by simp [Scc.Sem.Layout.regions] : (Ly).Λ.pinned ∈ (Ly).Λ.regions)
  have hpf := (Ly).pool_fit
  have h0 := ha 0 (by decide)
  have h7 := ha 7 (by decide)
  simp only [Range.contains, Range.Disjoint, Range.Sub, Range.InSpace] at h0 h7 hdp hhp hsp hpin hsub
  -- off every placed label (they lie in `.data` or the heap)
  have hoff : ∀ k < 8, ¬ ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains (a.toNat + k) := by
    rintro k hk ⟨l, b, hl, hx⟩
    have hs := Spike.Lib.X64WakeGOf.heapData_of_placed hm hl hx
    have hk' := ha k hk
    simp only [Range.contains] at hs hk'
    omega
  refine ⟨fun ⟨l, b, hl, hx⟩ => hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩,
    ⟨Spike.Lib.X64Consumer.mapped_K0_of_mem fun k hk => .inr (ha k hk), fun _ => ⟨fun k hk => ?_, ?_⟩⟩, hG,
    unmapped_child hh (by omega) hlo (by omega) (by omega)⟩
  · exact .inr (.inr (ha k (by simpa [Scc.Sem.Kernel.locBytes] using hk)))
  · rintro ⟨l, b, hl, hx⟩
    exact hoff 0 (by decide) ⟨l, b, hl, by simpa using hx⟩

/-- **`hS`/`hSx` at the instance**: main's permit word `pinA + 24` and the second TCB's word `pinA + 160`
take the store of `1` in the child's frame, given the pinned region through `pinA + 200` (`hpin2`) and `G`
allowing `1` at the word (`hG`). -/
theorem childSt_IH {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tp tq sp)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    {a : BitVec 64} (ha : a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 160#64)
    (hG : G ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128))
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {tls : Nat} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hlo : -lo ≤ r1.size) :
    StOk (helloMs (Ly) G lbl lsize) (DFrame (childR (r1.lo + r1.size) lo)
        (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1) a 1#64 := by
  rcases ha with rfl | rfl
  · exact stOk_pinnedH hpl i hm (Spike.Lib.X64WakeChildSt.pin_pinned hpl i hpin2 (c := 24) (by decide)) hG hh
      hsub hlo
  · exact stOk_pinnedH hpl i hm (Spike.Lib.X64WakeChildSt.pin_pinned hpl i hpin2 (c := 160) (by decide)) hG hh
      hsub hlo

end Place

end Spike.Lib.X64HelloChildSt

/-- info: 'Spike.Lib.X64HelloChildSt.unmapped_child' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildSt.unmapped_child

/-- info: 'Spike.Lib.X64HelloChildSt.childSt_IH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildSt.childSt_IH

/-- info: 'Spike.Lib.X64HelloChildSt.StOk.withBW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildSt.StOk.withBW

/-- info: 'Spike.Lib.X64HelloChildSt.stOk_pinnedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildSt.stOk_pinnedH

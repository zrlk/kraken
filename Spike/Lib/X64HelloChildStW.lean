/-
**The child segment's runtime-store premises at the worker's memory side** (x86-64; the twin of
`Spike/Lib/A64HelloChildStW.lean`: `Hello.SegR.ChildPrem`'s `hS`, `htp4`, `hSx` at the clone's data):
`X64HelloChildSt.childSt_IH` at main's permit word (`pinA + 24`) and `X64HelloChildSt.stOk_pinnedH` at the
second TCB's word (`pinA + 136`), read through the packet's `ThreadId` word `meW` (main's TCB, `pinA + 8`) and the
clone's thread pointer `tls` (hello's second TCB, `pinA + 144`, `X64HelloWcSp3.tH`), at `helloMsW`
(`StOk.withBW`).

- `childPrem_St`: `hS`, `htp4`, `hSx` at `w.w5 = ofNat meW`, `tp = ofNat tls`, the child's first memory on the
  stub's region `childR top lo`. Premises: the memory relation (`hm`), the pinned region reaching `pinA + 200`
  (`hpin2`), `G` allowing `1` at the two words `pinA + 24`, `pinA + 136` (`hG`), `meW` main's TCB (`hmeW`),
  `tls` the second TCB (`htls`, `TlsTcb.tls_eq` at hello's second TCB), the clone's handed range in the stack
  pool and at least `-lo` bytes.

## Differences from the AArch64 version

- The stub's frame depth is a parameter `lo` with `-lo ≤ r1.size` (AArch64: `-272`, `272 ≤ r1.size`).
- `StOk` has no executable or end-pc arguments; the alignment is `X64WakeChildSt.childSt_al`.
-/
import Spike.Lib.X64HelloChildSt
import Spike.Lib.X64HelloByteOutP

namespace Spike.Lib.X64HelloChildStW

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (MemRelP Range)
open Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Sem.X64 (abi)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64 (DFrame)
open Spike.Lib.X64.Flow.Ret0 (StOk)
open Spike.Lib.X64.WakePh.Child (childR)
open Spike.Lib.X64HelloByteOutP (helloMsW)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {AbW : isa.State → Prop}

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => RuntimeLayout.ofPlaceWX hpl i

/-- **`ChildPrem`'s `hS`, `htp4`, `hSx`** at the worker's memory side `helloMsW`, the packet's `ThreadId` word
`meW` main's TCB and the clone's thread pointer `tls` the second TCB. -/
theorem childPrem_St {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tp tq sp)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hG : ∀ a : BitVec 64, a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 168#64 →
      G ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128))
    {meW tls : Nat} (hmeW : BitVec.ofNat 64 meW = (Ly).pinA + 8#64)
    (htls : BitVec.ofNat 64 tls = (Ly).pinA + 144#64)
    {x : KState} {tid : Nat} {th : Thread isa} {r1 : Range} {lo : Int}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hlo : -lo ≤ r1.size) :
    StOk (helloMsW (Ly) G lbl lsize AbW)
        (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1)
        (BitVec.ofNat 64 meW + 16#64) 1#64 ∧
      (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 ∧
      StOk (helloMsW (Ly) G lbl lsize AbW)
        (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1)
        (BitVec.ofNat 64 tls + 24#64) 1#64 := by
  have e24 : BitVec.ofNat 64 meW + 16#64 = (Ly).pinA + 24#64 := by rw [hmeW]; bv_omega
  have e136 : BitVec.ofNat 64 tls + 24#64 = (Ly).pinA + 168#64 := by rw [htls]; bv_omega
  rw [e24, e136]
  exact ⟨Spike.Lib.X64HelloChildSt.StOk.withBW (Spike.Lib.X64HelloChildSt.childSt_IH hpl i hm hpin2 (.inl rfl)
      (hG _ (.inl rfl)) hh hsub hlo) _ _,
    Spike.Lib.X64WakeChildSt.childSt_al hpl i,
    Spike.Lib.X64HelloChildSt.StOk.withBW (Spike.Lib.X64HelloChildSt.stOk_pinnedH hpl i hm
      (Spike.Lib.X64WakeChildSt.pin_pinned hpl i hpin2 (c := 168) (by decide)) (hG _ (.inr rfl)) hh hsub hlo) _ _⟩

end Spike.Lib.X64HelloChildStW

/-- info: 'Spike.Lib.X64HelloChildStW.childPrem_St' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloChildStW.childPrem_St

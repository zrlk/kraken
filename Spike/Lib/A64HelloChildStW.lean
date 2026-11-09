/-
**The child segment's runtime-store premises at the worker's memory side** (AArch64, `hS`,
`htp4`, `hSx`; `Hello.SegR.ChildPrem`'s fields at `childP_of_clone`'s data): `HelloChildSt.childSt_IH` at main's
permit word (`pinA + 24`) and `HelloChildSt.stOk_pinnedH` at the second TCB's word (`pinA + 136`), read through
the packet's `ThreadId` word `meW` (main's TCB, `pinA + 8`) and the clone's thread pointer `tls` (the second TCB,
`pinA + 144`), at `helloMsW` (`StOk.withBW`).

- `childPrem_St`: `hS`, `htp4`, `hSx` at `w.w5 = ofNat meW`, `tp = ofNat tls`, the child's first memory on the
  stub's region `childR top (-272)`. Premises: the memory relation (`hm`), the pinned region reaching
  `pinA + 200` (`hpin2`, `A64HelloChildRoot.hpin2_H`), `G` allowing `1` at the two words `pinA + 24`,
  `pinA + 168` (`hG`), `meW` main's TCB (`hmeW`, from `A64HelloChildRoot.meW_H`), `tls` the second TCB (`htls`,
  row clone-tls-TcbArea's `TlsTcb.tls_eq` at hello's `tcbOf q = pinA + 144`), the clone's handed range in the
  stack pool and at least 272 bytes.
-/
import Spike.Lib.A64HelloChildSt
import Spike.Lib.HelloByteOutP
import Spike.Lib.WakeChildSt

namespace Spike.Lib.HelloChildStW

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (MemRelP Range)
open Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64.Flow (DFrame)
open Spike.Lib.A64.Flow.Ret0 (StOk)
open Spike.Lib.A64.Flow.Worker.Wake.Child (childR)
open Spike.Lib.HelloByteOutP (helloMsW)

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (hpl : PlaceW pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)
    {G : Loc → Val → Prop} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {AbW : isaLSE2.State → Prop}

local notation "Ly" => RuntimeLayout.ofPlaceW hpl i

/-- **`ChildPrem`'s `hS`, `htp4`, `hSx`** at the worker's memory side `helloMsW`, the packet's `ThreadId` word
`meW` main's TCB and the clone's thread pointer `tls` the second TCB. -/
theorem childPrem_St {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}
    (hm : MemRelP (Ly).Λ lbl lsize ts tm sm tp tq sp)
    (hpin2 : (Ly).pinA.toNat + 200 ≤ (Ly).Λ.pinned.lo + (Ly).Λ.pinned.size)
    (hG : ∀ a : BitVec 64, a = (Ly).pinA + 24#64 ∨ a = (Ly).pinA + 168#64 →
      G ⟨a, 8⟩ ((1#64 : BitVec 64).setWidth 128))
    {meW tls : Nat} (hmeW : BitVec.ofNat 64 meW = (Ly).pinA + 8#64)
    (htls : BitVec.ofNat 64 tls = (Ly).pinA + 144#64)
    {x : KState} {tid : Nat} {th : Thread isaLSE2} {r1 : Range}
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (hsub : r1.Sub (Ly).Λ.stackPool) (hsz : 272 ≤ r1.size)
    {exe : _root_.Executable} {endPc : Int64} :
    StOk (helloMsW (Ly) G lbl lsize AbW)
        (DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1)
        exe endPc (BitVec.ofNat 64 meW + 16#64) 1#64 ∧
      (BitVec.ofNat 64 meW + 16#64).toNat % 4 = 0 ∧
      StOk (helloMsW (Ly) G lbl lsize AbW)
        (DFrame (childR (r1.lo + r1.size) (-272)) (childAfter abi x tid th (r1.lo + r1.size) tls).st.st.1)
        exe endPc (BitVec.ofNat 64 tls + 24#64) 1#64 := by
  have e24 : BitVec.ofNat 64 meW + 16#64 = (Ly).pinA + 24#64 := by rw [hmeW]; bv_omega
  have e136 : BitVec.ofNat 64 tls + 24#64 = (Ly).pinA + 168#64 := by rw [htls]; bv_omega
  rw [e24, e136]
  refine ⟨?_, Spike.Lib.WakeChildSt.childSt_al hpl i, ?_⟩
  · exact Spike.Lib.HelloChildSt.StOk.withBW (Spike.Lib.HelloChildSt.childSt_IH hpl i hm hpin2 (.inl rfl)
      (hG _ (.inl rfl)) hh hsub (by omega)) _ _
  · have hlo' := Spike.Lib.WakeChildSt.pinned_lo_le hpl i
    refine Spike.Lib.HelloChildSt.StOk.withBW (Spike.Lib.HelloChildSt.stOk_pinnedH hpl i hm (fun k hk => ?_)
      (hG _ (.inr rfl)) hh hsub (by omega)) _ _
    rw [show (168#64 : BitVec 64) = BitVec.ofNat 64 168 from rfl, Spike.Lib.WakeChildSt.pinA_add hpl i (by decide)]
    simp only [Range.contains]; omega

end Spike.Lib.HelloChildStW

/-- info: 'Spike.Lib.HelloChildStW.childPrem_St' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloChildStW.childPrem_St

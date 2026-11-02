/-
**hello.w's self-word memory sides on x86-64** (x86-64 only; the hello counterpart of
`X64WakeInstMsM` and `X64WakeSelfOK`): main's park and the worker's tail read their TCB's self word (`%fs:0`),
a runtime load that needs the word owned (`OwnAt … tp tp`). As in wake, each thread's memory side is its side
with its own self word owned and its runtime writes narrowed to words off both self words (`X64WakeOwnX.msXW`):
main's `msHX := msXW (msH …) T T W`, the worker's `msWHX := msXW (msWH …) W T W`, at `T = tcbM L = pinA + 8`
and hello's second TCB `W = tcbWH L = pinA + 112`.

- `tcbWH`, `tcbM_ne_tcbWH`: hello's second TCB's self word and its distinctness (`X64HelloMs`'s, re-exported).
- `offTcb_park_tcbWH`, `tcbM_roomH`, `pin_room120_ofPlaceWX`: the park's word `tcbM + 16` misses `tcbWH`'s,
  `tcbM + 24` fits, and `pinA + 120` fits at a placed output.
- `ldOk_msXW`, `limOk_msXW`, `stOk_msXW_park`: the runtime accesses' facts transfer from any memory side to its
  `msXW` (a read's `mp … false` is unchanged; the park's exchange at `T + 16` misses both self words).
- `msHX`, `msWHX`: the two memory sides at record `w`; `ldOk_msHX`, `limOk_msHX`, `stOk_msHX_park`: the lifts at
  main's; `ownAt_msHX`, `ownAt_msWHX`: each side owns its self word holding its address (the `hown` premises of
  the park and the worker's tail).

## Differences from wake and AArch64

Unlike AArch64, whose park and worker tail read the thread pointer from a register, x86-64's read the TCB's
self word through `%fs`, so each thread's memory side must own that word. hello's second TCB is at
`pinA + 112` (its header at `pinA + 104`, `X64HelloGOf2H`), where wake's is at `pinA + 104`, so wake's
`X64WakeInst.offTcb_park_tcb2` does not apply; `offTcb_park_tcbWH` is its counterpart at `pinA + 112`.
-/
import Spike.Lib.X64WakeSelfOK
import Spike.Lib.X64HelloMs
import Spike.Lib.X64HelloMsW

namespace Spike.Lib.X64HelloOwnLift

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.Inv2Core
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM)
open Spike.Lib.X64WakeOwnX (OffTcb msXW msXW_mp_of offTcb_add ownAt_msXW)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)

/-! ## The self words -/

export Spike.Lib.X64HelloMs (tcbWH tcbM_ne_tcbWH)

/-- **The park's word `tcbM + 16` misses `tcbWH`'s** (no wrap-around). -/
theorem offTcb_park_tcbWH (L : RuntimeLayout) (hpin : L.pinA.toNat + 120 ≤ 2 ^ 64) :
    OffTcb (tcbWH L) ⟨tcbM L + 16#64, 8⟩ := by
  left
  show (L.pinA + 8#64 + 16#64).toNat + 8 ≤ (L.pinA + 112#64).toNat
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := L.pinA.toNat + 8 % 2 ^ 64) (by omega),
    Nat.mod_eq_of_lt (a := L.pinA.toNat + 8 % 2 ^ 64 + 16 % 2 ^ 64) (by omega),
    Nat.mod_eq_of_lt (a := L.pinA.toNat + 112 % 2 ^ 64) (by omega)]
  omega

/-- **`tcbM + 24` fits** (`stOk_msXW_park`'s `hT`). -/
theorem tcbM_roomH (L : RuntimeLayout) (hpin : L.pinA.toNat + 120 ≤ 2 ^ 64) :
    (tcbM L).toNat + 24 ≤ 2 ^ 64 :=
  X64WakeInst.tcbM_room L (by omega)

/-- **`pinA + 120` fits at a placed output** (the pinned region below `2 ^ 32`). -/
theorem pin_room120_ofPlaceWX {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ : Scc.Sem.Layout} (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (RuntimeLayout.ofPlaceWX hp i).pinA.toNat + 120 ≤ 2 ^ 64 := by
  have hb := PlaceWX.below32_of_placeWX hp Λ.pinned (by simp [Scc.Sem.Layout.regions])
  have he : (RuntimeLayout.ofPlaceWX hp i).Λ.pinned = Λ.pinned := rfl
  rw [PlaceWX.pinA_toNat_ofPlaceWX hp i, he]
  omega

/-! ## The runtime accesses at any `msXW` -/

section Gen

variable {ms : MemSide isa} {F : MachineData → Prop} {O T W : BitVec 64}

/-- A runtime load's facts at `msXW` (a read's `mp … false` is unchanged by the narrowing). -/
theorem ldOk_msXW {a : BitVec 64} (h : LdOk ms F a) : LdOk (msXW ms O T W) F a :=
  ⟨h.rt, ⟨h.mp, fun h => nomatch h⟩, h.unmapped⟩

/-- The prologue's limit load at `msXW`. -/
theorem limOk_msXW {a Z : BitVec 64} (h : LimOk ms F a Z) : LimOk (msXW ms O T W) F a Z :=
  ⟨h.rt, ⟨h.mp, fun h => nomatch h⟩, h.unmapped, h.room⟩

/-- **The park's exchange at `T + 16` at `msXW`**: off `T`'s word (no wrap-around, `hT`) and off `W`'s
(`hW`). -/
theorem stOk_msXW_park (h : StOk ms F (T + 16#64) 0#64) (hT : T.toNat + 24 ≤ 2 ^ 64)
    (hW : OffTcb W ⟨T + 16#64, 8⟩) : StOk (msXW ms O T W) F (T + 16#64) 0#64 :=
  ⟨h.rt, msXW_mp_of h.mp (offTcb_add (k := 16) (by decide) (by omega)) hW, h.G, h.unmapped⟩

end Gen

/-! ## hello's two memory sides -/

section Ms

variable {ι : Type} (L : RuntimeLayout) (G : ι → Loc → Val → Prop) (SR : ι → SpawnRec)

export Spike.Lib.X64HelloMs (msHX)

/-- **The worker's memory side at record `w`**: `X64HelloMsW.msWH` owning `tcbWH`, its runtime writes off both
self words. -/
abbrev msWHX (w : ι) : MemSide isa := msXW (X64HelloMsW.msWH L G SR w) (tcbWH L) (tcbM L) (tcbWH L)

variable {L G SR} {w : ι} {F : MachineData → Prop}

/-- A runtime load at main's side. -/
theorem ldOk_msHX {a : BitVec 64} (h : LdOk (X64HelloMs.msH L G SR w) F a) : LdOk (msHX L G SR w) F a :=
  ldOk_msXW h

/-- The prologue's limit load at main's side. -/
theorem limOk_msHX {a Z : BitVec 64} (h : LimOk (X64HelloMs.msH L G SR w) F a Z) :
    LimOk (msHX L G SR w) F a Z :=
  limOk_msXW h

/-- **The park's exchange at `tcbM + 16` at main's side**, given `pinA + 120` in the address space
(`pin_room120_ofPlaceWX` at a placed output). -/
theorem stOk_msHX_park (h : StOk (X64HelloMs.msH L G SR w) F (tcbM L + 16#64) 0#64)
    (hpin : L.pinA.toNat + 120 ≤ 2 ^ 64) : StOk (msHX L G SR w) F (tcbM L + 16#64) 0#64 :=
  stOk_msXW_park h (tcbM_roomH L hpin) (offTcb_park_tcbWH L hpin)

/-- **main's side owns `tcbM` holding `tcbM`** at every pc (the park's `%fs:0` load). -/
theorem ownAt_msHX {exe : _root_.Executable} {endPc pc : Int64} :
    Spike.Lib.X64.OwnAt (msHX L G SR w) exe endPc pc (L.pinA + 8#64) (L.pinA + 8#64) :=
  ownAt_msXW

/-- **The worker's side owns `tcbWH` holding `tcbWH`** at every pc (the tail's `%fs:0` load). -/
theorem ownAt_msWHX {exe : _root_.Executable} {endPc pc : Int64} :
    Spike.Lib.X64.OwnAt (msWHX L G SR w) exe endPc pc (tcbWH L) (tcbWH L) :=
  ownAt_msXW

/-- Inhabitation: main's side owns exactly `tcbM`, the worker's exactly `tcbWH`. -/
example (s : isa.State) : (msHX L G SR w).own s = [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)] ∧
    (msWHX L G SR w).own s = [(⟨tcbWH L, 8⟩, (tcbWH L).setWidth 128)] :=
  ⟨rfl, rfl⟩

end Ms

end Spike.Lib.X64HelloOwnLift

/-- info: 'Spike.Lib.X64HelloMs.tcbM_ne_tcbWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMs.tcbM_ne_tcbWH

/-- info: 'Spike.Lib.X64HelloOwnLift.offTcb_park_tcbWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.offTcb_park_tcbWH

/-- info: 'Spike.Lib.X64HelloOwnLift.tcbM_roomH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.tcbM_roomH

/-- info: 'Spike.Lib.X64HelloOwnLift.pin_room120_ofPlaceWX'
  depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Spike.Lib.X64HelloOwnLift.pin_room120_ofPlaceWX

/-- info: 'Spike.Lib.X64HelloOwnLift.ldOk_msXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.ldOk_msXW

/-- info: 'Spike.Lib.X64HelloOwnLift.limOk_msXW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.limOk_msXW

/-- info: 'Spike.Lib.X64HelloOwnLift.stOk_msXW_park' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.stOk_msXW_park

/-- info: 'Spike.Lib.X64HelloOwnLift.ldOk_msHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.ldOk_msHX

/-- info: 'Spike.Lib.X64HelloOwnLift.limOk_msHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.limOk_msHX

/-- info: 'Spike.Lib.X64HelloOwnLift.stOk_msHX_park' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.stOk_msHX_park

/-- info: 'Spike.Lib.X64HelloOwnLift.ownAt_msHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.ownAt_msHX

/-- info: 'Spike.Lib.X64HelloOwnLift.ownAt_msWHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloOwnLift.ownAt_msWHX

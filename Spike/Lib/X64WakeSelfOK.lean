/-
**`SelfOK` at the TCB placement** (x86-64 only):
`X64WakeInst.SelfOK T W g` and `X64WakeInstMsM.stOk_msM_park`'s side facts at
the real self words `T = tcbM L = pinA + 8` (main's TCB) and
`W = tcb2 L = pinA + 104` (the second TCB), from the runtime words being
outside every placed label and the flag's word inside its label.

- `nlab_of_rt`: a runtime word of `wakeMs` (or of either `msXW` side: same
  `rt`) is outside every placed label (`MemSide.ofLabels`'s `rt`, by
  definition).
- `inLabel_cT`: the flag's word is inside its label (`GhOK`, the memory
  relation's placement, the label regions in the address space).
- `selfOK_of`: `SelfOK` from the words distinct, both outside every placed
  label and the flag's word inside one.
- `tcbM_ne_tcb2`, `offTcb_park_tcb2`, `tcbM_room`: the two TCB words differ
  (unconditionally), the park's word `tcbM + 16` misses `tcb2`'s (for
  `pinA + 144` in the address space) and `tcbM + 24` fits (for `pinA + 112`).
- `pin_room_ofPlaceWX`: `pinA + 144` fits at a placed output (the pinned
  region below `2 ^ 32`).
- `selfOK_tcb`: `SelfOK (tcbM L) (tcb2 L) g` from the two words being
  `wakeMs`' runtime words (`LdOk.rt` at main's `%fs:0` and the worker's) and
  the flag's word in its label: the real-placement inhabitation check
  (`T`, `W` and `cT` distinct).
-/
import Spike.Lib.X64WakeInstMsM
import Spike.Lib.X64WakeInstFields
import Spike.Lib.X64WakeOwnT2

namespace Spike.Lib.X64WakeInst

open Kraken.Promising Kraken.Promising.X64 Scc.Sem
open Spike.Lib Spike.Lib.Inv2Core
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM tcb2)
open Spike.Lib.X64WakeOwnX (OffTcb msXW)

section Inst

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **A runtime word of `wakeMs` is outside every placed label.** -/
theorem nlab_of_rt {g : Gh} {a : BitVec 64} (h : (wakeMs hp i g).rt a.toNat) :
    ¬ InLabel g.lbl g.lsize ⟨a, 8⟩ :=
  h

/-- The same at either `msXW` side (its `rt` is `wakeMs`'). -/
theorem nlab_of_rtX {g : Gh} {a O T W : BitVec 64} (h : (msXW (wakeMs hp i g) O T W).rt a.toNat) :
    ¬ InLabel g.lbl g.lsize ⟨a, 8⟩ :=
  h

end Inst

/-- **The flag's word is inside its label**: `GhOK`'s placed `cS`, the
memory relation placing labels in the heap or data, those in the address
space (`hsp`). -/
theorem inLabel_cT {Λ : Scc.Sem.Layout} {g : Gh} {ts : Nat → Option Nat} {tm : Memory} {sm : WeakMem.Memory}
    {tp tq sp : List Nat} (hm : MemRelP Λ g.lbl g.lsize ts tm sm tp tq sp)
    (hsp : ∀ x, Λ.heap.contains x ∨ Λ.data.contains x → x < 2 ^ 64)
    (h : X64WakeInstFields.GhOK Λ g) : InLabel g.lbl g.lsize g.cT := by
  obtain ⟨-, -, -, ⟨b, hl, ho, hT⟩, -⟩ := h
  have ho' : @LT.lt Nat _ g.cS.offset (g.lsize g.cS.label) := ho
  have hc : (lrange g.lsize g.cS.label b).contains (b + 8 * g.cS.offset) := by
    show b ≤ b + 8 * g.cS.offset ∧ b + 8 * g.cS.offset < b + 8 * g.lsize g.cS.label
    omega
  have hlt := hsp _ (X64WakeGOf.heapData_of_placed hm hl hc)
  refine ⟨g.cS.label, b, hl, ?_⟩
  rw [hT]
  show (lrange g.lsize g.cS.label b).contains (BitVec.ofNat 64 (b + 8 * g.cS.offset)).toNat
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact hc

/-- **`SelfOK` from its parts**: the words distinct, both outside every
placed label, the flag's word inside one (so not main's). -/
theorem selfOK_of {T W : BitVec 64} {g : Gh} (hTW : T ≠ W) (hT : ¬ InLabel g.lbl g.lsize ⟨T, 8⟩)
    (hW : ¬ InLabel g.lbl g.lsize ⟨W, 8⟩) (hcT : InLabel g.lbl g.lsize g.cT) : SelfOK T W g :=
  ⟨fun h => hTW (by cases h; rfl), hT, hW, fun h => hT (h ▸ hcT)⟩

/-- **The two TCB words differ.** -/
theorem tcbM_ne_tcb2 (L : RuntimeLayout) : tcbM L ≠ tcb2 L := by
  unfold tcbM tcb2
  bv_omega

/-- **The park's word `tcbM + 16` misses `tcb2`'s** (no wrap-around). -/
theorem offTcb_park_tcb2 (L : RuntimeLayout) (hpin : L.pinA.toNat + 144 ≤ 2 ^ 64) :
    OffTcb (tcb2 L) ⟨tcbM L + 16#64, 8⟩ := by
  left
  show (L.pinA + 8#64 + 16#64).toNat + 8 ≤ (L.pinA + 136#64).toNat
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := L.pinA.toNat + 8 % 2 ^ 64) (by omega),
    Nat.mod_eq_of_lt (a := L.pinA.toNat + 8 % 2 ^ 64 + 16 % 2 ^ 64) (by omega),
    Nat.mod_eq_of_lt (a := L.pinA.toNat + 136 % 2 ^ 64) (by omega)]
  omega

/-- **`tcbM + 24` fits** (`stOk_msM_park`'s `hT`). -/
theorem tcbM_room (L : RuntimeLayout) (hpin : L.pinA.toNat + 112 ≤ 2 ^ 64) :
    (tcbM L).toNat + 24 ≤ 2 ^ 64 := by
  show (L.pinA + 8#64).toNat + 24 ≤ 2 ^ 64
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := L.pinA.toNat + 8 % 2 ^ 64) (by omega)]
  omega

/-- **`pinA + 144` fits at a placed output** (the pinned region below `2 ^ 32`). -/
theorem pin_room_ofPlaceWX {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out}
    {Λ : Scc.Sem.Layout} (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) :
    (RuntimeLayout.ofPlaceWX hp i).pinA.toNat + 144 ≤ 2 ^ 64 := by
  have hb := PlaceWX.below32_of_placeWX hp Λ.pinned (by simp [Scc.Sem.Layout.regions])
  have he : (RuntimeLayout.ofPlaceWX hp i).Λ.pinned = Λ.pinned := rfl
  rw [PlaceWX.pinA_toNat_ofPlaceWX hp i, he]
  omega

/-- **`SelfOK` at the real self words** (the inhabitation check at the
placement): `tcbM`, `tcb2` runtime words of `wakeMs` (`hT`, `hW`: the
`LdOk.rt` of main's `%fs:0` and the worker's), the flag's word in its label
(`inLabel_cT`). -/
theorem selfOK_tcb {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
    (hp : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat) {g : Gh}
    (hT : (wakeMs hp i g).rt (tcbM (RuntimeLayout.ofPlaceWX hp i)).toNat)
    (hW : (wakeMs hp i g).rt (tcb2 (RuntimeLayout.ofPlaceWX hp i)).toNat)
    (hcT : InLabel g.lbl g.lsize g.cT) :
    SelfOK (tcbM (RuntimeLayout.ofPlaceWX hp i)) (tcb2 (RuntimeLayout.ofPlaceWX hp i)) g :=
  selfOK_of (tcbM_ne_tcb2 _) (nlab_of_rt hp i hT) (nlab_of_rt hp i hW) hcT

end Spike.Lib.X64WakeInst

/-- info: 'Spike.Lib.X64WakeInst.inLabel_cT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.inLabel_cT

/-- info: 'Spike.Lib.X64WakeInst.offTcb_park_tcb2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.offTcb_park_tcb2

/-- info: 'Spike.Lib.X64WakeInst.pin_room_ofPlaceWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.pin_room_ofPlaceWX

/-- info: 'Spike.Lib.X64WakeInst.selfOK_tcb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeInst.selfOK_tcb

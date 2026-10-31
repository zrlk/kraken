/-
**`WCompat0`'s own facts are satisfiable at main owning `tcbM`** (x86-64): the non-vacuity of the x86-64 change
to `X64WakeM0.WCompat0` (`own0` reads `Q.own w 0 s []`, with `ownConst0`,
`ownMp0`, `ownCov0`) at `X64WakeOwnX.wakeOwnX T`, with no premise beyond the
instance's.

The memory side of main's rows is any side `ms` with the owned word `⟨T, 8⟩`
added and its runtime writes narrowed to words whose bytes miss
`[T, T + 8)` (`OffTcb`): `msX ms T`. Park's exchange is at `T + 16`
(`X64Park`: `xchg(0, [tp + 16])` with `tp = tcbM`), whose bytes
`[T + 16, T + 24)` miss `[T, T + 8)`, so the narrowing keeps park's
`StOk.mp` (`msX_mp_park`). The location data adds `⟨T, 8⟩` as main's owned
word (`wakeLocsX`), so `WakeP`'s cover holds it (`WakeP.wakeP_own_cov`).

- `OffTcb`, `offTcb_self`, `offTcb_park`: the byte ranges; `⟨T, 8⟩` is not
  off itself, `⟨T + 16, 8⟩` is (no wrap-around past `2 ^ 64`).
- `msX`, `msX_own0`, `msX_mp_park`: the memory side (`WCompat0.own0` by
  `rfl`), and park's write allowed in it.
- `ownConst0X`, `ownMp0X`: `WCompat0.ownConst0` and `WCompat0.ownMp0` at
  `msX` and `wakeOwnX`.
- `wakeLocsX`, `wakeLocsX_ok`, `ownCov0X`: the location data, its separation
  facts (`WakeLocs.OK`), and `WCompat0.ownCov0` at `wakeP … (wakeLocsX …)`.
-/
import Spike.Lib.X64WakeOwnX
import Spike.Lib.WakeP

namespace Spike.Lib.X64WakeOwnX

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeP Spike.Lib.Inv2Core

/-! ## The byte ranges -/

/-- **`L`'s bytes miss the TCB word `[T, T + 8)`.** -/
def OffTcb (T : BitVec 64) (L : Loc) : Prop :=
  L.addr.toNat + L.bytes ≤ T.toNat ∨ T.toNat + 8 ≤ L.addr.toNat

/-- The TCB word itself is not off the TCB word. -/
theorem offTcb_self (T : BitVec 64) : ¬ OffTcb T ⟨T, 8⟩ := by
  unfold OffTcb; simp only; omega

/-- **Park's permit word `⟨T + 16, 8⟩` is off the TCB word** (no
wrap-around past `2 ^ 64`). -/
theorem offTcb_park {T : BitVec 64} (hT : T.toNat + 24 ≤ 2 ^ 64) : OffTcb T ⟨T + 16#64, 8⟩ := by
  unfold OffTcb
  right
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## main's memory side -/

/-- **main's memory side owning `tcbM`**: `ms` with the owned word
`⟨T, 8⟩ ↦ T` and its runtime writes narrowed to words off `[T, T + 8)`. -/
def msX (ms : MemSide isa) (T : BitVec 64) : MemSide isa :=
  { ms with
    own := fun _ => [(⟨T, 8⟩, T.setWidth 128)]
    mp := fun L w => ms.mp L w ∧ (w = true → OffTcb T L) }

/-- (`WCompat0.own0`) `msX` owns `wakeOwnX`'s words of thread 0. -/
theorem msX_own0 {ι : Type} (ms : MemSide isa) (T : BitVec 64) (w : ι) (s : isa.State) :
    (msX ms T).own s = wakeOwnX T w 0 s [] :=
  rfl

/-- **Park's exchange at `T + 16` stays a runtime write of `msX`.** -/
theorem msX_mp_park {ms : MemSide isa} {T : BitVec 64} (hmp : ms.mp ⟨T + 16#64, 8⟩ true)
    (hT : T.toNat + 24 ≤ 2 ^ 64) : (msX ms T).mp ⟨T + 16#64, 8⟩ true :=
  ⟨hmp, fun _ => offTcb_park hT⟩

/-- (`WCompat0.ownConst0`) `wakeOwnX`'s words of thread 0 are constant. -/
theorem ownConst0X {ι : Type} (T : BitVec 64) (w : ι) (s s' : isa.State) :
    wakeOwnX T w 0 s' [] = wakeOwnX T w 0 s [] :=
  rfl

/-- (`WCompat0.ownMp0`) **main never writes its TCB word as the runtime's**
under `msX`. -/
theorem ownMp0X {ι : Type} (ms : MemSide isa) (T : BitVec 64) (w : ι) (s : isa.State) (L : Loc) (v : Val)
    (hm : (L, v) ∈ wakeOwnX T w 0 s []) : ¬ (msX ms T).mp L true := by
  simp only [wakeOwnX_zero, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  exact fun h => offTcb_self T (h.2 rfl)

/-! ## The location data -/

/-- **The location data with main owning `tcbM`**: `⟨T, 8⟩` main's owned
word; each thread's other footprint words the runtime words `msX` lets it
write (`WakeInst.wakeLocs`' form). -/
def wakeLocsX (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat) (cT : Loc)
    (cS : WeakMem.Address) (ms : MemSide isa) (T : BitVec 64) : WakeLocs where
  lbl := lbl
  lsize := lsize
  cT := cT
  cS := cS
  own i L := i = 0 ∧ L = ⟨T, 8⟩
  priv _ L := (msX ms T).mp L true

/-- **`wakeLocsX`' separation facts**, given `tcbM` outside every placed
label and not the flag's word, and `ms`'s runtime writes outside every
placed label. -/
theorem wakeLocsX_ok {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {cT : Loc}
    {cS : WeakMem.Address} {ms : MemSide isa} {T : BitVec 64}
    (hTl : ¬ InLabel lbl lsize ⟨T, 8⟩) (hcT : cT ≠ ⟨T, 8⟩)
    (hmpl : ∀ L, ms.mp L true → ¬ InLabel lbl lsize L) :
    (wakeLocsX lbl lsize cT cS ms T).OK where
  disj i j l _ _ hij h := by
    rintro ⟨rfl, rfl⟩
    rcases h with ⟨hj, -⟩ | hp
    · exact hij hj.symm
    · exact offTcb_self T (hp.2 rfl)
  own_nlab _ _ _ h := by obtain ⟨-, rfl⟩ := h; exact hTl
  priv_nlab _ _ _ h := hmpl _ h.1
  c_own h := hcT h.2

/-- (`WCompat0.ownCov0`) **main's TCB word is in its cover set** at
`wakeP … (wakeLocsX …)` (`WakeP.wakeP_own_cov`). -/
theorem ownCov0X {I : ISA} {K : Abi I} {μ : Marks} {ι : Type} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {cT : Loc} {cS : WeakMem.Address} {ms : MemSide isa} (T : BitVec 64)
    (w : ι) (s : isa.State) (L : Loc) (v : Val) (hm : (L, v) ∈ wakeOwnX T w 0 s []) :
    (wakeP K μ (wakeLocsX lbl lsize cT cS ms T)).cov 0 L := by
  simp only [wakeOwnX_zero, List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨rfl, -⟩ := hm
  exact wakeP_own_cov ⟨rfl, rfl⟩

end Spike.Lib.X64WakeOwnX

/-- info: 'Spike.Lib.X64WakeOwnX.offTcb_park' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.offTcb_park

/-- info: 'Spike.Lib.X64WakeOwnX.ownMp0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.ownMp0X

/-- info: 'Spike.Lib.X64WakeOwnX.wakeLocsX_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.wakeLocsX_ok

/-- info: 'Spike.Lib.X64WakeOwnX.ownCov0X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeOwnX.ownCov0X

/-
**The child stub's premises from the clone's facts.** The child after the
`clone` (`Spike.Lib.Handover.childAfter`) handed the range `r1` whose top is
`top = r1.lo + r1.size` runs in the region `⟨ofNat top, lo, 0⟩` (no deeper
than `r1`) under the frame `DFrame R m0` for the child's first memory `m0`.
The stub's segment asks of that region and frame:

- `childStub_region`: the region does not wrap, its base is 16-aligned, it
  has at least 128 bytes below the base, nothing above, and the handover's
  own side conditions (`top < 2 ^ 64`, `lo ≤ 0`, `-lo ≤ r1.size`);
- `childStub_hlim`: the stack-limit word `[tpidr_el0, #8]` of a thread
  pointer `tls` is the runtime's, mapped for a read, not in the child's
  private memory under the frame (it lies outside `r1`), and every value
  runtime memory may hold there leaves 80 bytes below `top`.

The `_stk` corollaries instantiate the runtime's layout: `r1` the second
16 KiB half of a 32 KiB stack area at `stk`, `lo = -16384` (the region is
`r1` exactly).
-/
import Spike.Lib.A64Ret0
import Spike.Lib.A64Handover
import Scc.Sem.OwnDom

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow (tcbA)

/-- **The child's first memory** after a `clone` that handed `r1`: the
parent's bytes on `r1`, nothing else. -/
theorem childAfter_dmem {x : KState} {tid : Nat} {t : Thread isaLSE2} {top tls : Nat} {r1 : Range}
    (hh : handed x tid top = some (tid, r1)) :
    (childAfter abi x tid t top tls).st.st.1.dmem = copyRange t.st.st.1.dmem ∅ r1 := by
  unfold childAfter; rw [hh]; rfl

/-- The stack-limit word of a thread pointer `tls`. -/
theorem tcbA_ofNat {r : Reg64s} {tls : Nat} (h : r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls) :
    tcbA r 8 = BitVec.ofNat 64 (tls + 8) := by
  rw [tcbA, h, show (8 : Int64).toInt = ((8 : Nat) : Int) from rfl, BitVec.ofInt_add, BitVec.ofInt_toInt,
    BitVec.ofInt_natCast, BitVec.ofNat_add]

/-- A first byte outside the copied range: nothing loads there. -/
theorem loadInt_copyRange_none {src : _root_.Mem 64} {r : Range} {a : BitVec 64} (hr : r.lo + r.size ≤ 2 ^ 64)
    (ha : ¬ r.contains a.toNat) {n : Nat} (hn : 0 < n) : Mem.loadInt (copyRange src ∅ r) a n = none := by
  cases hl : Mem.loadInt (copyRange src ∅ r) a n with
  | none => rfl
  | some _ =>
    have h0 := Mem.get?_isSome_of_loadBytes (Mem.loadBytes_isSome_of_loadInt hl) 0 hn
    rw [BitVec.add_zero, Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.mem_iff_isSome_getElem?,
      mem_copyRange, mem_addrs_iff hr] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 ha
    · exact absurd h0 Std.ExtHashMap.not_mem_empty

/-- **The region of the child's stub**: `⟨ofNat top, lo, 0⟩` for the handed
range's top, no deeper than the range. -/
theorem childStub_region {r1 : Range} {lo : Int} (htop : r1.lo + r1.size < 2 ^ 64)
    (hal : (r1.lo + r1.size) % 16 = 0) (hlo : lo ≤ -128) (hsz : -lo ≤ r1.size) :
    let R : Spike.Lib.Region := ⟨BitVec.ofNat 64 (r1.lo + r1.size), lo, 0⟩
    r1.lo + r1.size < 2 ^ 64 ∧ lo ≤ 0 ∧ -lo ≤ r1.size ∧
      R.OK ∧ R.base.toNat % 16 = 0 ∧ R.lo ≤ -128 ∧ 0 ≤ R.hi := by
  intro R
  have hb : R.base.toNat = r1.lo + r1.size := by
    show (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  refine ⟨htop, by omega, hsz, ⟨?_, ?_⟩, by rw [hb]; exact hal, hlo, Int.le_refl 0⟩
  · rw [hb]; show (0 : Int) ≤ ((r1.lo + r1.size : Nat) : Int) + lo; omega
  · rw [hb]; show ((r1.lo + r1.size : Nat) : Int) + 0 ≤ 2 ^ 64; omega

/-- **The stack-limit premise of the child's stub**, for the thread pointer
`tls` and the entry `sp` the handed range's top, under the frame of the
child's first memory. -/
theorem childStub_hlim {ms : MemSide isaLSE2} {x : KState} {tid : Nat} {t : Thread isaLSE2} {r1 : Range}
    {tls : Nat} {lo : Int} (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (htop : r1.lo + r1.size < 2 ^ 64) (hsz : -lo ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8) (h80 : 80 ≤ r1.lo + r1.size)
    (hrt : ms.rt (tls + 8)) (hmp : ms.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, ms.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 80 ≤ r1.lo + r1.size) :
    ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, Spike.Lib.A64.Flow.DFrame ({ base := BitVec.ofNat 64 (r1.lo + r1.size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤
          (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat := by
  intro r hr
  rw [tcbA_ofNat hr]
  have ha : (BitVec.ofNat 64 (tls + 8)).toNat = tls + 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hb : (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = r1.lo + r1.size := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  refine ⟨by rw [ha]; exact hrt, hmp, fun m hF => ?_, fun v hv => ?_⟩
  · rw [hF _ (by omega) (by simp only [hb, ha]; omega), childAfter_dmem hh]
    exact loadInt_copyRange_none (by omega) (by unfold Range.contains; omega) (by decide)
  · have h1 := hG v hv
    have e48 : (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec).toNat = r1.lo + r1.size - 48 := by
      rw [BitVec.toNat_sub, hb, show ((48 : Int64).toBitVec).toNat = 48 from rfl]; omega
    have e80 : (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat =
        r1.lo + r1.size - 80 := by
      rw [BitVec.toNat_sub, e48, show ((32 : Int64).toBitVec).toNat = 32 from rfl]; omega
    rw [e48, e80]; omega

/-! ## The runtime's layout: `r1` the upper half of a 32 KiB area -/

/-- `childStub_region` for `r1 = ⟨stk + 16384, 16384⟩`, `lo = -16384`. -/
theorem childStub_region_stk {r1 : Range} {stk : Nat} (hr1 : r1 = ⟨stk + 16384, 16384⟩) (hal : stk % 16 = 0)
    (hbd : stk + 32768 < 2 ^ 64) :
    let R : Spike.Lib.Region := ⟨BitVec.ofNat 64 (r1.lo + r1.size), -16384, 0⟩
    r1.lo + r1.size < 2 ^ 64 ∧ (-16384 : Int) ≤ 0 ∧ -(-16384 : Int) ≤ r1.size ∧
      R.OK ∧ R.base.toNat % 16 = 0 ∧ R.lo ≤ -128 ∧ 0 ≤ R.hi := by
  have h1 : r1.lo = stk + 16384 := by rw [hr1]
  have h2 : r1.size = 16384 := by rw [hr1]
  exact childStub_region (by omega) (by omega) (by omega) (by omega)

/-- `childStub_hlim` for `r1 = ⟨stk + 16384, 16384⟩`: every value runtime
memory may hold at the limit word is at most `r1`'s base plus 4096 (the
limit `scc_rt_thread_init` writes, `ThreadInit.fields`' second). -/
theorem childStub_hlim_stk {ms : MemSide isaLSE2} {x : KState} {tid : Nat} {t : Thread isaLSE2} {r1 : Range}
    {stk tls : Nat} {lo : Int} (hr1 : r1 = ⟨stk + 16384, 16384⟩)
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (hbd : stk + 32768 < 2 ^ 64)
    (hsz : -lo ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ stk + 16384 ∨ stk + 32768 ≤ tls + 8)
    (hrt : ms.rt (tls + 8)) (hmp : ms.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, ms.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat ≤ stk + 16384 + 4096) :
    ∀ r : Reg64s, r.TPIDR_EL0.toBitVec = BitVec.ofNat 64 tls →
      ms.rt (tcbA r 8).toNat ∧ ms.mp ⟨tcbA r 8, 8⟩ false ∧
      (∀ m, Spike.Lib.A64.Flow.DFrame ({ base := BitVec.ofNat 64 (r1.lo + r1.size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (tcbA r 8) 8 = none) ∧
      ∀ v : Val, ms.G ⟨tcbA r 8, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤
          (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat := by
  have h1 : r1.lo = stk + 16384 := by rw [hr1]
  have h2 : r1.size = 16384 := by rw [hr1]
  exact childStub_hlim hh (by omega) hsz htls (by omega) (by omega) hrt hmp
    fun v hv => by have := hG v hv; omega

end Spike.Lib.A64.Rt

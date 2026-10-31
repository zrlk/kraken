/-
**The child stub's premises from the clone's facts** (x86-64; twin of
`Spike/Lib/Rt/A64RtChildPrem.lean`). The child after the `clone`
(`Spike.Lib.Handover.childAfter`) handed the range `r1` whose top is
`top = r1.lo + r1.size` runs in the region `⟨ofNat top, lo, 0⟩` (no deeper
than `r1`, `Child.childR`) under the frame `DFrame R m0` for the child's
first memory `m0`. The stub's segment asks of that region and frame:

- `childStub_region`: the region does not wrap, it has at least 128 bytes
  below the base, nothing above, and the handover's own side conditions
  (`top < 2 ^ 64`, `lo ≤ 0`, `-lo ≤ r1.size`);
- `childStub_hlim`: the stack-limit word `%fs:8` of a thread pointer `tls`
  is the runtime's, mapped for a read, not in the child's private memory
  under the frame (it lies outside `r1`), and every value runtime memory
  may hold there leaves 80 bytes below `top`.

The `_stk` corollaries instantiate the runtime's layout: `r1` the second
16 KiB half of a 32 KiB stack area at `stk`, `lo = -16384` (the region is
`r1` exactly).

**Unlike AArch64**: the thread pointer is `fsBase` (A64's `TPIDR_EL0`)
and the limit word is `fsBase + 8` (`Ret0.limA`'s shape; A64's
`tcbA r 8`), so `tcbA_ofNat` is stated on `fsBase`; no alignment (`hal`)
premise or conclusion (`seg_child` and the x86-64 prologues take none).
The two room bounds are the same as A64's: the child enters
`scc_rt_thr_worker` at `top - 8`, whose check address is `top - 48`
(`pushq %rbp`, `leaq -32(%rsp)`), and `wc_worker`'s is `top - 80`.
-/
import Spike.Lib.X64Handover
import Spike.Lib.X64Block
import Scc.Sem.OwnDom

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover

/-- **The child's first memory** after a `clone` that handed `r1`: the
parent's bytes on `r1`, nothing else. -/
theorem childAfter_dmem {x : KState} {tid : Nat} {t : Thread isa} {top tls : Nat} {r1 : Range}
    (hh : handed x tid top = some (tid, r1)) :
    (childAfter abi x tid t top tls).st.st.1.dmem = copyRange t.st.st.1.dmem ∅ r1 := by
  unfold childAfter; rw [hh]; rfl

/-- The stack-limit word `%fs:8` of a thread pointer `tls`. -/
theorem tcbA_ofNat {r : Reg64s} {tls : Nat} (h : r.fsBase.toBitVec = BitVec.ofNat 64 tls) :
    r.fsBase.toBitVec + (8 : Int64).toBitVec = BitVec.ofNat 64 (tls + 8) := by
  rw [h, BitVec.ofNat_add]; rfl

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
    (hlo : lo ≤ -128) (hsz : -lo ≤ r1.size) :
    let R : Spike.Lib.Region := ⟨BitVec.ofNat 64 (r1.lo + r1.size), lo, 0⟩
    r1.lo + r1.size < 2 ^ 64 ∧ lo ≤ 0 ∧ -lo ≤ r1.size ∧
      R.OK ∧ R.lo ≤ -128 ∧ 0 ≤ R.hi := by
  intro R
  have hb : R.base.toNat = r1.lo + r1.size := by
    show (BitVec.ofNat 64 (r1.lo + r1.size)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop]
  refine ⟨htop, by omega, hsz, ⟨?_, ?_⟩, hlo, Int.le_refl 0⟩
  · rw [hb]; show (0 : Int) ≤ ((r1.lo + r1.size : Nat) : Int) + lo; omega
  · rw [hb]; show ((r1.lo + r1.size : Nat) : Int) + 0 ≤ 2 ^ 64; omega

/-- **The stack-limit premise of the child's stub**, for the thread pointer
`tls` and the entry `%rsp` the handed range's top, under the frame of the
child's first memory. -/
theorem childStub_hlim {ms : MemSide isa} {x : KState} {tid : Nat} {t : Thread isa} {r1 : Range}
    {tls : Nat} {lo : Int} (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (htop : r1.lo + r1.size < 2 ^ 64) (hsz : -lo ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ r1.lo ∨ r1.lo + r1.size ≤ tls + 8) (h80 : 80 ≤ r1.lo + r1.size)
    (hrt : ms.rt (tls + 8)) (hmp : ms.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, ms.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat + 80 ≤ r1.lo + r1.size) :
    ∀ r : Reg64s, r.fsBase.toBitVec = BitVec.ofNat 64 tls →
      ms.rt (r.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 (r1.lo + r1.size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (r.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
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
theorem childStub_region_stk {r1 : Range} {stk : Nat} (hr1 : r1 = ⟨stk + 16384, 16384⟩)
    (hbd : stk + 32768 < 2 ^ 64) :
    let R : Spike.Lib.Region := ⟨BitVec.ofNat 64 (r1.lo + r1.size), -16384, 0⟩
    r1.lo + r1.size < 2 ^ 64 ∧ (-16384 : Int) ≤ 0 ∧ -(-16384 : Int) ≤ r1.size ∧
      R.OK ∧ R.lo ≤ -128 ∧ 0 ≤ R.hi := by
  have h1 : r1.lo = stk + 16384 := by rw [hr1]
  have h2 : r1.size = 16384 := by rw [hr1]
  exact childStub_region (by omega) (by omega) (by omega)

/-- `childStub_hlim` for `r1 = ⟨stk + 16384, 16384⟩`: every value runtime
memory may hold at the limit word is at most `r1`'s base plus 4096 (the
limit `scc_rt_thread_init` writes, `ThreadInit.fields`' second). -/
theorem childStub_hlim_stk {ms : MemSide isa} {x : KState} {tid : Nat} {t : Thread isa} {r1 : Range}
    {stk tls : Nat} {lo : Int} (hr1 : r1 = ⟨stk + 16384, 16384⟩)
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1)) (hbd : stk + 32768 < 2 ^ 64)
    (hsz : -lo ≤ r1.size) (htls : tls + 16 ≤ 2 ^ 64)
    (hout : tls + 16 ≤ stk + 16384 ∨ stk + 32768 ≤ tls + 8)
    (hrt : ms.rt (tls + 8)) (hmp : ms.mp ⟨BitVec.ofNat 64 (tls + 8), 8⟩ false)
    (hG : ∀ v : Val, ms.G ⟨BitVec.ofNat 64 (tls + 8), 8⟩ v → (v.setWidth 64).toNat ≤ stk + 16384 + 4096) :
    ∀ r : Reg64s, r.fsBase.toBitVec = BitVec.ofNat 64 tls →
      ms.rt (r.fsBase.toBitVec + (8 : Int64).toBitVec).toNat ∧
      ms.mp ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ false ∧
      (∀ m, Spike.Lib.X64.DFrame ({ base := BitVec.ofNat 64 (r1.lo + r1.size), lo := lo, hi := 0 } : Spike.Lib.Region)
          (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1 m →
        Mem.loadInt m.dmem (r.fsBase.toBitVec + (8 : Int64).toBitVec) 8 = none) ∧
      ∀ v : Val, ms.G ⟨r.fsBase.toBitVec + (8 : Int64).toBitVec, 8⟩ v →
        (v.setWidth 64).toNat ≤ (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec).toNat ∧
        (v.setWidth 64).toNat ≤
          (BitVec.ofNat 64 (r1.lo + r1.size) - (48 : Int64).toBitVec - (32 : Int64).toBitVec).toNat := by
  have h1 : r1.lo = stk + 16384 := by rw [hr1]
  have h2 : r1.size = 16384 := by rw [hr1]
  exact childStub_hlim hh (by omega) hsz htls (by omega) (by omega) hrt hmp
    fun v hv => by have := hG v hv; omega

end Spike.Lib.X64.Rt

/-- info: 'Spike.Lib.X64.Rt.childAfter_dmem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.childAfter_dmem

/-- info: 'Spike.Lib.X64.Rt.tcbA_ofNat' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.tcbA_ofNat

/-- info: 'Spike.Lib.X64.Rt.loadInt_copyRange_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.loadInt_copyRange_none

/-- info: 'Spike.Lib.X64.Rt.childStub_region' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.childStub_region

/-- info: 'Spike.Lib.X64.Rt.childStub_hlim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.childStub_hlim

/-- info: 'Spike.Lib.X64.Rt.childStub_region_stk' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.childStub_region_stk

/-- info: 'Spike.Lib.X64.Rt.childStub_hlim_stk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.childStub_hlim_stk

/-
**wake.w on x86-64: the child after the `clone` is at its node** (the twin
of `Spike/Lib/A64WakeChildAt.lean`'s `child_at`): the thread `childAfter`
gives (`Spike.Lib.X64Handover.child_st`: `retRegs64 … 0` with `%rsp` the
handed stack's top and `fsBase` the TLS, the handed range `r1` copied into
its empty private memory) is in the fragment `At … (childN …)` of
`Spike.Lib.X64.WakePh.Child`, so `seg_child` runs it.

The region is the handed stack's top `r1.lo + r1.size` with offsets
`[lo, 0)` (`childR`), `lo ≤ 0` no deeper than the range; every word of it is
mapped (the handed bytes), and the frame condition is the child's first
memory outside the region (`DFrame`). The worker's words are the parent's
`%r12`/`%rbx` (the `syscall` writes `%rax`, `%rcx`, `%r11` only), the thread
pointer `tls`, `%rsp` the top.

- `childR`: the child's region (A64's, restated: that one lives in an
  AArch64 module).
- `loadInt_copyRange`: a word inside the copied range is mapped (likewise).
- `child_at`: the child after a `clone` whose stack range is handed is at
  `childN`.
-/
import Spike.Lib.X64WakeChild
import Spike.Lib.X64Handover
import Scc.Sem.SysX64
import Scc.Sem.OwnDom

namespace Spike.Lib.X64.WakePh.Child

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (x21L svcB)

/-- **The child's region**: offsets `[lo, 0)` below the stack top `top`. -/
def childR (top : Nat) (lo : Int) : Region := ⟨BitVec.ofNat 64 top, lo, 0⟩

/-- **A word inside the copied range is mapped.** -/
theorem loadInt_copyRange {src : _root_.Mem 64} {r : Range} {a : BitVec 64} (hr : r.lo + r.size ≤ 2 ^ 64)
    (h1 : r.lo ≤ a.toNat) (h2 : a.toNat + 8 ≤ r.lo + r.size) :
    (Mem.loadInt (copyRange src ∅ r) a 8).isSome = true := by
  simp only [Mem.loadInt, Option.isSome_map, Mem.loadBytes, List.allSome_isSome_iff, List.forall_mem_map,
    List.mem_range]
  intro i hi
  rw [Std.ExtHashMap.get?_eq_getElem?, ← Std.ExtHashMap.mem_iff_isSome_getElem?, mem_copyRange]
  refine .inl ((mem_addrs_iff hr _).mpr ?_)
  have ha := a.isLt
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  unfold Range.contains
  omega

/-- **The child after the `clone` is at its node**: a thread `t` at the
clone's `syscall` (`.x21 + 46`, a 2-byte cell there: `hcode`), whose stack
top `r1.lo + r1.size` ends the handed range `r1`, gives a child in `At` of
`childN` for the region `childR` (no deeper than `r1`), the frame condition
its first memory outside the region, the worker's words the parent's
`%r12`/`%rbx`, the thread pointer `tls`, `%rsp` the top, any source control
`cW`. -/
theorem child_at {exe : _root_.Executable} {endPc : Int64} {x : KState} {tid : Nat}
    {t : Thread isa} {r1 : Range} {tls : Nat} {lo : Int} {cW : Ctl}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s ((_root_.Executable.labels exe).label x21L + 46) svcB)
    (he : t.st.exe = exe) (hn : t.st.endPc = endPc) (hd : t.st.decls = {})
    (hpc : t.st.st.2 = (_root_.Executable.labels exe).label x21L + 46)
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (htop : r1.lo + r1.size < 2 ^ 64) (_hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) :
    At exe endPc (childR (r1.lo + r1.size) lo)
      (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1)
      (childN (_root_.Executable.labels exe).label cW (t.st.st.1.regs.get64 .r12)
        (t.st.st.1.regs.get64 .rbx) (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
      (childAfter abi x tid t (r1.lo + r1.size) tls).st cW := by
  have hc : (childAfter abi x tid t (r1.lo + r1.size) tls).st =
      { t.st with
        st := (({ t.st.st.1 with
                  regs := ({ retRegs64 t.st 0 with
                    rsp := UInt64.ofNat (r1.lo + r1.size), fsBase := UInt64.ofNat tls } : Reg64s)
                  dmem := copyRange t.st.st.1.dmem ∅ r1 } : MachineData), nextPc t.st) } := by
    unfold childAfter; rw [hh]; rfl
  have hcell : CellAt t.st (op64 .syscall) 2 := (hcode t.st he hn).cell0 rfl rfl hpc
  have hnext := nextPc_of_cellAt hcell
  rw [hc]
  refine ⟨he, hn, hd, ?_, ⟨_, _, _, fun k => BitVec.ofInt 64 ((Mem.loadInt (copyRange t.st.st.1.dmem ∅ r1)
    ((childR (r1.lo + r1.size) lo).addr k) 8).getD 0)⟩, ⟨rfl, rfl, rfl, ?_, ?_⟩, DFrame.refl _ _, ?_⟩
  · show nextPc t.st = _
    rw [hnext, hpc, Int64.add_assoc]; rfl
  · intro r k h
    by_cases hr : r = .rsp
    · subst hr
      simp only [SO.get, childN, oC, ite_true, Option.some.injEq] at h
      subst h
      show (UInt64.ofNat _).toBitVec = BitVec.ofNat 64 _ + BitVec.ofInt 64 0
      exact (BitVec.add_zero _).symm
    · simp [SO.get, childN, oC, lk, hr] at h
  · intro k hk
    obtain ⟨-, hk1, hk2⟩ := hk
    have hR : (childR (r1.lo + r1.size) lo).OK := ⟨by simp [childR]; omega, by simp [childR]; omega⟩
    have ha := Region.addr_toNat_of hR (k := k) hk1 (by simp [childR] at hk2 ⊢; omega)
    simp only [childR, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htop] at ha hk1 hk2
    have hs := loadInt_copyRange (src := t.st.st.1.dmem) (r := r1)
      (a := (childR (r1.lo + r1.size) lo).addr k) (by omega) (by simp only [childR] at *; omega)
      (by simp only [childR] at *; omega)
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨j, hj, by simp [hj]⟩
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- info: 'Spike.Lib.X64.WakePh.Child.child_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms child_at

end Spike.Lib.X64.WakePh.Child

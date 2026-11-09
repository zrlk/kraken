/-
**hello.w on x86-64: the child after the `clone` is at the stub's node** (the twin of
`Spike/Lib/A64HelloChildAt.lean`; wake's x86-64 version is `Spike/Lib/X64WakeChildAt.lean`): the thread
`childAfter` gives (`Spike.Lib.X64Handover.child_st`: `retRegs64 … 0` with `%rsp` the handed stack's top and
`fsBase` the TLS, the handed range `r1` copied into its empty private memory) is in the fragment
`At … (childN …)` of `Spike.Lib.X64.Flow.Worker.Hello.Child`, so `seg_child` runs it.

The region is wake's `childR` (the handed stack's top, offsets `[lo, 0)`); every word of it is mapped
(`WakePh.Child.loadInt_copyRange`), and the frame condition is the child's first memory outside the region
(`DFrame`). The worker's six words are the parent's `%r12, %rbx, %r13, %r14, %r15, %r9` (the slice's four words,
the cell, main's word; the `syscall` writes `%rax`, `%rcx`, `%r11` only), the thread pointer `tls`, `%rsp` the
top.

- `hello_svcIn`: the clone's `syscall` in hello's cells, at `.Lwc_main.x3 + 94`.
- `child_atH`: the child after a `clone` (at any pc `q` holding the `syscall`) whose stack range is handed is
  at `childN`.

## Differences from the AArch64 version

- The `syscall` is the 25th cell after `.Lwc_main.x3`, 94 bytes on (A64's `svc`, 25 instructions past
  `.sp6`); `childN`'s pc is `q + 2` (A64's `q + 4`); the labels are the listing's own (no `pfx`).
- The words are read from `%r12, %rbx, %r13, %r14, %r15, %r9` (A64's `x9 .. x14`); the child's registers are
  `retRegs64` with `%rsp` and `fsBase` set (A64's `X0`, `SP`, `TPIDR_EL0`).
- A64's `clonePreH_child_at` is dead and not twinned.
-/
import Spike.Lib.X64HelloChild
import Spike.Lib.X64WakeChildAt
import Spike.Lib.X64HelloWcSp6

namespace Spike.Lib.X64.Flow.Worker.Hello.Child

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Scc.Cert.Rt.X64 (Lays endOf blockAt)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (svcB)
open Spike.Lib.X64.WakePh.Child (childR loadInt_copyRange)
open SccCode (helloCells)

/-- The clone's `syscall` in hello's cells, 24 cells and 94 bytes past `.x25`. -/
theorem hello_svcIn : blockAt helloCells x25L 24 94 svcB = true := by
  have h := Spike.Lib.X64.HelloPh.WcSp6.hello_wcSp6InH
  simp only [Spike.Lib.X64.HelloPh.WcSp6.wcSp6InH, Bool.and_eq_true] at h
  exact h.2

/-- **The child after the `clone` is at the stub's node**: a thread `t` at the clone's `syscall` (pc `q`, a
2-byte cell there: `hcode`; `childN`'s pc is `q + 2`: `hq`), whose stack top `r1.lo + r1.size` ends the handed
range `r1`, gives a child in `At` of `childN` for the region `childR` (no deeper than `r1`), the frame condition
its first memory outside the region, the worker's words the parent's `%r12, %rbx, %r13, %r14, %r15, %r9`, the
thread pointer `tls`, `%rsp` the top, any source control `cW`. -/
theorem child_atH {exe : _root_.Executable} {endPc : Int64} {q : Int64} {x : KState}
    {tid : Nat} {t : Thread isa} {r1 : Range} {tls : Nat} {lo : Int} {cW : Ctl}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q svcB)
    (hq : (_root_.Executable.labels exe).label x25L + 94 = q)
    (he : t.st.exe = exe) (hn : t.st.endPc = endPc) (hd : t.st.decls = {})
    (hpc : t.st.st.2 = q)
    (hh : handed x tid (r1.lo + r1.size) = some (tid, r1))
    (htop : r1.lo + r1.size < 2 ^ 64) (_hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) :
    At exe endPc (childR (r1.lo + r1.size) lo)
      (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi x tid t (r1.lo + r1.size) tls).st.st.1)
      (childN (_root_.Executable.labels exe).label cW
        ⟨t.st.st.1.regs.get64 .r12, t.st.st.1.regs.get64 .rbx, t.st.st.1.regs.get64 .r13,
          t.st.st.1.regs.get64 .r14, t.st.st.1.regs.get64 .r15, t.st.st.1.regs.get64 .r9⟩
        (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
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
    rw [hnext, hpc, ← hq, Int64.add_assoc]; rfl
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
  · exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

end Spike.Lib.X64.Flow.Worker.Hello.Child

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Child.hello_svcIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Child.hello_svcIn

/-- info: 'Spike.Lib.X64.Flow.Worker.Hello.Child.child_atH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.Worker.Hello.Child.child_atH

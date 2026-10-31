/-
**wake.w on x86-64: both halves of the spawn from main's `ClonePre`** (the
twins of `A64WakeParentAt`'s `parent_at_preR` / `parent_at_pre` and
`A64WakeChildAt`'s `clonePre_child_at`): in a layout of wake.w's x64 cells
(`hp : Lays exe SccCode.wakeCells kp`), main's state at its `clone`
(`X64WakePreA.ClonePre`) gives the parent at `pN .ts` and the child at
`childN` once the clone hands `r1`.

The clone's `syscall` is `wcCloneIn`'s last block (`wake_wcCloneIn`).
Main's region is `wc_main`'s frame, base `%rbp = %rsp + 64` (`hRb`), offsets
within `[-64, 16]` (the 64 bytes below `%rbp`, then the saved `%rbp` and the
return address: `hRlo`, `hRhi`), so the 80 bytes at `%rsp` that
`ClonePre.frame` puts in `r0`.

- `wake_svcCode`: the clone's `syscall` at `cloneAt`.
- `parent_at_preR`, `parent_at_pre`: the parent at `pN .ts`.
- `clonePre_child_at`: the child at `childN`, the worker's words `cA`/`meW`.
-/
import Spike.Lib.X64WakeParentAt
import Spike.Lib.X64WakeChildAt
import Spike.Lib.X64WakePreA
import Spike.Lib.X64WakeCloneIn

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (oW x21L svcB wcCloneIn)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays)

/-- **The clone's `syscall` is at `cloneAt`** in a layout of wake.w's cells. -/
theorem wake_svcCode {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
    (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s ((_root_.Executable.labels exe).label x21L + 46) svcB := by
  have h := wake_wcCloneIn
  simp only [wcCloneIn, Bool.and_eq_true] at h
  exact fun s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h.2

namespace Parent

/-- **The parent after main's `clone` is at `pN .ts`**, for any region
inside main's stack range `r0` (`hin`; `r1` is off `r0`: `ClonePre.disj`). -/
theorem parent_at_preR {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    {R : Region} {F : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP)
    (hin : (r0.lo : Int) ≤ R.base.toNat + R.lo ∧ (R.base.toNat : Int) + R.hi ≤ r0.lo + r0.size)
    (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧
      At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1)
        (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hd := h.disj
  obtain ⟨th, hth, -, -⟩ := h.frame
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hh, -⟩ := h
    simp [handed, hh]
  exact ⟨th, hth, parent_at (wake_svcCode hp hend) (hat th hth) hh htop hR
    (regionDisj_of_sub hd hin.1 hin.2 hlh) hr0 hrm⟩

/-- **The parent after main's `clone` is at `pN .ts`** (wake's layout `hp`):
main's state at the clone (`ClonePre`) whose thread `th` is in `At` of the
clone's node with `JS` (`hat`), for a region of `wc_main`'s frame: base
`%rsp + 64` (`hRb`), offsets within `[-64, 16]` (`hRlo`, `hRhi`). Once the
clone hands `r1` and the kernel returns the child's id `0 < r < pidMax`,
`th` is in `At` of `pN .ts` with the frame condition its memory outside the
region. -/
theorem parent_at_pre {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    {R : Region} {F : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64)
    (hRlo : -64 ≤ R.lo) (hRhi : R.hi ≤ 16) (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧
      At exe endPc R (DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1)
        (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  obtain ⟨th, hth, hf0, hf1⟩ := h.frame
  have hb := hRb th hth
  exact parent_at_preR hp hend h hat ⟨by omega, by omega⟩ hlh hR htop hr0 hrm

end Parent

namespace Child

/-- **The child after main's `clone` is at `childN`** (wake's layout `hp`):
main's state at the clone (`ClonePre`; `hX`: its runtime facts pin the
executable, its end and no declarations) gives the child, after the clone
hands it `r1`, in `At` of `childN` for `childR` (no deeper than `r1`), with
`cA`/`meW`/`tls` `ClonePre`'s. -/
theorem clonePre_child_at {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (htop : r1.lo + r1.size < 2 ^ 64) {lo : Int} (hlo : lo ≤ 0) (hsz : -lo ≤ r1.size) (cW : Ctl) :
    ∃ (th : Thread isa) (tls cA meW : Nat), t.1.threads = #[th] ∧
      callOf abi th = some (.clone (r1.lo + r1.size) tls) ∧
      At exe endPc (childR (r1.lo + r1.size) lo)
        (DFrame (childR (r1.lo + r1.size) lo) (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st.st.1)
        (childN (_root_.Executable.labels exe).label cW (BitVec.ofNat 64 cA) (BitVec.ofNat 64 meW)
          (BitVec.ofNat 64 tls) (BitVec.ofNat 64 (r1.lo + r1.size)))
        (childAfter abi t.2 0 th (r1.lo + r1.size) tls).st cW := by
  obtain ⟨th, -, tls, cA, meW, -, hth, -, hpc, -, -, hcall, -, -, h12, hbx, hheld, -, -, -, hXs, -⟩ := h
  obtain ⟨he, hn, hd⟩ := hX _ hXs
  have hh : handed t.2 0 (r1.lo + r1.size) = some (0, r1) := by
    simp [handed, hheld]
  have h12' : th.st.st.1.regs.get64 .r12 = BitVec.ofNat 64 cA := by
    subst h12; simp
  have hbx' : th.st.st.1.regs.get64 .rbx = BitVec.ofNat 64 meW := by
    subst hbx; simp
  refine ⟨th, tls, cA, meW, hth, hcall, ?_⟩
  rw [← h12', ← hbx']
  exact child_at (wake_svcCode hp hend) he hn hd (he ▸ hpc) hh htop hlo hsz

end Child

/-- info: 'Spike.Lib.X64.WakePh.wake_svcCode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wake_svcCode

/-- info: 'Spike.Lib.X64.WakePh.Parent.parent_at_preR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Parent.parent_at_preR

/-- info: 'Spike.Lib.X64.WakePh.Parent.parent_at_pre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Parent.parent_at_pre

/-- info: 'Spike.Lib.X64.WakePh.Child.clonePre_child_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Child.clonePre_child_at

end Spike.Lib.X64.WakePh

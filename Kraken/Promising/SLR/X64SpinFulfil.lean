/-
Which instruction of the x64 spinlock worker (`X64SpinTrees.spinWorker`) can
fulfil an outstanding promise with a release store, leaving no promise dead
(`Thread.RelFulfilsLive`, `NPSafe`'s prepay conjunct): the x64 twin of
`SwpPrepay.relFulfils_pos`.

Under `Arch.tso` every store is a release, so unlike the AArch64 worker
(where only the unlock `stlr` qualifies) three cells can fulfil:

- the swap `xchgl %eax,(%rdi)` (position 5), with the message `(Lk, %eax)`;
- the counter store `movl %ecx,(%rsi)` (position 10), with `(C, %ecx)`;
- the unlock `movl $0,(%rdi)` (position 11), with `(Lk, 0)`.

In each case every other outstanding promise at the same location lies above
`ts` (`writeSuccs_fulfil_live`); for the two plain stores the write is also
above the thread's `coh` of the location and `vwOld` (`WriteOk`). The lemma is
stated for an arbitrary `Arch`; the store kinds only restrict which of the
three cases occur.
-/
import Kraken.Promising.SLR.X64SpinCells
import Kraken.Promising.SLR.X64SpinNoNT
import Kraken.Promising.SLR.SpinRelease

namespace Kraken.Promising.SLR.X64SpinInv

open Kraken Kraken.Promising Kraken.Promising.X64
open Kraken.Promising.SLR.Spinlock
open Kraken.Promising.SLR.SpinCommon
open Kraken.Promising.SLR.X64SpinTrees

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinWorker)]

/-- The facts of a live fulfilment of `ts` by a write of `(l, v)` against the
memory `mem`, with outstanding promises `prom`: the message at `ts`, and the
other promises at `l` above `ts`. -/
def LiveFulfil (prom : List Time) (mem : Memory) (l : Loc) (v : Val) (ts : Time) : Prop :=
  (∃ w, mem.get? ts = some w ∧ w.loc = l ∧ w.val = v) ∧
    ∀ p ∈ prom, p ≠ ts → ∀ w, mem.get? p = some w → w.loc = l → ts < p

/-- **The fulfilling instructions** of the worker (see the module doc). -/
theorem relFulfils_pos {P : Params} {A : Arch} {tid : Nat} {t : Thread isa} {mem : Memory} {ts : Time} {i : Nat}
    (hF : Frame P t.st) (hp : AtPos t.st i)
    (hi : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨
      i = 12 ∨ i = 14)
    (hb : ∀ p ∈ t.prom, p ≤ mem.last) (h : t.RelFulfilsLive A tid ts mem) :
    (i = 5 ∧ A.storeKind (A.rmwKind .acqRel).storeKind = .rel ∧
        LiveFulfil t.prom mem P.Lk (BitVec.setWidth 128 (eaxOf t.st)) ts) ∨
      (i = 10 ∧ A.storeKind .plain = .rel ∧ LiveFulfil t.prom mem P.C (BitVec.setWidth 128 (ecxOf t.st)) ts ∧
        t.views.getCoh P.C < ts ∧ t.views.vwOld < ts) ∨
      (i = 11 ∧ A.storeKind .plain = .rel ∧ LiveFulfil t.prom mem P.Lk 0#128 ts ∧
        t.views.getCoh P.Lk < ts ∧ t.views.vwOld < ts) := by
  obtain ⟨tree, hex, hrf⟩ := h
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_load_lock t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hex; cases hex
    simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_test t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_jne_spin t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_mov_one t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_xchg t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hex; cases hex
    simp only [EvTree.RelFulfilsLive, or_false, false_or, Option.some.injEq, exists_eq_left'] at hrf
    obtain ⟨x, hx, c', hc, ⟨hk, hin, hout⟩, hnd⟩ := hrf
    have hmp : x.2.2.mem = mem ∧ x.2.2.prom = t.prom := by
      rw [(readSuccs_memProm A _ hx).1, (readSuccs_memProm A _ hx).2]
      split <;> exact ⟨rfl, rfl⟩
    have hb' : ∀ p ∈ x.2.2.prom, p ≤ x.2.2.mem.last := by rw [hmp.1, hmp.2]; exact hb
    obtain ⟨hmsg, -, hlive⟩ := writeSuccs_fulfil_live hc hb' hin hout hnd
    rw [hmp.1, hmp.2] at hlive
    rw [hmp.1] at hmsg
    exact .inl ⟨rfl, hk, hmsg, hlive⟩
  · rw [exec_test2 t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_jne_retry t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_load_counter t.st (hF.at hp (by decide)) hF.rsi hF.dc] at hex; cases hex
    simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_add t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_store_counter t.st (hF.at hp (by decide)) hF.rsi hF.dc] at hex; cases hex
    simp only [EvTree.RelFulfilsLive, or_false] at hrf
    obtain ⟨cx', hc, ⟨hk, hin, hout⟩, hnd⟩ := hrf
    obtain ⟨hmsg, hok, hlive⟩ := writeSuccs_fulfil_live hc hb hin hout hnd
    exact .inr (.inl ⟨rfl, hk, ⟨hmsg, hlive⟩,
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1, writeOk_rel_vwOld hk hok⟩)
  · rw [exec_unlock t.st (hF.at hp (by decide)) hF.rdi hF.dl] at hex; cases hex
    simp only [EvTree.RelFulfilsLive, or_false] at hrf
    obtain ⟨cx', hc, ⟨hk, hin, hout⟩, hnd⟩ := hrf
    obtain ⟨hmsg, hok, hlive⟩ := writeSuccs_fulfil_live hc hb hin hout hnd
    exact .inr (.inr ⟨rfl, hk, ⟨hmsg, hlive⟩,
      Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hok.1, writeOk_rel_vwOld hk hok⟩)
  · rw [exec_jmp_done t.st (hF.at hp (by decide))] at hex; cases hex; simp [EvTree.RelFulfilsLive] at hrf
  · rw [exec_end t.st hF.exe hp] at hex; cases hex

end Kraken.Promising.SLR.X64SpinInv

/-
**Stage 3: the ticket part of a ticket lock's
liveness invariant, generic in the ISA, the lock and its ticket predicate.**
ISA-neutral.

Every ticket lock's `InvW` (`LiveTicketInv` for AArch64, `LiveX64TicketInv`
and `LiveX64Ticket2Inv` for x64) carries the same four facts about the tickets
taken, for a ticket predicate `Ticketed`, the ticket `tk` of a ticketed thread
and the location `XL` of `next` with `xc` tickets taken (`TkFacts`):

- `xmsg`: every message of `XL` was written by a ticketed thread;
- `tkLt`, `tkInj`, `tkSurj`: the tickets of the ticketed threads are exactly
  `0, …, xc - 1`, each held once.

`TkFacts.frame`: a step of `tid` that keeps its ticket and writes no `XL`
message keeps them (the per-lock `tk_frame`). `TkFacts.take`: a step of an
unticketed `tid` that takes ticket `xc` and appends the `XL` message keeps
them at `xc + 1`, and `xc + 1` is at most the number of threads (pigeonhole;
the ticket half of the per-lock `inv_tkt`).
-/
import Kraken.Promising.LiveSpinCommon

namespace Kraken.Promising.Live.TicketGlobal

open Kraken.Promising Kraken.Promising.Live Kraken.Promising.Live.SpinStep

variable {I : ISA} (Ticketed : Thread I → Prop) (tk : Thread I → Nat) (XL : Loc)

/-- **The ticket facts** of a configuration with `xc` tickets taken. -/
structure TkFacts (xc : Nat) (cfg : Config I) : Prop where
  xmsg : ∀ ts w, cfg.mem.get? ts = some w → w.loc = XL → ∃ tw, cfg.threads[w.tid]? = some tw ∧ Ticketed tw
  tkLt : ∀ (i : Nat) t, cfg.threads[i]? = some t → Ticketed t → tk t < xc
  tkInj : ∀ (i j : Nat) ti tj, cfg.threads[i]? = some ti → cfg.threads[j]? = some tj → Ticketed ti → Ticketed tj →
    tk ti = tk tj → i = j
  tkSurj : ∀ k < xc, ∃ i : Nat, ∃ t, cfg.threads[i]? = some t ∧ Ticketed t ∧ tk t = k

variable {Ticketed tk XL} {xc tid : Nat} {cfg : Config I} {t t' : Thread I} {mem' : Memory}

/-- **The ticket facts after a step that keeps the thread's ticket** and
writes no message of `XL`. -/
theorem TkFacts.frame (h : TkFacts Ticketed tk XL xc cfg) (ht : cfg.threads[tid]? = some t)
    (htk : Ticketed t' ↔ Ticketed t) (hk : Ticketed t → tk t' = tk t)
    (hm4 : ∀ ts w, mem'.get? ts = some w → w.loc = XL → cfg.mem.get? ts = some w) :
    TkFacts Ticketed tk XL xc (cfg.withThread tid t' mem') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ts w hw hl
    obtain ⟨tw, h1, h2⟩ := h.xmsg ts w (hm4 ts w hw hl) hl
    by_cases e : w.tid = tid
    · rw [e] at h1 ⊢; rw [ht] at h1; cases h1; exact ⟨t', wt_tid ht, htk.mpr h2⟩
    · exact ⟨tw, by rw [wt_ne ht e]; exact h1, h2⟩
  · intro i u hu hk'
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · rw [hk (htk.mp hk')]; exact h.tkLt tid t ht (htk.mp hk')
    · exact h.tkLt i u hu hk'
  · intro i j ti tj hi hj hti htj e
    rcases wt_get ht hi with ⟨rfl, rfl⟩ | ⟨-, hi2⟩ <;> rcases wt_get ht hj with ⟨rfl, rfl⟩ | ⟨-, hj2⟩
    · rfl
    · exact h.tkInj _ _ _ _ ht hj2 (htk.mp hti) htj (by rw [← hk (htk.mp hti)]; exact e)
    · exact h.tkInj _ _ _ _ hi2 ht hti (htk.mp htj) (by rw [← hk (htk.mp htj)]; exact e)
    · exact h.tkInj _ _ _ _ hi2 hj2 hti htj e
  · intro k hk'
    obtain ⟨i, u, hu, h1, h2⟩ := h.tkSurj k hk'
    by_cases e : i = tid
    · subst e; rw [ht] at hu; cases hu
      exact ⟨i, t', wt_tid ht, htk.mpr h1, by rw [hk h1]; exact h2⟩
    · exact ⟨i, u, by rw [wt_ne ht e]; exact hu, h1, h2⟩

/-- **Taking ticket `xc`**: an unticketed thread becomes ticketed with ticket
`xc` and appends a message of `XL`. The ticket facts hold at `xc + 1`, and
the `xc + 1` holders are distinct threads. -/
theorem TkFacts.take (h : TkFacts Ticketed tk XL xc cfg) (ht : cfg.threads[tid]? = some t) (v : Val)
    (h0 : ¬ Ticketed t) (h1 : Ticketed t') (hk : tk t' = xc) :
    xc + 1 ≤ cfg.threads.size ∧
      TkFacts Ticketed tk XL (xc + 1) (cfg.withThread tid t' (cfg.mem.append { loc := XL, val := v, tid }).1) := by
  have hother : ∀ i u, cfg.threads[i]? = some u → Ticketed u → i ≠ tid := fun i u hu hu' e => by
    subst e; rw [ht] at hu; cases hu; exact h0 hu'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- pigeonhole: the holders of `0, …, xc - 1` and `tid` are `xc + 1` distinct threads
    have hch : ∀ k, k < xc → ∃ i, i ≠ tid ∧ i < cfg.threads.size ∧
        ∃ u, cfg.threads[i]? = some u ∧ Ticketed u ∧ tk u = k := fun k hk' => by
      obtain ⟨i, u, hu, h1, h2⟩ := h.tkSurj k hk'
      exact ⟨i, hother i u hu h1, lt_size_of_get? hu, u, hu, h1, h2⟩
    obtain ⟨g, hg⟩ := Classical.skolem.mp (fun k => (Classical.em (k < xc)).elim
      (fun hk' => (hch k hk').imp fun i hi => fun _ => hi) (fun hk' => ⟨0, fun h => absurd h hk'⟩))
    exact SpinCommon.pigeon cfg.threads.size (xc + 1) (fun k => if k < xc then g k else tid)
      (fun k hk' => by
        split
        · exact (hg k ‹_›).2.1
        · exact lt_size_of_get? ht)
      (fun i j hi hj e => by
        split at e <;> split at e
        · obtain ⟨-, -, u, hu, -, hku⟩ := hg i ‹_›
          obtain ⟨-, -, u', hu', -, hku'⟩ := hg j ‹_›
          rw [e] at hu; rw [hu] at hu'; cases hu'; omega
        · exact absurd e (hg i ‹_›).1
        · exact absurd e.symm (hg j ‹_›).1
        · omega)
  · intro ts w hw hl
    rcases cfg.mem.get?_append_eq_some _ hw with ⟨-, hw⟩ | ⟨-, rfl⟩
    · obtain ⟨tw, h1', h2⟩ := h.xmsg ts w hw hl
      exact ⟨tw, by rw [wt_ne ht (hother _ _ h1' h2)]; exact h1', h2⟩
    · exact ⟨t', wt_tid ht, h1⟩
  · intro i u hu hk'
    rcases wt_get ht hu with ⟨-, rfl⟩ | ⟨-, hu⟩
    · omega
    · have := h.tkLt i u hu hk'; omega
  · intro i j ti tj hi hj hti htj e
    rcases wt_get ht hi with ⟨rfl, rfl⟩ | ⟨-, hi2⟩ <;> rcases wt_get ht hj with ⟨rfl, rfl⟩ | ⟨-, hj2⟩
    · rfl
    · have := h.tkLt _ _ hj2 htj; omega
    · have := h.tkLt _ _ hi2 hti; omega
    · exact h.tkInj _ _ _ _ hi2 hj2 hti htj e
  · intro k hk'
    by_cases e : k = xc
    · exact ⟨tid, t', wt_tid ht, h1, hk.trans e.symm⟩
    · obtain ⟨i, u, hu, h1', h2⟩ := h.tkSurj k (by omega)
      exact ⟨i, u, by rw [wt_ne ht (hother i u hu h1')]; exact hu, h1', h2⟩

end Kraken.Promising.Live.TicketGlobal

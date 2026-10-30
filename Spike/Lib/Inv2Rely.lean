/-
**Rely stability of the two-thread relation** (design note
0.7 (O2)–(O4)). ISA-generic. A message of thread `j` after the spawn goes to
`j`'s footprint (`post_foot`), which is outside the other thread's cover set
(`foot_cov`), hence outside its owned words (`own_cov`) and the frozen words
(`frz_cov`). So thread `i`'s facts in `Inv2Core` that mention only the
memory at `i`'s cover set survive any message of `j`:

- `CohCoversL.append_out`: the location-restricted cover is kept by a
  message outside the location set (store, promise or the source of a
  fulfilment of the other thread);
- `CohCoversL.append_own`: the thread's own append with its coherence view
  at the location raised to the new timestamp (a store, cf.
  `CohCovers.append`);
- `CohCoversL.promise`: the thread's own promise (the new timestamp is
  promised);
- `TLatestP.append_out`, `OwnVal.append_out`, `OwnOk.append_out`: the owned
  words keep their values under a message to another location;
- `Inv2Core.not_cov_of_foot`, `not_frz_of_foot`, `own_ne_of_foot`: a
  location in thread `j`'s footprint is outside thread `i`'s cover set
  (`i ≠ j`), outside the frozen words, and no owned word of `i`;
- `Inv2Core.frzT_append`, `pre_tid_append`, `post_foot_append`,
  `prom_append`: the memory-only fields of the core for the appended
  memory (a message of thread `j` in its footprint);
- `scov_push`, `frzS_push`: the source side, a pushed message outside the
  frozen source words.

The per-thread facts of the stepping thread (its own cover, owned words,
promises) and the memory relation are the rows' (1.6).
-/
import Spike.Lib.Inv2Core

namespace Spike.Lib.Inv2Rely

open Kraken.Promising Scc.Sem Spike.Lib.Inv2Core

/-! ## Appended memories -/

/-- An old timestamp of an appended memory is at most the old `last`. -/
theorem le_last_of_ne {tm : Memory} {w w' : Msg} {k : Nat} (hk : (tm.append w).1.get? k = some w')
    (hne : k ≠ tm.last + 1) : k ≤ tm.last :=
  Kraken.Promising.Memory.le_last_of_get? (CohCoversP.get?_append_ne hk hne)

/-- A message of an appended memory is the new one or an old one. -/
theorem get?_append_cases {tm : Memory} {w w' : Msg} {k : Nat} (hk : (tm.append w).1.get? k = some w') :
    (k = tm.last + 1 ∧ w' = w) ∨ (k ≠ tm.last + 1 ∧ tm.get? k = some w') := by
  by_cases he : k = tm.last + 1
  · subst he; rw [Scc.Sem.Memory.get?_append_new] at hk; exact .inl ⟨rfl, (Option.some.inj hk).symm⟩
  · exact .inr ⟨he, CohCoversP.get?_append_ne hk he⟩

/-! ## The cover -/

/-- **A message outside the location set keeps the restricted cover.** -/
theorem CohCoversL.append_out {vs : Views} {prom : List Time} {tm : Memory} {L : Loc → Prop}
    (h : CohCoversL vs prom tm L) {w : Msg} (hw : ¬ L w.loc) : CohCoversL vs prom (tm.append w).1 L := by
  intro k w' hk hl hp
  rcases get?_append_cases hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
  · exact absurd hl hw
  · exact h k w' hk' hl hp

/-- **The thread's own append** with its coherence views raised and the new
message's location covered at the new timestamp keeps the restricted
cover. -/
theorem CohCoversL.append_own {vs vs' : Views} {prom : List Time} {tm : Memory} {L : Loc → Prop}
    (h : CohCoversL vs prom tm L) (hle : ∀ l, vs.getCoh l ≤ vs'.getCoh l) {w : Msg}
    (hw : tm.last + 1 ≤ vs'.getCoh w.loc) : CohCoversL vs' prom (tm.append w).1 L := by
  intro k w' hk hl hp
  rcases get?_append_cases hk with ⟨rfl, rfl⟩ | ⟨-, hk'⟩
  · exact hw
  · exact Nat.le_trans (h k w' hk' hl hp) (hle _)

/-- **The thread's own promise keeps the restricted cover**: the appended
message is promised. -/
theorem CohCoversL.promise {vs : Views} {prom : List Time} {tm : Memory} {L : Loc → Prop}
    (h : CohCoversL vs prom tm L) (w : Msg) :
    CohCoversL vs (prom ++ [(tm.append w).2]) (tm.append w).1 L := by
  intro k w' hk hl hp
  rcases get?_append_cases hk with ⟨rfl, -⟩ | ⟨-, hk'⟩
  · exact absurd (List.mem_append_right _ (List.mem_singleton.mpr rfl)) hp
  · exact h k w' hk' hl fun hm => hp (List.mem_append_left _ hm)

/-- Raising the coherence views keeps the restricted cover. -/
theorem CohCoversL.mono {vs vs' : Views} {prom : List Time} {tm : Memory} {L : Loc → Prop}
    (h : CohCoversL vs prom tm L) (hle : ∀ l, vs.getCoh l ≤ vs'.getCoh l) : CohCoversL vs' prom tm L :=
  fun k w hk hl hp => Nat.le_trans (h k w hk hl hp) (hle w.loc)

/-! ## The owned words -/

/-- **The latest write not promised of a word is kept by a message to
another location.** -/
theorem TLatestP.append_out {tm : Memory} {prom : List Time} {a k : Nat} (h : TLatestP tm prom a k) {w : Msg}
    (hw : w.loc ≠ wordLoc a) : TLatestP (tm.append w).1 prom a k := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, fun k'' w' hlt hg hl => ?_⟩
  · rcases h1 with h0 | ⟨w', hg, hl, hp⟩
    · exact .inl h0
    · exact .inr ⟨w', by rw [Scc.Sem.Memory.get?_append_le (Kraken.Promising.Memory.le_last_of_get? hg)]; exact hg,
        hl, hp⟩
  · rcases get?_append_cases hg with ⟨-, rfl⟩ | ⟨-, hg'⟩
    · exact absurd hl hw
    · exact h2 k'' w' hlt hg' hl

/-- **A word's value is kept by a message to another location.** -/
theorem OwnVal.append_out {tm : Memory} {prom : List Time} {a : Nat} {v : Val} (h : OwnVal tm prom a v) {w : Msg}
    (hw : w.loc ≠ wordLoc a) : OwnVal (tm.append w).1 prom a v := by
  obtain ⟨k, hl, hr⟩ := h
  refine ⟨k, TLatestP.append_out hl hw, ?_⟩
  rcases hl.1 with h0 | ⟨w', hg, -, -⟩
  · subst h0; simpa [Memory.read?, Memory.initVal, Memory.append] using hr
  · rw [Scc.Sem.read?_append_le (Kraken.Promising.Memory.le_last_of_get? hg)]; exact hr

/-- **The owned words keep their values under a message to none of
them.** -/
theorem OwnOk.append_out {own : List (Loc × Val)} {tm : Memory} {prom : List Time}
    (h : Spike.Lib.ExtRows.OwnOk own tm prom) {w : Msg} (hw : ∀ L v, (L, v) ∈ own → w.loc ≠ L) :
    Spike.Lib.ExtRows.OwnOk own (tm.append w).1 prom := by
  intro L v hm
  obtain ⟨hb, hv⟩ := h L v hm
  refine ⟨hb, OwnVal.append_out hv ?_⟩
  rw [← Spike.Lib.ExtRows.loc_wordLoc hb]
  exact hw L v hm

/-! ## The core under a message of the other thread -/

namespace Inv2Core

variable {I : ISA} {Λ : Scc.Sem.Layout} {R : SpawnRec} {P : Inv2Params I} {G : Loc → Val → Prop}
  {own : Nat → List (Loc × Val)} {tm : Memory} {t0 t1 : Thread I} {sm : WeakMem.Memory}
  {s0 s1 : TermRun.TTh} {ts : Nat → Option Nat} {tp sp : List Nat}

/-- (O2, O3) **A location in thread `j`'s footprint is outside the other
thread's cover set.** -/
theorem not_cov_of_foot (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {i j : Nat} {l : Loc}
    (hi : i < 2) (hj : j < 2) (hij : i ≠ j) (hf : P.foot j l) : ¬ P.cov i l :=
  h.foot_cov i j l hi hj hij hf

/-- (3) **A location in a thread's footprint is not frozen**: the frozen
words are in the other thread's cover set. -/
theorem not_frz_of_foot (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {j : Nat} {l : Loc}
    (hj : j < 2) (hf : P.foot j l) : ¬ P.frz l := fun hz =>
  h.foot_cov (1 - j) j l (by omega) hj (by omega) hf (h.frz_cov (1 - j) l (by omega) hz)

/-- (O1, O3) **A location in thread `j`'s footprint is no owned word of the
other thread.** -/
theorem own_ne_of_foot (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {i j : Nat} {l : Loc}
    (hi : i < 2) (hj : j < 2) (hij : i ≠ j) (hf : P.foot j l) : ∀ L v, (L, v) ∈ own i → l ≠ L :=
  fun L v hm he => h.foot_cov i j l hi hj hij hf (he ▸ h.own_cov i L v hi hm)

/-- **Thread `i`'s cover survives a message of thread `j` in `j`'s
footprint.** -/
theorem cov_append {vs : Views} {prom : List Time} {i j : Nat}
    (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) (hc : CohCoversL vs prom tm (P.cov i))
    (hi : i < 2) (hj : j < 2) (hij : i ≠ j) {w : Msg} (hf : P.foot j w.loc) :
    CohCoversL vs prom (tm.append w).1 (P.cov i) :=
  CohCoversL.append_out hc (not_cov_of_foot h hi hj hij hf)

/-- **Thread `i`'s owned words survive a message of thread `j` in `j`'s
footprint.** -/
theorem own_append {prom : List Time} {i j : Nat}
    (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) (ho : Spike.Lib.ExtRows.OwnOk (own i) tm prom)
    (hi : i < 2) (hj : j < 2) (hij : i ≠ j) {w : Msg} (hf : P.foot j w.loc) :
    Spike.Lib.ExtRows.OwnOk (own i) (tm.append w).1 prom :=
  OwnOk.append_out ho (own_ne_of_foot h hi hj hij hf)

/-- (3) **No frozen message after the spawn**, for the appended memory (a
message in a footprint). -/
theorem frzT_append (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {w : Msg} (hj : w.tid < 2)
    (hf : P.foot w.tid w.loc) : ∀ k w', (tm.append w).1.get? k = some w' → R.T < k → ¬ P.frz w'.loc := by
  intro k w' hk hT
  rcases get?_append_cases hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
  · exact not_frz_of_foot h hj hf
  · exact h.frzT k w' hk' hT

/-- (O5) **The messages up to the spawn are thread 0's**, for the appended
memory (the spawn is before the new message). -/
theorem pre_tid_append (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) (hT : R.T ≤ tm.last) (w : Msg) :
    ∀ k w', (tm.append w).1.get? k = some w' → k ≤ R.T → w'.tid = 0 := by
  intro k w' hk hk'
  rcases get?_append_cases hk with ⟨he, -⟩ | ⟨-, hk''⟩
  · rw [he] at hk'; exact absurd hk' (Nat.not_le_of_lt (Nat.lt_succ_of_le hT))
  · exact h.pre_tid k w' hk'' hk'

/-- (O5, O2) **The later messages are a thread's, in its footprint**, for
the appended memory (the new message of thread `0` or `1`, in its
footprint). -/
theorem post_foot_append (h : Inv2Core Λ R P G own tm t0 t1 sm s0 s1 ts tp sp) {w : Msg}
    (hj : w.tid = 0 ∨ w.tid = 1) (hf : P.foot w.tid w.loc) :
    ∀ k w', (tm.append w).1.get? k = some w' → R.T < k → (w'.tid = 0 ∨ w'.tid = 1) ∧ P.foot w'.tid w'.loc := by
  intro k w' hk hT
  rcases get?_append_cases hk with ⟨-, rfl⟩ | ⟨-, hk'⟩
  · exact ⟨hj, hf⟩
  · exact h.post_foot k w' hk' hT

/-- (7) **A promise of thread `i` stays its message after the spawn** in an
appended memory. -/
theorem prom_append {prom : List Time} {i : Nat}
    (hp : ∀ k ∈ prom, R.T < k ∧ ∃ w, tm.get? k = some w ∧ w.tid = i) (w : Msg) :
    ∀ k ∈ prom, R.T < k ∧ ∃ w', (tm.append w).1.get? k = some w' ∧ w'.tid = i := by
  intro k hk
  obtain ⟨hT, w', hg, ht⟩ := hp k hk
  exact ⟨hT, w', by rw [Scc.Sem.Memory.get?_append_le (Kraken.Promising.Memory.le_last_of_get? hg)]; exact hg, ht⟩

end Inv2Core

/-! ## The source side -/

/-- **A source thread's cover of the frozen source words is kept by a pushed
message outside them.** -/
theorem scov_push {sm : WeakMem.Memory} {frzS : WeakMem.Address → Prop} {coh : WeakMem.Address → Nat}
    (h : ∀ k m, sm[k]? = some m → frzS m.loc → k ≤ coh m.loc) {m : WeakMem.Msg} (hm : ¬ frzS m.loc) :
    ∀ k m', (sm.push m)[k]? = some m' → frzS m'.loc → k ≤ coh m'.loc := by
  intro k m' hk hz
  rw [Array.getElem?_push] at hk
  split at hk
  · cases hk; exact absurd hz hm
  · exact h k m' hk hz

/-- (3) **No frozen source message after the spawn** is kept by a pushed
message outside the frozen source words. -/
theorem frzS_push {sm : WeakMem.Memory} {S : Nat} {frzS : WeakMem.Address → Prop}
    (h : ∀ k m, sm[k]? = some m → S ≤ k → ¬ frzS m.loc) {m : WeakMem.Msg} (hm : ¬ frzS m.loc) :
    ∀ k m', (sm.push m)[k]? = some m' → S ≤ k → ¬ frzS m'.loc := by
  intro k m' hk hS
  rw [Array.getElem?_push] at hk
  split at hk
  · cases hk; exact hm
  · exact h k m' hk hS

end Spike.Lib.Inv2Rely

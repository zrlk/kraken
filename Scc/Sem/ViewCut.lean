/-
**The view cut and its global invariants** (M2 view relation groundwork,
pure lemmas; nothing here is used by `Correct` or `Components` yet).

The source and target views are related through the message map
`ts : Nat → Option Nat` of `MemRelP`: a source view bound `Vs` (a message
index) is *cut* against a target view bound `Vt` (a timestamp) when every
source message at or below `Vs` has its image at or below `Vt`.

- `Cut`, `Cut.mono` (monotone in the target bound), `Cut.anti` (antitone in
  the source bound), `cut_max_iff`, `Cut.max_left`/`Cut.max_right`,
  `Cut.congr` (the map only matters up to `Vs`);
- `pairTop_le_succ`, `Cut.pairTop`: a pair read's `pairTop k` is at most
  `k + 1`, so a cut up to `k + 1` covers it;
- `Cut.store`, `Cut.store_of_lt`: a lockstep append (`MemRelP.store`: the
  source pushes at `sm.size` imaged at `tm.last + 1`) keeps a cut, raised to
  the new message on both sides or left alone below `sm.size`.

The global invariants, with frontier `N`:

- `Mono N ts`: images are monotone along source indices from `N` on
  (`ts j ≤ ts k` for `j ≤ k`, `N ≤ k`);
- `Full N ts F`: every image below `N` is at most `F` (`Full.mono`);
- `cut_of_mono_full`: together they give `Cut ts k (max tk F)` for every
  source message `k` imaged at `tk`, the bound each read needs;
- `Mono.store`, `Full.store`: kept by the lockstep append. The other
  `MemRelP` steps of the phase after the frontier (`runtime_write`,
  `fulfil_runtime`, `fulfil`, `promise_unmirrored`) leave `ts` unchanged, so
  they keep both trivially. `MemRelP.alloc` and `MemRelP.fulfil_unmirrored`
  break `Mono N` in general (they image a high source index at an old
  timestamp); they are excluded after the frontier.

The handover lemma at the target (Kraken) level:

- `OwnBelow tid t mem`: every message of `tid` in `mem` is an outstanding
  promise of `t` or at most `t`'s `vwAll`;
- `OwnBelow.init`, `OwnBelow.stepOne_self`, `OwnBelow.stepOne_other`,
  `OwnBelow.promise_self`, `OwnBelow.promise_other`, `OwnBelow.stepSemC`:
  kept by every certified instruction or promise step of any thread;
- `OwnBelow.le_vwAll`: with no outstanding promise, every message the
  thread wrote is at most its `vwAll`.

Not covered: the lift of `OwnBelow` through the kernel steps of
`ExtMachine.Step`, the images at the frontier, register views.
-/
import Scc.Sem.MemRelP

namespace Scc.Sem.ViewCut

open Kraken.Promising

local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *); omega))

/-! ## The cut -/

/-- **The cut** between a source view bound `Vs` and a target view bound
`Vt`: every source message at or below `Vs` has its image at or below
`Vt`. -/
def Cut (ts : Nat → Option Nat) (Vs Vt : Nat) : Prop :=
  ∀ k, k ≤ Vs → ∀ t, ts k = some t → t ≤ Vt

variable {ts ts' : Nat → Option Nat}

/-- A cut holds against every larger target bound. -/
theorem Cut.mono {Vs Vt Vt' : Nat} (h : Cut ts Vs Vt) (hle : Vt ≤ Vt') : Cut ts Vs Vt' :=
  fun k hk t ht => Nat.le_trans (h k hk t ht) hle

/-- A cut holds for every smaller source bound. -/
theorem Cut.anti {Vs Vs' Vt : Nat} (h : Cut ts Vs Vt) (hle : Vs' ≤ Vs) : Cut ts Vs' Vt :=
  fun k hk t ht => h k (Nat.le_trans hk hle) t ht

/-- A cut of a join is a cut of each side. -/
theorem cut_max_iff {a b V : Nat} : Cut ts (max a b) V ↔ Cut ts a V ∧ Cut ts b V := by
  refine ⟨fun h => ⟨h.anti (Nat.le_max_left _ _), h.anti (Nat.le_max_right _ _)⟩, fun ⟨ha, hb⟩ k hk t ht => ?_⟩
  rcases Nat.le_total a b with hab | hab
  · exact hb k (by omega) t ht
  · exact ha k (by omega) t ht

theorem Cut.max_left {Vs Vt V : Nat} (h : Cut ts Vs Vt) : Cut ts Vs (max Vt V) :=
  h.mono (Nat.le_max_left _ _)

theorem Cut.max_right {Vs Vt V : Nat} (h : Cut ts Vs Vt) : Cut ts Vs (max V Vt) :=
  h.mono (Nat.le_max_right _ _)

/-- Only the map up to `Vs` matters. -/
theorem Cut.congr {Vs Vt : Nat} (h : Cut ts Vs Vt) (he : ∀ k, k ≤ Vs → ts' k = ts k) : Cut ts' Vs Vt :=
  fun k hk t ht => h k hk t (by rw [← he k hk]; exact ht)

/-- `Promises.pairTop` moves a timestamp up by at most one (to the pair's
second word). -/
theorem pairTop_le_succ (pairs : List WeakMem.Ts) (k : WeakMem.Ts) : Promises.pairTop pairs k ≤ k + 1 := by
  unfold Promises.pairTop
  split
  · exact Nat.le_refl _
  · exact Nat.le_succ k

/-- A cut up to `k + 1` covers a pair read's `pairTop k`. -/
theorem Cut.pairTop {k Vt : Nat} (pairs : List WeakMem.Ts) (h : Cut ts (k + 1) Vt) :
    Cut ts (Promises.pairTop pairs k) Vt :=
  h.anti (pairTop_le_succ pairs k)

/-! ## A lockstep append -/

section Store

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}

/-- **A lockstep append keeps a cut, raised on both sides**: the source
bound raised to the new index `sm.size`, the target bound to the new
timestamp `tm.last + 1` (the map of `MemRelP.store`). -/
theorem Cut.store (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {Vs Vt : Nat} (hc : Cut ts Vs Vt) :
    Cut (fun k => if k = sm.size then some (tm.last + 1) else ts k) (max Vs sm.size) (max Vt (tm.last + 1)) := by
  intro k hk t ht
  by_cases hks : k = sm.size
  · simp only [hks, ↓reduceIte, Option.some.injEq] at ht
    subst ht
    exact Nat.le_max_right _ _
  · simp only [hks, ↓reduceIte] at ht
    by_cases hkv : k ≤ Vs
    · exact Nat.le_trans (hc k hkv t ht) (Nat.le_max_left _ _)
    · have := h.ts_le_last (h.lt_of_ts ht) ht
      simp only [Memory.last] at this ⊢
      omega

/-- **A lockstep append keeps a cut below the new index**: a source bound
below `sm.size` does not see the new message. -/
theorem Cut.store_of_lt {Vs Vt : Nat} (hc : Cut ts Vs Vt) (hlt : Vs < sm.size) (L : Nat) :
    Cut (fun k => if k = sm.size then some L else ts k) Vs Vt :=
  hc.congr fun k hk => by simp only [show k ≠ sm.size by omega, ↓reduceIte]

end Store

/-! ## The global invariants -/

/-- **Monotone from the frontier `N` on**: the image of every source message
at or after `N` is at least the image of every earlier one. -/
def Mono (N : Nat) (ts : Nat → Option Nat) : Prop :=
  ∀ k, N ≤ k → ∀ j, j ≤ k → ∀ tj tk, ts j = some tj → ts k = some tk → tj ≤ tk

/-- **Full below the frontier `N`**: every image of a source message before
`N` is at most `F` (for each thread, `F` is any of its target views in the
relation). -/
def Full (N : Nat) (ts : Nat → Option Nat) (F : Nat) : Prop :=
  ∀ j, j < N → ∀ t, ts j = some t → t ≤ F

theorem Full.mono {N F F' : Nat} (h : Full N ts F) (hle : F ≤ F') : Full N ts F' :=
  fun j hj t ht => Nat.le_trans (h j hj t ht) hle

/-- `Full` is the cut up to the frontier's last index. -/
theorem Full.cut {N F : Nat} (h : Full N ts F) : Cut ts (N - 1) F ∨ N = 0 := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · exact .inr hN
  · exact .inl fun k hk t ht => h k (by omega) t ht

/-- **The bound of a read**: under `Mono N` and `Full N F`, every source
message at or below a message `k` imaged at `tk` is imaged at or below
`max tk F`. -/
theorem cut_of_mono_full {N F k tk : Nat} (hm : Mono N ts) (hf : Full N ts F) (hk : ts k = some tk) :
    Cut ts k (max tk F) := by
  intro j hj t ht
  by_cases hjN : j < N
  · exact Nat.le_trans (hf j hjN t ht) (Nat.le_max_right _ _)
  · exact Nat.le_trans (hm k (by omega) j hj t tk ht hk) (Nat.le_max_left _ _)

/-- `cut_of_mono_full` at a pair read: the pair's second word `k + 1` is
imaged at `tk` too. -/
theorem cut_pairTop_of_mono_full {N F k tk : Nat} (pairs : List WeakMem.Ts) (hm : Mono N ts)
    (hf : Full N ts F) (hk : ts (k + 1) = some tk) : Cut ts (Promises.pairTop pairs k) (max tk F) :=
  (cut_of_mono_full hm hf hk).pairTop pairs

section Store

variable {Λ : Layout} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {tm : Memory} {sm : WeakMem.Memory} {tp tq sp : List Nat}

/-- **A lockstep append keeps `Mono N`**: the new image `tm.last + 1` is
above every image (`MemRelP.ts_le_last`), and the new index above every
indexed message (`MemRelP.ts_dom`). -/
theorem Mono.store (h : MemRelP Λ lbl lsize ts tm sm tp tq sp) {N : Nat} (hm : Mono N ts) :
    Mono N (fun k => if k = sm.size then some (tm.last + 1) else ts k) := by
  have hlast : ∀ k t, ts k = some t → t ≤ tm.last := fun k t ht => h.ts_le_last (h.lt_of_ts ht) ht
  intro k hNk j hj tj tk htj htk
  by_cases hks : k = sm.size
  · simp only [hks, ↓reduceIte, Option.some.injEq] at htk
    subst htk
    by_cases hjs : j = sm.size
    · simp only [hjs, ↓reduceIte, Option.some.injEq] at htj
      omega
    · simp only [hjs, ↓reduceIte] at htj
      have := hlast j tj htj
      omega
  · simp only [hks, ↓reduceIte] at htk
    have hkl := h.lt_of_ts htk
    simp only [show j ≠ sm.size by omega, ↓reduceIte] at htj
    exact hm k hNk j hj tj tk htj htk

/-- **A lockstep append keeps `Full N F`** when the frontier is at most the
source memory size. -/
theorem Full.store {N F : Nat} (hf : Full N ts F) (hN : N ≤ sm.size) (L : Nat) :
    Full N (fun k => if k = sm.size then some L else ts k) F := by
  intro j hj t ht
  simp only [show j ≠ sm.size by omega, ↓reduceIte] at ht
  exact hf j hj t ht

end Store

/-! ## Handover: a thread's own writes -/

variable {I : ISA}

/-- **Every message of `tid` is below its thread**: an outstanding promise
of `t`, or at most `t`'s `vwAll`. -/
def OwnBelow (tid : Nat) (t : Thread I) (mem : Memory) : Prop :=
  ∀ ts w, mem.get? ts = some w → w.tid = tid → ts ∈ t.prom ∨ ts ≤ t.views.vwAll

/-- No messages: nothing to check. -/
theorem OwnBelow.init (tid : Nat) (t : Thread I) (init : List (Loc × Val)) :
    OwnBelow tid t { init, msgs := #[] } := by
  intro ts w hg _
  unfold Memory.get? at hg
  split at hg
  · cases hg
  · simp at hg

/-- **With no outstanding promise**, every message the thread wrote is at
most its `vwAll`. -/
theorem OwnBelow.le_vwAll {tid : Nat} {t : Thread I} {mem : Memory} (h : OwnBelow tid t mem)
    (hp : t.prom = []) : ∀ ts w, mem.get? ts = some w → w.tid = tid → ts ≤ t.views.vwAll := by
  intro ts w hg hw
  rcases h ts w hg hw with h | h
  · rw [hp] at h; cases h
  · exact h

/-- **An instruction of the thread keeps `OwnBelow`**: its appends are at
most its new `vwAll` (`stepOne_own`), a promise it fulfils is too
(`stepOne_fulfil`), and `vwAll` only grows (`stepOne_grow`). -/
theorem OwnBelow.stepOne_self (A : Arch) {tid : Nat} {t : Thread I} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A t tid mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (hf : t.views.FwdOk) (h : OwnBelow tid t mem) :
    OwnBelow tid o.thread o.mem := by
  intro ts w hg hw
  by_cases hnew : mem.last < ts
  · exact .inr (stepOne_own A hstep ho ts w hnew hg).2
  · have hg' : mem.get? ts = some w := by
      rw [← (Memory.Prefix.stepOne hstep ho).get? (Nat.le_of_not_lt hnew)]; exact hg
    rcases h ts w hg' hw with hp | hle
    · by_cases ho' : ts ∈ o.thread.prom
      · exact .inl ho'
      · exact .inr (stepOne_fulfil A hstep ho hf ts hp ho')
    · right
      have hg := (Live.CertCut.stepOne_grow A hstep ho).1
      have h1 := hg.vwOld
      have h2 := hg.vwOldNT
      simp only [Views.vwAll] at hle ⊢
      omega_t

/-- **An instruction of another thread keeps `OwnBelow`**: it appends only
messages of its own (`stepOne_own`). -/
theorem OwnBelow.stepOne_other (A : Arch) {tid j : Nat} (hj : j ≠ tid) {t tj : Thread I} {mem : Memory}
    {outs : List (Except String (Kraken.Promising.Outcome I))} (hstep : stepOne A tj j mem = some outs)
    {o : Kraken.Promising.Outcome I} (ho : .ok o ∈ outs) (h : OwnBelow tid t mem) : OwnBelow tid t o.mem := by
  intro ts w hg hw
  by_cases hnew : mem.last < ts
  · exact absurd ((stepOne_own A hstep ho ts w hnew hg).1.symm.trans hw) hj
  · exact h ts w (by rw [← (Memory.Prefix.stepOne hstep ho).get? (Nat.le_of_not_lt hnew)]; exact hg) hw

/-- **A promise of the thread keeps `OwnBelow`**: the new message is the new
outstanding promise. -/
theorem OwnBelow.promise_self {tid : Nat} {t : Thread I} {mem : Memory} (w : Msg) (h : OwnBelow tid t mem) :
    OwnBelow tid (Live.Sem.promThread t mem w) (mem.append w).1 := by
  intro ts w' hg hw
  by_cases hne : ts = mem.last + 1
  · left
    simp only [List.mem_append, List.mem_singleton]
    right
    simp only [hne, Memory.last, Memory.append]
  · rcases h ts w' (CohCoversP.get?_append_ne hg hne) hw with hp | hle
    · exact .inl (List.mem_append_left _ hp)
    · exact .inr hle

/-- **A promise of another thread keeps `OwnBelow`**: its message is not
`tid`'s. -/
theorem OwnBelow.promise_other {tid : Nat} {t : Thread I} {mem : Memory} {w : Msg} (hw : w.tid ≠ tid)
    (h : OwnBelow tid t mem) : OwnBelow tid t (mem.append w).1 := by
  intro ts w' hg hw'
  by_cases hne : ts = mem.last + 1
  · rw [hne, Memory.get?_append_new] at hg
    cases hg
    exact absurd hw' hw
  · exact h ts w' (CohCoversP.get?_append_ne hg hne) hw'

/-- **Every certified step keeps `OwnBelow`** (`StepSemC` of any thread
`j`; the thread `tid` itself needs its forwarding invariant `FwdOk`). -/
theorem OwnBelow.stepSemC {A : Arch} {cs : CertSem I} {j tid : Nat}
    {c c' : Config I} (hs : StepSemC A cs j c c') {t : Thread I} (ht : c.threads[tid]? = some t)
    (hf : t.views.FwdOk) (h : OwnBelow tid t c.mem) :
    ∃ t', c'.threads[tid]? = some t' ∧ OwnBelow tid t' c'.mem := by
  rcases hs with ⟨t0, outs, o, ht0, hst, ho, -, rfl⟩ | ⟨t0, w, ht0, hw, -, rfl⟩
  · rw [Config.withThread_get? c _ _ (lt_size_of_get? ht0)]
    by_cases hj : j = tid
    · subst hj
      rw [ht] at ht0; cases ht0
      exact ⟨o.thread, by rw [ite_eq_left rfl], OwnBelow.stepOne_self A hst ho hf h⟩
    · exact ⟨t, by rw [ite_eq_right hj]; exact ht, OwnBelow.stepOne_other A hj hst ho h⟩
  · rw [Config.withThread_get? c _ _ (lt_size_of_get? ht0)]
    by_cases hj : j = tid
    · subst hj
      rw [ht] at ht0; cases ht0
      exact ⟨_, by rw [ite_eq_left rfl], OwnBelow.promise_self w h⟩
    · exact ⟨t, by rw [ite_eq_right hj]; exact ht, OwnBelow.promise_other (hw ▸ hj) h⟩

end Scc.Sem.ViewCut

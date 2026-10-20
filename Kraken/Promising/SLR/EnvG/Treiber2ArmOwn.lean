/-
Part 1: **thread-owned write sets at the final clean
erasure**: the generic half of the ghost-free route for a location written by
non-release RMWs (`treiber2_arm.kl`'s `top`, popped by a plain `CAS`).
ISA-neutral.

## Why

A non-release write must write a value pure for its location's release
predicate (`StoreOk`/`RmwOkCAdj`; `PromisePure'`), and purity is per value. When
releases and non-release writes of the same location write the same values
(a Treiber stack's push `CASL` and pop `CAS` both write node addresses), no
release predicate on the location can carry anything: its predicate must be
`Pred.emp`. The history of the location is then recovered at the final clean
erasure from the threads' **own** resources instead of message slots:

- the threads that write `x` together hold all of `x` (here two threads with
  shares adding up to `1`), so no slot and no other thread holds any of it,
  and every message of `x` lies in one of their write sets
  (`msg_mem_pair`, from `Erase.writes` and `X_total_cases`);
- a word a thread keeps whole (`q = 1`) is read, by any read whose window
  covers the word's maximal write, at that write's value (`thread_read`; the
  thread-owned form of `Treiber2.slot_read`, via `total_max_of_thread`).

Each thread records its own writes of `x` in its write set (`Plan.after` with
no planned release is `Res.addW`) and its own final facts locally; the
program-specific layer combines them (`EnvG/Treiber2ArmFinal.lean`).
-/
import Kraken.Promising.SLR.StoreHelpers
import Kraken.Promising.SLR.EnvG.TreiberVCCommon

namespace Kraken.Promising.SLR.EnvG.OwnWrites

open Kraken Kraken.Promising
open Kraken.Promising.SLR.EnvG.TreiberCommon (read?_of_get? get?_of_read?)

variable {I : ISA} {rF : Nat → Res} {g : Ghost} {T : Nat → Prop} {c : Config I}

/-- `omega` on `Time`/`View` (abbreviations of `Nat`), as in `ReleasePrefix`. -/
local macro "omega_t" : tactic => `(tactic| ((try simp only [Time, View] at *) <;> omega))

/-- **Two threads holding all of `x` exclude every slot** from `x`. -/
theorem slot_q_zero (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size)
    (hij : i ≠ j) {x : Loc} (hq : ((rF i).wr x).q + ((rF j).wr x).q = 1) {s : Slot} (hs : s ∈ g.u) :
    (s.res.wr x).q = 0 := by
  have hsub : (((rF i).op (rF j)).op s.res).Sub (total rF g c) :=
    Res.Sub.op_mono (threadsRes_sub_pair rF hi hj hij) (slotsRes_sub hs)
  have h := ((hsub.valid E.valid).1 x)
  have h' : (((rF i).wr x).q + ((rF j).wr x).q) + (s.res.wr x).q ≤ 1 := h
  have := (s.res.wr x).nonneg
  rw [hq] at h'
  grind

/-- **Every write of `x` in the total is in one of the two holders' write
sets**, when they hold all of `x` and are the only threads. -/
theorem X_pair (E : Erase rF g T c) {i j : Nat} (hi : i < c.threads.size) (hj : j < c.threads.size)
    (hij : i ≠ j) (hall : ∀ k, k < c.threads.size → k = i ∨ k = j) {x : Loc}
    (hq : ((rF i).wr x).q + ((rF j).wr x).q = 1) {p : Val × Time} (hp : ((total rF g c).wr x).X p) :
    ((rF i).wr x).X p ∨ ((rF j).wr x).X p := by
  rcases X_total_cases hp with ⟨k, hk, hXk⟩ | ⟨s, hs, hXs⟩
  · rcases hall k hk with rfl | rfl
    · exact .inl hXk
    · exact .inr hXk
  · exact ((s.res.wr x).zero (slot_q_zero E hi hj hij hq hs) _ hXs).elim

/-- **Every message of `x` is in one of the two holders' write sets** at a
configuration with no outstanding promise. -/
theorem msg_mem_pair (E : Erase rF g T c) (hno : ∀ ts, ¬ Outstanding c ts) {i j : Nat}
    (hi : i < c.threads.size) (hj : j < c.threads.size) (hij : i ≠ j)
    (hall : ∀ k, k < c.threads.size → k = i ∨ k = j) {x : Loc}
    (hq : ((rF i).wr x).q + ((rF j).wr x).q = 1) {V : Time} {wm : Msg} (hV : c.mem.get? V = some wm)
    (hl : wm.loc = x) : ((rF i).wr x).X (wm.val, V) ∨ ((rF j).wr x).X (wm.val, V) := by
  have hpos : 0 < ((total rF g c).wr x).q := by
    have h1 := (sub_total_thread (rF := rF) (g := g) hi).q_le x
    have h2 := (sub_total_thread (rF := rF) (g := g) hj).q_le x
    have := ((rF i).wr x).nonneg; have := ((rF j).wr x).nonneg
    grind
  refine X_pair E hi hj hij hall hq (((E.writes x (.inl hpos)) _).mpr (.inr ⟨wm, hV, hl, rfl, .inl (hno V)⟩))

/-- **A word a thread keeps whole** (`q = 1`, maximal write `(y, t)`): a read
of it whose window `(tl, B]` covers `t` reads `y` (the thread-owned form of
`Treiber2.slot_read`). -/
theorem thread_read (E : Erase rF g T c) (hno : ∀ ts, ¬ Outstanding c ts) {j : Nat} (hj : j < c.threads.size)
    {l : Loc} {y : Val} {t : Time} (hq : ((rF j).wr l).q = 1) (hX : ((rF j).wr l).X (y, t))
    (hmax : ∀ p, ((rF j).wr l).X p → p.2 ≤ t) {tl B : Time} {u : Val}
    (hrd : c.mem.read? l tl = some u)
    (hwin : ∀ p wm, tl < p → p ≤ B → c.mem.get? p = some wm → wm.loc ≠ l) (htB : t ≤ B) : u = y := by
  obtain ⟨hpos, hXt, hmt⟩ := total_max_of_thread E hj hq hX hmax
  have hw := E.writes l (.inl hpos)
  have hset : ∀ ts, Settled c g ts := fun ts => .inl (hno ts)
  have hrt : c.mem.read? l t = some y := by
    rcases (hw (y, t)).mp hXt with ⟨h0, h1⟩ | ⟨wm, hg, hl, hv, -⟩
    · simp only at h0 h1; subst h0; subst h1; simp [Memory.read?]
    · simp only at hg hv; rw [← hl, ← hv]; exact read?_of_get? hg
  have htl : tl ≤ t := by
    by_cases h0 : tl = 0
    · omega_t
    · obtain ⟨wm, hg, hl, hv⟩ := get?_of_read? h0 hrd
      exact hmt (u, tl) ((hw (u, tl)).mpr (.inr ⟨wm, hg, hl, hv, hset tl⟩))
  have hte : tl = t := by
    refine Classical.byContradiction fun hne => ?_
    have hlt : tl < t := by omega_t
    have ht0 : t ≠ 0 := by omega_t
    obtain ⟨wm, hg, hl, -⟩ := get?_of_read? ht0 hrt
    exact hwin t wm hlt htB hg hl
  subst hte
  rw [hrd] at hrt
  exact Option.some.inj hrt

end Kraken.Promising.SLR.EnvG.OwnWrites

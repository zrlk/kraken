/-
**The ISA-neutral ownership facts of the SPSC rings**:
the copies shared by the x64 SPSC proof (`EnvG/X64SpscVC.lean`, `SpscX`) and the AArch64 SPSC proof
(`EnvG/A64SpscVCP.lean`, `A64SpscRead.lean`, `SpscA`), now aliases of these
(`hoist_alias`, statements verbatim).

- `Full x w V R`: all of `x`, with maximal write `w` at or below `V`;
  `Hold x V r`: all of `x`, every write at or below `V`;
- `KeepsFull r r'`: every fully held location keeps its permission;
- `wr_after_ne`, `keepsFull_store`, `full_after`: a store's resource
  (`Plan.after`) at the other locations and at the written one;
- `read?_le_last`, `read?_prefix`, `writeSnap_read?`: reads survive memory
  growth (also `TakeUSkip`'s and `Dekker`'s copies);
- `OkPred`: a usable acquire predicate relative to the last message read.
-/
import Kraken.Promising.SLR.EnvG.Plan
import Kraken.Promising.SLR.EnvG.Facts
import Kraken.Promising.ReleasePrefix

namespace Kraken.Promising.SLR.EnvG.SpscCommon

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **All of `x`, with maximal write `w`** at or below `V`. -/
def Full (x : Loc) (w : Val) (V : View) (R : Res) : Prop :=
  (R.wr x).q = 1 ∧ ∃ ts, (R.wr x).X (w, ts) ∧ (∀ p, (R.wr x).X p → p.2 ≤ ts) ∧ ts ≤ V

/-- The permission of `x` in `r'` is that of `r`, if `r` holds all of it. -/
abbrev KeepsFull (r r' : Res) : Prop :=
  ∀ x, (r.wr x).q = 1 → (r'.wr x).q = 1 ∧ ∀ p, (r'.wr x).X p ↔ (r.wr x).X p

theorem keepsFull_refl (r : Res) : KeepsFull r r := fun _ h => ⟨h, fun _ => Iff.rfl⟩

/-- All of `x`, every write at or below `V`. -/
def Hold (x : Loc) (V : View) (r : Res) : Prop := (r.wr x).q = 1 ∧ ∀ p, (r.wr x).X p → p.2 ≤ V

theorem Hold.mono {x : Loc} {V V' : View} {r : Res} (h : Hold x V r) (hV : V ≤ V') : Hold x V' r :=
  ⟨h.1, fun p hp => Nat.le_trans (h.2 p hp) hV⟩

theorem Hold.keep {x : Loc} {V V' : View} {r r' : Res} (h : Hold x V r) (hk : KeepsFull r r') (hV : V ≤ V') :
    Hold x V' r' :=
  ⟨(hk x h.1).1, fun p hp => Nat.le_trans (h.2 p ((hk x h.1).2 p |>.mp hp)) hV⟩

theorem Full.mono {x : Loc} {w : Val} {V V' : View} {r : Res} (h : Full x w V r) (hV : V ≤ V') : Full x w V' r :=
  h.imp id fun ⟨ts, hX, hm, hts⟩ => ⟨ts, hX, hm, Nat.le_trans hts hV⟩

theorem Full.keep {x : Loc} {w : Val} {V V' : View} {r r' : Res} (h : Full x w V r) (hk : KeepsFull r r')
    (hV : V ≤ V') : Full x w V' r' := by
  obtain ⟨hq, ts, hX, hm, hts⟩ := h
  exact ⟨(hk x hq).1, ts, ((hk x hq).2 _).mpr hX, fun p hp => hm p (((hk x hq).2 p).mp hp), Nat.le_trans hts hV⟩

theorem Full.hold {x : Loc} {w : Val} {V : View} {r : Res} (h : Full x w V r) : Hold x V r :=
  ⟨h.1, fun p hp => h.2.elim fun _ ⟨_, hm, hts⟩ => Nat.le_trans (hm p hp) hts⟩

theorem q_keep {x : Loc} {r r' : Res} (h : (r.wr x).q = 1) (hk : KeepsFull r r') : (r'.wr x).q = 1 := (hk x h).1

/-- A store's resource keeps every location it does not write or give. -/
theorem wr_after_ne {pl : Plan} {l x : Loc} {v : Val} {tw : Time} {cl : Prop} {r : Res} (hx : x ≠ l)
    (hw : pl.Whole l v) (hg : x ∉ pl.gives l v) : (pl.after l v tw cl r).wr x = r.wr x := by
  unfold Plan.after
  split
  · rw [Res.addW_wr_ne _ _ hx, pl.keep_of_whole hw]; simp only [Res.drop, hg, ↓reduceIte]
  · rw [Res.addW_wr_ne _ _ hx]

theorem wr_only_mem {L : List Loc} {r : Res} {x : Loc} (h : x ∈ L) : (Res.only L r).wr x = r.wr x := by
  simp only [Res.only, h, ↓reduceIte]

theorem min_mono {a b c d : Nat} (h1 : a ≤ c) (h2 : b ≤ d) : min a b ≤ min c d := by omega

/-- A store keeps a fully held location it does not write or give. -/
theorem keepsFull_store {pl : Plan} {l : Loc} {v : Val} {tw : Time} {cl : Prop} {r : Res} {x : Loc} (hx : x ≠ l)
    (hw : pl.Whole l v) (hg : x ∉ pl.gives l v) : (r.wr x).q = 1 → ((pl.after l v tw cl r).wr x).q = 1 ∧
      ∀ p, ((pl.after l v tw cl r).wr x).X p ↔ (r.wr x).X p := fun h => by
  rw [wr_after_ne hx hw hg]; exact ⟨h, fun _ => Iff.rfl⟩

/-- **The written location after a store**: all of it (kept), with maximal
write `(v, tw)` if every earlier write is below `tw`. -/
theorem full_after {pl : Plan} {l : Loc} {v : Val} {tw : Time} {cl : Prop} {r : Res} (hw : pl.Whole l v)
    (hg : l ∉ pl.gives l v) (hq : (r.wr l).q = 1) (hlt : ∀ p, (r.wr l).X p → p.2 < tw) {V : View}
    (hV : tw ≤ V) : Full l v V (pl.after l v tw cl r) := by
  have hwr : (pl.keep l v cl r).wr l = r.wr l := pl.keep_wr_self hg hw cl r
  have hX : ∀ p, ((pl.after l v tw cl r).wr l).X p ↔ (r.wr l).X p ∨ (0 < (r.wr l).q ∧ p = (v, tw)) := by
    intro p
    unfold Plan.after
    split
    · rw [Res.addW_X_self, hwr]
    · rw [Res.addW_X_self]
  have hq' : ((pl.after l v tw cl r).wr l).q = 1 := by
    unfold Plan.after
    split
    · rw [Res.addW_q, hwr]; exact hq
    · rw [Res.addW_q]; exact hq
  refine ⟨hq', tw, (hX _).mpr (.inr ⟨by rw [hq]; decide, rfl⟩), fun p hp => ?_, hV⟩
  rcases (hX p).mp hp with hp | ⟨-, rfl⟩
  · exact Nat.le_of_lt (hlt p hp)
  · exact Nat.le_refl _

/-! ## Reads, memory growth, usable acquire predicates -/

/-- A message read is at or below the last timestamp. -/
theorem read?_le_last {m : Memory} {l : Loc} {t : Time} {v : Val} (h : m.read? l t = some v) : t ≤ m.last := by
  unfold Memory.read? at h
  split at h
  · next h0 => rw [h0]; exact Nat.zero_le _
  · split at h
    · next w hw => exact Memory.last_le_of_get?_eq_some m hw
    · cases h

/-- A message read at a memory is read at every extension of it. -/
theorem read?_prefix {m m' : Memory} (h : m.Prefix m') {l : Loc} {t : Time} {v : Val}
    (hr : m.read? l t = some v) : m'.read? l t = some v := by
  rw [h.read? (read?_le_last hr)]; exact hr

/-- A message read before a write is read after it. -/
theorem writeSnap_read? {I : ISA} {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) {x : Loc} {ts : Time} {u : Val} (hr : c.mem.read? x ts = some u) :
    c'.mem.read? x ts = some u := by
  have hpre : c.mem.Prefix c'.mem := by
    rcases h.mem with ⟨hm, -⟩ | ⟨hm, -⟩
    · rw [hm]; exact ⟨rfl, List.prefix_refl _⟩
    · rw [hm]; exact Memory.Prefix.append _ _
  exact read?_prefix hpre hr

/-- **A usable acquire predicate** `φ` for the release predicate `ψ`,
relative to the last message read `K`: `ψ`, or the empty resource at a view
at or below `K` (where an earlier take relaxed it). -/
def OkPred (ψ φ : Pred) (K : Time) : Prop := ∀ v m V R, φ.P v m V R → ψ.P v m V R ∨ (V ≤ K ∧ R = Res.unit)

theorem OkPred.refl (ψ : Pred) (K : Time) : OkPred ψ ψ K := fun _ _ _ _ h => .inl h

theorem OkPred.mono {ψ φ : Pred} {K K' : Time} (h : OkPred ψ φ K) (hK : K ≤ K') : OkPred ψ φ K' :=
  fun v m V R hP => (h v m V R hP).imp id fun ⟨h1, h2⟩ => ⟨Nat.le_trans h1 hK, h2⟩

end Kraken.Promising.SLR.EnvG.SpscCommon

/-
Whole-thread environment: **what a
load's clean-erasure knowledge says about the value read** (the first
consumer of the `cl` conjunct of a load; no program proof uses `ClAt` so
far). ISA-neutral.

**Exclusive writer.** Under clean erasure (`T = ⊥`), if thread `tid` holds
*all* of `l` (fraction `1`), then every message to `l` that is not an own
outstanding promise is in its write set: a settled message is in the total
write set (`Erase.writes`), which is the holder's, since every other
component has fraction `0` (`Erase.unique_holder`); an unsettled one is a
valid promise of another thread (`Erase.promValid`), which would need a
permission for `l` that nobody else has (`mayWrite`).

- `X_of_read_full`: the statement at `ClAt`;
- `Plan.after_wr_of_whole`: a whole release that keeps `l` changes `l`'s
  permission only by the released message;
- `X_of_read_clAtV`: the statement at `EnvGLRV`'s `ClAtV`, in both in-flight
  modes (the in-flight message is an own outstanding promise, which a read
  never returns: `ReadAt.notOwn`).

Use (the `[f]=1` of `mp_incl.kl`): the writer holds all of `f` with write
set `{(0, 0)}`, so under `cl` its load of `f` read `0`, its `incl` stored
`1`, and its post can say so (`ThreadRuleRX.done` asks for the post under
`cl` only). Not done here: the program proof.
-/
import Kraken.Promising.SLR.EnvG.LRValEnv
import Kraken.Promising.SLR.Adequacy

namespace Kraken.Promising.SLR.EnvG

open Kraken Kraken.Promising

variable {I : ISA}

/-- **Exclusive writer, clean erasure**: thread `tid` holding all of `l`
holds every non-own message to `l` in its write set. -/
theorem X_of_read_full {rF : Nat → Res} {tid : Nat} {r : Res} {g : Ghost} {c : Config I}
    (E : Erase (setRes rF tid r) g (fun _ => False) c) (htid : tid < c.threads.size) {l : Loc}
    (hq : (r.wr l).q = 1) {tr : Time} {v : Val} (hrd : c.mem.read? l tr = some v) (hno : tr ∉ ownProm tid c) :
    (r.wr l).X (v, tr) := by
  have hq' : ((setRes rF tid r tid).wr l).q = 1 := by rw [setRes_self]; exact hq
  obtain ⟨hth, hsl⟩ := E.unique_holder htid hq'
  -- the message is a settled message (or the initial one)
  have hF : Fulf c g l (v, tr) := by
    unfold Memory.read? at hrd
    split at hrd
    · next h0 => exact .inl ⟨h0, (Option.some.inj hrd).symm⟩
    · split at hrd
      · next w hw =>
        split at hrd
        · next hl =>
          have hwl : w.loc = l := by simpa using hl
          obtain rfl := Option.some.inj hrd
          by_cases hS : Settled c g tr
          · exact .inr ⟨w, hw, hwl, rfl, hS⟩
          · exfalso
            simp only [Settled, not_or] at hS
            obtain ⟨hout, hpd⟩ := hS
            obtain ⟨i, t, hti, htr⟩ := Classical.byContradiction hout
            have hit : i ≠ tid := by
              rintro rfl
              exact hno (by rw [ownProm_eq hti]; exact htr)
            have hmw := E.promValid i t hti (fun h => h) tr htr hpd w hw
            rw [setRes_ne rF r hit, hwl] at hmw
            have hi := lt_size_of_get? hti
            rcases hmw with hp | ⟨s, hs, -, hp⟩
            · have := hth i hi hit
              rw [setRes_ne rF r hit] at this
              rw [this] at hp; exact Rat.lt_irrefl hp
            · rw [hsl s hs] at hp; exact Rat.lt_irrefl hp
        · cases hrd
      · cases hrd
  -- so it is in the total write set, which is the holder's
  have hpos : 0 < ((total (setRes rF tid r) g c).wr l).q := by
    have := (sub_total_thread (rF := setRes rF tid r) (g := g) htid).q_le l
    rw [hq'] at this
    grind
  have hX := (E.writes l (.inl hpos) (v, tr)).mpr hF
  rcases X_total_cases hX with ⟨j, hj, hXj⟩ | ⟨s, hs, hXs⟩
  · by_cases hjt : j = tid
    · subst hjt; rw [setRes_self] at hXj; exact hXj
    · exact (((setRes rF tid r j).wr l).zero (hth j hj hjt) _ hXj).elim
  · exact ((s.res.wr l).zero (hsl s hs) _ hXs).elim

/-- **A whole release that keeps `l`** changes `l`'s permission only by the
released message (fraction unchanged, write set grows by at most it). -/
theorem Plan.after_wr_of_whole (pl : Plan) {l' : Loc} {v' : Val} (hs : pl.Whole l' v') {l : Loc}
    (hl : l ∉ pl.gives l' v') (ts : Time) (P : Prop) (rv : Res) :
    ((pl.after l' v' ts P rv).wr l).q = (rv.wr l).q ∧
      ∀ p, ((pl.after l' v' ts P rv).wr l).X p → (rv.wr l).X p ∨ p = (v', ts) := by
  have hd : ∀ cl, (pl.keep l' v' cl rv).wr l = rv.wr l := fun cl => by
    simp only [pl.keep_of_whole hs, Res.drop, hl, ↓reduceIte]
  have key : ∀ r : Res, r.wr l = rv.wr l →
      ((r.addW l' (v', ts)).wr l).q = (rv.wr l).q ∧
        ∀ p, ((r.addW l' (v', ts)).wr l).X p → (rv.wr l).X p ∨ p = (v', ts) := fun r hr => by
    refine ⟨by rw [Res.addW_q, hr], fun p hp => ?_⟩
    by_cases he : l = l'
    · subst he
      rcases (Res.addW_X_self r l (v', ts) p).mp hp with h | ⟨-, h⟩
      · exact .inl (hr ▸ h)
      · exact .inr h
    · rw [Res.addW_wr_ne r _ he, hr] at hp; exact .inl hp
  unfold Plan.after
  split
  · exact key _ (hd P)
  · exact key _ rfl

/-- **Exclusive writer at `EnvGLRV`'s load knowledge**: if the virtual
resource holds all of `l` and no planned release gives `l` away (whole
entries), a read of a non-own message to `l` at the anchor returns a write
of the virtual write set, with or without a release in flight. -/
theorem X_of_read_clAtV {tid : Nat} {pl : Plan} {cl : Prop} {rv : Res} {g : Ghost} {c : Config I}
    (hK : ClAtV tid pl cl rv g c) (htid : tid < c.threads.size) {l : Loc} (hq : (rv.wr l).q = 1)
    (hgive : ∀ l' v', l ∉ pl.gives l' v') (hwhole : ∀ e ∈ pl.entries, e.split = none) {tr : Time} {v : Val}
    (hrd : c.mem.read? l tr = some v) (hno : tr ∉ ownProm tid c) : (rv.wr l).X (v, tr) := by
  obtain ⟨r, ⟨rF, E⟩, hinf⟩ := hK
  rcases hinf with ⟨rfl, -⟩ | ⟨ts, l', v', hts, -, -, ⟨P, -, rfl⟩, -⟩
  · exact X_of_read_full E htid hq hrd hno
  · obtain ⟨hq', hX⟩ := pl.after_wr_of_whole (Plan.Whole.of_entries hwhole l' v') (hgive l' v') ts P rv
    rcases hX _ (X_of_read_full E htid (hq'.trans hq) hrd hno) with h | h
    · exact h
    · simp only [Prod.mk.injEq] at h
      exact absurd (h.2 ▸ hts) hno

end Kraken.Promising.SLR.EnvG

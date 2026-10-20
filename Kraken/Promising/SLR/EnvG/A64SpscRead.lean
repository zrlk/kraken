/-
**Part 2: the read and release lemmas of
the AArch64 SPSC proof** (ISA-neutral in content; hoist candidates shared
with `EnvG/X64SpscRead.lean`).

- **Earlier own messages at a release** (`prev_anchor`, `prev_of_snap`):
  a message of the thread's snapshot is below the fresh timestamp
  `c.mem.last + 1` of every admissible anchor `c` and is read in the
  appended memory. This discharges the memory-dependent part (`Prev`) of the
  `RelOb` of `tail := 2`, `tail := 3`, `head := 2`, `head := 3`: the
  writer's own earlier `= 1` (`= 2`) message exists in every anchor memory.
- `read?_of_writeSnap`, `writeSnap_read?`: the message a store writes is in
  the new snapshot; earlier messages stay.
- **The cumulative spin read** (`SpinU`, `spinU_read`): an acquire load of
  `l` (not forwarded) by a thread holding an acquire id of `l` whose
  predicate is `ψ` above the last message read `K`. The read `tr` is at or
  above `K`; the spin facts move to `tr`; fully held locations are kept;
  and for **every** message `t ∈ (K, tr]` (read or skipped) with an impure
  value `u`, the slot of `(l, t)` satisfies `ψ` at `u`, and the thread now
  holds everything that slot holds fully, with the slot's write sets
  (`takeUpTo_wr_full`); it held none of it before (validity).
- `takeEffU_full` (alias of the neutral `TakeUEnv.takeEffU_keepsFull`): a cumulative take
  keeps a fully held location as it was.
-/
import Kraken.Promising.SLR.EnvG.A64SpscSpec

namespace Kraken.Promising.SLR.EnvG.SpscA

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

variable {I : ISA}

/-! ## Messages of the snapshot at a release -/

/-- A message read at `m` is at or below `m.last`. -/
theorem read?_le_last {m : Memory} {l : Loc} {t : Time} {u : Val} (hr : m.read? l t = some u) : t ≤ m.last := by
  unfold Memory.read? at hr
  split at hr
  · next h0 => rw [h0]; exact Nat.zero_le _
  · split at hr
    · next w hw => exact m.last_le_of_get?_eq_some hw
    · cases hr

/-- **A snapshot message at every anchor of a release**: below the fresh
timestamp, and read in the appended memory. -/
theorem prev_anchor {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (hanc : AnchorOk tid σ c g) {l : Loc}
    {t : Time} {u : Val} (hr : σ.snap.mem.read? l t = some u) (w : Msg) :
    t < c.mem.last + 1 ∧ (c.mem.append w).1.read? l t = some u := by
  have hc := hanc.read? hr
  exact ⟨Nat.lt_succ_of_le (read?_le_last hc), read?_prefix (Memory.Prefix.append _ _) hc⟩

/-- **`Prev` at every anchor of a release** from a message of the
snapshot. -/
theorem prev_of_snap {tid : Nat} {σ : State I} {c : Config I} {g : Ghost} (hanc : AnchorOk tid σ c g) {l : Loc}
    {k : BitVec 64} (h : ∃ t u, σ.snap.mem.read? l t = some u ∧ lo u = k) (w : Msg) :
    Prev (c.mem.append w).1 l k (c.mem.last + 1) := by
  obtain ⟨t, u, hr, hu⟩ := h
  obtain ⟨hlt, hr'⟩ := prev_anchor hanc hr w
  exact ⟨t, hlt, u, hr', hu⟩

-- A message read before a write is read after it (neutral).
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.writeSnap_read? ↦ Kraken.Promising.SLR.EnvG.SpscA.writeSnap_read?]

/-- **The written message is in the new snapshot.** -/
theorem read?_of_writeSnap {tid : Nat} {c c' : Config I} {l : Loc} {v : Val} {tw : Time}
    (h : WriteSnap tid c c' l v tw) (h0 : tw ≠ 0) : c'.mem.read? l tw = some v := by
  have hg : c'.mem.get? tw = some ⟨l, v, tid⟩ := by
    rcases h.mem with ⟨hm, hg, -⟩ | ⟨hm, rfl⟩
    · rw [hm]; exact hg
    · rw [hm]; exact Memory.get?_append_last _ _
  simp [Memory.read?, h0, hg]

/-! ## The cumulative take keeps what is fully held -/

-- **A load keeps a full write permission** (`TakeUX64.takeEffU_wr_full`): the
-- ISA-neutral `takeEffU_keepsFull`, statement verbatim.
hoist_alias [Kraken.Promising.SLR.EnvG.takeEffU_keepsFull ↦ Kraken.Promising.SLR.EnvG.SpscA.takeEffU_full]

/-! ## Facts about all messages up to a timestamp -/

/-- **Every message of `l` at or below `K`** has a low word satisfying `Q`. -/
def UpTo (m : Memory) (l : Loc) (K : Time) (Q : BitVec 64 → Prop) : Prop :=
  ∀ t ≤ K, ∀ u, m.read? l t = some u → Q (lo u)

theorem UpTo.prefix {m m' : Memory} {l : Loc} {K : Time} {Q : BitVec 64 → Prop} (h : UpTo m l K Q)
    (hm : m.Prefix m') (hK : K ≤ m.last) : UpTo m' l K Q := fun t ht u hr => by
  rw [hm.read? (Nat.le_trans ht hK)] at hr
  exact h t ht u hr

theorem UpTo.snap {tid : Nat} {c c' : Config I} {l : Loc} {K : Time} {Q : BitVec 64 → Prop}
    (h : UpTo c.mem l K Q) (hs : SnapLe tid c c') (hK : ∃ v, c.mem.read? l K = some v) : UpTo c'.mem l K Q :=
  h.prefix ⟨hs.init, hs.msgs⟩ (hK.elim fun _ hr => read?_le_last hr)

theorem UpTo.extend {m : Memory} {l : Loc} {K tr : Time} {Q : BitVec 64 → Prop} (h : UpTo m l K Q)
    (hnew : ∀ t, K < t → t ≤ tr → ∀ u, m.read? l t = some u → Q (lo u)) : UpTo m l tr Q := fun t ht u hr => by
  rcases Nat.lt_or_ge K t with hlt | hge
  · exact hnew t hlt ht u hr
  · exact h t hge u hr

theorem UpTo.mono {m : Memory} {l : Loc} {K : Time} {Q Q' : BitVec 64 → Prop} (h : UpTo m l K Q)
    (hQ : ∀ x, Q x → Q' x) : UpTo m l K Q' := fun t ht u hr => hQ _ (h t ht u hr)

/-! ## Spinning with the cumulative take -/

-- **A usable acquire predicate** `φ` for the release predicate `ψ`, relative
-- to the last message read `K` (`X64SpscRead.OkPred`; neutral).
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.OkPred ↦ Kraken.Promising.SLR.EnvG.SpscA.OkPred,
  Kraken.Promising.SLR.EnvG.SpscCommon.OkPred.refl ↦ Kraken.Promising.SLR.EnvG.SpscA.OkPred.refl,
  Kraken.Promising.SLR.EnvG.SpscCommon.OkPred.mono ↦ Kraken.Promising.SLR.EnvG.SpscA.OkPred.mono]

/-- A predicate relaxed at timestamps `≤ tr` is usable relative to `tr`. -/
theorem OkPred.takeAtL {ψ φ : Pred} {K tr : Time} {L : List Time} (h : OkPred ψ φ K) (hK : K ≤ tr)
    (hL : ∀ t ∈ L, t ≤ tr) : OkPred ψ (φ.takeAtL L) tr := fun v m V R hP => by
  rcases Pred.takeAtL_P hP with ⟨t, ht, rfl, rfl⟩ | hP
  · exact .inr ⟨hL _ ht, rfl⟩
  · exact (h v m V R hP).imp id fun ⟨h1, h2⟩ => ⟨Nat.le_trans h1 hK, h2⟩

/-- **Spin facts** at `l` (release predicate `ψ`): no own forwarding item,
the last message read `K` at or below the coherence view, and a held
acquire id with a usable predicate. -/
structure SpinU (l : Loc) (ψ : Pred) (K : Time) (σ : State I) : Prop where
  fwd : σ.vs.getFwd l = none
  coh : K ≤ σ.vs.getCoh l
  msg : ∃ vK, σ.snap.mem.read? l K = some vK
  id : ∃ ι, ι < σ.g.acqTab.length ∧ 1 ≤ σ.r.acq l ι ∧ OkPred ψ (σ.g.acqPred ι) K

-- `KeepsFull`, `keepsFull_refl`: the ISA-neutral `SpscCommon` ones.
hoist_alias [Kraken.Promising.SLR.EnvG.SpscCommon.KeepsFull ↦ Kraken.Promising.SLR.EnvG.SpscA.KeepsFull,
  Kraken.Promising.SLR.EnvG.SpscCommon.keepsFull_refl ↦ Kraken.Promising.SLR.EnvG.SpscA.keepsFull_refl]

/-- **What every `EnvGTU` load keeps.** -/
structure LoadKeepU (tid : Nat) (σ σ' : State I) : Prop where
  ghost : σ.g.Le σ'.g
  full : KeepsFull σ.r σ'.r
  vs : VLe σ.vs σ'.vs
  fwd : ∀ x, σ'.vs.getFwd x = σ.vs.getFwd x
  snap : SnapLe tid σ.snap σ'.snap
  cl : σ'.cl → σ.cl

theorem LoadKeepU.rel {tid : Nat} {σ σ' : State I} (h : LoadKeepU tid σ σ') : σ'.g.rel = σ.g.rel := h.ghost.rel

theorem loadKeepU {A : Arch} {pl : Plan} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {n : Nat} {v : Val} (hs : (EnvGTU I A tid pl).step (.load k xcl a n) σ v σ') :
    LoadKeepU tid σ σ' := by
  obtain ⟨ga, hanc, ⟨rF, E⟩, hcl, tr, -, hlv, a', ha, hr, hg, -⟩ := step_loadFactsTU hs
  exact ⟨by rw [hg]; exact hanc.ghost.trans ha.ghost_le, fun x hq => by rw [hr]; exact takeEffU_full hanc.lt E ha hq,
    hlv.mono, hlv.getFwd, hanc.snap, fun h => (hcl ▸ h).1⟩

/-- A non-acquire load keeps the resource. -/
theorem load_r_eq {A : Arch} {pl : Plan} {tid : Nat} {σ σ' : State I} {k : LoadKind} {xcl : Bool}
    {a : BitVec 64} {n : Nat} {v : Val} (hk : (A.loadKind k).isAcquire = false)
    (hs : (EnvGTU I A tid pl).step (.load k xcl a n) σ v σ') : σ'.r = σ.r := by
  obtain ⟨ga, -, -, -, tr, -, -, a', ha, hr, -⟩ := step_loadFactsTU hs
  rw [hr, takeEffU_of_not_acq ha hk]

theorem SpinU.fence {l : Loc} {ψ : Pred} {K : Time} {σ σ' : State I} (h : SpinU l ψ K σ) (hf : FenceLe σ σ') :
    SpinU l ψ K σ' := by
  obtain ⟨hfw, hc, hm, ι, hlt, ha, hok⟩ := h
  exact ⟨by rw [hf.getFwd]; exact hfw, by rw [hf.getCoh]; exact hc, by rw [hf.snap]; exact hm, ι,
    by rw [hf.g]; exact hlt, by rw [hf.r]; exact ha, by rw [hf.g]; exact hok⟩

/-- The spin facts survive a load that keeps the resource. -/
theorem SpinU.load_keep {tid : Nat} {l : Loc} {ψ : Pred} {K : Time} {σ σ' : State I} (h : SpinU l ψ K σ)
    (hk : LoadKeepU tid σ σ') (hr : σ'.r = σ.r) : SpinU l ψ K σ' := by
  obtain ⟨hf, hc, ⟨vK, hm⟩, ι, hlt, ha, hok⟩ := h
  exact ⟨by rw [hk.fwd]; exact hf, Nat.le_trans hc (hk.vs.coh l), ⟨vK, hk.snap.read? hm⟩, ι,
    Nat.lt_of_lt_of_le hlt hk.ghost.acqTab.length_le, by rw [hr]; exact ha,
    by rw [Ghost.acqPred_of_prefix hk.ghost.acqTab hlt]; exact hok⟩

/-- **The spin facts survive a store to another location** whose planned
release, if any, does not give `l` away (whole-location plans). -/
theorem SpinU.store_other {A : Arch} {pl : Plan} {tid : Nat} {l : Loc} {ψ : Pred} {K : Time} {σ σ' : State I}
    {k : StoreKind} {xcl : Bool} {a : BitVec 64} {n : Nat} {v : Val} {b : Bool} (h : SpinU l ψ K σ)
    (hs : (EnvGTU I A tid pl).step (.store k xcl a n v) σ b σ') (hne : l ≠ ⟨a, n⟩) (hwh : pl.Whole ⟨a, n⟩ v)
    (hng : l ∉ pl.gives ⟨a, n⟩ v) : SpinU l ψ K σ' := by
  obtain ⟨c, tw, hanc, hws, -, hwv, -, ⟨P, -, hr⟩, -⟩ := step_storeFactsTU hs
  obtain ⟨hf, hc, ⟨vK, hm⟩, ι, hlt, ha, hok⟩ := h
  have hghost : σ.g.Le σ'.g := hanc.ghost
  refine ⟨by rw [hwv.fwdOther l hne]; exact hf, Nat.le_trans hc (hwv.mono.coh l),
    ⟨vK, writeSnap_read? hws (hanc.snap.read? hm)⟩, ι, Nat.lt_of_lt_of_le hlt hghost.acqTab.length_le, ?_,
    by rw [Ghost.acqPred_of_prefix hghost.acqTab hlt]; exact hok⟩
  rw [hr]
  unfold Plan.after
  split
  · rw [Res.addW_acq, pl.keep_of_whole hwh]
    simp only [Res.drop, hng, ↓reduceIte]
    exact ha
  · rw [Res.addW_acq]; exact ha

/-- **A cumulative spin read** (a non-forwarded acquire load of `l` with
spin facts at `K`): the read `tr ≥ K` is a message of the new snapshot,
below the new views; the spin facts move to `tr`; fully held locations are
kept; and every message `t ∈ (K, tr]` with an impure value `u` (read or
skipped) had a slot satisfying `ψ` at `u`, everything of which the thread
held fully is now all the thread's, with the slot's write sets (and the
thread held none of it before). -/
theorem spinU_read {A : Arch} {pl : Plan} {tid : Nat} {a : BitVec 64} {n : Nat} {ψ : Pred} {K : Time}
    {σ σ' : State I} {k : LoadKind} {v : Val} (hacqk : (A.loadKind k).isAcquire = true)
    (hrel : σ.g.rel ⟨a, n⟩ = ψ) (hsp : SpinU ⟨a, n⟩ ψ K σ)
    (hs : (EnvGTU I A tid pl).step (.load k false a n) σ v σ') :
    ∃ tr, SpinU ⟨a, n⟩ ψ tr σ' ∧ K ≤ tr ∧ σ'.snap.mem.read? ⟨a, n⟩ tr = some v ∧
      tr ≤ σ'.vs.vrNew ∧ tr ≤ σ'.vs.vwNew ∧
      ∀ t u, K < t → t ≤ tr → σ'.snap.mem.read? ⟨a, n⟩ t = some u → ¬ Pred.Pure ψ u →
        ∃ R, ψ.P u σ'.snap.mem t R ∧
          ∀ x, (R.wr x).q = 1 → (σ.r.wr x).q = 0 ∧ (σ'.r.wr x).q = 1 ∧ ∀ p, (σ'.r.wr x).X p ↔ (R.wr x).X p := by
  obtain ⟨ga, hanc, ⟨rF, E⟩, -, tr, hrd, hlv, a', ha, hr, hg, -⟩ := step_loadFactsTU hs
  obtain ⟨hfw, hcoh, ⟨vK, hmsg⟩, ι, hlt, hacq1, hok⟩ := hsp
  have hn := hanc.lt
  have hacq : σ.r.acq ⟨a, n⟩ ι = 1 := Nat.le_antisymm (E.thread_acq_le hn _ _) hacq1
  have hnf := not_fwded_of_none (tr := tr) hfw
  have hc : TakeCond A k σ.vs ⟨a, n⟩ tr := ⟨hacqk, hnf⟩
  have hok' : OkPred ψ (ga.acqPred ι) K := by rw [hanc.acqPred hlt]; exact hok
  have hK' : σ'.snap.mem.read? ⟨a, n⟩ K = some vK := hanc.snap.read? hmsg
  have hKtr : K ≤ tr := by
    refine Nat.le_of_not_lt fun hlt' => ?_
    obtain ⟨w, hw, hl, -⟩ : ∃ w, σ'.snap.mem.get? K = some w ∧ w.loc = ⟨a, n⟩ ∧ w.val = vK := by
      have h0 : K ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt')
      simp only [Memory.read?, h0, ↓reduceIte] at hK'
      split at hK'
      · next w hw =>
        by_cases hl : w.loc = ⟨a, n⟩
        · simp only [hl, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hK'
          exact ⟨w, hw, hl, hK'⟩
        · simp [hl] at hK'
      · cases hK'
    have hB : K ≤ readBound A σ.vs k ⟨a, n⟩ := Nat.le_trans hcoh (Nat.le_max_right _ _)
    have := (Memory.writeIn_iff _ _ _ _).mpr ⟨K, w, hlt', hB, hw, hl⟩
    rw [hrd.window] at this; cases this
  obtain ⟨ι', L, hL, h1, h2, hp⟩ := takeEffU_held ha hacq1 (hanc.acqLen hlt)
  have hvw := hlv.acq hacqk hnf
  refine ⟨tr, ⟨by rw [hlv.getFwd]; exact hfw, hlv.coh hnf, ⟨v, hrd.val⟩, ι', by rw [hg]; exact h2,
    by rw [hr]; exact h1, by rw [hg, hp]; exact hok'.takeAtL hKtr hL⟩, hKtr, hrd.val, hvw.1, hvw.2, ?_⟩
  intro t u hKt htr hrt himp
  obtain ⟨s, hs, hkey, hid, hP⟩ := slot_of_seen (k := (⟨a, n⟩, t)) E hn hacq hrt
    (by rw [hanc.rel, hrel]; exact himp)
  have hPs : ψ.P u σ'.snap.mem t s.res := by
    rcases hok' u _ t s.res hP with h | ⟨h, -⟩
    · exact h
    · exact absurd h (Nat.not_le.mpr hKt)
  refine ⟨s.res, hPs, fun x hq => ?_⟩
  have hsum := E.q_add_le_one_slot hn hs x
  rw [setRes_self, hq] at hsum
  have h0 := (σ.r.wr x).nonneg
  obtain ⟨hq', hX'⟩ := loadFactsTU_wr_full ⟨rF, E⟩ hn ha hr hc hs hkey htr (by rw [hid]; exact hacq) hq
  exact ⟨by grind, hq', hX'⟩

#print axioms prev_of_snap
#print axioms read?_of_writeSnap
#print axioms takeEffU_full
#print axioms spinU_read

end Kraken.Promising.SLR.EnvG.SpscA

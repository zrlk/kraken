/-
**The x64 xchg spinlock's release on `EnvG`**: the
lock's plan, the release `StoreOk` of `movl $0, (Lk)` (a plain store, hence a
release, under `Arch.tso`) at a holding state, and what the thread keeps
(`Post` of `SLR/Adequacy.lean`). ISA-neutral.

**Why not `CasRelease.lockPlan`.** A failed `xchg` still writes (`1`), so it
claims the update slots of the message it read. When that message's low word
is not `0`, `lockPred` says nothing about the slots, so the thread's resource
gains an unknown part (`junk`), possibly with a share of the counter. The CAS
lock's `lockPlan` gives the whole counter away and its `Bad` disjunct needs `Pool`'s
`(r.wr C).q = 1` *exactly*, which an unclean thread with junk cannot show.
`xlockPlan` differs from `lockPlan` in one place: it gives a share of exactly
`1` of the counter (`Perm.take 1`, the write set along) and keeps the rest.
Everything else (`lockGives`, `lockDelta`, `Perm.leaveD` for the lock) is the
CAS lock's, reused from `EnvG/CasRelease.lean`.

- `Res.share2Give`/`Res.share2Keep`, `Plan.Split.share2D`: `CasRelease`'s
  `shareD` split with a second clamped location (now in `EnvG/SplitD.lean`,
  moved unchanged).
- `xlockSplit`, `xlockPlan` and its lemmas.
- `HoldingWX`: `CasRelease.HoldingW` with `1 ≤ (r.wr C).q`.
- `storeOk_xlockRelease`: as `storeOk_lockRelease`, at `Arch.tso` and store
  kind `.plain`.
- `xlockRelease_post`: as `lockRelease_post`.

The two-location split generalises `Plan.Split.shareD` (and
`share`); both could move to `EnvG/Split.lean`, and `lockPlan` could be
`xlockPlan` (for CAS the counter share is exactly `1`, so `take 1` gives all
of it).
-/
import Kraken.Promising.SLR.EnvG.CasRelease
import Kraken.Promising.SLR.EnvG.SplitD

namespace Kraken.Promising.SLR.EnvG.X64Spin

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvG.CasSmoke
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

variable {I : ISA}

/-! ## The plan -/

/-- **The x64 lock release split**: `CasSmoke.lockSplit` with exactly a share
`1` of the counter given. -/
noncomputable def xlockSplit (P : Sys) (tid : Nat) : Plan.Split P.Lk :=
  Plan.Split.share2D P.Lk (lockGives P tid) (lockDelta P) (fun cl r hq => lockDelta_lt P cl r hq) P.C
    (fun _ _ => 1)

/-- **The x64 lock's plan**: a write of `0` to `Lk` is a release with
`xlockSplit`. -/
noncomputable def xlockPlan (P : Sys) (tid : Nat) : Plan :=
  ⟨[{ loc := P.Lk, val := some 0, gives := [], split := some (xlockSplit P tid) }]⟩

theorem xlockPlan_valid (P : Sys) (tid : Nat) : (xlockPlan P tid).Valid := by
  intro e he
  simp only [xlockPlan, List.mem_singleton] at he
  subst he
  exact List.not_mem_nil

theorem xlockPlan_find (P : Sys) (tid : Nat) :
    (xlockPlan P tid).find? P.Lk 0 =
      some { loc := P.Lk, val := some 0, gives := [], split := some (xlockSplit P tid) } := by
  simp [xlockPlan, Plan.find?]

theorem xlockPlan_rel_zero (P : Sys) (tid : Nat) : (xlockPlan P tid).rel P.Lk 0 = true := by
  rw [Plan.rel, xlockPlan_find]; rfl

theorem xlockPlan_rel_ne {P : Sys} {tid : Nat} {l : Loc} (h : l ≠ P.Lk) (v : Val) :
    (xlockPlan P tid).rel l v = false := by
  simp [xlockPlan, Plan.rel, Plan.find?, Ne.symm h]

theorem xlockPlan_rel_one {P : Sys} {tid : Nat} : (xlockPlan P tid).rel P.Lk 1#128 = false := by
  simp [xlockPlan, Plan.rel, Plan.find?]

/-- The plan gives no location whole (`RelRmwGiveOk.of_gives_nil`). -/
theorem xlockPlan_gives (P : Sys) (tid : Nat) (l : Loc) (v : Val) : (xlockPlan P tid).gives l v = [] := by
  simp only [Plan.gives, xlockPlan, Plan.find?, List.find?]
  split <;> rfl

theorem xlockPlan_give (P : Sys) (tid : Nat) (cl : Prop) (r : Res) :
    (xlockPlan P tid).give P.Lk 0 cl r = Res.share2Give (lockGives P tid) P.Lk (lockDelta P cl r) P.C 1 r := by
  rw [Plan.give, xlockPlan_find]; rfl

theorem xlockPlan_keep (P : Sys) (tid : Nat) (cl : Prop) (r : Res) :
    (xlockPlan P tid).keep P.Lk 0 cl r = Res.share2Keep (lockGives P tid) P.Lk (lockDelta P cl r) P.C 1 r := by
  rw [Plan.keep, xlockPlan_find]; rfl

theorem xlockPlan_after (P : Sys) (tid : Nat) (tw : Time) (cl : Prop) (r : Res) :
    (xlockPlan P tid).after P.Lk 0 tw cl r =
      (Res.share2Keep (lockGives P tid) P.Lk (lockDelta P cl r) P.C 1 r).addW P.Lk (0, tw) := by
  simp only [Plan.after, xlockPlan_rel_zero, ↓reduceIte, xlockPlan_keep]

/-! ## The release -/

/-- **Holding, as far as the release needs it**: `CasSmoke.HoldingW` with at
least (not exactly) all of `C`. -/
def HoldingWX (P : Sys) (tid : Nat) (S : Nat → Bool) (r : Res) : Prop :=
  1 ≤ (r.wr P.C).q ∧ tid < P.N ∧ 1 ≤ (r.wr (P.F tid)).q ∧ 0 < (r.wr P.Lk).q ∧
    ∀ j < P.N, j ≠ tid → (S j = false → 1 / 2 ≤ (r.wr (P.K j)).q) ∧ (S j = true → 1 ≤ (r.wr (P.F j)).q)

/-- The share `1` of `C` given is exactly `1`, with `C`'s write set. -/
theorem take_one_q {a : Perm} (h : 1 ≤ a.q) : (a.take 1).q = 1 := a.take_q_of (by decide) h

theorem take_one_X {a : Perm} (h : 1 ≤ a.q) (p : Val × Time) : (a.take 1).X p ↔ a.X p := by
  have := take_one_q h
  simp only [Perm.take] at this ⊢
  constructor
  · exact And.right
  · exact fun hp => ⟨by rw [this]; decide, hp⟩

/-- The pool for `S[tid := true]` in what an x64 lock release gives. -/
theorem pool_xlockGive {P : Sys} {tid : Nat} (hL : SpinLocs P.N P.Lk P.C P.K P.F) {S : Nat → Bool} {r : Res}
    (hH : HoldingWX P tid S r) (δ : Rat) :
    Pool P.N P.C P.K P.F (setTrue S tid) (Res.share2Give (lockGives P tid) P.Lk δ P.C 1 r) := by
  obtain ⟨hC, htid, hFt, -, hS⟩ := hH
  refine ⟨?_, fun j hj => ⟨fun hSj => ?_, fun hSj => ?_⟩⟩
  · rw [Res.share2Give_wr_y (Ne.symm hL.lk_c)]; exact take_one_q hC
  · have hne : j ≠ tid := fun e => by subst e; simp [setTrue] at hSj
    have hSj' : S j = false := by simpa [setTrue, hne] using hSj
    rw [Res.share2Give_wr_ne (hL.k_lk j hj) (hL.k_c j hj)
      (by simp [lockGives]; exact .inr (.inl ⟨j, ⟨hj, hne⟩, rfl⟩))]
    exact ((hS j hj hne).1 hSj')
  · rw [Res.share2Give_wr_ne (hL.f_lk j hj) (hL.f_c j hj) (by simp [lockGives]; exact .inr (.inr ⟨j, hj, rfl⟩))]
    by_cases hne : j = tid
    · subst hne; exact hFt
    · have hSj' : S j = true := by simpa [setTrue, hne] using hSj
      exact (hS j hj hne).2 hSj'

/-- **The x64 lock's release VC** (`movl $0, (Lk)`, a plain store of `0`, a
release under `Arch.tso`) at a holding state (`HoldingWX`), and, in clean
mode, at least the own lock share and either the counter relation for
`S[tid := true]` below `vwOld` or a surplus of the lock. Unclean, nothing more
is assumed. (`CasSmoke.storeOk_lockRelease` for `xlockPlan` under `Arch.tso`.) -/
theorem storeOk_xlockRelease {P : Sys} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N)
    {tid : Nat} {σ : State I} (hW : World P σ.g) {S : Nat → Bool} (hH : HoldingWX P tid S σ.r)
    (hclean : σ.cl → 1 / (P.N : Rat) ≤ (σ.r.wr P.Lk).q ∧
      ((∃ k ts, CounterGood P (setTrue S tid) k ts σ.r ∧ ts ≤ σ.vs.vwOld) ∨
        1 / (P.N : Rat) < (σ.r.wr P.Lk).q)) :
    StoreOk Arch.tso tid (xlockPlan P tid) σ .plain false P.Lk 0 := by
  have hpos : 0 < (σ.r.wr P.Lk).q := hH.2.2.2.1
  have hN : (0 : Rat) < 1 / (P.N : Rat) := one_div_pos hN0
  refine ⟨rfl, hpos, fun h => absurd (xlockPlan_rel_zero P tid) (by rw [h]; decide),
    fun _ => ⟨.inl rfl, ?_, by rw [xlockPlan_gives]; exact List.not_mem_nil, ?_⟩⟩
  · rw [hW.1]; exact lockPred_not_pure_zero
  intro c g _ hwb
  rw [hW.1, xlockPlan_give]
  intro _
  have hbad : 0 < lockDelta P σ.cl σ.r →
      Bad P.N P.Lk P.C P.K P.F (Res.share2Give (lockGives P tid) P.Lk (lockDelta P σ.cl σ.r) P.C 1 σ.r) :=
    fun h0 =>
    ⟨by rw [Res.share2Give_wr_self, Perm.take_q_of _ (by grind) (Rat.le_of_lt (lockDelta_lt P _ _ hpos))]; exact h0,
      _, pool_xlockGive hL hH _⟩
  by_cases hcl : σ.cl
  · obtain ⟨hown, hmode⟩ := hclean hcl
    by_cases hs : 1 / (P.N : Rat) < (σ.r.wr P.Lk).q
    · right
      apply hbad
      simp only [lockDelta, hcl, hs, hN, and_self, ↓reduceIte]; grind
    · have hgood := hmode.resolve_right hs
      obtain ⟨k, ts, ⟨⟨hX, hmax⟩, hk⟩, hts⟩ := hgood
      left
      have hCw : (Res.share2Give (lockGives P tid) P.Lk (lockDelta P σ.cl σ.r) P.C 1 σ.r).wr P.C =
          (σ.r.wr P.C).take 1 := Res.share2Give_wr_y (Ne.symm hL.lk_c)
      refine ⟨k, setTrue S tid, ts, pool_xlockGive hL hH _, by rw [hCw, take_one_X hH.1]; exact hX,
        fun p hp => hmax p (by rw [hCw, take_one_X hH.1] at hp; exact hp), hk, ?_⟩
      have := hwb.rel rfl
      simp only [Time, View] at *
      omega
  · right
    apply hbad
    simp only [lockDelta, hcl, ↓reduceIte]; grind

/-- **After a clean x64 release**: `Post` (`CasSmoke.lockRelease_post` for
`xlockPlan`). -/
theorem xlockRelease_post {P : Sys} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N)
    {tid : Nat} (htid : tid < P.N) (tw : Time) {Pc : Prop} (hP : Pc) {r : Res}
    (hK : 1 ≤ (r.wr (P.K tid)).q) (hown : 1 / (P.N : Rat) ≤ (r.wr P.Lk).q)
    (hX : ¬ 1 / (P.N : Rat) < (r.wr P.Lk).q → ∀ p, (r.wr P.Lk).X p → p.1 ≠ 0 → p.2 < tw) :
    Post P.N P.Lk P.K ((xlockPlan P tid).after P.Lk 0 tw Pc r) := by
  have hN : (0 : Rat) < 1 / (P.N : Rat) := one_div_pos hN0
  have hKg : P.K tid ∉ lockGives P tid := by
    intro h
    simp only [lockGives, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at h
    rcases h with h | ⟨j, ⟨hj, hne⟩, e⟩ | ⟨j, hj, e⟩
    · exact hL.k_c tid htid h
    · exact hne (hL.k_inj j hj tid htid e)
    · exact hL.k_f tid htid j hj e.symm
  rw [xlockPlan_after]
  have hδ : lockDelta P Pc r = if 1 / (P.N : Rat) < (r.wr P.Lk).q then (r.wr P.Lk).q - 1 / (P.N : Rat) else 0 := by
    simp only [lockDelta, hP, hN, and_true, ↓reduceIte]
  have hkq : ((Res.share2Keep (lockGives P tid) P.Lk (lockDelta P Pc r) P.C 1 r).wr P.Lk).q =
      (r.wr P.Lk).q - (r.wr P.Lk).clampQ (lockDelta P Pc r) := by
    simp only [Res.share2Keep, ↓reduceIte, Perm.leaveD]
  have hq' : 1 / (P.N : Rat) ≤ (r.wr P.Lk).q - (r.wr P.Lk).clampQ (lockDelta P Pc r) := by
    rw [hδ]; simp only [Perm.clampQ]; split <;> grind
  refine ⟨⟨tid, htid, ?_⟩, ?_, fun p hp hp0 => ?_⟩
  · rw [Res.addW_wr_ne _ _ (hL.k_lk tid htid)]
    simp only [Res.share2Keep, hL.k_lk tid htid, hL.k_c tid htid, hKg, ↓reduceIte]
    exact hK
  · rw [Res.addW_q, hkq]; exact hq'
  · have hpos : 0 < ((Res.share2Keep (lockGives P tid) P.Lk (lockDelta P Pc r) P.C 1 r).wr P.Lk).q := by
      rw [hkq]; grind
    refine ⟨(0, tw), (Res.addW_X_self _ _ _ _).mpr (.inr ⟨hpos, rfl⟩), rfl, ?_⟩
    rcases (Res.addW_X_self _ _ _ _).mp hp with hp | ⟨-, rfl⟩
    · simp only [Res.share2Keep, ↓reduceIte, Perm.leaveD] at hp
      obtain ⟨hc0, -, hp⟩ := hp
      refine hX (fun hs => ?_) p hp hp0
      rw [hδ] at hc0
      simp only [hs, ↓reduceIte, Perm.clampQ] at hc0
      grind
    · exact absurd rfl hp0

end Kraken.Promising.SLR.EnvG.X64Spin

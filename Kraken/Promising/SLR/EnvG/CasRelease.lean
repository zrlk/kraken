/-
**The CAS spinlock's release on `EnvG`**: the lock's plan
with a resource-dependent split (`Plan.Split`, F1), the release `StoreOk` of
`stlr wzr, [Lk]` at a holding state, and what the thread keeps (`Post` of
`SLR/Adequacy.lean`). ISA-neutral.

Ported from the F1 prototype (definitions copied):
`lockGives`, `lockDelta`, `lockSplit`, `lockPlan`, `pool_lockGive`,
`storeOk_lockRelease`, `lockRelease_post` (the prototype's `lockRelease_after`,
extended to `Post`). `setTrueS` is not copied: `SpinCommon.setTrue`
(`SLR/SpinRelease.lean`, ISA-neutral) is used.

**Changes against the prototype:**
- *The split drops the kept write set of `Lk` when it gives a share*
  (`Perm.leaveD`, `Res.shareKeepD`, `Plan.Split.shareD`, now in
  `EnvG/SplitD.lean`; the generic
  `Plan.Split.share` of `EnvG/Split.lean` keeps it). `Post`'s write-set
  clause (every non-zero own write of `Lk` is followed by a write of `0`)
  cannot be shown for writes forwarded inside an acquired `Bad` share: the
  lock predicate does not bound their timestamps. With `shareD`, a release
  that gives a share (`Bad`: clean surplus, or unclean) keeps no write of
  `Lk` but its own unlock, and a release that gives none (clean, `Good`) holds
  exactly `1/N` of `Lk`, so its acquired slots carried no `Lk` share and its
  write set of `Lk` is its own.
- `lockDelta` tests `0 < 1/N` itself, so `lockPlan P tid` takes no `hN`.
-/
import Kraken.Promising.SLR.EnvG.SplitD
import Kraken.Promising.SLR.EnvG.Simp
import Kraken.Promising.SLR.SpinClaim
import Kraken.Promising.SLR.SpinAcquire
import Kraken.Promising.SLR.SpinRelease

namespace Kraken.Promising.SLR.EnvG.CasSmoke

open Kraken Kraken.Promising Kraken.Promising.SLR.EnvG
open Kraken.Promising.SLR.Spinlock Kraken.Promising.SLR.SpinCommon

variable {I : ISA}

/-! ## The lock's plan -/

/-- The locations a lock release gives whole: the counter, the pool's half of
`K j` (`j ≠ tid`), and every `F j`. -/
def lockGives (P : Sys) (tid : Nat) : List Loc :=
  P.C :: (((List.range P.N).filter (· ≠ tid)).map P.K ++ (List.range P.N).map P.F)

open Classical in
/-- The share of `Lk` a lock release gives (`SwpRelease`'s three cases):
clean with a surplus `q - 1/N`, clean without `0`, unclean `q/2`. -/
noncomputable def lockDelta (P : Sys) (cl : Prop) (r : Res) : Rat :=
  if cl then (if 1 / (P.N : Rat) < (r.wr P.Lk).q ∧ 0 < 1 / (P.N : Rat) then (r.wr P.Lk).q - 1 / (P.N : Rat) else 0)
  else (r.wr P.Lk).q / 2

theorem lockDelta_lt (P : Sys) (cl : Prop) (r : Res) (hq : 0 < (r.wr P.Lk).q) : lockDelta P cl r < (r.wr P.Lk).q := by
  unfold lockDelta
  split
  · split
    · grind
    · exact hq
  · grind

/-- **The lock release split** (`shareD`: a share given takes the write set
of `Lk` along). -/
noncomputable def lockSplit (P : Sys) (tid : Nat) : Plan.Split P.Lk :=
  Plan.Split.shareD P.Lk (lockGives P tid) (lockDelta P) fun cl r hq => lockDelta_lt P cl r hq

/-- **The lock's plan**: a write of `0` to `Lk` is a release with
`lockSplit`. -/
noncomputable def lockPlan (P : Sys) (tid : Nat) : Plan :=
  ⟨[{ loc := P.Lk, val := some 0, gives := [], split := some (lockSplit P tid) }]⟩

theorem lockPlan_valid (P : Sys) (tid : Nat) : (lockPlan P tid).Valid := by
  intro e he
  simp only [lockPlan, List.mem_singleton] at he
  subst he
  exact List.not_mem_nil

theorem lockPlan_find (P : Sys) (tid : Nat) :
    (lockPlan P tid).find? P.Lk 0 = some { loc := P.Lk, val := some 0, gives := [], split := some (lockSplit P tid) } := by
  simp [lockPlan, Plan.find?]

theorem lockPlan_rel_zero (P : Sys) (tid : Nat) : (lockPlan P tid).rel P.Lk 0 = true := by
  rw [Plan.rel, lockPlan_find]; rfl

theorem lockPlan_rel_ne {P : Sys} {tid : Nat} {l : Loc} (h : l ≠ P.Lk) (v : Val) : (lockPlan P tid).rel l v = false := by
  simp [lockPlan, Plan.rel, Plan.find?, Ne.symm h]

theorem lockPlan_rel_one {P : Sys} {tid : Nat} : (lockPlan P tid).rel P.Lk 1#128 = false := by
  simp [lockPlan, Plan.rel, Plan.find?]

theorem lockPlan_give (P : Sys) (tid : Nat) (cl : Prop) (r : Res) :
    (lockPlan P tid).give P.Lk 0 cl r = Res.shareGive (lockGives P tid) P.Lk (lockDelta P cl r) r := by
  rw [Plan.give, lockPlan_find]; rfl

theorem lockPlan_keep (P : Sys) (tid : Nat) (cl : Prop) (r : Res) :
    (lockPlan P tid).keep P.Lk 0 cl r = Res.shareKeepD (lockGives P tid) P.Lk (lockDelta P cl r) r := by
  rw [Plan.keep, lockPlan_find]; rfl

theorem lockPlan_after (P : Sys) (tid : Nat) (tw : Time) (cl : Prop) (r : Res) :
    (lockPlan P tid).after P.Lk 0 tw cl r =
      (Res.shareKeepD (lockGives P tid) P.Lk (lockDelta P cl r) r).addW P.Lk (0, tw) := by
  simp only [Plan.after, lockPlan_rel_zero, ↓reduceIte, lockPlan_keep]

/-! ## The release -/

/-- **Holding, as far as the release needs it** (`SpinCommon.Holding` without
`S tid = false` and the own token `K tid`, which need the validity of the
thread's resource with its acquired slots, known only in clean mode): all of
`C`, the own fresh token `F tid`, a positive lock share, and the pool's part
for `S` of the other threads' tokens. -/
def HoldingW (P : Sys) (tid : Nat) (S : Nat → Bool) (r : Res) : Prop :=
  (r.wr P.C).q = 1 ∧ tid < P.N ∧ 1 ≤ (r.wr (P.F tid)).q ∧ 0 < (r.wr P.Lk).q ∧
    ∀ j < P.N, j ≠ tid → (S j = false → 1 / 2 ≤ (r.wr (P.K j)).q) ∧ (S j = true → 1 ≤ (r.wr (P.F j)).q)

theorem Holding.toW {P : Sys} {tid : Nat} {S : Nat → Bool} {r : Res} (h : Holding P tid S r) : HoldingW P tid S r :=
  ⟨h.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- The pool for `S[tid := true]` in what a lock release gives. -/
theorem pool_lockGive {P : Sys} {tid : Nat} (hL : SpinLocs P.N P.Lk P.C P.K P.F) {S : Nat → Bool} {r : Res}
    (hH : HoldingW P tid S r) (δ : Rat) :
    Pool P.N P.C P.K P.F (setTrue S tid) (Res.shareGive (lockGives P tid) P.Lk δ r) := by
  obtain ⟨hC, htid, hFt, -, hS⟩ := hH
  refine ⟨?_, fun j hj => ⟨fun hSj => ?_, fun hSj => ?_⟩⟩
  · rw [Res.shareGive_wr_ne (Ne.symm hL.lk_c) (by simp [lockGives])]; exact hC
  · have hne : j ≠ tid := fun e => by subst e; simp [setTrue] at hSj
    have hSj' : S j = false := by simpa [setTrue, hne] using hSj
    rw [Res.shareGive_wr_ne (hL.k_lk j hj) (by simp [lockGives]; exact .inr (.inl ⟨j, ⟨hj, hne⟩, rfl⟩))]
    exact ((hS j hj hne).1 hSj')
  · rw [Res.shareGive_wr_ne (hL.f_lk j hj) (by simp [lockGives]; exact .inr (.inr ⟨j, hj, rfl⟩))]
    by_cases hne : j = tid
    · subst hne; exact hFt
    · have hSj' : S j = true := by simpa [setTrue, hne] using hSj
      exact (hS j hj hne).2 hSj'

/-- **The CAS lock's release VC** (`stlr wzr, [Lk]`, a release store of `0`)
at a holding state: the pool for `S` merged in (`HoldingW`), and, in clean
mode, at least the own lock share and either the counter relation for
`S[tid := true]` below `vwOld` or a surplus of the lock. Unclean, nothing
more is assumed. -/
theorem storeOk_lockRelease {P : Sys} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N)
    {tid : Nat} {σ : State I} (hW : World P σ.g) {S : Nat → Bool} (hH : HoldingW P tid S σ.r)
    (hclean : σ.cl → 1 / (P.N : Rat) ≤ (σ.r.wr P.Lk).q ∧
      ((∃ k ts, CounterGood P (setTrue S tid) k ts σ.r ∧ ts ≤ σ.vs.vwOld) ∨
        1 / (P.N : Rat) < (σ.r.wr P.Lk).q)) :
    StoreOk Arch.armv8 tid (lockPlan P tid) σ .rel false P.Lk 0 := by
  have hpos : 0 < (σ.r.wr P.Lk).q := hH.2.2.2.1
  have hN : (0 : Rat) < 1 / (P.N : Rat) := one_div_pos hN0
  have hgives : (lockPlan P tid).gives P.Lk 0 = [] := by rw [Plan.gives, lockPlan_find]; rfl
  refine ⟨rfl, hpos, fun h => absurd (lockPlan_rel_zero P tid) (by rw [h]; decide),
    fun _ => ⟨effRel_rel _ _, ?_, by rw [hgives]; exact List.not_mem_nil, ?_⟩⟩
  · rw [hW.1]; exact lockPred_not_pure_zero
  intro c g _ hwb
  rw [hW.1, lockPlan_give]
  intro _
  have hbad : 0 < lockDelta P σ.cl σ.r →
      Bad P.N P.Lk P.C P.K P.F (Res.shareGive (lockGives P tid) P.Lk (lockDelta P σ.cl σ.r) σ.r) := fun h0 =>
    ⟨by rw [Res.shareGive_wr_self, Perm.take_q_of _ (by grind) (Rat.le_of_lt (lockDelta_lt P _ _ hpos))]; exact h0,
      _, pool_lockGive hL hH _⟩
  by_cases hcl : σ.cl
  · obtain ⟨hown, hmode⟩ := hclean hcl
    by_cases hs : 1 / (P.N : Rat) < (σ.r.wr P.Lk).q
    · right
      apply hbad
      simp only [lockDelta, hcl, hs, hN, and_self, ↓reduceIte]; grind
    · have hgood := hmode.resolve_right hs
      obtain ⟨k, ts, ⟨⟨hX, hmax⟩, hk⟩, hts⟩ := hgood
      left
      have hCw : (Res.shareGive (lockGives P tid) P.Lk (lockDelta P σ.cl σ.r) σ.r).wr P.C = σ.r.wr P.C :=
        Res.shareGive_wr_ne (Ne.symm hL.lk_c) (by simp [lockGives])
      refine ⟨k, setTrue S tid, ts, pool_lockGive hL hH _, by rw [hCw]; exact hX,
        fun p hp => hmax p (by rw [hCw] at hp; exact hp), hk, ?_⟩
      have := hwb.rel rfl
      simp only [Time, View] at *
      omega
  · right
    apply hbad
    simp only [lockDelta, hcl, ↓reduceIte]; grind

/-- **After a clean release** (what `StoreFacts` gives, `σ'.r = after … Pc r`
with `σ.cl → Pc`, at `Pc`): `Post`. The own token `K tid` is kept whole, the
lock share is at least `1/N`, and the write set of `Lk` is the unlock alone
(a share was given) or, without a surplus, the own writes, each below the
unlock (`hX`). -/
theorem lockRelease_post {P : Sys} (hL : SpinLocs P.N P.Lk P.C P.K P.F) (hN0 : 0 < P.N)
    {tid : Nat} (htid : tid < P.N) (tw : Time) {Pc : Prop} (hP : Pc) {r : Res}
    (hK : 1 ≤ (r.wr (P.K tid)).q) (hown : 1 / (P.N : Rat) ≤ (r.wr P.Lk).q)
    (hX : ¬ 1 / (P.N : Rat) < (r.wr P.Lk).q → ∀ p, (r.wr P.Lk).X p → p.1 ≠ 0 → p.2 < tw) :
    Post P.N P.Lk P.K ((lockPlan P tid).after P.Lk 0 tw Pc r) := by
  have hN : (0 : Rat) < 1 / (P.N : Rat) := one_div_pos hN0
  have hKg : P.K tid ∉ lockGives P tid := by
    intro h
    simp only [lockGives, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq] at h
    rcases h with h | ⟨j, ⟨hj, hne⟩, e⟩ | ⟨j, hj, e⟩
    · exact hL.k_c tid htid h
    · exact hne (hL.k_inj j hj tid htid e)
    · exact hL.k_f tid htid j hj e.symm
  rw [lockPlan_after]
  -- the share given, clean
  have hδ : lockDelta P Pc r = if 1 / (P.N : Rat) < (r.wr P.Lk).q then (r.wr P.Lk).q - 1 / (P.N : Rat) else 0 := by
    simp only [lockDelta, hP, hN, and_true, ↓reduceIte]
  have hkq : ((Res.shareKeepD (lockGives P tid) P.Lk (lockDelta P Pc r) r).wr P.Lk).q =
      (r.wr P.Lk).q - (r.wr P.Lk).clampQ (lockDelta P Pc r) := by
    simp only [Res.shareKeepD, ↓reduceIte, Perm.leaveD]
  have hq' : 1 / (P.N : Rat) ≤ (r.wr P.Lk).q - (r.wr P.Lk).clampQ (lockDelta P Pc r) := by
    rw [hδ]; simp only [Perm.clampQ]; split <;> grind
  refine ⟨⟨tid, htid, ?_⟩, ?_, fun p hp hp0 => ?_⟩
  · rw [Res.addW_wr_ne _ _ (hL.k_lk tid htid)]
    simp only [Res.shareKeepD, hL.k_lk tid htid, hKg, ↓reduceIte]
    exact hK
  · rw [Res.addW_q, hkq]; exact hq'
  · have hpos : 0 < ((Res.shareKeepD (lockGives P tid) P.Lk (lockDelta P Pc r) r).wr P.Lk).q := by
      rw [hkq]; grind
    refine ⟨(0, tw), (Res.addW_X_self _ _ _ _).mpr (.inr ⟨hpos, rfl⟩), rfl, ?_⟩
    rcases (Res.addW_X_self _ _ _ _).mp hp with hp | ⟨-, rfl⟩
    · simp only [Res.shareKeepD, ↓reduceIte, Perm.leaveD] at hp
      obtain ⟨hc0, -, hp⟩ := hp
      refine hX (fun hs => ?_) p hp hp0
      rw [hδ] at hc0
      simp only [hs, ↓reduceIte, Perm.clampQ] at hc0
      grind
    · exact absurd rfl hp0

end Kraken.Promising.SLR.EnvG.CasSmoke

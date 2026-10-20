import WeakCore.TermStep
import WeakCore.TermLiveProps

/-!
# S9: once-only facts (stage B)

Machine-level once-only facts for `SysInv` (TermSys) and the S10 step.

* **Region ids are ghost.**  The runtime never allocates a region id: `region`,
  `regionBuf` and `openPub` bind `tok (lit 0) none`/`ptr (rgn (lit 0))`
  (`TermRun.tstep`); only the typing view names the region, `ridNext η =
  ridPair η.tid η.rid` (TermStep), from a ghost counter `η.rid` that is not in
  `CE` and is existential in `ThInvRE`.  So freshness is not a fact about
  `Step` runs; it is a fact about per-thread ghost counters `rc : Nat → Nat`
  that `SysInv` must carry.  Here: per-thread disjoint id spaces
  (`ridPair_inj`), per-thread strictly increasing ids (`ridPair_lt`), the
  counter bookkeeping (`RidUsed`, `ridSet`), and the stage-A transport that
  lets S10 re-pick a thread's view with its counter at `rc i` (`raiseRid_inv`,
  `repick_fresh`) so that `MintStep.fresh` mints an unused id.
* **Mints of `wd`.**  Only `MintStep.fresh` mints `wd` (`MintStep_wd`); the
  proposed `MintOK` (`MintOKL`: distinct fresh ids plus a `wd`-free rest) is
  kept by every `MintStep` (`MintOKL_step`) and gives `M (wd n) ≤ 1`.
* **The fresh-mint key lemma** (`keySum_fresh`, `fresh_key_le_one`): at a key
  nobody holds before, the stepping thread's post bound `≤ 1` gives `KeySum`.
  Promise credits are zero at `wd`, and debits at `wd n`/`rg n` when no Σ word
  names `n` (`pSum_PromCr_wd`, `pSum_PromCr_rg`).
* **EpochMono, globally.**  Over memory alone: `EpochLocal Ep mem` (every
  message at an epoch address is a number at least its coherence predecessor,
  promises included) implies monotonicity along coherence (`EpochLocal.mono`),
  hence TermStep's `EpochMono` (`EpochMono_of_local`); it is kept by any
  memory extension whose new messages are locally monotone (`EpochLocal_ext`),
  along `Step` (`EpochLocal_step`) and `Steps` (`EpochLocal_steps`).  Once-only
  of epoch mints at one address: `epoch_mint_once`.
-/

namespace TermOnce

open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address Ts Arch AllocLabel)
open Promises.Sim (MemExt)

/-! ## 1. Region ids -/

theorem ridPair_pos (t k : Nat) : 0 < ridPair t k :=
  Nat.mul_pos (Nat.two_pow_pos t) (by omega)

/-- A thread's ids strictly increase with its counter. -/
theorem ridPair_lt {t k k' : Nat} (h : k < k') : ridPair t k < ridPair t k' := by
  unfold ridPair
  exact Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos t)

theorem ridPair_le {t k k' : Nat} (h : k ≤ k') : ridPair t k ≤ ridPair t k' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt (ridPair_lt h)

/-- The ids handed out under per-thread counters `rc`: thread `t` has used
`ridPair t k` for `k < rc t`. -/
def RidUsed (rc : Nat → Nat) (n : Nat) : Prop := ∃ t k, k < rc t ∧ n = ridPair t k

/-- Thread `t`'s counter set to `r`. -/
def ridSet (rc : Nat → Nat) (t r : Nat) : Nat → Nat := fun t' => if t' = t then r else rc t'

/-- An id at or above its thread's counter is unused. -/
theorem ridPair_unused {rc : Nat → Nat} {t k : Nat} (hk : rc t ≤ k) : ¬ RidUsed rc (ridPair t k) := by
  rintro ⟨t', k', hk', e⟩
  obtain ⟨rfl, rfl⟩ := ridPair_inj e
  omega

theorem RidUsed_mono {rc rc' : Nat → Nat} (h : ∀ t, rc t ≤ rc' t) {n : Nat} (hu : RidUsed rc n) :
    RidUsed rc' n := by
  obtain ⟨t, k, hk, rfl⟩ := hu
  exact ⟨t, k, Nat.lt_of_lt_of_le hk (h t), rfl⟩

theorem ridSet_self (rc : Nat → Nat) (t r : Nat) : ridSet rc t r t = r := by simp [ridSet]

theorem ridSet_other (rc : Nat → Nat) {t t' : Nat} (r : Nat) (h : t' ≠ t) : ridSet rc t r t' = rc t' := by
  simp [ridSet, h]

theorem ridSet_ge {rc : Nat → Nat} {t r : Nat} (h : rc t ≤ r) : ∀ t', rc t' ≤ ridSet rc t r t' := by
  intro t'
  by_cases e : t' = t
  · subst e; rw [ridSet_self]; exact h
  · rw [ridSet_other rc r e]; exact Nat.le_refl _

/-- After a bump, an id is used iff it was, or it is one of thread `t`'s ids
between the old and the new counter. -/
theorem RidUsed_ridSet {rc : Nat → Nat} {t r n : Nat} (h : RidUsed (ridSet rc t r) n) :
    RidUsed rc n ∨ ∃ k, rc t ≤ k ∧ k < r ∧ n = ridPair t k := by
  obtain ⟨t', k, hk, rfl⟩ := h
  by_cases e : t' = t
  · subst e
    rw [ridSet_self] at hk
    by_cases hlt : k < rc t'
    · exact Or.inl ⟨t', k, hlt, rfl⟩
    · exact Or.inr ⟨k, Nat.le_of_not_lt hlt, hk, rfl⟩
  · rw [ridSet_other rc r e] at hk
    exact Or.inl ⟨t', k, hk, rfl⟩

/-- `ridNext η` of a view whose counter is at least its thread's `rc` is
unused, and strictly above every id the thread used. -/
theorem fresh_unused {rc : Nat → Nat} {η : TEnv} (h : rc η.tid ≤ η.rid) :
    ¬ RidUsed rc (ridNext η) ∧ ∀ k, k < rc η.tid → ridPair η.tid k < ridNext η :=
  ⟨ridPair_unused h, fun _ hk => ridPair_lt (Nat.lt_of_lt_of_le hk h)⟩

/-- **The counter after a fresh mint** at `η` (`rc η.tid ≤ η.rid`): thread
`η.tid`'s counter becomes `η.rid + 1`; every used id stays used, the minted
id becomes used, and the counters only grow. -/
theorem fresh_bump {rc : Nat → Nat} {η : TEnv} (h : rc η.tid ≤ η.rid) :
    (∀ t, rc t ≤ ridSet rc η.tid (η.rid + 1) t) ∧ RidUsed (ridSet rc η.tid (η.rid + 1)) (ridNext η) ∧
      (∀ n, RidUsed rc n → RidUsed (ridSet rc η.tid (η.rid + 1)) n) := by
  have hge := ridSet_ge (rc := rc) (t := η.tid) (r := η.rid + 1) (by omega)
  refine ⟨hge, ⟨η.tid, η.rid, ?_, rfl⟩, fun n hn => RidUsed_mono hge hn⟩
  rw [ridSet_self]; omega

/-- A fresh id of thread `η.tid` is no id of any other thread. -/
theorem ridNext_ne_other {η : TEnv} {t k : Nat} (h : t ≠ η.tid) : ridNext η ≠ ridPair t k :=
  ridPair_ne_of_tid (Ne.symm h)

/-! ### Re-picking a thread's view with a raised counter

`ThInvRE` and `SysInvW.env` hide the view `η`; its counter is free above its
current value.  S10 raises it to the thread's `rc` before calling
`tstepMC_step`, so that `MintStep.fresh` names an unused id. -/

/-- `η` with its region counter set to `r`. -/
def raiseRid (η : TEnv) (r : Nat) : TEnv := η.withSto η.sto (Rd := r)

theorem CE_raiseRid (η : TEnv) (r : Nat) : CE (raiseRid η r) = CE η := rfl
theorem raiseRid_rid (η : TEnv) (r : Nat) : (raiseRid η r).rid = r := rfl
theorem raiseRid_tid (η : TEnv) (r : Nat) : (raiseRid η r).tid = η.tid := rfl

theorem Ext_raiseRid {η : TEnv} (hc : Coh η) {r : Nat} (hr : η.rid ≤ r) : Ext η (raiseRid η r) :=
  Ext_withSto hc (fun _ _ h => h) (fun _ => Nat.le_refl _) (hR := hr)

/-- **(S9) The stage-A data survive raising the counter**: `EnvOK` and
`FInvR` at `raiseRid η r` for `r ≥ η.rid`, same `CE`. -/
theorem raiseRid_inv {p : Prog} {η : TEnv} {r : Nat} (hE : EnvOK p η) (hr : η.rid ≤ r) {ρ : Nat → Nat}
    {σs : List Ty} {K : TEnv → Nat → List Word → Res → Prop} {cx : Cx} {env : Env} {Rf : Res}
    (hi : FInvR ρ η σs K cx env Rf) :
    EnvOK p (raiseRid η r) ∧ FInvR ρ (raiseRid η r) σs K cx env Rf := by
  have hx := Ext_raiseRid hE.2.1 hr
  exact ⟨⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, FInvR_ext hE.2.1 hE.2.2 hx hi⟩

/-- **(S9) A view whose fresh id is unused**: from any `η` with the stage-A
data, one with the same `CE` and `tid`, counter `max η.rid (rc η.tid)`, whose
`ridNext` is unused under `rc`. -/
theorem repick_fresh {p : Prog} {η : TEnv} (hE : EnvOK p η) {ρ : Nat → Nat} {σs : List Ty}
    {K : TEnv → Nat → List Word → Res → Prop} {cx : Cx} {env : Env} {Rf : Res}
    (hi : FInvR ρ η σs K cx env Rf) (rc : Nat → Nat) :
    ∃ η', CE η' = CE η ∧ η'.tid = η.tid ∧ rc η.tid ≤ η'.rid ∧ η.rid ≤ η'.rid ∧ EnvOK p η' ∧
      FInvR ρ η' σs K cx env Rf ∧ ¬ RidUsed rc (ridNext η') ∧ η'.wit = η.wit := by
  have h1 : η.rid ≤ max η.rid (rc η.tid) := Nat.le_max_left _ _
  have h2 : rc η.tid ≤ max η.rid (rc η.tid) := Nat.le_max_right _ _
  obtain ⟨hE', hi'⟩ := raiseRid_inv hE h1 hi
  exact ⟨raiseRid η _, rfl, rfl, h2, h1, hE', hi', (fresh_unused (η := raiseRid η _) h2).1, rfl⟩

/-! ## 2. What a step mints at `wd` and `rg` -/

/-- **Only `fresh` mints `wd`**: a `MintStep` creates no `wd n`, or it is the
fresh step at `n = ridNext η`. -/
theorem MintStep_wd {g : G} {η : TEnv} {s s' : St} {C F : Res} (h : MintStep g η s s' C F) (n : Nat) :
    F (.wd n) = 0 ∨ (n = ridNext η ∧ F = Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) := by
  cases h with
  | none => exact Or.inl rfl
  | fresh =>
      by_cases e : n = ridNext η
      · exact Or.inr ⟨e, rfl⟩
      · left; simp [Res.add_apply, e]
  | epoch => left; simp
  | share => left; simp
  | claim => left; simp
  | epoch2 => left; simp
  | alloc => left; simp
  | consume => exact Or.inl rfl

/-- What a step mints at `rg n`: nothing, the fresh id, or a claim consuming
an epoch token of `n`. -/
theorem MintStep_rg {g : G} {η : TEnv} {s s' : St} {C F : Res} (h : MintStep g η s s' C F) (n : Nat) :
    F (.rg n) = 0 ∨ (n = ridNext η ∧ F = Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) ∨
      ∃ j, C = Res.one (.ep n j) ∧ F = Res.one (.rg n) := by
  cases h with
  | none => exact Or.inl rfl
  | fresh =>
      by_cases e : n = ridNext η
      · exact Or.inr (Or.inl ⟨e, rfl⟩)
      · left; simp [Res.add_apply, e]
  | epoch => left; simp
  | share => left; simp
  | claim n' j =>
      by_cases e : n = n'
      · subst e; exact Or.inr (Or.inr ⟨j, rfl, rfl⟩)
      · left; simp [e]
  | epoch2 => left; simp
  | alloc => left; simp
  | consume => exact Or.inl rfl

/-! ## 3. Proposed `Init` and `MintOK` -/

/-- The fresh mints of the ids `L`: `rg n + wd n` each. -/
def MintSum (L : List Nat) : Res := Res.sum (L.map fun n => Res.one (.rg n) + Res.one (.wd n))

/-- **(S9) Proposed `MintOK`, with its witness list**: the cumulative mint is
the fresh mints of pairwise-distinct ids `L` plus a `wd`-free rest `X` (epoch,
share and claim mints).  `MintOK M := ∃ L, MintOKL L M` fits `SysInvW`'s
`Res → Prop`; S10 keeps `L ⊆ RidUsed rc` alongside. -/
def MintOKL (L : List Nat) (M : Res) : Prop := L.Nodup ∧ ∃ X : Res, M = MintSum L + X ∧ ∀ n, X (.wd n) = 0

/-- The proposed `MintOK`. -/
def MintOK (M : Res) : Prop := ∃ L, MintOKL L M

/-- The proposed initial budget: nothing (the `spawn` shape with a non-affine
shared argument; in general `InitOK`). -/
def Init : Res := .zero

theorem MintSum_nil : MintSum [] = .zero := rfl

theorem MintSum_cons (n : Nat) (L : List Nat) :
    MintSum (n :: L) = Res.one (.rg n) + Res.one (.wd n) + MintSum L := rfl

theorem MintSum_wd : ∀ (L : List Nat) (n : Nat), MintSum L (.wd n) = L.count n
  | [], _ => rfl
  | a :: L, n => by
      rw [MintSum_cons, Res.add_apply, Res.add_apply, MintSum_wd L n, List.count_cons]
      by_cases e : a = n
      · subst e; simp [Nat.add_comm]
      · have e' : n ≠ a := Ne.symm e
        simp [e, e']

theorem MintSum_rg : ∀ (L : List Nat) (n : Nat), MintSum L (.rg n) = L.count n
  | [], _ => rfl
  | a :: L, n => by
      rw [MintSum_cons, Res.add_apply, Res.add_apply, MintSum_rg L n, List.count_cons]
      by_cases e : a = n
      · subst e; simp [Nat.add_comm]
      · have e' : n ≠ a := Ne.symm e
        simp [e, e']

theorem count_le_one_of_nodup : ∀ {L : List Nat}, L.Nodup → ∀ n, L.count n ≤ 1
  | [], _, _ => by simp
  | a :: L, h, n => by
      obtain ⟨ha, hL⟩ := List.nodup_cons.1 h
      rw [List.count_cons]
      by_cases e : a = n
      · subst e
        rw [List.count_eq_zero_of_not_mem ha]; simp
      · have := count_le_one_of_nodup hL n
        simp [e]; omega

/-- **`wd` is minted at most once per id.** -/
theorem MintOKL_wd_le {L : List Nat} {M : Res} (h : MintOKL L M) (n : Nat) : M (.wd n) ≤ 1 := by
  obtain ⟨hnd, X, rfl, hX⟩ := h
  rw [Res.add_apply, hX n, MintSum_wd]
  have := count_le_one_of_nodup hnd n
  omega

theorem MintOK_wd_le {M : Res} (h : MintOK M) (n : Nat) : M (.wd n) ≤ 1 :=
  let ⟨_, hL⟩ := h; MintOKL_wd_le hL n

theorem MintOKL_init : MintOKL [] .zero :=
  ⟨List.nodup_nil, .zero, by rw [MintSum_nil, Res.add_zero], fun _ => rfl⟩

/-- **(S9) `MintOK` is kept by every step's mint**: a fresh mint extends `L`
by the minted id (which must be new: S10 gets it from `L ⊆ RidUsed rc` and
`repick_fresh`); every other mint joins the rest. -/
theorem MintOKL_step {g : G} {L : List Nat} {M : Res} (h : MintOKL L M) {η : TEnv} {s s' : St} {C F : Res}
    (hm : MintStep g η s s' C F) (hnew : ridNext η ∉ L) :
    ∃ L', MintOKL L' (M + F) ∧ (∀ n, n ∈ L → n ∈ L') ∧ ∀ n, n ∈ L' → n ∈ L ∨ n = ridNext η := by
  obtain ⟨hnd, X, rfl, hX⟩ := h
  have hF := MintStep_wd hm
  by_cases hf : F = Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))
  · refine ⟨ridNext η :: L, ⟨List.nodup_cons.2 ⟨hnew, hnd⟩, X, ?_, hX⟩, fun n hn => List.mem_cons_of_mem _ hn,
      fun n hn => ?_⟩
    · rw [hf, MintSum_cons]
      exact Res.ext fun k => by simp only [Res.add_apply]; omega
    · rcases List.mem_cons.1 hn with e | e
      · exact Or.inr e
      · exact Or.inl e
  · refine ⟨L, ⟨hnd, X + F, Res.add_assoc _ _ _, fun n => ?_⟩, fun _ h => h, fun n hn => Or.inl hn⟩
    rw [Res.add_apply, hX n]
    rcases hF n with h0 | ⟨-, h1⟩
    · rw [h0]
    · exact absurd h1 hf

/-! ## 4. The fresh-mint key lemma (S10) -/

/-- `TermSys.KeySum`, restated (definitionally equal). -/
def KeySumL (N : Nat) (T : Nat → Res) (HS : Res) (k : Key) : Prop :=
  ((List.range N).map (fun i => T i k)).sum + HS k ≤ 1

theorem sum_range_zero {N : Nat} {f : Nat → Nat} (h0 : ∀ j, j < N → f j = 0) :
    ((List.range N).map f).sum = 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih (fun j hj => h0 j (Nat.lt_succ_of_lt hj))]
      simp [h0 N (Nat.lt_succ_self N)]

theorem sum_range_zero_but {N i : Nat} {f : Nat → Nat} (h0 : ∀ j, j < N → j ≠ i → f j = 0) :
    ((List.range N).map f).sum ≤ f i := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      by_cases e : N = i
      · subst e
        rw [sum_range_zero (fun j hj => h0 j (Nat.lt_succ_of_lt hj) (Nat.ne_of_lt hj))]
        omega
      · rw [h0 N (Nat.lt_succ_self N) e]
        have := ih (fun j hj hne => h0 j (Nat.lt_succ_of_lt hj) hne)
        omega

/-- **(S9) KeySum after a mint at a key nobody else held** (S10's fresh-mint
case for `rg n`/`wd n`, `n = ridNext η` unused): the idle threads hold nothing
at `k`, and the stepping thread's frame plus the shared holding is at most
one. -/
theorem keySum_fresh {N i : Nat} {T : Nat → Res} {HS : Res} {k : Key}
    (hother : ∀ j, j < N → j ≠ i → T j k = 0) (hstep : T i k + HS k ≤ 1) : KeySumL N T HS k := by
  have := sum_range_zero_but (f := fun j => T j k) hother
  unfold KeySumL
  omega

/-- **(S9) The stepping thread's bound at a fresh key**, from `tstepMC_step`'s
inequality: nothing at `k` before (frame `Rf + Rs`, holding `H`, credits
`pSum cr`, new debits `pSum db'`) and `F k ≤ 1` (the fresh mint) ⟹ the new
total and holding carry at most one `k`. -/
theorem fresh_key_le_one {Tot H' cr' db C Rf Rs H cr db' F : Res} {k : Key}
    (hle : Tot + H' + cr' + db + C ≤ Rf + Rs + H + cr + db' + F)
    (h0 : (Rf + Rs) k = 0) (hH : H k = 0) (hcr : cr k = 0) (hdb : db' k = 0) (hF : F k ≤ 1) :
    Tot k + H' k ≤ 1 := by
  have := hle k
  simp only [Res.add_apply] at this h0
  omega

theorem fresh_F_rg (η : TEnv) :
    (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) (.rg (ridNext η)) = 1 := by simp

theorem fresh_F_wd (η : TEnv) :
    (Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η))) (.wd (ridNext η)) = 1 := by simp

/-! ### Promise credits at `wd` and at an unnamed region -/

theorem WRes_wd {E : TEnv} {a : Address} {w : Word} {R : Res} (h : WRes E a w R) (n : Nat) : R (.wd n) = 0 := by
  rcases h with ⟨n', P, -, -, rfl⟩ | ⟨-, rfl⟩ <;> simp

theorem VRes_wd {E : TEnv} {a : Address} {w : Word} {R : Res} (h : VRes E a w R) (n : Nat) : R (.wd n) = 0 := by
  rcases h with ⟨-, -, h⟩ | ⟨-, rfl⟩
  · exact WRes_wd h n
  · rfl

/-- No Σ word names region `n` at `a` ⟹ a word there carries no `rg n`. -/
theorem VRes_rg_noWord {E : TEnv} {a : Address} {w : Word} {R : Res} (h : VRes E a w R) {n : Nat}
    (hn : ∀ P, ¬ WordAt E a n P) : R (.rg n) = 0 := by
  rcases h with ⟨-, -, ⟨n', P, hw, -, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩
  · have : n ≠ n' := fun e => hn P (e ▸ hw)
    simp [this]
  · rfl
  · rfl

theorem sum_map_zero_at {f : Ts → Res} {k : Key} : ∀ (L : List Ts), (∀ t, t ∈ L → f t k = 0) →
    Res.sum (L.map f) k = 0
  | [], _ => rfl
  | t :: L, h => by
      simp only [List.map_cons, Res.sum_cons, Res.add_apply]
      rw [h t (List.mem_cons_self ..), sum_map_zero_at L (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]

theorem pSum_zero_of {s : St} {f : Ts → Res} {k : Key} (h : ∀ t, t ∈ s.promises → f t k = 0) :
    pSum s f k = 0 :=
  sum_map_zero_at s.promises h

/-- (U3, fix b) No Σ word names region `n` at the promised unit ⟹ the debit
carries no `wd n` (an initialising debit's word token is its own region's). -/
theorem DbRes_wd_noWord {E : TEnv} {mem : Memory} {m : Msg} {tw : Ts} {R : Res} (h : DbRes E mem m tw R)
    {n : Nat} (hn : ∀ P, ¬ WordAt E m.loc n P) (hns : ¬ DesigAt E mem m.loc tw) : R (.wd n) = 0 := by
  rcases h with ⟨-, -, h3, h4⟩ | ⟨-, rfl⟩
  · by_cases hi : InitAt mem m.loc tw
    · obtain ⟨R₁, Z, hF, -, hZ, rfl⟩ := h3 hi
      rw [hZ hns, Res.add_zero]
      rcases hF with ⟨n', P, hw, rfl⟩ | ⟨-, rfl⟩
      · have : n ≠ n' := fun e => hn P (e ▸ hw)
        simp only [Res.add_apply, wr, wdW]
        split <;> split <;> simp [this]
      · rfl
    · exact WRes_wd (h4 hi) n
  · rfl

/-- (H) No outstanding promise of the thread is designated (a designated debit
carries a block value, `BlkDb`). -/
def NoDesigP (E : TEnv) (s : St) : Prop :=
  ∀ t m, t ∈ s.promises → s.mem[t]? = some m → ¬ DesigAt E s.mem m.loc t

/-- **Credits at `wd` are zero; debits at `wd n` are zero when no Σ word names
region `n`** (and, (H), no promise is designated) (S10's `hcr`/`hdb` of `fresh_key_le_one` at `wd n`; under fix (b) an
initialising debit holds its word token). -/
theorem pSum_PromCr_wd {E : TEnv} {s : St} {cr db : Ts → Res} (h : PromCr E s cr db) (n : Nat)
    (hn : ∀ a P, ¬ WordAt E a n P) (hns : NoDesigP E s) :
    pSum s cr (.wd n) = 0 ∧ pSum s db (.wd n) = 0 := by
  refine ⟨pSum_zero_of fun t ht => ?_, pSum_zero_of fun t ht => ?_⟩
  · obtain ⟨m, -, -, ⟨w, -, hc⟩ | ⟨-, hc⟩⟩ := h t ht
    · exact VRes_wd hc n
    · rw [hc]; rfl
  · obtain ⟨m, hm, hd, -⟩ := h t ht
    exact DbRes_wd_noWord hd (hn m.loc) (hns t m ht hm)

/-- Credits and debits at `rg n` are zero when no Σ word names region `n`. -/
theorem pSum_PromCr_rg {E : TEnv} {s : St} {cr db : Ts → Res} (h : PromCr E s cr db) {n : Nat}
    (hn : ∀ a P, ¬ WordAt E a n P) (hns : NoDesigP E s) : pSum s cr (.rg n) = 0 ∧ pSum s db (.rg n) = 0 := by
  refine ⟨pSum_zero_of fun t ht => ?_, pSum_zero_of fun t ht => ?_⟩
  · obtain ⟨m, -, -, ⟨w, -, hc⟩ | ⟨-, hc⟩⟩ := h t ht
    · exact VRes_rg_noWord hc (hn m.loc)
    · rw [hc]; rfl
  · obtain ⟨m, hm, hd, -⟩ := h t ht
    exact DbRes_rg_noWord hd (hn m.loc) (hns t m ht hm)

/-! ## 5. EpochMono over all messages -/

/-- Message `t` is locally monotone for the epoch addresses `Ep`: at an epoch
address it is a number, at least its coherence predecessor (promises
included: a certified promise at an epoch word is fulfilled by an RMW reading
exactly that predecessor). -/
def LocalMono (Ep : Address → Prop) (mem : Memory) (t : Nat) : Prop :=
  ∀ m : Msg, mem[t]? = some m → Ep m.loc →
    ∃ v, m.val = .num v ∧ ∀ w, PredAt mem m.loc t w → ∃ u, w.val = .num u ∧ u ≤ v

/-- **(S9) The global epoch invariant**: every message is locally monotone. -/
def EpochLocal (Ep : Address → Prop) (mem : Memory) : Prop := ∀ t, LocalMono Ep mem t

/-- The latest message at `a` strictly below `t'`, at or above a given one. -/
theorem pred_exists {mem : Memory} {a : Address} {t t' : Nat} {m : Msg} (hlt : t < t') (hm : mem[t]? = some m)
    (ha : m.loc = a) :
    ∃ (t0 : Nat) (m0 : Msg), t ≤ t0 ∧ t0 < t' ∧ mem[t0]? = some m0 ∧ m0.loc = a ∧
      ∀ (t'' : Nat) (m'' : Msg), t0 < t'' → t'' < t' → mem[t'']? = some m'' → m''.loc ≠ a := by
  induction t' with
  | zero => omega
  | succ t' ih =>
      by_cases hc : ∃ m', mem[t']? = some m' ∧ m'.loc = a
      · obtain ⟨m', h1, h2⟩ := hc
        refine ⟨t', m', by omega, Nat.lt_succ_self _, h1, h2, fun t'' m'' h3 h4 _ => ?_⟩
        omega
      · have hne : t ≠ t' := fun e => hc ⟨m, e ▸ hm, ha⟩
        obtain ⟨t0, m0, h1, h2, h3, h4, h5⟩ := ih (by omega)
        refine ⟨t0, m0, h1, by omega, h3, h4, fun t'' m'' h6 h7 h8 => ?_⟩
        by_cases e : t'' = t'
        · subst e; exact fun hl => hc ⟨m'', h8, hl⟩
        · exact h5 t'' m'' h6 (by omega) h8

/-- **(S9) EpochLocal gives monotonicity along coherence order**, over all
messages (promises included). -/
theorem EpochLocal.mono {Ep : Address → Prop} {mem : Memory} (h : EpochLocal Ep mem) :
    ∀ (t' t : Nat) (m m' : Msg) (v v' : Nat), t < t' → mem[t]? = some m → mem[t']? = some m' → m.loc = m'.loc →
      Ep m.loc → m.val = .num v → m'.val = .num v' → v ≤ v' := by
  intro t'
  induction t' using Nat.strongRecOn with
  | ind t' ih =>
      intro t m m' v v' hlt hm hm' hl hep hv hv'
      obtain ⟨t0, m0, h1, h2, h3, h4, h5⟩ := pred_exists hlt hm hl
      have hp : PredAt mem m'.loc t' (mw m0) := ⟨t0, m0, h2, h3, h4, rfl, h5⟩
      obtain ⟨v1, hv1, hpr⟩ := h t' m' hm' (hl ▸ hep)
      rw [hv'] at hv1
      cases hv1
      obtain ⟨u, hu, hle⟩ := hpr _ hp
      have hu' : m0.val = .num u := hu
      rcases Nat.eq_or_lt_of_le h1 with e | hlt0
      · subst e
        rw [hm] at h3; cases h3
        rw [hv] at hu'; cases hu'
        exact hle
      · have := ih t0 h2 t m m0 v u hlt0 hm h3 (hl.trans h4.symm) hep hv hu'
        omega

/-- **(S9) TermStep's `EpochMono` from the global invariant**, at any view
whose epoch words are epoch addresses. -/
theorem EpochMono_of_local {Ep : Address → Prop} {E : TEnv} {s : St} (h : EpochLocal Ep s.mem)
    (hep : ∀ a n P, WordAt E a n P → P.epoch = true → Ep a) : EpochMono E s := by
  intro a n P t t' m m' v v' hw hpe hlt _ _ hm hm' hl hl' hv hv'
  exact h.mono t' t m m' v v' hlt hm hm' (hl.trans hl'.symm) (hl ▸ hep a n P hw hpe) hv hv'

/-- **(S9) EpochLocal is kept by a memory extension** whose new messages are
locally monotone, with epoch addresses growing only at addresses with no old
message. -/
theorem EpochLocal_ext {Ep Ep' : Address → Prop} {mem mem' : Memory} (h : EpochLocal Ep mem)
    (he : MemExt mem mem')
    (hEp : ∀ (t : Nat) (m : Msg), mem[t]? = some m → Ep' m.loc → Ep m.loc)
    (hnew : ∀ t, mem.size ≤ t → LocalMono Ep' mem' t) : EpochLocal Ep' mem' := by
  intro t
  by_cases ht : t < mem.size
  · intro m hm hep
    have hm0 : mem[t]? = some m := by rw [← he.get t ht]; exact hm
    obtain ⟨v, hv, hpr⟩ := h t m hm0 (hEp t m hm0 hep)
    refine ⟨v, hv, fun w hw => hpr w ?_⟩
    exact (PredAt_prefix (fun t' h' => he.get t' h') (Nat.le_of_lt ht)).2 hw
  · exact hnew t (Nat.le_of_not_lt ht)

/-- **(S9) EpochLocal along a machine step**, under S10's per-step hypothesis
on the new messages (from the typing of `casEpoch`/`fetchEpoch`/`caspBump`,
plain stores refused at epoch words, and certified promises). -/
theorem EpochLocal_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {Ep Ep' : Address → Prop}
    (hs : Step p k arch c c') (h : EpochLocal Ep c.mem)
    (hEp : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → Ep' m.loc → Ep m.loc)
    (hnew : ∀ t, c.mem.size ≤ t → LocalMono Ep' c'.mem t) : EpochLocal Ep' c'.mem :=
  EpochLocal_ext h (TermLiveProps.Step_ext hs) hEp hnew

/-- **(S9) EpochLocal along a run**, for epoch addresses `Ep c` read off each
configuration (S10: the epoch words of `E_g`'s Σ). -/
theorem EpochLocal_steps {p : Prog} {k : Promises.Knobs} {arch : Arch} {Ep : Cfg → Address → Prop}
    (hstep : ∀ c c', Step p k arch c c' → EpochLocal (Ep c) c.mem →
      (∀ (t : Nat) (m : Msg), c.mem[t]? = some m → Ep c' m.loc → Ep c m.loc) ∧
      ∀ t, c.mem.size ≤ t → LocalMono (Ep c') c'.mem t)
    {c0 c : Cfg} (hr : Steps p k arch c0 c) (h0 : EpochLocal (Ep c0) c0.mem) : EpochLocal (Ep c) c.mem :=
  Steps.inv (P := fun c => EpochLocal (Ep c) c.mem)
    (fun c c' hc hs => let ⟨h1, h2⟩ := hstep c c' hs hc; EpochLocal_step hs hc h1 h2) hr h0

/-- **(S9) Epoch mints at one address are once-only**: two messages at an
epoch address, both of value `j` with a predecessor below `j` (the data of
`MintStep.epoch`/`epoch2`), are the same message. -/
theorem epoch_mint_once {Ep : Address → Prop} {mem : Memory} (h : EpochLocal Ep mem) {a : Address} (ha : Ep a)
    {t1 t2 : Nat} {m1 m2 : Msg} {w1 w2 : Word} {j u1 u2 : Nat}
    (hm1 : mem[t1]? = some m1) (hl1 : m1.loc = a) (hv1 : m1.val = .num j) (hp1 : PredAt mem a t1 w1)
    (hw1 : w1.val = .num u1) (hu1 : u1 < j)
    (hm2 : mem[t2]? = some m2) (hl2 : m2.loc = a) (hv2 : m2.val = .num j) (hp2 : PredAt mem a t2 w2)
    (hw2 : w2.val = .num u2) (hu2 : u2 < j) : t1 = t2 := by
  have key : ∀ {t1 t2 : Nat} {m1 m2 : Msg} {w2 : Word} {u2 : Nat}, t1 < t2 → mem[t1]? = some m1 → m1.loc = a →
      m1.val = .num j → PredAt mem a t2 w2 → w2.val = .num u2 → u2 < j → False := by
    intro t1 t2 m1 m2 w2 u2 hlt hm1 hl1 hv1 hp2 hw2 hu2
    obtain ⟨t0, m0, h0lt, hm0, hl0, rfl, hn⟩ := hp2
    have ht1 : t1 ≤ t0 := by
      apply Nat.le_of_not_lt
      intro hc
      exact hn t1 m1 hc hlt hm1 hl1
    have hv0 : m0.val = .num u2 := hw2
    rcases Nat.eq_or_lt_of_le ht1 with e | hlt'
    · subst e; rw [hm1] at hm0; cases hm0; rw [hv1] at hv0; cases hv0; omega
    · have := h.mono t0 t1 m1 m0 j u2 hlt' hm1 hm0 (hl1.trans hl0.symm) (hl1 ▸ ha) hv1 hv0
      omega
  rcases Nat.lt_trichotomy t1 t2 with hlt | e | hlt
  · exact (key (m2 := m2) hlt hm1 hl1 hv1 hp2 hw2 hu2).elim
  · exact e
  · exact (key (m2 := m1) hlt hm2 hl2 hv2 hp1 hw1 hu1).elim

/-- A mint's record survives memory growth (S10 keeps each minted `ep n j`'s
message in the configuration's memory). -/
theorem PredAt_ext {mem mem' : Memory} (he : MemExt mem mem') {a : Address} {t : Ts} {w : Word}
    (ht : t ≤ mem.size) (h : PredAt mem a t w) : PredAt mem' a t w :=
  (PredAt_prefix (fun t' h' => he.get t' h') ht).1 h

/-! ## 6. The share bound: the shape S10 needs

`Σ_i Tot_i (sh n) + HS (sh n) ≤ shares(latest state of n)`
is kept by a step whose holdings at `sh n` change by `S' + C ≤ S + F` while
the share count moves by `sc + F ≤ sc' + C`.  `MintStep.share` gives the
count-up case (`F = 1`, `sc' = sc + 1`).  A lend-down step lowers the count by
one while stage A records its consumed share as a *drop* (`MintStep.none`,
`Tot` an upper bound), so S10 needs the exact consumption `C = one (sh n)` at
down moves (a `MintStep` constructor, or the exact `Tot'` of
`tstepMC_lendDown`): reported. -/

/-- The share bound's arithmetic step. -/
theorem shareBound_step {S S' sc sc' C F : Nat} (h : S ≤ sc) (hstep : S' + C ≤ S + F)
    (hcnt : sc + F ≤ sc' + C) : S' ≤ sc' := by
  omega

theorem one_sh_cases (m n : Nat) : Res.one (.sh m) (.sh n) = 0 ∨ Res.one (.sh m) = Res.one (.sh n) := by
  by_cases e : m = n
  · subst e; exact Or.inr rfl
  · left; simp [Ne.symm e]

/-- What a step mints at `sh n`: nothing, or one share by `MintStep.share` at
a word of region `n` whose state's count goes up by one. -/
theorem MintStep_sh {g : G} {η : TEnv} {s s' : St} {C F : Res} (h : MintStep g η s s' C F) (n : Nat) :
    F (.sh n) = 0 ∨ F = Res.one (.sh n) := by
  cases h with
  | none => exact Or.inl rfl
  | fresh => left; simp
  | epoch => left; simp
  | share => exact one_sh_cases _ n
  | claim => left; simp
  | epoch2 => left; simp
  | alloc => left; simp
  | consume => exact Or.inl rfl

/-! ## (F2′) Own-handle mints -/

/-- (F2′) What a step mints at `own l`: nothing, or the allocation of the
fresh label `l`. -/
theorem MintStep_own {g : G} {η : TEnv} {s s' : St} {C F : Res} (h : MintStep g η s s' C F) (l : Nat) :
    F (.own l) = 0 ∨ ∃ g, FreshIn g s.nalloc s'.nalloc l ∧ F = Res.one (.own l) := by
  cases h with
  | none => exact Or.inl rfl
  | fresh => left; simp
  | epoch => left; simp
  | share => left; simp
  | claim => left; simp
  | epoch2 => left; simp
  | consume => exact Or.inl rfl
  | alloc hf _hs =>
      rename_i l'
      by_cases e : l' = l
      · subst e; exact Or.inr ⟨g, hf, rfl⟩
      · left; simp [Ne.symm e]

/-- (F2′) The cumulative own-handle mint: one `own l` per label of the
pairwise-distinct `A` (as `MintOKL`'s `L` for `wd`). -/
def MintOwnL (A : List Nat) (M : Res) : Prop := A.Nodup ∧ ∀ l, M (.own l) = A.count l

/-- **(F2′) `own l` is minted at most once per label.** -/
theorem MintOwnL_le {A : List Nat} {M : Res} (h : MintOwnL A M) (l : Nat) : M (.own l) ≤ 1 := by
  rw [h.2 l]; exact count_le_one_of_nodup h.1 l

theorem MintOwnL_init : MintOwnL [] .zero := ⟨List.nodup_nil, fun _ => rfl⟩

/-- **(F2′) `MintOwnL` is kept by every step's mint**: an allocation extends
`A` by its label (which must be new: the caller gets it from the label's
freshness, `SysInvW.fresh`); every other mint is `own`-free. -/
theorem MintOwnL_step {g : G} {A : List Nat} {M : Res} (h : MintOwnL A M) {η : TEnv} {s s' : St} {C F : Res}
    (hm : MintStep g η s s' C F) (hnew : ∀ l, F (.own l) ≠ 0 → l ∉ A) :
    ∃ A', MintOwnL A' (M + F) ∧ (∀ l, l ∈ A → l ∈ A') ∧
      ∀ l, l ∈ A' → l ∈ A ∨ ∃ g, FreshIn g s.nalloc s'.nalloc l := by
  obtain ⟨hnd, hc⟩ := h
  have keep : (∀ l, F (.own l) = 0) → ∃ A', MintOwnL A' (M + F) ∧ (∀ l, l ∈ A → l ∈ A') ∧
      ∀ l, l ∈ A' → l ∈ A ∨ ∃ g, FreshIn g s.nalloc s'.nalloc l := fun h0 =>
    ⟨A, ⟨hnd, fun l => by rw [Res.add_apply, hc l, h0 l, Nat.add_zero]⟩, fun _ h => h, fun _ h => Or.inl h⟩
  cases hm with
  | none => exact keep fun _ => rfl
  | fresh => exact keep fun _ => by simp
  | epoch => exact keep fun _ => by simp
  | share => exact keep fun _ => by simp
  | claim => exact keep fun _ => by simp
  | epoch2 => exact keep fun _ => by simp
  | consume => exact keep fun _ => rfl
  | alloc hf _hs =>
      rename_i l0
      have hn : l0 ∉ A := hnew l0 (by simp)
      refine ⟨l0 :: A, ⟨List.nodup_cons.2 ⟨hn, hnd⟩, fun l => ?_⟩, fun l hl => List.mem_cons_of_mem _ hl,
        fun l hl => ?_⟩
      · rw [Res.add_apply, hc l, List.count_cons]
        by_cases e : l0 = l
        · subst e; simp
        · have e' : l ≠ l0 := Ne.symm e
          simp [e, e']
      · rcases List.mem_cons.1 hl with e | e
        · subst e; exact Or.inr ⟨g, hf⟩
        · exact Or.inl e

end TermOnce

#print axioms TermOnce.ridPair_pos
#print axioms TermOnce.ridPair_lt
#print axioms TermOnce.ridPair_unused
#print axioms TermOnce.RidUsed_mono
#print axioms TermOnce.RidUsed_ridSet
#print axioms TermOnce.fresh_unused
#print axioms TermOnce.fresh_bump
#print axioms TermOnce.ridNext_ne_other
#print axioms TermOnce.raiseRid_inv
#print axioms TermOnce.repick_fresh
#print axioms TermOnce.MintStep_wd
#print axioms TermOnce.MintStep_rg
#print axioms TermOnce.MintStep_sh
#print axioms TermOnce.MintStep_own
#print axioms TermOnce.MintOwnL_le
#print axioms TermOnce.MintOwnL_init
#print axioms TermOnce.MintOwnL_step
#print axioms TermOnce.MintOKL_wd_le
#print axioms TermOnce.MintOK_wd_le
#print axioms TermOnce.MintOKL_init
#print axioms TermOnce.MintOKL_step
#print axioms TermOnce.keySum_fresh
#print axioms TermOnce.fresh_key_le_one
#print axioms TermOnce.DbRes_wd_noWord
#print axioms TermOnce.pSum_PromCr_wd
#print axioms TermOnce.pSum_PromCr_rg
#print axioms TermOnce.EpochLocal.mono
#print axioms TermOnce.EpochMono_of_local
#print axioms TermOnce.EpochLocal_ext
#print axioms TermOnce.EpochLocal_step
#print axioms TermOnce.EpochLocal_steps
#print axioms TermOnce.epoch_mint_once
#print axioms TermOnce.PredAt_ext
#print axioms TermOnce.shareBound_step

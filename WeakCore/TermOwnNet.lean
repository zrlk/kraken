import WeakCore.TermOwnFresh

/-! # TermOwnNet: the own-key net bound (`ownNet_of`, a theorem, not a clause)

K-net at `own l` (`SysInvN.knet`) with own-free credits and debits (`TermOwnFresh.promCrK_own`):
frames plus private holdings of all threads, plus the shared holding, carry `own l` at most once. -/

namespace TermOwnNet
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermBal
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem sum_range_congr {f g : Nat → Nat} : ∀ {N : Nat}, (∀ n, n < N → f n = g n) →
    ((List.range N).map f).sum = ((List.range N).map g).sum
  | 0, _ => rfl
  | N + 1, h => by
      rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append,
        sum_range_congr (fun n hn => h n (by omega))]
      simp [h N (by omega)]

/-- Thread `i`'s credits and debits carry no own key (any `i`: off the threads `pSumAt` is zero). -/
theorem pSumAt_own_zero {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (i l : Nat) :
    pSumAt c i (cr i) (.own l) = 0 ∧ pSumAt c i (db i) (.own l) = 0 := by
  cases hth : c.ths[i]? with
  | none =>
    rw [pSumAt_key, pSumAt_key]
    unfold promsOf; rw [hth]; exact ⟨rfl, rfl⟩
  | some th =>
    rw [pSumAt_some hth, pSumAt_some hth]
    obtain ⟨_, -, -, -, -, -, hK⟩ := h.thr i th hth
    exact TermOwnFresh.promCrK_own hK l

/-- **`ownNet_of`**: at a `SysInvN` configuration the own key of any label is carried at most once by
frames, private holdings and the shared holding. -/
theorem ownNet_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (l : Nat) :
    ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum + HS (.own l) ≤ 1 := by
  have hk : KeyNet c Tot HP HS cr db (.own l) := h.knet (.own l) trivial
  unfold KeyNet at hk
  have e1 : ((List.range c.ths.size).map (fun i => (Tot i + HP i + pSumAt c i (cr i)) (.own l))).sum =
      ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum :=
    sum_range_congr fun n _ => by
      simp only [Res.add_apply]; rw [(pSumAt_own_zero h n l).1]; rfl
  have e2 : ((List.range c.ths.size).map (fun i => pSumAt c i (db i) (.own l))).sum = 0 := by
    rw [sum_range_congr (g := fun _ => 0) fun n _ => (pSumAt_own_zero h n l).2]
    exact TermOwnFresh.sum_range_zero (fun _ _ => rfl)
  rw [e1, e2] at hk
  exact hk

theorem le_sum_of_mem' {x : Nat} : ∀ {L : List Nat}, x ∈ L → x ≤ L.sum
  | [], h => absurd h List.not_mem_nil
  | y :: L, h => by
      rw [List.sum_cons]
      rcases List.mem_cons.1 h with rfl | h
      · omega
      · have := le_sum_of_mem' h; omega

/-- Per thread: a single thread's frame plus private holding, plus the shared holding, at most one. -/
theorem ownNet_one {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (l : Nat) {i : Nat} (hi : i < c.ths.size) :
    (Tot i + HP i) (.own l) + HS (.own l) ≤ 1 := by
  have h1 := ownNet_of h l
  have h2 : (Tot i + HP i) (.own l) ≤ ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum :=
    le_sum_of_mem' (List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
  omega

end TermOwnNet

#print axioms TermOwnNet.pSumAt_own_zero
#print axioms TermOwnNet.ownNet_of
#print axioms TermOwnNet.ownNet_one

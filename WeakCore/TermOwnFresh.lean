import WeakCore.TermBal
import WeakCore.TermTyped

/-! # TermOwnFresh: no own-handle key of a not-yet-allocated fresh label is held (T20b2, S10)

Replaces the obligation `ownKeySto` (`TermBal.OwnKeyStoN`) by a proved `SysInvN` clause `OwnFreshZ`:
at every thread `q`'s fresh label `freshLabel lbase n q j` with `q.nalloc ≤ j`, the own-handle key has zero
load (frames, private and shared holdings, credits).  That is all `TermBal.mintRoom_at` uses
(`mintRoomF_at` below).

* thread step (`ownFresh_thread`): the step inequality of `TOut` at `own x` (the `ridT_D` pattern); the old
  load is zero (nalloc only grows), the step mints no `own x` (`AllocGT` and `freshLabel_inj`: the step's own
  fresh labels are below its new `nalloc`), new debits carry no own key (`PromCr_own_zero`);
* promise step (`ownFresh_prom`): `PAcct` at `own x`, with the post-state credits/debits own-free;
* the (H)-sensitive part is the single lemma `promCrK_own` (credits are `OldCr` `VRes`, `PlantCr ∧ CrKeys`;
  debits `DbRes`). -/

namespace TermOwnFresh
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermBal
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- At the zero witnesses (init) the clause holds trivially. -/
theorem ownFreshZ_zero {c : Cfg} : OwnFreshZ c (fun _ => .zero) (fun _ => .zero) .zero (fun _ _ => .zero) := by
  intro q thq j _ _
  refine ⟨fun n _ => ?_, rfl⟩
  rw [Res.add_apply, Res.add_apply, pSumAt_key]
  show 0 + 0 + ((promsOf c n).map (fun _ => (0 : Nat))).sum = 0
  generalize promsOf c n = L
  induction L with
  | nil => rfl
  | cons t L ih => simp only [List.map_cons, List.sum_cons] at ih ⊢; omega

theorem sum_range_zero {f : Nat → Nat} : ∀ {N : Nat}, (∀ n, n < N → f n = 0) → ((List.range N).map f).sum = 0
  | 0, _ => rfl
  | N + 1, h => by
      rw [List.range_succ, List.map_append, List.sum_append, sum_range_zero (fun n hn => h n (by omega))]
      simp [h N (by omega)]

/-- The clause gives the zero key load `mintRoom_at` needs. -/
theorem keyLoad_zero {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr : Nat → Ts → Res}
    (h : OwnFreshZ c Tot HP HS cr) {q : Nat} {thq : TTh} {j : Nat} (hq : c.ths[q]? = some thq)
    (hj : thq.nalloc ≤ j) : KeyLoad c Tot HP HS cr (.own (freshLabel c.lbase c.n q j)) = 0 := by
  obtain ⟨h1, h2⟩ := h q thq j hq hj
  unfold KeyLoad
  rw [sum_range_zero h1, h2]

/-- **(H) isolation**: a thread's credits and debits carry no own key. -/
theorem promCrK_own {E : TEnv} {s : St} {cr db : Ts → Res} (h : TermPlant.PromCrK E s cr db) (l : Nat) :
    pSum s cr (.own l) = 0 ∧ pSum s db (.own l) = 0 := by
  refine ⟨TermTyped.sum_map_key_zero fun t ht => ?_, TermTyped.sum_map_key_zero fun t ht => ?_⟩
  · obtain ⟨m, -, -, (⟨w, -, hw⟩ | ⟨-, hz⟩) | ⟨-, hk⟩⟩ := h t ht
    · exact TermTyped.VRes_own_zero hw l
    · rw [hz]; rfl
    · exact hk l
  · obtain ⟨m, -, hd, -⟩ := h t ht
    exact TermTyped.DbRes_own_zero hd l

theorem threadSteps_lbase {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) : c'.lbase = c.lbase := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := step_thread_inv h
  rfl

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **Thread step.** -/
theorem ownFresh_thread (hb1 : AllocGT p k arch Sp Init MintOK c0) (hN : PromNodupR p k arch Sp c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ)
    (hK : ∀ t l, crS t (.own l) = cr i t (.own l))
    (h : OwnFreshZ c Tot HP HS cr) :
    OwnFreshZ c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) := by
  intro q thq j hq hj
  have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
  have hlb : c'.lbase = c.lbase := threadSteps_lbase X.hc'
  rw [hsz, TermStep.threadSteps_n X.hc', hlb]
  have hi : i < c.ths.size := lt_of_getq X.hth
  have hqs : q < c.ths.size := hsz ▸ lt_of_getq hq
  have hnal : th.nalloc ≤ r.2.2.nalloc := (TermTyped.tstep_wrUp _ _ _ _ r X.hr).2.2.1
  -- the old freshness of `q`'s label `j`
  obtain ⟨thq0, hq0, hle0⟩ : ∃ thq0, c.ths[q]? = some thq0 ∧ thq0.nalloc ≤ j := by
    by_cases hqi : q = i
    · subst hqi
      rw [X.e3] at hq; cases hq
      exact ⟨th, X.hth, Nat.le_trans hnal hj⟩
    · rw [X.ho q hqi] at hq
      exact ⟨thq, hq, hj⟩
  obtain ⟨hz, hzS⟩ := h q thq0 j hq0 hle0
  generalize hx : freshLabel c.lbase c.n q j = x at hz hzS ⊢
  -- the step mints no `own x`
  have hF0 : F (.own x) = 0 := by
    cases e : F (.own x) with
    | zero => rfl
    | succ n =>
      exfalso
      obtain ⟨j', -, hj2, hl⟩ := hb1 X Y (Z.toC _ _ _ _ _) x (by rw [e]; exact Nat.succ_ne_zero n)
      have hl' : freshLabel c.lbase c.n q j = freshLabel c.lbase c.n i j' := hx.trans hl
      obtain ⟨rfl, rfl⟩ := freshLabel_inj (Cfg.lt_n hqs) (Cfg.lt_n hi) hl'
      rw [X.e3] at hq; cases hq
      have : j < r.2.2.nalloc := hj2
      omega
  have hPC : TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db' := Z.2.2.2.2.2.1
  have hd0 : pSum (stOf r.1 r.2.1 r.2.2) db' (.own x) = 0 := (promCrK_own hPC x).2
  have hzi := hz i hi
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, Fd, hFd, hineq, -⟩ := Z
  have hI := hineq (.own x)
  have hT := congrFun hsum (.own x)
  rw [pSumAt_some X.hth (cr i)] at hzi
  simp only [Res.add_apply] at hI hT hzi
  rw [TermBal.pSum_congr_key (fun t => hK t x)] at hI
  refine ⟨fun n hn => ?_, by omega⟩
  by_cases hni : n = i
  · subst hni
    rw [upd_self, upd_self, updD_self, thread_pSumAt_self X]
    simp only [Res.add_apply]
    omega
  · have hzn := hz n hn
    have hδ := CrShift_sum hFd X.inv.disj (hN c X.run) (.own x) [n]
      (List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩)
    rw [upd_other _ _ hni, upd_other _ _ hni, updD_other _ _ _ hni, thread_pSumAt_other X hni]
    simp only [Res.add_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hzn hδ ⊢
    rw [pSumAt_add]
    omega

/-- **Promise step**, given the post-state debits of the promiser own-free (`promCrK_own` at its new
`PromCrK`). -/
theorem ownFresh_prom {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hdb : ∀ l, pSum (promSt (stOf c.mem c.pairs th) a v w) db' (.own l) = 0)
    (h : OwnFreshZ c Tot HP HS cr) :
    OwnFreshZ (promise c j a v w) Tot (upd HP j HP') HS' (upd cr j cr') := by
  intro q thq jj hq hjj
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hsz : (promise c j a v w).ths.size = c.ths.size := TermStep.promise_size c j a v w
  have hlb : (promise c j a v w).lbase = c.lbase := by rw [hpi.1]
  rw [hsz, TermStep.promise_n, hlb]
  obtain ⟨thq0, hq0, hle0⟩ : ∃ thq0, c.ths[q]? = some thq0 ∧ thq0.nalloc ≤ jj := by
    by_cases hqj : q = j
    · subst hqj
      rw [hpi.2.1] at hq; cases hq
      exact ⟨th, X.hth, hjj⟩
    · rw [TermStep.promise_other hqj] at hq
      exact ⟨thq, hq, hjj⟩
  obtain ⟨hz, hzS⟩ := h q thq0 jj hq0 hle0
  generalize freshLabel c.lbase c.n q jj = x at hz hzS ⊢
  have hj : j < c.ths.size := lt_of_getq X.hth
  have hzj := hz j hj
  rw [pSumAt_some X.hth (cr j)] at hzj
  unfold PAcct at hA
  have hA' := congrFun hA (.own x)
  have hd := hdb x
  have hd0 : pSum (stOf c.mem c.pairs th) (db j) (.own x) = 0 := by
    obtain ⟨S0, -, -, -, -, -, hK⟩ := X.inv.thr j th X.hth
    exact (promCrK_own hK x).2
  simp only [Res.add_apply] at hA' hzj
  refine ⟨fun n hn => ?_, by omega⟩
  by_cases hnj : n = j
  · subst hnj
    rw [upd_self, upd_self, promise_pSumAt_self X.hth]
    simp only [Res.add_apply]
    omega
  · rw [upd_other _ _ hnj, upd_other _ _ hnj, promise_pSumAt_other hnj]
    exact hz n hn

/-- **`mintRoom_at` with the clause** in place of `OwnKeyStoN`. -/
theorem mintRoomF_at (hb1 : AllocGT p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hof : OwnFreshZ c Tot HP HS cr)
    (hc : ∀ n j, C = Res.one (.ep n j) → F = Res.one (.rg n) →
      KeyLoad c Tot HP HS cr (.rg n) + 1 ≤ 1 + KeyDebt c db (.rg n))
    (ha : F = Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)) →
      KeyLoad c Tot HP HS cr (.rg (ridNext η)) ≤ KeyDebt c db (.rg (ridNext η)) ∧
        KeyLoad c Tot HP HS cr (.wd (ridNext η)) ≤ KeyDebt c db (.wd (ridNext η))) :
    ∀ key, ExclKey key → F key ≠ 0 → KeyLoad c Tot HP HS cr key + F key ≤ 1 + KeyDebt c db key := by
  intro key hk hF
  have hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F := Z.2.2.2.2.2.2.1
  have h1 := MintStep_le_one hMS key
  cases key with
  | rg n =>
    rcases TermOnce.MintStep_rg hMS n with h0 | ⟨e, hf⟩ | ⟨j, hC, hf⟩
    · exact absurd h0 hF
    · subst e
      have := (ha hf).1
      omega
    · have := hc n j hC hf
      rw [hf]
      simp only [Res.one_apply, ite_true]
      omega
  | wd n =>
    rcases TermOnce.MintStep_wd hMS n with h0 | ⟨e, hf⟩
    · exact absurd h0 hF
    · subst e
      have := (ha hf).2
      omega
  | own l =>
    obtain ⟨j, hj1, -, hl⟩ := hb1 X Y (Z.toC _ _ _ _ _) l hF
    have hl' : l = freshLabel c.lbase c.n i j := hl
    subst hl'
    have := keyLoad_zero hof X.hth hj1
    omega
  | _ => exact hk.elim

/-- **T20′ `knetT`** with the clause (replaces `knetT_D`'s `OwnKeyStoN`). -/
theorem knetT_F (hb1 : AllocGT p k arch Sp Init MintOK c0)
    (hres : TicketFreeRun p k arch Sp c0) (hN : PromNodupR p k arch Sp c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hcl : ClaimAt th.term C F) (hof : OwnFreshZ c Tot HP HS cr)
    {rc : Nat → Nat} (hrc : RidOK c Tot HP HS cr db rc) (hle : rc i ≤ η.rid) :
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) (upd db i db') key := by
  have htid : η.tid = i := Y.2.1
  have hle' : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  exact knetT_coreD X Y Z (hN c X.run)
    (mintRoomF_at hb1 X Y Z hof (claimRoom_at hres X hcl) (fun _ => ridFresh_of hrc hle'))

end

end TermOwnFresh

#print axioms TermOwnFresh.keyLoad_zero
#print axioms TermOwnFresh.promCrK_own
#print axioms TermOwnFresh.ownFresh_thread
#print axioms TermOwnFresh.ownFresh_prom
#print axioms TermOwnFresh.mintRoomF_at
#print axioms TermOwnFresh.knetT_F
#print axioms TermOwnFresh.ownFreshZ_zero

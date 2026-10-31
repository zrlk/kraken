import WeakCore.TermMainDefs
import WeakCore.TermOnce

/-!
# TermBal: the accounting fields of `TermMain.Obligations`

The four accounting fields `balT` (T19), `knetT` (T20), `balP`
(P8) and `knetP` (P9) are proved here, in their exact field types.

The net form `KeyNet` and the balance count every outstanding promise's credit
on the left and its debit on the right, so the promise step's `PAcct` and the
thread step's `TOut` inequality are exactly the per-thread deltas of these
sums: every field is per-key `Nat` algebra over the threads, one index
changed (`sum_range_upd`).  No telescoping along promise chains is needed.

* `knetP_proof`, `balP_proof`: no hypothesis.
* `knetT_proof`: under `MintRoomT` (a key the step mints has room in the old
  bound); `mintRoomT_of_zero` reduces it to `MintZeroT` (a minted exclusive
  key is held nowhere before the step), since a `MintStep` mints each key at
  most once (`MintStep_le_one`).
* `balT_proof`: under `MintClosedT` (`MintOK` is closed under the step's mint).
-/

namespace TermBal

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## 1. Sum algebra -/

theorem res_sum_apply : ∀ (L : List Res) (key : Key), Res.sum L key = (L.map (fun r => r key)).sum
  | [], _ => rfl
  | r :: L, key => by
    simp only [Res.sum_cons, Res.add_apply, List.map_cons, List.sum_cons, res_sum_apply L key]

/-- `pSum` at one key reads its family only at that key. -/
theorem pSum_congr_key {s : St} {f g : Ts → Res} {key : Key} (h : ∀ t, f t key = g t key) :
    pSum s f key = pSum s g key := by
  unfold pSum
  rw [res_sum_apply, res_sum_apply, List.map_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun t _ => h t)

theorem thSum_apply (N : Nat) (f : Nat → Res) (key : Key) :
    thSum N f key = ((List.range N).map (fun j => f j key)).sum := by
  unfold thSum
  rw [res_sum_apply, List.map_map]
  rfl

theorem sum_range_congr {N : Nat} {f g : Nat → Nat} (h : ∀ j, j < N → f j = g j) :
    ((List.range N).map f).sum = ((List.range N).map g).sum := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append,
      ih (fun j hj => h j (Nat.lt_succ_of_lt hj))]
    simp [h N (Nat.lt_succ_self N)]

/-- A sum over the threads with one index changed. -/
theorem sum_range_upd {N i : Nat} (hi : i < N) {f g : Nat → Nat} (h : ∀ j, j ≠ i → f j = g j) :
    ((List.range N).map f).sum + g i = ((List.range N).map g).sum + f i := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    by_cases e : N = i
    · subst e
      rw [sum_range_congr (fun j hj => h j (Nat.ne_of_lt hj))]
      omega
    · have := ih (by omega)
      rw [h N e]
      omega

theorem lt_of_getq {α : Type} {xs : Array α} {i : Nat} {x : α} (h : xs[i]? = some x) : i < xs.size := by
  rcases Nat.lt_or_ge i xs.size with h1 | h1
  · exact h1
  · simp [h1] at h

theorem pSumAt_some {c : Cfg} {i : Nat} {th : TTh} (h : c.ths[i]? = some th) (f : Ts → Res) :
    pSumAt c i f = pSum (stOf c.mem c.pairs th) f := by
  unfold pSumAt; rw [h]

/-- `pSumAt` reads only the thread's `promises`. -/
theorem pSumAt_eq {c c' : Cfg} {i : Nat} (h : c'.ths[i]? = c.ths[i]?) (f : Ts → Res) :
    pSumAt c' i f = pSumAt c i f := by
  unfold pSumAt
  rw [h]
  cases c.ths[i]? with
  | none => rfl
  | some _ => rfl

/-- The load of an exclusive key: frames, private holdings and credits of all
threads, and the shared holding (the left side of `KeyNet`). -/
def KeyLoad (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr : Nat → Ts → Res) (key : Key) : Nat :=
  ((List.range c.ths.size).map (fun i => (Tot i + HP i + pSumAt c i (cr i)) key)).sum + HS key

/-- The outstanding debit of a key (the right side of `KeyNet`, less one;
`TermMain.Debt`). -/
def KeyDebt (c : Cfg) (db : Nat → Ts → Res) (key : Key) : Nat :=
  ((List.range c.ths.size).map (fun i => pSumAt c i (db i) key)).sum

theorem keyNet_iff {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {key : Key} :
    KeyNet c Tot HP HS cr db key ↔ KeyLoad c Tot HP HS cr key ≤ 1 + KeyDebt c db key := Iff.rfl

/-! ## 2. The promise step (P8, P9): no hypothesis -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

theorem promise_pSumAt_self {c : Cfg} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) (f : Ts → Res) :
    pSumAt (promise c j a v w) j f = pSum (promSt (stOf c.mem c.pairs th) a v w) f := by
  rw [pSumAt_some (promise_inv (a := a) (v := v) (w := w) hth).2.1, (promise_inv hth).2.2]

theorem promise_pSumAt_other {c : Cfg} {j n : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} (hn : n ≠ j)
    (f : Ts → Res) : pSumAt (promise c j a v w) n f = pSumAt c n f :=
  pSumAt_eq (TermStep.promise_other hn) f

/-- **P9 `knetP`** (K-net after a promise step), exactly: the promise moves
the promised message's holding between `HS`/`HP j` and the promiser's credit
and debit, which `PAcct` balances key by key. -/
theorem knetP_proof {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db') :
    ∀ key, ExclKey key → KeyNet (promise c j a v w) Tot (upd HP j HP') HS' (upd cr j cr') (upd db j db') key := by
  intro key hk
  have hold := X.inv.knet key hk
  have hj : j < c.ths.size := lt_of_getq X.hth
  unfold PAcct at hA
  have hA' := congrFun hA key
  have hs1 : ((List.range c.ths.size).map (fun n => (Tot n + HP n + pSumAt c n (cr n)) key)).sum +
        (Tot j + upd HP j HP' j + pSumAt (promise c j a v w) j (upd cr j cr' j)) key =
      ((List.range c.ths.size).map
          (fun n => (Tot n + upd HP j HP' n + pSumAt (promise c j a v w) n (upd cr j cr' n)) key)).sum +
        (Tot j + HP j + pSumAt c j (cr j)) key :=
    sum_range_upd (f := (fun n => (Tot n + HP n + pSumAt c n (cr n)) key)) (g := (fun n => (Tot n + upd HP j HP' n + pSumAt (promise c j a v w) n (upd cr j cr' n)) key)) hj (fun n hn => by rw [upd_other _ _ hn, upd_other _ _ hn, promise_pSumAt_other hn])
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt (promise c j a v w) j (upd db j db' j) key =
      ((List.range c.ths.size).map (fun n => pSumAt (promise c j a v w) n (upd db j db' n) key)).sum +
        pSumAt c j (db j) key :=
    sum_range_upd (f := (fun n => pSumAt c n (db n) key)) (g := (fun n => pSumAt (promise c j a v w) n (upd db j db' n) key)) hj (fun n hn => by rw [upd_other _ _ hn, promise_pSumAt_other hn])
  rw [upd_self, upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs1
  rw [upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs2
  unfold KeyNet at hold ⊢
  rw [TermStep.promise_size]
  simp only [Res.add_apply] at hs1 hs2 hold hA' ⊢
  omega

/-- **P8 `balP`** (the balance after a promise step), with the same mint. -/
theorem balP_proof {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db') :
    ∃ M, MintOK M ∧
      thSum (promise c j a v w).ths.size
          (fun i => Tot i + pSumAt (promise c j a v w) i (upd cr j cr' i) + upd HP j HP' i) + HS' ≤
        Init + M + thSum (promise c j a v w).ths.size (fun i => pSumAt (promise c j a v w) i (upd db j db' i)) := by
  obtain ⟨M, hM, hb⟩ := X.inv.bal
  refine ⟨M, hM, Res.le_def.2 fun key => ?_⟩
  have hold := hb key
  have hj : j < c.ths.size := lt_of_getq X.hth
  unfold PAcct at hA
  have hA' := congrFun hA key
  have hs1 : ((List.range c.ths.size).map (fun n => (Tot n + pSumAt c n (cr n) + HP n) key)).sum +
        (Tot j + pSumAt (promise c j a v w) j (upd cr j cr' j) + upd HP j HP' j) key =
      ((List.range c.ths.size).map
          (fun n => (Tot n + pSumAt (promise c j a v w) n (upd cr j cr' n) + upd HP j HP' n) key)).sum +
        (Tot j + pSumAt c j (cr j) + HP j) key :=
    sum_range_upd (f := (fun n => (Tot n + pSumAt c n (cr n) + HP n) key)) (g := (fun n => (Tot n + pSumAt (promise c j a v w) n (upd cr j cr' n) + upd HP j HP' n) key)) hj (fun n hn => by rw [upd_other _ _ hn, upd_other _ _ hn, promise_pSumAt_other hn])
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt (promise c j a v w) j (upd db j db' j) key =
      ((List.range c.ths.size).map (fun n => pSumAt (promise c j a v w) n (upd db j db' n) key)).sum +
        pSumAt c j (db j) key :=
    sum_range_upd (f := (fun n => pSumAt c n (db n) key)) (g := (fun n => pSumAt (promise c j a v w) n (upd db j db' n) key)) hj (fun n hn => by rw [upd_other _ _ hn, promise_pSumAt_other hn])
  rw [upd_self, upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs1
  rw [upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs2
  rw [TermStep.promise_size]
  simp only [Res.add_apply, thSum_apply] at hs1 hs2 hold hA' ⊢
  omega

/-! ## 3. The thread step (T19, T20) -/

theorem thread_pSumAt_self {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (f : Ts → Res) :
    pSumAt c' i f = pSum (stOf r.1 r.2.1 r.2.2) f := by
  rw [pSumAt_some X.e3, X.e1, X.e2]

theorem thread_pSumAt_other {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) {n : Nat} (hn : n ≠ i) (f : Ts → Res) :
    pSumAt c' n f = pSumAt c n f :=
  pSumAt_eq (X.ho n hn) f

/-- **(new obligation for T20) Room for a mint**: an exclusive key the step
mints fits in the old net bound. -/
def MintRoomT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ key, ExclKey key → F key ≠ 0 → KeyLoad c Tot HP HS cr key + F key ≤ 1 + KeyDebt c db key

/-- **(new obligation, sufficient for `MintRoomT`) A minted exclusive key is
held nowhere before the step** (fresh `rg`/`wd` at `ridNext η`: rid
freshness; `alloc`'s `own l`: fresh label; `claim n j`'s `rg n`: the S9b
ghost-holder decision). -/
def MintZeroT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ key, ExclKey key → F key ≠ 0 → KeyLoad c Tot HP HS cr key = 0

/-- **(new obligation for T19) `MintOK` is closed under the step's mint.** -/
def MintClosedT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ M, MintOK M → MintOK (M + F)

/-- A step mints every key at most once. -/
theorem MintStep_le_one {g : G} {η : TEnv} {s s' : St} {C F : Res} (h : MintStep g η s s' C F) (key : Key) :
    F key ≤ 1 := by
  cases h with
  | none => simp
  | consume => simp
  | fresh =>
    simp only [Res.add_apply, Res.one_apply]
    split <;> split <;> simp_all
  | _ => simp only [Res.one_apply]; split <;> simp

theorem mintRoomT_of_zero (h : MintZeroT p k arch Sp Init MintOK c0) : MintRoomT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z key hk hF
  have h0 := h X Y Z key hk hF
  obtain ⟨-, -, -, -, -, -, hMS, -⟩ := Z
  have := MintStep_le_one hMS key
  omega

/-- **T20 `knetT`, core**: K-net after a thread step, given room for its mints. -/
theorem knetT_core {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hroom : ∀ key, ExclKey key → F key ≠ 0 → KeyLoad c Tot HP HS cr key + F key ≤ 1 + KeyDebt c db key) :
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS' (upd cr i cr') (upd db i db') key := by
  intro key hk
  have hroom : KeyLoad c Tot HP HS cr key + F key ≤ 1 + KeyDebt c db key := by
    by_cases hF : F key = 0
    · have := X.inv.knet key hk
      rw [keyNet_iff] at this
      omega
    · exact hroom key hk hF
  have hi : i < c.ths.size := lt_of_getq X.hth
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, hineq, -⟩ := Z
  have hI := hineq key
  have hT := congrFun hsum key
  have hs1 : ((List.range c.ths.size).map (fun n => (Tot n + HP n + pSumAt c n (cr n)) key)).sum +
        (upd Tot i Tot' i + upd HP i HP' i + pSumAt c' i (upd cr i cr' i)) key =
      ((List.range c.ths.size).map
          (fun n => (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (upd cr i cr' n)) key)).sum +
        (Tot i + HP i + pSumAt c i (cr i)) key :=
    sum_range_upd (f := (fun n => (Tot n + HP n + pSumAt c n (cr n)) key)) (g := (fun n => (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (upd cr i cr' n)) key)) hi (fun n hn => by
      rw [upd_other _ _ hn, upd_other _ _ hn, upd_other _ _ hn, thread_pSumAt_other X hn])
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt c' i (upd db i db' i) key =
      ((List.range c.ths.size).map (fun n => pSumAt c' n (upd db i db' n) key)).sum +
        pSumAt c i (db i) key :=
    sum_range_upd (f := (fun n => pSumAt c n (db n) key)) (g := (fun n => pSumAt c' n (upd db i db' n) key)) hi (fun n hn => by rw [upd_other _ _ hn, thread_pSumAt_other X hn])
  rw [upd_self, upd_self, upd_self, thread_pSumAt_self X, pSumAt_some X.hth] at hs1
  rw [upd_self, thread_pSumAt_self X, pSumAt_some X.hth] at hs2
  unfold KeyLoad KeyDebt at hroom
  unfold KeyNet
  rw [TermStep.threadSteps_size X.hc']
  simp only [Res.add_apply] at hs1 hs2 hroom hI hT ⊢
  omega

/-- **T20 `knetT`** (K-net after a thread step), under `MintRoomT`. -/
theorem knetT_proof (hR : MintRoomT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ) :
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS' (upd cr i cr') (upd db i db') key :=
  knetT_core X Y Z (hR X Y Z)

/-- **T19 `balT`** (the balance after a thread step), under `MintClosedT`,
with the mint `M + F` (the consumption `C` is dropped). -/
theorem balT_proof (hM : MintClosedT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ) :
    ∃ M, MintOK M ∧
      thSum c'.ths.size (fun j => upd Tot i Tot' j + pSumAt c' j (upd cr i cr' j) + upd HP i HP' j) + HS' ≤
        Init + M + thSum c'.ths.size (fun j => pSumAt c' j (upd db i db' j)) := by
  obtain ⟨M, hMo, hb⟩ := X.inv.bal
  refine ⟨M + F, hM X Y (Z.toC _ _ _ _ _) M hMo, Res.le_def.2 fun key => ?_⟩
  have hold := hb key
  have hi : i < c.ths.size := lt_of_getq X.hth
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, hineq, -⟩ := Z
  have hI := hineq key
  have hT := congrFun hsum key
  have hs1 : ((List.range c.ths.size).map (fun n => (Tot n + pSumAt c n (cr n) + HP n) key)).sum +
        (upd Tot i Tot' i + pSumAt c' i (upd cr i cr' i) + upd HP i HP' i) key =
      ((List.range c.ths.size).map
          (fun n => (upd Tot i Tot' n + pSumAt c' n (upd cr i cr' n) + upd HP i HP' n) key)).sum +
        (Tot i + pSumAt c i (cr i) + HP i) key :=
    sum_range_upd (f := (fun n => (Tot n + pSumAt c n (cr n) + HP n) key)) (g := (fun n => (upd Tot i Tot' n + pSumAt c' n (upd cr i cr' n) + upd HP i HP' n) key)) hi (fun n hn => by
      rw [upd_other _ _ hn, upd_other _ _ hn, upd_other _ _ hn, thread_pSumAt_other X hn])
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt c' i (upd db i db' i) key =
      ((List.range c.ths.size).map (fun n => pSumAt c' n (upd db i db' n) key)).sum +
        pSumAt c i (db i) key :=
    sum_range_upd (f := (fun n => pSumAt c n (db n) key)) (g := (fun n => pSumAt c' n (upd db i db' n) key)) hi (fun n hn => by rw [upd_other _ _ hn, thread_pSumAt_other X hn])
  rw [upd_self, upd_self, upd_self, thread_pSumAt_self X, pSumAt_some X.hth] at hs1
  rw [upd_self, thread_pSumAt_self X, pSumAt_some X.hth] at hs2
  rw [TermStep.threadSteps_size X.hc']
  simp only [Res.add_apply, thSum_apply] at hs1 hs2 hold hI hT ⊢
  omega

/-! ## 4. Discharging `MintRoomT` and `MintClosedT` by mint kind

A `MintStep` mints an exclusive key in three ways (`MintStep_rg`,
`MintStep_wd`, `MintStep_own`): `fresh` (`rg`/`wd` of `ridNext η`), `alloc`
(`own l` at a label of `FreshIn g …`) and `claim n j` (`rg n` for `ep n j`).
`MintStep` ties neither its constructor to the term nor `alloc`'s `g` to the
step's `g`, so `TOut` admits imprecise witnesses; the parts below are stated
for every witness. -/

/-- (a) **Rid freshness at the step**: a fresh mint names an id nobody holds.
Needs the step's view `η` chosen with `η.rid` at least the thread's counter
(`TermOnce.repick_fresh`) and a run invariant that every held `rg`/`wd` id is
used (`TermOnce.RidUsed`). -/
def RidFreshT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    F = Res.one (.rg (ridNext η)) + Res.one (.wd (ridNext η)) →
    KeyLoad c Tot HP HS cr (.rg (ridNext η)) ≤ KeyDebt c db (.rg (ridNext η)) ∧
      KeyLoad c Tot HP HS cr (.wd (ridNext η)) ≤ KeyDebt c db (.wd (ridNext η))

/-- (b1) **An own key is minted at one of the stepping thread's fresh
labels** (the `g` of `MintStep.alloc` is the step's: a stream-A export of
`tstepMCF_step`). -/
def AllocGT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ l, F (.own l) ≠ 0 → FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l

/-- (b2) **No own key of a label outside `E_g` is held** (frames, private
holdings, credits, shared holding) at a reachable configuration. -/
def OwnKeyStoN (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res},
    TermSpawnStep.StepsG p k arch Sp c0 c → SysInvN p k arch Init MintOK c Eg Tot HP HS cr db →
    ∀ l, Eg.sto l = none → KeyLoad c Tot HP HS cr (.own l) = 0

/-- (c) **Room for a claim** (S9b, the ghost-holder decision): the region key a
claim mints fits in the old net bound. -/
def ClaimRoomT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ n j, C = Res.one (.ep n j) → F = Res.one (.rg n) → KeyLoad c Tot HP HS cr (.rg n) + 1 ≤ 1 + KeyDebt c db (.rg n)

/-- **Room for a thread step's mints, per instance**, from (a) at this step, (b1) with (b2), and (c). -/
theorem mintRoom_at (hb1 : AllocGT p k arch Sp Init MintOK c0) (hb2 : OwnKeyStoN p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
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
    have hsto : Eg.sto (freshLabel c.lbase c.n i j) = none := (X.inv.fresh i th X.hth j hj1).1
    have := hb2 X.run X.inv _ hsto
    omega
  | _ => exact hk.elim

/-- **`MintRoomT` from its parts** (a), (b1) with (b2), and (c). -/
theorem mintRoomT_of_parts (ha : RidFreshT p k arch Sp Init MintOK c0) (hb1 : AllocGT p k arch Sp Init MintOK c0)
    (hb2 : OwnKeyStoN p k arch Sp Init MintOK c0) (hc : ClaimRoomT p k arch Sp Init MintOK c0) :
    MintRoomT p k arch Sp Init MintOK c0 :=
  fun X Y Z => mintRoom_at hb1 hb2 X Y Z (hc X Y Z) (ha X Y Z)

/-- (a) from the rid clause (`RidOK`) at a view whose counter is at least
the thread's (`TermOnce.repick_fresh`). -/
theorem ridFresh_of {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {rc : Nat → Nat}
    {η : TEnv} (h : RidOK c Tot HP HS cr db rc) (hle : rc η.tid ≤ η.rid) :
    KeyLoad c Tot HP HS cr (.rg (ridNext η)) ≤ KeyDebt c db (.rg (ridNext η)) ∧
      KeyLoad c Tot HP HS cr (.wd (ridNext η)) ≤ KeyDebt c db (.wd (ridNext η)) := by
  have hu := (TermOnce.fresh_unused hle).1
  exact ⟨h _ hu (.rg (ridNext η)) (Or.inl rfl), h _ hu (.wd (ridNext η)) (Or.inr rfl)⟩

/-- **T20 `knetT` with the rid clause**: K-net after a thread step at a view
`η` above the counters `rc` of `RidOK`, from (b1), (b2) and (c). -/
theorem knetT_rid (hb1 : AllocGT p k arch Sp Init MintOK c0) (hb2 : OwnKeyStoN p k arch Sp Init MintOK c0)
    (hc : ClaimRoomT p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ) {rc : Nat → Nat} (hrc : RidOK c Tot HP HS cr db rc) (hle : rc i ≤ η.rid) :
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS' (upd cr i cr') (upd db i db') key := by
  have htid : η.tid = i := Y.2.1
  have hle' : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  exact knetT_core X Y Z (mintRoom_at hb1 hb2 X Y Z (hc X Y Z) (fun _ => ridFresh_of hrc hle'))

/-- With the trivial `MintOK` (the balance's mint unconstrained: K-net now
carries the per-key bounds `MintOK` was for), `MintClosedT` holds. -/
theorem mintClosedT_true : MintClosedT p k arch Sp Init (fun _ => True) c0 :=
  fun _ _ _ _ _ => trivial

/-! ## 5. S9b under D5: ticket locks out of the interim scope

Design decision: D5 now (no `claim`/`mkTicket` in headline 1's
programs), D1 (word ghost-holder) scheduled with R2.  `claimRoom` is then
vacuous: a claim-shaped mint comes only from a `claim` term (`ClaimExportT`,
a stream-A export), and no reachable term is a `claim` (`TicketFreeRun`, from
`NoTicket p` by the residual invariant). -/

/-- The ticket-lock operations. -/
def opTicket : Op → Bool
  | .claim _ _ => true
  | .mkTicket _ _ _ _ _ => true
  | _ => false

/-- No ticket-lock operation anywhere in a term. -/
def exprNoTicket : Expr → Bool
  | .let_ _ op e => !opTicket op && exprNoTicket e
  | .split _ _ _ e => exprNoTicket e
  | .unpack _ _ _ e => exprNoTicket e
  | .unpackT _ _ _ e => exprNoTicket e
  | .region _ _ _ _ e => exprNoTicket e
  | .openPub _ _ _ _ e => exprNoTicket e
  | .case _ _ e₁ _ e₂ => exprNoTicket e₁ && exprNoTicket e₂
  | .ifnull _ e₁ _ e₂ => exprNoTicket e₁ && exprNoTicket e₂
  | .parity _ _ e₁ e₂ => exprNoTicket e₁ && exprNoTicket e₂
  | .ifeq _ _ e₁ e₂ => exprNoTicket e₁ && exprNoTicket e₂
  | .cas _ _ _ _ _ _ e₁ e₂ => exprNoTicket e₁ && exprNoTicket e₂
  | .casp _ _ _ _ _ _ _ _ e₁ e₂ => exprNoTicket e₁ && exprNoTicket e₂
  | .ret _ => true
  | .tail _ _ _ _ => true

/-- **(D5) The program uses no ticket lock** (syntactic; folded
into `ProgScopeOK`). -/
def NoTicket (p : Prog) : Bool := p.all fun d => exprNoTicket d.body

/-- (RunScope style) Every reachable thread's term is ticket-free. -/
def TicketFreeRun (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop :=
  ∀ c, TermSpawnStep.StepsG p k arch Sp c0 c → ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → exprNoTicket th.term = true

/-- **(new hypothesis) Reachable terms are residuals of program
code**, here only for ticket-freedom: from `NoTicket p` (and the initial
configuration's terms, which E's invariant covers). -/
def ResidualNoTicket (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop :=
  NoTicket p = true → TicketFreeRun p k arch Sp c0

/-- **(new hypothesis, stream-A export) A
claim-shaped mint comes from a `claim` term.**  Not provable over today's
`TOut`, whose `MintStep` is a free witness; it becomes a projection once
`tstepMCF_step` exports it and `TOut` carries it. -/
def ClaimExportT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ n j, C = Res.one (.ep n j) → F = Res.one (.rg n) → ∃ x w tk e, th.term = .let_ x (.claim w tk) e

/-- **`claimRoom` under D5**: vacuous, since no reachable step is a claim. -/
theorem claimRoom_D5 (hx : ClaimExportT p k arch Sp Init MintOK c0) (hr : TicketFreeRun p k arch Sp c0) :
    ClaimRoomT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z n j hC hF
  obtain ⟨x, w, tk, e, he⟩ := hx X Y Z n j hC hF
  have h := hr c X.run i th X.hth
  rw [he] at h
  simp [exprNoTicket, opTicket] at h

/-- `claimRoom` from `NoTicket p`, the residual invariant and the export. -/
theorem claimRoom_noTicket (hn : NoTicket p = true) (hres : ResidualNoTicket p k arch Sp c0)
    (hx : ClaimExportT p k arch Sp Init MintOK c0) : ClaimRoomT p k arch Sp Init MintOK c0 :=
  claimRoom_D5 hx (hres hn)

end

/-! ## 6. The thread step with a cross-thread credit transfer `δ` (check 7, option (d))

`TOut`'s last conjunct pays `Σ_{Fd} δ` out of the stepping thread's
inequality; idle threads' credits become `cr j + δ` (`updD`).  What the idle
threads receive is at most `Σ_{Fd} δ` (`CrShift_sum`: promises are
thread-disjoint and, by `PromNodupR`, duplicate-free).  At an unused region
id the step's inequality has nothing on its right, so `δ` carries nothing
there either (`ridT_D`). -/

/-- **(new field) Every thread's promises are duplicate-free** at a reachable
configuration (promises append the fresh timestamp `mem.size`, `AllPromLt`;
thread steps only remove promises). -/
def PromNodupR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop :=
  ∀ c, TermSpawnStep.StepsG p k arch Sp c0 c → ∀ (n : Nat) (th : TTh), c.ths[n]? = some th → th.promises.Nodup

/-- (S10, 2b) The run invariant behind `PromNodupR`: promise well-formedness and duplicate-free
promises (the `Sp`-arm of `promNodupR_of` keeps it). -/
def PromNodupI (c : Cfg) : Prop :=
  (c.ths.size = 0 ∨ TermFul.PWFall c) ∧ ∀ (n : Nat) (th : TTh), c.ths[n]? = some th → th.promises.Nodup

/-- (S10) **`PromNodupR` from the initial configuration**: duplicate-free
promises and promise well-formedness (`TermFul.PWFall`: promises are messages,
not pair starts) at `c0` (or no thread at all).  A thread step keeps a sublist
of the stepping thread's promises (`TermFul.tstep_fulfil`) and leaves the
others; a promise step appends `mem.size`, which no promise reaches. -/
theorem promNodupR_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (hSp : ∀ c c', Sp c c' → PromNodupI c → PromNodupI c')
    (h0 : ∀ (n : Nat) (th : TTh), c0.ths[n]? = some th → th.promises.Nodup)
    (hw0 : c0.ths.size = 0 ∨ TermFul.PWFall c0) : PromNodupR p k arch Sp c0 := by
  intro c hr
  refine (TermSpawnStep.stepsG_pres (P := PromNodupI) (fun c c' hs hp => ?_) hSp hr ⟨hw0, h0⟩).2
  obtain ⟨hw, hn⟩ := hp
  rcases hw with hz | hw
  · exfalso
    cases hs with
    | thread i hs' _ =>
        obtain ⟨th, -, hth, -⟩ := TermFul.threadSteps_inv hs'
        have hi := TermCert.arr_lt hth
        omega
    | prom i a v w hi _ _ => omega
  refine ⟨Or.inr (TermFul.step_pwfAll hs hw), ?_⟩
  cases hs with
  | thread i hs' _ =>
      obtain ⟨th, r, hth, hr, -, -, e3, -⟩ := TermFul.threadSteps_inv hs'
      have hw2 : ∀ t, t ∈ th.promises → t < c.mem.size ∧ t ∉ c.pairs :=
        fun t ht => (hw i).2 t (by rw [TermFul.promsOf_some hth]; exact ht)
      have hsub := (TermFul.tstep_fulfil (fun t ht => (hw2 t ht).1) (fun t ht => (hw2 t ht).2) hr).1
      intro n th' hn'
      by_cases hni : n = i
      · subst hni
        rw [e3] at hn'
        cases hn'
        exact List.Nodup.sublist hsub (hn _ _ hth)
      · have hpj : TermFul.promsOf c' n = TermFul.promsOf c n := by
          simp only [threadSteps, hth, List.mem_map] at hs'
          obtain ⟨_, _, rfl⟩ := hs'
          unfold TermFul.promsOf
          rw [TermFul.set_other hni]
        rw [TermFul.promsOf_some hn'] at hpj
        cases hc : c.ths[n]? with
        | none => simp only [TermFul.promsOf, hc, Option.map_none, Option.getD_none] at hpj; rw [hpj]; exact List.nodup_nil
        | some th0 => rw [TermFul.promsOf_some hc] at hpj; rw [hpj]; exact hn _ _ hc
  | prom i a v w hi _ _ =>
      intro n th' hn'
      by_cases hni : n = i
      · subst hni
        cases hth : c.ths[n]? with
        | none => rw [Array.getElem?_eq_getElem hi] at hth; cases hth
        | some th =>
            have hx : (promise c n a v w).ths[n]? = some { th with promises := th.promises ++ [c.mem.size] } := by
              simp only [promise, hth]; exact TermCert.arr_set hth
            rw [hx] at hn'
            cases hn'
            refine List.nodup_append.2 ⟨hn _ _ hth, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
            intro x hx y hy hxy
            rw [List.mem_singleton] at hy
            have hlt := ((hw n).2 x (by rw [TermFul.promsOf_some hth]; exact hx)).1
            rw [hxy, hy] at hlt
            exact Nat.lt_irrefl _ hlt
      · have hpj : TermFul.promsOf (promise c i a v w) n = TermFul.promsOf c n := by
          unfold TermFul.promsOf promise
          split
          · rfl
          · dsimp only; rw [TermFul.set_other hni]
        rw [TermFul.promsOf_some hn'] at hpj
        cases hc : c.ths[n]? with
        | none => simp only [TermFul.promsOf, hc, Option.map_none, Option.getD_none] at hpj; rw [hpj]; exact List.nodup_nil
        | some th0 => rw [TermFul.promsOf_some hc] at hpj; rw [hpj]; exact hn _ _ hc

theorem nsum_map_add (f g : Nat → Nat) : ∀ (l : List Nat),
    (l.map (fun n => f n + g n)).sum = (l.map f).sum + (l.map g).sum
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.sum_cons, nsum_map_add f g l]; omega

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **T20′ core**: K-net after a thread step with transfer `δ`, given room
for its mints. -/
theorem knetT_coreD {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hnd : ∀ (n : Nat) (th : TTh), c.ths[n]? = some th → th.promises.Nodup)
    (hroom : ∀ key, ExclKey key → F key ≠ 0 → KeyLoad c Tot HP HS cr key + F key ≤ 1 + KeyDebt c db key) :
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) (upd db i db') key := by
  intro key hk
  have hroom' : KeyLoad c Tot HP HS cr key + F key ≤ 1 + KeyDebt c db key := by
    by_cases hF : F key = 0
    · have := X.inv.knet key hk
      rw [keyNet_iff] at this
      omega
    · exact hroom key hk hF
  have hi : i < c.ths.size := lt_of_getq X.hth
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, Fd, hFd, hineq, -⟩ := Z
  have hI := hineq key
  have hT := congrFun hsum key
  have hδ := CrShift_sum hFd X.inv.disj hnd key (List.range c.ths.size) List.nodup_range
  have hsp := nsum_map_add (fun n => (Tot n + HP n + pSumAt c n (cr n)) key) (fun n => pSumAt c n δ key)
    (List.range c.ths.size)
  have hs1 : ((List.range c.ths.size).map
          (fun n => (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n δ key)).sum +
        (upd Tot i Tot' i + upd HP i HP' i + pSumAt c' i (updD cr i cr' δ i)) key =
      ((List.range c.ths.size).map
          (fun n => (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (updD cr i cr' δ n)) key)).sum +
        ((Tot i + HP i + pSumAt c i (cr i)) key + pSumAt c i δ key) :=
    sum_range_upd (f := fun n => (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n δ key)
      (g := fun n => (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (updD cr i cr' δ n)) key) hi
      (fun n hn => by
        show (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n δ key =
          (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (updD cr i cr' δ n)) key
        rw [upd_other _ _ hn, upd_other _ _ hn, updD_other _ _ _ hn, thread_pSumAt_other X hn]
        simp only [Res.add_apply]
        rw [pSumAt_add]
        omega)
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt c' i (upd db i db' i) key =
      ((List.range c.ths.size).map (fun n => pSumAt c' n (upd db i db' n) key)).sum +
        pSumAt c i (db i) key :=
    sum_range_upd (f := fun n => pSumAt c n (db n) key) (g := fun n => pSumAt c' n (upd db i db' n) key) hi
      (fun n hn => by
        show pSumAt c n (db n) key = pSumAt c' n (upd db i db' n) key
        rw [upd_other _ _ hn, thread_pSumAt_other X hn])
  rw [upd_self, upd_self, updD_self, thread_pSumAt_self X, pSumAt_some X.hth (cr i)] at hs1
  rw [upd_self, thread_pSumAt_self X, pSumAt_some X.hth (db i)] at hs2
  unfold KeyLoad KeyDebt at hroom'
  unfold KeyNet
  rw [TermStep.threadSteps_size X.hc']
  simp only [Res.add_apply] at hs1 hs2 hroom' hI hT hsp ⊢
  omega

/-- **Room for a claim, per step, under D5**: vacuous, since a claim-shaped
mint comes from a `claim` term (`ClaimAt`, exported by `tstepMCF_stepG`) and no
reachable term is one (`TicketFreeRun`). -/
theorem claimRoom_at (hres : TicketFreeRun p k arch Sp c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {C F : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (hcl : ClaimAt th.term C F) :
    ∀ n j, C = Res.one (.ep n j) → F = Res.one (.rg n) →
      KeyLoad c Tot HP HS cr (.rg n) + 1 ≤ 1 + KeyDebt c db (.rg n) := by
  intro n j h1 h2
  obtain ⟨x, w, tk, e, he⟩ := hcl n j h1 h2
  have h := hres c X.run i th X.hth
  rw [he] at h
  simp [exprNoTicket, opTicket] at h

/-- **T20′ `knetT`** (field type plus the step's `ClaimAt`), from (b1), (b2),
ticket-freedom and `PromNodupR`. -/
theorem knetT_D (hb1 : AllocGT p k arch Sp Init MintOK c0) (hb2 : OwnKeyStoN p k arch Sp Init MintOK c0)
    (hres : TicketFreeRun p k arch Sp c0) (hN : PromNodupR p k arch Sp c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hcl : ClaimAt th.term C F)
    (_hcs : CrShiftP c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cr i δ)
    {rc : Nat → Nat} (hrc : RidOK c Tot HP HS cr db rc) (hle : rc i ≤ η.rid) :
    ∀ key, ExclKey key → KeyNet c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) (upd db i db') key := by
  have htid : η.tid = i := Y.2.1
  have hle' : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  exact knetT_coreD X Y Z (hN c X.run)
    (mintRoom_at hb1 hb2 X Y Z (claimRoom_at hres X hcl) (fun _ => ridFresh_of hrc hle'))

/-- **T19′ `balT`** (field type), with the mint `M + F`. -/
theorem balT_D (hM : MintClosedT p k arch Sp Init MintOK c0) (hN : PromNodupR p k arch Sp c0) {c c' : Cfg}
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (_hcs : CrShiftP c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cr i δ) :
    ∃ M, MintOK M ∧
      thSum c'.ths.size (fun j => upd Tot i Tot' j + pSumAt c' j (updD cr i cr' δ j) + upd HP i HP' j) + HS' ≤
        Init + M + thSum c'.ths.size (fun j => pSumAt c' j (upd db i db' j)) := by
  obtain ⟨M, hMo, hb⟩ := X.inv.bal
  refine ⟨M + F, hM X Y (Z.toC _ _ _ _ _) M hMo, Res.le_def.2 fun key => ?_⟩
  have hold := hb key
  have hi : i < c.ths.size := lt_of_getq X.hth
  have hnd := hN c X.run
  have hdisj := X.inv.disj
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, Fd, hFd, hineq, -⟩ := Z
  have hI := hineq key
  have hT := congrFun hsum key
  have hδ := CrShift_sum hFd hdisj hnd key (List.range c.ths.size) List.nodup_range
  have hsp := nsum_map_add (fun n => (Tot n + pSumAt c n (cr n) + HP n) key) (fun n => pSumAt c n δ key)
    (List.range c.ths.size)
  have hs1 : ((List.range c.ths.size).map
          (fun n => (Tot n + pSumAt c n (cr n) + HP n) key + pSumAt c n δ key)).sum +
        (upd Tot i Tot' i + pSumAt c' i (updD cr i cr' δ i) + upd HP i HP' i) key =
      ((List.range c.ths.size).map
          (fun n => (upd Tot i Tot' n + pSumAt c' n (updD cr i cr' δ n) + upd HP i HP' n) key)).sum +
        ((Tot i + pSumAt c i (cr i) + HP i) key + pSumAt c i δ key) :=
    sum_range_upd (f := fun n => (Tot n + pSumAt c n (cr n) + HP n) key + pSumAt c n δ key)
      (g := fun n => (upd Tot i Tot' n + pSumAt c' n (updD cr i cr' δ n) + upd HP i HP' n) key) hi
      (fun n hn => by
        show (Tot n + pSumAt c n (cr n) + HP n) key + pSumAt c n δ key =
          (upd Tot i Tot' n + pSumAt c' n (updD cr i cr' δ n) + upd HP i HP' n) key
        rw [upd_other _ _ hn, upd_other _ _ hn, updD_other _ _ _ hn, thread_pSumAt_other X hn]
        simp only [Res.add_apply]
        rw [pSumAt_add]
        omega)
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt c' i (upd db i db' i) key =
      ((List.range c.ths.size).map (fun n => pSumAt c' n (upd db i db' n) key)).sum +
        pSumAt c i (db i) key :=
    sum_range_upd (f := fun n => pSumAt c n (db n) key) (g := fun n => pSumAt c' n (upd db i db' n) key) hi
      (fun n hn => by
        show pSumAt c n (db n) key = pSumAt c' n (upd db i db' n) key
        rw [upd_other _ _ hn, thread_pSumAt_other X hn])
  rw [upd_self, upd_self, updD_self, thread_pSumAt_self X, pSumAt_some X.hth (cr i)] at hs1
  rw [upd_self, thread_pSumAt_self X, pSumAt_some X.hth (db i)] at hs2
  rw [TermStep.threadSteps_size X.hc']
  simp only [Res.add_apply, thSum_apply] at hs1 hs2 hold hI hT hsp ⊢
  omega

/-- **One key across a thread step, at any bound `b`**: if the key's load plus the
step's mint fits in `b` plus the debits before the step, the load fits in `b` plus the
debits after it (`knetT_coreD`'s sum, with `1` generalised to `b`). -/
theorem knetT_keyB {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop}
    {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hnd : ∀ (n : Nat) (th : TTh), c.ths[n]? = some th → th.promises.Nodup) (key : Key) (b : Nat)
    (hroom' : KeyLoad c Tot HP HS cr key + F key ≤ b + KeyDebt c db key) :
    KeyLoad c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) key ≤ b + KeyDebt c' (upd db i db') key := by
  have hi : i < c.ths.size := lt_of_getq X.hth
  obtain ⟨-, -, -, -, -, -, hsum⟩ := Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, Fd, hFd, hineq, -⟩ := Z
  have hI := hineq key
  have hT := congrFun hsum key
  have hδ := CrShift_sum hFd X.inv.disj hnd key (List.range c.ths.size) List.nodup_range
  have hsp := nsum_map_add (fun n => (Tot n + HP n + pSumAt c n (cr n)) key) (fun n => pSumAt c n δ key)
    (List.range c.ths.size)
  have hs1 : ((List.range c.ths.size).map
          (fun n => (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n δ key)).sum +
        (upd Tot i Tot' i + upd HP i HP' i + pSumAt c' i (updD cr i cr' δ i)) key =
      ((List.range c.ths.size).map
          (fun n => (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (updD cr i cr' δ n)) key)).sum +
        ((Tot i + HP i + pSumAt c i (cr i)) key + pSumAt c i δ key) :=
    sum_range_upd (f := fun n => (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n δ key)
      (g := fun n => (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (updD cr i cr' δ n)) key) hi
      (fun n hn => by
        show (Tot n + HP n + pSumAt c n (cr n)) key + pSumAt c n δ key =
          (upd Tot i Tot' n + upd HP i HP' n + pSumAt c' n (updD cr i cr' δ n)) key
        rw [upd_other _ _ hn, upd_other _ _ hn, updD_other _ _ _ hn, thread_pSumAt_other X hn]
        simp only [Res.add_apply]
        rw [pSumAt_add]
        omega)
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt c' i (upd db i db' i) key =
      ((List.range c.ths.size).map (fun n => pSumAt c' n (upd db i db' n) key)).sum +
        pSumAt c i (db i) key :=
    sum_range_upd (f := fun n => pSumAt c n (db n) key) (g := fun n => pSumAt c' n (upd db i db' n) key) hi
      (fun n hn => by
        show pSumAt c n (db n) key = pSumAt c' n (upd db i db' n) key
        rw [upd_other _ _ hn, thread_pSumAt_other X hn])
  rw [upd_self, upd_self, updD_self, thread_pSumAt_self X, pSumAt_some X.hth (cr i)] at hs1
  rw [upd_self, thread_pSumAt_self X, pSumAt_some X.hth (db i)] at hs2
  unfold KeyLoad KeyDebt at hroom' ⊢
  rw [TermStep.threadSteps_size X.hc']
  simp only [Res.add_apply] at hs1 hs2 hroom' hI hT hsp ⊢
  omega

/-- `RidOK` is monotone in the counters. -/
theorem RidOK_mono {c : Cfg} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {rc rc' : Nat → Nat}
    (h : RidOK c Tot HP HS cr db rc) (hle : ∀ t, rc t ≤ rc' t) : RidOK c Tot HP HS cr db rc' :=
  fun n hn => h n (fun hu => hn (TermOnce.RidUsed_mono hle hu))

/-- **T21 `ridT`** (net rid clause after a thread step), at the counters bumped at the
stepping thread.  No hypothesis on the new debits: at an id unused after the step the
step mints nothing (a fresh mint names `ridNext η`, now used; a claim is excluded by
ticket-freedom), so `knetT_keyB` at bound `0` carries the old net bound over. -/
theorem ridT_N (hres : TicketFreeRun p k arch Sp c0) {c c' : Cfg} {Eg : GEnv}
    {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh} {r : Memory × List Ts × TTh}
    {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hcl : ClaimAt th.term C F) (hN : PromNodupR p k arch Sp c0)
    (rc : Nat → Nat) (hrc : RidOK c Tot HP HS cr db rc) (hle : rc i ≤ η.rid) :
    ∃ rc', RidOK c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ) (upd db i db') rc' := by
  have htid : η.tid = i := Y.2.1
  have hle' : rc η.tid ≤ η.rid := by rw [htid]; exact hle
  obtain ⟨-, hU, hmono⟩ := TermOnce.fresh_bump hle'
  refine ⟨TermOnce.ridSet rc η.tid (η.rid + 1), fun n hn key hkey => ?_⟩
  have hn0 : ¬ TermOnce.RidUsed rc n := fun h => hn (hmono n h)
  have hnf : n ≠ ridNext η := fun e => hn (e ▸ hU)
  have hcl : ∀ j, ¬ (C = Res.one (.ep n j) ∧ F = Res.one (.rg n)) := fun j ⟨h1, h2⟩ => by
    obtain ⟨x, w, tk, e, he⟩ := hcl n j h1 h2
    have h := hres c X.run i th X.hth
    rw [he] at h
    simp [exprNoTicket, opTicket] at h
  have hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F := Z.2.2.2.2.2.2.1
  have hF0 : F key = 0 := by
    rcases hkey with rfl | rfl
    · rcases TermOnce.MintStep_rg hMS n with h0 | ⟨e, -⟩ | ⟨j, h1, h2⟩
      · exact h0
      · exact absurd e hnf
      · exact absurd ⟨h1, h2⟩ (hcl j)
    · rcases TermOnce.MintStep_wd hMS n with h0 | ⟨e, -⟩
      · exact h0
      · exact absurd e hnf
  have hold : KeyLoad c Tot HP HS cr key ≤ KeyDebt c db key := hrc n hn0 key hkey
  have h := knetT_keyB X Y Z (hN c X.run) key 0 (by omega)
  unfold KeyLoad KeyDebt at h
  simpa using h

/-- **P10 `ridP`** (net rid clause after a promise step), at the same counters: `PAcct`
is an equality, so the promiser's load minus debit is unchanged key by key (as in
`knetP_proof`, at bound `0`).  No hypothesis. -/
theorem ridP_N {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hA : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db') :
    ∃ rc', RidOK (promise c j a v w) Tot (upd HP j HP') HS' (upd cr j cr') (upd db j db') rc' := by
  obtain ⟨rc, hrc⟩ := X.inv.rid
  refine ⟨rc, fun n hn key hkey => ?_⟩
  have hold := hrc n hn key hkey
  have hj : j < c.ths.size := lt_of_getq X.hth
  unfold PAcct at hA
  have hA' := congrFun hA key
  have hs1 : ((List.range c.ths.size).map (fun n => (Tot n + HP n + pSumAt c n (cr n)) key)).sum +
        (Tot j + upd HP j HP' j + pSumAt (promise c j a v w) j (upd cr j cr' j)) key =
      ((List.range c.ths.size).map
          (fun n => (Tot n + upd HP j HP' n + pSumAt (promise c j a v w) n (upd cr j cr' n)) key)).sum +
        (Tot j + HP j + pSumAt c j (cr j)) key :=
    sum_range_upd (f := (fun n => (Tot n + HP n + pSumAt c n (cr n)) key))
      (g := (fun n => (Tot n + upd HP j HP' n + pSumAt (promise c j a v w) n (upd cr j cr' n)) key)) hj
      (fun n hn => by rw [upd_other _ _ hn, upd_other _ _ hn, promise_pSumAt_other hn])
  have hs2 : ((List.range c.ths.size).map (fun n => pSumAt c n (db n) key)).sum +
        pSumAt (promise c j a v w) j (upd db j db' j) key =
      ((List.range c.ths.size).map (fun n => pSumAt (promise c j a v w) n (upd db j db' n) key)).sum +
        pSumAt c j (db j) key :=
    sum_range_upd (f := (fun n => pSumAt c n (db n) key))
      (g := (fun n => pSumAt (promise c j a v w) n (upd db j db' n) key)) hj
      (fun n hn => by rw [upd_other _ _ hn, promise_pSumAt_other hn])
  rw [upd_self, upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs1
  rw [upd_self, promise_pSumAt_self X.hth, pSumAt_some X.hth] at hs2
  rw [TermStep.promise_size]
  simp only [Res.add_apply] at hs1 hs2 hold hA' ⊢
  omega

end

#print axioms knetP_proof
#print axioms balP_proof
#print axioms knetT_proof
#print axioms balT_proof
#print axioms mintRoomT_of_zero
#print axioms mintRoomT_of_parts
#print axioms mintClosedT_true
#print axioms ridFresh_of
#print axioms knetT_rid
#print axioms claimRoom_D5
#print axioms claimRoom_noTicket
#print axioms knetT_coreD
#print axioms ridT_N
#print axioms ridP_N
#print axioms knetT_D
#print axioms balT_D
#print axioms claimRoom_at

#print axioms promNodupR_of

end TermBal

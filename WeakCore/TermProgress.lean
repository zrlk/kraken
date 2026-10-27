import WeakCore.TermProgressDefs
import WeakCore.ExtArmZ
import WeakCore.TermCertScope
import WeakCore.TermLiveProps
/-!
# TermProgress — item 36: per-thread progress on EM0 runs, and its sharpness

On a run from an EM0 start (the premises of the frozen `ExtArmZ.reachable_typed_em0`), every thread that is not
finished-and-promise-free either has a move of its own (`MovesBy`: a certified thread step, a certified promise, a
spawn, or an extern step) or is stuck for one of two listed reasons (`StuckWhy`): (u) promises out and not
certifiable, (s) at a spawn site, promise-free, at capacity (`progress_main`).  A listed reason really blocks the
thread (`stuck_sharp`, machine-only).  Configuration level: `progress_main_cfg`.

The vocabulary (`StuckWhy`, `SpawnBy`, `ExtBy`, `MovesBy`, `movesBy_step`) lives in `TermProgressDefs` (shared with
the liveness system).  The definition and statement texts are the original ones, with the
rename `progress_em0` → `progress_main`, `progress_em0_cfg` →
`progress_main_cfg`; its unused premise `c.final = false` is dropped.  The helper lemmas (`cert_movesBy`, `thr_typed`, `pf_progress`, `site_eval`,
`publish_progress`) were moved here.

Proof route (STUDY §A):
* promises out: `Certified c i` gives the first move of the certifying solo run (`cert_movesBy`), else (u);
* promise-free, unfinished: at a spawn site `Spawn` if below capacity (`site_eval`), else (s); at an extern site
  the empty certificate (`extCfg_noPromises`); otherwise a thread step (`pf_progress`, with `publish_progress`
  for `publish`), certified by the empty run (`threadStep_promFree`, `tstep_ext`'s promise half).
* sharpness: (u) each move prefixes to a solo run certifying `c`; (s) `threadSteps_spawn`, `cert_site` on the
  promise configuration, the capacity, and the term shape.
-/

namespace TermProgress
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep
open WeakMem (Arch)

/-! ## Machine-level helpers -/

/-- A thread `c.ths[i]? = some th` has `i < c.ths.size`. -/
theorem lt_of_get {c : Cfg} {i : Nat} {th : TTh} (hth : c.ths[i]? = some th) : i < c.ths.size := by
  rcases Nat.lt_or_ge i c.ths.size with h | h
  · exact h
  · simp [Array.getElem?_eq_none h] at hth

/-- (now with thread `i`'s own move) **A certified thread with promises has a
move of its own**: the first move of the certifying solo run. -/
theorem cert_movesBy {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c : Cfg} {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (hp : th.promises ≠ []) (hc : Certified p k arch c i)
    (hpk : ¬ ∃ x a e, th.term = .let_ x (.ext .park a) e ∧ th.permit = none) :
    MovesBy p k arch cap c i := by
  obtain ⟨c1, hso, hnp⟩ := hc
  cases hso with
  | refl => simp [noPromises, hth] at hnp; exact absurd hnp hp
  | thread h1 h2 => exact .inl ⟨_, h1, _, h2, hnp⟩
  | prom a v w hw h2 => exact .inr (.inl ⟨a, v, w, lt_of_get hth, hw, _, h2, hnp⟩)
  | ext h1 h2 =>
      obtain ⟨th', x, n, a, e, rt, ws, rs, h3, hterm, hN, hev, hrs, rfl⟩ := extSteps_elim h1
      have e1 : th = th' := Option.some.inj (hth.symm.trans h3)
      subst e1
      have hen : ExtEnabled n th := by
        by_cases hn : n = .park
        · subst hn
          cases hpm : th.permit
          · exact absurd ⟨x, a, e, hterm, hpm⟩ hpk
          · exact Or.inr (by rw [hpm]; rfl)
        · exact Or.inl hn
      exact .inr (.inr (.inr ⟨_, x, n, a, e, th, rt, ws, rs, hth, hterm, fun h => absurd h hN, hen, hev,
        (mem_resultsL _ _ _ _ _).1 hrs, ⟨_, h2, hnp⟩, rfl⟩))

/-- A thread step of a promise-free thread leaves it promise-free (`tstep_ext`'s promise half). -/
theorem threadStep_promFree {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (hnp : th.promises = []) (h : c' ∈ threadSteps p k arch c i) :
    noPromises c' i = true := by
  have hi := lt_of_get hth
  unfold threadSteps at h
  rw [hth] at h
  simp only [List.mem_map] at h
  obtain ⟨⟨mem, pairs, th'⟩, hin, rfl⟩ := h
  have hp' : th'.promises = [] := by
    have hx := (TermLiveProps.tstep_ext _ _ _ _ _ hin).prom
    rcases hq : th'.promises with _ | ⟨t, ts⟩
    · rfl
    · have ht := hx t (by simp [stOf, hq])
      simp [stOf, hnp] at ht
  simp [noPromises, Array.set!, hi, hp']

/-- A `SpawnT` term is a spawn site or an extern site. -/
theorem spawnT_cases {t : Expr} (h : TermStep.SpawnT t) :
    (∃ x f a T ts e, t = .let_ x (.spawn f a T ts) e) ∨ (∃ x n a e, t = .let_ x (.ext n a) e) := by
  unfold TermStep.SpawnT at h
  split at h
  · exact .inl ⟨_, _, _, _, _, _, rfl⟩
  · exact .inr ⟨_, _, _, _, rfl⟩
  · exact h.elim

/-! ## Typing helpers -/
section
open CoreTyping TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain

/-- A thread of a `SysInvN` configuration is typed, with its frame invariant. -/
theorem thr_typed {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → WeakMem.Ts → Res}
    {i : Nat} {th : TTh} (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hth : c.ths[i]? = some th) :
    ∃ ρ η cx, Typed p cx th.term ∧ FInv ρ η th.σs (Resume p th.stack) cx th.env := by
  obtain ⟨S, hS⟩ := h.thr i th hth
  obtain ⟨ρ, η, cx, Rf, Rs, -, -, -, hT, htv, hFI, -⟩ := ThSysAt.env h.clo hS
  have hNI : ∀ c : Cx, TvOK c → noIallV c.ret = true := fun _ h => h.2.2.2.2.2.2.2
  exact ⟨ρ, η, cx, hT.1,
    FInvR_FInv (hNI cx htv) (fun E rd ws R h => ResumeR_Resume hNI th.stack Rs E rd ws R h) hFI⟩

/-- Typing gives the argument words at spawn/ext sites. -/
theorem site_eval {p : Prog} {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {th : TTh} {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) :
    ∀ a, (∃ f T ts, op = .spawn f a T ts) ∨ (∃ n, op = .ext n a) → ∃ rt ws, evalAt th.env a = some (rt, ws) := by
  intro a ha
  rw [hterm] at hT
  cases hT with
  | let_ hop' _ =>
    rcases ha with ⟨f, T, ts, rfl⟩ | ⟨n, rfl⟩
    · cases hop' with
      | spawn hu =>
        obtain ⟨-, rt, ws, hea, -⟩ := use_FInv hu hi
        exact ⟨rt, ws, hea⟩
    · cases hop' with
      | ext hu =>
        obtain ⟨-, rt, ws, hea, -⟩ := use_FInv hu hi
        exact ⟨rt, ws, hea⟩

/-- A `publish` has a thread step (no `NoHold` needed for progress). -/
theorem publish_progress {p : Prog} {g : G} {mem : WeakMem.Memory} {pairs : List WeakMem.Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.publish a) e)
    (hT : Typed p cx th.term) (hi : FInv ρ η th.σs (Resume p th.stack) cx th.env) :
    tstep g mem pairs th ≠ [] := by
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
    cases hop with
    | publish hu =>
      obtain ⟨-, lab, c, pw, μr, ru, hea, hpw, -⟩ := ownPtr_inv hu hi
      simp [tstep, hterm, evalOp, hea, ol]
    | publishBuf hu =>
      obtain ⟨-, μr, nr, ur, ψ, wsb, hea, -⟩ := ownBuf_inv hu hi
      simp [tstep, hterm, evalOp, hea, ol]

/-- (now also covering `publish` via `publish_progress`) A promise-free, unfinished
thread of a `SysInvN` configuration in run scope that is not at a spawn/ext site has a thread step. -/
theorem pf_progress {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → WeakMem.Ts → Res}
    {i : Nat} {th : TTh} [ProgRetIall p] (hP : ProgT p)
    (h : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hrs : TermScope.RunScope c)
    (hth : c.ths[i]? = some th) (hnd : isDone th = false) (hnp : th.promises = [])
    (hns : ¬ SpawnT th.term) :
    threadSteps p k arch c i ≠ [] := by
  obtain ⟨S, hS⟩ := h.thr i th hth
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hFI, hsum, -, hm, -, -, hRP⟩ := ThSysAt.env h.clo hS
  have hT' : Typed p cx th.term := hT.1
  have hNI : ∀ c : Cx, TvOK c → noIallV c.ret = true := fun _ h => h.2.2.2.2.2.2.2
  have hi : FInv ρ η th.σs (Resume p th.stack) cx th.env :=
    FInvR_FInv (hNI cx htv) (fun E rd ws R h => ResumeR_Resume hNI th.stack Rs E rd ws R h) hFI
  rcases Classical.em (∃ x a e, th.term = .let_ x (.publish a) e) with ⟨x, a, e, hpub⟩ | hnpub
  · have key := publish_progress (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hpub hT' hi
    unfold threadSteps; rw [hth]; simpa using key
  have hsc := TermCertScope.scopeAt_of (p := p) (i := i) hrs th hth hns ρ η cx hE hT' htv hi
  have hn : 0 < (gOf p k arch c i).n := by
    show 0 < c.n
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Cfg.lt_n (lt_of_get hth))
  have hwin : PubWinT (CE η) (stOf c.mem c.pairs th) th := by
    intro x a e rt ws ad hterm; exact absurd ⟨x, a, e, hterm⟩ hnpub
  have key := (tstep_footprint (g := gOf p k arch c i) (mem := c.mem) (pairs := c.pairs) hP rfl hn hnd hsc hT' hi hE htv
    hm h.bf (Or.inl hnp) hwin hRP pwSkel_ok pwSubS_ok pwSig_ok).1
  unfold threadSteps; rw [hth]; simpa using key

end

/-! ## Item 36 -/

/-- (M1) Every extern call admits some result list (`resultsL` is never empty; `devChoice w`: the value 0). -/
theorem exists_admits (n : ExtName) (i : Nat) (ws : List Word) (tr : List Event) : ∃ rs, n.Admits i ws tr rs := by
  have hne : n.resultsL i ws tr ≠ [] := by
    cases n <;> rcases ws with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;>
      simp [CoreTerm.ExtName.resultsL, List.range_eq_nil]
  obtain ⟨rs, hrs⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨rs, (mem_resultsL _ _ _ _ _).1 hrs⟩

/-- **Item 36 (progress half).** On an EM0 run, every thread that is not finished-and-promise-free can move,
or is stuck for a listed reason. -/
theorem progress_main {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (O : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : TermMain.InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsE p k arch c0.cap c0 c) :
    ∀ i th, c.ths[i]? = some th → ¬ (isDone th = true ∧ th.promises = []) →
      MovesBy p k arch c0.cap c i ∨ StuckWhy p k arch c0.cap c i th := by
  intro i th hth hnf
  by_cases hpk : ∃ x a e, th.term = .let_ x (.ext .park a) e ∧ th.permit = none
  · -- (D4) parked without a permit: a certified promise is a move; otherwise the thread is parked
    obtain ⟨x, a, e, hterm, hpm⟩ := hpk
    by_cases hpr : ∃ a v w, w < c.mem.size ∧ Certified p k arch (promise c i a v w) i
    · obtain ⟨a', v, w, hw, hc⟩ := hpr
      exact .inl (.inr (.inl ⟨a', v, w, lt_of_get hth, hw, hc⟩))
    · exact .inr (.parked ⟨x, a, e, hterm⟩ hpm (fun a' v w hw hc => hpr ⟨a', v, w, hw, hc⟩))
  by_cases hp : th.promises = []
  · obtain ⟨Eg, Tot, HP, HS, cr, db, hN, -⟩ := ExtArmZ.machine_tokens_main_em0 O hk h0 hr
    have hnd : isDone th = false := by
      cases hd : isDone th
      · rfl
      · exact absurd ⟨hd, hp⟩ hnf
    by_cases hs : TermStep.SpawnT th.term
    · obtain ⟨ρ, η, cx, hT, hi⟩ := thr_typed hN hth
      rcases spawnT_cases hs with ⟨x, f, a, T, ts, e, hterm⟩ | ⟨x, n, a, e, hterm⟩
      · obtain ⟨rt, ws, hev⟩ := site_eval hterm hT hi a (.inl ⟨f, T, ts, rfl⟩)
        by_cases hcap : c.ths.size < c0.cap
        · exact .inl (.inr (.inr (.inl ⟨_, x, f, a, T, ts, e, th, rt, ws, hth, hterm, hp, hcap, hev, rfl⟩)))
        · exact .inr (.atCap ⟨x, f, a, T, ts, e, hterm⟩ hp (Nat.le_of_not_lt hcap))
      · obtain ⟨rt, ws, hev⟩ := site_eval hterm hT hi a (.inr ⟨n, rfl⟩)
        have hen : ExtEnabled n th := by
          by_cases hn : n = .park
          · subst hn
            cases hpm : th.permit
            · exact absurd ⟨x, a, e, hterm, hpm⟩ hpk
            · exact Or.inr (by rw [hpm]; rfl)
          · exact Or.inl hn
        obtain ⟨rs, hadm⟩ := exists_admits n i ws c.trace
        exact .inl (.inr (.inr (.inr ⟨_, x, n, a, e, th, rt, ws, rs, hth, hterm, fun _ => hp, hen, hev, hadm,
          ⟨_, .refl _, by rw [extCfg_noPromises hth, hp]; rfl⟩, rfl⟩)))
    · have hPSc : TermScope.ProgScopeOK p = true := TermScope.ProgScopeOKW.scope O.progScope
      haveI : TermTv.ProgRetIall p :=
        ⟨fun _ hd => TermScope.noIallV_of_drf _ (TermScope.ProgScopeOK.decl hPSc hd).2.1⟩
      have hrs : TermScope.RunScope c :=
        TermScope.runDRFR_of hPSc (ExtArmZ.spLeafArms_em0 (cap := c0.cap)).runDRF O.runDRF0 hr
      have hne := pf_progress (TermScope.progT_of_check O.checked) hN hrs hth hnd hp hs
      obtain ⟨c', hc'⟩ := List.exists_mem_of_ne_nil _ hne
      exact .inl (.inl ⟨c', hc', c', .refl _, threadStep_promFree hth hp hc'⟩)
  · by_cases hc : Certified p k arch c i
    · exact .inl (cert_movesBy hth hp hc hpk)
    · exact .inr (.uncert hp hc)

/-- **Item 36 (sharpness).** A listed reason really blocks the thread. Machine-only (no typing). -/
theorem stuck_sharp {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c : Cfg} {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (h : StuckWhy p k arch cap c i th) : ¬ MovesBy p k arch cap c i := by
  intro hm
  cases h with
  | uncert hp hnc =>
    apply hnc
    rcases hm with ⟨c', h1, c'', h2, h3⟩ | ⟨a, v, w, -, hw, c'', h2, h3⟩ |
      ⟨c', x, f, a, T, ts, e, th', rt, ws, h1, -, h3, -⟩ | ⟨c', x, n, a, e, th', rt, ws, rs, h1, h2, h3, -, h4, hadm, ⟨c'', h5, h6⟩, -⟩
    · exact ⟨c'', .thread h1 h2, h3⟩
    · exact ⟨c'', .prom a v w hw h2, h3⟩
    · rw [hth] at h1; cases h1; exact absurd h3 hp
    · rw [hth] at h1; cases h1
      have hN : ¬ ExtNeedsNoProm n th := fun hn => hp (h3 hn)
      have hmem : extCfg c i th x n e ws rs ∈ extSteps c i := extSteps_intro hth h2 hN h4 ((mem_resultsL _ _ _ _ _).2 hadm)
      exact ⟨c'', .ext hmem h5, h6⟩
  | atCap hs hp hcap =>
    obtain ⟨x, f, a, T, ts, e, hterm⟩ := hs
    rcases hm with ⟨c', h1, -⟩ | ⟨a', v, w, hi, -, hc⟩ |
      ⟨c', x', f', a'', T', ts', e', th', rt, ws, h1, -, -, h4, -⟩ | ⟨c', x', n, a'', e', th', rt, ws, rs, h1, h2, -⟩
    · rw [threadSteps_spawn hth hterm] at h1; simp at h1
    · have hget : (promise c i a' v w).ths[i]? = some
          ⟨th.term, th.env, th.σs, th.stack, th.vs, th.promises ++ [c.mem.size], th.nalloc, th.undefs, th.tidLbl,
            th.permit⟩ := by
        have he : c.ths[i] = th := Option.some.inj ((Array.getElem?_eq_getElem hi).symm.trans hth)
        simp [promise, Array.set!, hi, he]
      have := cert_site hget ⟨x, f, a, T, ts, e, hterm⟩ hc
      simp at this
    · rw [hth] at h1; cases h1; exact absurd h4 (Nat.not_lt.mpr hcap)
    · rw [hth] at h1; cases h1; rw [hterm] at h2; cases h2
  | parked hs hpm hnc =>
    obtain ⟨x, a, e, hterm⟩ := hs
    rcases hm with ⟨c', h1, -⟩ | ⟨a', v, w, -, hw, hc⟩ |
      ⟨c', x', f', a'', T', ts', e', th', rt, ws, h1, h2, -⟩ | ⟨c', x', n, a'', e', th', rt, ws, rs, h1, h2, -, hen, -⟩
    · unfold threadSteps at h1
      rw [hth] at h1
      simp only [List.mem_map] at h1
      obtain ⟨r, hr, -⟩ := h1
      exact TermStep.not_spawnT_of_mem hr (by rw [hterm]; trivial)
    · exact hnc a' v w hw hc
    · rw [hth] at h1; cases h1; rw [hterm] at h2; cases h2
    · rw [hth] at h1; cases h1; rw [hterm] at h2; cases h2
      rcases hen with hen | hen
      · exact hen rfl
      · rw [hpm] at hen; cases hen

/-- **Item 36 (A1 corollary, configuration level).** A reachable configuration (final or not) has a machine move, or every
unfinished thread is stuck for a listed reason. -/
theorem progress_main_cfg {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c0 : Cfg}
    (O : TermMain.ObligationsFX p k arch (fun c c' => Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') Init
      (fun _ => True) c0) (hk : k.storeDepRts = true) (h0 : TermMain.InitOK p k arch Init (fun _ => True) c0)
    {c : Cfg} (hr : StepsE p k arch c0.cap c0 c) :
    (∃ c', Step p k arch c c' ∨ Spawn p k arch c0.cap c c' ∨ Ext p k arch c c') ∨
    ∀ i th, c.ths[i]? = some th → ¬ (isDone th = true ∧ th.promises = []) → StuckWhy p k arch c0.cap c i th := by
  rcases Classical.em (∃ i, MovesBy p k arch c0.cap c i) with ⟨i, hi⟩ | hno
  · exact .inl (movesBy_step hi)
  · refine .inr fun i th hth hnd => ?_
    rcases progress_main O hk h0 hr i th hth hnd with hm | hs
    · exact absurd ⟨i, hm⟩ hno
    · exact hs

end TermProgress
#print axioms TermProgress.lt_of_get
#print axioms TermProgress.cert_movesBy
#print axioms TermProgress.threadStep_promFree
#print axioms TermProgress.spawnT_cases
#print axioms TermProgress.thr_typed
#print axioms TermProgress.site_eval
#print axioms TermProgress.publish_progress
#print axioms TermProgress.pf_progress
#print axioms TermProgress.progress_main
#print axioms TermProgress.stuck_sharp
#print axioms TermProgress.progress_main_cfg

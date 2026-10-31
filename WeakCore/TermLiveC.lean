import WeakCore.TermLiveL3
/-!
# TermLiveC — the held branch of liveness

A thread that keeps touching a word `b` whose latest value is in a held state of its protocol, while the holder `h`
has crashed, waits forever on `b`: from the crash on (and on a promise-free suffix), `b`'s latest value is constant.

* `HeldBy` — ONE invariant witness (`SysInvN` with `OwnLive`, `ObsAll`) in which `b` is a word of `P` (region `n`),
  `b`'s latest value is held, and `h`'s frame carries `rg n`.
* `held_latest_const` — the core: the latest value of `b` is constant from `n₀` on (by induction over the run, with
  the witness carried across every move: `sysInvO_mstepE_ext`; a write at `b` by another thread contradicts
  `TermLiveHeld.held_word_changes_only_by_holder_sum_noFoot`; a promise step contradicts the promise-free suffix).
* `forced_wait_held_thm` — the run form (`StuckOnW`).

`PromFreeFrom` is a hypothesis restricting the run (from `n₀` on, no outstanding promise); it is not a fairness
condition.  Without it the proof does not go through, and the statement is likely false: `SysInvN` does not forbid a
non-holder's promise of a write at `b`, and a promised message counts for `Latest`.

This supersedes `TermLiveMach.forced_wait_is_livelock` (whose hold view is unlinked and which has no promise-free
hypothesis) for the held branch.
-/
namespace TermLiveC
open CoreLang CoreTerm TermRun TermSpawnStep TermExtStep TermLiveMach TermLiveL3
open WeakMem (Arch Address)

/-! ### The single-witness held state (decision (3)) -/

/-- **`HeldBy c b n P h`**: ONE invariant witness (`SysInvN` with the spawn-era companions `OwnLive`, `ObsAll`) in
which `b` is a non-ghost word of `P` naming region `n`, `b`'s latest value is in a held state of `P`, thread `h`'s
frame bound carries `rg n`, and no outstanding promise owes `rg n`.  The `Debt = 0` clause is redundant under
`PromFreeFrom` (`debt_zero_of_allNoProm`); it is kept for the `HeldPromFree` follow-up, which drops `PromFreeFrom`. -/
def HeldBy (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) (c : Cfg) (b : Address) (n : Nat)
    (P : Proto) (h : Nat) : Prop :=
  ∃ Eg Tot HP HS cr db, TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    TermSpawn.OwnLive Eg c ∧ TermSpawn.ObsAll Eg c ∧
    WordAtG Eg b n P ∧ (∀ cl, Eg.sto b.label = some cl → TermSound.IniAt Eg.ini cl b (.word (.lit n) P)) ∧
    pwf P = true ∧ (∃ v, Latest c b v ∧ TermLiveHeld.HeldV P v) ∧
    h < c.ths.size ∧ 1 ≤ Tot h (.rg n) ∧ TermMain.Debt c db (.rg n) = 0

/-- The hold view of `HeldBy` (for `Induced`-shaped statements); `hvI` is untouched.  `heldAt` and `holder` each pick
their own witness and are unlinked in `Induced`/`InducedW`: a consumer needing the link uses `HeldBy` itself. -/
def hvH (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) : HoldView where
  heldAt c b n P := ∃ h, HeldBy p k arch Init c b n P h
  holder c b n h := ∃ P, HeldBy p k arch Init c b n P h

/-- From `n₀` on, no thread has an outstanding promise. -/
def PromFreeFrom {L : Type} (r : LRun L) (n₀ : Nat) : Prop :=
  ∀ m, n₀ ≤ m → TermMain.AllNoProm (r.cfg m)

/-- With no outstanding promise, nothing is owed: `HeldBy`'s `Debt = 0` clause is redundant under `PromFreeFrom`. -/
theorem debt_zero_of_allNoProm {c : Cfg} (h : TermMain.AllNoProm c) (db : Nat → WeakMem.Ts → TermSound.Res)
    (key : TermSound.Key) : TermMain.Debt c db key = 0 := by
  unfold TermMain.Debt
  have : ∀ l : List Nat, (l.map (fun i => TermSys.pSumAt c i (db i) key)).sum = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => rw [List.map_cons, List.sum_cons, ih, TermMain.pSumAt_zero h]
  exact this _

/-! ### The held branch (item 15 C) -/

/-- **C, run form.** A thread that is scheduled infinitely often and touches `b` infinitely often (`TouchesW`: any access
at `b` — `cas`, `casp`, `fetch`, `ldp`, a load — except a `NoWordRead` load) is `StuckOnW` on `b` once `b` is held
(`HB`) by a crashed holder, from a point on which the run is promise-free.  `StuckOnW`'s content is only that `b`'s
latest value is eventually constant while the thread keeps touching it; it does not say the thread makes no progress
elsewhere. -/
def forced_wait_held (sys : LSys) (Setting : Cfg → Prop)
    (HB : Cfg → Address → Nat → Proto → Nat → Prop) : Prop :=
  ∀ c₀, Setting c₀ →
  ∀ (r : LRun sys.L) (D : Nat → Option Nat) i b n P h m n₀, sys.Run r → r.cfg 0 = c₀ →
    CrashOK sys r D → D h = some m → m ≤ n₀ → HB (r.cfg n₀) b n P h → PromFreeFrom r n₀ →
    Often (fun n => r.lbl n = some (sys.thr i)) → Often (fun n => TouchesW (r.cfg n) i b) →
    StuckOnW sys r i b

/-! ### Memory: the latest value across an extension -/

section mem
open WeakMem (Msg Memory Val)

/-- The latest message at `b` is frozen: every message at `b` is at or below it. -/
theorem latest_frozen {mem : Memory} {b : Address} {v : Val} (h : Promises.LatestIs mem b v) :
    ∃ (t : Nat) (m : Msg), mem[t]? = some m ∧ m.loc = b ∧ m.val = v ∧
      ∀ (t' : Nat) (m' : Msg), mem[t']? = some m' → m'.loc = b → t' ≤ t := by
  obtain ⟨t, m, hm, hl, hv, hb⟩ := h
  refine ⟨t, m, hm, hl, hv, fun t' m' hm' hl' => Nat.le_of_not_lt fun hlt => ?_⟩
  have h1 := Promises.betweenAt_of_witness hlt hm' hl'
  rw [hb] at h1
  cases h1

/-- An extension that appends nothing at `b` keeps `b`'s latest value. -/
theorem latest_ext_noNew {mem mem' : Memory} {b : Address} {v : Val} (he : Promises.Sim.MemExt mem mem')
    (hno : ∀ t (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc ≠ b) (h : Promises.LatestIs mem b v) :
    Promises.LatestIs mem' b v := by
  obtain ⟨t, m, hm, hl, hv, hfz⟩ := latest_frozen h
  have ht : t < mem.size := Promises.lt_size_of_getElem? hm
  refine Promises.latestIs_of_frozen (N := t) (m := m) ?_ hl hv fun t' m' hm' hl' => ?_
  · rw [he.get t ht]; exact hm
  · rcases Nat.lt_or_ge t' mem.size with h1 | h1
    · rw [he.get t' h1] at hm'; exact hfz t' m' hm' hl'
    · exact absurd hl' (hno t' m' h1 hm')

/-- A least witness below a bound. -/
theorem exists_first_aux {P : Nat → Prop} : ∀ K N, N < K → P N → ∃ t, P t ∧ ∀ t', t' < t → ¬ P t'
  | 0, _, hN, _ => absurd hN (Nat.not_lt_zero _)
  | K + 1, N, hN, hp => by
    by_cases h : ∃ t', t' < N ∧ P t'
    · obtain ⟨t', ht', hp'⟩ := h
      exact exists_first_aux K t' (by omega) hp'
    · exact ⟨N, hp, fun t' ht' hp' => h ⟨t', ht', hp'⟩⟩

theorem exists_first {P : Nat → Prop} {N : Nat} (hp : P N) : ∃ t, P t ∧ ∀ t', t' < t → ¬ P t' :=
  exists_first_aux (N + 1) N (Nat.lt_succ_self N) hp

/-- The first appended message at `b` is preceded (`PredAt`) by `b`'s old latest message. -/
theorem pred_of_first {mem mem' : Memory} {b : Address} {v : Val} (he : Promises.Sim.MemExt mem mem')
    (h : Promises.LatestIs mem b v) {t : Nat}
    (hfirst : ∀ t' (m' : Msg), mem.size ≤ t' → t' < t → mem'[t']? = some m' → m'.loc ≠ b) (ht : mem.size ≤ t) :
    ∃ wd, TermStep.PredAt mem' b t wd ∧ wd.val = v := by
  obtain ⟨t0, m0, hm0, hl0, hv0, hfz⟩ := latest_frozen h
  have h0 : t0 < mem.size := Promises.lt_size_of_getElem? hm0
  refine ⟨TermMem.mw m0, ⟨t0, m0, Nat.lt_of_lt_of_le h0 ht, by rw [he.get t0 h0]; exact hm0, hl0, rfl, fun t' m' h1 h2 hm' => ?_⟩,
    hv0⟩
  rcases Nat.lt_or_ge t' mem.size with h3 | h3
  · rw [he.get t' h3] at hm'
    intro hl'
    exact absurd (Nat.lt_of_lt_of_le h1 (hfz t' m' hm' hl')) (Nat.lt_irrefl _)
  · exact hfirst t' m' h3 h2 hm'

end mem

/-! ### The witness extension (item 2) -/

/-- What a witness keeps across a move by `j` (`none`: a stutter): the store typing only grows, every other
existing thread's frame bound and debits are unchanged (`N`: the thread count before the move). -/
def WitExt (N j : Nat) (Eg Eg' : TermCut.GEnv) (Tot Tot' : Nat → TermSound.Res) (db db' : Nat → WeakMem.Ts → TermSound.Res) :
    Prop :=
  (∀ l cl, Eg.sto l = some cl → Eg'.sto l = some cl) ∧ (∀ l, Eg.ini l ≤ Eg'.ini l) ∧
    ∀ i, i ≠ j → i < N → Tot' i = Tot i ∧ db' i = db i

section ext
open CoreTyping TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermSpawn
open WeakMem (Msg Memory VState Ts AllocLabel)

/-- The store typing only grows, and `ini` only grows. -/
def StoIniExt (Eg Eg' : GEnv) : Prop :=
  (∀ l cl, Eg.sto l = some cl → Eg'.sto l = some cl) ∧ ∀ l, Eg.ini l ≤ Eg'.ini l

theorem StoIniExt.refl (Eg : GEnv) : StoIniExt Eg Eg := ⟨fun _ _ h => h, fun _ => Nat.le_refl _⟩

theorem StoIniExt.trans {E1 E2 E3 : GEnv} (a : StoIniExt E1 E2) (b : StoIniExt E2 E3) : StoIniExt E1 E3 :=
  ⟨fun l cl h => b.1 l cl (a.1 l cl h), fun l => Nat.le_trans (a.2 l) (b.2 l)⟩

/-- New messages of a thread step that land at a typed label land in the stepper's cut. -/
def CutNew (c c' : Cfg) (j : Nat) (Eg : GEnv) : Prop :=
  ∀ (t : Nat) (m : Msg) (th' : TTh), c'.ths[j]? = some th' → t ∉ th'.promises → c.mem[t]? = none →
    c'.mem[t]? = some m → ∀ cl, Eg.sto m.loc.label = some cl → Eg.InCut j m.loc.label

variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}

/-- **The extern arm with the witness frame**: `TermExtMid.sysInvN_extStepW`, with its frame packaged as
`StoIniExt`. -/
theorem extStepW {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {MintOK : Res → Prop}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hX : Ext p k arch c c') :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' ∧
        StoIniExt Eg Eg' ∧ ∀ j, j < c.ths.size → Tot' j = Tot j ∧ db' j = db j :=
  let ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, hs, hi, hf⟩ := TermExtMid.sysInvN_extStepW hN hOL hObs hX
  ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, ⟨hs, hi⟩, hf⟩

/-- **The spawn arm with the witness frame**: `TermSpawnMid.sysInvN_spawnStepW` (its kid-entry premise from
`spawnTy_of_sysInvN`), with its frame packaged as `StoIniExt`. -/
theorem spawnStepW {cap : Nat} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {MintOK : Res → Prop}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hS : TermSpawnStep.Spawn p k arch cap c c') (hc : c.cap = cap) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' ∧
        StoIniExt Eg Eg' ∧ ∀ j, j < c.ths.size → Tot' j = Tot j ∧ db' j = db j :=
  let ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, hs, hi, hf⟩ :=
    TermSpawnMid.sysInvN_spawnStepW hN hOL hObs hS hc (TermSpawnMid.spawnTy_of_sysInvN hN)
  ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, ⟨hs, hi⟩, hf⟩

/-- The setting's obligations (the EM0 form: `Sp := Spawn ∨ Ext`). -/
theorem obl_of_setting {c₀ : Cfg} (S : Setting p k arch Init c₀) :
    Obligations p k arch (fun c c' => Spawn p k arch c₀.cap c c' ∨ Ext p k arch c c') Init (fun _ => True) c₀
      TermPlantF.plantOf TermPlantF.plantN :=
  S.obl.toObligationsCX S.sdr (A9SpawnFinal.spArms_of S.obl ExtArmZ.spLeafArms_em0 S.start)

/-- **The thread arm with the witness frame**, plus `CutNew` (a new message at a typed label is in the stepper's cut,
from `TOut`'s `WrLocA2`). -/
theorem threadStepW {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    {j : Nat} (hc' : c' ∈ threadSteps p k arch c j) (hcert : Certified p k arch c' j) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' ∧
        WitExt c.ths.size j Eg Eg' Tot Tot' db db' ∧ CutNew c c' j Eg := by
  have O := obl_of_setting S
  obtain ⟨pl, hPI⟩ := TermPoolThread.poolInv_of hN.pool
  obtain ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hX, ⟨hE1, hC⟩, hW⟩ :=
    sysInvO_threadRW O (TermMain.poolStaging_of O) (TermFgnNew.fgnNew_of O.scope) hrun hN hc' hcert hPI hOL hObs
      (fun Eg' => StoIniExt Eg Eg' ∧ CutNew c c' j Eg)
      (fun th r S0 ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPub hPfrP hS hF0 => by
        have hfr : ∀ l, FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc l → Eg.sto l = none := by
          intro l hf
          obtain ⟨q, hq1, -, hq⟩ := hf
          have h2 : Eg.sto (freshLabel c.lbase c.n j q) = none := (X.inv.fresh j th X.hth q hq1).1
          have h3 : l = freshLabel c.lbase c.n j q := hq
          rw [h3]; exact h2
        refine ⟨⟨fun l cl hl => ?_, fun l => ?_⟩, ?_⟩
        · simp only [EgT, GEnv.withFp, GEnv.post]
          split
          · rename_i hf; rw [hfr l hf] at hl; cases hl
          · exact hl
        · show Eg.ini l ≤ E'.ini l
          exact (hF0.2.2.2.2.1 l).1
        · intro t m th' hth' htp hnone hsome cl hcl
          obtain ⟨-, -, -, -, -, -, -, -, -, -, Fd, -, -, -, hWL, -⟩ := Z
          rw [X.e3] at hth'
          cases hth'
          have hsome' : (stOf r.1 r.2.1 r.2.2).mem[t]? = some m := by
            show r.1[t]? = some m
            rw [← X.e1]; exact hsome
          rcases hWL (CE η) t m htp hsome' with ⟨-, h1⟩ | hf | ⟨c1, h1, -⟩ | ⟨c1, n1, h1, -⟩
          · have h2 : c.mem[t]? = some m := h1
            rw [hnone] at h2; cases h2
          · rw [hfr _ hf] at hcl; cases hcl
          · rw [Y.1, Cut_sto] at h1
            exact ⟨c1, (cutSto_some.1 h1).1, (cutSto_some.1 h1).2⟩
          · rw [Y.1, Cut_sto] at h1
            exact ⟨c1, (cutSto_some.1 h1).1, (cutSto_some.1 h1).2⟩)
  exact ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hX, ⟨hE1.1, hE1.2, hW⟩, hC⟩

/-- **The promise arm with the witness frame.** -/
theorem promStepW {c₀ c : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hj : j < c.ths.size) (hw : w < c.mem.size) (hcert : Certified p k arch (promise c j a v w) j) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) (promise c j a v w) Eg' Tot' HP' HS' cr' db' ∧
        OwnLive Eg' (promise c j a v w) ∧ ObsAll Eg' (promise c j a v w) ∧
        WitExt c.ths.size j Eg Eg' Tot Tot' db db' := by
  have O := obl_of_setting S
  obtain ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hX, hE1, hW⟩ :=
    sysInvO_promW O (TermMain.poolStaging_of O) hrun hN hj hw hcert hOL hObs (StoIniExt Eg)
      (fun _ _ _ => ⟨fun _ _ h => h, fun l => plantG_ini_le _ _ _ l⟩)
  exact ⟨Eg', Tot', HP', HS', cr', db', hSys, hO, hX, ⟨hE1.1, hE1.2, hW⟩⟩

end ext

/-- (D4) An extern thread move is an `Ext` step. -/
theorem extBy_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : TermProgress.ExtBy p k arch c i c') : Ext p k arch c c' := by
  obtain ⟨x, n, a, e, th, rt, ws, rs, h1, h2, h3, -, h4, h5, h6, rfl⟩ := h
  exact .mk i x n a e th rt ws rs h1 h2 h3 h4 h5 h6

/-- (D4) An environment move (a spurious wake) is an `Ext` step (O5, `TermPermit.park_site_step`). -/
theorem env_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : mstepE p k arch c (i, .env) c') : Ext p k arch c c' := by
  obtain ⟨x, a, e, th, rt, ws, h1, h2, -, h4, h5, rfl⟩ := h
  have hx := TermPermit.park_site_step p k arch h1 h2 h4 h5
  rw [wake_of_ne _ _ _ _ (by decide)] at hx
  exact hx

theorem sysInvO_mstepE_ext {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c₀ c c' : Cfg}
    (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c) (hcap : c.cap = c₀.cap)
    {Eg : TermCut.GEnv} {Tot HP : Nat → TermSound.Res} {HS : TermSound.Res}
    {cr db : Nat → WeakMem.Ts → TermSound.Res}
    (hN : TermMain.SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    (hOL : TermSpawn.OwnLive Eg c) (hObs : TermSpawn.ObsAll Eg c) {l : Nat × Lbl} (hs : mstepE p k arch c l c') :
    ∃ Eg' Tot' HP' HS' cr' db', TermMain.SysInvN p k arch Init (fun _ => True) c' Eg' Tot' HP' HS' cr' db' ∧
      TermSpawn.OwnLive Eg' c' ∧ TermSpawn.ObsAll Eg' c' ∧ WitExt c.ths.size l.1 Eg Eg' Tot Tot' db db' := by
  -- (`hcap` is not needed: a spawn's capacity is the configuration's own, `SpawnBy c.cap`.)
  have _hc : c.cap = c₀.cap := hcap
  obtain ⟨j, bb⟩ := l
  cases bb with
  | thr =>
    rcases hs with ⟨hc', hcert⟩ | hsp | hx
    · obtain ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, h4, -⟩ := threadStepW S hrun hN hOL hObs hc' hcert
      exact ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, h4⟩
    · obtain ⟨x, f, a, T, ts, e, th, rt, ws, h1, h2, h3, h4, h5, rfl⟩ := hsp
      obtain ⟨Eg', Tot', HP', HS', cr', db', g1, g2, g3, g4, g5⟩ :=
        spawnStepW hN hOL hObs (.mk j x f a T ts e th rt ws h1 h2 h3 h4 h5) rfl
      exact ⟨Eg', Tot', HP', HS', cr', db', g1, g2, g3, g4.1, g4.2, fun i _ hi => g5 i hi⟩
    · obtain ⟨Eg', Tot', HP', HS', cr', db', g1, g2, g3, g4, g5⟩ := extStepW hN hOL hObs (extBy_ext hx)
      exact ⟨Eg', Tot', HP', HS', cr', db', g1, g2, g3, g4.1, g4.2, fun i _ hi => g5 i hi⟩
  | prom =>
    obtain ⟨a, v, w, hj, hw, hcert, rfl⟩ := hs
    exact promStepW S hrun hN hOL hObs hj hw hcert
  | env =>
    obtain ⟨Eg', Tot', HP', HS', cr', db', g1, g2, g3, g4, g5⟩ := extStepW hN hOL hObs (env_ext hs)
    exact ⟨Eg', Tot', HP', HS', cr', db', g1, g2, g3, g4.1, g4.2, fun i _ hi => g5 i hi⟩

/-! ### The held core -/

section core
open CoreTyping TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain TermSpawn
open WeakMem (Msg Memory VState Ts AllocLabel)

variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}

/-- `HeldBy` at a fixed latest value `v`, without the `Debt` clause (implied on a promise-free suffix). -/
def HeldAt (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (c : Cfg) (b : Address) (n : Nat)
    (P : Proto) (h : Nat) (v : WeakMem.Val) : Prop :=
  ∃ Eg Tot HP HS cr db, SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
    OwnLive Eg c ∧ ObsAll Eg c ∧
    WordAtG Eg b n P ∧ (∀ cl, Eg.sto b.label = some cl → IniAt Eg.ini cl b (.word (.lit n) P)) ∧
    pwf P = true ∧ Latest c b v ∧ TermLiveHeld.HeldV P v ∧ h < c.ths.size ∧ 1 ≤ Tot h (.rg n)

/-- A promise step leaves an outstanding promise. -/
theorem promise_not_allNoProm {c : Cfg} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} (hj : j < c.ths.size) :
    ¬ AllNoProm (promise c j a v w) := by
  intro hA
  obtain ⟨th, hth⟩ : ∃ th, c.ths[j]? = some th := ⟨c.ths[j], Array.getElem?_eq_getElem hj⟩
  obtain ⟨-, hpj, -⟩ := promise_inv (a := a) (v := v) (w := w) hth
  have := hA j _ hpj
  simp at this

/-- **A machine step with the witness frame** (between promise-free configurations): the new witness, the frame
`WitExt`, the thread count only grows, and either memory is unchanged (spawn, extern) or the step is a certified
thread step with `CutNew`. -/
theorem mstep_wit {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hA' : AllNoProm c') {l : Nat × Lbl} (hs : mstepE p k arch c l c') :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' ∧
      WitExt c.ths.size l.1 Eg Eg' Tot Tot' db db' ∧ c.ths.size ≤ c'.ths.size ∧
      (c'.mem = c.mem ∨ (c' ∈ threadSteps p k arch c l.1 ∧ Certified p k arch c' l.1 ∧ CutNew c c' l.1 Eg)) := by
  obtain ⟨j, bb⟩ := l
  cases bb with
  | thr =>
    rcases hs with ⟨hc', hcert⟩ | hsp | hx
    · obtain ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, h4, h5⟩ := threadStepW S hrun hN hOL hObs hc' hcert
      exact ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, h4, Nat.le_of_eq (TermStep.threadSteps_size hc').symm,
        .inr ⟨hc', hcert, h5⟩⟩
    · obtain ⟨x, f, a, T, ts, e, th, rt, ws, g1, g2, g3, g4, g5, rfl⟩ := hsp
      obtain ⟨Eg', Tot', HP', HS', cr', db', k1, k2, k3, k4, k5⟩ :=
        spawnStepW hN hOL hObs (.mk j x f a T ts e th rt ws g1 g2 g3 g4 g5) rfl
      exact ⟨Eg', Tot', HP', HS', cr', db', k1, k2, k3, ⟨k4.1, k4.2, fun i _ hi => k5 i hi⟩,
        by show c.ths.size ≤ (spawnT c j _ _).ths.size; rw [TermSpawnMid.spawnT_size]; omega, .inl rfl⟩
    · have hX : Ext p k arch c c' := extBy_ext hx
      obtain ⟨Eg', Tot', HP', HS', cr', db', k1, k2, k3, k4, k5⟩ := extStepW hN hOL hObs hX
      have hfr := Ext.frame hX
      exact ⟨Eg', Tot', HP', HS', cr', db', k1, k2, k3, ⟨k4.1, k4.2, fun i _ hi => k5 i hi⟩,
        Nat.le_of_eq hfr.2.2.2.2.1.symm, .inl hfr.1⟩
  | prom =>
    obtain ⟨a, v', w, hj, -, -, rfl⟩ := hs
    exact absurd hA' (promise_not_allNoProm hj)
  | env =>
    have hX : Ext p k arch c c' := env_ext hs
    obtain ⟨Eg', Tot', HP', HS', cr', db', k1, k2, k3, k4, k5⟩ := extStepW hN hOL hObs hX
    have hfr := Ext.frame hX
    exact ⟨Eg', Tot', HP', HS', cr', db', k1, k2, k3, ⟨k4.1, k4.2, fun i _ hi => k5 i hi⟩,
      Nat.le_of_eq hfr.2.2.2.2.1.symm, .inl hfr.1⟩

/-- The witness frame keeps a typed, initialised unit at `b` (its cell and its `IniAt`) and the token count of a
thread other than the stepper. -/
theorem wit_keep {N j h : Nat} {Eg Eg' : GEnv} {Tot Tot' : Nat → Res} {db db' : Nat → Ts → Res}
    (hX : WitExt N j Eg Eg' Tot Tot' db db') {b : Address} {U : Ty} {cl : Cell} (hcl : Eg.sto b.label = some cl)
    (hI : ∀ cl, Eg.sto b.label = some cl → IniAt Eg.ini cl b U) (hjh : j ≠ h) (hh : h < N) :
    Eg'.sto b.label = some cl ∧ (∀ cl2, Eg'.sto b.label = some cl2 → IniAt Eg'.ini cl2 b U) ∧ Tot' h = Tot h := by
  have hcl' := hX.1 _ _ hcl
  refine ⟨hcl', fun cl2 hc2 => ?_, (hX.2.2 h (Ne.symm hjh) hh).1⟩
  rw [hcl'] at hc2; cases hc2
  exact IniAt_mono hX.2.1 (hI cl hcl)

/-- **A certified thread step, seen from a typed label `b.label`**: either memory is unchanged (a frame step), or
the step is `r ∈ tstep …` of thread `j` with its typing at its cut `CE η` (resources, scope, memory's held part),
`η`'s store is a part of the global one with the same `ini`, and every new message at `b.label` lies in the cut. -/
theorem thread_new_env {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    {b : Address} {cl : Cell} (hcl : Eg.sto b.label = some cl) (hA' : AllNoProm c')
    {j : Nat} (hc' : c' ∈ threadSteps p k arch c j) (hcert : Certified p k arch c' j)
    (hCN : CutNew c c' j Eg) :
    c'.mem = c.mem ∨ ∃ (th : TTh) (r : Memory × List Ts × TTh) (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs : Res),
      r ∈ tstep (gOf p k arch c j) c.mem c.pairs th ∧ c'.mem = r.1 ∧ j < c.ths.size ∧ Rf + Rs = Tot j ∧
      TypedK p η cx th.term ∧ FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ EnvOK p η ∧ TvOK cx ∧
      MemInv (gOf p k arch c j) (CE η) (stOf c.mem c.pairs th) ∧ StepScope cx th.term ∧
      MemHeld (CE η) (stOf c.mem c.pairs th) (HP j + HS) ∧ η.ini = Eg.ini ∧
      (∀ c1, (CE η).sto b.label = some c1 → Eg.sto b.label = some c1) ∧
      ∀ t (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m → m.loc.label = b.label → (CE η).sto b.label = some cl := by
  have O := obl_of_setting S
  obtain ⟨th, r, hth, hr, e1, e2, e3, ho⟩ := TermStepper.threadSteps_upd hc'
  have hj : j < c.ths.size := by
    rcases Nat.lt_or_ge j c.ths.size with h1 | h1
    · exact h1
    · simp [h1] at hth
  obtain ⟨S0, hS⟩ := hN.thr j th hth
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hFI, hsum, -, hm, hH, -, -⟩ := ThSysAt.env hN.clo hS
  have X : TCtxX p k arch (fun c c' => Spawn p k arch c₀.cap c c' ∨ Ext p k arch c c') Init (fun _ => True) c₀ c c'
      Eg Tot HP HS cr db j th r := ⟨hrun, hN, hth, hr, hc', e1, e2, e3, ho, hcert⟩
  have Y : EnvAt p Eg j th (Tot j) S0 ρ η cx Rf Rs := ⟨hCE, htid, hE, hT, htv, hFI, hsum⟩
  rcases O.scope X Y with hsc | hR
  · have hini' : η.ini = Eg.ini := congrArg TEnv.ini hCE
    refine .inr ⟨th, r, ρ, η, cx, Rf, Rs, hr, e1, hj, hsum, hT, hFI, hE, htv, hm, hsc, hH, hini', fun c1 hc1 => ?_,
      fun t m ht hm0 hlab => ?_⟩
    · rw [hCE, Cut_sto] at hc1
      exact cutSto_sub hc1
    · have hnone : c.mem[t]? = none := Array.getElem?_eq_none ht
      have hnp' : ∀ th', c'.ths[j]? = some th' → t ∉ th'.promises := fun th' h1 => by
        rw [hA' j th' h1]; simp
      have hcut : Eg.InCut j b.label := by
        rw [e3] at hnp'
        have := hCN t m r.2.2 e3 (hnp' _ rfl) hnone hm0 cl (by rw [hlab]; exact hcl)
        rw [hlab] at this; exact this
      obtain ⟨cl', hcl', hown⟩ := hcut
      rw [hcl] at hcl'; cases hcl'
      rw [hCE, Cut_sto]
      exact cutSto_some.2 ⟨hcl, hown⟩
  · exact .inl (by rw [e1]; exact (frame_keep hR hT.1 hT.2 hFI hE htv hm r hr).1)

/-- A thread step by `j ≠ h` on a promise-free pair keeps `b`'s latest value: a new message at `b` would be a write
at a held word by a thread without the token. -/
theorem thread_latest_keep {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db)
    {b : Address} {n : Nat} {P : Proto} {h : Nat} {v : WeakMem.Val}
    (hW : WordAtG Eg b n P) (hI : ∀ cl, Eg.sto b.label = some cl → IniAt Eg.ini cl b (.word (.lit n) P))
    (hpwf : pwf P = true) (hL : Latest c b v) (hV : TermLiveHeld.HeldV P v) (hh : h < c.ths.size)
    (hT1 : 1 ≤ Tot h (.rg n)) (hA : AllNoProm c) (hA' : AllNoProm c')
    {j : Nat} (hjh : j ≠ h) (hc' : c' ∈ threadSteps p k arch c j) (hcert : Certified p k arch c' j)
    (hCN : CutNew c c' j Eg) :
    Latest c' b v := by
  have hext : Promises.Sim.MemExt c.mem c'.mem := TermLiveProps.threadSteps_ext hc'
  obtain ⟨cl, hcl, hat, hg⟩ := hW
  show Promises.LatestIs c'.mem b v
  rcases thread_new_env S hrun hN hcl hA' hc' hcert hCN with hmem | ⟨th, r, ρ, η, cx, Rf, Rs, hr, e1, hj, hsum, hT, hFI,
      hE, htv, hm, hsc, hH, hini', hsub, hcut⟩
  · rw [hmem]; exact hL
  · refine latest_ext_noNew hext (fun t m ht hm0 hl => ?_) hL
    -- the first new message at `b`
    obtain ⟨t1, ⟨m1, ht1, hm1, hl1⟩, hmin⟩ := exists_first (P := fun t => ∃ m : Msg, c.mem.size ≤ t ∧
      c'.mem[t]? = some m ∧ m.loc = b) ⟨m, ht, hm0, hl⟩
    have hfirst : ∀ t' (m' : Msg), c.mem.size ≤ t' → t' < t1 → c'.mem[t']? = some m' → m'.loc ≠ b :=
      fun t' m' h1 h2 h3 h4 => hmin t' h2 ⟨m', h1, h3, h4⟩
    obtain ⟨wd, hpre, hwv⟩ := pred_of_first hext hL hfirst ht1
    have hw : WordAt (CE η) m1.loc n P := by
      rw [hl1]
      exact ⟨cl, hcut t1 m1 ht1 hm1 (by rw [hl1]), hat, hg⟩
    have hini : TermLiveHeld.IniU η m1.loc n P := by
      intro c1 hc1
      rw [hl1] at hc1 ⊢
      rw [hini']
      exact hI c1 (hsub c1 hc1)
    have hn : TermLiveHeld.NewAt c.mem r.1 t1 m1 := ⟨Array.getElem?_eq_none ht1, by rw [← e1]; exact hm1⟩
    have hpre' : PredAt r.1 m1.loc t1 wd := by rw [hl1, ← e1]; exact hpre
    have hheld : TermLiveHeld.HeldV P wd.val := by rw [hwv]; exact hV
    have W := hN.toW hA
    exact hjh (TermLiveHeld.held_word_changes_only_by_holder_sum_noFoot (W.tokSum_thread hj n) hh hj hT1 hsum
      hT.1 hT.2 hFI hE htv hm hsc hH hr hn hw (W.hwd hj hsum n) hini hpwf hpre' hheld)

/-- **One step of the held invariant** (a move by `j ≠ h` between promise-free configurations). -/
theorem heldAt_step {c₀ c c' : Cfg} (S : Setting p k arch Init c₀) (hrun : StepsE p k arch c₀.cap c₀ c)
    {b : Address} {n : Nat} {P : Proto} {h : Nat} {v : WeakMem.Val}
    (hH : HeldAt p k arch Init c b n P h v) (hA : AllNoProm c) (hA' : AllNoProm c') {l : Nat × Lbl}
    (hlh : l.1 ≠ h) (hs : mstepE p k arch c l c') : HeldAt p k arch Init c' b n P h v := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, ⟨cl, hcl, hat, hg⟩, hI, hpwf, hL, hV, hh, hT1⟩ := hH
  obtain ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, hX, hsz, hmem⟩ := mstep_wit S hrun hN hOL hObs hA' hs
  obtain ⟨hcl', hI', hT'⟩ := wit_keep hX hcl hI hlh hh
  refine ⟨Eg', Tot', HP', HS', cr', db', h1, h2, h3, ⟨cl, hcl', hat, hg⟩, hI', hpwf, ?_, hV,
    Nat.lt_of_lt_of_le hh hsz, by rw [hT']; exact hT1⟩
  rcases hmem with hm | ⟨hc', hcert, hCN⟩
  · show Promises.LatestIs c'.mem b v
    rw [hm]; exact hL
  · exact thread_latest_keep S hrun hN ⟨cl, hcl, hat, hg⟩ hI hpwf hL hV hh hT1 hA hA' hlh hc' hcert hCN

/-- **Run induction on a promise-free suffix past `h`'s crash point**: an invariant kept by every machine step of a
thread other than `h` between promise-free configurations holds from `n₀` on. -/
theorem suffix_induct {c₀ : Cfg} {r : LRun (machineE p k arch).L} {D : Nat → Option Nat}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) (hD : CrashOK (machineE p k arch) r D)
    {h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀) (hpf : PromFreeFrom r n₀) (I : Cfg → Prop)
    (hI0 : I (r.cfg n₀))
    (hstep : ∀ (c c' : Cfg) (l : Nat × Lbl), StepsE p k arch c₀.cap c₀ c → I c → AllNoProm c → AllNoProm c' →
      l.1 ≠ h → mstepE p k arch c l c' → I c') :
    ∀ m', n₀ ≤ m' → I (r.cfg m') := by
  have step : ∀ d, I (r.cfg (n₀ + d)) := by
    intro d
    induction d with
    | zero => exact hI0
    | succ d ih =>
      have hmv := hr (n₀ + d)
      have hreach := machineE_run_stepsE hr (n₀ + d)
      rw [h0] at hreach
      cases hl : r.lbl (n₀ + d) with
      | none =>
        rw [hl] at hmv
        have he : r.cfg (n₀ + d + 1) = r.cfg (n₀ + d) := hmv
        rw [← Nat.add_assoc, he]; exact ih
      | some l =>
        rw [hl] at hmv
        have hmv' : mstepE p k arch (r.cfg (n₀ + d)) l (r.cfg (n₀ + d + 1)) := hmv
        have hlh : l.1 ≠ h := fun e => (hD h m hm).2 (n₀ + d) (by omega) ⟨l, hl, by rw [← e]; rfl⟩
        rw [← Nat.add_assoc]
        exact hstep _ _ l hreach.1 ih (hpf _ (Nat.le_add_right _ _)) (hpf _ (by omega)) hlh hmv'
  intro m' hm'
  obtain ⟨d, rfl⟩ : ∃ d, m' = n₀ + d := ⟨m' - n₀, by omega⟩
  exact step d

end core

/-- The core: the latest value of `b` is constant from `n₀` on. -/
theorem held_latest_const {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : TermSound.Res} {c₀ : Cfg}
    (S : Setting p k arch Init c₀) {r : LRun (machineE p k arch).L} {D : Nat → Option Nat}
    (hr : (machineE p k arch).Run r) (h0 : r.cfg 0 = c₀) (hD : CrashOK (machineE p k arch) r D)
    {b : Address} {n : Nat} {P : Proto} {h m n₀ : Nat} (hm : D h = some m) (hmn : m ≤ n₀)
    (hH : HeldBy p k arch Init (r.cfg n₀) b n P h) (hpf : PromFreeFrom r n₀) :
    ∃ v, ∀ m', n₀ ≤ m' → Latest (r.cfg m') b v := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, hW, hI, hpwf, ⟨v, hL, hV⟩, hh, hT1, -⟩ := hH
  have base : HeldAt p k arch Init (r.cfg n₀) b n P h v := ⟨Eg, Tot, HP, HS, cr, db, hN, hOL, hObs, hW, hI, hpwf, hL, hV, hh, hT1⟩
  have hall := suffix_induct hr h0 hD hm hmn hpf (fun c => HeldAt p k arch Init c b n P h v) base
    (fun _ _ _ hrun hH hA hA' hlh hs => heldAt_step S hrun hH hA hA' hlh hs)
  refine ⟨v, fun m' hm' => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hL', -⟩ := hall m' hm'
  exact hL'

theorem forced_wait_held_thm (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : TermSound.Res) :
    forced_wait_held (machineE p k arch) (Setting p k arch Init) (HeldBy p k arch Init) := by
  intro c₀ S r D i b n P h m n₀ hr h0 hD hm hmn hH hpf hs ht
  obtain ⟨v, hv⟩ := held_latest_const S hr h0 hD hm hmn hH hpf
  exact ⟨⟨n₀, v, hv⟩, hs, ht⟩

end TermLiveC

#print axioms TermLiveC.debt_zero_of_allNoProm
#print axioms TermLiveC.sysInvO_mstepE_ext
#print axioms TermLiveC.held_latest_const
#print axioms TermLiveC.mstep_wit
#print axioms TermLiveC.wit_keep
#print axioms TermLiveC.thread_new_env
#print axioms TermLiveC.suffix_induct
#print axioms TermLiveC.forced_wait_held_thm

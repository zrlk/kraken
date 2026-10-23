import WeakCore.TermMain

/-! # TermInitOKOld (RetPw): the pre-RetPw `InitOK` (`InitOKOld`, through the pre-RetPw
`ResumeR`/`ThInvRE`, verbatim from the earlier version) implies the RetPw `InitOK` at configurations whose
threads all have empty stacks (every `TermInit.InitShape` start). -/

namespace TermMain
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Pre-RetPw `ResumeR`. -/
def ResumeROld (p : Prog) : List Frame → Res → TEnv → Nat → List Word → Res → Prop
  | [], Rs, _, _, _, _ => Rs = .zero
  | f :: rest, Rs, E, rd, ws, R => ∃ Rc Rrest, Rs = Rc + Rrest ∧ ∃ ρ η c, CE η = E ∧ η.rid = rd ∧
      EnvOK p η ∧ TypedK p η c f.body ∧ TvOK c ∧
      FInvR ρ η f.σs (ResumeROld p rest Rrest) c ((f.x, f.ty, ws) :: f.env) (Rc + R)

/-- Pre-RetPw `ThInvRE`. -/
def ThInvREOld (p : Prog) (E : TEnv) (th : TTh) (Tot : Res) : Prop :=
  ∃ ρ η cx Rf Rs, CE η = E ∧ EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
    FInvR ρ η th.σs (ResumeROld p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot

/-- Pre-RetPw `ThSys`. -/
def ThSysOld (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (Eg : GEnv)
    (Tot HP HS : Res) (cr db : Ts → Res) : Prop :=
  ∃ S, ThInvREOld p (Cut Eg g.i S) th Tot ∧ ThInvE p (Cut Eg g.i S) th ∧
    MemInv g (Cut Eg g.i S) (stOf mem pairs th) ∧
    MemHeldP (Cut Eg g.i S) (stOf mem pairs th) HP ∧ MemHeldS (Cut Eg g.i S) (stOf mem pairs th) HS ∧
    TermPlant.PromCrK (Cut Eg g.i S) (stOf mem pairs th) cr db

structure SysInvWOld (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop)
    (c : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) : Prop where
  thr : ∀ i th, c.ths[i]? = some th →
    ThSysOld p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i)
  held : MemHeldG Eg c HS
  clo : GStoClo Eg
  /-- (GStoMg) cell types have guarded `μ` bodies. -/
  cmg : GStoMg Eg
  shty : SharedTyOK Eg
  proms : PromsOK Eg c
  /-- (S8b A1) Every thread's foreign promises meet `FpOK` at its cut (any
  `seen`: `FpOK` reads only `sto`, `tid`, `pfr` and `fp`). -/
  fpok : ∀ i th (S : AllocLabel → Prop), c.ths[i]? = some th → FpOK (Cut Eg i S) (stOf c.mem c.pairs th)
  /-- (S8b) Every thread's labels yet to allocate are globally fresh. -/
  fresh : ∀ i th, c.ths[i]? = some th → ∀ j, th.nalloc ≤ j →
    GFreshL Eg c th (freshLabel c.lbase c.n i j)
  bal : ∃ M, MintOK M ∧
    thSum c.ths.size (fun i => Tot i + pSumAt c i (cr i) + HP i) + HS ≤
      Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))
  tok : ∀ n, KeySum c.ths.size (fun i => Tot i + HP i) HS (.rg n)
  wd : ∀ n, KeySum c.ths.size (fun i => Tot i + HP i) HS (.wd n)
  /-- (F2′) At most one own-handle key `own l` system-wide (as `wd`). -/
  own : ∀ l, KeySum c.ths.size (fun i => Tot i + HP i) HS (.own l)
  /-- (S8b) The box fence is on: a box's frontier reaches its creator's
  `vRelSt` before the reference escapes. -/
  bf : c.boxFence = true
  /-- (S8b) Every box's words are latest below its frontier (`BoxTopG`). -/
  boxtop : BoxTopG Eg c
  /-- (S8b) Distinct threads' promises are disjoint. -/
  disj : PromsDisj c
  /-- (S8b) No thread's foreign promises are its own. -/
  fpfree : FpOwnFree Eg c
  /-- (S8b) Every promise is a message. -/
  plt : AllPromLt c
  /-- (S8b) Every thread's `vWr` is at most the memory size. -/
  vwr : VWrLe c
  /-- (S8b) Every cell's frontier is at most the memory size. -/
  frle : FrontierLe Eg c.mem.size
  /-- (F2′ step 3, RiniLe) Every label's real-count bound `rini` is at most
  its reader-visible count `ini` (a plant raises only `ini`). -/
  rle : ∀ l, Eg.rini l ≤ Eg.ini l
  /-- (U3) Box payloads name allocated labels (`GBoxNamed`);
  thread-step preservation open. -/
  bnamed : GBoxNamed Eg

/-- Pre-RetPw `InitOK`. -/
def InitOKOld (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  (∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvWOld p k arch Init MintOK c0 Eg Tot HP HS cr db ∧ (∃ rc, RidOK c0 Tot HP HS cr db rc) ∧
      OwnFreshZ c0 Tot HP HS cr ∧ TermUndefZ.UndefAtG Eg c0.mem ∧
      (∀ i th (S : AllocLabel → Prop), c0.ths[i]? = some th →
        TermOwnCohZ.OwnCohZ (Cut Eg i S) (stOf c0.mem c0.pairs th)) ∧ (∀ l, Eg.box l = none) ∧ (∀ l, Eg.pfr l = none) ∧
      OwnKeyOwnG c0 Eg Tot ∧ OwnPubG c0 Eg Tot HP HS ∧ StoNI Eg ∧
      (∀ l cl, Eg.sto l = some cl → TermA4.wrapTop cl.ty = true) ∧ TermPtrRts.LblSto Eg c0 ∧ (∀ l cl, Eg.sto l = some cl → TermSound.LayT cl.ty) ∧ c0.mem = #[] ∧
      TermViewInv.ViewInv c0 ∧
      ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.vs.vWr ≤ c0.mem.size - 1) ∧ AllNoProm c0 ∧
    TermLiveProps.CfgCoh c0

/-- At an empty stack the pre-RetPw and RetPw return continuations agree. -/
theorem resumeROld_nil (p : Prog) (Rs : Res) : ResumeROld p [] Rs = ResumeR p [] Rs := by
  funext E rd ws R; rfl

/-- The pre-RetPw `ThSys` gives the RetPw one at a thread with an empty stack. -/
theorem thSys_of_old {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
    {Tot HP HS : Res} {cr db : Ts → Res} (hst : th.stack = [])
    (h : ThSysOld p g mem pairs th Eg Tot HP HS cr db) : ThSys p g mem pairs th Eg Tot HP HS cr db := by
  obtain ⟨S, ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hFI, hsum⟩, hrest⟩ := h
  rw [hst, resumeROld_nil] at hFI
  exact ⟨S, ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, by rw [hst]; exact hFI, hsum,
    fun _ _ h => by rw [hst] at h; cases h⟩, hrest⟩

/-- The pre-RetPw `SysInvW` gives the RetPw one when every thread's stack is empty. -/
theorem sysInvW_of_old {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hst : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.stack = []) (hn : c.n ≤ c.ths.size)
    (h : SysInvWOld p k arch Init MintOK c Eg Tot HP HS cr db) : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db :=
  ⟨fun i th hth => thSys_of_old (hst i th hth) (h.thr i th hth), h.held, h.clo, h.cmg, h.shty, h.proms, h.fpok,
    h.fresh, h.bal, h.tok, h.wd, h.own, h.bf, h.boxtop, h.disj, h.fpfree, h.plt, h.vwr, h.frle, h.rle, h.bnamed,
    TermFreshU.freshU_le hn⟩

/-- **The pre-RetPw `InitOK` gives the RetPw `InitOK` at every configuration whose threads all have
empty stacks** (in particular every `TermInit.InitShape` configuration; there `initOK_of` proves
`InitOK` directly, unchanged). -/
theorem initOK_of_old {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hst : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.stack = []) (hn : c0.n ≤ c0.ths.size)
    (h : InitOKOld p k arch Init MintOK c0) (htd : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.tidLbl = none) : InitOK p k arch Init MintOK c0 := by
  obtain ⟨⟨Eg, Tot, HP, HS, cr, db, hW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩,
    hnp, hcoh⟩ := h
  exact ⟨⟨Eg, Tot, HP, HS, cr, db, sysInvW_of_old hst hn hW, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15, htd⟩, hnp, hcoh⟩

end TermMain

#print axioms TermMain.initOK_of_old

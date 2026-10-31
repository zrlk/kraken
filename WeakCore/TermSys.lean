import WeakCore.TermCut
import WeakCore.TermLiveHeld
import WeakCore.TermPlant

/-!
# S7h: the system invariant (`SysInv`), skeleton

The A-strict system invariant: one global ghost environment `E_g` (`GEnv`), thread `i`'s
environment its cut `Cut E_g i S_i` (`tid = i`, its own `seen`).  For each
thread the stage-A invariant with resources and credits at its cut
(`ThInvRE`, `MemInv`, `PromCr`), the plain stage-A invariant alongside (S7f
issue 4, option (i): `ThInvE` at the same cut), and memory's holding split into
the thread's private part `HP i` and the shared part `HS` (`MemHeldP`,
`MemHeldS`); globally the shared holding `MemHeldG E_g c HS`, closed cell types
(`GStoClo`), the shared-type condition (`SharedTyOK`: `noOR`), the ghost
foreign promises (`PromsOK`, S7i), the token balance (abstract initial
budget `Init` and mint predicate `MintOK`, fixed by S9/S10) and the per-key sum
bounds `machine_tokens`/`machine_words` read (`KeySum` at `rg n` and `wd n`).

Not here: `SysInv_step` (S8–S10), `SysInv_init` (S11).
-/

namespace TermSys

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Definitions -/

/-- (S7h, S7i) **The shared-type condition**: every shared cell's type has
only `pub` references (`noOR`), what moving a shared entry between a cut and
`PubE` needs (`MemHeldS_of_G`, `MemHeldG_of_S`).  It follows from any thread's
`PubCpl` (`noOR_of`); kept as a clause (S7i: `WuR`/`ResRigid` dropped, the
shared holding is chosen, not unique). -/
def SharedTyOK (Eg : GEnv) : Prop :=
  ∀ l cl, Eg.Shared l → Eg.sto l = some cl → noOR cl.ty = true

/-- (S8b) **Label `l` is fresh for thread `th` globally**: `E_g` has no
cell, box, initialised count or frontier there, and every message of memory at
`l` is one of `th`'s own outstanding promises (the global form of `FreshLP`;
only the thread itself allocates at its `freshLabel`s). -/
def GFreshL (Eg : GEnv) (c : Cfg) (th : TTh) (l : AllocLabel) : Prop :=
  Eg.sto l = none ∧ Eg.box l = none ∧ Eg.ini l = 0 ∧ Eg.pfr l = none ∧
    ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label = l → t ∈ th.promises

/-- (S8b) **The global box clause**: every word of every box of `E_g` is the
latest at its address at some timestamp at most the box's frontier, no message
there after it, and that timestamp no thread's promise.  Each thread's
`BoxTopP` follows (`BoxTopP_of_G`); its preservation is S8c's. -/
def BoxTopG (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ l B, Eg.box l = some B → BoxWords B fun o w =>
    ∃ t, t ≤ B.fr ∧ t ∉ allProms c ∧ LatestP c.mem [] (fun _ => t) ⟨l, o⟩ w

/-- (S8b) A thread's `BoxTopP` at its cut, skipping any promises of the
configuration, from `BoxTopG`. -/
theorem BoxTopP_of_G {Eg : GEnv} {c : Cfg} {i : Nat} {S : AllocLabel → Prop} {P : List Ts}
    (h : BoxTopG Eg c) (hP : ∀ t, t ∈ P → t ∈ allProms c) : BoxTopP (Cut Eg i S) c.mem P :=
  fun l B hB => (h l B hB).imp fun _ _ ⟨t, ht, hn, hm, _, hl⟩ =>
    ⟨t, ht, hm, fun hp => hn (hP _ hp), fun t' m h1 h2 h3 => absurd (hl t' m h1 h2 h3) (by simp)⟩

/-- (S8b) Distinct threads' outstanding promises are disjoint (a promise is a
new timestamp, `AllPromLt`). -/
def PromsDisj (c : Cfg) : Prop :=
  ∀ (i j : Nat) (thi thj : TTh) (t : Ts), i ≠ j → c.ths[i]? = some thi → c.ths[j]? = some thj → t ∈ thi.promises →
    t ∉ thj.promises

/-- (S8b) No thread's ghost foreign promises include one of its own. -/
def FpOwnFree (Eg : GEnv) (c : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh) (t : Ts), c.ths[i]? = some th → t ∈ Eg.fpOf i → t ∉ th.promises

/-- (S8b) Every thread's promises are messages (each thread's `PromLt`). -/
def AllPromLt (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh) (t : Ts), c.ths[i]? = some th → t ∈ th.promises → t < c.mem.size

/-- (S8b) Every thread's write view is at most the memory size: `vWr` is only
ever raised to an own write's timestamp or to an allocation's last message. -/
def VWrLe (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.vs.vWr ≤ c.mem.size

/-- (S8b) **The frontier bound**, at cells: every frontier of a cell of `E_g`
is at most `n` (at the configuration, the memory size).  A frontier is set
only at a publish, to the publisher's old `vWr` (`VWrLe`).  Box labels (no
cell) are not covered: `EFoot` leaves a new box's frontier unconstrained. -/
def FrontierLe (Eg : GEnv) (n : Nat) : Prop :=
  ∀ (l : AllocLabel) (cl : Cell) (f : Ts), Eg.sto l = some cl → Eg.pfr l = some f → f ≤ n

/-- (S7h) **Thread `g.i`'s part of `SysInv`**, at its cut of `E_g` with some
`seen` set `S`: the stage-A invariant with resources (frame total `Tot`), the
plain one alongside, memory's holding split into the private part `HP` and the
shared part `HS`, and the promise credits. -/
def ThSys (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (Eg : GEnv)
    (Tot HP HS : Res) (cr db : Ts → Res) : Prop :=
  ∃ S, ThInvRE p (Cut Eg g.i S) th Tot ∧ ThInvE p (Cut Eg g.i S) th ∧
    MemInv g (Cut Eg g.i S) (stOf mem pairs th) ∧
    MemHeldP (Cut Eg g.i S) (stOf mem pairs th) HP ∧ MemHeldS (Cut Eg g.i S) (stOf mem pairs th) HS ∧
    TermPlant.PromCrK (Cut Eg g.i S) (stOf mem pairs th) cr db

/-- `ThInvMC` with the system's credit invariant `PromCrK` (own credits
or key-free plant credits). -/
def ThInvMCK (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) (Tot H : Res)
    (cr db : Ts → Res) : Prop :=
  ∃ E, ThInvRE p E th Tot ∧ MemInv g E (stOf mem pairs th) ∧ MemHeld E (stOf mem pairs th) H ∧
    TermPlant.PromCrK E (stOf mem pairs th) cr db

/-- (S7h) Thread `i`'s total over its promises of `f` (nothing past the
threads). -/
def pSumAt (c : Cfg) (i : Nat) (f : Ts → Res) : Res :=
  match c.ths[i]? with
  | some th => pSum (stOf c.mem c.pairs th) f
  | none => .zero

/-- (2b) A fresh label: no cell, box, initialisation, plant, or message. -/
def FreshX (Eg : GEnv) (c : Cfg) (x : AllocLabel) : Prop :=
  Eg.sto x = none ∧ Eg.box x = none ∧ Eg.ini x = 0 ∧ Eg.pfr x = none ∧
    ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ x

/-- (2b) No thread (frames, private holdings, credits) and no shared holding has `x`'s own key. -/
def OwnZ (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr : Nat → Ts → Res) (x : AllocLabel) : Prop :=
  (∀ n, n < c.ths.size → (Tot n + HP n + pSumAt c n (cr n)) (.own x) = 0) ∧ HS (.own x) = 0

/-- (2b, freshU) The unborn stripes `[ths.size, N)` are fresh and unowned. -/
def FreshU (N : Nat) (Eg : GEnv) (c : Cfg) (Tot HP : Nat → Res) (HS : Res) (cr : Nat → Ts → Res) : Prop :=
  ∀ q j, c.ths.size ≤ q → q < N →
    FreshX Eg c (freshLabel c.lbase N q j) ∧ OwnZ c Tot HP HS cr (freshLabel c.lbase N q j)

/-- (S7h) A sum over the threads `0..N-1`. -/
def thSum (N : Nat) (f : Nat → Res) : Res := Res.sum ((List.range N).map f)

/-- (S7h) **The per-key sum bound** over `N` threads holding `T i` and the
shared holding `HS`: at most one `k` (`TermLiveHeld.TokSum` at `rg n`). -/
def KeySum (N : Nat) (T : Nat → Res) (HS : Res) (k : Key) : Prop :=
  ((List.range N).map (fun i => T i k)).sum + HS k ≤ 1

/-- (GStoMg) **Every cell type of `E_g` has guarded `μ` bodies** (`mg`).  Cells are created only
by allocation, at `cl ρ η.wit 0 0 t` (`new`, `t` a context type: `TvOK`) or an array of a
well-formed `τ` (`newBuf`); `mg_cl` with the witnesses' `WitAF.mg` gives `mg` there. -/
def GStoMg (Eg : GEnv) : Prop := ∀ l c, Eg.sto l = some c → mg c.ty = true

/-- Initially (no cells) `GStoMg` holds. -/
theorem GStoMg_empty : GStoMg {} := fun _ _ h => by cases h

/-- (GStoMg) A buffer cell's element type has guarded `μ` bodies. -/
theorem GStoMg.elem {Eg : GEnv} (h : GStoMg Eg) {l : AllocLabel} {c : Cell} {N : Idx} {e : Ty}
    (hc : Eg.sto l = some c) (ht : c.ty = .array N e) : mg e = true := by
  have := h l c hc; rw [ht] at this; simpa [mg] using this

#print axioms GStoMg_empty
#print axioms GStoMg.elem

/-- (S7h) **`SysInv` with its witnesses**: `E_g`, the frame totals `Tot i`,
private holdings `HP i`, the shared holding `HS`, the credits and debits
`cr i`/`db i`.  (S7i) Each thread's cut skips, at shared non-word units, its
own promises and `Eg.fpOf i`, together every promise (`PromsOK`).  The balance is stated against an abstract initial budget
`Init` and a mint `M` constrained by the abstract `MintOK` (S9: once-only);
the per-key bounds count each thread's frame and private holding and the
shared holding once. -/
structure SysInvW (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop)
    (c : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res) : Prop where
  thr : ∀ i th, c.ths[i]? = some th →
    ThSys p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i)
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
  /-- (2b, freshU) unborn stripes are fresh and unowned (`TermFreshU`); vacuous when `n ≤ ths.size`. -/
  freshU : FreshU c.n Eg c Tot HP HS cr

/-- **(S7h) The system invariant** (A-strict). -/
def SysInv (p : Prog) (k : Promises.Knobs) (arch : Arch) (Init : Res) (MintOK : Res → Prop) (c : Cfg) : Prop :=
  ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
    SysInvW p k arch Init MintOK c Eg Tot HP HS cr db

/-! ## Introduction and projections -/

theorem SysInv.intro {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) : SysInv p k arch Init MintOK c :=
  ⟨Eg, Tot, HP, HS, cr, db, h⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
  {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}

theorem SysInvW.thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) :
    ThSys p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) :=
  h.thr i th hth

theorem SysInvW.thread_lt (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    (hi : i < c.ths.size) :
    ThSys p (gOf p k arch c i) c.mem c.pairs c.ths[i] Eg (Tot i) (HP i) HS (cr i) (db i) :=
  h.thr i _ (Array.getElem?_eq_getElem hi)

end

/-! ## A thread's part: the stage-A forms at its cut -/

section
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv}
  {Tot HP HS : Res} {cr db : Ts → Res}

/-- (S7h) Memory's holding at the cut recomposes from its private and shared
parts (`MemHeld_join`, `Cut_cov`). -/
theorem ThSys.memHeld (h : ThSys p g mem pairs th Eg Tot HP HS cr db) :
    ∃ S, MemHeld (Cut Eg g.i S) (stOf mem pairs th) (HP + HS) := by
  obtain ⟨S, -, -, -, hP, hS, -⟩ := h
  exact ⟨S, MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hP hS⟩

/-- (S7h) **A thread's `ThInvMC`** at its cut, holding `HP + HS`. -/
theorem ThSys.thInvMC (h : ThSys p g mem pairs th Eg Tot HP HS cr db) :
    ThInvMCK p g mem pairs th Tot (HP + HS) cr db := by
  obtain ⟨S, hR, -, hm, hP, hS, hC⟩ := h
  exact ⟨Cut Eg g.i S, hR, hm, MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hP hS, hC⟩

/-- (S7h) **A thread's plain `ThInvM`** (S7f issue 4, option (i)).  (S8b)
`ThInvM` carries the box fence (`hbf`). -/
theorem ThSys.thInvM (h : ThSys p g mem pairs th Eg Tot HP HS cr db)
    (hbf : g.boxFence = true) (hTy : ∀ S, TyOKE g (Cut Eg g.i S)) (hRc : RecFresh g g.i th.nalloc) :
    ThInvM p g mem pairs th := by
  obtain ⟨S, -, hE, hm, -⟩ := h
  exact ⟨Cut Eg g.i S, hE, hm, hbf, hTy S, hRc⟩

/-- (S7h) `ThInvR`: the thread holds at most `Tot`. -/
theorem ThSys.thInvR (h : ThSys p g mem pairs th Eg Tot HP HS cr db) : ThInvR p th Tot := by
  obtain ⟨S, hR, -⟩ := h
  exact hR.thInvR

/-- **(S7h) The per-thread hypotheses of `tstepMC_step` at the cut**: the
frame's view is the cut (`CE η = Cut E_g g.i S`, so `η.tid = g.i`), its typing
and frame invariant, closed cell types (`StoClo`, from `GStoClo`), `MemInv`,
`MemHeld` (holding `HP + HS`) and `PromCr` at `CE η`. -/
theorem ThSys.env (hclo : GStoClo Eg) (h : ThSys p g mem pairs th Eg Tot HP HS cr db) :
    ∃ S ρ η cx Rf Rs, CE η = Cut Eg g.i S ∧ η.tid = g.i ∧ EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot ∧ TermTyped.StoClo (CE η) ∧
      MemInv g (CE η) (stOf mem pairs th) ∧ MemHeld (CE η) (stOf mem pairs th) (HP + HS) ∧
      TermPlant.PromCrK (CE η) (stOf mem pairs th) cr db ∧ RetPw th.σs th.stack cx.ret ∧ DyFr p annNew (progTgts p) η th.σs th.term := by
  obtain ⟨S, ⟨ρ, η, cx, Rf, Rs, hCE, hE, hT, htv, hi, hsum, hRP, hDy⟩, -, hm, hP, hS, hC⟩ := h
  have hH := MemHeld_join (fun _ _ hc hp => Cut_cov hc hp) hP hS
  have htid : (CE η).tid = (Cut Eg g.i S).tid := congrArg TEnv.tid hCE
  refine ⟨S, ρ, η, cx, Rf, Rs, hCE, htid, hE, hT, htv, hi, hsum, ?_, ?_, ?_, ?_, hRP, hDy⟩
  · rw [hCE]; exact StoClo_Cut hclo g.i S
  · rw [hCE]; exact hm
  · rw [hCE]; exact hH
  · rw [hCE]; exact hC

end

/-! ## Global consequences -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
  {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}

/-- (S7h) Thread `i`'s `ThInvMC` from `SysInv`. -/
theorem SysInvW.thInvMC (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) :
    ThInvMCK p (gOf p k arch c i) c.mem c.pairs th (Tot i) (HP i + HS) (cr i) (db i) :=
  (h.thread hth).thInvMC

/-- (S7h) Thread `i`'s plain `ThInvM` from `SysInv`. -/
theorem SysInvW.thInvM (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) (hTy : ∀ S, TyOKE (gOf p k arch c i) (Cut Eg i S))
    (hRc : RecFresh (gOf p k arch c i) i th.nalloc) :
    ThInvM p (gOf p k arch c i) c.mem c.pairs th :=
  (h.thread hth).thInvM h.bf hTy hRc

/-- (S7h) Thread `i`'s `tstepMC_step` hypotheses at its cut from `SysInv`
(`ThSys.env`; note `(gOf p k arch c i).i = i`). -/
theorem SysInvW.env (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat} {th : TTh}
    (hth : c.ths[i]? = some th) :
    ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ η.tid = i ∧ EnvOK p η ∧ TypedK p η cx th.term ∧ TvOK cx ∧
      FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧ TermTyped.StoClo (CE η) ∧
      MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) ∧
      MemHeld (CE η) (stOf c.mem c.pairs th) (HP i + HS) ∧ TermPlant.PromCrK (CE η) (stOf c.mem c.pairs th) (cr i) (db i) ∧
      RetPw th.σs th.stack cx.ret ∧ DyFr p annNew (progTgts p) η th.σs th.term :=
  (h.thread hth).env h.clo

/-- **(S7i) Every cut adopts the shared holding**: at thread `i`'s cut (any
`seen`), over a state with the configuration's memory and `i`'s promises, `HS`
is a shared part (`MemHeldS_of_G`, `PromsOK`, `SharedTyOK`).  What an idle
thread uses after another thread's step. -/
theorem SysInvW.memHeldS_of_held (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    {th : TTh} (hth : c.ths[i]? = some th) (S : AllocLabel → Prop) {s : St} (hmem : s.mem = c.mem)
    (hpr : s.promises = th.promises) : MemHeldS (Cut Eg i S) s HS :=
  MemHeldS_of_G hmem h.shty (fun t => by rw [hpr]; exact h.proms i th hth t) h.held

/-- **(S7i) A cut's shared part is a global shared holding** (`MemHeldG_of_S`):
what the stepping thread provides. -/
theorem SysInvW.memHeldG_of_S (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    {th : TTh} (hth : c.ths[i]? = some th) {S : AllocLabel → Prop} {s : St} {H : Res} (hmem : s.mem = c.mem)
    (hpr : s.promises = th.promises) (hs : MemHeldS (Cut Eg i S) s H) : MemHeldG Eg c H :=
  MemHeldG_of_S hmem h.shty (fun t => by rw [hpr]; exact h.proms i th hth t) hs

theorem sum_add_key (T H : Nat → Res) (k : Key) : ∀ l : List Nat,
    (l.map fun i => (T i + H i) k).sum = (l.map fun i => T i k).sum + (l.map fun i => H i k).sum
  | [] => rfl
  | a :: l => by
      simp only [List.map_cons, List.sum_cons]
      rw [sum_add_key T H k l, Res.add_apply]
      omega

/-- (S7h) The `machine_tokens` sum form (`TermLiveHeld.TokSum`) over the
threads' frames and private holdings and the shared holding. -/
theorem SysInvW.tokSum (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) (n : Nat) :
    TermLiveHeld.TokSum (fun i => Tot i + HP i) c.ths.size HS n :=
  h.tok n

/-- (S7h) The sum form against one thread `j`'s whole holding `HP j + HS`
(the `hs` of `held_word_changes_only_by_holder_sum`). -/
theorem SysInvW.tokSum_thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {j : Nat}
    (hj : j < c.ths.size) (n : Nat) : TermLiveHeld.TokSum Tot c.ths.size (HP j + HS) n := by
  have h0 : ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.rg n))).sum + HS (.rg n) ≤ 1 := h.tok n
  have e := sum_add_key Tot HP (.rg n) (List.range c.ths.size)
  have h2 : HP j (.rg n) ≤ ((List.range c.ths.size).map fun i => HP i (.rg n)).sum :=
    TermLiveHeld.single_le_sum (fun i => HP i (.rg n)) (List.mem_range.mpr hj)
  show ((List.range c.ths.size).map (fun i => Tot i (.rg n))).sum + (HP j + HS) (.rg n) ≤ 1
  rw [Res.add_apply]
  omega

/-- **(S7h) Token uniqueness from `SysInv`**: two threads holding `rg n` in
their frames are the same thread (`tokUniq_of_sum`). -/
theorem SysInvW.tokUniq (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i j n : Nat}
    (hi : i < c.ths.size) (hj : j < c.ths.size) (h1 : 1 ≤ Tot i (.rg n)) (h2 : 1 ≤ Tot j (.rg n)) : i = j :=
  TermLiveHeld.tokUniq_of_sum (Tot := fun i => Tot i + HP i) (h.tok n) hi hj
    (show 1 ≤ Tot i (.rg n) + HP i (.rg n) by omega) (show 1 ≤ Tot j (.rg n) + HP j (.rg n) by omega)

/-- **(S7h) `machine_words` at a thread from `SysInv`**: thread `i`'s frame
and whole holding carry at most one `wd n`. -/
theorem SysInvW.wd_thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    (hi : i < c.ths.size) (n : Nat) : Tot i (.wd n) + (HP i + HS) (.wd n) ≤ 1 := by
  have h0 : ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.wd n))).sum + HS (.wd n) ≤ 1 := h.wd n
  have h2 : (Tot i + HP i) (.wd n) ≤ ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.wd n))).sum :=
    TermLiveHeld.single_le_sum (fun i => (Tot i + HP i) (.wd n)) (List.mem_range.mpr hi)
  rw [Res.add_apply] at h2 ⊢
  omega

/-- (S7h) The `hwd` of the held-word lemmas (`held_write_needs_token`,
`held_word_changes_only_by_holder_sum`): the frame part `Rf` of thread `i`'s
total and its whole holding carry at most one `wd n`. -/
theorem SysInvW.hwd (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    (hi : i < c.ths.size) {Rf Rs : Res} (hTot : Rf + Rs = Tot i) (n : Nat) :
    Rf (.wd n) + (HP i + HS) (.wd n) ≤ 1 := by
  have := h.wd_thread hi n
  rw [← hTot, Res.add_apply] at this
  omega

/-- **(S7h) Word uniqueness from `SysInv`**: two threads whose frames carry
`wd n` are the same thread. -/
theorem SysInvW.wdUniq (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i j n : Nat}
    (hi : i < c.ths.size) (hj : j < c.ths.size) (h1 : 1 ≤ Tot i (.wd n)) (h2 : 1 ≤ Tot j (.wd n)) : i = j := by
  apply Classical.byContradiction
  intro hij
  have h0 : ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.wd n))).sum + HS (.wd n) ≤ 1 := h.wd n
  have h3 : (Tot i + HP i) (.wd n) + (Tot j + HP j) (.wd n) ≤
      ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.wd n))).sum :=
    TermLiveHeld.two_le_sum (fun i => (Tot i + HP i) (.wd n)) List.nodup_range
      (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij
  rw [Res.add_apply, Res.add_apply] at h3
  omega

/-- (F2′) Thread `i`'s frame and whole holding carry at most one `own l`. -/
theorem SysInvW.own_thread (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    (hi : i < c.ths.size) (l : Nat) : Tot i (.own l) + (HP i + HS) (.own l) ≤ 1 := by
  have h0 : ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum + HS (.own l) ≤ 1 := h.own l
  have h2 : (Tot i + HP i) (.own l) ≤ ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum :=
    TermLiveHeld.single_le_sum (fun i => (Tot i + HP i) (.own l)) (List.mem_range.mpr hi)
  rw [Res.add_apply] at h2 ⊢
  omega

/-- (F2′) The frame part `Rf` of thread `i`'s total and its whole holding
carry at most one `own l`. -/
theorem SysInvW.hown (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i : Nat}
    (hi : i < c.ths.size) {Rf Rs : Res} (hTot : Rf + Rs = Tot i) (l : Nat) :
    Rf (.own l) + (HP i + HS) (.own l) ≤ 1 := by
  have := h.own_thread hi l
  rw [← hTot, Res.add_apply] at this
  omega

/-- **(F2′) Own-handle uniqueness from `SysInv`**: two threads whose frames
carry `own l` are the same thread. -/
theorem SysInvW.ownUniq (h : SysInvW p k arch Init MintOK c Eg Tot HP HS cr db) {i j l : Nat}
    (hi : i < c.ths.size) (hj : j < c.ths.size) (h1 : 1 ≤ Tot i (.own l)) (h2 : 1 ≤ Tot j (.own l)) : i = j := by
  apply Classical.byContradiction
  intro hij
  have h0 : ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum + HS (.own l) ≤ 1 := h.own l
  have h3 : (Tot i + HP i) (.own l) + (Tot j + HP j) (.own l) ≤
      ((List.range c.ths.size).map (fun i => (Tot i + HP i) (.own l))).sum :=
    TermLiveHeld.two_le_sum (fun i => (Tot i + HP i) (.own l)) List.nodup_range
      (List.mem_range.mpr hi) (List.mem_range.mpr hj) hij
  rw [Res.add_apply, Res.add_apply] at h3
  omega

/-- (S7h) `machine_words` from `SysInv`, for every thread. -/
theorem machine_words_of_SysInv {Init : Res} {MintOK : Res → Prop} (h : SysInv p k arch Init MintOK c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvW p k arch Init MintOK c Eg Tot HP HS cr db ∧
      ∀ i n, i < c.ths.size → Tot i (.wd n) + (HP i + HS) (.wd n) ≤ 1 := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hw⟩ := h
  exact ⟨Eg, Tot, HP, HS, cr, db, hw, fun i n hi => hw.wd_thread hi n⟩

/-- (S7h) Token uniqueness from `SysInv`, for every pair of threads. -/
theorem tokUniq_of_SysInv {Init : Res} {MintOK : Res → Prop} (h : SysInv p k arch Init MintOK c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvW p k arch Init MintOK c Eg Tot HP HS cr db ∧
      ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j := by
  obtain ⟨Eg, Tot, HP, HS, cr, db, hw⟩ := h
  exact ⟨Eg, Tot, HP, HS, cr, db, hw, fun i j n hi hj h1 h2 => hw.tokUniq hi hj h1 h2⟩

end

#print axioms SysInv.intro
#print axioms SysInvW.thread
#print axioms SysInvW.thread_lt
#print axioms ThSys.memHeld
#print axioms ThSys.thInvMC
#print axioms ThSys.thInvM
#print axioms BoxTopP_of_G
#print axioms ThSys.thInvR
#print axioms ThSys.env
#print axioms SysInvW.thInvMC
#print axioms SysInvW.thInvM
#print axioms SysInvW.env
#print axioms SysInvW.memHeldS_of_held
#print axioms SysInvW.memHeldG_of_S
#print axioms sum_add_key
#print axioms SysInvW.tokSum
#print axioms SysInvW.tokSum_thread
#print axioms SysInvW.tokUniq
#print axioms SysInvW.wd_thread
#print axioms SysInvW.hwd
#print axioms SysInvW.wdUniq
#print axioms SysInvW.own_thread
#print axioms SysInvW.hown
#print axioms SysInvW.ownUniq
#print axioms machine_words_of_SysInv
#print axioms tokUniq_of_SysInv

end TermSys

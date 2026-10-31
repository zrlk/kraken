import WeakCore.TermScopeW
import WeakCore.TermStartW
import WeakCore.ExtArmZ
/-! # TermStartD: the device start and slot-ownership (token) race freedom at it

* `slotP`: the slot protocol of an N-slot DMA ring.
* `boardTerm`/`Board`/`startD`: the device-start wrapper (platform glue, not program code; see the trusted device assumption below).
* `BoardOK`: the decidable program-side facts of a device start (the spawned function is a `device` decl).
* `initShape_startD`, `runScope_startD`: the start is an `InitShape`/`RunScope` start.
* `token_unique_net_board`, `token_unique_final_board`, `machine_tokens_main_board`, `reachable_typed_board`: the
  `ExtArmZ` finals at a device start.

What is proved is **slot-ownership (token) race freedom**: no region token is held by two threads' frames. The DMA
data cells of a device program are public cells and are NOT protected by these theorems; data-level DRF is deferred
(it needs region references to cross to the device thread).
Trusted device assumption (outside the theorems): the real device touches only what the code of the device's threads
touches, where the device's threads are the device thread and every thread descended from it by spawns.
-/

namespace TermStartD
open CoreLang CoreTerm CoreTyping TermRun TermSound TermCut TermScope TermInit TermStartW TermMain TermExtStep
open TermSys TermMem TermStep TermSpawn
open WeakMem (Arch Ts)

/-- The slot protocol of an N-slot DMA ring, one word per slot:
`0 ↦ r` free (the word holds the slot's region; the CPU takes it by `cas 0 1`), `1 ↦ ∅` CPU-owned (the CPU fills the
slot, then hands it over by `store rel 1 → 2`), `2 ↦ r` ready (the device takes it by `cas acq 2 3`), `3 ↦ ∅`
device-owned (the device serves the slot, then completes it by `store rel 3 → 0`). Both held states declare the
recovery target `0` (`recover(1->0, 3->0)`): no term makes that move; it fixes what a trusted reclaim step, if one is
added later, may write. The slot's region is an ownership token for the protocol: it guards no buffer unless the program puts one in it.
Source: `<0!, 1, 2!, 3 ; 0->1, 1->2, 2->3, 3->0 ; recover(1->0, 3->0)>`. -/
def slotP : Proto := ⟨[⟨0, 0, true⟩, ⟨0, 1, false⟩, ⟨0, 2, true⟩, ⟨0, 3, false⟩],
  [(0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 0)], false, [], [], [], false, false, false, false, false, [(1, 0), (3, 0)]⟩

/-- **The device-start wrapper's body.** Thread 0 calls the CPU decl `setup` on its start argument `a`; `setup`
returns the CPU's and the device's arguments `(ca, da)`; thread 0 spawns the device decl `dev` on `da` at the checked
type `T` (the platform attaching the device to the regions `setup` chose; a trusted assumption), then calls the CPU decl
`main` on `(ca, d)`, `d` the device thread's id, and exits as `wrapTerm` does. This is the only spawn of a device decl
outside device decls: no CPU decl spawns, calls or tail-calls a device decl or takes one as a value (`checkDecl`'s kind
rules). A device decl may itself spawn threads, running device or CPU decls, and call CPU decls; the trusted device assumption counts
the device thread and every thread descended from it by spawns as part of the device. The wrapper is not a decl: `checkDecl`'s kind rules do not apply to it; `check`/`checkW` do. -/
def boardTerm (dev : String) (T : Ty) (rt : Option Ty) : Expr :=
  .let_ "s" (.call "setup" [] (.var "a")) <|
  .split (.var "s") "ca" "da" <|
  .let_ "d" (.spawn dev (.var "da") T) <|
  .let_ "m" (.pair (.var "ca") (.var "d")) <|
  .let_ "r" (.call "main" [] (.var "m")) (exitTail rt)

/-- A device start: the device decl, its argument type, and thread 0's start argument (its type and words:
register handles and other number words). -/
structure Board where
  dev : String
  devTy : Ty
  argTy : Ty
  args : List Word

/-- The wrapper thread of a device start. -/
def boardTh (p : Prog) (b : Board) : TTh :=
  { term := boardTerm b.dev b.devTy (mainRet p), env := [("a", b.argTy, b.args)] }

/-- The wrapper's checking context: `a : argTy`, returning `Unit`. -/
def bcx (b : Board) : Cx := { vars := [("a", b.argTy, true)], ret := .unit }

/-- **The device start**: the wrapper thread alone, empty memory, empty trace, thread capacity `cap`. -/
def startD (p : Prog) (b : Board) (cap : Nat) : Cfg := { mem := #[], ths := #[boardTh p b], cap := cap }

/-- The start words are numbers and form a resource-free value of `argTy`, laid out as `argTy`. -/
def BoardArgOK (p : Prog) (b : Board) : Prop :=
  (∀ w ∈ b.args, ∃ m, w = cst (.num m)) ∧
  (∀ i, VRR (fun _ => 0) (Cut (Eg0 p) i S0) b.argTy (shp b.argTy) b.args .zero) ∧ Lay [] b.argTy b.argTy b.args

/-- **The program-side facts of a device start**, each decidable for a concrete program except `arg`. The
spawned function must be a `device` decl (`devKind`); `setup` and `main` may be of any kind. -/
structure BoardOK (p : Prog) (b : Board) : Prop where
  checked : checkProg p = .ok ()
  scope : ProgScopeOKW p = true
  devKind : ((p.find? (·.name == b.dev)).map (·.kind == .device)).getD false = true
  wrap : check p (bcx b) (boardTerm b.dev b.devTy (mainRet p)) = .ok ()
  wrapW : checkW p (bcx b) (boardTerm b.dev b.devTy (mainRet p)) = .ok ()
  wrapScope : allOK (boardTerm b.dev b.devTy (mainRet p)) = true
  argDrf : drf b.argTy = true
  argTv : (TermClose.tb 0 b.argTy && TermTv.mg b.argTy && wrapOK b.argTy) = true
  arg : BoardArgOK p b

theorem startD_get {p : Prog} {b : Board} {cap i : Nat} {th : TTh} (h : (startD p b cap).ths[i]? = some th) :
    i = 0 ∧ th = boardTh p b := by
  simp only [startD] at h
  rcases i with _ | i
  · simp at h; exact ⟨rfl, h.symm⟩
  · simp at h

theorem bcx_tvOK {b : Board} (h : (TermClose.tb 0 b.argTy && TermTv.mg b.argTy && wrapOK b.argTy) = true) :
    TermTv.TvOK (bcx b) := by
  simp only [Bool.and_eq_true] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [bcx, h.1.1, h.1.2, Cx.opaqueOK] <;> decide

/-- The exit tail, at no hidden positions: no refused allocation, and no tainted call. -/
theorem scan_exitTail_clean (ann : Op → Option Ty) (tg : List Ty) (rt : Option Ty) :
    (scan ann tg [] (exitTail rt)).1 = [] ∧ ∀ c ∈ (scan ann tg [] (exitTail rt)).2, c.2 = [] := by
  rcases rt with _ | t
  · simp only [exitTail, scan, both, opCalls]; constructor
    · split <;> simp [hits]
    · simp
  · simp only [exitTail]
    (repeat' split) <;> simp only [scan, both, opCalls] <;> refine ⟨?_, by simp⟩ <;> (repeat' split) <;> simp_all [hits]

/-- The wrapper term, at no hidden positions: no refused allocation, and no tainted call. -/
theorem scan_board_clean (ann : Op → Option Ty) (tg : List Ty) (dev : String) (T : Ty) (rt : Option Ty) :
    (scan ann tg [] (boardTerm dev T rt)).1 = [] ∧ ∀ c ∈ (scan ann tg [] (boardTerm dev T rt)).2, c.2 = [] := by
  obtain ⟨h1, h2⟩ := scan_exitTail_clean ann tg rt
  simp only [boardTerm, scan, both, opCalls]
  refine ⟨?_, ?_⟩
  · rw [h1]; (repeat' split) <;> simp_all [hits]
  · intro c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, taintOf_nil] at hc
    repeat' (rcases hc with hc | hc)
    all_goals first | rfl | exact h2 _ hc | (subst hc; rfl)

/-- The wrapper term has the entry frame's opened-type-package clause, at no type arguments. -/
theorem dyFr_board (ann : Op → Option Ty) (tg : List Ty) (p : Prog) (η : TEnv) (b : Board) :
    DyFr p ann tg η [] (boardTerm b.dev b.devTy (mainRet p)) := by
  obtain ⟨h1, h2⟩ := scan_board_clean ann tg b.dev b.devTy (mainRet p)
  exact dyFr_init p ann tg η _ [] (fun _ _ h => by simp at h) ⟨h1, fun c hc hne => absurd (h2 c hc) hne⟩

/-- **The wrapper's entry frame** at a device start. -/
theorem entryOK_board {p : Prog} {b : Board} {i : Nat} (B : BoardOK p b) : EntryOK p i (boardTh p b) := by
  have hv := B.arg.2.1 i
  exact ⟨fun _ => 0, bcx b, ⟨check_sound p _ _ B.wrap, B.wrapW, fun v hm => by
      simp only [bcx, List.mem_singleton] at hm; subst hm; have h3 := B.argTv; simp only [Bool.and_eq_true] at h3; exact h3.2,
      fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩, bcx_tvOK B.argTv,
    ⟨TermSpawn.finv_entry (fun _ _ => trivial) rfl rfl hv B.arg.2.2, fun _ _ _ _ _ _ => rfl,
    heldOK_entry rfl hv⟩, dyFr_board annNew (progTgts p) p _ b⟩

/-- **`InitShape` at a device start.** -/
theorem initShape_startD {p : Prog} {b : Board} {cap : Nat} (B : BoardOK p b) : InitShape p (startD p b cap) where
  mem := rfl
  pairs := rfl
  bf := rfl
  thr := fun i th hth => by
    obtain ⟨-, rfl⟩ := startD_get hth
    exact ⟨rfl, rfl, rfl, entryOK_board B⟩
  vs0 := fun i th hth => by
    obtain ⟨-, rfl⟩ := startD_get hth
    refine ⟨rfl, rfl, rfl, rfl, rfl, fun e he w hw => ?_⟩
    simp only [boardTh, List.mem_singleton] at he
    subst he
    obtain ⟨m, rfl⟩ := B.arg.1 w hw
    exact ⟨rfl, rfl⟩
  envNoLoc := fun i th hth => by
    obtain ⟨-, rfl⟩ := startD_get hth
    intro e he w hw a g
    simp only [boardTh, List.mem_singleton] at he
    subst he
    obtain ⟨m, rfl⟩ := B.arg.1 w hw
    simp [cst, Promises.TVal.mk0]
  tid0 := fun i th hth => by
    obtain ⟨-, rfl⟩ := startD_get hth
    rfl
  tys0 := fun i th hth => by
    obtain ⟨-, rfl⟩ := startD_get hth
    rfl

/-- **`RunScope` at a device start.** -/
theorem runScope_startD {p : Prog} {b : Board} {cap : Nat} (B : BoardOK p b) : RunScope (startD p b cap) :=
  runDRF_init fun i th hth => by
    obtain ⟨-, rfl⟩ := startD_get hth
    have hσ : AllDrf (boardTh p b).σs := fun σ (hσ : σ ∈ ([] : List Ty)) => by cases hσ
    refine ⟨B.wrapScope, hσ, fun e he => ?_, rfl⟩
    simp only [boardTh, List.mem_singleton] at he
    subst he
    exact B.argDrf

/-- A device start's run relation besides `Step`: a spawn (capacity `cap`) or an extern step. -/
abbrev SpD (p : Prog) (k : Promises.Knobs) (arch : Arch) (cap : Nat) : Cfg → Cfg → Prop :=
  fun c c' => TermSpawnStep.Spawn p k arch cap c c' ∨ Ext p k arch c c'

/-- A device start is an `InitOK` start. -/
theorem initOK_startD {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {b : Board} {cap : Nat}
    (B : BoardOK p b) : InitOK p k arch Init (fun _ => True) (startD p b cap) :=
  initOK_of (initShape_startD B) trivial

/-- **The obligations at a device start**. -/
theorem oblX_board {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {b : Board} {cap : Nat}
    (B : BoardOK p b) :
    ObligationsFX p k arch (SpD p k arch cap) Init (fun _ => True) (startD p b cap) :=
  ⟨B.checked, B.scope, runScope_startD B⟩

/-- **Slot-ownership (token) race freedom at a device start** (`token_unique_net_em0` at `startD`): along every
run of a checked device program from its device start, at every reachable configuration, no region token is held by
two threads' frames unless a promise owes it; in particular no slot word's region is held by the device thread and a
CPU thread at once. This is race freedom of the slot OWNERSHIP protocol, not of memory: the DMA data cells are public
cells, unprotected by this theorem, and data-level DRF is deferred. Trusted device assumption (outside the theorem): the
real device touches only what the code of the device's threads touches (the device thread and every thread
descended from it by spawns). -/
theorem token_unique_net_board {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {b : Board} {cap : Nat}
    (B : BoardOK p b)
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE p k arch cap (startD p b cap) c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      FrameTie p k arch c Eg Tot ∧ SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      ∀ n, Debt c db (.rg n) = 0 →
      ∀ i j, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  ExtArmZ.token_unique_net_em0 (oblX_board (Init := Init) B) hk (initOK_startD (Init := Init) B) hr

/-- **Slot-ownership (token) race freedom at a device start, gross form** at promise-free configurations: no
region token is held by two threads' frames. Not data-level: the DMA data cells are public cells, unprotected by this
theorem; data-level DRF is deferred. The trusted device assumption is as in `token_unique_net_board`. -/
theorem token_unique_final_board {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {b : Board} {cap : Nat}
    (B : BoardOK p b)
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE p k arch cap (startD p b cap) c) (hn : AllNoProm c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot ∧ ∀ i j n, i < c.ths.size → j < c.ths.size →
      1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j :=
  ExtArmZ.token_unique_final_em0 (oblX_board (Init := Init) B) hk (initOK_startD (Init := Init) B) hr hn

/-- **`machine_tokens_main_em0` at a device start**: the system invariant, the net key bounds, the gross bounds
and region-token uniqueness at promise-free configurations, and every thread typed at its cut with `MemInv`. The token
bounds are slot-ownership (token) race freedom; the DMA data cells are public cells, unprotected; data-level DRF is
deferred. The trusted device assumption is as in `token_unique_net_board`. -/
theorem machine_tokens_main_board {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {b : Board} {cap : Nat}
    (B : BoardOK p b)
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE p k arch cap (startD p b cap) c) :
    ∃ (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db : Nat → Ts → Res),
      SysInvN p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS cr db key) ∧
      (AllNoProm c → SysInvW p k arch Init (fun _ => True) c Eg Tot HP HS cr db ∧
        ∀ i j n, i < c.ths.size → j < c.ths.size → 1 ≤ Tot i (.rg n) → 1 ≤ Tot j (.rg n) → i = j) ∧
      ∀ i th, c.ths[i]? = some th → ∃ S ρ η cx Rf Rs, CE η = Cut Eg i S ∧ EnvOK p η ∧ Typed p cx th.term ∧
        FInvR ρ η th.σs (ResumeR p th.stack Rs) cx th.env Rf ∧ Rf + Rs = Tot i ∧
        MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th) :=
  ExtArmZ.machine_tokens_main_em0 (oblX_board (Init := Init) B) hk (initOK_startD (Init := Init) B) hr

/-- **Every thread of a device start is well typed** along every run, at ONE global environment
(`FrameTie`); the device thread included. This makes no race-freedom claim: the DMA data cells are public cells,
unprotected; data-level DRF is deferred. -/
theorem reachable_typed_board {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {b : Board} {cap : Nat}
    (B : BoardOK p b)
    (hk : k.storeDepRts = true) {c : Cfg} (hr : StepsE p k arch cap (startD p b cap) c) :
    ∃ (Eg : GEnv) (Tot : Nat → Res), FrameTie p k arch c Eg Tot :=
  ExtArmZ.reachable_typed_em0 (oblX_board (Init := Init) B) hk (initOK_startD (Init := Init) B) hr

end TermStartD

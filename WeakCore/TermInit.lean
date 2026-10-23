import WeakCore.TermScope

/-!
# TermInit: the initial configuration (S11)

The standard initial configuration: empty memory, no promises, every thread
at an entry frame (the `spawn` shape `tail f [] a ts` with its argument, or
any frame typed at the empty global environment).  `SysInvW` holds there with
the empty global environment `Eg0 p` (no cells, no boxes, no frontiers), zero
frame totals, holdings and credits, and the rid clause (`ridOK_init`); so
`TermMain.InitOK` holds (`TermMain.initOK_of`).

The per-thread hypothesis `EntryOK` is the entry frame's typing at the empty
cut; `entryOK_of` discharges it for an entry term the checker accepts in a
context typing the argument as a resource-free value.
-/

namespace TermInit

open CoreLang CoreTerm CoreTyping TermRun TermSound TermStep TermCut TermSys TermMain TermScope TermTv TermMem
open WeakMem (Memory Ts AllocLabel Address Msg)

/-- The empty global environment of program `p`. -/
def Eg0 (p : Prog) : GEnv := { prog := p }

/-- No label seen. -/
def S0 : AllocLabel → Prop := fun _ => False

@[simp] theorem Eg0_sto (p : Prog) (l : AllocLabel) : (Eg0 p).sto l = none := rfl
@[simp] theorem Eg0_ini (p : Prog) (l : AllocLabel) : (Eg0 p).ini l = 0 := rfl
@[simp] theorem Eg0_rini (p : Prog) (l : AllocLabel) : (Eg0 p).rini l = 0 := rfl
@[simp] theorem Eg0_pfr (p : Prog) (l : AllocLabel) : (Eg0 p).pfr l = none := rfl
@[simp] theorem Eg0_box (p : Prog) (l : AllocLabel) : (Eg0 p).box l = none := rfl
@[simp] theorem Eg0_fpOf (p : Prog) (i : Nat) : (Eg0 p).fpOf i = [] := rfl
@[simp] theorem Eg0_prog (p : Prog) : (Eg0 p).prog = p := rfl

@[simp] theorem cutSto_Eg0 (p : Prog) (i : Nat) (l : AllocLabel) : cutSto (Eg0 p) i l = none := by
  simp [cutSto, GEnv.InCut, Eg0]

theorem cut_sto (p : Prog) (i : Nat) (S : AllocLabel → Prop) (l : AllocLabel) : (Cut (Eg0 p) i S).sto l = none :=
  cutSto_Eg0 p i l

/-- **The entry frame of thread `i`**: typed, with a resource-free frame, at
the empty cut. -/
def EntryOK (p : Prog) (i : Nat) (th : TTh) : Prop :=
  ∃ (ρ : Nat → Nat) (cx : Cx), TypedK p (Cut (Eg0 p) i S0) cx th.term ∧ TvOK cx ∧
    FInvR ρ (Cut (Eg0 p) i S0) th.σs (ResumeR p [] .zero) cx th.env .zero

/-- **The standard initial configuration**: empty memory, the box fence on,
and every thread at an entry frame with no promises, an empty stack and no
writes. -/
structure InitShape (p : Prog) (c0 : Cfg) : Prop where
  mem : c0.mem = #[]
  pairs : c0.pairs = []
  bf : c0.boxFence = true
  thr : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
    th.promises = [] ∧ th.stack = [] ∧ th.vs.vWr = 0 ∧ EntryOK p i th
  /-- (seenFacts at the start) zero scalar views, and argument words with zero view and read
  timestamp (e.g. `cst`): `TermViewInv.viewInv_init`; at the spawn shape `vs0_spawn`/`spawn0_vs0`. -/
  vs0 : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
    th.vs.vRd = 0 ∧ th.vs.vCtrl = 0 ∧ th.vs.vPreBase = 0 ∧ th.vs.vRelSt = 0 ∧
      th.vs.coh = (fun _ => 0) ∧
      ∀ e ∈ th.env, ∀ w ∈ e.2.2, w.view = 0 ∧ w.rts = 0
  /-- (D-B `LblSto` at the start) no argument word is a location. -/
  envNoLoc : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
    ∀ e ∈ th.env, ∀ w ∈ e.2.2, ∀ (a : WeakMem.Address) (g : Nat), w.val ≠ .loc a g
  /-- (E2, stage 1) no start thread has a `ThreadId` box yet. -/
  tid0 : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.tidLbl = none


theorem memInv_init {g : G} {p : Prog} {i : Nat} {th : TTh} (hp : th.promises = []) :
    MemInv g (Cut (Eg0 p) i S0) (stOf #[] [] th) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (simp_all [stOf, MemOKP, OwnOKSF, PromLt, FreshLP, PrivCoh, SeenLE, OwnHidP, PubDefP, OwnPubV, PubInv, SeenOwn,
    Inh, PubCpl, PubMem, PubPair, PubLive, BoxInv, BoxTopP, PromOK, cutSto_Eg0, S0, Cut])


theorem memHeldOn_init {Q : AllocLabel → Prop} {p : Prog} {i : Nat} {S : AllocLabel → Prop} {s : St} :
    MemHeldOn Q (Cut (Eg0 p) i S) s .zero :=
  ⟨[], fun _ => .zero, List.nodup_nil, (fun l c _ h => by simp [Cut] at h), (fun _ h => by simp at h), rfl,
    (fun _ h => by simp at h)⟩

/-- No thread of `c` has a promise: there are none at all. -/
theorem allProms_nil {c : Cfg} (h : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = []) (t : Ts) :
    t ∉ allProms c := by
  intro ht
  simp only [allProms, List.mem_flatMap] at ht
  obtain ⟨th, hth, ht⟩ := ht
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem (Array.mem_toList_iff.1 hth)
  rw [h i _ (Array.getElem?_eq_getElem hi)] at ht
  cases ht

theorem res_zero_apply (key : Key) : Res.zero key = 0 := rfl

theorem sum_range_zero : ∀ (N : Nat), ((List.range N).map (fun _ => (0 : Nat))).sum = 0
  | 0 => rfl
  | N + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range_zero N]; rfl

theorem pSumAt_init {c : Cfg} (h : ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → th.promises = [])
    (i : Nat) (f : Ts → Res) : pSumAt c i f = .zero := by
  unfold pSumAt
  cases e : c.ths[i]? with
  | none => rfl
  | some th => simp [pSum, stOf, h i th e]

theorem thSum_zero (N : Nat) {f : Nat → Res} (hf : ∀ i, f i = .zero) : thSum N f = .zero := by
  unfold thSum
  induction N with
  | zero => rfl
  | succ N ih => rw [List.range_succ, List.map_append, Res.sum_append, ih]; simp [Res.sum, hf]

/-- **`SysInvW` at the standard initial configuration** (S11), with the
empty global environment and zero totals, holdings and credits. -/
theorem sysInvW_init {p : Prog} {k : Promises.Knobs} {arch : WeakMem.Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hs : InitShape p c0) (hM : MintOK .zero) :
    SysInvW p k arch Init MintOK c0 (Eg0 p) (fun _ => .zero) (fun _ => .zero) .zero (fun _ _ => .zero)
      (fun _ _ => .zero) := by
  have hpr : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.promises = [] := fun i th h => (hs.thr i th h).1
  refine ⟨?thr, ?held, ?clo, ?cmg, ?shty, ?proms, ?fpok, ?fresh, ?bal, ?tok, ?wd, ?own, hs.bf, ?boxtop, ?disj, ?fpfree,
    ?plt, ?vwr, ?frle, fun _ => Nat.le_refl _, ?bnamed, ?freshU⟩
  case freshU =>
    intro q j _ _
    refine ⟨⟨rfl, rfl, rfl, rfl, fun t m hm _ => ?_⟩, fun n _ => ?_, rfl⟩
    · rw [hs.mem] at hm; simp at hm
    · rw [pSumAt_init hpr]; rfl
  case clo => intro l cl h; simp at h
  case cmg => intro l cl h; simp at h
  case shty => intro l cl ⟨f, h⟩; simp at h
  case boxtop => intro l B h; simp at h
  case frle => intro l cl f h; simp at h
  case bnamed => intro l B h; simp at h
  case thr =>
    intro i th hth
    obtain ⟨hp, hst, hv, ρ, cx, hT, htv, hFI⟩ := hs.thr i th hth
    have hE : EnvOK p (Cut (Eg0 p) i S0) := ⟨rfl, Coh_CE (Cut (Eg0 p) i S0), CohR_CE (Cut (Eg0 p) i S0)⟩
    refine ⟨S0, ⟨ρ, Cut (Eg0 p) i S0, cx, .zero, .zero, rfl, hE, hT, htv, by rw [hst]; exact hFI,
      Res.add_zero _, fun _ _ h => by rw [hst] at h; cases h⟩, ⟨ρ, Cut (Eg0 p) i S0, cx, rfl, hE, hT.1, htv, by rw [hst]; exact ⟨hFI.1, fun _ _ h => by cases h⟩⟩, ?_,
      memHeldOn_init, memHeldOn_init, ?_⟩
    · show MemInv _ _ (stOf c0.mem c0.pairs th)
      rw [hs.mem, hs.pairs]
      exact memInv_init hp
    · intro t ht
      simp [stOf, hp] at ht
  case held =>
    refine ⟨[], fun _ => .zero, List.nodup_nil, ?_, ?_, rfl, ?_⟩
    · intro l cl ⟨f, h⟩; simp at h
    · intro l h; simp at h
    · intro l h; simp at h
  case proms =>
    intro i th hth t
    simp only [hpr i th hth, Eg0_fpOf, List.nil_append, List.not_mem_nil, false_iff]
    exact allProms_nil hpr t
  case fpok =>
    intro i th S _
    exact ⟨fun t h => by simp [Cut] at h, fun t _ h => by simp [Cut] at h⟩
  case fresh =>
    intro i th _ j _
    refine ⟨rfl, rfl, rfl, rfl, fun t m h _ => ?_⟩
    rw [hs.mem] at h
    simp at h
  case bal =>
    refine ⟨.zero, hM, ?_⟩
    rw [thSum_zero _ (fun i => by rw [pSumAt_init hpr]; simp)]
    exact Res.zero_le _
  case tok =>
    intro n
    simp only [KeySum, Res.add_apply, res_zero_apply, Nat.add_zero]
    rw [sum_range_zero]
    exact Nat.zero_le _
  case wd =>
    intro n
    simp only [KeySum, Res.add_apply, res_zero_apply, Nat.add_zero]
    rw [sum_range_zero]
    exact Nat.zero_le _
  case own =>
    intro n
    simp only [KeySum, Res.add_apply, res_zero_apply, Nat.add_zero]
    rw [sum_range_zero]
    exact Nat.zero_le _
  case disj =>
    intro i j thi thj t _ hi _ ht
    rw [hpr i thi hi] at ht
    cases ht
  case fpfree =>
    intro i th t _ h
    cases h
  case plt =>
    intro i th t hth ht
    rw [hpr i th hth] at ht
    cases ht
  case vwr =>
    intro i th hth
    rw [(hs.thr i th hth).2.2.1]
    exact Nat.zero_le _

/-- The rid clause initially: no key is held, so every `rc` (and every debit) works. -/
theorem ridOK_init {c0 : Cfg} {db : Nat → Ts → Res} (rc : Nat → Nat) :
    RidOK c0 (fun _ => .zero) (fun _ => .zero) .zero (fun _ _ => .zero) db rc := by
  intro n _ key _
  refine Nat.le_trans (Nat.le_of_eq (Nat.add_eq_zero_iff.2 ⟨TermOnce.sum_range_zero (fun i _ => ?_), rfl⟩))
    (Nat.zero_le _)
  have hp : pSumAt c0 i (fun _ => Res.zero) = .zero := by
    unfold pSumAt
    cases c0.ths[i]? with
    | none => rfl
    | some th =>
      show Res.sum (th.promises.map fun _ => Res.zero) = .zero
      induction th.promises with
      | nil => rfl
      | cons _ _ ih => simp [Res.sum_cons, ih]
  simp [hp]

/-! ## The scope invariant initially -/

theorem envDRF_all {env : Env} {t : Expr} (h : ∀ e ∈ env, drf e.2.1 = true) : EnvDRF env t := by
  intro x _ rt ws hl
  unfold lookupE at hl
  cases hf : env.find? (·.1 == x) with
  | none => rw [hf] at hl; cases hl
  | some e =>
    rw [hf] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    have := h e (List.mem_of_find?_eq_some hf)
    rw [hl] at this
    exact this

/-- **`RunScope` initially** (T1's initial hypothesis): every thread's term
passes `allOK`, its type arguments and environment types are `drf`, and its
stack is empty.  For the `spawn` shape `tail f [] (v "a") ts` with argument
type `t` this is: `ts` and `t` are `drf`. -/
theorem runDRF_init {c0 : Cfg}
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
      allOK th.term = true ∧ AllDrf th.σs ∧ (∀ e ∈ th.env, drf e.2.1 = true) ∧ th.stack = []) :
    RunScope c0 := by
  intro i th hth
  obtain ⟨h1, h2, h3, h4⟩ := h i th hth
  exact ⟨h1, h2, envDRF_all h3, by rw [h4]; intro f hf; cases hf⟩

theorem runDRF_spawn {c0 : Cfg}
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → ∃ (f : String) (ts : List Ty) (t : Ty) (ws : List Word),
      th.term = .tail f [] (.var "a") ts ∧ th.env = [("a", t, ws)] ∧ th.σs = [] ∧ th.stack = [] ∧
      ts.all drf = true ∧ drf t = true) :
    RunScope c0 := by
  refine runDRF_init fun i th hth => ?_
  obtain ⟨f, ts, t, ws, h1, h2, h3, h4, h5, h6⟩ := h i th hth
  refine ⟨by rw [h1]; exact h5, ?_, ?_, h4⟩
  · rw [h3]; intro σ hσ; cases hσ
  rw [h2]
  intro e he
  simp only [List.mem_singleton] at he
  rw [he]
  exact h6

/-! ## `EntryOK` from the checker -/

/-- (D9) At a `tail`, `checkW` is `check` plus A1's key-free type arguments. -/
theorem checkW_tail_of {p : Prog} {cx : Cx} {f : String} {is : List String} {a : At} {ts : List Ty}
    (h : check p cx (.tail f is a ts) = .ok ()) (hts : ts.all TermScope.argOK = true) :
    TermScope.checkW p cx (.tail f is a ts) = .ok () := by
  unfold check at h
  unfold TermScope.checkW
  simp only [hts, Bool.not_true]
  exact h

/-- **`EntryOK` for a spawned thread** `tail f [] (v "a") ts` with argument
`ws : t`: the checker accepts the entry in the context `a : t` (any return
type `r`), the context's types are in scope (`TvOK`), and the argument is a
resource-free value of `t` at the empty cut, laid out at `t`. -/
theorem entryOK_of {p : Prog} {i : Nat} {th : TTh} {f : String} {ts : List Ty} {t r : Ty} {ws : List Word}
    (hterm : th.term = .tail f [] (.var "a") ts) (henv : th.env = [("a", t, ws)]) (hσ : th.σs = [])
    (hchk : check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok ())
    (htv : TvOK { vars := [("a", t, true)], ret := r })
    (hv : VRR (fun _ => 0) (Cut (Eg0 p) i S0) t (shp t) ws .zero) (hlay : Lay [] t t ws)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true) :
    EntryOK p i th := by
  have hRL : RLink (Cut (Eg0 p) i S0) := RLink_of (Coh_CE (Cut (Eg0 p) i S0)) (CohR_CE (Cut (Eg0 p) i S0))
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  refine ⟨fun _ => 0, { vars := [("a", t, true)], ret := r }, ?_, htv, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [hterm]
    exact ⟨check_sound p _ _ hchk, checkW_tail_of hchk hts,
      fun v hm => by simp only [List.mem_singleton] at hm; subst hm; exact hwt,
      fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩
  · intro k t' h; simp at h
  · intro x e hx
    obtain ⟨rfl, rfl⟩ := hfind x e hx
    refine ⟨t, ws, by rw [henv]; simp [lookupE], VRR_VR t hRL hv, by rw [hσ]; exact hlay⟩
  · intro _ _ _ _ _; trivial
  · refine ⟨fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _), fun k σ h => by rw [hσ] at h; simp at h,
      fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _)⟩
  · simp
  · refine ⟨fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h, fun σ h => by rw [hσ] at h; simp at h⟩
  · intro k; exact ⟨rfl, rfl, rfl⟩
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro _ _ _ _ _ _; rfl
  · refine ⟨by simp, by simp, fun y h => by simp at h, fun _ => .zero, fun x e hx _ => ?_, ?_⟩
    · obtain ⟨rfl, rfl⟩ := hfind x e hx
      exact ⟨t, ws, by rw [henv]; simp [lookupE], hv⟩
    · simp only [TermSound.Holds, List.filter, Bool.true_or, List.map, Res.sum_cons, Res.sum_nil, Res.add_zero]
      exact Res.le_refl _

#print axioms sysInvW_init
#print axioms ridOK_init
#print axioms runDRF_init
#print axioms runDRF_spawn
#print axioms entryOK_of

/-! ## `InitShape.vs0` at the spawn shape -/

/-- The `InitShape.vs0` condition. -/
def Vs0 (c0 : Cfg) : Prop :=
  ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th →
    th.vs.vRd = 0 ∧ th.vs.vCtrl = 0 ∧ th.vs.vPreBase = 0 ∧ th.vs.vRelSt = 0 ∧
      th.vs.coh = (fun _ => 0) ∧
      ∀ e ∈ th.env, ∀ w ∈ e.2.2, w.view = 0 ∧ w.rts = 0

/-- **`vs0` for spawned threads**: the initial view state (`VState.init`, the `TTh` default) and
constant argument words (`cst`). -/
theorem vs0_spawn {c0 : Cfg}
    (h : ∀ (i : Nat) (th : TTh), c0.ths[i]? = some th → th.vs = WeakMem.VState.init ∧
      ∃ (t : Ty) (vals : List WeakMem.Val), th.env = [("a", t, vals.map cst)]) : Vs0 c0 := by
  intro i th hth
  obtain ⟨hv, t, vals, he⟩ := h i th hth
  rw [hv, he]
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun e hm w hw => ?_⟩
  simp only [List.mem_singleton] at hm
  subst hm
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
  exact ⟨rfl, rfl⟩

/-- The spawn configuration on empty memory: thread `i` runs `tail f [] a ts` with `a : t` bound
to the constants `vals`, at the default thread state. -/
def spawn0 (thr : List (String × List Ty × Ty × List WeakMem.Val)) : Cfg :=
  { mem := #[], ths := (thr.map fun x =>
      ({ term := .tail x.1 [] (.var "a") x.2.1, env := [("a", x.2.2.1, x.2.2.2.map cst)] } : TTh)).toArray }

/-- **`InitShape.vs0` holds at `spawn0`.** -/
theorem spawn0_vs0 (thr : List (String × List Ty × Ty × List WeakMem.Val)) : Vs0 (spawn0 thr) := by
  refine vs0_spawn fun i th hth => ?_
  simp only [spawn0, List.getElem?_toArray, List.getElem?_map] at hth
  cases hx : thr[i]? with
  | none => rw [hx] at hth; cases hth
  | some x =>
      rw [hx] at hth
      cases hth
      exact ⟨rfl, x.2.2.1, x.2.2.2, rfl⟩

#print axioms vs0_spawn
#print axioms spawn0_vs0

end TermInit

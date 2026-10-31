import WeakCore.TermSpawnRun
import WeakCore.TermSpawnArg
import WeakCore.TermSpawnStep
import WeakCore.TermSpawnKidMem
/-!
# TermSpawnMid — a mid-run spawn

The configuration change of `Step.spawn`, abstracted from the new Op:
`spawnT c i par kid` replaces thread `i` by `par` and appends `kid` at index `c.ths.size`.
The global environment gains the kid's foreign promises (c1): `EgK Eg c`.
-/
namespace TermSpawnMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

-- The spawn's configuration change (memory unchanged): the `TermSpawnStep.spawnT`.
export TermSpawnStep (spawnT)

/-- The spawned global environment: the kid's foreign promises are every outstanding promise. -/
def EgK (Eg : GEnv) (c : Cfg) : GEnv := Eg.withFp (fun j => if j = c.ths.size then allProms c else Eg.fpOf j)

/-- The kid's shape, `V` the parent's post-barrier `vRelSt`. -/
structure KidShape (par kid : TTh) (f : String) (ts : List Ty) (t : Ty) (ws : List Word) : Prop where
  term : kid.term = .tail f [] (.var "a") ts
  env : kid.env = [("a", t, ws.map (TermSpawn.bumpW par.vs.vRelSt))]
  σs : kid.σs = []
  stack : kid.stack = []
  vs : kid.vs = { par.vs with mine := [] }
  promises : kid.promises = []
  nalloc : kid.nalloc = 0
  undefs : kid.undefs = 0
  tys : kid.tys = []

section shape
variable {c : Cfg} {i : Nat} {par kid : TTh}

@[simp] theorem spawnT_mem : (spawnT c i par kid).mem = c.mem := rfl
@[simp] theorem spawnT_pairs : (spawnT c i par kid).pairs = c.pairs := rfl
@[simp] theorem spawnT_lbase : (spawnT c i par kid).lbase = c.lbase := rfl
@[simp] theorem spawnT_bf : (spawnT c i par kid).boxFence = c.boxFence := rfl

theorem spawnT_size : (spawnT c i par kid).ths.size = c.ths.size + 1 := by
  simp [spawnT]

theorem spawnT_get_kid : (spawnT c i par kid).ths[c.ths.size]? = some kid := by
  have h : c.ths.size = (c.ths.set! i par).size := by simp
  simp only [spawnT]; rw [h, Array.getElem?_push_size]

theorem spawnT_get_par (hi : i < c.ths.size) : (spawnT c i par kid).ths[i]? = some par := by
  simp [spawnT, Array.getElem?_push, hi, Nat.ne_of_lt hi]

theorem spawnT_get_ne {j : Nat} (hj : j ≠ i) (hjn : j ≠ c.ths.size) :
    (spawnT c i par kid).ths[j]? = c.ths[j]? := by
  simp [spawnT, Array.getElem?_push, hjn, Ne.symm hj]

end shape

/-! ## The ghost foreign promises -/

theorem EgK_fp_kid (Eg : GEnv) (c : Cfg) : (EgK Eg c).fpOf c.ths.size = allProms c := by
  simp [EgK, GEnv.withFp]

theorem EgK_fp_ne (Eg : GEnv) (c : Cfg) {j : Nat} (h : j ≠ c.ths.size) : (EgK Eg c).fpOf j = Eg.fpOf j := by
  simp [EgK, GEnv.withFp, h]

theorem cutSto_EgK (Eg : GEnv) (c : Cfg) (j : Nat) : cutSto (EgK Eg c) j = cutSto Eg j := rfl

theorem cut_EgK_ne (Eg : GEnv) (c : Cfg) {j : Nat} (h : j ≠ c.ths.size) (S : AllocLabel → Prop) :
    Cut (EgK Eg c) j S = Cut Eg j S := by
  simp only [Cut, EgK_fp_ne Eg c h]; rfl

theorem InclS_cut_EgK (Eg : GEnv) (c : Cfg) (i j : Nat) (S S' : AllocLabel → Prop) :
    InclS (Cut Eg i S) (Cut (EgK Eg c) j S') :=
  ⟨rfl, fun _ _ f hc hf => cutSto_shared (Eg := EgK Eg c) (cutSto_sub hc) ⟨f, hf⟩, fun _ => Nat.le_refl _,
    fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

/-! ## Promises of the spawned configuration -/

theorem spawnT_get_cases {c : Cfg} {i : Nat} {par kid : TTh} {j : Nat} {t : TTh} (hi : i < c.ths.size)
    (h : (spawnT c i par kid).ths[j]? = some t) :
    (j = i ∧ t = par) ∨ (j = c.ths.size ∧ t = kid) ∨ (j ≠ i ∧ j ≠ c.ths.size ∧ c.ths[j]? = some t) := by
  by_cases hji : j = i
  · subst hji; rw [spawnT_get_par hi] at h; cases h; exact .inl ⟨rfl, rfl⟩
  · by_cases hjn : j = c.ths.size
    · subst hjn; rw [spawnT_get_kid] at h; cases h; exact .inr (.inl ⟨rfl, rfl⟩)
    · rw [spawnT_get_ne hji hjn] at h; exact .inr (.inr ⟨hji, hjn, h⟩)

theorem mem_allProms_spawnT {c : Cfg} {i : Nat} {th par kid : TTh} (hth : c.ths[i]? = some th)
    (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = []) {t : Ts} :
    t ∈ allProms (spawnT c i par kid) ↔ t ∈ allProms c := by
  have hi : i < c.ths.size := TermSpawn.lt_of_get hth
  rw [TermStepper.mem_allProms, TermStepper.mem_allProms]
  constructor
  · rintro ⟨j, tj, hj, ht⟩
    rcases spawnT_get_cases hi hj with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, -, hj'⟩
    · rw [hpp] at ht; cases ht
    · rw [hkp] at ht; cases ht
    · exact ⟨j, tj, hj', ht⟩
  · rintro ⟨j, tj, hj, ht⟩
    by_cases hji : j = i
    · subst hji; rw [hth] at hj; cases hj; rw [hnp] at ht; cases ht
    · have hjn : j ≠ c.ths.size := fun e => by
        subst e; simp at hj
      exact ⟨j, tj, by rw [spawnT_get_ne hji hjn]; exact hj, ht⟩

theorem PromAtG_EgK (Eg : GEnv) (c c' : Cfg) (a : Address) : PromAtG (EgK Eg c) c' a = PromAtG Eg c' a := rfl

theorem mem_PromAtG_spawnT {Eg : GEnv} {c : Cfg} {i : Nat} {th par kid : TTh} (hth : c.ths[i]? = some th)
    (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = []) (a : Address) {t : Ts} :
    t ∈ PromAtG (EgK Eg c) (spawnT c i par kid) a ↔ t ∈ PromAtG Eg c a := by
  rw [PromAtG_EgK]
  unfold PromAtG
  by_cases hw : WordUnitG Eg a
  · simp only [hw, ↓reduceIte]
  · by_cases hq : PredUG Eg a
    · simp only [hw, hq, ↓reduceIte, List.mem_filter, mem_allProms_spawnT hth hnp hpp hkp]; exact Iff.rfl
    · simp only [hw, hq, ↓reduceIte, mem_allProms_spawnT hth hnp hpp hkp]

/-- **The global shared holding after the spawn** (`SysInvN.held`). -/
theorem memHeldG_spawnT {Eg : GEnv} {c : Cfg} {i : Nat} {th par kid : TTh} {HS : Res} (hth : c.ths[i]? = some th)
    (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = []) (h : MemHeldG Eg c HS) :
    MemHeldG (EgK Eg c) (spawnT c i par kid) HS := by
  obtain ⟨L, Rl, hn, hc, hq, rfl, he⟩ := h
  refine ⟨L, Rl, hn, hc, hq, rfl, fun l hl => ⟨(he l hl).1, fun cl hcl => ?_⟩⟩
  obtain ⟨vals, hv, hk⟩ := (he l hl).2 cl hcl
  exact ⟨vals, fun o w hw => LatestNP_congrP (fun t _ _ _ => (mem_PromAtG_spawnT hth hnp hpp hkp _).symm) (hv o w hw), hk⟩

/-- `PromsOK` after the spawn, at the kid. -/
theorem promsOK_kid {Eg : GEnv} {c : Cfg} {i : Nat} {th par kid : TTh} (hth : c.ths[i]? = some th)
    (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = []) (t : Ts) :
    t ∈ kid.promises ++ (EgK Eg c).fpOf c.ths.size ↔ t ∈ allProms (spawnT c i par kid) := by
  rw [hkp, EgK_fp_kid, mem_allProms_spawnT hth hnp hpp hkp]; simp

/-! ## The kid's `ThSys` -/

-- No cell of the kid's cut is the kid's own (owners are live threads): the `TermSpawnKidMem.cutSto_kid_own`.
export TermSpawnKidMem (cutSto_kid_own)

/-- **The kid's `ThSys`**, at any striping `g` of the kid's index, given its entry typing (`hty`) and its
memory invariant (`hM`). -/
theorem thSys_kidM {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {g : G}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th par kid : TTh}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hgi : g.i = c.ths.size)
    (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hpp : par.promises = []) (hkp : kid.promises = [])
    (hty : ThInvRE p (Cut (EgK Eg c) c.ths.size (fun _ => False)) kid .zero ∧
      ThInvE p (Cut (EgK Eg c) c.ths.size (fun _ => False)) kid)
    (hM : MemInv g (Cut (EgK Eg c) c.ths.size (fun _ => False)) (stOf c.mem c.pairs kid)) :
    ThSys p g (spawnT c i par kid).mem (spawnT c i par kid).pairs kid
      (EgK Eg c) .zero .zero HS (fun _ => .zero) (fun _ => .zero) := by
  unfold ThSys; rw [hgi]
  refine ⟨fun _ => False, hty.1, hty.2, hM, ?_, ?_, ?_⟩
  · refine ⟨[], fun _ => .zero, List.nodup_nil, ?_, ?_, rfl, ?_⟩
    · intro l cl hq _
      obtain ⟨⟨c1, hc1, ho⟩, -⟩ := hq
      exact absurd ho (cutSto_kid_own hOL hc1)
    · intro l h; cases h
    · intro l h; cases h
  · exact MemHeldS_of_G (c := spawnT c i par kid) rfl hN.shty (promsOK_kid hth hnp hpp hkp)
      (memHeldG_spawnT hth hnp hpp hkp hN.held)
  · intro tw htw
    simp [stOf, hkp] at htw

/-! ## The kid's entry typing -/

/-- `res_move` from any source thread `i`, at any shape: a value at `i`'s cut, bumped to `V ≥` its seen
frontiers, at any cut containing `i`'s shared part. -/
theorem arg_move {Eg Eg2 : GEnv} {S S2 : AllocLabel → Prop} {i j : Nat} {V : Ts} {R0 : Ty} {sh : Shp}
    {res : List Word}
    (hI : InclS (Cut Eg i (fun _ => False)) (Cut Eg2 j S2)) (hS : SeenLE (Cut Eg i S) V)
    (hn : noOR R0 = true) (hv : VR (fun _ => 0) (Cut Eg i S) R0 sh res) :
    VR (fun _ => 0) (Cut Eg2 j S2) R0 sh (res.map (TermSpawn.bumpW V)) := by
  have h1 := VR_up _ _ _ _ (WLe_bumpS V res) hv
  have h2 : VR (fun _ => 0) (Cut Eg i (fun _ => False)) R0 sh (res.map (TermSpawn.bumpW V)) :=
    VR_unsee V R0 (Cut Eg i S) (Cut Eg i (fun _ => False)) _ _ _ (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl
      (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl))
      (fun _ _ h => h) (LocAbove_bumpS V res) h1 (fun _ => Nat.le_refl _)
  exact VR_transferS R0 (Cut Eg i (fun _ => False)) (Cut Eg2 j S2) _ _ _ hn (fun _ _ _ h => h) (fun _ _ _ h => h)
    rfl hI.prog hI.sto hI.ini hI.rini hI.pfr (fun _ h => (h : False).elim) hI.box h2

/-- `finv_entry` with the runtime type `rt` of the argument apart from its static type `t`. -/
theorem finv_entryR {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {th : TTh} {t rt r : Ty} {ws : List Word}
    {K : TEnv → List Word → Prop} (hK : ∀ E ws, K E ws)
    (henv : th.env = [("a", rt, ws)]) (hσ : th.σs = [])
    (hv : VRR (fun _ => 0) (Cut Eg i S) t (shp rt) ws .zero) (hlay : Lay [] t rt ws) :
    FInv (fun _ => 0) (Cut Eg i S) th.σs K { vars := [("a", t, true)], ret := r } th.env := by
  have hRL : RLink (Cut Eg i S) := RLink_of (Coh_CE (Cut Eg i S)) (CohR_CE (Cut Eg i S))
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k t' h; simp at h
  · intro x e hx
    obtain ⟨rfl, rfl⟩ := hfind x e hx
    refine ⟨rt, ws, by rw [henv]; simp [lookupE], VRR_VR t hRL hv, by rw [hσ]; exact hlay⟩
  · intro _ _ _ _ _; exact hK _ _
  · refine ⟨fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _), fun k σ h => by rw [hσ] at h; simp at h,
      fun k _ hk => by rw [hσ] at hk; exact absurd hk (Nat.not_lt_zero _)⟩
  · simp
  · refine ⟨fun k h => by simp [KEnv.ask] at h, fun k h => by simp [KEnv.ask] at h, fun σ h => by rw [hσ] at h; simp at h⟩
  · intro k; exact ⟨rfl, rfl, rfl⟩
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h
  · intro k h; simp [KEnv.ask] at h

/-- `entryR_of` with the runtime type `rt` apart from the static `t`. -/
theorem entryR_ofR {p : Prog} {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {th : TTh} {f : String}
    {ts : List Ty} {t rt r : Ty} {ws : List Word} (Tot : Res) (hp : Eg.prog = p)
    (hterm : th.term = .tail f [] (.var "a") ts) (henv : th.env = [("a", rt, ws)]) (hσ : th.σs = [])
    (hstk : th.stack = [])
    (hchk : check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok ())
    (htv : TvOK { vars := [("a", t, true)], ret := r })
    (hv : VRR (fun _ => 0) (Cut Eg i S) t (shp rt) ws .zero) (hlay : Lay [] t rt ws)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true) :
    ThInvRE p (Cut Eg i S) th Tot ∧ ThInvE p (Cut Eg i S) th := by
  have hfind : ∀ x e, ([("a", t, true)] : List (String × Ty × Bool)).find? (·.1 == x) = some e →
      x = "a" ∧ e = ("a", t, true) := by
    intro x e h
    by_cases hx : "a" = x
    · subst hx; simp at h; exact ⟨rfl, h.symm⟩
    · have : ("a" == x) = false := by simpa using hx
      simp [List.find?, this] at h
  have hE : EnvOK p (Cut Eg i S) := ⟨hp, Coh_CE (Cut Eg i S), CohR_CE (Cut Eg i S)⟩
  have hT : TypedK p (Cut Eg i S) { vars := [("a", t, true)], ret := r } th.term := by
    rw [hterm]
    exact ⟨check_sound p _ _ hchk, TermInit.checkW_tail_of hchk hts,
      fun v hm => by simp only [List.mem_singleton] at hm; subst hm; exact hwt,
      fun k hk _ => absurd hk (Nat.not_lt_zero _)⟩
  refine ⟨⟨fun _ => 0, Cut Eg i S, { vars := [("a", t, true)], ret := r }, Tot, .zero, rfl, hE, hT, htv,
    ⟨finv_entryR (fun _ _ => trivial) henv hσ hv hlay, ?_, ?_⟩, Res.add_zero _,
    (fun f rest h => by rw [hstk] at h; cases h), by rw [hterm, hσ]; exact dyFr_tail annNew (progTgts p) p _ f _ ts⟩,
    ⟨fun _ => 0, Cut Eg i S, { vars := [("a", t, true)], ret := r }, rfl, hE, hT.1, htv, ?_⟩⟩
  · rw [hstk]; intro _ _ _ _ _ _; rfl
  · refine HeldOK_mono (Rf := .zero) ⟨by simp, by simp, fun y h => by simp at h, fun _ => .zero, fun x e hx _ => ?_, ?_⟩
      (Res.zero_le _)
    · obtain ⟨rfl, rfl⟩ := hfind x e hx
      exact ⟨rt, ws, by rw [henv]; simp [lookupE], hv⟩
    · simp only [TermSound.Holds, List.filter, Bool.true_or, List.map, Res.sum_cons, Res.sum_nil, Res.add_zero]
      exact Res.le_refl _
  · rw [hstk]; exact ⟨finv_entryR (fun _ _ => trivial) henv hσ hv hlay, (fun _ _ h => by cases h),
    by rw [hterm, hσ]; exact dyFr_tail annNew (progTgts p) p _ f _ ts⟩

/-- **The kid's entry typing** at its cut, from the parent's argument value (static `t`, runtime `rt`;
resource-free, closed, copyable: ints and published pointers) and the callee check. The cut transport
`Cut Eg i S → Cut (EgK Eg c) c.ths.size _` is `arg_move` (shared part + `SeenLE` at the bump). -/
theorem kid_tyM {p : Prog} {Eg : GEnv} {c : Cfg} {i : Nat} {S : AllocLabel → Prop} {par kid : TTh}
    {f : String} {ts : List Ty} {t rt r : Ty} {ws : List Word}
    (hp : Eg.prog = p) (hK : KidShape par kid f ts rt ws)
    (ha : Ty.affine t = false) (htb : tb 0 t = true) (hd : TermScope.drf t = true)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true)
    (hchk : check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok ())
    (htv : TvOK { vars := [("a", t, true)], ret := r })
    (hv : VR (fun _ => 0) (Cut Eg i S) t (shp rt) ws) (hlay : Lay [] t rt ws)
    (hS : SeenLE (Cut Eg i S) par.vs.vRelSt) :
    ThInvRE p (Cut (EgK Eg c) c.ths.size (fun _ => False)) kid .zero ∧
      ThInvE p (Cut (EgK Eg c) c.ths.size (fun _ => False)) kid := by
  have hn : noOR t = true := noOR_of_aff _ [] ha (TermScope.rgnFree_of_drf _ hd)
  have hv' := arg_move (InclS_cut_EgK Eg c i c.ths.size (fun _ => False) (fun _ => False)) hS hn hv
  exact entryR_ofR .zero hp hK.term hK.env hK.σs hK.stack hchk htv (VR_VRR_copy_closed htb ha hv')
    (Lay_bumpS _ hlay) hts hwt

/-! ## The parent and the other threads -/

/-- Off the kid's index, `ThSys` does not see the kid's foreign promises. -/
theorem thSys_EgK {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {Eg : GEnv} {c : Cfg}
    {T H HS : Res} {cr db : Ts → Res} (hi : g.i ≠ c.ths.size) :
    ThSys p g mem pairs th (EgK Eg c) T H HS cr db ↔ ThSys p g mem pairs th Eg T H HS cr db := by
  unfold ThSys
  simp only [cut_EgK_ne Eg c hi]

/-- The parent's post-barrier state is the barrier's. -/
theorem stOf_par {mem : Memory} {pairs : List Ts} {th par : TTh} (hnp : th.promises = [])
    (hpar : par.vs = (fenceS (stOf mem pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs) :
    stOf mem pairs par = fenceS (stOf mem pairs th) .sy := by
  obtain ⟨h1, h2, h3, h4⟩ := hpar
  unfold stOf at *; unfold fenceS at *
  simp only at h1
  rw [h1, h2, h3, h4, hnp]

/-- **The parent's `ThSys`** after the spawn, given its post-step typing (`hParTy`), at any striping `g`
of the parent (no comparison of `gOf` before/after: on M0 both are `gOf c i`). -/
theorem thSys_parM {p : Prog} {g : G} {c : Cfg} {Eg : GEnv} {i : Nat}
    {th par kid : TTh} {T H HS : Res} {cr db : Ts → Res}
    (hT : ThSys p g c.mem c.pairs th Eg T H HS cr db) (hi : g.i ≠ c.ths.size)
    (hnp : th.promises = [])
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs)
    (hParTy : ∀ S, ThSysAt p g c.mem c.pairs th Eg T H HS cr db S →
      ThInvRE p (Cut Eg g.i S) par T ∧ ThInvE p (Cut Eg g.i S) par) :
    ThSys p g (spawnT c i par kid).mem (spawnT c i par kid).pairs par (EgK Eg c) T H HS cr db := by
  rw [thSys_EgK hi]
  obtain ⟨S, hRE, hE, hM, hP, hS, hC⟩ := hT
  have hty := hParTy S ⟨hRE, hE, hM, hP, hS, hC⟩
  have hs := stOf_par (mem := c.mem) (pairs := c.pairs) hnp hpar
  refine ⟨S, hty.1, hty.2, ?_, ?_, ?_, ?_⟩
  · show MemInv _ _ (stOf c.mem c.pairs par)
    rw [hs]; exact MemInv_fenceG _ hM
  · show MemHeldP _ (stOf c.mem c.pairs par) H
    rw [hs]; exact hP
  · show MemHeldS _ (stOf c.mem c.pairs par) HS
    rw [hs]; exact hS
  · intro tw htw
    simp [stOf, hpar.2.1] at htw

/-- **Another thread's `ThSys`** after the spawn, at any striping `g` off the kid's index. -/
theorem thSys_otherM {p : Prog} {g : G} {c : Cfg} {Eg : GEnv} {i : Nat}
    {tj par kid : TTh} {T H HS : Res} {cr db : Ts → Res}
    (hT : ThSys p g c.mem c.pairs tj Eg T H HS cr db) (hj : g.i ≠ c.ths.size) :
    ThSys p g (spawnT c i par kid).mem (spawnT c i par kid).pairs tj (EgK Eg c) T H HS cr db :=
  (thSys_EgK hj).2 hT

/-! ## The preservation statement (for review; proof assembled after the per-thread parts) -/

/-- A per-thread total extended by `.zero` at the kid's index. -/
def extZ (F : Nat → Res) (n : Nat) : Nat → Res := fun j => if j = n then .zero else F j
/-- A per-thread credit map extended by `fun _ => .zero` at the kid's index. -/
def extZT (F : Nat → Ts → Res) (n : Nat) : Nat → Ts → Res := fun j => if j = n then (fun _ => .zero) else F j

/-- The static side of the spawn's typing rule, as the kid's entry needs it. -/
structure KidEntryOK (p : Prog) (t : Ty) (f : String) (ts : List Ty) : Prop where
  aff : Ty.affine t = false
  tb : tb 0 t = true
  drf : TermScope.drf t = true
  tsDrf : ts.all TermScope.drf = true
  tsArg : ts.all TermScope.argOK = true
  wrap : TermScope.wrapOK t = true
  chk : ∃ r, check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok () ∧
    TvOK { vars := [("a", t, true)], ret := r }

-- `sysInvN_spawn` (the old `hg` statement) is superseded by `sysInvN_spawnS` (TermSpawnMidAsm).

end TermSpawnMid
#print axioms TermSpawnMid.memHeldG_spawnT
#print axioms TermSpawnMid.promsOK_kid
#print axioms TermSpawnMid.thSys_kidM
#print axioms TermSpawnMid.arg_move
#print axioms TermSpawnMid.kid_tyM
#print axioms TermSpawnMid.thSys_parM
#print axioms TermSpawnMid.thSys_otherM
#print axioms TermSpawnMid.mem_allProms_spawnT
#print axioms TermSpawnMid.spawnT_size
#print axioms TermSpawnMid.spawnT_get_kid
#print axioms TermSpawnMid.spawnT_get_par
#print axioms TermSpawnMid.spawnT_get_ne
#print axioms TermSpawnMid.EgK_fp_kid
#print axioms TermSpawnMid.EgK_fp_ne
#print axioms TermSpawnMid.cutSto_EgK
#print axioms TermSpawnMid.cut_EgK_ne
#print axioms TermSpawnMid.InclS_cut_EgK
#print axioms TermSpawnMid.spawnT_get_cases
#print axioms TermSpawnMid.PromAtG_EgK
#print axioms TermSpawnMid.mem_PromAtG_spawnT
#print axioms TermSpawnMid.finv_entryR
#print axioms TermSpawnMid.entryR_ofR
#print axioms TermSpawnMid.thSys_EgK
#print axioms TermSpawnMid.stOf_par

/-! (hygiene) axiom reports for theorems that had none. -/
#print axioms TermSpawnMid.spawnT_mem
#print axioms TermSpawnMid.spawnT_pairs
#print axioms TermSpawnMid.spawnT_lbase
#print axioms TermSpawnMid.spawnT_bf

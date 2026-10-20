import WeakCore.TermSpawnMid
import WeakCore.TermSpawnKidMem
/-!
# TermSpawnMidKid — the kid's full `ThSys` after a mid-run spawn (+ the `memInv_kidM`)
-/
namespace TermSpawnMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The kid's `ThSys`**, from the parent's `ThSys`, the spawn's shape and the typing rule's content. -/
theorem thSys_kidFull {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {g : G}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th par kid : TTh}
    {f : String} {ts : List Ty} {t rt r : Ty} {ws : List Word}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hgi : g.i = c.ths.size) (hth : c.ths[i]? = some th) (hnp : th.promises = [])
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs)
    (hK : KidShape par kid f ts rt ws)
    (ha : Ty.affine t = false) (htb : tb 0 t = true) (hd : TermScope.drf t = true)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true)
    (hchk : check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok ())
    (htv : TvOK { vars := [("a", t, true)], ret := r })
    (hArg : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      VR (fun _ => 0) (Cut Eg i S) t (shp rt) ws ∧ Lay [] t rt ws)
    (hU : ∀ q, Eg.sto (freshLabel g.lbase g.n g.i q) = none ∧ Eg.box (freshLabel g.lbase g.n g.i q) = none ∧
      Eg.ini (freshLabel g.lbase g.n g.i q) = 0 ∧ Eg.pfr (freshLabel g.lbase g.n g.i q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → m.loc.label ≠ freshLabel g.lbase g.n g.i q) :
    ThSys p g (spawnT c i par kid).mem (spawnT c i par kid).pairs kid
      (EgK Eg c) .zero .zero HS (fun _ => .zero) (fun _ => .zero) := by
  obtain ⟨S, hRE, hE, hM, hP, hS, hC⟩ := hN.thr i th hth
  have hp : Eg.prog = p := by
    obtain ⟨ρ, η, cx, Rf, Rs, hce, hEO, -⟩ := hRE
    have : (CE η).prog = (Cut Eg i S).prog := by rw [hce]; rfl
    exact this.symm.trans hEO.1
  have hSL : SeenLE (Cut Eg i S) par.vs.vRelSt := by
    rw [hpar.1]; exact (MemInv_fenceG .sy hM).2.2.2.2.1
  obtain ⟨hv, hlay⟩ := hArg S ⟨hRE, hE, hM, hP, hS, hC⟩
  have hty := kid_tyM (c := c) hp hK ha htb hd hts hwt hchk htv hv hlay hSL
  have hMk : MemInv g (Cut (EgK Eg c) c.ths.size (fun _ => False)) (stOf c.mem c.pairs kid) :=
    TermSpawnKidMem.memInv_kidM _ hM hnp hOL hN.shty hN.boxSto hN.boxtop hObs hU hK.promises hK.nalloc
  exact thSys_kidM hN hOL hgi hth hnp hpar.2.1 hK.promises hty hMk

/-- **`thr` after the spawn.** `hThrS`: the old threads' `ThSys` at the post-spawn striping (on M0 this is
`SysInvN.thr`, the stride `c.n` being unchanged); `hParTy`: the parent's continuation typing. -/
theorem thr_spawnT {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th par kid : TTh}
    {f : String} {ts : List Ty} {t rt r : Ty} {ws : List Word}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hth : c.ths[i]? = some th) (hnp : th.promises = [])
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs)
    (hK : KidShape par kid f ts rt ws)
    (ha : Ty.affine t = false) (htb : tb 0 t = true) (hd : TermScope.drf t = true)
    (hts : ts.all TermScope.argOK = true) (hwt : TermScope.wrapOK t = true)
    (hchk : check p { vars := [("a", t, true)], ret := r } (.tail f [] (.var "a") ts) = .ok ())
    (htv : TvOK { vars := [("a", t, true)], ret := r })
    (hArg : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      VR (fun _ => 0) (Cut Eg i S) t (shp rt) ws ∧ Lay [] t rt ws)
    (hU : ∀ q, Eg.sto (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.box (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      Eg.ini (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = 0 ∧
      Eg.pfr (freshLabel c.lbase (spawnT c i par kid).n c.ths.size q) = none ∧
      ∀ (t : Nat) (m : Msg), c.mem[t]? = some m →
        m.loc.label ≠ freshLabel c.lbase (spawnT c i par kid).n c.ths.size q)
    (hThrS : ∀ j tj, c.ths[j]? = some tj →
      ThSys p (gOf p k arch (spawnT c i par kid) j) c.mem c.pairs tj Eg (Tot j) (HP j) HS (cr j) (db j))
    (hParTy : ∀ S, ThSysAt p (gOf p k arch (spawnT c i par kid) i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      ThInvRE p (Cut Eg i S) par (Tot i) ∧ ThInvE p (Cut Eg i S) par) :
    ∀ j tj, (spawnT c i par kid).ths[j]? = some tj →
      ThSys p (gOf p k arch (spawnT c i par kid) j) (spawnT c i par kid).mem (spawnT c i par kid).pairs tj
        (EgK Eg c) (extZ Tot c.ths.size j) (extZ HP c.ths.size j) HS (extZT cr c.ths.size j) (extZT db c.ths.size j) := by
  intro j tj hj
  have hi := TermSpawn.lt_of_get hth
  rcases spawnT_get_cases hi hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, hjn, hj'⟩
  · simp only [extZ, extZT, Nat.ne_of_lt hi, ↓reduceIte]
    exact thSys_parM (hThrS j th hth) (Nat.ne_of_lt hi) hnp hpar hParTy
  · simp only [extZ, extZT, ↓reduceIte]
    exact thSys_kidFull hN hOL hObs rfl hth hnp hpar hK ha htb hd hts hwt hchk htv hArg hU
  · simp only [extZ, extZT, hjn, ↓reduceIte]
    exact thSys_otherM (hThrS j tj hj') hjn


/-- **The kid's labels** (`ThLbl`, for `ptrGL`): the kid's argument (static = runtime type `t`, as in
The `spawn f a T ts`) names only frontier/box labels; its stack is empty. -/
theorem thLbl_kid {p : Prog} {Eg : GEnv} {c : Cfg} {i : Nat} {S : AllocLabel → Prop} {par kid : TTh}
    {f : String} {ts : List Ty} {t : Ty} {ws : List Word}
    (hK : KidShape par kid f ts t ws) (ha : Ty.affine t = false) (hd : TermScope.drf t = true)
    (hv : VR (fun _ => 0) (Cut Eg i S) t (shp t) ws) (hlay : Lay [] t t ws)
    (hS : SeenLE (Cut Eg i S) par.vs.vRelSt) :
    TermPtrRts.ThLbl (EgK Eg c) kid := by
  have hn : noOR t = true := noOR_of_aff _ [] ha (TermScope.rgnFree_of_drf _ hd)
  have hv' := arg_move (InclS_cut_EgK Eg c i c.ths.size (fun _ => False) (fun _ => False)) hS hn hv
  have hL := Lay_bumpS par.vs.vRelSt hlay
  have hwc : wc t = some (ws.map (TermSpawn.bumpW par.vs.vRelSt)).length := by
    have h1 := hL.2.2.1
    cases hu : accs t with
    | none => simp [wc, hu] at h1
    | some us => simp only [wc, hu, Option.map_some]; rw [hL.1 us hu]
  have hl := TermPtrRts.labsIn_pubVR (G := fun l => (EgK Eg c).pfr l ≠ none ∨ (EgK Eg c).box l ≠ none)
    t (fun _ => 0) (Cut (EgK Eg c) c.ths.size (fun _ => False)) t _ (fun _ _ _ h => h)
    (fun l f h => Or.inl (by intro h2; change Eg.pfr l = some f at h; change Eg.pfr l = none at h2; rw [h] at h2; cases h2))
    (fun l B h => Or.inr (by intro h2; change Eg.box l = some B at h; change Eg.box l = none at h2; rw [h] at h2; cases h2))
    rfl hwc hL.2.2.2.1 hv'
  refine ⟨?_, fun fr hfr => by rw [hK.stack] at hfr; cases hfr⟩
  intro x rt0 ws0 hm w hw l hnm
  rw [hK.env] at hm
  simp only [List.mem_singleton, Prod.mk.injEq] at hm
  obtain ⟨-, rfl, rfl⟩ := hm
  obtain ⟨a0, g, hva, rfl⟩ := hnm
  exact hl w hw a0 g hva

/-- **The parent's labels** after a spawn: its env is `th.env` plus a numeric binding, its stack `th.stack`. -/
theorem thLbl_par {Eg : GEnv} {c : Cfg} {i : Nat} {th par : TTh} {x : String} {n : Nat}
    (hL : TermPtrRts.LblSto Eg c) (hth : c.ths[i]? = some th)
    (henv : par.env = (x, .int, [cst (.num n)]) :: th.env) (hst : par.stack = th.stack) :
    TermPtrRts.ThLbl (EgK Eg c) par := by
  obtain ⟨h1, h2⟩ := hL i th hth
  have hs : ∀ l f, Eg.pfr l = some f → (EgK Eg c).pfr l = some f := fun _ _ h => h
  have hb : ∀ l B, Eg.box l = some B → (EgK Eg c).box l = some B := fun _ _ h => h
  refine ⟨?_, fun fr hfr => ?_⟩
  · rw [henv]
    refine TermPtrRts.envLbl_cons (TermPtrRts.envLbl_mono hs hb h1) ?_
    intro w hw l hn
    obtain ⟨a', g, hv, -⟩ := hn
    simp [TermPtrRts.pubWords, TermPtrRts.sNo] at hw
    subst hw
    cases hv
  · rw [hst] at hfr
    exact TermPtrRts.envLbl_mono hs hb (h2 fr hfr)

end TermSpawnMid

#print axioms TermSpawnMid.thSys_kidFull
#print axioms TermSpawnMid.thr_spawnT
#print axioms TermSpawnMid.thLbl_kid
#print axioms TermSpawnMid.thLbl_par

import WeakCore.TermSpawnMidAsm
import WeakCore.TermSpawnMidBridge
import WeakCore.TermSpawnTy
import WeakCore.TermBoxG
import WeakCore.TermBoxO
/-!
# TermSpawnMidM0 — `sysInvN_spawnMid` on the M0 base

On M0 the stripe width is `c.n = max cap ths.size`; a spawn into an unborn stripe (`ths.size < c.n`)
keeps it (`spawnT_n`), so every [M0] hypothesis of `sysInvN_spawnMid` is the pre-state's
`SysInvN`/`freshU` fact (`kid_of_freshU` for the kid's stripe).
-/
namespace TermSpawnMid
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open TermSpawn TermSpawnGlobM
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (M0) A spawn into an unborn stripe keeps the stripe width. -/
theorem spawnT_n {c : Cfg} {i : Nat} {par kid : TTh} (hcap : c.ths.size < c.n) :
    (spawnT c i par kid).n = c.n := by
  have hs := spawnT_size (c := c) (i := i) (par := par) (kid := kid)
  have hc : (spawnT c i par kid).cap = c.cap := rfl
  unfold Cfg.n at hcap ⊢
  rw [hs, hc]
  omega

theorem gOf_spawnT {p : Prog} {k : Promises.Knobs} {arch : Arch} {c : Cfg} {i : Nat} {par kid : TTh}
    (hcap : c.ths.size < c.n) (j : Nat) : gOf p k arch (spawnT c i par kid) j = gOf p k arch c j := by
  unfold gOf; rw [spawnT_n hcap]; rfl

/-- **`SysInvN` across a mid-run spawn, M0 form**: the [M0] hypotheses discharged; `hcap` is `Spawn`'s own
premise at `cap := c.cap` (`c.n = max cap ths.size`). -/
theorem sysInvN_spawn_M0 {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th par kid : TTh} {f : String} {ts : List Ty} {t : Ty} {ws : List Word}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hth : c.ths[i]? = some th) (hnp : th.promises = []) (hcap : c.ths.size < c.cap)
    (hpar : par.vs = (fenceS (stOf c.mem c.pairs th) .sy).vs ∧ par.promises = [] ∧ par.nalloc = th.nalloc ∧
      par.undefs = th.undefs)
    (hPenv : ∃ (x : String) (w0 : Word), par.env = (x, .tid, [w0]) :: th.env ∧ par.stack = th.stack ∧
      ∀ w ∈ TermPtrRts.pubWords .tid [w0], ∀ l, TermPtrRts.Names l w → Eg.pfr l ≠ none ∨ Eg.box l ≠ none)
    (hTBp : TidBox Eg par) (hTBk : TidBox Eg kid)
    (hK : KidShape par kid f ts t ws)
    (hKE : KidEntryOK p t f ts)
    (hArg : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      VR (fun _ => 0) (Cut Eg i S) t (shp t) ws ∧ Lay [] t t ws)
    (hParTy : ∀ S, ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
      ThInvRE p (Cut Eg i S) par (Tot i) ∧ ThInvE p (Cut Eg i S) par) :
    SysInvN p k arch Init MintOK (spawnT c i par kid) (EgK Eg c) (extZ Tot c.ths.size) (extZ HP c.ths.size) HS
        (extZT cr c.ths.size) (extZT db c.ths.size) ∧
      OwnLive (EgK Eg c) (spawnT c i par kid) ∧ ObsAll (EgK Eg c) (spawnT c i par kid) := by
  have hcap : c.ths.size < c.n := Nat.lt_of_lt_of_le hcap (Nat.le_max_left _ _)
  have hn := spawnT_n (i := i) (par := par) (kid := kid) hcap
  have hg := gOf_spawnT (p := p) (k := k) (arch := arch) (i := i) (par := par) (kid := kid) hcap
  refine sysInvN_spawnMid hN hOL hObs hth hnp hpar hPenv hTBp hTBk hK hKE hArg
    (fun j tj h => by rw [hg]; exact hN.thr j tj h)
    (fun S h => hParTy S (by rw [hg] at h; exact h))
    (fun j tj h q hq => by rw [hn]; exact hN.fresh j tj h q hq)
    (fun q => by rw [hn]; exact (TermFreshU.kid_of_freshU hcap hN.freshU q).1)
    (fun q thq j h hj => by rw [hn]; exact hN.ownF q thq j h hj)
    (fun j => by rw [hn]; exact (TermFreshU.kid_of_freshU hcap hN.freshU j).2)
    (fun j l h => by unfold TgtOK at h ⊢; rw [hn]; exact h)
    (by rw [hn]; exact hN.freshU)


/-- (E2) Replacing thread `i` before the spawn replaces nothing the spawn keeps. -/
theorem spawnT_setC {c : Cfg} {i : Nat} {th1 par kid : TTh} :
    spawnT (TermSetTh.setC c i th1 c.trace) i par kid = spawnT c i par kid := by
  have e : (c.ths.set! i th1).set! i par = c.ths.set! i par := by
    apply Array.ext_getElem?
    intro j
    by_cases h : i = j
    · subst h; simp [Array.set!, Array.getElem?_setIfInBounds]
    · simp [Array.set!, h]
  unfold spawnT TermSetTh.setC
  simp only [e]

/-- **The spawn arm** (the `SpawnArmX`): `SysInvN` across a `Spawn` step at the run's capacity `cap = c.cap`
(`steps_cap`).  (E2) The parent first takes its next label `tidLabel` as the kid's box (`TermBox.sysInvN_box`:
`nalloc + 1`, `E_g` gains the published unit cell), then spawns (`sysInvN_spawn_M0` at the boxed configuration).
`hTy` is the spawn typing rule's kid entry (OpT.spawn); the argument and the parent's continuation are typed
from the site thread's invariant (`arg_of_site`, `par_of_site`). -/
theorem sysInvN_spawnStep {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cap : Nat} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hS : TermSpawnStep.Spawn p k arch cap c c') (hc : c.cap = cap)
    (hTy : ∀ (i : Nat) (x f : String) (a : At) (T : Ty) (ts : List Ty) (e : Expr) (th : TTh) (rt : Ty) (ws : List Word),
      c.ths[i]? = some th → th.term = .let_ x (.spawn f a T ts) e → evalAt th.env a = some (rt, ws) →
      KidEntryOK p T f ts) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' := by
  obtain ⟨i, x, f, a, T, ts, e, th, rt, ws, hth, hterm, hnp, hlt, hev, rfl⟩ := TermSpawnStep.Spawn.elim hS
  have hKE := hTy i x f a T ts e th rt ws hth hterm hev
  have hl : TermSpawnStep.tidLabel c i th = freshLabel c.lbase c.n i th.nalloc := rfl
  have hB := TermBox.sysInvN_box (tl := th.tidLbl) hN hOL hth hnp hl (.inl rfl)
  have hG := hN.fresh i th hth th.nalloc (Nat.le_refl _)
  have hOL1 := TermBox.ownLive_box (i := i) (th' := TermBox.thB th th.tidLbl) (tr := c.trace)
    (l := TermSpawnStep.tidLabel c i th) hOL
  have hObs1 := TermBox.obsAll_box (i := i) (th' := TermBox.thB th th.tidLbl) (tr := c.trace) hG.1 hG.2.2.2.1
    (fun t m ht he => by have := hG.2.2.2.2 t m ht he; rw [hnp] at this; cases this) hObs
  have hth1 := TermSetTh.setC_self (th' := TermBox.thB th th.tidLbl) (tr := c.trace) hth
  obtain ⟨hv, hpp, hna, hun⟩ := TermSpawnMidZ.spawnPar_hpar c i th x e
  obtain ⟨hpt, hpe, hpk, hps, hptl⟩ := TermSpawnMidZ.spawnPar_shape c i th x e
  have hcap : (TermSetTh.setC c i (TermBox.thB th th.tidLbl) c.trace).ths.size <
      (TermSetTh.setC c i (TermBox.thB th th.tidLbl) c.trace).cap := by
    rw [TermSetTh.setC_size]; show c.ths.size < c.cap; rw [hc]; exact hlt
  have hw0 : ∀ w ∈ TermPtrRts.pubWords .tid [cst (.loc ⟨TermSpawnStep.tidLabel c i th, 0⟩ 0)], ∀ l,
      TermPtrRts.Names l w → (TermBox.EgB Eg (TermSpawnStep.tidLabel c i th)).pfr l ≠ none ∨
        (TermBox.EgB Eg (TermSpawnStep.tidLabel c i th)).box l ≠ none := by
    intro w hw l hn
    refine .inl ?_
    obtain ⟨a', g, hva, rfl⟩ := hn
    have hw' : w = cst (.loc ⟨TermSpawnStep.tidLabel c i th, 0⟩ 0) := by
      simp [TermPtrRts.pubWords, TermPtrRts.sNo] at hw; exact hw
    subst hw'
    have e1 : a' = ⟨TermSpawnStep.tidLabel c i th, 0⟩ := by
      simp [cst, Promises.TVal.mk0] at hva; exact hva.1.symm
    subst e1
    simp
  have hTBp : TidBox (TermBox.EgB Eg (TermSpawnStep.tidLabel c i th)) (TermSpawnStep.spawnPar c i th x e) :=
    fun l' hl' => hB.tidBox i _ hth1 l' (by rw [hptl] at hl'; exact hl')
  have hTBk : TidBox (TermBox.EgB Eg (TermSpawnStep.tidLabel c i th)) (TermSpawnStep.spawnKid c i th f ts T ws) := by
    intro l' hl'
    have e1 : TermSpawnStep.tidLabel c i th = l' := Option.some.inj hl'
    subst e1
    exact ⟨TermBox.EgB_sto_self, TermBox.EgB_pfr_self⟩
  unfold TermSpawnStep.spawnCfg
  rw [← spawnT_setC (th1 := TermBox.thB th th.tidLbl)]
  exact ⟨_, _, _, _, _, _, sysInvN_spawn_M0 hB hOL1 hObs1 hth1 hnp hcap ⟨by rw [hv]; rfl, hpp.trans hnp, hna, hun⟩
    ⟨x, _, hpe, hpk, hw0⟩ hTBp hTBk (TermSpawnMidZ.spawnKid_shape c i th x e f ts T ws) hKE
    (fun S hS => arg_of_site hS.2.1 hterm hev)
    (fun S hS => par_of_site hterm hpt hpe hps hpk
      ⟨by rw [Cut_sto]; exact TermBox.cutSto_EgB_self, TermBox.EgB_pfr_self⟩ hS.1 hS.2.1)⟩


/-- **The spawn typing content from the invariant** (`hTy` of `sysInvN_spawnStep`): inverting `OpT.spawn`
under the site thread's `ThSys` gives the kid's entry (no obligation). -/
theorem spawnTy_of_sysInvN {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) :
    ∀ (i : Nat) (x f : String) (a : At) (T : Ty) (ts : List Ty) (e : Expr) (th : TTh) (rt : Ty) (ws : List Word),
      c.ths[i]? = some th → th.term = .let_ x (.spawn f a T ts) e → evalAt th.env a = some (rt, ws) →
      KidEntryOK p T f ts := by
  intro i x f a T ts e th rt ws hth hterm hev
  obtain ⟨S0, hS0⟩ := hN.thr i th hth
  obtain ⟨ρ0, η0, cx0, hCE0, hEnv0, hT0, hrest0⟩ := hS0.2.1
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop _ => exact kidEntryOK_of (spawnPrem_of hop)

/-- **The spawn arm, closed**: `sysInvN_spawnStep` with `hTy := spawnTy_of_sysInvN hN`. -/
theorem sysInvN_spawnArm {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {cap : Nat} {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    (hN : SysInvN p k arch Init MintOK c Eg Tot HP HS cr db) (hOL : OwnLive Eg c) (hObs : ObsAll Eg c)
    (hS : TermSpawnStep.Spawn p k arch cap c c') (hc : c.cap = cap) :
    ∃ (Eg' : GEnv) (Tot' HP' : Nat → Res) (HS' : Res) (cr' db' : Nat → Ts → Res),
      SysInvN p k arch Init MintOK c' Eg' Tot' HP' HS' cr' db' ∧ OwnLive Eg' c' ∧ ObsAll Eg' c' :=
  sysInvN_spawnStep hN hOL hObs hS hc (spawnTy_of_sysInvN hN)

/-- A spawn keeps the capacity. -/
theorem Spawn.cap_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c c' : Cfg}
    (h : TermSpawnStep.Spawn p k arch cap c c') : c'.cap = c.cap := by
  obtain ⟨i, x, f, a, T, ts, e, th, rt, ws, -, -, -, -, -, rfl⟩ := TermSpawnStep.Spawn.elim h
  rfl

/-- **The capacity along a run** with spawns. -/
theorem StepsG.cap_eq {p : Prog} {k : Promises.Knobs} {arch : Arch} {cap : Nat} {c0 c : Cfg}
    (h : TermSpawnStep.StepsG p k arch (TermSpawnStep.Spawn p k arch cap) c0 c) : c.cap = c0.cap :=
  TermSpawnStep.stepsG_pres (P := fun c => c.cap = c0.cap)
    (fun _ _ hs e => (TermStep.step_cap hs).trans e) (fun _ _ hs e => (Spawn.cap_eq hs).trans e) h rfl

end TermSpawnMid

#print axioms TermSpawnMid.spawnT_n
#print axioms TermSpawnMid.sysInvN_spawn_M0
#print axioms TermSpawnMid.sysInvN_spawnStep
#print axioms TermSpawnMid.spawnTy_of_sysInvN
#print axioms TermSpawnMid.sysInvN_spawnArm
#print axioms TermSpawnMid.StepsG.cap_eq
#print axioms TermSpawnMid.gOf_spawnT

/-! (hygiene) axiom reports for theorems that had none. -/
#print axioms TermSpawnMid.Spawn.cap_eq
#print axioms TermSpawnMid.spawnT_setC

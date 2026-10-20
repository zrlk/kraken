import WeakCore.TermOverCrBII

/-! # TermOverCrOwnCommon: the step-kind–independent glue of the own cover (M5)

Shared by `OpenOverCrOwnA` and `OpenOverCrOwnC`; no step-kind parameter.
* `cutT_self`: the post-step cut of the stepping thread is the stepper's witness `E'`
  (at `E'.seen`; `seen` is irrelevant to `OverCrE`, `overCrE_cutT`);
* `cutT_sto` / `cutT_pfr` / …: the field equalities;
* `pre_overCrE`: the pre-state's cover at `CE η`, from `OverCrG` at `crPl`;
* `old_of_new` / `old_of_newP`: a post-step own frontier cell is an old cell (never fresh), with
  its old frontier (given the stepper's `PfrG` at `PubAt`, off `publish`).
-/

namespace TermOverCrOwnCommon
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 c c' : Cfg}
  {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
  {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **The post-step cut is the stepper's witness** (TermMain's `hCut`). -/
theorem cutT_self {E' : TEnv} {Tot' : Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hRE : ThInvRE p E' r.2.2 Tot') :
    Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen = E' := by
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) :=
    Y.1 ▸ hF
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  have hself := Cut_self (g := gOf p k arch c i) hF0 hfr
  have hEE : CE E' = E' := by
    obtain ⟨_, η', _, _, _, hce', -⟩ := hRE
    rw [← hce']
    rfl
  have hfs : fpSync Eg c' i = Eg.fpOf i := fpSync_self X.inv.proms X.inv.fpfree X.hth X.ho
  unfold EgT
  exact (Cut_withFp (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') (fpSync Eg c') _ E'.seen hfs).trans
    (hself.symm.trans hEE)
#print axioms TermOverCrOwnCommon.cutT_self

end

section
variable {X : GEnv} {i : Nat} {E' : TEnv}

/-- `OverCrE` at the post-step cut (any `seen`) is `OverCrE` at `E'`. -/
theorem overCrE_cutT (hcut : Cut X i E'.seen = E') (Sj : AllocLabel → Prop) {s : St} {cr : Ts → Res}
    {l : AllocLabel} {cl : Cell} :
    TermOverCr.OverCrE (Cut X i Sj) s cr l cl ↔ TermOverCr.OverCrE E' s cr l cl := by
  constructor
  · intro h
    have h' : TermOverCr.OverCrE (Cut X i E'.seen) s cr l cl := h
    rw [hcut] at h'
    exact h'
  · intro h
    have h' : TermOverCr.OverCrE (Cut X i E'.seen) s cr l cl := by rw [hcut]; exact h
    exact h'
#print axioms TermOverCrOwnCommon.overCrE_cutT

theorem cutT_sto (hcut : Cut X i E'.seen = E') (Sj : AllocLabel → Prop) : (Cut X i Sj).sto = E'.sto := by
  have h := congrArg TEnv.sto hcut
  exact h
#print axioms TermOverCrOwnCommon.cutT_sto

theorem cutT_pfr (hcut : Cut X i E'.seen = E') : X.pfr = E'.pfr := by
  have h := congrArg TEnv.pfr hcut
  exact h
#print axioms TermOverCrOwnCommon.cutT_pfr

theorem cutT_ini (hcut : Cut X i E'.seen = E') : X.ini = E'.ini := by
  have h := congrArg TEnv.ini hcut
  exact h
#print axioms TermOverCrOwnCommon.cutT_ini

theorem cutT_rini (hcut : Cut X i E'.seen = E') : X.rini = E'.rini := by
  have h := congrArg TEnv.rini hcut
  exact h
#print axioms TermOverCrOwnCommon.cutT_rini

theorem cutT_tid (hcut : Cut X i E'.seen = E') : E'.tid = i := by
  have h := congrArg TEnv.tid hcut
  exact h.symm
#print axioms TermOverCrOwnCommon.cutT_tid

theorem cutT_fp (hcut : Cut X i E'.seen = E') : X.fpOf i = E'.fp := by
  have h := congrArg TEnv.fp hcut
  exact h
#print axioms TermOverCrOwnCommon.cutT_fp

end

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 c c' : Cfg}
  {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat} {th : TTh}
  {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **The pre-state's own cover at `CE η`**, credits `cr i + pl i`. -/
theorem pre_overCrE {pl : Nat → Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs) (hG : TermOverCr.OverCrG Eg c (crPl cr pl))
    {l : AllocLabel} {cl : Cell} (hs : (CE η).sto l = some cl) (ho : cl.owner = some i)
    (hp : (CE η).pfr l ≠ none) :
    TermOverCr.OverCrE (CE η) (stOf c.mem c.pairs th) (fun t => cr i t + pl i t) l cl := by
  rw [Y.1] at hs hp ⊢
  exact hG i th S X.hth l cl hs ho hp
#print axioms TermOverCrOwnCommon.pre_overCrE

/-- **Values transfer along the step** (`ValOfR_mono` from `EFoot`: cells, frontiers and boxes
change only from none, counts only grow). -/
theorem valOfR_step {E' : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    {T : Ty} {ws : List Word} {R0 : Res} (h : ValOfR (CE η) T ws R0) : ValOfR E' T ws R0 := by
  obtain ⟨hpg, htd, hsto, hbox, hini, hpfr, -, -, -, hri, -⟩ := hF
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  refine ValOfR_mono hpg.symm htd.symm (fun l cl hc => ?_) (fun l => (hini l).1) h (fun l f hf => ?_)
    (fun l B hB => ?_) hri
  · rcases hsto l with e | ⟨hFr, -⟩
    · rw [e]; exact hc
    · have hg := (hfr l hFr).1
      rw [Y.1] at hc
      have := cutSto_sub hc
      rw [hg] at this; cases this
  · rcases hpfr l with e | ⟨e, -⟩ | ⟨-, e, -⟩
    · rw [e]; exact hf
    · rw [e] at hf; cases hf
    · rw [e] at hf; cases hf
  · rcases hbox l with e | ⟨hFr, -⟩
    · rw [e]; exact hB
    · have hg := (hfr l hFr).2.1
      rw [Y.1] at hB
      have hB' : Eg.box l = some B := hB
      rw [hg] at hB'; cases hB'
#print axioms TermOverCrOwnCommon.valOfR_step

/-- **A post-step frontier cell is an old cell** (never one of the step's fresh labels), and its
old frontier is either the new one or none (a frontier planted in the step). -/
theorem old_of_new {E' : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    {l : AllocLabel} {cl : Cell} (hs : E'.sto l = some cl) (hp : E'.pfr l ≠ none) :
    (CE η).sto l = some cl ∧ ((CE η).pfr l = E'.pfr l ∨ (CE η).pfr l = none) := by
  obtain ⟨-, -, hsto, -, -, hpfr, -⟩ := hF
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  rcases hsto l with e | ⟨hFr, -⟩
  · refine ⟨e ▸ hs, ?_⟩
    rcases hpfr l with e2 | ⟨e2, -⟩ | ⟨-, -, e2⟩
    · exact .inl e2.symm
    · exact .inr e2
    · rw [e2] at hs; cases hs
  · have hg := hfr l hFr
    have hEs : (CE η).sto l = none := by
      rw [Y.1]
      show cutSto Eg i l = none
      unfold cutSto
      split
      · exact hg.1
      · rfl
    have hEp : (CE η).pfr l = none := by rw [Y.1]; exact hg.2.2
    rcases hpfr l with e2 | ⟨-, F, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, e2⟩
    · exact absurd (e2.trans hEp) hp
    · rw [hEs] at hc1; cases hc1
    · rw [e2] at hs; cases hs
#print axioms TermOverCrOwnCommon.old_of_new

/-- `old_of_new` with a frontier tag (`PfrG` at `P`; TermMain's `hPfrP` has `P = PubAt th`) off `P`:
the old frontier is the new one. -/
theorem old_of_newP {E' : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    {P : AllocLabel → Prop} (hPf : PfrG { gOf p k arch c i with pf := P } (CE η) E')
    {l : AllocLabel} {cl : Cell} (hnp : ¬ P l) (hs : E'.sto l = some cl)
    (hp : E'.pfr l ≠ none) :
    (CE η).sto l = some cl ∧ (CE η).pfr l = E'.pfr l := by
  obtain ⟨h1, -⟩ := old_of_new X Y hF hs hp
  refine ⟨h1, ?_⟩
  by_cases e : E'.pfr l = (CE η).pfr l
  · exact e.symm
  · exact absurd (hPf l (by rw [h1]; exact Option.some_ne_none _) e) hnp
#print axioms TermOverCrOwnCommon.old_of_newP

end

end TermOverCrOwnCommon

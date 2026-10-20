import WeakCore.TermMainDefs
import WeakCore.TermOwnG0Defs

/-!
# TermInterf: interference freedom (S8c)

An idle thread's invariants survive another thread's step (thread step or
promise step).  Each theorem `X_holds` below has exactly the type of the
`Obligations` field `X` of `TermMain` (possibly behind explicit hypotheses
named in its docstring), so the field can be replaced by the theorem.
-/

namespace TermInterf

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-! ## Moving a frame along a growing environment -/

/-- A frame's view moves to any `CE`-shaped environment containing it with the
same program, thread and a larger `seen` (the frame part of `S8c`). -/
theorem ThInvRE_incl {p : Prog} {E E' : TEnv} {th : TTh} {Tot : Res} (hce' : CE E' = E')
    (hp : E'.prog = E.prog) (ht : E'.tid = E.tid) (hI : Incl E E') (hS : ∀ l, E.seen l → E'.seen l)
    (h : ThInvRE p E th Tot) : ThInvRE p E' th Tot := by
  obtain ⟨ρ, η, cx, Rf, Rs, hce, hEO, hT, htv, hFI, hsum⟩ := h
  have hs : η.sto = E.sto := by rw [← hce]; rfl
  have hi : η.ini = E.ini := by rw [← hce]; rfl
  have hpf : η.pfr = E.pfr := by rw [← hce]; rfl
  have hse : η.seen = E.seen := by rw [← hce]; rfl
  have hbx : η.box = E.box := by rw [← hce]; rfl
  have hri : η.rini = E.rini := by rw [← hce]; rfl
  have hpr : η.prog = E.prog := by rw [← hce]; rfl
  have htd : η.tid = E.tid := by rw [← hce]; rfl
  have he : Ext η (η.withSto E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini) :=
    Ext_withSto hEO.2.1 (fun l c h => hI.sto l c (hs ▸ h)) (fun l => hi ▸ hI.ini l)
      (fun l f h => hI.pfr l f (hpf ▸ h)) (fun l h => hS l (hse ▸ h)) (fun l B h => hI.box l B (hbx ▸ h))
      (Nat.le_refl _) E'.fp E'.rini (fun l => hri ▸ hI.rini l)
  refine ⟨ρ, η.withSto E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini, cx, Rf, Rs, ?_,
    ⟨hEO.1, he.1, he.2.2.2.2.2.2.2.2.2.2.1⟩, hT, htv, FInvR_ext hEO.2.1 hEO.2.2 he hFI, hsum⟩
  rw [← hce']
  have e1 : η.prog = E'.prog := hpr.trans hp.symm
  have e2 : η.tid = E'.tid := htd.trans ht.symm
  unfold CE TEnv.withSto
  simp only [e1, e2]

/-- `ThInvRE_incl` for the plain invariant. -/
theorem ThInvE_incl {p : Prog} {E E' : TEnv} {th : TTh} (hce' : CE E' = E')
    (hp : E'.prog = E.prog) (ht : E'.tid = E.tid) (hI : Incl E E') (hS : ∀ l, E.seen l → E'.seen l)
    (h : ThInvE p E th) : ThInvE p E' th := by
  obtain ⟨ρ, η, cx, hce, hEO, hT, htv, hFI, hrp⟩ := h
  have hs : η.sto = E.sto := by rw [← hce]; rfl
  have hi : η.ini = E.ini := by rw [← hce]; rfl
  have hpf : η.pfr = E.pfr := by rw [← hce]; rfl
  have hse : η.seen = E.seen := by rw [← hce]; rfl
  have hbx : η.box = E.box := by rw [← hce]; rfl
  have hri : η.rini = E.rini := by rw [← hce]; rfl
  have hpr : η.prog = E.prog := by rw [← hce]; rfl
  have htd : η.tid = E.tid := by rw [← hce]; rfl
  have he : Ext η (η.withSto E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini) :=
    Ext_withSto hEO.2.1 (fun l c h => hI.sto l c (hs ▸ h)) (fun l => hi ▸ hI.ini l)
      (fun l f h => hI.pfr l f (hpf ▸ h)) (fun l h => hS l (hse ▸ h)) (fun l B h => hI.box l B (hbx ▸ h))
      (Nat.le_refl _) E'.fp E'.rini (fun l => hri ▸ hI.rini l)
  refine ⟨ρ, η.withSto E'.sto E'.ini E'.pfr E'.seen E'.box η.rid E'.fp E'.rini, cx, ?_,
    ⟨hEO.1, he.1, he.2.2.2.2.2.2.2.2.2.2.1⟩, hT, htv, FInv_ext hEO.2.1 he hFI, hrp⟩
  rw [← hce']
  have e1 : η.prog = E'.prog := hpr.trans hp.symm
  have e2 : η.tid = E'.tid := htd.trans ht.symm
  unfold CE TEnv.withSto
  simp only [e1, e2]

/-- Only `fp` differs between a cut of `X` and of `X.withFp f`. -/
theorem Incl_cut_withFp (X : GEnv) (f : Nat → List Ts) (j : Nat) (S : AllocLabel → Prop) :
    Incl (Cut X j S) (Cut (X.withFp f) j S) :=
  ⟨rfl, fun _ _ h => h, fun _ => Nat.le_refl _, fun _ _ h => h, fun _ _ h => h, fun _ => Nat.le_refl _⟩

/-- A cut moves along a growing `E_g`, keeping both invariants of a frame. -/
theorem frame_move {p : Prog} {Eg Eg' : GEnv} {j : Nat} {S : AllocLabel → Prop} {th : TTh} {Tot : Res}
    (hp : Eg'.prog = Eg.prog) (hI : Incl (Cut Eg j S) (Cut Eg' j S))
    (h1 : ThInvRE p (Cut Eg j S) th Tot) (h2 : ThInvE p (Cut Eg j S) th) :
    ThInvRE p (Cut Eg' j S) th Tot ∧ ThInvE p (Cut Eg' j S) th :=
  ⟨ThInvRE_incl (E := Cut Eg j S) (CE_Cut _ _ _) hp rfl hI (fun _ h => h) h1,
    ThInvE_incl (E := Cut Eg j S) (CE_Cut _ _ _) hp rfl hI (fun _ h => h) h2⟩

/-! ## The global footprint of a thread step -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The thread step's global footprint (`EFoot_post` at the stepping cut). -/
theorem gfoot_of {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    GFoot (gOf p k arch c i) Eg (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') th.nalloc r.2.2.nalloc
      c.mem.size := by
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  exact EFoot_post hF0 (X.inv.gfresh X.hth _) (X.inv.vwr i th X.hth)

/-- **T16a `interfFrameT`.** -/
theorem interfFrameT_holds : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      ThInvRE p (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) thj (Tot j) ∧ ThInvE p (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) thj := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji _ hold
  have hgf := gfoot_of X Y Z
  have hI := (Cut_other hgf (j := j) hji Sj).1
  exact frame_move hgf.1 (hI.trans (Incl_cut_withFp _ _ j Sj)) hold.1 hold.2.1

end

/-! ## The ghost plant -/

/-- Under `PlantSpec` the plant only adds frontiers: every cut grows. -/
theorem Incl_cut_plant {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n : Nat} (hP : PlantSpec Eg P j n)
    (i : Nat) (S : AllocLabel → Prop) : Incl (Cut Eg i S) (Cut (plantG Eg P N) i S) := by
  have hpf : ∀ l f, Eg.pfr l = some f → (plantG Eg P N).pfr l = some f := fun l f hf => by
    cases e : P l with
    | none => simp only [plantG, e]; exact hf
    | some f' => rw [(hP l f' e).1] at hf; cases hf
  refine ⟨rfl, fun l c hc => ?_, plantG_ini_le Eg P N, hpf, fun _ _ h => h, fun _ => Nat.le_refl _⟩
  obtain ⟨h1, h2⟩ := cutSto_some.1 hc
  exact cutSto_some.2 ⟨h1, h2.imp id fun ⟨f, hf⟩ => ⟨f, hpf l f hf⟩⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The `plantSpec` field's type (P2), the hypothesis of the promise-step lemmas. -/
def PlantSpecF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size

/-- **P4a `interfFrameP`**, given P2 (`plantSpec`). -/
theorem interfFrameP_holds (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      ThInvRE p (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) thj (Tot j') ∧ ThInvE p (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) thj := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj _ _ hold
  exact frame_move (Eg := Eg) rfl ((Incl_cut_plant (N := plantN c Eg j a v w) (hspec X) j' Sj).trans (Incl_cut_withFp _ _ j' Sj)) hold.1 hold.2.1

end

/-! ## Memory growing away from a label -/

/-- Cut of `X.withFp f`: only `fp` differs. -/
theorem cutSto_withFp (X : GEnv) (f : Nat → List Ts) (j : Nat) : cutSto (X.withFp f) j = cutSto X j := rfl

/-- (per-event shape) Memory grown by messages none of which is at `a.label`
keeps the latest word at `a`. -/
theorem LatestNP_grow {mem mem' : Memory} {P : List Ts} {a : Address} {w : Word}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc.label ≠ a.label)
    (h : LatestNP mem P a w) : LatestNP mem' P a w := by
  obtain ⟨t, m, htP, hm, hl, hw, hlast⟩ := h
  refine ⟨t, m, htP, by rw [hpre t (lt_of_get hm)]; exact hm, hl, hw, fun t' m' hlt hm' hl' => ?_⟩
  rcases Nat.lt_or_ge t' mem.size with h1 | h1
  · rw [hpre t' h1] at hm'; exact hlast t' m' hlt hm' hl'
  · exact absurd (congrArg Address.label hl') (hnew t' m' h1 hm')

theorem CellOKR_mono {η₁ η₂ : TEnv} (hp : η₁.prog = η₂.prog) (ht : η₁.tid = η₂.tid) (hI : Incl η₁ η₂)
    {n nr : Nat} {T : Ty} {vals : List Word} {R : Res} (h : CellOKR η₁ n nr T vals R) : CellOKR η₂ n nr T vals R := by
  rcases h with ⟨h1, h2⟩ | ⟨N, e, us, Rs, hTe, hu, hn, hl, hRs, hR, hj⟩
  · exact Or.inl ⟨h1, ValOfR_mono hp ht hI.sto hI.ini h2 hI.pfr hI.box hI.rini⟩
  · exact Or.inr ⟨N, e, us, Rs, hTe, hu, hn, hl, hRs, hR,
      fun j Rj h1 h2 => slotR_imp (hj j Rj h1 h2) rfl
        (fun h => ValOfR_mono hp ht hI.sto hI.ini h hI.pfr hI.box hI.rini)⟩

/-- A private cell's entry moves when its cell, count and promises stay, the
environment grows, and memory grows away from it. -/
theorem HeldEntry_priv_move {E E' : TEnv} {s s' : St} {l : AllocLabel} {R : Res}
    (hp : E.prog = E'.prog) (ht : E.tid = E'.tid) (hI : Incl E E') (hpv : Priv E l) (hpv' : Priv E' l)
    (hsto : E'.sto l = E.sto l) (hini : E'.ini l = E.ini l) (hri : E'.rini l = E.rini l) (hpr : s'.promises = s.promises)
    (hpre : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), s.mem.size ≤ t → s'.mem[t]? = some m → m.loc.label ≠ l)
    (h : HeldEntry E s l R) : HeldEntry E' s' l R := by
  refine ⟨fun h0 => h.1 (hsto ▸ h0), fun c hc => ?_⟩
  obtain ⟨vals, hv, hk⟩ := h.2 c (hsto ▸ hc)
  refine ⟨vals, fun o w hw => ?_, by rw [hini, TEnv.rc_congr hini hri]; exact CellOKR_mono hp ht hI hk⟩
  have h1 := hv o w hw
  rw [PromAt_own (a := ⟨l, o⟩) hpv] at h1
  rw [PromAt_own (a := ⟨l, o⟩) hpv', hpr]
  exact LatestNP_grow hpre (fun t m h1 h2 => hnew t m h1 h2) h1

/-- (H) `gfoot_ini_other` for `rini`: unchanged at a cell that is not the stepper's. -/
theorem gfoot_rini_other {g : G} {Eg Eg' : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg' n n' v)
    (hfr : GFreshE g Eg n n') {l : AllocLabel} {cl : Cell} (hc : Eg.sto l = some cl)
    (ho : cl.owner ≠ some g.i) : Eg'.rini l = Eg.rini l := by
  rcases hf.2.2.2.2.2.2 l with e | hF | ⟨c', hc', ho'⟩
  · exact e
  · rw [(hfr l hF).1] at hc; cases hc
  · rw [hc] at hc'; cases hc'; exact absurd ho' ho

/-- `MemHeldP` moves when the private labels coincide and every entry moves. -/
theorem MemHeldP_move {E E' : TEnv} {s s' : St} {H : Res}
    (hpriv : ∀ l, Priv E' l ↔ Priv E l) (hsto : ∀ l, Priv E l → E'.sto l = E.sto l)
    (hent : ∀ l R, Priv E l → HeldEntry E s l R → HeldEntry E' s' l R)
    (h : MemHeldP E s H) : MemHeldP E' s' H := by
  obtain ⟨L, Rl, hn, hc, hq, hH, he⟩ := h
  exact ⟨L, Rl, hn, fun l c hpv hs => hc l c ((hpriv l).1 hpv) (by rw [← hsto l ((hpriv l).1 hpv)]; exact hs),
    fun l hl => (hpriv l).2 (hq l hl), hH, fun l hl => hent l _ (hq l hl) (he l hl)⟩

/-! ## Private cells of an idle thread across a global step -/

/-- A cell of `j ≠ g.i` keeps its sharing status... at private cells: the
private labels of `j` are the same before and after a global step of `g.i`. -/
theorem Priv_gfoot {g : G} {Eg Eg2 : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg2 n n' v)
    {j : Nat} (hj : j ≠ g.i) (f : Nat → List Ts) (S S' : AllocLabel → Prop) (l : AllocLabel) :
    Priv (Cut (Eg2.withFp f) j S') l ↔ Priv (Cut Eg j S) l := by
  have hle := hf.le
  constructor
  · rintro ⟨⟨c, hc, ho⟩, hp⟩
    have hc2 : Eg2.sto l = some c := cutSto_sub (Eg := Eg2) hc
    have ho' : c.owner = some j := ho
    have hc1 : Eg.sto l = some c := by
      rcases hf.2.1 l with e | ⟨-, -, -, T, hT⟩
      · rw [← e]; exact hc2
      · rw [hT] at hc2; cases hc2; exact absurd ho'.symm (by simpa using hj)
    have hp1 : Eg.pfr l = none := by
      cases e : Eg.pfr l with
      | none => rfl
      | some f0 => have := hle.pfr l f0 e; exact absurd (hp.symm.trans this) (by simp)
    exact ⟨⟨c, cutSto_own hc1 ho', ho'⟩, hp1⟩
  · rintro ⟨⟨c, hc, ho⟩, hp⟩
    have ho' : c.owner = some j := ho
    have hc1 : Eg.sto l = some c := cutSto_sub hc
    have hc2 : Eg2.sto l = some c := hle.sto l c hc1
    have hp1 : Eg.pfr l = none := hp
    refine ⟨⟨c, cutSto_own (Eg := Eg2.withFp f) hc2 ho', ho'⟩, ?_⟩
    show Eg2.pfr l = none
    rcases hf.2.2.2.2.1 l with e | ⟨-, f0, -, -, c', hc', ho2⟩ | ⟨-, -, hs0⟩
    · rw [e]; exact hp1
    · rw [hc1] at hc'; cases hc'; rw [ho'] at ho2; cases ho2; exact absurd rfl hj
    · rw [hc2] at hs0; cases hs0

/-- At a private label of `j`, the cut's cell is unchanged. -/
theorem cutSto_gfoot_priv {g : G} {Eg Eg2 : GEnv} {n n' : Nat} {v : Ts} (hf : GFoot g Eg Eg2 n n' v)
    {j : Nat} (f : Nat → List Ts) (S : AllocLabel → Prop) {l : AllocLabel}
    (h : Priv (Cut Eg j S) l) : cutSto (Eg2.withFp f) j l = cutSto Eg j l := by
  obtain ⟨⟨c, hc, ho⟩, hp⟩ := h
  have hc1 : Eg.sto l = some c := cutSto_sub hc
  rw [show cutSto Eg j l = some c from hc]
  exact cutSto_own (Eg := Eg2.withFp f) (hf.le.sto l c hc1) ho

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (B1 at the system) every new message of the step is at a fresh label of
`i` or at a cell of `i`'s cut. -/
theorem tctx_writeAt {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m →
      FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label ∨ ∃ cl, cutSto Eg i m.loc.label = some cl := by
  obtain ⟨S0, -, hE0, hm0, -⟩ := X.inv.thr i th X.hth
  intro t m ht hm
  rw [X.e1] at hm
  exact tstep_writeAt hE0 hm0.2.2.1 X.hr t m ht hm

/-- Memory below the old size is unchanged by the step. -/
theorem tctx_pre {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    ∀ t, t < c.mem.size → c'.mem[t]? = c.mem[t]? := by
  intro t ht
  rw [X.e1]
  exact (TermLiveProps.tstep_ext _ _ _ _ r X.hr).mem.get t ht

/-- No new message lands at a private cell of an idle thread. -/
theorem tctx_noNewPriv {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) {j : Nat} (hji : j ≠ i)
    {S : AllocLabel → Prop} {l : AllocLabel} (hpv : Priv (Cut Eg j S) l) :
    ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → c'.mem[t]? = some m → m.loc.label ≠ l := by
  intro t m ht hm e
  obtain ⟨⟨cl, hc, ho⟩, hp⟩ := hpv
  have hc1 : Eg.sto l = some cl := cutSto_sub hc
  rcases tctx_writeAt X t m ht hm with hF | ⟨cl', hc'⟩
  · rw [e] at hF
    rw [((X.inv.gfresh X.hth r.2.2.nalloc) l hF).1] at hc1; cases hc1
  · rw [e, cutSto_priv hc1 ho (Ne.symm hji) hp] at hc'; cases hc'

/-- The step's promises are old ones. -/
theorem tctx_sub {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    ∀ t, t ∈ r.2.2.promises → t ∈ th.promises := by
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  exact fun t ht => (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1.subset ht

/-- Every thread of `c'` is an old thread with fewer promises. -/
theorem tctx_old {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) {j : Nat} {thj : TTh}
    (h : c'.ths[j]? = some thj) :
    ∃ th0, c.ths[j]? = some th0 ∧ (∀ t, t ∈ thj.promises → t ∈ th0.promises) ∧
      (j = i → th0 = th ∧ thj = r.2.2) ∧ (j ≠ i → thj = th0) := by
  by_cases hji : j = i
  · subst hji
    rw [X.e3] at h; cases h
    exact ⟨th, X.hth, tctx_sub X, fun _ => ⟨rfl, rfl⟩, fun h => absurd rfl h⟩
  · rw [X.ho j hji] at h
    exact ⟨thj, h, fun _ h => h, fun h => absurd h hji, fun _ => rfl⟩

/-- **T14 `fpokVisT`.** -/
theorem fpokVisT_holds : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ (j j' : Nat) (thj thj' : TTh) (t : Ts) (m : Msg) (S' : AllocLabel → Prop), j ≠ j' → c'.ths[j]? = some thj →
      c'.ths[j']? = some thj' → t ∈ thj'.promises → c'.mem[t]? = some m → Vis (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j S') m.loc.label := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j j' thj thj' t m S' hjj hj hj' ht hm
  have hgf := gfoot_of X Y Z
  obtain ⟨th0', h0', hs', -, -⟩ := tctx_old X hj'
  obtain ⟨th0, h0, -, -, -⟩ := tctx_old X hj
  have ht0 : t ∈ th0'.promises := hs' t ht
  have hlt : t < c.mem.size := X.inv.plt j' th0' t h0' ht0
  have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
  have hnj : t ∉ th0.promises := fun h => X.inv.disj j j' th0 th0' t hjj h0 h0' h ht0
  have hall : t ∈ allProms c := mem_allProms.2 ⟨j', th0', h0', ht0⟩
  have hfp : t ∈ Eg.fpOf j := by
    rcases List.mem_append.1 ((X.inv.proms j th0 h0 t).2 hall) with h | h
    · exact absurd h hnj
    · exact h
  have hvis : Vis (Cut Eg j S') m.loc.label := (X.inv.fpok j th0 S' h0).2 t m hfp hm0
  intro hpv
  by_cases hji : j = i
  · subst hji
    obtain ⟨⟨cl, hc, ho⟩, hp⟩ := hpv
    have ho' : cl.owner = some j := ho
    have hc2 : (Eg.post (gOf p k arch c j) th.nalloc r.2.2.nalloc E').sto m.loc.label = some cl := cutSto_sub hc
    rcases hgf.2.1 m.loc.label with e | ⟨hF, -, -, -, -⟩
    · rw [e] at hc2
      have hp1 : Eg.pfr m.loc.label = none := by
        cases e2 : Eg.pfr m.loc.label with
        | none => rfl
        | some f0 => have := hgf.le.pfr _ f0 e2; exact absurd (hp.symm.trans this) (by simp)
      exact hvis ⟨⟨cl, cutSto_own hc2 ho', ho'⟩, hp1⟩
    · obtain ⟨jj, hjj1, -, hl⟩ := hF
      have := (X.inv.fresh j th X.hth jj hjj1).2.2.2.2 t m hm0 hl
      have e0 : th0 = th := by rw [X.hth] at h0; cases h0; rfl
      exact hnj (e0 ▸ this)
  · exact hvis ((Priv_gfoot hgf hji _ S' S' _).1 hpv)

/-- Distinct threads' fresh labels are distinct, and one thread's are injective. -/
theorem freshLabel_inj {b n i j k k' : Nat} (hi : i < n) (hj : j < n)
    (e : freshLabel b n i k = freshLabel b n j k') : i = j ∧ k = k' := by
  unfold freshLabel at e
  have e1 : i + n * k = j + n * k' := by
    rw [Nat.add_assoc, Nat.add_assoc] at e; exact Nat.add_left_cancel e
  have hm : (i + n * k) % n = (j + n * k') % n := by rw [e1]
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hm
  subst hm
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel e1)⟩

/-- **T15 `freshT`.** -/
theorem freshT_holds : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj, c'.ths[j]? = some thj → ∀ m, thj.nalloc ≤ m →
      GFreshL (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' thj (freshLabel c'.lbase c'.n j m) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj hj m hm
  have hgf := gfoot_of X Y Z
  have hlb : c'.lbase = c.lbase := (threadSteps_lbase X.hc').1
  have hsz : c'.ths.size = c.ths.size := TermStep.threadSteps_size X.hc'
  rw [hlb, TermStep.threadSteps_n X.hc']
  have hjlt : j < c.ths.size := by rw [← hsz]; exact TermLiveProps.lt_of_get hj
  have hilt : i < c.ths.size := TermLiveProps.lt_of_get X.hth
  by_cases hji : j = i
  · subst hji
    rw [X.e3] at hj; cases hj
    have hnF : ¬ FreshIn (gOf p k arch c j) th.nalloc r.2.2.nalloc (freshLabel c.lbase c.n j m) := by
      rintro ⟨jj, -, h2, e⟩
      have := (freshLabel_inj (Cfg.lt_n hjlt) (Cfg.lt_n hjlt) e).2
      omega
    have hnal : th.nalloc ≤ r.2.2.nalloc := (TermTyped.tstep_wrUp _ _ _ _ r X.hr).2.2.1
    have old := X.inv.fresh j th X.hth m (Nat.le_trans hnal hm)
    have hFL := Z.2.2.1.2.2.2.1.1 m hm
    refine ⟨?_, ?_, hFL.2.2.1, hFL.2.2.2, fun t m' hm' hl => hFL.2.1 t m' (by rw [← X.e1]; exact hm') hl⟩
    · show (Eg.post (gOf p k arch c j) th.nalloc r.2.2.nalloc E').sto _ = none
      rw [post_sto_old hnF]; exact old.1
    · show (Eg.post (gOf p k arch c j) th.nalloc r.2.2.nalloc E').box _ = none
      rw [post_box_old hnF]; exact old.2.1
  · have hj0 : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hj
    have old := X.inv.fresh j thj hj0 m hm
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc (freshLabel c.lbase c.n j m) := by
      rintro ⟨jj, -, -, e⟩
      exact hji (freshLabel_inj (Cfg.lt_n hjlt) (Cfg.lt_n hilt) e).1
    have hnO : ¬ Eg.OwnAt i (freshLabel c.lbase c.n j m) := fun ⟨cl, hc, _⟩ => by rw [old.1] at hc; cases hc
    refine ⟨?_, ?_, ?_, ?_, fun t m' hm' hl => ?_⟩
    · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto _ = none
      rcases hgf.2.1 (freshLabel c.lbase c.n j m) with e | ⟨hF, -⟩
      · rw [e]; exact old.1
      · exact absurd hF hnF
    · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box _ = none
      rcases hgf.2.2.1 (freshLabel c.lbase c.n j m) with e | ⟨hF, -⟩
      · rw [e]; exact old.2.1
      · exact absurd hF hnF
    · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini _ = 0
      rcases (hgf.2.2.2.1 (freshLabel c.lbase c.n j m)).2 with e | hF | hO
      · rw [e]; exact old.2.2.1
      · exact absurd hF hnF
      · exact absurd hO hnO
    · show (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').pfr _ = none
      rcases hgf.2.2.2.2.1 (freshLabel c.lbase c.n j m) with e | ⟨-, -, -, -, hO⟩ | ⟨hF, -⟩
      · rw [e]; exact old.2.2.2.1
      · exact absurd hO hnO
      · exact absurd hF hnF
    · rcases Nat.lt_or_ge t c.mem.size with h1 | h1
      · rw [tctx_pre X t h1] at hm'; exact old.2.2.2.2 t m' hm' hl
      · rcases tctx_writeAt X t m' h1 hm' with hF | ⟨cl, hc⟩
        · rw [hl] at hF; exact absurd hF hnF
        · rw [hl] at hc; have h0 := old.1; rw [cutSto_sub hc] at h0; cases h0

/-- **T16c `interfHPT`.** -/
theorem interfHPT_holds : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      MemHeldP (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) (HP j) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji _ hold
  have hgf := gfoot_of X Y Z
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  refine MemHeldP_move (Priv_gfoot hgf hji _ Sj Sj) (fun l hpv => cutSto_gfoot_priv hgf _ Sj hpv)
    (fun l R hpv he => ?_) hold.2.2.2.1
  obtain ⟨⟨cl, hc, ho⟩, hp⟩ := hpv
  have hpv0 : Priv (Cut Eg j Sj) l := ⟨⟨cl, hc, ho⟩, hp⟩
  refine HeldEntry_priv_move (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) (s' := stOf c'.mem c'.pairs thj)
    rfl rfl hI hpv0 ((Priv_gfoot hgf hji _ Sj Sj l).2 hpv0)
    (cutSto_gfoot_priv hgf _ Sj hpv0) ?_ ?_ rfl (tctx_pre X) (tctx_noNewPriv X hji hpv0) he
  · have hc1 : Eg.sto l = some cl := cutSto_sub hc
    have ho' : cl.owner = some j := ho
    exact gfoot_ini_other hgf hfr hc1 (by rw [ho']; intro e; exact hji (Option.some.inj e))
  · have hc1 : Eg.sto l = some cl := cutSto_sub hc
    have ho' : cl.owner = some j := ho
    exact gfoot_rini_other hgf hfr hc1 (by rw [ho']; intro e; exact hji (Option.some.inj e))

end

/-! ## Promise credits of an idle thread -/


/-- The SysInvN clause `PromIniOK` (B4 (a0)) as a hypothesis on reachable
configurations. -/
def PromTyA0F (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res},
    TermSpawnStep.StepsG p k arch Sp c0 c → SysInvN p k arch Init MintOK c Eg Tot HP HS cr db → PromIniOK Eg c

/-- Credits and debits move when memory below the promises is kept and each
promise's `VRes` and (U3, fix b) `DbRes` move. -/
theorem PromCr_move {E E' : TEnv} {s s' : St} {cr db : Ts → Res} (h : PromCr E s cr db)
    (hp : s'.promises = s.promises) (hlt : ∀ t, t ∈ s.promises → t < s.mem.size)
    (hm : ∀ t, t < s.mem.size → s'.mem[t]? = s.mem[t]?)
    (hv : ∀ t m w R, t ∈ s.promises → s.mem[t]? = some m → VRes E m.loc w R → VRes E' m.loc w R)
    (hdv : ∀ t m R, t ∈ s.promises → s.mem[t]? = some m → DbRes E s.mem m t R → DbRes E' s.mem m t R) :
    PromCr E' s' cr db := by
  intro tw htw
  rw [hp] at htw
  obtain ⟨m, hm1, hd, hc⟩ := h tw htw
  have hlt' := hlt tw htw
  refine ⟨m, by rw [hm tw hlt']; exact hm1,
    DbRes_mem hm hlt' (hdv tw m _ htw hm1 hd), ?_⟩
  rcases hc with ⟨w, hw, hcw⟩ | ⟨hnw, hcz⟩
  · exact Or.inl ⟨w, (PredAt_prefix hm (Nat.le_of_lt hlt')).1 hw, hv tw m _ _ htw hm1 hcw⟩
  · exact Or.inr ⟨fun w hw => hnw w ((PredAt_prefix hm (Nat.le_of_lt hlt')).2 hw), hcz⟩

/-- `VRes` moves when the cell, its frontier and its visibility stay, and the
count either stays or the address was already initialised (and grows). -/
theorem VRes_move {E E' : TEnv} {a : Address} {w : Word} {R : Res}
    (hs : E'.sto a.label = E.sto a.label) (ht : E'.tid = E.tid) (hp : E'.pfr a.label = E.pfr a.label)
    (hi : E'.ini a.label = E.ini a.label ∨ (E.ini a.label ≤ E'.ini a.label ∧ IniW E a))
    (h : VRes E a w R) : VRes E' a w R := by
  have hV := Vis_congr hs ht hp
  have hW := WRes_congr (w := w) (R := R) hs
  rcases hi with hi | ⟨hle, hiw⟩
  · exact (VRes_congr hs ht hp hi).2 h
  · have hiw' : IniW E' a := fun c N e us hc hT hu => by
      rw [hs] at hc
      exact Nat.lt_of_lt_of_le (hiw c N e us hc hT hu) (Nat.mul_le_mul_right _ hle)
    rcases h with ⟨h1, -, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hV.2 h1, hiw', hW.2 h3⟩
    · exact Or.inr ⟨fun ⟨a1, _⟩ => h1 ⟨hV.1 a1, hiw⟩, h2⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (U3, fix b) The move conditions of `VRes_move`/`DbRes_move` at the idle
thread's own promises across a thread step (the old-credit core of
`interfCrT_holds`). -/
theorem interfCrT_cond (hA0 : PromTyA0F p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj) :
    ∀ t m, t ∈ thj.promises → c.mem[t]? = some m →
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto m.loc.label =
          (Cut Eg j Sj).sto m.loc.label ∧
        (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).tid = (Cut Eg j Sj).tid ∧
        (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr m.loc.label =
          (Cut Eg j Sj).pfr m.loc.label ∧
        ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini m.loc.label =
            (Cut Eg j Sj).ini m.loc.label ∨
          ((Cut Eg j Sj).ini m.loc.label ≤ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini m.loc.label ∧
            IniW (Cut Eg j Sj) m.loc)) ∧
        ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc m.loc.label =
            (Cut Eg j Sj).rc m.loc.label ∨
          ∀ cl, (Cut Eg j Sj).sto m.loc.label = some cl → cl.owner ≠ some (Cut Eg j Sj).tid) := by
  have hgf := gfoot_of X Y Z
  have hpi := hA0 X.run X.inv
  intro t m ht hm
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc m.loc.label := by
    rintro ⟨jj, hjj, -, hl⟩
    exact X.inv.disj j i thj th t hji hj X.hth ht ((X.inv.fresh i th X.hth jj hjj).2.2.2.2 t m hm hl)
  have hsto : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto m.loc.label = Eg.sto m.loc.label :=
    hgf.sto_old hnF
  have hnO : (∀ cl, Eg.sto m.loc.label = some cl → cl.owner ≠ some i) →
      (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').pfr m.loc.label = Eg.pfr m.loc.label := fun hno => by
    rcases hgf.2.2.2.2.1 m.loc.label with e | ⟨-, -, -, -, cl, hc, ho⟩ | ⟨hF, -⟩
    · exact e
    · exact absurd ho (hno cl hc)
    · exact absurd hF hnF
  cases hsl : Eg.sto m.loc.label with
  | none =>
    have hp := hnO (fun cl hc => by rw [hsl] at hc; cases hc)
    have hc1 : cutSto (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') j m.loc.label = cutSto Eg j m.loc.label :=
      cutSto_congr hsto (fun cl hc _ => by rw [hsl] at hc; cases hc)
    refine ⟨hc1, rfl, hp, .inl ?_, .inr fun cl hc => ?_⟩
    · rcases (hgf.2.2.2.1 m.loc.label).2 with e | hF | ⟨cl, hc, -⟩
      · exact e
      · exact absurd hF hnF
      · rw [hsl] at hc; cases hc
    · have hc' : Eg.sto m.loc.label = some cl := cutSto_sub hc
      rw [hsl] at hc'; cases hc'
  | some cl =>
    by_cases ho : cl.owner = some i
    · -- a promise of `j` at a cell of `i`: shared (`fpok` of `i`)
      have hall : t ∈ allProms c := mem_allProms.2 ⟨j, thj, hj, ht⟩
      have hnth : t ∉ th.promises := fun h => X.inv.disj j i thj th t hji hj X.hth ht h
      have hfp : t ∈ Eg.fpOf i := by
        rcases List.mem_append.1 ((X.inv.proms i th X.hth t).2 hall) with h | h
        · exact absurd h hnth
        · exact h
      have hvis : Vis (Cut Eg i S) m.loc.label := (X.inv.fpok i th S X.hth).2 t m hfp hm
      obtain ⟨f, hf⟩ : Eg.Shared m.loc.label := by
        cases e : Eg.pfr m.loc.label with
        | none => exact absurd ⟨⟨cl, cutSto_own hsl ho, ho⟩, e⟩ hvis
        | some f => exact ⟨f, e⟩
      have hf' := hgf.le.pfr _ f hf
      have hc1 : cutSto (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') j m.loc.label = cutSto Eg j m.loc.label := by
        rw [cutSto_eq_shared ⟨f, hf'⟩, cutSto_eq_shared ⟨f, hf⟩, hsto]
      refine ⟨hc1, rfl, hf'.trans hf.symm, .inr ⟨hgf.le.ini _, ?_⟩, .inr fun c1 hc => ?_⟩
      rotate_left
      · have hc1' : Eg.sto m.loc.label = some c1 := cutSto_sub hc
        rw [hsl] at hc1'; cases hc1'
        rw [ho]; intro e; exact hji (Option.some.inj e).symm
      intro c1 N e us hc hT hu
      have hc1' : Eg.sto m.loc.label = some c1 := cutSto_sub hc
      rw [hsl] at hc1'; cases hc1'
      have := hpi j thj t m hj ht hm cl hsl ⟨f, hf⟩ N e us hT hu
      exact this
    · have hp := hnO (fun cl' hc => by rw [hsl] at hc; cases hc; exact ho)
      have hc1 : cutSto (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') j m.loc.label = cutSto Eg j m.loc.label :=
        cutSto_congr hsto (fun _ _ _ => by unfold GEnv.Shared; rw [hp])
      have hi1 := gfoot_ini_other hgf (X.inv.gfresh X.hth _) hsl ho
      have hr1 := gfoot_rini_other hgf (X.inv.gfresh X.hth _) hsl ho
      exact ⟨hc1, rfl, hp, .inl hi1, .inl (TEnv.rc_congr hi1 hr1)⟩

/-- The idle thread's `VRes` at its own promises moves across a thread step. -/
theorem interfCrT_mover (hA0 : PromTyA0F p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj) :
    ∀ t m w R, t ∈ thj.promises → c.mem[t]? = some m → VRes (Cut Eg j Sj) m.loc w R →
      VRes (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) m.loc w R := by
  intro t m w R ht hm hv
  obtain ⟨h1, h2, h3, h4, -⟩ := interfCrT_cond (Sj := Sj) hA0 X Y Z hji hj t m ht hm
  exact VRes_move h1 h2 h3 h4 hv

/-- (U3, fix b) The idle thread's `DbRes` at its own promises moves across a thread step. -/
theorem interfDb_mover (hA0 : PromTyA0F p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj) (M : Memory) :
    ∀ t m R, t ∈ thj.promises → c.mem[t]? = some m → DbRes (Cut Eg j Sj) M m t R →
      DbRes (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) M m t R := by
  intro t m R ht hm hd
  obtain ⟨h1, h2, h3, h4, h5⟩ := interfCrT_cond (Sj := Sj) hA0 X Y Z hji hj t m ht hm
  have hI := (Cut_other (gfoot_of X Y Z) (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  exact DbRes_move h1 h2 h3 h4 h5 hd hI.box

/-- **T16d `interfCrT`, old credits**, given B4 (a0) (`PromTyA0F`): an idle
thread's `PromCr` credits move. The system now carries `PromCrK`; the
plant branch and the transfer `δ` are the open `Obligations.interfCrT`. -/
theorem interfCrT_holds (hA0 : PromTyA0F p k arch Sp Init MintOK c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      PromCr (Cut Eg (gOf p k arch c j).i Sj) (stOf c.mem c.pairs thj) (cr j) (db j) →
      PromCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) (cr j) (db j) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj _ hC0
  exact PromCr_move hC0 rfl (fun t ht => X.inv.plt j thj t hj ht) (tctx_pre X) (interfCrT_mover hA0 X Y Z hji hj)
    (interfDb_mover hA0 X Y Z hji hj _)

end

/-! ## Boxes (T17) -/

theorem LatestS_grow {mem mem' : Memory} {S : Ts → Prop} {coh : Address → Ts} {a : Address} {w : Word}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc.label ≠ a.label)
    (h : LatestS mem S coh a w) : LatestS mem' S coh a w := by
  obtain ⟨⟨m, hm, hma, hmv, hmw⟩, hs, hn⟩ := h
  refine ⟨⟨m, by rw [hpre _ (lt_of_get hm)]; exact hm, hma, hmv, hmw⟩, hs, fun t m' ht hm' hl => ?_⟩
  rcases Nat.lt_or_ge t mem.size with h1 | h1
  · rw [hpre t h1] at hm'; exact hn t m' ht hm' hl
  · exact absurd (congrArg Address.label hl) (hnew t m' h1 hm')

/-- No skipped message after the coherence point: nothing needs skipping. -/
theorem LatestP_unskip {mem : Memory} {P : List Ts} {coh : Address → Ts} {a : Address} {w : Word}
    (hno : ∀ (t : Ts) (m : Msg), t ∈ P → mem[t]? = some m → m.loc ≠ a)
    (h : LatestP mem P coh a w) : LatestP mem [] coh a w := by
  obtain ⟨hm, -, hn⟩ := h
  exact ⟨hm, by simp, fun t m ht hm' hl => absurd hl (hno t m (hn t m ht hm' hl) hm')⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (certification) **After a thread step that creates a box, the
stepper has no outstanding promise at the box's label** (box words are never
written, so such a promise cannot be fulfilled by the certifying run). -/
def NoBoxPromF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ l B, FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l → E'.box l = some B →
      ∀ t, t ∈ r.2.2.promises → ∀ m, c'.mem[t]? = some m → m.loc.label ≠ l

/-- Promises after a thread step are old promises. -/
theorem tctx_allProms {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) {t : Ts} (h : t ∈ allProms c') :
    t ∈ allProms c := by
  obtain ⟨j, thj, hj, ht⟩ := mem_allProms.1 h
  obtain ⟨th0, h0, hs, -, -⟩ := tctx_old X hj
  exact mem_allProms.2 ⟨j, th0, h0, hs t ht⟩

/-- **T17 `boxtopT`**, given `NoBoxPromF`. -/
theorem boxtopT_holds (hnb : NoBoxPromF p k arch Sp Init MintOK c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    BoxTopG (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c' := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr l B hB
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
  · have hB' : E'.box l = some B := by
      have : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box l = some B := hB
      rwa [post_box_fresh hF] at this
    have hno := hnb X Y Z hS hPfr l B hF hB'
    -- every promise of `c'` at `l` is the stepper's
    have hall : ∀ t m, t ∈ allProms c' → c'.mem[t]? = some m → m.loc.label ≠ l := by
      intro t m ht hm hl
      obtain ⟨j, thj, hj, htj⟩ := mem_allProms.1 ht
      by_cases hji : j = i
      · subst hji; rw [X.e3] at hj; cases hj; exact hno t htj m hm hl
      · have hj0 : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hj
        have hlt : t < c.mem.size := X.inv.plt j thj t hj0 htj
        have hm0 : c.mem[t]? = some m := by rw [← tctx_pre X t hlt]; exact hm
        obtain ⟨jj, hjj, -, e⟩ := hF
        exact X.inv.disj j i thj th t hji hj0 X.hth htj
          ((X.inv.fresh i th X.hth jj hjj).2.2.2.2 t m hm0 (hl.trans e))
    refine (Z.2.2.1.2.2.2.2.2.2.2.2.2.1.2.1 l B hB').imp fun o w ⟨t, ht, hl⟩ => ⟨t, ht, ?_, ?_⟩
    · intro hta
      obtain ⟨⟨m, hm, hma, -⟩, -, -⟩ := hl
      exact hall t m hta (by rw [X.e1]; exact hm) (by rw [hma])
    · have hl' := LatestP_unskip (fun t m ht hm hma => hno t ht m (by rw [X.e1]; exact hm)
        (by rw [hma])) hl
      rw [X.e1]; exact hl'
  · have hB0 : Eg.box l = some B := by
      have : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box l = some B := hB
      rwa [post_box_old hF] at this
    have hcut : cutSto Eg i l = none := (hm0.2.2.2.2.2.2.2.2.2.1.2.2 l B hB0).1
    refine (X.inv.boxtop l B hB0).imp fun o w ⟨t, ht, hn, hl⟩ => ⟨t, ht, fun h => hn (tctx_allProms X h), ?_⟩
    refine LatestS_grow (tctx_pre X) (fun t' m h1 h2 e => ?_) hl
    rcases tctx_writeAt X t' m h1 h2 with hF' | ⟨cl, hc⟩
    · have e' : m.loc.label = l := e
      rw [e'] at hF'; exact hF hF'
    · rw [e, hcut] at hc; cases hc

end

/-! ## The promise step -/

theorem push_get {mem : Memory} {x : Msg} {t : Nat} {m : Msg} (h : (mem.push x)[t]? = some m) :
    (t < mem.size ∧ mem[t]? = some m) ∨ (t = mem.size ∧ m = x) := by
  rw [Array.getElem?_push] at h
  split at h
  · cases h; exact .inr ⟨by assumption, rfl⟩
  · exact .inl ⟨lt_of_get h, h⟩

theorem push_pre {mem : Memory} {x : Msg} : ∀ t, t < mem.size → (mem.push x)[t]? = mem[t]? :=
  fun t ht => by rw [Array.getElem?_push]; simp [Nat.ne_of_lt ht]

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (certification) **Where a promise lies**: the promised address's
label is a cell of the promiser's cut or one of its labels yet to allocate (B1
along the certifying run). -/
def PromLocF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    (∃ cl, cutSto Eg j a.label = some cl) ∨ ∃ m, th.nalloc ≤ m ∧ a.label = freshLabel c.lbase c.n j m

/-- Threads after a promise step: old ones, the promiser with the new timestamp. -/
theorem prom_old {c : Cfg} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) {i : Nat} {thi : TTh} (h : (promise c j a v w).ths[i]? = some thi) :
    ∃ th0, c.ths[i]? = some th0 ∧ thi.nalloc = th0.nalloc ∧
      ∀ t, t ∈ thi.promises → t ∈ th0.promises ∨ (i = j ∧ t = c.mem.size) := by
  by_cases hij : i = j
  · subst hij
    rw [(promise_inv (a := a) (v := v) (w := w) hth).2.1] at h; cases h
    refine ⟨th, hth, rfl, fun t ht => ?_⟩
    rcases List.mem_append.1 ht with h | h
    · exact .inl h
    · exact .inr ⟨rfl, List.mem_singleton.1 h⟩
  · rw [promise_other hth hij] at h
    exact ⟨thi, h, rfl, fun t ht => .inl ht⟩

theorem prom_mem {c : Cfg} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hth : c.ths[j]? = some th) : (promise c j a v w).mem = c.mem.push ⟨a, v, w⟩ := by
  rw [(promise_inv (a := a) (v := v) (w := w) hth).1]

/-- From `PromLocF`: the promised label is not another thread's private cell,
fresh label, nor a box label. -/
theorem promLoc_not {c : Cfg} {Eg : GEnv} {j : Nat} {th : TTh} {a : Address}
    (hloc : (∃ cl, cutSto Eg j a.label = some cl) ∨ ∃ m, th.nalloc ≤ m ∧ a.label = freshLabel c.lbase c.n j m)
    (hfr : ∀ m, th.nalloc ≤ m → Eg.sto (freshLabel c.lbase c.n j m) = none ∧
      Eg.box (freshLabel c.lbase c.n j m) = none)
    (hbox : ∀ l B, Eg.box l = some B → cutSto Eg j l = none) :
    (∀ i S, i ≠ j → ¬ Priv (Cut Eg i S) a.label) ∧ (∀ l B, Eg.box l = some B → a.label ≠ l) ∧
    ((∃ cl, Eg.sto a.label = some cl) ∨ ∃ m, th.nalloc ≤ m ∧ a.label = freshLabel c.lbase c.n j m) := by
  rcases hloc with ⟨cl, hc⟩ | ⟨m, hm, e⟩
  · refine ⟨?_, ?_, .inl ⟨cl, cutSto_sub hc⟩⟩
    · rintro i S hij ⟨⟨c1, hc1, ho1⟩, hp⟩
      obtain ⟨h1, h2⟩ := cutSto_some.1 hc
      rw [cutSto_sub hc1] at h1
      have e1 : c1 = cl := Option.some.inj h1
      subst e1
      have ho1' : c1.owner = some i := ho1
      rcases h2 with h2 | ⟨f, hf⟩
      · rw [ho1'] at h2; cases h2; exact hij rfl
      · have hp' : Eg.pfr a.label = none := hp
        rw [hp'] at hf; cases hf
    · intro l B hB e
      rw [e, hbox l B hB] at hc; cases hc
  · refine ⟨?_, ?_, .inr ⟨m, hm, e⟩⟩
    · rintro i S _ ⟨⟨c1, hc1, _⟩, _⟩
      have := cutSto_sub hc1; rw [e, (hfr m hm).1] at this; cases this
    · intro l B hB e'
      rw [← e', e, (hfr m hm).2] at hB; cases hB

/-- The SysInvN facts `promLoc_not` uses, at the promiser. -/
theorem pctx_promLoc {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat}
    {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts} (hpl : PromLocF p k arch Sp Init MintOK c0)
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) :
    (∀ i S, i ≠ j → ¬ Priv (Cut Eg i S) a.label) ∧ (∀ l B, Eg.box l = some B → a.label ≠ l) ∧
    ((∃ cl, Eg.sto a.label = some cl) ∨ ∃ m, th.nalloc ≤ m ∧ a.label = freshLabel c.lbase c.n j m) := by
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
  exact promLoc_not (hpl X) (fun m hm => ⟨(X.inv.fresh j th X.hth m hm).1, (X.inv.fresh j th X.hth m hm).2.1⟩)
    (fun l B hB => (hm0.2.2.2.2.2.2.2.2.2.1.2.2 l B hB).1)

/-- A planted cut is no more private than the old one. -/
theorem Priv_plant {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} (f : Nat → List Ts) {i : Nat}
    {S : AllocLabel → Prop} {l : AllocLabel} (h : Priv (Cut ((plantG Eg P N).withFp f) i S) l) :
    Priv (Cut Eg i S) l := by
  obtain ⟨⟨c1, hc1, ho1⟩, hp⟩ := h
  have hc : Eg.sto l = some c1 := cutSto_sub (Eg := plantG Eg P N) hc1
  have ho : c1.owner = some i := ho1
  have hp' : Eg.pfr l = none := by
    have hp1 : (plantG Eg P N).pfr l = none := hp
    simp only [plantG] at hp1
    split at hp1
    · cases hp1
    · exact hp1
  exact ⟨⟨c1, cutSto_own hc ho, ho⟩, hp'⟩

/-- (B1) At a label the plant does not choose, a planted cut's counts are the old ones. -/
theorem cutP_ini {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n i : Nat}
    {S : AllocLabel → Prop} {l : AllocLabel} (hn : P l = none) :
    (Cut (EgP Eg P N j n) i S).ini l = (Cut Eg i S).ini l := plantG_ini_none hn

theorem cutP_rc {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} {j n i : Nat}
    {S : AllocLabel → Prop} {l : AllocLabel} (hn : P l = none) :
    (Cut (EgP Eg P N j n) i S).rc l = (Cut Eg i S).rc l := by
  unfold TEnv.rc; rw [cutP_ini hn]; rfl

theorem InitR_ini {E E' : TEnv} {c : Cell} {l : AllocLabel} {o : Nat} (h : E'.ini l = E.ini l)
    (H : InitR E' c l o) : InitR E c l o := fun N e us h1 h2 => by have := H N e us h1 h2; rwa [h] at this

theorem InitRr_rc {E E' : TEnv} {c : Cell} {l : AllocLabel} {o : Nat} (h : E'.rc l = E.rc l)
    (H : InitRr E' c l o) : InitRr E c l o := fun N e us h1 h2 => by have := H N e us h1 h2; rwa [h] at this

theorem IniSeg_ini {E E' : TEnv} {c : Cell} {l : AllocLabel} {b : Nat} (h : E'.ini l = E.ini l)
    (H : IniSeg E' c l b) : IniSeg E c l b := by unfold IniSeg at H ⊢; rwa [h] at H

/-- **P5 `fpokVisP`**, given `PromLocF`. -/
theorem fpokVisP_holds (hpl : PromLocF p k arch Sp Init MintOK c0) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ (i i' : Nat) (thi thi' : TTh) (t : Ts) (m : Msg) (S : AllocLabel → Prop), i ≠ i' →
      (promise c j a v w).ths[i]? = some thi → (promise c j a v w).ths[i']? = some thi' → t ∈ thi'.promises →
      (promise c j a v w).mem[t]? = some m → Vis (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) i S) m.loc.label := by
  intro c Eg Tot HP HS cr db j th a v w X i i' thi thi' t m S hii hi hi' ht hm hpv
  have hpv0 := Priv_plant _ hpv
  obtain ⟨th0, h0, -, -⟩ := prom_old X.hth hi
  obtain ⟨th0', h0', -, hs'⟩ := prom_old X.hth hi'
  rw [prom_mem X.hth] at hm
  rcases hs' t ht with ht0 | ⟨rfl, rfl⟩
  · have hlt := X.inv.plt i' th0' t h0' ht0
    rw [push_pre t hlt] at hm
    have hnj : t ∉ th0.promises := fun h => X.inv.disj i i' th0 th0' t hii h0 h0' h ht0
    have hfp : t ∈ Eg.fpOf i := by
      rcases List.mem_append.1 ((X.inv.proms i th0 h0 t).2 (mem_allProms.2 ⟨i', th0', h0', ht0⟩)) with h | h
      · exact absurd h hnj
      · exact h
    exact (X.inv.fpok i th0 S h0).2 t m hfp hm hpv0
  · rcases push_get hm with ⟨h1, -⟩ | ⟨-, rfl⟩
    · exact Nat.lt_irrefl _ h1
    · exact (pctx_promLoc hpl X).1 i S hii hpv0

/-- **P7 `boxtopP`**, given `PromLocF`. -/
theorem boxtopP_holds (hpl : PromLocF p k arch Sp Init MintOK c0) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    BoxTopG (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) := by
  intro c Eg Tot HP HS cr db j th a v w X l B hB
  have hB0 : Eg.box l = some B := hB
  have hne := (pctx_promLoc hpl X).2.1 l B hB0
  refine (X.inv.boxtop l B hB0).imp fun o w' ⟨t, ht, hn, hl⟩ => ⟨t, ht, fun h => ?_, ?_⟩
  · rw [allProms_promise X.hth] at h
    rcases h with h | rfl
    · exact hn h
    · obtain ⟨⟨m, hm, -⟩, -, -⟩ := hl
      exact Nat.lt_irrefl _ (lt_of_get hm)
  · rw [prom_mem X.hth]
    refine LatestS_grow push_pre (fun t' m h1 h2 e => ?_) hl
    rcases push_get h2 with ⟨h3, -⟩ | ⟨-, rfl⟩
    · exact absurd h3 (Nat.not_lt.2 h1)
    · exact hne e

/-- **P6 `freshP`**, given `PlantSpecF` and `PromLocF`. -/
theorem freshP_holds (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ i thi, (promise c j a v w).ths[i]? = some thi → ∀ m, thi.nalloc ≤ m →
      GFreshL (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w) thi
        (freshLabel (promise c j a v w).lbase (promise c j a v w).n i m) := by
  intro c Eg Tot HP HS cr db j th a v w X i thi hi m hm
  have hlb : (promise c j a v w).lbase = c.lbase := by
    rw [(promise_inv (a := a) (v := v) (w := w) X.hth).1]
  rw [hlb, TermStep.promise_n]
  obtain ⟨th0, h0, hna, hs⟩ := prom_old X.hth hi
  have old := X.inv.fresh i th0 h0 m (hna ▸ hm)
  have hilt : i < c.ths.size := TermLiveProps.lt_of_get h0
  have hjlt : j < c.ths.size := TermLiveProps.lt_of_get X.hth
  refine ⟨old.1, old.2.1, ?_, ?_, fun t m' hm' hl => ?_⟩
  · show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini _ = 0
    simp only [plantG]
    split
    · rename_i f hf
      obtain ⟨-, ⟨cl, hc, -⟩, -⟩ := hspec X _ f hf
      rw [old.1] at hc; cases hc
    · exact old.2.2.1
  · show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = none
    simp only [plantG]
    split
    · rename_i f hf
      obtain ⟨-, ⟨cl, hc, -⟩, -⟩ := hspec X _ f hf
      rw [old.1] at hc; cases hc
    · exact old.2.2.2.1
  · rw [prom_mem X.hth] at hm'
    rcases push_get hm' with ⟨h1, h2⟩ | ⟨rfl, rfl⟩
    · have := old.2.2.2.2 t m' h2 hl
      by_cases hij : i = j
      · subst hij
        rw [(promise_inv (a := a) (v := v) (w := w) X.hth).2.1] at hi; cases hi
        rw [X.hth] at h0; cases h0
        exact List.mem_append_left _ this
      · rw [promise_other X.hth hij] at hi; rw [hi] at h0; cases h0; exact this
    · by_cases hij : i = j
      · subst hij
        rw [(promise_inv (a := a) (v := v) (w := w) X.hth).2.1] at hi; cases hi
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · exfalso
        rcases (pctx_promLoc hpl X).2.2 with ⟨cl, hc⟩ | ⟨m', -, e⟩
        · have hl' : a.label = freshLabel c.lbase c.n i m := hl
          rw [hl', old.1] at hc; cases hc
        · have hl' : a.label = freshLabel c.lbase c.n i m := hl
          exact hij (freshLabel_inj (Cfg.lt_n hilt) (Cfg.lt_n hjlt) (hl'.symm.trans e)).1

/-- The plant changes nothing at a label that is no private cell of `j`. -/
theorem plant_none {Eg : GEnv} {P : AllocLabel → Option Ts} {j n : Nat} (hP : PlantSpec Eg P j n)
    {S : AllocLabel → Prop} {l : AllocLabel} (hv : Vis (Cut Eg j S) l) : P l = none := by
  cases e : P l with
  | none => rfl
  | some f =>
    obtain ⟨hp, ⟨cl, hc, ho⟩, -⟩ := hP l f e
    exact absurd ⟨⟨cl, cutSto_own hc ho, ho⟩, hp⟩ hv

/-- **P4c `interfHPP`**, given `PlantSpecF` and `PromLocF`. -/
theorem interfHPP_holds (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      MemHeldP (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj) (HP j') := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj _ hold
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  -- at a private cell of `j'` the plant is inactive and the cut's cell unchanged
  have hpn : ∀ l, Priv (Cut Eg j' Sj) l → plantOf c Eg j a v w l = none := fun l ⟨⟨cl, hc, ho⟩, _⟩ => by
    cases e : plantOf c Eg j a v w l with
    | none => rfl
    | some f =>
      obtain ⟨-, ⟨cl', hc', ho'⟩, -⟩ := hP l f e
      rw [cutSto_sub hc] at hc'; cases hc'
      have ho1 : cl.owner = some j' := ho
      rw [ho1] at ho'; cases ho'; exact absurd rfl hjj
  have hst : ∀ l, Priv (Cut Eg j' Sj) l →
      (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).sto l = (Cut Eg j' Sj).sto l := fun l hpv => by
    obtain ⟨⟨cl, hc, ho⟩, _⟩ := hpv
    rw [show (Cut Eg j' Sj).sto l = some cl from hc]
    exact cutSto_own (Eg := (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).withFp (fpProm Eg j c.mem.size)) (cutSto_sub (Eg := Eg) hc) ho
  have hpriv : ∀ l, Priv (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) l ↔ Priv (Cut Eg j' Sj) l :=
    fun l => ⟨Priv_plant _, fun hpv => by
      refine ⟨⟨_, (hst l hpv).trans hpv.1.choose_spec.1, hpv.1.choose_spec.2⟩, ?_⟩
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = none
      simp only [plantG, hpn l hpv]
      exact hpv.2⟩
  refine MemHeldP_move hpriv hst (fun l R hpv he => ?_) hold.2.2.2.1
  refine HeldEntry_priv_move (E := Cut Eg j' Sj) (s := stOf c.mem c.pairs thj)
    (s' := stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj) rfl rfl hI hpv ((hpriv l).2 hpv) (hst l hpv) (plantG_ini_none (hpn l hpv)) rfl rfl
    push_pre (fun t m h1 h2 e => ?_) he
  rcases push_get h2 with ⟨h3, -⟩ | ⟨-, rfl⟩
  · exact absurd h3 (Nat.not_lt.2 h1)
  · exact (pctx_promLoc hpl X).1 j' Sj hjj (e ▸ hpv)

/-- **P4d `interfCrP`, old credits**, given `PlantSpecF`.  (D2) The plant
branch is the open `Obligations.interfCrP`. -/
theorem interfCrP_holds (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      PromCr (Cut Eg (gOf p k arch c j').i Sj) (stOf c.mem c.pairs thj) (cr j') (db j') →
      PromCr (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj) (cr j') (db j') := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold hC0
  have hP := hspec X
  have hcond : ∀ t m, t ∈ thj.promises → c.mem[t]? = some m →
      cutSto (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) j' m.loc.label = cutSto Eg j' m.loc.label ∧
      (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = Eg.pfr m.loc.label ∧
      (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini m.loc.label = Eg.ini m.loc.label := by
    intro t m ht hm
    have hnj : t ∉ th.promises := fun h => X.inv.disj j' j thj th t hjj hj X.hth ht h
    have hfp : t ∈ Eg.fpOf j := by
      rcases List.mem_append.1 ((X.inv.proms j th X.hth t).2 (mem_allProms.2 ⟨j', thj, hj, ht⟩)) with h | h
      · exact absurd h hnj
      · exact h
    have hn := plant_none hP ((X.inv.fpok j th Sj X.hth).2 t m hfp hm)
    have hpf : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = Eg.pfr m.loc.label := by
      simp only [plantG, hn]
    have hc : cutSto (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) j' m.loc.label = cutSto Eg j' m.loc.label :=
      cutSto_congr rfl (fun _ _ _ => by unfold GEnv.Shared; rw [hpf])
    exact ⟨hc, hpf, plantG_ini_none hn⟩
  refine PromCr_move hC0 rfl (fun t ht => X.inv.plt j' thj t hj ht) push_pre ?_ ?_
  · intro t m w' R ht hm hv
    obtain ⟨hc, hpf, hi⟩ := hcond t m ht hm
    exact VRes_move (E := Cut Eg j' Sj) hc rfl hpf (.inl hi) hv
  · intro t m R ht hm hd
    obtain ⟨hc, hpf, hi⟩ := hcond t m ht hm
    exact DbRes_move (E := Cut Eg j' Sj) hc rfl hpf (.inl hi) (.inl (TEnv.rc_congr hi rfl)) hd

end



/-! ### (§11) `PromCrK` of idle threads (P4d′, T16d) and the promiser's own plant credits (P3′) -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **P4d′ `interfCrP`** (D2, `PromCrK`), given `PlantSpecF`. -/
theorem interfCrPK_holds (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      TermPlant.PromCrK (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj)
        (cr j') (db j') := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold tw htw
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  have hPlt : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => X.inv.plt j' thj t hj ht
  obtain ⟨m, hm, hd, hc0⟩ := hold.2.2.2.2.2 tw htw
  have hlt := hPlt tw htw
  have hm' : (c.mem.push ⟨a, v, w⟩)[tw]? = some m := by rw [push_pre tw hlt]; exact hm
  -- the promise's label: not the promiser's private cell, so the plant is inactive there
  have hnj : tw ∉ th.promises := fun h => X.inv.disj j' j thj th tw hjj hj X.hth htw h
  have hfp : tw ∈ Eg.fpOf j := by
    rcases List.mem_append.1 ((X.inv.proms j th X.hth tw).2 (mem_allProms.2 ⟨j', thj, hj, htw⟩)) with h | h
    · exact absurd h hnj
    · exact h
  have hn := plant_none hP ((X.inv.fpok j th Sj X.hth).2 tw m hfp hm)
  have hpf : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = Eg.pfr m.loc.label := by
    simp only [plantG, hn]
  have hcs : cutSto (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) j' m.loc.label = cutSto Eg j' m.loc.label :=
    cutSto_congr rfl (fun _ _ _ => by unfold GEnv.Shared; rw [hpf])
  have hvm : ∀ (u : Word) (R : Res), VRes (Cut Eg j' Sj) m.loc u R →
      VRes (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) m.loc u R :=
    fun u R h => VRes_move (E := Cut Eg j' Sj) hcs rfl hpf (.inl (plantG_ini_none hn)) h
  refine ⟨m, hm', DbRes_mem push_pre hlt
    (DbRes_move (E := Cut Eg j' Sj) hcs rfl hpf (.inl (plantG_ini_none hn))
      (.inl (TEnv.rc_congr (plantG_ini_none hn) rfl)) hd), ?_⟩
  rcases hc0 with (⟨u, hu, hvu⟩ | ⟨hnu, hz⟩) | ⟨hpc, hk⟩
  · exact .inl (.inl ⟨u, (PredAt_prefix push_pre (Nat.le_of_lt hlt)).1 hu, hvm _ _ hvu⟩)
  · exact .inl (.inr ⟨fun u hu => hnu u ((PredAt_prefix push_pre (Nat.le_of_lt hlt)).2 hu), hz⟩)
  · refine .inr ⟨?_, hk⟩
    have hpc' : PlantCr (Cut Eg j' Sj) (stOf c.mem c.pairs thj) m tw (cr j' tw) := hpc
    obtain ⟨cl, hsto, hpne⟩ : ∃ cl, (Cut Eg j' Sj).sto m.loc.label = some cl ∧
        (Cut Eg j' Sj).pfr m.loc.label ≠ none :=
      let ⟨cl, _, _, _, _, _, _, h1, _, h3, _⟩ := hpc'; ⟨cl, h1, h3⟩
    have hsto2 : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).sto m.loc.label = some cl :=
      hI.sto _ _ hsto
    have hpfl : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).pfr m.loc.label =
        (Cut Eg j' Sj).pfr m.loc.label := hpf
    have hVis : Vis (Cut Eg j' Sj) m.loc.label := fun h => hpne h.2
    refine TermPlant.PlantCr_mono (E := Cut Eg j' Sj) (s := stOf c.mem c.pairs thj) push_pre
      (by show c.mem.size ≤ (c.mem.push ⟨a, v, w⟩).size; rw [Array.size_push]; exact Nat.le_succ _) rfl hPlt (hsto2.trans hsto.symm) rfl
      (fun h => by rw [hpfl]; exact h) (fun h => ?_) (fun t ht h => ?_)
      (fun S ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini) hpc'
    · have hstoEq : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).sto
          (⟨m.loc.label, m.loc.offset⟩ : Address).label =
          (Cut Eg j' Sj).sto (⟨m.loc.label, m.loc.offset⟩ : Address).label := by
        show _ = _; rw [hsto2]; exact hsto.symm
      have h' : WordUnit (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj)
          ⟨m.loc.label, m.loc.offset⟩ := h
      rw [WordUnit_congr hstoEq] at h'; exact h'
    · have h1 := FpAt_sub h
      change t ∈ fpProm Eg j c.mem.size j' at h1
      simp only [fpProm, hjj, ↓reduceIte] at h1
      rw [FpAt_vis (a := ⟨m.loc.label, 0⟩) hVis]
      rcases List.mem_append.1 h1 with h2 | h2
      · exact h2
      · rw [List.mem_singleton] at h2; subst h2; exact absurd ht (Nat.lt_irrefl _)


/-- **T16d `interfCrT`** (D2 §11, `PromCrK`), given B4 (a0): an idle thread's
credits move (old credits by `interfCrT_mover`, plant credits by
`PlantCr_mono`), and a `δ`-point is the thread's own promise whose old credit
plus `δ` is its `CrShiftP` plant credit (H8). -/
theorem interfCrTK_holds (hA0 : PromTyA0F p k arch Sp Init MintOK c0) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    CrShiftP c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') cr i δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      TermPlant.PromCrK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj)
        (fun t => cr j t + δ t) (db j) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hsh j thj Sj hji hj hold tw htw
  have hgf := gfoot_of X Y Z
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hmv := interfCrT_mover (Sj := Sj) hA0 X Y Z hji hj
  have hPlt : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => X.inv.plt j thj t hj ht
  have hpre := tctx_pre X
  have hsz : c.mem.size ≤ c'.mem.size := by
    apply Nat.le_of_not_lt; intro h
    have e := hpre _ h
    rw [Array.getElem?_eq_none (Nat.le_refl _), Array.getElem?_eq_getElem h] at e
    cases e
  obtain ⟨m, hm, hd, hc0⟩ := hold.2.2.2.2.2 tw htw
  have hlt := hPlt tw htw
  have hm' : c'.mem[tw]? = some m := by rw [hpre tw hlt]; exact hm
  refine ⟨m, hm', DbRes_mem hpre hlt
    (interfDb_mover (Sj := Sj) hA0 X Y Z hji hj _ tw m _ htw hm hd), ?_⟩
  show OldCr _ _ m tw (cr j tw + δ tw) ∨ (PlantCr _ _ m tw (cr j tw + δ tw) ∧ TermPlant.CrKeys (cr j tw + δ tw))
  by_cases hδ : δ tw = .zero
  · rw [hδ, Res.add_zero]
    rcases hc0 with (⟨u, hu, hvu⟩ | ⟨hnu, hz⟩) | ⟨hpc, hk⟩
    · exact .inl (.inl ⟨u, (PredAt_prefix hpre (Nat.le_of_lt hlt)).1 hu, hmv tw m _ _ htw hm hvu⟩)
    · exact .inl (.inr ⟨fun u hu => hnu u ((PredAt_prefix hpre (Nat.le_of_lt hlt)).2 hu), hz⟩)
    · refine .inr ⟨?_, hk⟩
      have hpc' : PlantCr (Cut Eg j Sj) (stOf c.mem c.pairs thj) m tw (cr j tw) := hpc
      obtain ⟨cl, hsto, hpne⟩ : ∃ cl, (Cut Eg j Sj).sto m.loc.label = some cl ∧
          (Cut Eg j Sj).pfr m.loc.label ≠ none :=
        let ⟨cl, _, _, _, _, _, _, h1, _, h3, _⟩ := hpc'; ⟨cl, h1, h3⟩
      have hsto2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto m.loc.label = some cl :=
        hI.sto _ _ hsto
      have hVis : Vis (Cut Eg j Sj) m.loc.label := fun h => hpne h.2
      refine TermPlant.PlantCr_mono (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) hpre hsz rfl hPlt
        (hsto2.trans hsto.symm) rfl (fun h hn => ?_) (fun h => ?_) (fun t ht h => ?_)
        (fun S ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini) hpc'
      · cases e : (Cut Eg j Sj).pfr m.loc.label with
        | none => exact h e
        | some f => exact absurd ((hI.pfr _ _ e).symm.trans hn) (fun h0 => by cases h0)
      · have hstoEq : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto
            (⟨m.loc.label, m.loc.offset⟩ : Address).label =
            (Cut Eg j Sj).sto (⟨m.loc.label, m.loc.offset⟩ : Address).label := by
          show _ = _; rw [hsto2]; exact hsto.symm
        have h' : WordUnit (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
            ⟨m.loc.label, m.loc.offset⟩ := h
        rw [WordUnit_congr hstoEq] at h'; exact h'
      · have h1 := FpAt_sub h
        change t ∈ fpSync Eg c' j at h1
        rw [FpAt_vis (a := ⟨m.loc.label, 0⟩) hVis]
        exact (List.mem_filter.1 h1).1
  · obtain ⟨j0, thj0, m0, -, hj0, ht0, hm0, hpl⟩ := hsh tw hδ
    have ej : j0 = j := by
      apply Classical.byContradiction; intro hne
      exact X.inv.disj j j0 thj thj0 tw (Ne.symm hne) hj hj0 htw ht0
    subst ej
    have e1 : thj0 = thj := Option.some.inj (hj0.symm.trans hj)
    subst e1
    have e2 : m0 = m := Option.some.inj (hm0.symm.trans hm')
    subst e2
    obtain ⟨hpc, hk⟩ := hpl Sj thj0 ((X.ho _ hji).trans hj)
    exact .inr ⟨hpc, hk⟩

/-- **P3′ `promSelfK`** (D2 §11): the promiser's plant credits survive its own
promise.  The new promise lies above every window bound (`wb < size`), so the
window, its pinned words and the lowest-promise clause are unchanged. -/
theorem promSelfK_holds :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {S : AllocLabel → Prop},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w → (∀ l, plantOf c Eg j a v w l = none) →
    ThSysAt p (gOf p k arch c j) c.mem c.pairs th Eg (Tot j) (HP j) HS (cr j) (db j) S →
    ∀ tw m, tw ∈ th.promises → c.mem[tw]? = some m →
      PlantCr (Cut Eg j S) (stOf c.mem c.pairs th) m tw (cr j tw) →
      PlantCr (Cut Eg j S) (promSt (stOf c.mem c.pairs th) a v w) m tw (cr j tw) := by
  intro c Eg Tot HP HS cr db j th a v w S X _ _ tw m _ _ h
  have hPlt : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  obtain ⟨c1, sb, S0, b0, S1, us, wb, hsto0, hown, hpf0, hseg, hat, hS, hwu0, hus, hn, hlo, hhi, htw, hwb, hfa,
    hlow, hR⟩ := h
  have hwb' : wb < c.mem.size := hwb
  have hpre : ∀ t, t < c.mem.size → (c.mem.push ⟨a, v, w⟩)[t]? = c.mem[t]? := push_pre
  have hwin : winL wb (th.promises ++ [c.mem.size]) = winL wb th.promises := by
    unfold winL
    rw [List.filter_append]
    have : List.filter (fun t => decide (t ≤ wb)) [c.mem.size] = [] := by
      simp only [List.filter_cons, List.filter_nil, decide_eq_true_eq, Nat.not_le.2 hwb', ↓reduceIte]
    rw [this, List.append_nil]
  refine ⟨c1, sb, S0, b0, S1, us, wb, hsto0, hown, hpf0, hseg, hat, hS, hwu0, hus, hn, hlo, hhi, htw,
    (show wb < (c.mem.push ⟨a, v, w⟩).size by rw [Array.size_push]; exact Nat.lt_succ_of_lt hwb'),
    fun tf mf h1 h2 h3 => ?_, fun t' m' h1 h2 h3 h4 h5 h6 => ?_, ?_⟩
  · by_cases hts : tf < c.mem.size
    · have h2' : (c.mem.push ⟨a, v, w⟩)[tf]? = some mf := h2
      rw [hpre tf hts] at h2'
      exact hfa tf mf h1 h2' h3
    · exact Nat.lt_of_lt_of_le hwb' (Nat.le_of_not_lt hts)
  · have h1' : t' ∈ th.promises ++ [c.mem.size] := h1
    rcases List.mem_append.1 h1' with h1 | h1
    · have h2' : (c.mem.push ⟨a, v, w⟩)[t']? = some m' := h2
      rw [hpre t' (hPlt t' h1)] at h2'
      exact hlow t' m' h1 h2' h3 h4 h5 h6
    · rw [List.mem_singleton] at h1; subst h1
      exact absurd (Nat.lt_of_le_of_lt h6 hwb') (Nat.lt_irrefl _)
  · rcases hR with ⟨K, ws, R0, hl, hv, hle, hp⟩ | e
    · refine Or.inl ⟨K, ws, R0, hl, hv, hle, fun i o w0 t' hK hI hw hL => ?_⟩
      have hL' : LowestIn (c.mem.push ⟨a, v, w⟩) (winL wb (th.promises ++ [c.mem.size])) _ t' := hL
      rw [hwin] at hL'
      have hW : ∀ t, t ∈ winL wb th.promises → t < c.mem.size :=
        fun t ht => hPlt t (TermPlant.mem_winL.1 ht).1
      have hL0 := TermPlant.LowestIn_back hW hpre hL'
      exact TermPlant.PredAt_mono (hW t' hL0.1) hpre (hp i o w0 t' hK hI hw hL0)
    · exact Or.inr e
end

/-! ## Pairs only grow (`tstep_pairsUp`, the converse of `TermFul.tstep_grow`) -/

section
open TermFul

/-- `pairs'` keeps every entry of `pairs`. -/
def PairsUp (pairs pairs' : List Ts) : Prop := ∀ q, q ∈ pairs → q ∈ pairs'

theorem PairsUp.refl (pairs : List Ts) : PairsUp pairs pairs := fun _ h => h

theorem PairsUp.trans {p1 p2 p3 : List Ts} (a : PairsUp p1 p2) (b : PairsUp p2 p3) : PairsUp p1 p3 :=
  fun q h => b q (a q h)

theorem pairsUp_eq {pairs pairs' : List Ts} (h : pairs' = pairs) : PairsUp pairs pairs' := by
  subst h; exact PairsUp.refl _

theorem stepRmwPair_pairsUp {arch : Arch} {mem : Memory} {pairs : List Ts}
    {th : Promises.Thread} {dst0 dst1 : WeakMem.Reg} {a : Address} {cmp0 cmp1 : WeakMem.Val}
    {new0 new1 : WeakMem.Expr} {deps : List WeakMem.Reg} {acq rel : Bool}
    {x : Memory × List Ts × Promises.Thread}
    (h : x ∈ Promises.stepRmwPair arch mem pairs th dst0 dst1 a cmp0 cmp1 new0 new1 deps acq rel) :
    PairsUp pairs x.2.1 := by
  rcases stepRmwPair_shape (mem' := x.1) (pairs' := x.2.1) (th' := x.2.2) h with ⟨-, h2⟩ | ⟨-, h2, -⟩
  · exact pairsUp_eq h2
  · intro q hq; rw [h2]; exact List.mem_append_left _ hq

theorem storeUnits_pairsUp {k : Promises.Knobs} {arch : Arch} {pw : Word} {a : Address} {rel : Bool} :
    ∀ (us : List Acc) (ws : List Word) (i : Nat) (s s' : St), s' ∈ storeUnits k arch pw a rel us ws i s →
      PairsUp s.pairs s'.pairs
  | [], _, _, s, s', hs => by
      simp only [storeUnits, List.mem_singleton] at hs; subst hs; exact PairsUp.refl _
  | .one :: us, w :: ws, i, s, s', hs => by
      simp only [storeUnits, List.mem_flatMap] at hs
      obtain ⟨⟨mem', th⟩, -, hs⟩ := hs
      have := storeUnits_pairsUp us ws (i + 1) _ s' hs
      exact this
  | .two :: us, w0 :: w1 :: ws, i, s, s', hs => by
      simp only [storeUnits] at hs
      obtain ⟨-, ⟨m0, m1, q1, -, -⟩, q2, -, -⟩ := stepStorePair_shape s.mem s.pairs (mth s pw w0 w1)
        (offs a i) (dataE 1 w0) (dataE 2 w1) [0] rel
      generalize Promises.stepStorePair s.mem s.pairs (mth s pw w0 w1) (offs a i) (dataE 1 w0)
        (dataE 2 w1) [0] rel = R at q1 q2 hs
      obtain ⟨mem', pairs', th⟩ := R
      simp only at q1 q2
      refine PairsUp.trans ?_ (storeUnits_pairsUp us ws (i + 2) _ s' hs)
      intro q hq
      change q ∈ pairs'
      rw [q2]; exact List.mem_append_left _ hq
  | .one :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [], _, _, s', hs => by simp [storeUnits] at hs
  | .two :: _, [_], _, _, s', hs => by simp [storeUnits] at hs

theorem alloc_pairsUp {k : Promises.Knobs} {arch : Arch} {lbl : AllocLabel} {us : List Acc}
    {ws : List Word} {s : St} {r : St × Word} (hr : r ∈ alloc k arch lbl us ws s) : PairsUp s.pairs r.1.pairs := by
  simp only [alloc, List.mem_map] at hr
  obtain ⟨s', hs, rfl⟩ := hr
  have := storeUnits_pairsUp _ _ _ _ s' hs
  exact this

theorem allocBuf_pairsUp {lbl : AllocLabel} {n : Nat} {zero : Option (List WeakMem.Val)} {s : St} :
    PairsUp s.pairs (allocBuf lbl n zero s).1.pairs := by
  unfold allocBuf
  exact PairsUp.refl _

theorem injM_pairsUp {g : G} {s : St} {ty : Ty} {j : Nat} {p : List Word} {r : St × List Word}
    (h : r ∈ injM g s ty j p) : PairsUp s.pairs r.1.pairs := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map] at h
      obtain ⟨⟨s', pw⟩, hs, rfl⟩ := h
      have := alloc_pairsUp hs
      dsimp only
      split
      · exact this
      · exact this
    · cases h
  · simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
    obtain ⟨x, -, rfl⟩ := h
    exact PairsUp.refl _

theorem pairsUp_load {s s' : St} (h : s'.mem = s.mem ∧ s'.pairs = s.pairs ∧ s'.promises = s.promises) :
    PairsUp s.pairs s'.pairs := pairsUp_eq h.2.1

theorem evalOp_pairsUp {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : PairsUp s.pairs r.1.pairs := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact PairsUp.refl _ | exact allocBuf_pairsUp)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact pairsUp_load (loadUnits_keep _ _ _ _ hx)
         | exact storeUnits_pairsUp _ _ _ _ _ hx
         | exact alloc_pairsUp hx
         | exact PairsUp.refl _)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact (pairsUp_load (projM_keep hx)).trans (injM_pairsUp hy)
         | exact (pairsUp_load (loadUnits_keep _ _ _ _ hx)).trans (storeUnits_pairsUp _ _ _ _ _ hy))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact (pairsUp_load (loadUnits_keep _ _ _ _ hx)).trans (storeUnits_pairsUp _ _ _ _ _ hy)
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact pairsUp_load (loadUnits_keep _ _ _ _ hx))
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact allocBuf_pairsUp)

/-- **A thread step keeps every pair entry.** -/
theorem tstep_pairsUp {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) : PairsUp pairs r.2.1 := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact PairsUp.refl _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact PairsUp.refl _)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', -, rfl⟩ := h
       exact PairsUp.refl _)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_pairsUp hx
         | exact PairsUp.refl _
         | exact stepRmwPair_pairsUp hx)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact (pairsUp_load (projM_keep hx)).trans (injM_pairsUp hy))

end

/-! ## MemInv of an idle thread (T16b), clause by clause -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The type of a T16b clause: clause `Q` of an idle thread's `MemInv` at the
new cut and memory. -/
def MemClT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Q : G → TEnv → St → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      Q (gOf p k arch c j) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj)

/-- `MemClT` with the stepper's `ThSysAt` at its cut and its frontier change only at its publish
(certWin-D: the facts that start the stepper's run at the successor, `TermXFO.anchPost`). -/
def MemClTH (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Q : G → TEnv → St → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      Q (gOf p k arch c j) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj)

/-- `MemClT` with the stepper's frontier change only at its publish (`PfrG` at `pf := PubAt th`). -/
def MemClTP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (Q : G → TEnv → St → Prop) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      Q (gOf p k arch c j) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj)

/-- **T16b `interfMemT` from its eleven clauses.** -/
theorem interfMemT_of_clauses
    (h1 : MemClTP p k arch Sp Init MintOK c0 fun _ E s => MemOKP E s.mem s.pairs s.promises)
    (h2 : MemClT p k arch Sp Init MintOK c0 fun _ E s => OwnOKPF E s.mem s.pairs s.vs s.promises)
    (h3 : MemClT p k arch Sp Init MintOK c0 fun _ _ s => PromLt s)
    (h4 : MemClT p k arch Sp Init MintOK c0 fun g E s => FreshLP g E s)
    (h5 : MemClT p k arch Sp Init MintOK c0 fun _ E s => SeenLE E s.vs.vRelSt)
    (h6 : MemClT p k arch Sp Init MintOK c0 fun _ E s => OwnHidP E s.mem s.vs s.promises)
    (h7 : MemClTP p k arch Sp Init MintOK c0 fun _ E s => PubDefP E s.mem s.promises)
    (h8 : MemClT p k arch Sp Init MintOK c0 fun _ E s => OwnPubV E s)
    (h9 : MemClTH p k arch Sp Init MintOK c0 fun _ E s => PubInv E s)
    (h10 : MemClTH p k arch Sp Init MintOK c0 fun g E s => BoxInv g E s)
    (h11 : MemClT p k arch Sp Init MintOK c0 fun _ _ s => PromOK s) :
    ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      MemInv (gOf p k arch c j) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS j thj Sj hji hj hold
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  exact ⟨h1 X Y Z hPub hPfrP hS j thj Sj hji hj hold, h2 X Y ZC j thj Sj hji hj hold, h3 X Y ZC j thj Sj hji hj hold,
    h4 X Y ZC j thj Sj hji hj hold, h5 X Y ZC j thj Sj hji hj hold, h6 X Y ZC j thj Sj hji hj hold,
    h7 X Y Z hPub hPfrP hS j thj Sj hji hj hold, h8 X Y ZC j thj Sj hji hj hold, h9 X Y ZC hS hPfrP j thj Sj hji hj hold,
    h10 X Y ZC hS hPfrP j thj Sj hji hj hold, h11 X Y ZC j thj Sj hji hj hold⟩

/-- (EFoot conjunct) **`rini` changes only at fresh labels or
own cells of the stepper**, at the step's S6 witness. -/
def RiniFootF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ l, E'.rini l = (CE η).rini l ∨ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l ∨ OwnAt (CE η) l

/-- At a cell not of the stepper, `E_g` keeps cell, frontier and count. -/
theorem tctx_other_cell {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} {cl : Cell} (hc : Eg.sto l = some cl) (ho : cl.owner ≠ some i) :
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl ∧
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = Eg.pfr l ∧
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l := by
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
    rw [(hfr l hF).1] at hc; cases hc
  refine ⟨(hgf.sto_old hnF).trans hc, ?_, gfoot_ini_other hgf hfr hc ho⟩
  rcases hgf.2.2.2.2.1 l with e | ⟨-, -, -, -, cl', hc', ho'⟩ | ⟨hF, -⟩
  · exact e
  · rw [hc] at hc'; cases hc'; exact absurd ho' ho
  · exact absurd hF hnF

/-- With `RiniFootF`, the real count too. -/
theorem tctx_other_rini (hri : RiniFootF p k arch Sp Init MintOK c0) {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} {cl : Cell} (hc : Eg.sto l = some cl) (ho : cl.owner ≠ some i) :
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').rini l = Eg.rini l := by
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  show E'.rini l = Eg.rini l
  rcases hri X Y Z l with e | hF | ⟨c1, hc1, ho1⟩
  · rw [e, Y.1]; rfl
  · rw [(hfr l hF).1] at hc; cases hc
  · rw [Y.1] at hc1 ho1
    rw [cutSto_sub hc1] at hc; cases hc
    exact absurd ho1 ho

/-- A cell of the idle thread `j` stays in its cut. -/
theorem tctx_jcut {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} (hji : j ≠ i) {l : AllocLabel} {cl : Cell} :
    cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j l = some cl → cl.owner = some j →
      Eg.sto l = some cl ∧ cutSto Eg j l = some cl := by
  intro hc ho
  have hgf := gfoot_of X Y Z
  have hc2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l = some cl := cutSto_sub hc
  rcases hgf.2.1 l with e | ⟨-, -, -, T, hT⟩
  · rw [e] at hc2; exact ⟨hc2, cutSto_own hc2 ho⟩
  · rw [hT] at hc2; cases hc2; exact absurd ho.symm (by intro h; exact hji (Option.some.inj h))

/-- Away from the stepper's fresh labels and cells, `E_g` is unchanged. -/
theorem tctx_notI {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} (hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l) (hnO : ¬ Eg.OwnAt i l) :
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = Eg.sto l ∧
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = Eg.pfr l ∧
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l ∧
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').box l = Eg.box l := by
  have hgf := gfoot_of X Y Z
  refine ⟨hgf.sto_old hnF, ?_, ?_, post_box_old hnF⟩
  · rcases hgf.2.2.2.2.1 l with e | ⟨-, -, -, -, hO⟩ | ⟨hF, -⟩
    · exact e
    · exact absurd hO hnO
    · exact absurd hF hnF
  · rcases (hgf.2.2.2.1 l).2 with e | hF | hO
    · exact e
    · exact absurd hF hnF
    · exact absurd hO hnO

/-- Clause 10 (`BoxInv`), given `NoBoxPromF`. -/
theorem cl10_boxInv (hnb : NoBoxPromF p k arch Sp Init MintOK c0) :
    MemClTH p k arch Sp Init MintOK c0 fun g E s => BoxInv g E s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr j thj Sj hji hj hold
  have hj' : c'.ths[j]? = some thj := by rw [X.ho j hji]; exact hj
  have hold10 := hold.2.2.1.2.2.2.2.2.2.2.2.2.1
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  refine ⟨fun jj hjj => ?_, BoxTopP_of_G (boxtopT_holds hnb X Y Z hS hPfr) (fun t ht => mem_allProms.2 ⟨j, thj, hj', ht⟩),
    fun l B hB => ?_⟩
  · have hG := freshT_holds X Y Z j thj hj' jj hjj
    rw [(threadSteps_lbase X.hc').1, TermStep.threadSteps_n X.hc'] at hG
    exact hG.2.1
  · have hB' : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').box l = some B := hB
    by_cases hF : FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l
    · rw [post_box_fresh hF] at hB'
      obtain ⟨hs0, hi0, -⟩ := Z.2.2.1.2.2.2.2.2.2.2.2.2.1.2.2 l B hB'
      refine ⟨?_, ?_, fun hs => ?_⟩
      · show cutSto _ j l = none
        cases e : cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j l with
        | none => rfl
        | some cl =>
          have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l = some cl := cutSto_sub e
          rw [post_sto_fresh hF, hs0] at h2; cases h2
      · exact hi0
      · obtain ⟨f, hf, -⟩ := hold.2.2.1.2.2.2.2.1 l hs
        have hf' : Eg.pfr l = some f := hf
        rw [(hfr l hF).2.2] at hf'; cases hf'
    · rw [post_box_old hF] at hB'
      obtain ⟨hcj, hij, hsj⟩ := hold10.2.2 l B hB'
      have hci : cutSto Eg i l = none := (hm0.2.2.2.2.2.2.2.2.2.1.2.2 l B hB').1
      have hnO : ¬ Eg.OwnAt i l := fun ⟨cl, hc, ho⟩ => by rw [cutSto_own hc ho] at hci; cases hci
      obtain ⟨hs1, hp1, hi1, -⟩ := tctx_notI X Y Z hF hnO
      refine ⟨?_, hi1.trans hij, fun hs => (hsj hs).imp fun o w h => ?_⟩
      · show cutSto _ j l = none
        have hcj' : cutSto Eg j l = none := hcj
        rw [cutSto_congr hs1 (fun _ _ _ => by unfold GEnv.Shared; rw [hp1])]
        exact hcj'
      · refine LatestS_grow (tctx_pre X) (fun t m h1 h2 e => ?_) h
        have e' : m.loc.label = l := e
        rcases tctx_writeAt X t m h1 h2 with hF' | ⟨cl, hc⟩
        · rw [e'] at hF'; exact hF hF'
        · rw [e', hci] at hc; cases hc

/-- Pairs of the step: old ones, or at new messages (`tstep_grow`). -/
theorem tctx_pairs {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) :
    ∀ q, q ∈ c'.pairs → q ∈ c.pairs ∨ c.mem.size ≤ q := by
  intro q hq
  rw [X.e2] at hq
  exact ((TermFul.tstep_grow X.hr).2 q hq).imp id (fun h => h.1)

/-- Clause 11 (`PromOK`). -/
theorem cl11_promOK : MemClT p k arch Sp Init MintOK c0 fun _ _ s => PromOK s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold
  obtain ⟨hnd, hnp, hnp1⟩ := hold.2.2.1.2.2.2.2.2.2.2.2.2.2
  have hlt : ∀ t, t ∈ thj.promises → t < c.mem.size := fun t ht => hold.2.2.1.2.2.1 t ht
  refine ⟨hnd, fun t ht hp => ?_, fun t ht q hq e => ?_⟩
  · rcases tctx_pairs X t hp with h | h
    · exact hnp t ht h
    · exact absurd (hlt t ht) (Nat.not_lt.2 h)
  · rcases tctx_pairs X q hq with h | h
    · exact hnp1 t ht q h e
    · exact absurd (hlt t ht) (by rw [e]; exact Nat.not_lt.2 (Nat.le_succ_of_le h))

/-- The stepper's witness is its new cut. -/
theorem tctx_cut {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ) :
    Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen = E' := by
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  have hself := Cut_self (g := gOf p k arch c i) hF0 (X.inv.gfresh X.hth _)
  have hEE : CE E' = E' := by
    obtain ⟨_, η', _, _, _, hce', -⟩ := Z.2.1
    rw [← hce']
    rfl
  have hfs : fpSync Eg c' i = Eg.fpOf i := fpSync_self X.inv.proms X.inv.fpfree X.hth X.ho
  exact (Cut_withFp (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E') (fpSync Eg c') _ E'.seen hfs).trans
    (hself.symm.trans hEE)


/-- `PromTyAOK` after a thread step (the SysInvN clause (a) at the new
configuration, kept by the thread-step obligation). -/
def PromTyAPostF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PromTyAOK (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c'

/-- (B3) **PromTyOK (a0) after a thread step**: every outstanding promise at a shared cell of
`EgT` lies at an initialised offset (preservation of `SysInvN.promIni`). -/
def PromIniPostF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ crS : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) crS (db i) δ →
    (∀ l, TermOwnG0Defs.PubAt th l → ∀ t, crS t = cr i t) →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PromIniOK (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') c'

/-- Clause 1 (`MemOKP`), given `PromTyAPostF` (only used at labels the step
newly shares, for the stepper's own remaining promises there). -/
theorem cl1_memOKP (hpa : PromTyAPostF p k arch Sp Init MintOK c0) :
    MemClTP p k arch Sp Init MintOK c0 fun _ E s => MemOKP E s.mem s.pairs s.promises := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS j thj Sj hji hj hold
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hgf := gfoot_of X Y ZC
  have hCut := tctx_cut X Y ZC
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hIS : InclS E' (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) := by
    have h := InclS_cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i j E'.seen Sj
    rw [hCut] at h; exact h
  have hm' := ZC.2.2.1
  have hold1 := hold.2.2.1.1
  -- a shared label of the new `E_g` is a cell of `E'` with a `noOR` type
  have hsh : ∀ l cl f, (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f →
      E'.sto l = some cl ∧ noOR cl.ty = true := fun l cl f hc hf => by
    have hs' : E'.sto l = some cl := by
      have h : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto l = some cl :=
        cutSto_shared hc ⟨f, hf⟩
      rw [hCut] at h; exact h
    have hf' : E'.pfr l = some f := by
      have h : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).pfr l = some f := hf
      rw [hCut] at h; exact h
    obtain ⟨-, -, -, h4, h5⟩ := hm'.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hs' hf'
    exact ⟨hs', noOR_of _ _ h4 h5⟩
  -- an unshared cell of `j`'s new cut is a private cell of `j`, untouched by the step
  have hpriv : ∀ l cl, cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j l = some cl →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = none →
      cutSto Eg j l = some cl ∧ Priv (Cut Eg j Sj) l := fun l cl hc hp => by
    obtain ⟨h1, h2⟩ := cutSto_some.1 hc
    rcases h2 with h2 | ⟨f, hf⟩
    · obtain ⟨hc1, hc0⟩ := tctx_jcut X Y ZC hji hc h2
      refine ⟨hc0, ⟨cl, hc0, h2⟩, ?_⟩
      show Eg.pfr l = none
      cases e : Eg.pfr l with
      | none => rfl
      | some f => have := hgf.le.pfr l f e; exact absurd (hp.symm.trans this) (by simp)
    · have hf' : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
      rw [hp] at hf'; cases hf'
  refine ⟨fun t m cl hn hm hc => ?_, fun t m0 m1 cl hp h0 h1 hc => ?_, fun t ht => ?_⟩
  · cases ep : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr m.loc.label with
    | some f =>
      obtain ⟨hs', hT⟩ := hsh _ cl f (cutSto_sub hc) ep
      by_cases hti : t ∈ r.2.2.promises
      · have hpt := hpa X Y Z hPub hPfrP hS i r.2.2 t m X.e3 hti hm cl (cutSto_sub hc) ⟨f, ep⟩
        exact .inr (WordOK_transferS (InclS_pub_cut _ j Sj) hT hpt)
      · rcases hm'.1.1 t m cl hti (by rw [← X.e1]; exact hm) hs' with h | h
        · exact .inl h
        · exact .inr (WordOK_transferS hIS hT h)
    | none =>
      obtain ⟨hc0, hpv⟩ := hpriv _ cl hc ep
      have hm1 : c'.mem[t]? = some m := hm
      rcases Nat.lt_or_ge t c.mem.size with h1 | h1
      · rw [tctx_pre X t h1] at hm1
        rcases hold1.1 t m cl hn hm1 hc0 with h | h
        · exact .inl h
        · exact .inr (WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini)
      · exact absurd rfl (tctx_noNewPriv X hji hpv t m h1 hm1)
  · cases ep : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr m0.loc.label with
    | some f =>
      obtain ⟨hs', hT⟩ := hsh _ cl f (cutSto_sub hc) ep
      have hp' : t ∈ r.2.1 := by rw [← X.e2]; exact hp
      have := hm'.1.2.1 t m0 m1 cl hp' (by rw [← X.e1]; exact h0) (by rw [← X.e1]; exact h1) hs'
      exact PairOK_transferS hIS hT this
    | none =>
      obtain ⟨hc0, hpv⟩ := hpriv _ cl hc ep
      have h0' : c'.mem[t]? = some m0 := h0
      have h1' : c'.mem[t + 1]? = some m1 := h1
      rcases tctx_pairs X t hp with hpo | hpn
      · have hlt : t + 1 < c.mem.size := hold1.2.2 t hpo
        rw [tctx_pre X t (Nat.lt_of_succ_lt hlt)] at h0'
        rw [tctx_pre X (t + 1) hlt] at h1'
        exact PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) (hold1.2.1 t m0 m1 cl hpo h0' h1' hc0)
          hI.box hI.rini
      · exact absurd rfl (tctx_noNewPriv X hji hpv t m0 hpn h0')
  · have ht' : t ∈ r.2.1 := by rw [← X.e2]; exact ht
    have := hm'.1.2.2 t ht'
    show t + 1 < c'.mem.size
    rw [X.e1]; exact this

/-- `E'` (the stepper's new cut) is in every idle cut's shared part. -/
theorem tctx_inclS {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (j : Nat) (Sj : AllocLabel → Prop) :
    InclS E' (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) := by
  have h := InclS_cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i j E'.seen Sj
  rw [tctx_cut X Y Z] at h; exact h

/-- A shared label of the new `E_g` is a cell of `E'`, with its frontier, of a
`noOR` type (the stepper's `PubCpl`). -/
theorem tctx_shared {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} {cl : Cell} {f : Ts}
    (hc : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl)
    (hf : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f) :
    E'.sto l = some cl ∧ E'.pfr l = some f ∧ noOR cl.ty = true := by
  have hCut := tctx_cut X Y Z
  have hs' : E'.sto l = some cl := by
    have h : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).sto l = some cl :=
      cutSto_shared hc ⟨f, hf⟩
    rw [hCut] at h; exact h
  have hf' : E'.pfr l = some f := by
    have h : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i E'.seen).pfr l = some f := hf
    rw [hCut] at h; exact h
  obtain ⟨-, -, -, h4, h5⟩ := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hs' hf'
  exact ⟨hs', hf', noOR_of _ _ h4 h5⟩

/-- (B2 at an idle thread's cell) A new message at an initialised offset of a
cell of `j` is a typed word in `j`'s new cut. -/
theorem tctx_newOK_j {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {j : Nat} (hji : j ≠ i) (Sj : AllocLabel → Prop) {l : AllocLabel} {cl : Cell} {o : Nat}
    (hc : Eg.sto l = some cl) (ho : cl.owner = some j)
    (hI : InitR (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o)
    {t : Nat} {m : Msg} (ht : c.mem.size ≤ t) (hm : c'.mem[t]? = some m) (hl : m.loc = ⟨l, o⟩) :
    WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m) := by
  have hoi : cl.owner ≠ some i := by rw [ho]; intro h; exact hji (Option.some.inj h)
  obtain ⟨hs2, hp2, -⟩ := tctx_other_cell X Y Z hc hoi
  cases ep : Eg.pfr l with
  | none =>
    exact absurd (congrArg Address.label hl) (tctx_noNewPriv X hji (S := Sj) ⟨⟨cl, cutSto_own hc ho, ho⟩, ep⟩ t m ht hm)
  | some f =>
    rw [ep] at hp2
    obtain ⟨hs', hf', hT⟩ := tctx_shared X Y Z hs2 hp2
    obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
    have hnp : t ∉ r.2.2.promises :=
      tstep_newNotProm (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr ht
    have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
    have hw := newMsg_wordOK_other Z.2.2.1 hs' (by rw [htid]; exact hoi) hf' (X.inv.frle l cl f hc ep) hI ht hnp
      (by rw [← X.e1]; exact hm) hl
    exact WordOK_transferS (tctx_inclS X Y Z j Sj) hT hw

/-- `HiddenP` moves along a growing environment and memory whose new messages at
the address are typed. -/
theorem HiddenP_move {η₁ η₂ : TEnv} {T : Ty} {mem mem' : Memory} {P : List Ts} {l : AllocLabel} {o : Nat} {V : Ts}
    (hpre : ∀ t, t < mem.size → mem'[t]? = mem[t]?)
    (hnew : ∀ (t : Nat) (m : Msg), mem.size ≤ t → mem'[t]? = some m → m.loc = ⟨l, o⟩ → WordOK η₂ T o (mw m))
    (hmono : ∀ w, WordOK η₁ T o w → WordOK η₂ T o w)
    (h : HiddenP η₁ T mem P l o V) : HiddenP η₂ T mem' P l o V := by
  intro t m hn hm hl hw
  rcases Nat.lt_or_ge t mem.size with h1 | h1
  · rw [hpre t h1] at hm
    obtain ⟨t', m', h2, h3, h4, h5⟩ := h t m hn hm hl (fun h' => hw (hmono _ h'))
    exact ⟨t', m', h2, h3, by rw [hpre t' (lt_of_get h4)]; exact h4, h5⟩
  · exact absurd (hnew t m h1 hm hl) hw

/-- Clause 6 (`OwnHidP`), given `RiniFootF`. -/
theorem cl6_ownHidP (hri : RiniFootF p k arch Sp Init MintOK c0) :
    MemClT p k arch Sp Init MintOK c0 fun _ E s => OwnHidP E s.mem s.vs s.promises := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold
  have hgf := gfoot_of X Y Z
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hmono : ∀ T o w, WordOK (Cut Eg j Sj) T o w →
      WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) T o w :=
    fun T o w h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini
  obtain ⟨hA, hB⟩ := hold.2.2.1.2.2.2.2.2.1
  -- counts at a cell of `j`
  have hcnt : ∀ l cl, Eg.sto l = some cl → cl.owner = some j →
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l ∧
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').rini l = Eg.rini l ∧
      (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = Eg.pfr l := fun l cl hc ho => by
    have hoi : cl.owner ≠ some i := by rw [ho]; intro h; exact hji (Option.some.inj h)
    exact ⟨(tctx_other_cell X Y Z hc hoi).2.2, tctx_other_rini hri X Y Z hc hoi, (tctx_other_cell X Y Z hc hoi).2.1⟩
  refine ⟨fun l cl hc ho o hr => ?_, fun l cl hc ho hlt => ?_⟩
  · have ho' : cl.owner = some j := ho
    obtain ⟨hc1, hc0⟩ := tctx_jcut X Y Z hji hc ho'
    obtain ⟨hi1, hr1, -⟩ := hcnt l cl hc1 ho'
    have hrr : InitRr (Cut Eg j Sj) cl l o := fun N e us hT hu => by
      have := hr N e us hT hu
      unfold TEnv.rc at this ⊢
      rw [Cut_ini, Cut_rini, hi1, hr1] at this
      exact this
    exact HiddenP_move (tctx_pre X) (fun t m h1 h2 h3 => tctx_newOK_j X Y Z hji Sj hc1 ho' hr.initR h1 h2 h3)
      (hmono _ _) (hA l cl hc0 ho' o hrr)
  · have ho' : cl.owner = some j := ho
    obtain ⟨hc1, hc0⟩ := tctx_jcut X Y Z hji hc ho'
    obtain ⟨hi1, hr1, hp1⟩ := hcnt l cl hc1 ho'
    have hlt0 : (Cut Eg j Sj).rc l < (Cut Eg j Sj).ini l := by
      unfold TEnv.rc at hlt ⊢
      rw [Cut_ini, Cut_rini] at hlt ⊢
      rw [hi1, hr1] at hlt
      exact hlt
    obtain ⟨f, hf, hns, hH⟩ := hB l cl hc0 ho' hlt0
    refine ⟨f, by rw [Cut_pfr, hp1]; exact hf, fun hz => hns (fun hz0 => hz ((ZW.stoAt (hc.trans hc0.symm)).2 hz0)),
      fun o hio => ?_⟩
    have hio0 : InitR (Cut Eg j Sj) cl l o := fun N e us hT hu => by
      have := hio N e us hT hu
      rw [Cut_ini, hi1] at this
      exact this
    exact HiddenP_move (tctx_pre X) (fun t m h1 h2 h3 => tctx_newOK_j X Y Z hji Sj hc1 ho' hio h1 h2 h3)
      (hmono _ _) (hH o hio0)


/-! ### Clause 9 (`PubInv`) in parts -/

/-- Every word of a segment is covered by a cell's words. -/
theorem seg_cover {η : TEnv} {n : Nat} {T S : Ty} {vals : List Word} {b o : Nat} {us : List Acc}
    (hc : CellOK η n T vals) (hs : SegOf T b S) (hu : accs S = some us) (ho : o < nWords us) :
    b + o < vals.length := by
  rcases hs with ⟨rfl, rfl, -⟩ | ⟨N, us', j, rfl, hus', hj, rfl⟩
  · rcases hc with ⟨hwc, -⟩ | ⟨N, e, us2, hT, -, -, -, -⟩
    · rw [wc_of_accs hu] at hwc; have := Option.some.inj hwc; omega
    · have := wc_of_accs hu; rw [hT, wc_array] at this; cases this
  · rw [hu] at hus'; cases hus'
    rcases hc with ⟨hwc, -⟩ | ⟨N2, e, us2, hT, hus2, -, hlen, -⟩
    · rw [wc_array] at hwc; cases hwc
    · simp only [Ty.array.injEq, Idx.lit.injEq] at hT
      obtain ⟨rfl, rfl⟩ := hT
      rw [hu] at hus2; cases hus2
      rw [hlen]
      have h1 : j * nWords us + o < (j + 1) * nWords us := by rw [Nat.succ_mul]; omega
      exact Nat.lt_of_lt_of_le h1 (Nat.mul_le_mul_right _ hj)

/-- `PubInv` from its parts. -/
theorem cl9_of_parts
    (ha : MemClT p k arch Sp Init MintOK c0 fun _ E _ => SeenOwn E)
    (hb : MemClT p k arch Sp Init MintOK c0 fun _ E _ => Inh E)
    (hc : MemClT p k arch Sp Init MintOK c0 fun _ E _ => PubCpl E)
    (hd : MemClTH p k arch Sp Init MintOK c0 fun _ E s => PubPair E s.mem s.pairs s.promises)
    (he : MemClT p k arch Sp Init MintOK c0 fun _ E s => PubLive E s.mem) :
    MemClTH p k arch Sp Init MintOK c0 fun _ E s => PubInv E s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr j thj Sj hji hj hold
  exact ⟨ha X Y Z j thj Sj hji hj hold, hb X Y Z j thj Sj hji hj hold, hc X Y Z j thj Sj hji hj hold,
    hd X Y Z hS hPfr j thj Sj hji hj hold, he X Y Z j thj Sj hji hj hold⟩

/-- Clause 9a (`SeenOwn`). -/
theorem cl9a_seenOwn : MemClT p k arch Sp Init MintOK c0 fun _ E _ => SeenOwn E := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l hl
  have hgf := gfoot_of X Y Z
  rcases hold.2.2.1.2.2.2.2.2.2.2.2.1.1 l hl with ⟨cl, hc, ho⟩ | ⟨hn, hb⟩
  · have hc1 : Eg.sto l = some cl := cutSto_sub hc
    exact .inl ⟨cl, cutSto_own (Eg := EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (hgf.le.sto l cl hc1) ho, ho⟩
  · obtain ⟨f, hf, -⟩ := hold.2.2.1.2.2.2.2.1 l hl
    have hf' : Eg.pfr l = some f := hf
    have hn' : Eg.sto l = none := by
      have h := hn
      have e : cutSto Eg j l = Eg.sto l := cutSto_eq_shared ⟨f, hf'⟩
      exact e ▸ h
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
      rw [((X.inv.gfresh X.hth _) l hF).2.2] at hf'; cases hf'
    refine .inr ⟨?_, fun e => hb ?_⟩
    · show cutSto _ j l = none
      cases e : cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j l with
      | none => rfl
      | some cl =>
        have h2 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').sto l = some cl := cutSto_sub e
        rw [hgf.sto_old hnF, hn'] at h2; cases h2
    · cases eb : Eg.box l with
      | none => exact eb
      | some B => have := hgf.le.box l B eb; exact absurd (this.symm.trans e) (by simp)

/-- Clause 9c (`PubCpl`): the stepper's `PubCpl` at its new cut. -/
theorem cl9c_pubCpl : MemClT p k arch Sp Init MintOK c0 fun _ E _ => PubCpl E := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l cl f hc hf
  obtain ⟨hs', hf', -⟩ := tctx_shared X Y Z (cutSto_sub hc) hf
  exact Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hs' hf'

/-- Clause 9b (`Inh`). -/
theorem cl9b_inh : MemClT p k arch Sp Init MintOK c0 fun _ E _ => Inh E := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l cl b S1 us hc hs hu hi
  have hgf := gfoot_of X Y Z
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  cases ep : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l with
  | some f =>
    obtain ⟨hs', -, hT⟩ := tctx_shared X Y Z (cutSto_sub hc) ep
    obtain ⟨ws, hv, hl⟩ := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.1 l cl b S1 us hs' hs hu hi
    exact ⟨ws, ValOf_transferS (tctx_inclS X Y Z j Sj) (noOR_seg hs hT) hv, hl⟩
  | none =>
    obtain ⟨-, h2⟩ := cutSto_some.1 hc
    rcases h2 with h2 | ⟨f, hf⟩
    · obtain ⟨hc1, hc0⟩ := tctx_jcut X Y Z hji hc h2
      have hoi : cl.owner ≠ some i := by rw [h2]; intro h; exact hji (Option.some.inj h)
      have hini := (tctx_other_cell X Y Z hc1 hoi).2.2
      have hi0 : IniSeg (Cut Eg j Sj) cl l b := by
        unfold IniSeg at hi ⊢; rw [Cut_ini] at hi ⊢; rw [hini] at hi; exact hi
      obtain ⟨ws, hv, hl⟩ := hold.2.2.1.2.2.2.2.2.2.2.2.1.2.1 l cl b S1 us hc0 hs hu hi0
      exact ⟨ws, ValOf_mono hI.prog rfl hI.sto hI.ini hv hI.pfr (fun _ h => h) hI.box hI.rini, hl⟩
    · rw [ep] at hf; cases hf

/-- Clause 9e (`PubLive`). -/
theorem cl9e_pubLive : MemClT p k arch Sp Init MintOK c0 fun _ E s => PubLive E s.mem := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l cl f b S1 us o hc ho hf hs hu hlt
  obtain ⟨hs', hf', -⟩ := tctx_shared X Y Z (cutSto_sub hc) hf
  have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
  by_cases hoi : cl.owner = some i
  · obtain ⟨vals, hcv, hl, -⟩ := Z.2.2.1.2.1 l cl hs' (by rw [htid]; exact hoi)
    have hcov := seg_cover hcv hs hu hlt
    obtain ⟨⟨m, hm, hma, -⟩, -, -⟩ := hl (b + o) _ (List.getElem?_eq_getElem hcov)
    exact ⟨_, m, by rw [X.e1]; exact hm, hma⟩
  · obtain ⟨t, m, hm, hma⟩ := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.2 l cl f b S1 us o hs' (by rw [htid]; exact hoi) hf' hs hu hlt
    exact ⟨t, m, by rw [X.e1]; exact hm, hma⟩


/-! ### Clause 7 (`PubDefP`) -/

/-- **A frontier newly set by a step is at least the
stepper's new `vWr`** (a publish appends nothing). -/
def PubFrontierF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ l f cl, (CE η).pfr l = none → E'.pfr l = some f → E'.sto l = some cl → r.2.2.vs.vWr ≤ f

/-- (B3) **`PlantFrozen` at every thread step**: the stepper leaves
the count of each of its shared cells unchanged. -/
def PlantFrozenF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    PlantFrozen i Eg (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E')

/-- (T1, the `hsc` of `stepper_newPos`) **The stepping term is in scope**, frame-only
terms (`StepScopeR`) included, at every `EnvAt` of the stepper (`Obligations.scope`,
`TermScope.scope_of`). -/
def StepScopeF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    StepScope cx th.term ∨ StepScopeR th.σs cx th.term


/-- **`RiniFootF` holds** (EFoot's `rini` locality). -/
theorem riniFoot_holds : RiniFootF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z l
  exact Z.1.rinieq l

/-- **`PubFrontierF` holds** (EFoot's publish/plant disjunct). -/
theorem pubFrontier_holds : PubFrontierF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z l f cl h0 hf hs
  rcases Z.1.2.2.2.2.2.1 l with e | ⟨-, F', e, -, -, -, hv, -⟩ | ⟨-, -, e⟩
  · rw [e, h0] at hf; cases hf
  · rw [e] at hf; cases hf; exact hv
  · rw [e] at hs; cases hs

theorem HiddenP_bound {η : TEnv} {T : Ty} {mem : Memory} {P : List Ts} {l : AllocLabel} {o : Nat} {V V' : Ts}
    (hV : V ≤ V') (h : HiddenP η T mem P l o V) : HiddenP η T mem P l o V' := fun t m h1 h2 h3 h4 =>
  let ⟨t', m', a1, a2, a3, a4⟩ := h t m h1 h2 h3 h4
  ⟨t', m', a1, Nat.le_trans a2 hV, a3, a4⟩

/-- `HiddenP` moved to another skip set and typing, where the messages skipped
only by the first are typed in the second. -/
theorem HiddenP_conv {η₁ η₂ : TEnv} {T : Ty} {mem : Memory} {P₁ P₂ : List Ts} {l : AllocLabel} {o : Nat} {V : Ts}
    (hP : ∀ (t : Ts) (m : Msg), t ∈ P₁ → mem[t]? = some m → m.loc = ⟨l, o⟩ → WordOK η₂ T o (mw m))
    (hmono : ∀ w, WordOK η₁ T o w → WordOK η₂ T o w)
    (h : HiddenP η₁ T mem P₁ l o V) : HiddenP η₂ T mem P₂ l o V := by
  intro t m _ hm hl hw
  by_cases ht : t ∈ P₁
  · exact absurd (hP t m ht hm hl) hw
  · exact h t m ht hm hl (fun h' => hw (hmono _ h'))

/-- (B2, any shared cell not of the stepper) A new message at an initialised
offset is typed in every idle cut. -/
theorem tctx_newOK_other {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    (j : Nat) (Sj : AllocLabel → Prop) {l : AllocLabel} {cl : Cell} {o : Nat} {f : Ts}
    (hc : Eg.sto l = some cl) (hoi : cl.owner ≠ some i) (hpf : Eg.pfr l = some f)
    (hI : InitR (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o)
    {t : Nat} {m : Msg} (ht : c.mem.size ≤ t) (hm : c'.mem[t]? = some m) (hl : m.loc = ⟨l, o⟩) :
    WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m) := by
  obtain ⟨hs2, hp2, -⟩ := tctx_other_cell X Y Z hc hoi
  rw [hpf] at hp2
  obtain ⟨hs', hf', hT⟩ := tctx_shared X Y Z hs2 hp2
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hnp : t ∉ r.2.2.promises :=
    tstep_newNotProm (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr ht
  have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
  have hw := newMsg_wordOK_other Z.2.2.1 hs' (by rw [htid]; exact hoi) hf' (X.inv.frle l cl f hc hpf) hI ht hnp
    (by rw [← X.e1]; exact hm) hl
  exact WordOK_transferS (tctx_inclS X Y Z j Sj) hT hw

/-- (B2, the stepper's own cell, SysInvN form of `SysInvW.newOwn_wordOK_init_sc`)
A new message at an initialised offset of a cell of the stepper is typed at `E'`. -/
theorem tctx_newOwn {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ)
    {l : AllocLabel} {cl : Cell} {o : Nat} (hc : Eg.sto l = some cl) (hoi : cl.owner = some i)
    (hI : InitR E' cl l o) {t : Nat} {m : Msg} (ht : c.mem.size ≤ t) (hm : c'.mem[t]? = some m)
    (hl : m.loc = ⟨l, o⟩) : WordOK E' cl.ty o (mw m) := by
  obtain ⟨S0, hRE0, -, hm0, -⟩ := X.inv.thr i th X.hth
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
    rw [(hfr l hF).1] at hc; cases hc
  have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
    rw [← Y.1]; exact Z.1
  have hsto' : E'.sto l = some cl := by
    rcases hF0.2.2.1 l with e | ⟨hF, -⟩
    · rw [e]; exact cutSto_own hc hoi
    · exact absurd hF hnF
  have htid : E'.tid = i := hF0.2.1
  have hmt : r.1[t]? = some m := by rw [← X.e1]; exact hm
  have hnp : t ∉ (stOf r.1 r.2.1 r.2.2).promises :=
    tstep_newNotProm (MemInv_promLt hm0) (MemInv_nopair hm0) X.hr ht
  have hwc : ∀ n, wc cl.ty = some n → o < n := by
    -- the scope at the stepper's own `ThInvRE` typing (cut `S0`): a frame-only
    -- term (`StepScopeR`) keeps memory, so appends nothing
    obtain ⟨ρ2, η2, cx2, Rf2, Rs2, hce2, hEO2, hTy2, hTv2, hF2, hRt2, -⟩ := hRE0
    have Y2 : EnvAt p Eg i th (Tot i) S0 ρ2 η2 cx2 Rf2 Rs2 :=
      ⟨hce2, congrArg TEnv.tid hce2, hEO2, hTy2, hTv2, hF2, hRt2⟩
    have hm2 : MemInv (gOf p k arch c i) (CE η2) (stOf c.mem c.pairs th) := by rw [hce2]; exact hm0
    have hs : StepScope cx2 th.term := by
      rcases hsc X Y2 with hs | hR
      · exact hs
      · have hk : r.1 = c.mem := (frame_keep hR hTy2.1 hTy2.2 hF2 hEO2 hTv2 hm2 r X.hr).1
        rw [hk, Array.getElem?_eq_none ht] at hmt; cases hmt
    have hFi : FInv ρ2 η2 th.σs (Resume p th.stack) cx2 th.env :=
      FInvR_FInv (hTv2.2.2.2.2.2.2.2)
        (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th.stack Rs2 E rd ws R h) hF2
    rcases tstep_newPos hEO2 hTy2.1 hTv2 hFi hm2 hs X.hr t m ht hmt with hF | hN0
    · rw [hl] at hF; exact absurd hF hnF
    · have hN : NewPos (Cut Eg (gOf p k arch c i).i S0) m.loc := by rw [← hce2]; exact hN0
      obtain ⟨cl', hsto2, hwc', -⟩ := newPos_b5 hN
      have e2 : (Cut Eg (gOf p k arch c i).i S0).sto m.loc.label = some cl := by rw [hl]; exact cutSto_own hc hoi
      rw [e2] at hsto2; cases hsto2
      intro n hn; have := hwc' n hn; rw [hl] at this; exact this
  have hft : ∀ f, E'.pfr l = some f → f ≤ t := fun f hpf' => by
    rcases hF0.2.2.2.2.2.1 l with e | ⟨-, F', e, -, hF2, -⟩ | ⟨hF, -, -⟩
    · rw [e] at hpf'
      exact Nat.le_trans (X.inv.frle l cl f hc hpf') ht
    · rw [e] at hpf'
      obtain rfl := Option.some.inj hpf'
      exact Nat.le_trans hF2 (Nat.le_trans (Nat.max_le.2 ⟨X.inv.vwr i th X.hth, Nat.le_refl _⟩) ht)
    · exact absurd hF hnF
  exact newMsg_wordOK_ownInit Z.2.2.1 hsto' (by rw [htid]; exact hoi) hI hwc ht hnp hmt hl
    (fun t' m' ht' hm'' hl' => tstep_once hm0.2.2.1 X.hr t' t m' m ht' ht hm'' hmt (hl'.trans hl.symm)
      (by rw [hl']; exact hnF)) hft

/-- Clause 7 (`PubDefP`), given `PlantFrozenF`, `StepScopeF`, `PubFrontierF`, `PromTyAPostF`. -/
theorem cl7_pubDefP (hpf : PlantFrozenF p k arch Sp Init MintOK c0) (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (hfr' : PubFrontierF p k arch Sp Init MintOK c0) (hpa : PromTyAPostF p k arch Sp Init MintOK c0) :
    MemClTP p k arch Sp Init MintOK c0 fun _ E s => PubDefP E s.mem s.promises := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS j thj Sj hji hj hold l cl f hc ho hf o hio
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hgf := gfoot_of X Y ZC
  have hfrE := X.inv.gfresh X.hth r.2.2.nalloc
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hs2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hc
  have hf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
  obtain ⟨hs', hf', hT⟩ := tctx_shared X Y ZC hs2 hf2
  have hIS := tctx_inclS X Y ZC j Sj
  have htid : E'.tid = i := by rw [← tctx_cut X Y ZC]; rfl
  cases ep : Eg.pfr l with
  | some f0 =>
    have hff : f0 = f := Option.some.inj ((hgf.le.pfr l f0 ep).symm.trans hf2)
    subst hff
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
      rw [(hfrE l hF).2.2] at ep; cases ep
    have hc1 : Eg.sto l = some cl := by rw [← hgf.sto_old hnF]; exact hs2
    have hc0 : cutSto Eg j l = some cl := cutSto_shared hc1 ⟨f0, ep⟩
    have hini : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l :=
      gfoot_ini_shared hgf hfrE (hpf X Y ZC) ⟨f0, ep⟩
    have hio0 : InitR (Cut Eg j Sj) cl l o := fun N e us hT' hu => by
      have := hio N e us hT' hu; rw [Cut_ini, hini] at this; exact this
    have hH := hold.2.2.1.2.2.2.2.2.2.1 l cl f0 hc0 ho ep o hio0
    refine HiddenP_move (tctx_pre X) (fun t m h1 h2 h3 => ?_)
      (fun w h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini) hH
    by_cases hoi : cl.owner = some i
    · have hio' : InitR E' cl l o := fun N e us hT' hu => by
        have := hio N e us hT' hu; rw [Cut_ini] at this; exact this
      exact WordOK_transferS hIS hT (tctx_newOwn hsc X Y ZC hc1 hoi hio' h1 h2 h3)
    · exact tctx_newOK_other X Y ZC j Sj hc1 hoi ep hio h1 h2 h3
  | none =>
    -- a cell newly shared by the step: the stepper's own, hidden by its `OwnHidP`
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
      intro hF
      have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
        rw [← Y.1]; exact ZC.1
      rcases hF0.2.2.2.2.2.1 l with e | ⟨-, -, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hs0⟩
      · rw [e] at hf'; exact absurd (hf'.symm.trans ep) (by simp)
      · have h2 : Eg.sto l = some c1 := cutSto_sub hc1
        rw [(hfrE l hF).1] at h2; cases h2
      · rw [hs0] at hs'; cases hs'
    have hc1 : Eg.sto l = some cl := by rw [← hgf.sto_old hnF]; exact hs2
    have hoi : cl.owner = some i := by
      rcases hgf.2.2.2.2.1 l with e | ⟨-, -, -, -, c1, hc1', ho1⟩ | ⟨hF, -⟩
      · have h3 : (Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').pfr l = some f := hf2
        rw [e, ep] at h3; cases h3
      · rw [hc1] at hc1'; cases hc1'; exact ho1
      · exact absurd hF hnF
    have hown : cl.owner = some E'.tid := by rw [htid]; exact hoi
    have hPi : ∀ (t : Ts) (m : Msg), t ∈ r.2.2.promises → r.1[t]? = some m → m.loc = ⟨l, o⟩ →
        WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m) := by
      intro t m ht hm hl
      have hl' : m.loc.label = l := by rw [hl]
      have := hpa X Y Z hPub hPfrP hS i r.2.2 t m X.e3 ht (by rw [X.e1]; exact hm) cl (by rw [hl']; exact hs2)
        ⟨f, by rw [hl']; exact hf2⟩
      rw [hl] at this
      exact WordOK_transferS (InclS_pub_cut _ j Sj) hT this
    have hmono : ∀ w, WordOK E' cl.ty o w →
        WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o w :=
      fun w h => WordOK_transferS hIS hT h
    have hio' : InitR E' cl l o := fun N e us hT' hu => by
      have := hio N e us hT' hu; rw [Cut_ini] at this; exact this
    have hmem : (stOf c'.mem c'.pairs thj).mem = r.1 := X.e1
    rw [hmem]
    by_cases hrc : E'.rc l < E'.ini l
    · obtain ⟨f1, hf1, -, hH⟩ := ZC.2.2.1.2.2.2.2.2.1.2 l cl hs' hown hrc
      rw [hf'] at hf1; cases hf1
      exact HiddenP_conv hPi hmono (hH o hio')
    · have hrr : InitRr E' cl l o := fun N e us hT' hu => by
        have := hio' N e us hT' hu
        unfold TEnv.rc
        have : E'.ini l ≤ E'.rini l := by unfold TEnv.rc at hrc; omega
        rw [Nat.min_eq_left this]; assumption
      have hH := ZC.2.2.1.2.2.2.2.2.1.1 l cl hs' hown o hrr
      have hle : r.2.2.vs.vWr ≤ f := hfr' X Y ZC l f cl (by rw [Y.1]; exact ep) hf' hs'
      exact HiddenP_conv hPi hmono (HiddenP_bound hle hH)


/-! ### Clause 9d (`PubPair`) -/

/-- (B4 PromTyOK (c) in `TwoAtT` form, at the new configuration)
**No outstanding promise at a shared cell lies in a two-word unit.** -/
def PromNoTwoPostF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ (k' : Nat) (thk : TTh) (t : Ts) (m : Msg), c'.ths[k']? = some thk → t ∈ thk.promises → c'.mem[t]? = some m →
      ∀ cl, (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = some cl →
        (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').Shared m.loc.label →
        ∀ o, TwoAtT cl.ty o → m.loc.offset ≠ o ∧ m.loc.offset ≠ o + 1

/-- (S8c open) **`PubPair` of an idle thread at the stepper's own
shared cells** (the part of clause 9d not reducible to the stepper's
`PubPair`: it needs the stepper's `OwnPairF` and B5). -/
def PairStepperF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ThSysAt p (gOf p k arch c i) c.mem c.pairs th Eg (Tot i) (HP i) HS (cr i) (db i) S →
    PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E' →
    ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c.ths[j]? = some thj →
      ThSysAt p (gOf p k arch c j) c.mem c.pairs thj Eg (Tot j) (HP j) HS (cr j) (db j) Sj →
      ∀ l cl f o, cl.owner = some i →
        (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl →
        (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f →
        TwoAtT cl.ty o →
        (∃ b S us o', SegOf cl.ty b S ∧ accs S = some us ∧ TwoAt us o' ∧ o = b + o' ∧
          IniSegN ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l) cl b) →
        ∀ (t0 t1 : Nat) (m0 m1 : Msg), t0 ∉ thj.promises → t1 ∉ thj.promises →
        c'.mem[t0]? = some m0 → c'.mem[t1]? = some m1 → m0.loc = ⟨l, o⟩ → m1.loc = ⟨l, o + 1⟩ →
        WeakMem.hiddenFrom c'.mem ⟨l, o⟩ t0 f = false → WeakMem.hiddenFrom c'.mem ⟨l, o + 1⟩ t1 f = false →
        WeakMem.pairStraddles c'.mem c'.pairs ⟨l, o⟩ t0 t1 = false →
        PairOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m0) (mw m1)

/-- Clause 9d (`PubPair`), given `PromNoTwoPostF` and `PairStepperF`. -/
theorem cl9d_pubPair (hnt : PromNoTwoPostF p k arch Sp Init MintOK c0) (hst : PairStepperF p k arch Sp Init MintOK c0) :
    MemClTH p k arch Sp Init MintOK c0 fun _ E s => PubPair E s.mem s.pairs s.promises := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr j thj Sj hji hj hold
    l cl f o hc hg hf hTw t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hh0 hh1 hps
  have hgd : ∃ b S us o', SegOf cl.ty b S ∧ accs S = some us ∧ TwoAt us o' ∧ o = b + o' ∧
      IniSegN ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l) cl b := by
    rcases hg with ⟨-, b, S1, us, o', h2, h3, h4, h5, h7⟩ | ⟨-, b, S1, us, o', h2, h3, h4, h5, -, h7⟩
    · exact ⟨b, S1, us, o', h2, h3, h4, h5, h7⟩
    · exact ⟨b, S1, us, o', h2, h3, h4, h5, h7⟩
  by_cases hoi : cl.owner = some i
  · exact hst X Y Z hS hPfr j thj Sj hji hj hold l cl f o hoi hc hf hTw hgd t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hh0 hh1 hps
  · have hs2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hc
    have hf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
    obtain ⟨hs', hf', hT⟩ := tctx_shared X Y Z hs2 hf2
    have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
    have hj' : c'.ths[i]? = some r.2.2 := X.e3
    have hnp : ∀ t m, c'.mem[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) → t ∉ r.2.2.promises :=
      fun t m hm hl ht => by
        have hl' : m.loc.label = l := by rcases hl with e | e <;> rw [e]
        have := hnt X Y Z hS hPfr i r.2.2 t m hj' ht hm cl (by rw [hl']; exact hs2) ⟨f, by rw [hl']; exact hf2⟩ o hTw
        rcases hl with e | e
        · exact this.1 (by rw [e])
        · exact this.2 (by rw [e])
    obtain ⟨b, S1, us, o', h2, h3, h4, h5, h7⟩ := hgd
    have hpp := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl f o hs'
      (.inl ⟨by rw [htid]; exact hoi, b, S1, us, o', h2, h3, h4, h5, h7⟩) hf' hTw t0 t1 m0 m1
      (hnp t0 m0 h0 (.inl hl0)) (hnp t1 m1 h1 (.inr hl1)) (by rw [← X.e1]; exact h0) (by rw [← X.e1]; exact h1)
      hl0 hl1 (by rw [← X.e1]; exact hh0) (by rw [← X.e1]; exact hh1) (by rw [← X.e1, ← X.e2]; exact hps)
    exact PairOK_transferS (tctx_inclS X Y Z j Sj) hT hpp


theorem CellOK_mono {η₁ η₂ : TEnv} (hp : η₁.prog = η₂.prog) (ht : η₁.tid = η₂.tid) (hI : Incl η₁ η₂)
    (hS : ∀ l, η₁.seen l → η₂.seen l)
    {n : Nat} {T : Ty} {vals : List Word} (h : CellOK η₁ n T vals) : CellOK η₂ n T vals := by
  rcases h with ⟨h1, h2⟩ | ⟨N, e, us, hT, hu, hn, hl, hj⟩
  · exact Or.inl ⟨h1, ValOf_mono hp ht hI.sto hI.ini h2 hI.pfr hS hI.box hI.rini⟩
  · exact Or.inr ⟨N, e, us, hT, hu, hn, hl,
      fun j hjn => ValOf_mono hp ht hI.sto hI.ini (hj j hjn) hI.pfr hS hI.box hI.rini⟩

/-! ### Clause 2 (`OwnOKPF`) -/

/-- A recorded pair whose words lie on either side of `(t0, t1)` straddles them. -/
theorem straddle_true {mem : Memory} {pairs : List Ts} {a : Address} {t0 t1 p : Ts} {m0 m1 : Msg}
    (hp : p ∈ pairs) (h0 : mem[p]? = some m0) (hl0 : m0.loc = a) (h1 : mem[p + 1]? = some m1)
    (hl1 : m1.loc = a.next) (hne : (p ≤ t0) ≠ (p + 1 ≤ t1)) : WeakMem.pairStraddles mem pairs a t0 t1 = true := by
  unfold WeakMem.pairStraddles
  rw [List.any_eq_true]
  refine ⟨p, hp, ?_⟩
  rw [h0, h1]
  simp only [Option.elim, hl0, hl1, decide_true, Bool.true_and]
  by_cases ha : p ≤ t0 <;> by_cases hb : p + 1 ≤ t1 <;> simp_all

/-- (B2 at every offset, B5) **A new message the step appends at a cell
of another thread is a typed word at the step's witness** (B2 gives it at
initialised offsets; elsewhere: no foreign write at an uninitialised slot, no
`undef` — `SW_nundef`). -/
def NewForeignTypedF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ (t : Nat) (m : Msg) (l : AllocLabel) (o : Nat) (cl : Cell), c.mem.size ≤ t → c'.mem[t]? = some m →
      m.loc = ⟨l, o⟩ → Eg.sto l = some cl → cl.owner ≠ some i → WordOK E' cl.ty o (mw m)

/-- (B5) **New messages in a two-word unit of another thread's cell come
as recorded pairs**: the first word's index is a new pair entry, followed by the
second word. -/
def NewPairF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ (t : Nat) (m : Msg) (l : AllocLabel) (o : Nat) (cl : Cell), c.mem.size ≤ t → c'.mem[t]? = some m →
      Eg.sto l = some cl → TwoAtT cl.ty o →
      (m.loc = ⟨l, o⟩ → t ∈ c'.pairs ∧ ∃ m1, c'.mem[t + 1]? = some m1 ∧ m1.loc = ⟨l, o + 1⟩) ∧
      (m.loc = ⟨l, o + 1⟩ → ∃ q, t = q + 1 ∧ c.mem.size ≤ q ∧ q ∈ c'.pairs ∧
        ∃ m0, c'.mem[q]? = some m0 ∧ m0.loc = ⟨l, o⟩)

/-- Clause 2 (`OwnOKPF`), given `RiniFootF`, `NewForeignTypedF`, `NewPairF`. -/
theorem cl2_ownOKPF (hri : RiniFootF p k arch Sp Init MintOK c0) (hnf : NewForeignTypedF p k arch Sp Init MintOK c0)
    (hnp : NewPairF p k arch Sp Init MintOK c0) :
    MemClT p k arch Sp Init MintOK c0 fun _ E s => OwnOKPF E s.mem s.pairs s.vs s.promises := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l cl hc ho
  have hgf := gfoot_of X Y Z
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have tmono : ∀ T o ww, WordOK (Cut Eg j Sj) T o ww →
      WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) T o ww :=
    fun T o ww h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini
  have ho' : cl.owner = some j := ho
  obtain ⟨hc1, hc0⟩ := tctx_jcut X Y Z hji hc ho'
  have hoi : cl.owner ≠ some i := by rw [ho']; intro h; exact hji (Option.some.inj h)
  obtain ⟨hs2, hp2, hini⟩ := tctx_other_cell X Y Z hc1 hoi
  have hrini := tctx_other_rini hri X Y Z hc1 hoi
  have hpf : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = Eg.pfr l := hp2
  have hrc : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l = (Cut Eg j Sj).rc l := by
    unfold TEnv.rc; rw [Cut_ini, Cut_rini, Cut_ini, Cut_rini, hini, hrini]
  obtain ⟨vals, hcv, hl, hpr⟩ := hold.2.2.1.2.1 l cl hc0 ho'
  -- a new message at `l`: `l` is shared and the message typed
  have hnew : ∀ (t : Nat) (m : Msg) (o : Nat), c.mem.size ≤ t → c'.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      Eg.pfr l ≠ none ∧
        WordOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m) := by
    intro t m o ht hm hlm
    have hsh : Eg.pfr l ≠ none := fun hp0 =>
      tctx_noNewPriv X hji (S := Sj) ⟨⟨cl, hc0, ho'⟩, hp0⟩ t m ht hm (by rw [hlm])
    obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hsh
    rw [hf] at hp2
    obtain ⟨-, -, hT⟩ := tctx_shared X Y Z hs2 hp2
    exact ⟨hsh, WordOK_transferS (tctx_inclS X Y Z j Sj) hT (hnf X Y Z t m l o cl ht hm hlm hc1 hoi)⟩
  have hcv' : CellOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      ((Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l) cl.ty vals := by
    rw [hrc]; exact CellOK_mono hI.prog rfl hI (fun _ h => h) hcv
  refine ⟨vals, hcv', fun o vv hv => ?_, fun hne => ?_⟩
  · obtain ⟨⟨m, hm, hma, hor⟩, hS, hlast⟩ := hl o vv hv
    refine ⟨⟨m, ?_, hma, hor.imp id fun ⟨h1, h2⟩ => ⟨by rw [hpf]; exact h1, tmono _ _ _ h2⟩⟩, hS,
      fun t m' ht hm' hl' => ?_⟩
    · have hm2 : c.mem[thj.vs.coh ⟨l, o⟩]? = some m := hm
      show c'.mem[thj.vs.coh ⟨l, o⟩]? = some m
      rw [tctx_pre X _ (lt_of_get hm2)]; exact hm2
    · have hm2 : c'.mem[t]? = some m' := hm'
      rcases Nat.lt_or_ge t c.mem.size with h1 | h1
      · rw [tctx_pre X t h1] at hm2
        rcases hlast t m' ht hm2 hl' with h | ⟨h3, h4⟩
        · exact .inl h
        · exact .inr ⟨by rw [hpf]; exact h3, tmono _ _ _ h4⟩
      · obtain ⟨hsh, hw⟩ := hnew t m' o h1 hm2 hl'
        exact .inr ⟨by rw [hpf]; exact hsh, by unfold TypedAt; rw [hl']; exact hw⟩
  · have hne0 : Eg.pfr l ≠ none := by rw [← hpf]; exact hne
    intro o hTw hrr t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hco0 hco1 hps
    have h0' : c'.mem[t0]? = some m0 := h0
    have h1' : c'.mem[t1]? = some m1 := h1
    have hps' : WeakMem.pairStraddles c'.mem c'.pairs ⟨l, o⟩ t0 t1 = false := hps
    have hpairs : ∀ q, q ∈ c.pairs → q + 1 < c.mem.size := hold.2.2.1.1.2.2
    have hpup : PairsUp c.pairs c'.pairs := by rw [X.e2]; exact tstep_pairsUp X.hr
    obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
    have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun hF => by
      rw [((X.inv.gfresh X.hth r.2.2.nalloc) l hF).1] at hc1; cases hc1
    have honce : ∀ (u1 u2 : Nat) (n1 n2 : Msg), c.mem.size ≤ u1 → c.mem.size ≤ u2 → c'.mem[u1]? = some n1 →
        c'.mem[u2]? = some n2 → n1.loc = n2.loc → n1.loc.label = l → u1 = u2 := fun u1 u2 n1 n2 a1 a2 a3 a4 a5 a6 =>
      tstep_once hm0.2.2.1 X.hr u1 u2 n1 n2 a1 a2 (by rw [← X.e1]; exact a3) (by rw [← X.e1]; exact a4) a5
        (by rw [a6]; exact hnF)
    have hnext : (⟨l, o⟩ : Address).next = ⟨l, o + 1⟩ := rfl
    rcases Nat.lt_or_ge t0 c.mem.size with a0 | a0 <;> rcases Nat.lt_or_ge t1 c.mem.size with a1 | a1
    · -- both old
      have h0o : c.mem[t0]? = some m0 := by rw [← tctx_pre X t0 a0]; exact h0'
      have h1o : c.mem[t1]? = some m1 := by rw [← tctx_pre X t1 a1]; exact h1'
      exact (hpr hne0 o hTw (fun N e us hT' hu => by have := hrr N e us hT' hu; rw [hrc] at this; exact this) t0 t1 m0 m1 hs0 hs1 h0o h1o hl0 hl1 hco0 hco1
        (pairStraddles_back (tctx_pre X) hpup hpairs hps')).imp id (fun h => PairOK_mono hI.prog rfl hI.sto hI.ini
          hI.pfr (fun _ h => h) h hI.box hI.rini)
    · -- t1 new, t0 old: t1 is the second word of a new pair, which straddles
      obtain ⟨q, rfl, hq, hqp, m0', hm0', hl0'⟩ := (hnp X Y Z t1 m1 l o cl a1 h1' hc1 hTw).2 hl1
      exact absurd (straddle_true hqp hm0' hl0' h1' (by rw [hl1]; rfl)
        (fun e => absurd (e.mpr (Nat.le_refl _)) (Nat.not_le.2 (Nat.lt_of_lt_of_le a0 hq)))) (by rw [hps']; simp)
    · -- t0 new
      obtain ⟨hqp, m1', hm1', hl1'⟩ := (hnp X Y Z t0 m0 l o cl a0 h0' hc1 hTw).1 hl0
      exact absurd (straddle_true hqp h0' hl0 hm1' (by rw [hl1']; rfl)
        (fun e => absurd (e.mp (Nat.le_refl _))
          (Nat.not_le.2 (Nat.lt_of_lt_of_le a1 (Nat.le_trans a0 (Nat.le_succ _)))))) (by rw [hps']; simp)
    · -- both new: the recorded pair
      obtain ⟨hqp, m1', hm1', hl1'⟩ := (hnp X Y Z t0 m0 l o cl a0 h0' hc1 hTw).1 hl0
      have e1 : t1 = t0 + 1 := by
        have := honce t1 (t0 + 1) m1 m1' a1 (by omega) h1' hm1' (by rw [hl1, hl1']) (by rw [hl1])
        exact this
      subst e1
      have hm1e : m1' = m1 := by rw [hm1'] at h1'; cases h1'; rfl
      subst hm1e
      have hs2' : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none := by rw [hp2]; exact hne0
      obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hs2'
      obtain ⟨hs', -, hT⟩ := tctx_shared X Y Z hs2 hf
      have hq' : t0 ∈ r.2.1 := by rw [← X.e2]; exact hqp
      have hpo := Z.2.2.1.1.2.1 t0 m0 m1' cl hq' (by rw [← X.e1]; exact h0') (by rw [← X.e1]; exact hm1')
        (by rw [hl0]; exact hs')
      rw [hl0] at hpo
      exact .inr (PairOK_transferS (tctx_inclS X Y Z j Sj) hT hpo)


/-- `hiddenFrom` only grows with memory. -/
theorem hiddenFrom_grow {mem mem' : Memory} (hpre : ∀ (t : Nat) (m : Msg), mem[t]? = some m → mem'[t]? = some m)
    {a : Address} {t b : Ts} (h : WeakMem.hiddenFrom mem' a t b = false) : WeakMem.hiddenFrom mem a t b = false := by
  unfold WeakMem.hiddenFrom at h ⊢
  rw [Bool.eq_false_iff] at h ⊢
  intro h1
  apply h
  rw [List.any_eq_true] at h1 ⊢
  obtain ⟨x, hx, hp⟩ := h1
  refine ⟨x, hx, ?_⟩
  cases e : mem[x]? with
  | none => rw [e] at hp; simp at hp
  | some m => rw [e] at hp; rw [hpre x m e]; exact hp

/-! ### N15 `pairStepper` from `newPair`, `ownCohLe`, `pubInit` -/

theorem hiddenFrom_true {mem : Memory} {a : Address} {t b t' : Ts} {m : Msg} (h1 : t < t') (h2 : t' ≤ b)
    (hm : mem[t']? = some m) (hl : m.loc = a) : WeakMem.hiddenFrom mem a t b = true := by
  unfold WeakMem.hiddenFrom
  rw [List.any_eq_true]
  exact ⟨t', List.mem_range.2 (Nat.lt_succ_of_le h2), by simp [h1, hm, hl]⟩

/-- The two words of a two-word unit of an initialised segment of a cell's
words are a pair of the cell's type. -/
theorem cellOK_pairOK {η : TEnv} {n : Nat} {T S : Ty} {vals : List Word} {b o' : Nat} {us : List Acc}
    {w0 w1 : Word} (hc : CellOK η n T vals) (hseg : SegOf T b S) (hu : accs S = some us) (hj : TwoAt us o')
    (hi : IniSegN n ⟨T, none⟩ b)
    (h0 : ∀ v, vals[b + o']? = some v → WLe1 v w0) (h1 : ∀ v, vals[b + o' + 1]? = some v → WLe1 v w1) :
    PairOK η T (b + o') w0 w1 := by
  obtain ⟨hv, hlen⟩ := CellOK_seg hc hseg hu hi
  have hl2 := TwoAt_lt hj
  have g0 : ((vals.drop b).take (nWords us))[o']? = vals[b + o']? := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
  have g1 : ((vals.drop b).take (nWords us))[o' + 1]? = vals[b + o' + 1]? := by
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop, Nat.add_assoc]
  obtain ⟨v0, e0⟩ : ∃ v, vals[b + o']? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨v1, e1⟩ : ∃ v, vals[b + o' + 1]? = some v := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  exact ⟨b, S, _, o', v0, v1, hseg, hv, by rw [g0, e0], by rw [g1, e1], h0 v0 e0, h1 v1 e1, rfl⟩

/-- **At a cell the step newly shares, the stepper's coherence is at
most its new `vWr`** (a formerly private cell holds only the stepper's own
writes and allocation), at the offsets inside the cell (`TermCohLe.ownCohLe_of`). -/
def OwnCohLeF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS) (cr i) (db i) δ →
    ∀ l, (CE η).pfr l = none → E'.pfr l ≠ none → ∀ cl vals, E'.sto l = some cl →
      CellOK E' (E'.rc l) cl.ty vals → ∀ o, o < vals.length → r.2.2.vs.coh ⟨l, o⟩ ≤ r.2.2.vs.vWr

/-- **N15 `pairStepper`**, given `NewPairF`, `OwnCohLeF`, `PlantFrozenF`, `PromNoTwoPostF`. -/
theorem pairStepper_holds (hnp : NewPairF p k arch Sp Init MintOK c0) (hco : OwnCohLeF p k arch Sp Init MintOK c0)
    (hpf : PlantFrozenF p k arch Sp Init MintOK c0) (hnt : PromNoTwoPostF p k arch Sp Init MintOK c0) :
    PairStepperF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hS hPfr j thj Sj hji hj hold
    l cl f o hoi hc hf hTw hgd t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hh0 hh1 hps
  have hgf := gfoot_of X Y Z
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hs2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto l = some cl := cutSto_sub hc
  have hf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l = some f := hf
  obtain ⟨hs', hf', hT⟩ := tctx_shared X Y Z hs2 hf2
  have htid : E'.tid = i := by rw [← tctx_cut X Y Z]; rfl
  have hfrE := X.inv.gfresh X.hth r.2.2.nalloc
  have hnF : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := by
    intro hF
    have hF0 : EFoot (gOf p k arch c i) (Cut Eg i S) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) := by
      rw [← Y.1]; exact Z.1
    rcases hF0.2.2.2.2.2.1 l with e | ⟨-, -, -, -, -, ⟨c1, hc1, -⟩, -⟩ | ⟨-, -, hs0⟩
    · have h4 : Eg.pfr l = none := (hfrE l hF).2.2
      rw [e] at hf'; exact absurd (hf'.symm.trans h4) (by simp)
    · have h2 : Eg.sto l = some c1 := cutSto_sub hc1
      rw [(hfrE l hF).1] at h2; cases h2
    · rw [hs0] at hs'; cases hs'
  have hc1 : Eg.sto l = some cl := by rw [← hgf.sto_old hnF]; exact hs2
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr i th X.hth
  have honce : ∀ (u1 u2 : Nat) (n1 n2 : Msg), c.mem.size ≤ u1 → c.mem.size ≤ u2 → c'.mem[u1]? = some n1 →
      c'.mem[u2]? = some n2 → n1.loc = n2.loc → n1.loc.label = l → u1 = u2 := fun u1 u2 n1 n2 a1 a2 a3 a4 a5 a6 =>
    tstep_once hm0.2.2.1 X.hr u1 u2 n1 n2 a1 a2 (by rw [← X.e1]; exact a3) (by rw [← X.e1]; exact a4) a5
      (by rw [a6]; exact hnF)
  have hnP : ∀ t m, c'.mem[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) → t ∉ r.2.2.promises :=
    fun t m hm hl ht => by
      have hl' : m.loc.label = l := by rcases hl with e | e <;> rw [e]
      have := hnt X Y Z hS hPfr i r.2.2 t m X.e3 ht hm cl (by rw [hl']; exact hs2) ⟨f, by rw [hl']; exact hf2⟩ o hTw
      rcases hl with e | e
      · exact this.1 (by rw [e])
      · exact this.2 (by rw [e])
  have hIS := tctx_inclS X Y Z j Sj
  -- the pair written by the step at `(t0, t0+1)`, typed by the stepper's MemOKP
  have hnewpair : ∀ m1' : Msg, t0 ∈ c'.pairs → c'.mem[t0 + 1]? = some m1' →
      PairOK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl.ty o (mw m0) (mw m1') := by
    intro m1' hq hm1'
    have hq' : t0 ∈ r.2.1 := by rw [← X.e2]; exact hq
    have hpo := Z.2.2.1.1.2.1 t0 m0 m1' cl hq' (by rw [← X.e1]; exact h0) (by rw [← X.e1]; exact hm1')
      (by rw [hl0]; exact hs')
    rw [hl0] at hpo
    exact PairOK_transferS hIS hT hpo
  cases ep : Eg.pfr l with
  | some f0 =>
    have hff : f0 = f := Option.some.inj ((hgf.le.pfr l f0 ep).symm.trans hf2)
    subst hff
    have hc0 : cutSto Eg j l = some cl := cutSto_shared hc1 ⟨f0, ep⟩
    have hpre : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → c'.mem[t]? = some m :=
      fun t m h => by rw [tctx_pre X t (lt_of_get h)]; exact h
    have hpairs : ∀ q, q ∈ c.pairs → q + 1 < c.mem.size := hold.2.2.1.1.2.2
    have hpup : PairsUp c.pairs c'.pairs := by rw [X.e2]; exact tstep_pairsUp X.hr
    rcases Nat.lt_or_ge t0 c.mem.size with a0 | a0 <;> rcases Nat.lt_or_ge t1 c.mem.size with a1 | a1
    · have h0o : c.mem[t0]? = some m0 := by rw [← tctx_pre X t0 a0]; exact h0
      have h1o : c.mem[t1]? = some m1 := by rw [← tctx_pre X t1 a1]; exact h1
      exact PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h)
        (hold.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl f0 o hc0
          (.inl ⟨by rw [hoi]; intro e; exact hji (Option.some.inj e).symm, hgd.imp fun b ⟨S1, us, o', h2, h3, h4, h5, h7⟩ =>
            ⟨S1, us, o', h2, h3, h4, h5, by
              have hini : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l = Eg.ini l :=
                gfoot_ini_shared hgf hfrE (hpf X Y Z) ⟨f0, ep⟩
              have h7' : IniSegN ((EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').ini l) cl b := h7
              rw [hini] at h7'; exact h7'⟩⟩)
          ep hTw t0 t1 m0 m1 hs0 hs1 h0o h1o hl0 hl1 (hiddenFrom_grow hpre hh0) (hiddenFrom_grow hpre hh1)
          (pairStraddles_back (tctx_pre X) hpup hpairs hps)) hI.box hI.rini
    · obtain ⟨q, rfl, hq, hqp, m0', hm0', hl0'⟩ := (hnp X Y Z t1 m1 l o cl a1 h1 hc1 hTw).2 hl1
      exact absurd (straddle_true hqp hm0' hl0' h1 (by rw [hl1]; rfl)
        (fun e => absurd (e.mpr (Nat.le_refl _)) (Nat.not_le.2 (Nat.lt_of_lt_of_le a0 hq)))) (by rw [hps]; simp)
    · obtain ⟨hqp, m1', hm1', hl1'⟩ := (hnp X Y Z t0 m0 l o cl a0 h0 hc1 hTw).1 hl0
      exact absurd (straddle_true hqp h0 hl0 hm1' (by rw [hl1']; rfl)
        (fun e => absurd (e.mp (Nat.le_refl _))
          (Nat.not_le.2 (Nat.lt_of_lt_of_le a1 (Nat.le_trans a0 (Nat.le_succ _)))))) (by rw [hps]; simp)
    · obtain ⟨hqp, m1', hm1', hl1'⟩ := (hnp X Y Z t0 m0 l o cl a0 h0 hc1 hTw).1 hl0
      have e1 : t1 = t0 + 1 := honce t1 (t0 + 1) m1 m1' a1 (Nat.le_succ_of_le a0) h1 hm1' (by rw [hl1, hl1'])
        (by rw [hl1])
      subst e1
      have hme : m1' = m1 := by rw [hm1'] at h1; cases h1; rfl
      subst hme
      exact hnewpair m1' hqp hm1'
  | none =>
    -- newly shared by the step: the stepper's own frontier-cell invariant at `E'`
    have hown : cl.owner = some E'.tid := by rw [htid]; exact hoi
    have hp0 : (CE η).pfr l = none := by rw [Y.1]; exact ep
    have hfne : E'.pfr l ≠ none := by rw [hf']; simp
    have hvf : r.2.2.vs.vWr ≤ f := pubFrontier_holds X Y Z l f cl hp0 hf' hs'
    obtain ⟨vals, hcv, hlat, hopf⟩ := Z.2.2.1.2.1 l cl hs' hown
    have hmem : ∀ t : Nat, c'.mem[t]? = r.1[t]? := fun t => by rw [X.e1]
    -- coherence is below both messages, else they are hidden below the frontier
    have hcohle : ∀ (t : Nat) (m : Msg) (o2 : Nat), c'.mem[t]? = some m → m.loc = ⟨l, o2⟩ →
        WeakMem.hiddenFrom c'.mem ⟨l, o2⟩ t f = false → o2 < vals.length → r.2.2.vs.coh ⟨l, o2⟩ ≤ t := by
      intro t m o2 hm hl hh hlt
      obtain ⟨⟨mc, hmc, hmcl, -⟩, -, -⟩ := hlat o2 _ (List.getElem?_eq_getElem hlt)
      refine Nat.le_of_not_lt fun hlt2 => ?_
      have := hiddenFrom_true (mem := c'.mem) hlt2 (Nat.le_trans (hco X Y Z l hp0 hfne cl vals hs' hcv o2 hlt) hvf)
        (by rw [hmem]; exact hmc) hmcl
      rw [hh] at this; cases this
    obtain ⟨b, S1, us, o', hseg, hus, hTw', rfl, hgini⟩ := hgd
    have hcov1 := seg_cover hcv hseg hus (o := o' + 1) (by have := TwoAt_lt hTw'; omega)
    have hcov0 := seg_cover hcv hseg hus (o := o') (by have := TwoAt_lt hTw'; omega)
    by_cases hrs : IniSegN (E'.rc l) cl b
    · have hrr : InitRr E' cl l (b + o') := by
        intro N e us2 hT2 hu2
        obtain ⟨us3, j3, hu3, hj3, hb3⟩ := hrs N e hT2
        have e3 : us3 = us2 := Option.some.inj (hu3.symm.trans hu2)
        have hS : us = us2 := by
          rcases hseg with ⟨-, rfl, hA⟩ | ⟨N', us', j', hT', hus', -, -⟩
          · rw [hT2] at hA; simp [accs] at hA
          · rw [hT2] at hT'; simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
            obtain ⟨-, rfl⟩ := hT'
            exact Option.some.inj (hus.symm.trans hu2)
        rw [e3, ← hS] at hb3
        rw [← hS]
        have := TwoAt_lt hTw'
        have hm := Nat.mul_le_mul_right (nWords us) (show j3 + 1 ≤ E'.rc l by omega)
        rw [Nat.succ_mul] at hm; omega
      have hpf' : E'.pfr l ≠ none := hfne
      rcases hopf hpf' (b + o') ⟨b, S1, us, o', hseg, hus, hTw', rfl⟩ hrr t0 t1 m0 m1
          (hnP t0 m0 h0 (.inl hl0)) (hnP t1 m1 h1 (.inr hl1)) (by show r.1[t0]? = some m0; rw [← hmem]; exact h0)
          (by show r.1[t1]? = some m1; rw [← hmem]; exact h1)
          hl0 hl1 (hcohle t0 m0 (b + o') h0 hl0 hh0 (by omega))
          (hcohle t1 m1 (b + o' + 1) h1 hl1 hh1 (by omega)) (by rw [← X.e1, ← X.e2]; exact hps) with
        ⟨-, -, hv0, hv1⟩ | hpo
      · exact PairOK_transferS hIS hT (cellOK_pairOK hcv hseg hus hTw' hrs hv0 hv1)
      · exact PairOK_transferS hIS hT hpo
    · have hini : IniSegN (E'.ini l) cl b := hgini
      have hrc : E'.rc l < E'.ini l := Nat.lt_of_not_le fun hle => hrs (hini.mono hle)
      have hpo := Z.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl f (b + o') hs'
        (.inr ⟨hrc, b, S1, us, o', hseg, hus, hTw', rfl, hrs, hini⟩) hf' ⟨b, S1, us, o', hseg, hus, hTw', rfl⟩
        t0 t1 m0 m1 (hnP t0 m0 h0 (.inl hl0)) (hnP t1 m1 h1 (.inr hl1)) (by show r.1[t0]? = some m0; rw [← hmem]; exact h0)
        (by show r.1[t1]? = some m1; rw [← hmem]; exact h1) hl0 hl1 (by rw [← X.e1]; exact hh0) (by rw [← X.e1]; exact hh1)
        (by rw [← X.e1, ← X.e2]; exact hps)
      exact PairOK_transferS hIS hT hpo

/-- Clause 3 (`PromLt`). -/
theorem cl3_promLt : MemClT p k arch Sp Init MintOK c0 fun _ _ s => PromLt s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold t ht
  have h1 : t < c.mem.size := hold.2.2.1.2.2.1 t ht
  have h2 : c.mem.size ≤ c'.mem.size := by
    rw [X.e1]; exact (TermLiveProps.tstep_ext _ _ _ _ r X.hr).mem.size
  exact Nat.lt_of_lt_of_le h1 h2

/-- Clause 5 (`SeenLE`). -/
theorem cl5_seenLE : MemClT p k arch Sp Init MintOK c0 fun _ E s => SeenLE E s.vs.vRelSt := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l hl
  obtain ⟨f, hf, hle⟩ := hold.2.2.1.2.2.2.2.1 l hl
  exact ⟨f, (gfoot_of X Y Z).le.pfr l f hf, hle⟩

/-- Clause 4, privSlot part (`PrivCoh`): the idle thread's view is unchanged and
no new message lands at its private cells. -/
theorem cl4_privCoh : MemClT p k arch Sp Init MintOK c0 fun _ E s => PrivCoh E s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold
  have hgf := gfoot_of X Y Z
  have hI : Incl (Cut Eg j Sj) (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) :=
    (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hold' : ∀ a, PrivU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) a →
      ∃ cl, Eg.sto a.label = some cl ∧ cutSto Eg j a.label = some cl ∧ cl.owner = some j ∧
        Eg.pfr a.label = none := by
    intro a ⟨cl, _, _, _, hc, ho, hpf, _⟩
    obtain ⟨hc1, hc0⟩ := tctx_jcut X Y Z hji hc ho
    have hoi : cl.owner ≠ some i := by rw [ho]; intro h; exact hji (Option.some.inj h)
    obtain ⟨-, hp2, -⟩ := tctx_other_cell X Y Z hc1 hoi
    exact ⟨cl, hc1, hc0, ho, by rw [← hp2]; exact hpf⟩
  refine PrivCoh_of (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj) hold.2.2.1.2.2.2.1.2 (fun a hu => ?_)
    (fun _ _ => rfl) (fun t m h1 h2 hu => ?_)
  · obtain ⟨cl, N, e, us, hc, ho, hpf, h4, h5, h6, h7⟩ := hu
    obtain ⟨cl', -, hc0, -, hpf'⟩ := hold' a ⟨cl, N, e, us, hc, ho, hpf, h4, h5, h6, h7⟩
    have hc' := (tctx_jcut X Y Z hji hc ho).2
    rw [hc0] at hc'; cases hc'
    exact ⟨cl, N, e, us, hc0, ho, hpf', h4, h5,
      Nat.le_trans (Nat.mul_le_mul_right _ (TEnv.rc_mono hI.ini hI.rini _)) h6, h7⟩
  · have hm2 : c'.mem[t]? = some m := h2
    rcases Nat.lt_or_ge t c.mem.size with h | h
    · rw [tctx_pre X t h] at hm2; exact ⟨h1, hm2⟩
    · obtain ⟨cl, -, hc0, ho, hpf⟩ := hold' _ hu
      exact absurd rfl (tctx_noNewPriv X hji (S := Sj) ⟨⟨cl, hc0, ho⟩, hpf⟩ t m h hm2)


/-- Clause 4 (`FreshLP`), from T15. -/
theorem cl4_freshLP : MemClT p k arch Sp Init MintOK c0 fun g E s => FreshLP g E s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold
  refine ⟨fun jj hjj => ?_, cl4_privCoh X Y Z j thj Sj hji hj hold⟩
  have hj' : c'.ths[j]? = some thj := by rw [X.ho j hji]; exact hj
  have hG := freshT_holds X Y Z j thj hj' jj hjj
  rw [(threadSteps_lbase X.hc').1, TermStep.threadSteps_n X.hc'] at hG
  refine ⟨?_, hG.2.2.2.2, hG.2.2.1, hG.2.2.2.1⟩
  show cutSto _ j _ = none
  cases e : cutSto (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j (freshLabel c.lbase c.n j jj) with
  | none => exact e
  | some cl => have := cutSto_sub e; rw [hG.1] at this; cases this

/-- Clause 8 (`OwnPubV`), given `RiniFootF`. -/
theorem cl8_ownPubV (hri : RiniFootF p k arch Sp Init MintOK c0) :
    MemClT p k arch Sp Init MintOK c0 fun _ E s => OwnPubV E s := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z j thj Sj hji hj hold l cl f hc ho hf
  have ho' : cl.owner = some j := ho
  obtain ⟨hc1, hc0⟩ := tctx_jcut X Y Z hji hc ho'
  have hoi : cl.owner ≠ some i := by rw [ho']; intro h; exact hji (Option.some.inj h)
  obtain ⟨-, hpf, hini⟩ := tctx_other_cell X Y Z hc1 hoi
  have hrini := tctx_other_rini hri X Y Z hc1 hoi
  have hf0 : Eg.pfr l = some f := by rw [← hpf]; exact hf
  rcases hold.2.2.1.2.2.2.2.2.2.2.1 l cl f hc0 ho' hf0 with h | h | ⟨t, ht, m, hm, hl, hft, hmin, hni⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨t, ht, m, ?_, hl, hft, fun u hu m' hm' hlm => ?_, fun hw => hni ?_⟩)
    · have : t < c.mem.size := lt_of_get hm
      show c'.mem[t]? = some m
      rw [tctx_pre X t this]; exact hm
    · have hu' : u < c.mem.size := hold.2.2.1.2.2.1 u hu
      have : c.mem[u]? = some m' := by rw [← tctx_pre X u hu']; exact hm'
      exact hmin u hu m' this hlm
    · intro c1 N e us hc1' hT hu
      have hrc : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc m.loc.label =
          (Cut Eg j Sj).rc m.loc.label := by
        unfold TEnv.rc; rw [hl, Cut_ini, Cut_rini, Cut_ini, Cut_rini, hini, hrini]
      show m.loc.offset < (Cut Eg j Sj).rc m.loc.label * nWords us
      rw [← hrc]
      refine hw c1 N e us ?_ hT hu
      rw [hl] at hc1' ⊢
      show cutSto _ j l = some c1
      have hc0' : cutSto Eg j l = some c1 := hc1'
      rw [hc0'] at hc0; cases hc0; exact hc

end

/-! ## MemInv of an idle thread across a promise step (P4b), clause by clause -/

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- The type of a P4b clause. -/
def MemClP (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat)
    (Q : G → TEnv → St → Prop) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      Q (gOf p k arch c j') (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj)

/-- **P4b `interfMemP` from its eleven clauses.** -/
theorem interfMemP_of_clauses
    (h1 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => MemOKP E s.mem s.pairs s.promises)
    (h2 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => OwnOKPF E s.mem s.pairs s.vs s.promises)
    (h3 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ _ s => PromLt s)
    (h4 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun g E s => FreshLP g E s)
    (h5 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => SeenLE E s.vs.vRelSt)
    (h6 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => OwnHidP E s.mem s.vs s.promises)
    (h7 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubDefP E s.mem s.promises)
    (h8 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => OwnPubV E s)
    (h9 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubInv E s)
    (h10 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun g E s => BoxInv g E s)
    (h11 : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ _ s => PromOK s) :
    ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' thj (Sj : AllocLabel → Prop), j' ≠ j → c.ths[j']? = some thj →
      ThSysAt p (gOf p k arch c j') c.mem c.pairs thj Eg (Tot j') (HP j') HS (cr j') (db j') Sj →
      MemInv (gOf p k arch c j') (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) (stOf (c.mem.push ⟨a, v, w⟩) c.pairs thj) := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  exact ⟨h1 X j' thj Sj hjj hj hold, h2 X j' thj Sj hjj hj hold, h3 X j' thj Sj hjj hj hold,
    h4 X j' thj Sj hjj hj hold, h5 X j' thj Sj hjj hj hold, h6 X j' thj Sj hjj hj hold,
    h7 X j' thj Sj hjj hj hold, h8 X j' thj Sj hjj hj hold, h9 X j' thj Sj hjj hj hold,
    h10 X j' thj Sj hjj hj hold, h11 X j' thj Sj hjj hj hold⟩

/-- P4b clause 3. -/
theorem pcl3_promLt : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ _ s => PromLt s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold t ht
  have := hold.2.2.1.2.2.1 t ht
  show t < (c.mem.push ⟨a, v, w⟩).size
  rw [Array.size_push]; exact Nat.lt_succ_of_lt this

/-- P4b clause 5, given `PlantSpecF`. -/
theorem pcl5_seenLE (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => SeenLE E s.vs.vRelSt := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l hl
  obtain ⟨f, hf, hle⟩ := hold.2.2.1.2.2.2.2.1 l hl
  exact ⟨f, (Incl_cut_plant (N := plantN c Eg j a v w) (hspec X) j' Sj).pfr l f hf, hle⟩

/-- P4b clause 11. -/
theorem pcl11_promOK : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ _ s => PromOK s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  exact hold.2.2.1.2.2.2.2.2.2.2.2.2.2

/-- At a cell of an idle thread `j'`, the planted `E_g` agrees with `E_g`. -/
theorem plant_jcell {Eg : GEnv} {P : AllocLabel → Option Ts} {j n j' : Nat} (hP : PlantSpec Eg P j n) (hjj : j' ≠ j)
    {l : AllocLabel} {cl : Cell} (hc : Eg.sto l = some cl) (ho : cl.owner = some j') :
    P l = none := by
  cases e : P l with
  | none => rfl
  | some f =>
    obtain ⟨-, ⟨cl', hc', ho'⟩, -⟩ := hP l f e
    rw [hc] at hc'; cases hc'; rw [ho] at ho'; cases ho'; exact absurd rfl hjj

/-- P4b clause 4, privSlot part (`PrivCoh`): the idle thread's view is
unchanged and the promise is not at its private cells. -/
theorem pcl4_privCoh (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PrivCoh E s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  have hold' : ∀ b, PrivU (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) b →
      ∃ cl, Eg.sto b.label = some cl ∧ cutSto Eg j' b.label = some cl ∧ cl.owner = some j' ∧
        Eg.pfr b.label = none := by
    intro b ⟨cl, _, _, _, hc, ho, hpf, _⟩
    have hc1 : Eg.sto b.label = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
    have hn := plant_jcell hP hjj hc1 ho
    have hpf' : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).pfr b.label =
        Eg.pfr b.label := by
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr b.label = Eg.pfr b.label
      simp only [plantG, hn]
    exact ⟨cl, hc1, cutSto_own hc1 ho, ho, by rw [← hpf']; exact hpf⟩
  refine PrivCoh_of (E := Cut Eg j' Sj) (s := stOf c.mem c.pairs thj) hold.2.2.1.2.2.2.1.2 (fun b hu => ?_)
    (fun _ _ => rfl) (fun t m h1 h2 hu => ?_)
  · obtain ⟨cl, N, e, us, hc, ho, hpf, h4, h5, h6, h7⟩ := hu
    obtain ⟨-, -, -, -, hpf'⟩ := hold' b ⟨cl, N, e, us, hc, ho, hpf, h4, h5, h6, h7⟩
    have hc1' : Eg.sto b.label = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
    exact ⟨cl, N, e, us, cutSto_own hc1' ho, ho, hpf', h4, h5,
      Nat.le_trans (Nat.mul_le_mul_right _ (TEnv.rc_mono hI.ini hI.rini _)) h6, h7⟩
  · rcases push_get h2 with ⟨-, h4⟩ | ⟨-, rfl⟩
    · exact ⟨h1, h4⟩
    · obtain ⟨cl, -, hc0, ho, hpf⟩ := hold' _ hu
      exact absurd ⟨⟨cl, hc0, ho⟩, hpf⟩ ((pctx_promLoc hpl X).1 j' Sj hjj)

/-- P4b clause 4, given `PlantSpecF` and `PromLocF` (from P6). -/
theorem pcl4_freshLP (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun g E s => FreshLP g E s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  refine ⟨fun jj hjj' => ?_, pcl4_privCoh hspec hpl X j' thj Sj hjj hj hold⟩
  have hj2 : (promise c j a v w).ths[j']? = some thj := by rw [promise_other X.hth hjj]; exact hj
  have hG := freshP_holds (plantN := plantN) hspec hpl X j' thj hj2 jj hjj'
  have hlb : (promise c j a v w).lbase = c.lbase := by
    rw [(promise_inv (a := a) (v := v) (w := w) X.hth).1]
  rw [hlb, TermStep.promise_n] at hG
  refine ⟨?_, fun t m hm hl => hG.2.2.2.2 t m (by rw [prom_mem X.hth]; exact hm) hl, hG.2.2.1, hG.2.2.2.1⟩
  show cutSto _ j' _ = none
  cases e : cutSto ((plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).withFp (fpProm Eg j c.mem.size)) j'
      (freshLabel c.lbase c.n j' jj) with
  | none => exact e
  | some cl =>
    have h1 : Eg.sto (freshLabel c.lbase c.n j' jj) = some cl :=
      cutSto_sub (Eg := (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).withFp (fpProm Eg j c.mem.size)) e
    have h2 : Eg.sto (freshLabel c.lbase c.n j' jj) = none := hG.1
    rw [h2] at h1; cases h1

/-- `PromTyAOK` after a promise step (B4 (a) at the new configuration, kept by
the promise-step obligation). -/
def PromTyAPostPF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PromTyAOK (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w)

/-- (B3) **PromTyOK (a0) after a promise step** (preservation of `SysInvN.promIni`). -/
def PromIniPostPF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    PromIniOK (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (promise c j a v w)

/-- Shared cells of the planted `E_g` have `noOR` types. -/
theorem pctx_noOR (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) {l : AllocLabel} {cl : Cell}
    (hs : Eg.sto l = some cl) (hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l) : noOR cl.ty = true := by
  obtain ⟨f, hf⟩ := hsh
  cases e : plantOf c Eg j a v w l with
  | some f' => exact (hspec X l f' e).2.2.2 cl hs
  | none =>
    have hf' : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, e] at h; exact h
    exact X.inv.shty l cl ⟨f, hf'⟩ hs

/-- The new message is typed in every idle cut containing its cell. -/
theorem pctx_newOK (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN) {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) {j' : Nat} (hjj : j' ≠ j)
    (Sj : AllocLabel → Prop) {cl : Cell}
    (hc : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).sto a.label = some cl) :
    WordOK (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) cl.ty a.offset (mw ⟨a, v, w⟩) := by
  have hs : Eg.sto a.label = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
  have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared a.label := by
    obtain ⟨-, h2⟩ := cutSto_some.1 hc
    rcases h2 with h2 | h2
    · cases e : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr a.label with
      | some f => exact ⟨f, e⟩
      | none =>
        exfalso
        have hp0 : Eg.pfr a.label = none := by
          simp only [plantG] at e
          split at e
          · cases e
          · exact e
        exact (pctx_promLoc hpl X).1 j' Sj hjj ⟨⟨cl, cutSto_own hs h2, h2⟩, hp0⟩
    · exact h2
  have hpj : (promise c j a v w).ths[j]? = some (thP th c.mem.size) :=
    (promise_inv (a := a) (v := v) (w := w) X.hth).2.1
  have hm : (promise c j a v w).mem[c.mem.size]? = some ⟨a, v, w⟩ := by
    rw [prom_mem X.hth, Array.getElem?_push]; simp
  have := hpa X j (thP th c.mem.size) c.mem.size ⟨a, v, w⟩ hpj (List.mem_append_right _ (List.mem_singleton_self _))
    hm cl hs hsh
  exact WordOK_transferS (InclS_pub_cut _ j' Sj) (pctx_noOR hspec X hs hsh) this

/-- P4b clause 6, given `PlantSpecF`, `PromLocF`, `PromTyAPostPF`. -/
theorem pcl6_ownHidP (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => OwnHidP E s.mem s.vs s.promises := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) (hspec X) j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  have hmono : ∀ T o ww, WordOK (Cut Eg j' Sj) T o ww →
      WordOK (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) T o ww :=
    fun T o ww h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini
  obtain ⟨hA, hB⟩ := hold.2.2.1.2.2.2.2.2.1
  have hnew : ∀ l cl o, (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).sto l = some cl →
      ∀ (t : Nat) (m : Msg), c.mem.size ≤ t → (c.mem.push ⟨a, v, w⟩)[t]? = some m → m.loc = ⟨l, o⟩ →
        WordOK (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) cl.ty o (mw m) := by
    intro l cl o hc t m h1 h2 h3
    rcases push_get h2 with ⟨h4, -⟩ | ⟨-, rfl⟩
    · exact absurd h4 (Nat.not_lt.2 h1)
    · have e : a = ⟨l, o⟩ := h3
      subst e
      exact pctx_newOK hspec hpl hpa X hjj Sj hc
  refine ⟨fun l cl hc ho o hr => ?_, fun l cl hc ho hlt => ?_⟩
  · have ho' : cl.owner = some j' := ho
    have hc1 : Eg.sto l = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
    have hn := plant_jcell (hspec X) hjj hc1 ho'
    exact HiddenP_move push_pre (hnew l cl o hc) (hmono _ _)
      (hA l cl (cutSto_own hc1 ho') ho' o (InitRr_rc (cutP_rc hn) hr))
  · have ho' : cl.owner = some j' := ho
    have hc1 : Eg.sto l = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
    have hn := plant_jcell (hspec X) hjj hc1 ho'
    obtain ⟨f, hf, hns, hH⟩ := hB l cl (cutSto_own hc1 ho') ho' (by rw [← cutP_rc hn, ← cutP_ini hn]; exact hlt)
    refine ⟨f, ?_, fun hz => hns (fun hz0 => hz ((ZW.stoAt (hc.trans (cutSto_own hc1 ho').symm)).2 hz0)),
      fun o hio => HiddenP_move push_pre (hnew l cl o hc) (hmono _ _)
      (hH o (InitR_ini (cutP_ini hn) hio))⟩
    show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f
    simp only [plantG, hn]; exact hf


/-- A label new in an idle cut after a promise step is a planted cell of the
promiser. -/
theorem pctx_newcut (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) {j' : Nat} {l : AllocLabel} {cl : Cell}
    (hc : cutSto (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) j' l = some cl) (h0 : cutSto Eg j' l = none) :
    Eg.sto l = some cl ∧ cl.owner = some j ∧ ∃ f, plantOf c Eg j a v w l = some f := by
  obtain ⟨hs, h2⟩ := cutSto_some.1 hc
  have hs' : Eg.sto l = some cl := hs
  rcases h2 with h2 | ⟨f, hf⟩
  · rw [cutSto_own hs' h2] at h0; cases h0
  · cases e : plantOf c Eg j a v w l with
    | none =>
      have hf' : Eg.pfr l = some f := by simp only [plantG, e] at hf; exact hf
      rw [cutSto_shared hs' ⟨f, hf'⟩] at h0; cases h0
    | some f' =>
      obtain ⟨-, ⟨cl', hc', ho'⟩, -⟩ := hspec X l f' e
      rw [hs'] at hc'; cases hc'
      exact ⟨hs', ho', f', rfl⟩

/-- P4b clause 1, given `PlantSpecF`, `PromLocF`, `PromTyAPostPF`. -/
theorem pcl1_memOKP (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => MemOKP E s.mem s.pairs s.promises := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
  have hI0 := (Incl_cut_plant (N := plantN c Eg j a v w) hP j S0).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j S0)
  have hIS := InclS_cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j j' S0 Sj
  have hpj : (promise c j a v w).ths[j]? = some (thP th c.mem.size) :=
    (promise_inv (a := a) (v := v) (w := w) X.hth).2.1
  have hold1 := hold.2.2.1.1
  refine ⟨fun t m cl hn hm hc => ?_, fun t m0 m1 cl hp h0 h1 hc => ?_, fun t ht => ?_⟩
  · rcases push_get hm with ⟨h1, h2⟩ | ⟨-, rfl⟩
    · cases e : cutSto Eg j' m.loc.label with
      | some cl' =>
        have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
        have e3 : cl' = cl := Option.some.inj h3
        subst e3
        rcases hold1.1 t m cl' hn h2 e with h | h
        · exact .inl h
        · exact .inr (WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini)
      | none =>
        obtain ⟨hs, ho, f, hf⟩ := pctx_newcut (plantN := plantN) hspec X hc e
        have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m.loc.label :=
          ⟨f, by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf]⟩
        have hT := pctx_noOR hspec X hs hsh
        by_cases htj : t ∈ th.promises
        · have := hpa X j (thP th c.mem.size) t m hpj (List.mem_append_left _ htj)
            (by rw [prom_mem X.hth, push_pre t h1]; exact h2) cl hs hsh
          exact .inr (WordOK_transferS (InclS_pub_cut _ j' Sj) hT this)
        · rcases hm0.1.1 t m cl htj h2 (cutSto_own hs ho) with h | h
          · exact .inl h
          · exact .inr (WordOK_transferS hIS hT
              (WordOK_mono hI0.prog rfl hI0.sto hI0.ini hI0.pfr (fun _ h => h) h hI0.box hI0.rini))
    · exact .inr (pctx_newOK hspec hpl hpa X hjj Sj hc)
  · have hlt : t + 1 < c.mem.size := hold1.2.2 t hp
    have h0' : c.mem[t]? = some m0 := by rw [← push_pre t (Nat.lt_of_succ_lt hlt)]; exact h0
    have h1' : c.mem[t + 1]? = some m1 := by rw [← push_pre (t + 1) hlt]; exact h1
    cases e : cutSto Eg j' m0.loc.label with
    | some cl' =>
      have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
      have e3 : cl' = cl := Option.some.inj h3
      subst e3
      exact PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) (hold1.2.1 t m0 m1 cl' hp h0' h1' e)
        hI.box hI.rini
    | none =>
      obtain ⟨hs, ho, f, hf⟩ := pctx_newcut (plantN := plantN) hspec X hc e
      have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared m0.loc.label :=
        ⟨f, by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf]⟩
      exact PairOK_transferS hIS (pctx_noOR hspec X hs hsh)
        (PairOK_mono hI0.prog rfl hI0.sto hI0.ini hI0.pfr (fun _ h => h)
          (hm0.1.2.1 t m0 m1 cl hp h0' h1' (cutSto_own hs ho)) hI0.box hI0.rini)
  · have := hold1.2.2 t ht
    show t + 1 < (c.mem.push ⟨a, v, w⟩).size
    rw [Array.size_push]; exact Nat.lt_succ_of_lt this


/-- `HiddenP` with fewer skipped messages and a weaker typing. -/
theorem HiddenP_weaken {η₁ η₂ : TEnv} {T : Ty} {mem : Memory} {P P' : List Ts} {l : AllocLabel} {o : Nat} {V : Ts}
    (hP : ∀ t, t ∉ P' → t ∉ P) (hmono : ∀ w, WordOK η₁ T o w → WordOK η₂ T o w)
    (h : HiddenP η₁ T mem P l o V) : HiddenP η₂ T mem P' l o V :=
  fun t m hn hm hl hw => h t m (hP t hn) hm hl (fun h' => hw (hmono _ h'))

/-- (plant) **The planted cell is publishable**: its type meets
`PubCpl` (what every reader's `PubCpl` needs at the new shared cell). -/
def PlantCplF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f, plantOf c Eg j a v w l = some f → ∀ cl, Eg.sto l = some cl →
      LayT cl.ty ∧ (∀ b S, SegOf cl.ty b S → accs S ≠ none → TearOK S) ∧ Ty.coupledOKIn [] cl.ty = true ∧
        Ty.noOwnIn [] cl.ty = true ∧ rgnFree cl.ty = true

/-- (plant) **The planted cell's initialised words are hidden below
its frontier** for any reader (no promise skipped, typing in `PubE`): what
`MemInv_plant` must give the readers. -/
def PlantHidF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f cl, plantOf c Eg j a v w l = some f → Eg.sto l = some cl →
      ∀ o, InitR (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl l o →
        HiddenP (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty (c.mem.push ⟨a, v, w⟩) [] l o f

/-- In an idle cut, a label of the old cut keeps its frontier across a promise step. -/
theorem pctx_oldcut_pfr (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res}
    {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh} {a : Address} {v : WeakMem.Val} {w : Ts}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w) {j' : Nat} (hjj : j' ≠ j)
    {l : AllocLabel} {cl : Cell} (hc : cutSto Eg j' l = some cl) :
    plantOf c Eg j a v w l = none := by
  cases e : plantOf c Eg j a v w l with
  | none => rfl
  | some f =>
    obtain ⟨hp, ⟨cl', hc', ho'⟩, -⟩ := hspec X l f e
    obtain ⟨h1, h2⟩ := cutSto_some.1 hc
    rw [h1] at hc'; cases hc'
    rcases h2 with h2 | ⟨f', hf'⟩
    · rw [h2] at ho'; cases ho'; exact absurd rfl hjj
    · rw [hp] at hf'; cases hf'

/-- P4b clause 7, given `PlantSpecF`, `PromLocF`, `PromTyAPostPF`, `PlantHidF`. -/
theorem pcl7_pubDefP (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN) (hph : PlantHidF p k arch Sp Init MintOK c0 plantOf plantN) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubDefP E s.mem s.promises := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl f hc ho hf o hio
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    have hH := hold.2.2.1.2.2.2.2.2.2.1 l cl' f e ho hf0 o (InitR_ini (cutP_ini hn) hio)
    refine HiddenP_move push_pre (fun t m h1 h2 h3' => ?_)
      (fun w h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini) hH
    rcases push_get h2 with ⟨h4, -⟩ | ⟨-, rfl⟩
    · exact absurd h4 (Nat.not_lt.2 h1)
    · have e' : a = ⟨l, o⟩ := h3'
      subst e'
      exact pctx_newOK hspec hpl hpa X hjj Sj hc
  | none =>
    obtain ⟨hs, -, f', hf'⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    have hff : f' = f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hf'] at h; exact Option.some.inj h
    subst hff
    have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l :=
      ⟨f', by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf']⟩
    have hT := pctx_noOR hspec X hs hsh
    have hH := hph X l f' cl hf' hs o (fun N e us hT' hu => hio N e us hT' hu)
    exact HiddenP_weaken (fun t _ => by simp) (fun w h => WordOK_transferS (InclS_pub_cut _ j' Sj) hT h) hH

/-- `PubInv` from its parts (promise step). -/
theorem pcl9_of_parts
    (ha : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E _ => SeenOwn E)
    (hb : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E _ => Inh E)
    (hc : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E _ => PubCpl E)
    (hd : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubPair E s.mem s.pairs s.promises)
    (he : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubLive E s.mem) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubInv E s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  exact ⟨ha X j' thj Sj hjj hj hold, hb X j' thj Sj hjj hj hold, hc X j' thj Sj hjj hj hold,
    hd X j' thj Sj hjj hj hold, he X j' thj Sj hjj hj hold⟩

/-- P4b clause 9a (`SeenOwn`). -/
theorem pcl9a_seenOwn : MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E _ => SeenOwn E := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l hl
  rcases hold.2.2.1.2.2.2.2.2.2.2.2.1.1 l hl with ⟨cl, hc, ho⟩ | ⟨hn, hb⟩
  · exact .inl ⟨cl, cutSto_own (Eg := EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (cutSto_sub (Eg := Eg) hc) ho, ho⟩
  · obtain ⟨f, hf, -⟩ := hold.2.2.1.2.2.2.2.1 l hl
    have hf' : Eg.pfr l = some f := hf
    have hn' : Eg.sto l = none := by
      have e : cutSto Eg j' l = Eg.sto l := cutSto_eq_shared ⟨f, hf'⟩
      exact e ▸ hn
    refine .inr ⟨?_, hb⟩
    show cutSto _ j' l = none
    cases e : cutSto (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' l with
    | none => rfl
    | some cl =>
      have h2 : Eg.sto l = some cl := cutSto_sub (Eg := EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) e
      rw [hn'] at h2; cases h2

/-- (B1, F2′) **Inhabitants at a planted cell's predicted slots**: a segment
of a planted cell that the raised count newly initialises has a value of its type
in every idle cut after the promise step (`TermTyped.certified_hinhW1` at one-word
slots, modulo its run facts `RunAgree`). -/
def PlantInhF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ j' (Sj : AllocLabel → Prop) l f cl b S us, plantOf c Eg j a v w l = some f → Eg.sto l = some cl →
      SegOf cl.ty b S → accs S = some us → ¬ IniSegN (Eg.ini l) cl b →
      IniSeg (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) cl l b →
      ∃ ws, ValOf (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) S ws ∧
        ws.length = nWords us

/-- P4b clause 9b (`Inh`), given `PlantSpecF` and `PlantInhF`. -/
theorem pcl9b_inh (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf)
    (hinh : PlantInhF p k arch Sp Init MintOK c0 plantOf plantN) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E _ => Inh E := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl b S1 us hc hs hu hi
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn : plantOf c Eg j a v w l = none := by
      cases e' : plantOf c Eg j a v w l with
      | none => rfl
      | some f' =>
        obtain ⟨hp0, ⟨cl2, hc2, ho2⟩, -⟩ := hP l f' e'
        obtain ⟨hc3, ho3⟩ := cutSto_some.1 e
        rw [hc2] at hc3; cases hc3
        rcases ho3 with h | ⟨f3, hf3⟩
        · rw [ho2] at h; cases h; exact absurd rfl hjj
        · rw [hp0] at hf3; cases hf3
    obtain ⟨ws, hv, hl⟩ := hold.2.2.1.2.2.2.2.2.2.2.2.1.2.1 l cl' b S1 us e hs hu (IniSeg_ini (cutP_ini hn) hi)
    exact ⟨ws, ValOf_mono hI.prog rfl hI.sto hI.ini hv hI.pfr (fun _ h => h) hI.box hI.rini, hl⟩
  | none =>
    obtain ⟨hs0, ho, f, hf⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
    have hI0 := (Incl_cut_plant (N := plantN c Eg j a v w) hP j S0).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j S0)
    have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l :=
      ⟨f, by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf]⟩
    have hT := pctx_noOR hspec X hs0 hsh
    by_cases hold0 : IniSegN (Eg.ini l) cl b
    rotate_left
    · exact hinh X j' Sj l f cl b S1 us hf hs0 hs hu hold0 hi
    obtain ⟨ws, hv, hl⟩ := hm0.2.2.2.2.2.2.2.2.1.2.1 l cl b S1 us (cutSto_own hs0 ho) hs hu hold0
    exact ⟨ws, ValOf_transferS (InclS_cut _ j j' S0 Sj) (noOR_seg hs hT)
      (ValOf_mono hI0.prog rfl hI0.sto hI0.ini hv hI0.pfr (fun _ h => h) hI0.box hI0.rini), hl⟩

/-- P4b clause 9c (`PubCpl`), given `PlantSpecF` and `PlantCplF`. -/
theorem pcl9c_pubCpl (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf)
    (hpc : PlantCplF p k arch Sp Init MintOK c0 plantOf) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E _ => PubCpl E := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl f hc hf
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    exact hold.2.2.1.2.2.2.2.2.2.2.2.1.2.2.1 l cl' f e hf0
  | none =>
    obtain ⟨hs0, -, f', hf'⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    exact hpc X l f' hf' cl hs0

/-- P4b clause 9e (`PubLive`), given `PlantSpecF`. -/
theorem pcl9e_pubLive (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubLive E s.mem := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl f b S1 us o hc ho hf hs hu hlt
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    obtain ⟨t, m, hm, hma⟩ := hold.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.2 l cl' f b S1 us o e ho hf0 hs hu hlt
    have hm' : c.mem[t]? = some m := hm
    exact ⟨t, m, by show (c.mem.push ⟨a, v, w⟩)[t]? = some m; rw [push_pre t (lt_of_get hm')]; exact hm', hma⟩
  | none =>
    obtain ⟨hs0, hoj, -, -⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
    obtain ⟨vals, hcv, hl, -⟩ := hm0.2.1 l cl (cutSto_own hs0 hoj) hoj
    have hcov := seg_cover hcv hs hu hlt
    obtain ⟨⟨m, hm, hma, -⟩, -, -⟩ := hl (b + o) _ (List.getElem?_eq_getElem hcov)
    have hm' : c.mem[th.vs.coh ⟨l, b + o⟩]? = some m := hm
    exact ⟨_, m, by show (c.mem.push ⟨a, v, w⟩)[_]? = some m; rw [push_pre _ (lt_of_get hm')]; exact hm', hma⟩


/-! ### P4b clause 2 (`OwnOKPF`) -/

/-- (B4 PromTyOK (c) in two-word-unit form) **The promised address is
in no two-word unit of its cell** (`certified_noPairPromX`, stated at `TwoAtT`). -/
def PromNoTwoPF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ cl, Eg.sto a.label = some cl → ∀ o, TwoAtT cl.ty o → a.offset ≠ o ∧ a.offset ≠ o + 1

/-- P4b clause 2, given `PlantSpecF`, `PromLocF`, `PromTyAPostPF`, `PromNoTwoPF`. -/
theorem pcl2_ownOKPF (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0)
    (hpa : PromTyAPostPF p k arch Sp Init MintOK c0 plantOf plantN) (hnt : PromNoTwoPF p k arch Sp Init MintOK c0) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => OwnOKPF E s.mem s.pairs s.vs s.promises := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl hc ho
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  have tmono : ∀ T o ww, WordOK (Cut Eg j' Sj) T o ww →
      WordOK (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj) T o ww :=
    fun T o ww h => WordOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini
  have ho' : cl.owner = some j' := ho
  have hc1 : Eg.sto l = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
  have hc0 : cutSto Eg j' l = some cl := cutSto_own hc1 ho'
  have hn := plant_jcell hP hjj hc1 ho'
  have hpf : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).pfr l = Eg.pfr l := by
    show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = Eg.pfr l
    simp only [plantG, hn]
  obtain ⟨vals, hcv, hl, hpr⟩ := hold.2.2.1.2.1 l cl hc0 ho'
  -- the new message is at a shared cell of `j'` only
  have hnew : ∀ o, a = ⟨l, o⟩ → Eg.pfr l ≠ none := fun o e hp0 => by
    apply (pctx_promLoc hpl X).1 j' Sj hjj
    rw [e]
    exact ⟨⟨cl, hc0, ho'⟩, hp0⟩
  refine ⟨vals, by rw [cutP_rc hn]; exact CellOK_mono hI.prog rfl hI (fun _ h => h) hcv, fun o vv hv => ?_, fun hne => ?_⟩
  · obtain ⟨⟨m, hm, hma, hor⟩, hS, hlast⟩ := hl o vv hv
    refine ⟨⟨m, ?_, hma, hor.imp id fun ⟨h1, h2⟩ => ⟨by rw [hpf]; exact h1, tmono _ _ _ h2⟩⟩, hS,
      fun t m' ht hm' hl' => ?_⟩
    · have hm2 : c.mem[thj.vs.coh ⟨l, o⟩]? = some m := hm
      show (c.mem.push ⟨a, v, w⟩)[thj.vs.coh ⟨l, o⟩]? = some m
      rw [push_pre _ (lt_of_get hm2)]; exact hm2
    · rcases push_get hm' with ⟨h1, h2⟩ | ⟨-, rfl⟩
      · rcases hlast t m' ht h2 hl' with h | ⟨h3, h4⟩
        · exact .inl h
        · exact .inr ⟨by rw [hpf]; exact h3, tmono _ _ _ h4⟩
      · have e : a = ⟨l, o⟩ := hl'
        refine .inr ⟨by rw [hpf]; exact hnew o e, ?_⟩
        show WordOK _ cl.ty a.offset (mw ⟨a, v, w⟩)
        have hal : a.label = l := by rw [e]
        exact pctx_newOK hspec hpl hpa X hjj Sj (by rw [hal]; exact hc)
  · have hne0 : Eg.pfr l ≠ none := by rw [← hpf]; exact hne
    intro o hTw hrr t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1 hc0' hc1' hps
    have hpairs : ∀ q, q ∈ c.pairs → q + 1 < c.mem.size := hold.2.2.1.1.2.2
    rcases push_get h0 with ⟨h0a, h0b⟩ | ⟨-, rfl⟩
    · rcases push_get h1 with ⟨h1a, h1b⟩ | ⟨-, rfl⟩
      · exact (hpr hne0 o hTw (InitRr_rc (cutP_rc hn) hrr) t0 t1 m0 m1 hs0 hs1 h0b h1b hl0 hl1 hc0' hc1'
          (pairStraddles_back push_pre (fun q h => h) hpairs hps)).imp id
          fun h => PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h) h hI.box hI.rini
      · have e : a = ⟨l, o + 1⟩ := hl1
        exact absurd (by rw [e]) ((hnt X cl (by rw [e]; exact hc1) o hTw).2)
    · have e : a = ⟨l, o⟩ := hl0
      exact absurd (by rw [e]) ((hnt X cl (by rw [e]; exact hc1) o hTw).1)


/-! ### P4b clause 9d (`PubPair`) -/

/-- (plant) **Pairs at a planted cell are typed for every reader**
(`PubPair` at `PubE`, nothing skipped): the reader side of `MemInv_plant`.
 At a unit of a segment below the planted `ini` (`PubPair`'s guard): an uninitialised
slot holds allocation placeholders, no pair of a value. -/
def PlantPairF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts)
    (plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat) : Prop :=
  ∀ {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts},
    PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w →
    ∀ l f cl, plantOf c Eg j a v w l = some f → Eg.sto l = some cl → ∀ o, TwoAtT cl.ty o →
      (∃ b S us o', SegOf cl.ty b S ∧ accs S = some us ∧ TwoAt us o' ∧ o = b + o' ∧
        IniSegN ((EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).ini l) cl b) →
      ∀ (t0 t1 : Nat) (m0 m1 : Msg), (c.mem.push ⟨a, v, w⟩)[t0]? = some m0 → (c.mem.push ⟨a, v, w⟩)[t1]? = some m1 →
        m0.loc = ⟨l, o⟩ → m1.loc = ⟨l, o + 1⟩ → WeakMem.hiddenFrom (c.mem.push ⟨a, v, w⟩) ⟨l, o⟩ t0 f = false →
        WeakMem.hiddenFrom (c.mem.push ⟨a, v, w⟩) ⟨l, o + 1⟩ t1 f = false →
        WeakMem.pairStraddles (c.mem.push ⟨a, v, w⟩) c.pairs ⟨l, o⟩ t0 t1 = false →
        PairOK (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)) cl.ty o (mw m0) (mw m1)

/-- P4b clause 9d, given `PlantSpecF`, `PromNoTwoPF`, `PlantPairF`. -/
theorem pcl9d_pubPair (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hnt : PromNoTwoPF p k arch Sp Init MintOK c0)
    (hpp : PlantPairF p k arch Sp Init MintOK c0 plantOf plantN) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => PubPair E s.mem s.pairs s.promises := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl f o hc hg hf hTw t0 t1 m0 m1 hs0 hs1 h0 h1 hl0 hl1
    hh0 hh1 hps
  have hP := hspec X
  have hI := (Incl_cut_plant (N := plantN c Eg j a v w) hP j' Sj).trans (Incl_cut_withFp _ (fpProm Eg j c.mem.size) j' Sj)
  have hc1 : Eg.sto l = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
  -- the new message is not at either word of the unit
  have hold' : ∀ (t : Nat) (m : Msg), (c.mem.push ⟨a, v, w⟩)[t]? = some m → (m.loc = ⟨l, o⟩ ∨ m.loc = ⟨l, o + 1⟩) →
      c.mem[t]? = some m := by
    intro t m ht hl
    rcases push_get ht with ⟨-, h2⟩ | ⟨-, rfl⟩
    · exact h2
    · rcases hl with e | e
      · have e' : a = ⟨l, o⟩ := e
        have hal : a.label = l := by rw [e']
        exact absurd (by rw [e']) ((hnt X cl (by rw [hal]; exact hc1) o hTw).1)
      · have e' : a = ⟨l, o + 1⟩ := e
        have hal : a.label = l := by rw [e']
        exact absurd (by rw [e']) ((hnt X cl (by rw [hal]; exact hc1) o hTw).2)
  have h0' := hold' t0 m0 h0 (.inl hl0)
  have h1' := hold' t1 m1 h1 (.inr hl1)
  have hpre : ∀ (t : Nat) (m : Msg), c.mem[t]? = some m → (c.mem.push ⟨a, v, w⟩)[t]? = some m :=
    fun t m h => by rw [push_pre t (lt_of_get h)]; exact h
  cases e : cutSto Eg j' l with
  | some cl' =>
    have h3 : some cl' = some cl := (hI.sto _ _ e).symm.trans hc
    have e3 : cl' = cl := Option.some.inj h3
    subst e3
    have hn := pctx_oldcut_pfr hspec X hjj e
    have hf0 : Eg.pfr l = some f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hn] at h; exact h
    have hpairs : ∀ q, q ∈ c.pairs → q + 1 < c.mem.size := hold.2.2.1.1.2.2
    exact PairOK_mono hI.prog rfl hI.sto hI.ini hI.pfr (fun _ h => h)
      (hold.2.2.1.2.2.2.2.2.2.2.2.1.2.2.2.1 l cl' f o e (by have h := hg; rw [cutP_ini hn, cutP_rc hn] at h; exact h) hf0 hTw t0 t1 m0 m1 hs0 hs1 h0' h1' hl0 hl1
        (hiddenFrom_grow hpre hh0) (hiddenFrom_grow hpre hh1)
        (pairStraddles_back push_pre (fun q h => h) hpairs hps)) hI.box hI.rini
  | none =>
    obtain ⟨hs0', -, f', hf'⟩ := pctx_newcut (plantN := plantN) hspec X hc e
    have hff : f' = f := by
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
      simp only [plantG, hf'] at h; exact Option.some.inj h
    subst hff
    have hsh : (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size).Shared l :=
      ⟨f', by show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr _ = _; simp only [plantG, hf']⟩
    exact PairOK_transferS (InclS_pub_cut _ j' Sj) (pctx_noOR hspec X hs0' hsh)
      (hpp X l f' cl hf' hs0' o hTw (hg.elim (fun h => h.2) (fun h => by
        obtain ⟨b, S, us, o', h1, h2, h3, h4, -, h6⟩ := h.2
        exact ⟨b, S, us, o', h1, h2, h3, h4, h6⟩)) t0 t1 m0 m1 h0 h1 hl0 hl1 hh0 hh1 hps)

/-- P4b clause 8, given `PlantSpecF`. -/
theorem pcl8_ownPubV (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun _ E s => OwnPubV E s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold l cl f hc ho hf
  have ho' : cl.owner = some j' := ho
  have hc1 : Eg.sto l = some cl := cutSto_sub (Eg := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) hc
  have hc0 : cutSto Eg j' l = some cl := cutSto_own hc1 ho'
  have hn := plant_jcell (hspec X) hjj hc1 ho'
  have hf0 : Eg.pfr l = some f := by
    have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = some f := hf
    simp only [plantG, hn] at h; exact h
  rcases hold.2.2.1.2.2.2.2.2.2.2.1 l cl f hc0 ho' hf0 with h | h | ⟨t, ht, m, hm, hl, hft, hmin, hni⟩
  · exact .inl h
  · exact .inr (.inl h)
  · refine .inr (.inr ⟨t, ht, m, ?_, hl, hft, fun u hu m' hm' hlm => ?_, fun hw => hni ?_⟩)
    · have hm' : c.mem[t]? = some m := hm
      show (c.mem.push ⟨a, v, w⟩)[t]? = some m
      rw [push_pre t (lt_of_get hm')]; exact hm'
    · have hu' : u < c.mem.size := hold.2.2.1.2.2.1 u hu
      have : c.mem[u]? = some m' := by rw [← push_pre u hu']; exact hm'
      exact hmin u hu m' this hlm
    · intro c1 N e us hc1' hT hu
      have hrc : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).rc m.loc.label =
          (Cut Eg j' Sj).rc m.loc.label := by rw [hl]; exact cutP_rc hn
      show m.loc.offset < (Cut Eg j' Sj).rc m.loc.label * nWords us
      rw [← hrc]
      refine hw c1 N e us ?_ hT hu
      rw [hl] at hc1' ⊢
      show cutSto _ j' l = some c1
      have hc0' : cutSto Eg j' l = some c1 := hc1'
      rw [hc0'] at hc0; cases hc0; exact hc

/-- P4b clause 10, given `PlantSpecF` and `PromLocF`. -/
theorem pcl10_boxInv (hspec : PlantSpecF p k arch Sp Init MintOK c0 plantOf) (hpl : PromLocF p k arch Sp Init MintOK c0) :
    MemClP p k arch Sp Init MintOK c0 plantOf plantN fun g E s => BoxInv g E s := by
  intro c Eg Tot HP HS cr db j th a v w X j' thj Sj hjj hj hold
  have hj2 : (promise c j a v w).ths[j']? = some thj := by rw [promise_other X.hth hjj]; exact hj
  have hold10 := hold.2.2.1.2.2.2.2.2.2.2.2.2.1
  obtain ⟨S0, -, -, hm0, -⟩ := X.inv.thr j th X.hth
  have hlb : (promise c j a v w).lbase = c.lbase := by
    rw [(promise_inv (a := a) (v := v) (w := w) X.hth).1]
  refine ⟨fun jj hjj' => ?_, ?_, fun l B hB => ?_⟩
  · have hG := freshP_holds (plantN := plantN) hspec hpl X j' thj hj2 jj hjj'
    rw [hlb, TermStep.promise_n] at hG
    exact hG.2.1
  · have h := BoxTopP_of_G (i := j') (S := Sj) (P := thj.promises) (boxtopP_holds (plantOf := plantOf) (plantN := plantN) hpl X)
      (fun t ht => mem_allProms.2 ⟨j', thj, hj2, ht⟩)
    rw [prom_mem X.hth] at h; exact h
  · have hB0 : Eg.box l = some B := hB
    obtain ⟨hcj, hij, hsj⟩ := hold10.2.2 l B hB0
    have hcj0 : cutSto Eg j l = none := (hm0.2.2.2.2.2.2.2.2.2.1.2.2 l B hB0).1
    have hn : plantOf c Eg j a v w l = none := by
      cases e : plantOf c Eg j a v w l with
      | none => rfl
      | some f =>
        obtain ⟨-, ⟨cl, hc, ho⟩, -⟩ := hspec X l f e
        rw [cutSto_own hc ho] at hcj0; cases hcj0
    have hpf : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr l = Eg.pfr l := by simp only [plantG, hn]
    refine ⟨?_, (cutP_ini hn).trans hij, fun hs => (hsj hs).imp fun o w' h => ?_⟩
    · show cutSto (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) j' l = none
      have hcj' : cutSto Eg j' l = none := hcj
      exact (cutSto_congr (Eg' := plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)) (Eg := Eg) rfl
        (fun _ _ _ => by unfold GEnv.Shared; rw [hpf])).trans hcj'
    · show LatestP (c.mem.push ⟨a, v, w⟩) thj.promises thj.vs.coh ⟨l, o⟩ w'
      exact LatestS_grow push_pre (fun t m h1 h2 e => by
        rcases push_get h2 with ⟨h3, -⟩ | ⟨-, rfl⟩
        · exact absurd h3 (Nat.not_lt.2 h1)
        · exact (pctx_promLoc hpl X).2.1 l B hB0 e) h

end

#print axioms gfoot_rini_other
#print axioms ThInvRE_incl
#print axioms ThInvE_incl
#print axioms interfFrameT_holds
#print axioms interfFrameP_holds
#print axioms interfHPT_holds
#print axioms fpokVisT_holds
#print axioms freshT_holds
#print axioms interfCrT_holds
#print axioms boxtopT_holds
#print axioms fpokVisP_holds
#print axioms boxtopP_holds
#print axioms freshP_holds
#print axioms interfHPP_holds
#print axioms interfCrP_holds
#print axioms interfMemT_of_clauses
#print axioms cl3_promLt
#print axioms cl4_privCoh
#print axioms cl4_freshLP
#print axioms cl5_seenLE
#print axioms cl8_ownPubV
#print axioms cl10_boxInv
#print axioms cl11_promOK
#print axioms cl1_memOKP
#print axioms cl6_ownHidP
#print axioms interfMemP_of_clauses
#print axioms pcl3_promLt
#print axioms pcl4_privCoh
#print axioms pcl4_freshLP
#print axioms pcl5_seenLE
#print axioms pcl8_ownPubV
#print axioms pcl10_boxInv
#print axioms pcl11_promOK
#print axioms pcl6_ownHidP
#print axioms pcl1_memOKP
#print axioms cl9_of_parts
#print axioms cl9a_seenOwn
#print axioms cl9b_inh
#print axioms cl9c_pubCpl
#print axioms cl9e_pubLive
#print axioms cl7_pubDefP
#print axioms pcl7_pubDefP
#print axioms pcl9_of_parts
#print axioms pcl9a_seenOwn
#print axioms pcl9b_inh
#print axioms pcl9c_pubCpl
#print axioms pcl9e_pubLive
#print axioms pcl2_ownOKPF
#print axioms pcl9d_pubPair
#print axioms cl9d_pubPair
#print axioms tstep_pairsUp
#print axioms cl2_ownOKPF
#print axioms pairStepper_holds
#print axioms interfCrT_mover
#print axioms interfCrPK_holds
#print axioms interfCrTK_holds
#print axioms promSelfK_holds
#print axioms riniFoot_holds
#print axioms pubFrontier_holds
#print axioms interfCrT_cond
#print axioms interfCrT_mover
#print axioms interfDb_mover

end TermInterf

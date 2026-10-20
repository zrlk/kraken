import WeakCore.TermOwnK5
import WeakCore.TermPlantF
import WeakCore.TermOwnG0Defs

/-!
# TermBiiT: the thread-step half of `bufInitIni` (bufInit rework, item 1)

`TermPlantF.BufInitIniT` (restated with the stepper's `PfrG` at `pf := PubAt th` and the target
link `BufInitOn th1 l`) holds vacuously: the newly shared cell is an own cell of the stepper whose
frontier changed, so the step publishes it (`PfrG`), and `TermOwnK5.bufInitIniT_pub` excludes a
certificate `bufInit` on a cell the step publishes.  From the fields `certWinC` / `CertScopeC`
(already used for `BufInitPubT`); nothing here feeds them.
-/

namespace TermBiiT
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermCertScope TermOwnK5 TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem bufInitIniT_pfr [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r)
    (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs
      (HP i + HS) (cr i) (db i) δ)
    (hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {l : AllocLabel} {f : Nat} (hn0 : Eg.pfr l = none) (hf : E'.pfr l = some f)
    {cl : Cell} (hcl : Eg.sto l = some cl)
    {c1 : Cfg} {th1 : TTh} (h1 : Solo p k arch i c' c1) (hc1 : Certified p k arch c1 i)
    (hth1 : c1.ths[i]? = some th1) (hon : BufInitOn th1 l) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : False := by
  have hF := Z.1
  have hCE : CE η = Cut Eg i S := Y.1
  have hnf : ¬ FreshIn (gOf p k arch c i) th.nalloc r.2.2.nalloc l := fun ⟨jj, hjj, _, hlj⟩ => by
    have hl' : l = freshLabel c.lbase c.n i jj := hlj
    have := (X.inv.fresh i th X.hth jj hjj).1
    rw [← hl', hcl] at this; cases this
  have hpf0 : (CE η).pfr l = none := by rw [hCE]; exact hn0
  -- the newly shared cell is an own cell of `i` in the cut
  obtain ⟨cc, hcc, hoc⟩ : ∃ cc, (CE η).sto l = some cc ∧ cc.owner = some i := by
    rcases hF.2.2.2.2.2.1 l with e2 | ⟨-, -, -, -, -, ⟨cc, hcc, hoc⟩, -⟩ | ⟨hfr, -⟩
    · rw [hf, hpf0] at e2; cases e2
    · refine ⟨cc, hcc, ?_⟩
      rw [hoc, hCE]; rfl
    · exact absurd hfr hnf
  have hsto : Eg.sto l = some cc := by rw [hCE] at hcc; exact cutSto_sub hcc
  -- its frontier changed, so the step publishes it
  have hpub : TermOwnG0Defs.PubAt th l :=
    hPfrP l (by rw [hcc]; exact fun h => by cases h) (by rw [hf, hpf0]; exact fun h => by cases h)
  obtain ⟨y, a, e, rt, ws, ad, hterm, hea, hws, hx⟩ := hpub
  obtain ⟨y1, bb, ib, v1, e1, rt1, w1, ad1, g1, hterm1, hbb, hw1, hl1⟩ := hon
  exact bufInitIniT_pub (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc hw X hsto hoc hterm hea hws hx h1 hc1 hth1 hterm1 rt1 w1 ad1 g1 hbb hw1 hl1

/-- **`BufInitIniT`** (thread-step half of the old `bufInitIni` field, restated), from `CertScopeC`
and `CertWinC`. -/
theorem bufInitIniT_of [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    BufInitIniT p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPfrP l f hn0 hf
    t m ht hm hl c1 th1 x bb i' v' e h1 hc1 hth1 hterm ht1 hon cl hcl
  exact (bufInitIniT_pfr (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc hw X Y Z hPfrP hn0 hf hcl h1 hc1 hth1 hon).elim

end TermBiiT

#print axioms TermBiiT.bufInitIniT_pfr
#print axioms TermBiiT.bufInitIniT_of

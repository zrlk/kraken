import WeakCore.TermNoBufOwn
import WeakCore.TermPlantF

/-!
# TermBufPubT: the thread-step post-publish `bufInit` exclusion (runAgree)

`TermPlantF.BufInitPubTR` (the `hZo` of the thread-step typed runs at `PubZO`) holds from the raw
certificate-window hypotheses: an own cell of the post-step environment with a frontier is a start cell of the
promiser's cut (`post_pfr_sto`), or the step publishes it, and in both cases `TermNoBufOwn.noBufT_pub`
rules out a `bufInit` after the run's publish.
-/

namespace TermBufPubT
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermTyped TermMain TermPlantF TermCertScope
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- A `publish` naming the stepper's own cell is the step's publish (`PubStepOf`): the reference's
offset `0` is an instance of `PubStepOf`'s `g'`. -/
theorem pubStep_of {Eg : GEnv} {i : Nat} {th : TTh} {l : AllocLabel} {cl : Cell}
    (h : TermOwnG0Defs.PubAt th l) (hs : Eg.sto l = some cl) (ho : cl.owner = some i) : PubStepOf Eg i th l :=
  let ⟨y, a, e, rt, ws, ad, h1, h2, h3, h4⟩ := h
  ⟨cl, y, a, e, rt, ws, ad, 0, hs, ho, h1, h2, h3, h4⟩

/-- (shared) **A cell of the post-step environment with a frontier** is a start cell of the stepper's
cut with that frontier (the footprint keeps the frontier of a start cell, fresh cells have none), or
the step sets the frontier, which is the step's publish (`PfrG`). -/
theorem post_pfr_sto {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {η : TEnv} {E' : TEnv}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (hCE : CE η = Cut Eg i S)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hPfrP : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    {l : AllocLabel} {cl : Cell} {f : Ts} (hcl : E'.sto l = some cl) (hf : E'.pfr l = some f) :
    (Eg.sto l = some cl ∧ Eg.pfr l = some f) ∨ PubStepOf Eg i th l := by
  rcases hF.2.2.2.2.2.1 l with e2 | ⟨hn, F, eF, -, -, ⟨cc, hcc, hoc⟩, -⟩ | ⟨-, -, hs0⟩
  · have hpf : Eg.pfr l = some f := by
      have h := e2.symm.trans hf
      rw [hCE] at h
      exact h
    rcases hF.2.2.1 l with es | ⟨hfr, -⟩
    · rw [es, hCE] at hcl
      exact .inl ⟨cutSto_sub hcl, hpf⟩
    · have h := (X.inv.gfresh X.hth r.2.2.nalloc l hfr).2.2
      rw [hpf] at h
      cases h
  · have hpub : TermOwnG0Defs.PubAt th l :=
      hPfrP l (by rw [hcc]; exact fun e => by cases e) (by rw [eF, hn]; exact fun e => by cases e)
    rw [hCE] at hcc hoc
    exact .inr (pubStep_of hpub (cutSto_sub hcc) hoc)
  · rw [hs0] at hcl
    cases hcl

/-- **`BufInitPubTR` holds**, from the thread-step certificate-window hypotheses. -/
theorem bufInitPubTR_of [TermTyped.WrIniC] {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop}
    {c0 : Cfg} (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p)
    (hsc : CertScopeC p k arch Sp Init MintOK c0) (hw : CertWinC p k arch Sp Init MintOK c0) (hPS : PwSkel)
    (hSub : PwSubS) (hSig : PwSig) : BufInitPubTR p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ X Y Z hPfrP c1 th1 c1' c3 th3
    l cl f h1 hth1 hpub hs h2 hc3 hth3 hcl ho hf
  have hCE : CE η = Cut Eg i S := Y.1
  have hF := Z.1
  have htid : E'.tid = i := by rw [hF.2.1, hCE]; rfl
  obtain ⟨cl0, hsto, hoi⟩ : ∃ cl0, Eg.sto l = some cl0 ∧ cl0.owner = some i := by
    rcases post_pfr_sto X hCE hF hPfrP hcl hf with ⟨h, -⟩ | ⟨cl0, -, -, -, -, -, -, -, hs0, ho0, -⟩
    · exact ⟨cl, h, by rw [ho, htid]⟩
    · exact ⟨cl0, hs0, ho0⟩
  exact TermNoBufOwn.noBufT_pub (hV0 := hV0) hP hsc hw X hsto (.inl hoi) h1.toSolo hth1 hpub hs h2 hc3 hth3 hPS hSub hSig

end TermBufPubT

#print axioms TermBufPubT.pubStep_of
#print axioms TermBufPubT.post_pfr_sto
#print axioms TermBufPubT.bufInitPubTR_of

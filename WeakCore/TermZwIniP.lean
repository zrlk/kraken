import WeakCore.TermZwIni
import WeakCore.TermMainDefs
import WeakCore.TermPlantF
import WeakCore.TermPlantFul

/-!
# TermZwIniP: `ZwIniG` at promise (plant) and thread steps
-/

namespace TermZwIniP

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermMain TermPlantF TermZwIni
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- The plant keeps the clause when its count covers every planted zero-width buffer. -/
theorem zwIni_plantG {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat} (hz : ZwIniG Eg)
    (hN : PlantZw Eg P N) : ZwIniG (plantG Eg P N) := by
  intro l c Nn e us hp hd hs hT hus h0 hinh
  change ¬ Eg.pubd l at hd
  change Eg.sto l = some c at hs
  change InhZ Eg.prog e at hinh
  simp only [plantG] at hp ⊢
  cases e1 : P l with
  | none =>
    simp only [e1] at hp ⊢
    exact hz l c Nn e us hp hd hs hT hus h0 hinh
  | some f =>
    exact Nat.le_trans (hN l f c Nn e us e1 hs hT hus h0 hinh) (Nat.le_max_right _ _)

/-- `plantN` covers every zero-width buffer `plantOf` plants (`PlantSpec`: an own cell of the
promiser, so its cut holds it; `NpZ_zw`). -/
theorem plantN_zw {c : Cfg} {Eg : GEnv} {j : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} {n : Nat}
    (hspec : PlantSpec Eg (plantOf c Eg j a v w) j n) :
    PlantZw Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) := by
  intro l f cc Nn e us hP hs hT hus h0 hinh
  obtain ⟨c0, hs0, ho⟩ := (hspec l f hP).2.1
  rw [hs] at hs0; cases hs0
  unfold plantN
  cases hth : c.ths[j]? with
  | none => simp [plantOf, hth] at hP
  | some th =>
    simp only
    have hcs : (cutP Eg j).sto l = some cc := cutSto_some.2 ⟨hs, Or.inl ho⟩
    exact Nat.le_of_eq (NpZ_zw hcs hT hus h0 hinh).symm

/-- (promise step) **`E_g` after a promise keeps the clause** (the plant covers zero-width
buffers: `PlantZw`, from `plantN_zw` for the standard plant). -/
theorem zwIni_prom {Eg : GEnv} {P : AllocLabel → Option Ts} {N : AllocLabel → Nat}
    (hz : ZwIniG Eg) (hN : PlantZw Eg P N) (j m : Nat) : ZwIniG (EgP Eg P N j m) :=
  zwIni_plantG hz hN

/-- (thread step) **`EgT` keeps the clause** (`zwIni_post`; `withFp` touches only `fpOf`). -/
theorem zwIni_EgT {g : G} {Eg : GEnv} {S : AllocLabel → Prop} {E' : TEnv} {s s' : St} {c' : Cfg}
    (hz : ZwIniG Eg) (hf : EFoot g (Cut Eg g.i S) E' s s') (hfr : GFreshE g Eg s.nalloc s'.nalloc)
    (hnew : ∀ l, Eg.pfr l = none → E'.pfr l ≠ none → ¬ E'.seen l → ∀ cl N e us, E'.sto l = some cl →
      cl.ty = .array (.lit N) e → accs e = some us → nWords us = 0 → InhZ Eg.prog e → N ≤ E'.ini l) :
    ZwIniG (EgT Eg g s.nalloc s'.nalloc E' c') :=
  zwIni_post hz hf hfr hnew

/-- `promIni` read at a thread's cut (`bh1_of`'s `hpi`). -/
theorem promIniE_cut {Eg : GEnv} {c : Cfg} {i : Nat} {th : TTh} {S : AllocLabel → Prop}
    (h : PromIniOK Eg c) (hth : c.ths[i]? = some th) : PromIniE (Cut Eg i S) (stOf c.mem c.pairs th) :=
  fun t m ht hm cl hs hp => h i th t m hth ht hm cl (cutSto_sub hs) (Option.ne_none_iff_exists'.1 hp)

#print axioms promIniE_cut

/-- (BH1 guard) **A `bufInit` target is not published**: the op is own-path, so the frame holds
the target's own key (`TermPlantFul.ownKey_frame`), which `ownPub` forbids at a published cell. -/
theorem bufInit_notPubd {p : Prog} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {i : Nat} {th : TTh}
    (hop : OwnPubG c Eg Tot HP HS) (hth : c.ths[i]? = some th) {S : AllocLabel → Prop} {ρ : Nat → Nat}
    {η : TEnv} {cx : Cx} {Rf Rs : Res} {K : TEnv → Nat → List Word → Res → Prop}
    (hCE : CE η = Cut Eg i S) (hsum : Rf + Rs = Tot i) (hT : Typed p cx th.term)
    (hi : FInvR ρ η th.σs K cx th.env Rf) (hsc : StepScope cx th.term ∨ StepScopeR th.σs cx th.term)
    {x : String} {b ia v : At} {e : Expr} (hterm : th.term = .let_ x (.bufInit b ia v) e) :
    ∀ rt w ad, evalAt th.env b = some (rt, [w]) → w.val = .loc ad 0 → ¬ Eg.pubd ad.label := by
  intro rt w ad he hw hpd
  have hop' : OwnOpT cx th.term := Or.inl ⟨x, e, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨b, ia, v, hterm⟩))))⟩
  have htg : TermPlant.OpTgt th ad.label := ⟨b, rt, w, ad, 0, by rw [hterm]; rfl, he, hw, rfl⟩
  obtain ⟨cl, hs, -, h1⟩ := TermPlantFul.ownKey_frame hT hi hsc hop' htg
  have hs' : (Cut Eg i S).sto ad.label = some cl := by rw [← hCE]; exact hs
  have hg := cutSto_sub hs'
  have h2 := ((hop ad.label hpd).2 (by rw [hg]; simp)).1 i th hth
  have e1 := congrArg (fun R : Res => R (.own ad.label)) hsum
  simp only [Res.add_apply] at e1 h2
  omega

#print axioms bufInit_notPubd

#print axioms zwIni_plantG
#print axioms plantN_zw
#print axioms zwIni_prom
#print axioms zwIni_EgT

end TermZwIniP

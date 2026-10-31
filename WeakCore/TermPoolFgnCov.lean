import WeakCore.TermPoolStaging
import WeakCore.TermOverCrPoolG
import WeakCore.TermULBr

/-! The pool member `fgnCov`.  Stage 1: the reduction of the cover at the
split credits `crN … j` to the cover at `crPl cr pl j + δ` plus the support lemma (gap 2): every
item needing the transfer at its holder is `QCr` (→ `δc`) or a post pool tag (→ `δh`). -/

namespace TermPoolFgnCov
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh TermPoolStaging
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- `CrItemQ` is upward monotone in the credit at the item's holder. -/
theorem crItemQ_le {E : TEnv} {s : St} {F G : Ts → Res} {l : AllocLabel} {cl : Cell}
    {x : Ts × Nat × Ty × List Word × Res × (Nat → Bool)} (hle : x.2.2.2.2.1 ≤ G x.1)
    (h : TermOverCr.CrItemQ E s F l cl x) : TermOverCr.CrItemQ E s G l cl x := by
  obtain ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -, a13⟩ := h
  exact ⟨mh, usS, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, hle, a13⟩

theorem ne_zero_of_le {A B : Res} (hle : A ≤ B) (h : A ≠ .zero) : B ≠ .zero := by
  intro hB
  apply h
  exact Res.ext fun k => by
    have := hle k
    rw [hB] at this
    exact Nat.le_zero.1 this

/-- **Lowering the credits** of a cover: items keep their amounts, nonzero credits stay items. -/
theorem overCrL_lower {E : TEnv} {s : St} {F G : Ts → Res} {l : AllocLabel} {cl : Cell}
    {W : Nat → Ts → Prop} {Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))}
    (h : TermOverCr.OverCrL E s F l cl W Gs) (hle : ∀ t, G t ≤ F t)
    (hit : ∀ x ∈ Gs, x.2.2.2.2.1 ≤ G x.1) : TermOverCr.OverCrL E s G l cl W Gs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, fun x hx => crItemQ_le (hit x hx) (h2 x hx), h3, h4,
    fun t m ht hm hl hw hG => h5 t m ht hm hl hw (ne_zero_of_le (hle t) hG)⟩

/-- The split credits at a foreign `j`. -/
theorem crN_other (cr pl : Nat → Ts → Res) {i j : Nat} (cr' : Ts → Res) (s' : St) (plh dc dh : Ts → Res)
    (h : j ≠ i) (t : Ts) : crN cr pl i cr' s' plh dc dh j t = (cr j t + dc t) + (pl j t + dh t) := by
  simp only [crN, crPl_apply, updD_other _ _ _ h]

/-- The support hypothesis (gap 2) at one cover item list: an item whose amount exceeds the
pre credits plus pool at its holder sits at a promise of `thj` that is `QCr` (plant credit off `SlotFW`) or a post pool tag. -/
def SuppAt (cr pl : Nat → Ts → Res) (δ : Ts → Res) (c' : Cfg) (Eg' : GEnv) (j : Nat) (thj : TTh)
    (Gs : List (Ts × Nat × Ty × List Word × Res × (Nat → Bool))) : Prop :=
  ∀ x ∈ Gs, ¬ x.2.2.2.2.1 ≤ crPl cr pl j x.1 → x.1 ∈ thj.promises ∧
    (QCr Eg' c' j x.1 (cr j x.1 + δ x.1) ∨
      ∀ thj', c'.ths[j]? = some thj' → PTag Eg' c' j thj' (fun u => pl j u + δ u) x.1)

/-- **The reduction**: the cover at `crPl cr pl j + δ` and the support give the cover at `crN … j`. -/
theorem crN_cover {cr pl : Nat → Ts → Res} {δ cr' plh : Ts → Res} {c c' : Cfg} {Eg' : GEnv} {i j : Nat}
    {thj : TTh} {s' : St} {E : TEnv} {s : St} {l : AllocLabel} {cl : Cell}
    (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    (hOC : TermOverCr.OverCrE E s (fun t => crPl cr pl j t + δ t) l cl)
    (hS : ∀ Gs, TermOverCr.OverCrL E s (fun t => crPl cr pl j t + δ t) l cl (TermOverCr.WinG E s l) Gs →
      SuppAt cr pl δ c' Eg' j thj Gs) :
    TermOverCr.OverCrE E s (crN cr pl i cr' s' plh (δc δ cr c c' Eg' i) (δh δ cr pl c c' Eg' i) j) l cl := by
  classical
  obtain ⟨Gs, hL, hH⟩ := hOC
  have hsup := hS Gs hL
  refine ⟨Gs, overCrL_lower hL (fun t => ?_) (fun x hx => ?_), hH⟩
  · rw [crN_other _ _ _ _ _ _ _ hji]
    have := δc_add_δh_le δ cr pl c c' Eg' i t
    intro k
    have hk := this k
    simp only [Res.add_apply, crPl_apply] at hk ⊢
    omega
  · rw [crN_other _ _ _ _ _ _ _ hji]
    have hx := hL.2.1 x hx
    obtain ⟨mh, usS, -, -, -, -, -, -, -, -, -, -, -, hR, -⟩ := hx
    by_cases hn : x.2.2.2.2.1 ≤ crPl cr pl j x.1
    · intro k
      have := hn k
      simp only [Res.add_apply, crPl_apply] at this ⊢
      omega
    · obtain ⟨hp, hq⟩ := hsup x hx hn
      have hfull : δc δ cr c c' Eg' i x.1 = δ x.1 ∨ δh δ cr pl c c' Eg' i x.1 = δ x.1 := by
        by_cases hC : ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ x.1 ∈ thj.promises ∧
            QCr Eg' c' j x.1 (cr j x.1 + δ x.1)
        · left; unfold δc; rw [ite_eq_left hC]
        · right
          rcases hq with hq | hq
          · exact absurd ⟨j, thj, hji, hj, hp, hq⟩ hC
          · have hH : (¬ ∃ j thj, j ≠ i ∧ c.ths[j]? = some thj ∧ x.1 ∈ thj.promises ∧
                QCr Eg' c' j x.1 (cr j x.1 + δ x.1)) ∧
                ∃ j' thj', j' ≠ i ∧ c.ths[j']? = some thj' ∧ x.1 ∈ thj'.promises ∧
                  ¬ QCr Eg' c' j' x.1 (cr j' x.1 + δ x.1) ∧
                  ∀ thj'', c'.ths[j']? = some thj'' → PTag Eg' c' j' thj'' (fun u => pl j' u + δ u) x.1 :=
              ⟨hC, j, thj, hji, hj, hp, fun h => hC ⟨j, thj, hji, hj, hp, h⟩, hq⟩
            unfold δh; rw [ite_eq_left hH]
      intro k
      have hk := hR k
      simp only [Res.add_apply, crPl_apply] at hk ⊢
      rcases hfull with e | e
      · rw [e]; have := Res.zero_le (δh δ cr pl c c' Eg' i x.1) k; omega
      · rw [e]; have := Res.zero_le (δc δ cr c c' Eg' i x.1) k; omega

/-! ## Stage 2: `fgnCov` (amended with `StepTgt`) from `foreign_overCrCfg1PV` / `foreign_overCrNPOUV`

`pub` store: `foreign_overCrCfg1PVG` at `cv := crPl cr pl`, with `GdCovT` (`StepTgt`), `hPd`, `htgW1`
(`StepTgt`), `hUL` (`TermULBr.hUL_step`), `hDrop` (`CE η = Cut Eg i S`); named: the cell's upgraded
pre-cover and window transport `TermFreeQW.HWbRUp` (hWbR route (iii), `foreign_overCrCfg1PVG`).
Otherwise: `Gd = []` and `foreign_overCrNPOUV` (its drop premises vacuous).  Then `crN_cover` with the
named gap-2 support `SuppAll`. -/

/-- The gap-2 support at every item list of the post cover at `crPl cr pl j + δ`. -/
def SuppAll (cr pl : Nat → Ts → Res) (δ : Ts → Res) (c' : Cfg) (Eg' : GEnv) (j : Nat) (thj : TTh)
    (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell) : Prop :=
  ∀ Gs, TermOverCr.OverCrL (Cut Eg' j Sj) (stOf c'.mem c'.pairs thj) (fun t => crPl cr pl j t + δ t) l cl
      (TermOverCr.WinG (Cut Eg' j Sj) (stOf c'.mem c'.pairs thj) l) Gs →
    SuppAt cr pl δ c' Eg' j thj Gs

/-- The common antecedent of the amended `fgnCov` (its hypotheses up to the cell). -/
def Ante (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg)
    (c c' : Cfg) (Eg : GEnv) (Tot HP : Nat → Res) (HS : Res) (cr db pl : Nat → Ts → Res) (i : Nat) (th : TTh)
    (r : Memory × List Ts × TTh) (S : AllocLabel → Prop) (ρ : Nat → Nat) (η : TEnv) (cx : Cx) (Rf Rs : Res)
    (E' : TEnv) (Tot' HP' HS' C F : Res) (cr' db' δ : Ts → Res)
    (Gd : List TermPiece.GdE) (tg : TermPiece.GdE → Option Ts)
    (j : Nat) (thj : TTh) (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell) : Prop :=
  TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r ∧ EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs ∧
    TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ ∧
    TermOverCr.OverCrG Eg c (crPl cr pl) ∧ PoolTag Eg c pl ∧
    TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd ∧
    (∀ t, δ t = TermPlant.plantD1 Gd TermPiece.GdE.R tg t) ∧
    StepTgt p k arch c c' Eg i th r η cx E' Gd tg ∧ j ≠ i ∧ c.ths[j]? = some thj ∧
    (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl ∧ cl.owner = some j ∧
    (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none

/-- The cover at `crPl cr pl j + plantD1`, both branches. -/
theorem cover_cv {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
    {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell}
    (hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl)
    (hWb : TermPiece.PubShape cx th →
      TermFreeQW.HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (crPl cr pl) j thj Sj l cl) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => crPl cr pl j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  classical
  obtain ⟨X, Y, Z, hOC, -, hDrop, -, ⟨hPS, hPd, hW1, hNP⟩, hji, hj, hc2, hown, hpf2⟩ := hA
  have hUL := TermULBr.hUL_step X Y Z X.inv.undefLow hji hj hc2 hown hpf2
  by_cases hps : TermPiece.PubShape cx th
  · obtain ⟨lt, ot, n, L0, -, hTF, hcov, hLT, hLT0⟩ := hPS hps
    rw [Y.1] at hcov hLT hLT0 hDrop
    exact TermOverCrW.foreign_overCrCfg1PVG X Y Z hji hj hc2 hown hpf2 hTF hcov hLT0 hLT hDrop hPd
      (fun g hg hgl o tw hl _ hnw us hus h1 h2 h3 => hW1 j thj Sj l cl hji hj hc2 hown hpf2 g hg hgl o tw hl hnw us hus h1 h2 h3)
      hUL (hWb hps)
  · obtain ⟨rfl, hm⟩ := hNP hps
    exact TermOverCrW.foreign_overCrNPOUV hsc X Y Z hm hps hOC hji hj hc2 hown hpf2 List.nodup_nil
      (fun g hg => by cases hg) (fun g hg => by cases hg) (fun g hg => by cases hg)
      (fun y hy => by simp [TermOverCrW.dnOf] at hy) (fun y hy => by simp [TermOverCrW.dnOf] at hy) X.inv.promAbove hUL

/-- **The amended `fgnCov`** from the named premises: OPEN `hWbR` (at `pub` stores) and the gap-2
support. -/
theorem fgnCov_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
    (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0)
    (hWb : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
      {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
      {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell},
      Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ
        Gd tg j thj Sj l cl → TermPiece.PubShape cx th →
      TermFreeQW.HWbRUp c c' Eg (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (crPl cr pl) j thj Sj l cl)
    (hSup : ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat}
      {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
      {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
      {Gd : List TermPiece.GdE} {tg : TermPiece.GdE → Option Ts} {j : Nat} {thj : TTh}
      {Sj : AllocLabel → Prop} {l : AllocLabel} {cl : Cell},
      Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ
        Gd tg j thj Sj l cl →
      SuppAll cr pl δ c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j thj Sj l cl) :
    fgnCov p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F crS cr' db' δ plh Gd tg
    X Y Z _ hOC hPT hDrop hδ hST j thj Sj l cl hji hj hc2 hown hpf2
  have hA : Ante p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db pl i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F
      cr' db' δ Gd tg j thj Sj l cl := ⟨X, Y, Z.toC _ _ _ (cr i) (db i), hOC, hPT, hDrop, hδ, hST, hji, hj, hc2, hown, hpf2⟩
  have hcv := cover_cv hsc hA (hWb hA)
  have hcv' : TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => crPl cr pl j t + δ t) l cl := by
    have e : (fun t => crPl cr pl j t + δ t) = (fun t => crPl cr pl j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) :=
      funext fun t => by rw [hδ t]
    rw [e]; exact hcv
  exact crN_cover hji hj hcv' (hSup hA)

end TermPoolFgnCov

#print axioms TermPoolFgnCov.crN_cover
#print axioms TermPoolFgnCov.fgnCov_of
#print axioms TermPoolFgnCov.cover_cv

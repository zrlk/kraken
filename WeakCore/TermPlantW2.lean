import WeakCore.TermPlantF
import WeakCore.TermPlantS
import WeakCore.TermW2Pub
import WeakCore.TermW2Prom
import WeakCore.TermW2New

/-!
# TermPlantW2: the W2 leaf `PlantInhWF` from `PlantPromOKF`

A newly planted slot lies in the held prefix (`PrefixHeld_NpZ`), so its first word carries
an outstanding promise of the promiser; `PlantPromOKF` types that promise's word at the
published planted environment, and the `WordOK` witness is a whole value of the slot type.
-/

namespace TermPlantW2

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (W2) **`PlantInhWF` from `PlantPromOKF`.** -/
theorem plantInhW_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hPO : PlantPromOKF p k arch Sp Init MintOK c0 plantOf plantN) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PlantInhWF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X j' Sj l f cl b S us hpl hcl0 hseg hus h1 hnot hini
  obtain ⟨hPL, -⟩ := plantOf_some X.hth hpl
  obtain ⟨lp, -, hRp⟩ := id hPL
  obtain ⟨clp, hclp, -, -, -, -, -, h4, -⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hRp
  rw [hcl0] at hclp; cases hclp
  have hcP : (cutP Eg j).sto l = some cl := by
    obtain ⟨-, -, t, -, m, -, -, -, a1, g, -, hal, cl1, hc1, -, -⟩ := hPL
    subst hal
    have e1 : cl1 = cl := by rw [cutSto_sub hc1] at hcl0; cases hcl0; rfl
    subst e1; exact hc1
  rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us2, jj, hT, hus2, -, rfl⟩
  · exact absurd (fun N e hT => by rw [hT] at hA; simp [accs] at hA) hnot
  rw [hus] at hus2; cases hus2
  have hpos : 0 < nWords us := by omega
  -- the slot is above the start count and below the planted one
  have hge : Eg.ini l ≤ jj := Nat.le_of_not_lt fun hlt =>
    hnot fun N' e' hT' => by
      rw [hT] at hT'
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨-, rfl⟩ := hT'
      exact ⟨us, jj, hus, hlt, rfl⟩
  have hjI : jj < max (Eg.ini l) (NpZ (cutP Eg j) (stOf c.mem c.pairs th) l) := by
    obtain ⟨us3, j3, hus3, hj3, e⟩ := hini N S hT
    rw [hus] at hus3; cases hus3
    have e3 : jj = j3 := Nat.eq_of_mul_eq_mul_right hpos e
    subst e3
    have hi : (Cut (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j' Sj).ini l =
        max (Eg.ini l) (NpZ (cutP Eg j) (stOf c.mem c.pairs th) l) := by
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini l = _
      simp only [plantG, hpl, plantN, X.hth]
    rw [hi] at hj3; exact hj3
  have hjN : jj < NpZ (cutP Eg j) (stOf c.mem c.pairs th) l := by
    rcases Nat.le_total (Eg.ini l) (NpZ (cutP Eg j) (stOf c.mem c.pairs th) l) with h | h
    · rw [Nat.max_eq_right h] at hjI; exact hjI
    · rw [Nat.max_eq_left h] at hjI; omega
  have hoN : jj * nWords us < NpZ (cutP Eg j) (stOf c.mem c.pairs th) l * nWords us :=
    Nat.mul_lt_mul_of_pos_right hjN hpos
  rcases PrefixHeld_NpZ hcP N S us hT hus (jj * nWords us) hoN with hI | ⟨u, hu, m, hm, hloc⟩
  · have := hI N S us hT hus
    have hlt : jj * nWords us < Eg.ini l * nWords us := this
    have := Nat.lt_of_mul_lt_mul_right hlt
    omega
  have hu' : u ∈ th.promises := hu
  have hm' : c.mem[u]? = some m := hm
  obtain ⟨-, hW⟩ := hPO X l f hpl u m hu' hm' (by rw [hloc]) cl hcl0
  have hW' := WordOK_transfer (TermPlantS.Incl_pub_cut _ j' Sj) h4 hW
  rw [hT, hloc] at hW'
  obtain ⟨ws0, -, hv, hl, -⟩ := TermPlantS.WordOK_slot (i := 0) (jj := jj) hus hpos (by simp) hW'
  exact ⟨ws0, hv, hl⟩

/-- **P4b `plantInh`** for `plantOf`/`plantN`, the multi-word slots by `plantInhW_of`
(no W2 leaf). -/
theorem plantInh_ofP (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0) (h0 : TermPlantF.PromViewLtR p k arch Sp c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0)
    (hPO : PlantPromOKF p k arch Sp Init MintOK c0 plantOf plantN) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PlantInhF p k arch Sp Init MintOK c0 plantOf plantN :=
  plantInh_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun h0 hagree hbp hbr (plantInhW_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun hPO)

/-- (W2) **`PromWordWF`, closed**: the slots initialised at `Eg.ini` by `W2Prom.promWordW_of`, the
newly planted ones by `W2New.promWordNew_of`. -/
theorem promWordW_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromWordWF p k arch Sp Init MintOK c0 :=
  W2Prom.promWordW_of (hV0 := hV0) hP hrun hagree hbp hbr (W2New.promWordNew_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun h0 hagree hbp hbr) hPS hSub hSig

/-- (W2) `PubWordWF`, closed (`W2Pub.pubWordW_of`). -/
theorem pubWordW_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrunT : CertRunT p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hagree : RunAgreeT p k arch Sp Init MintOK c0) (hbp : BufInitPubT p k arch Sp Init MintOK c0)
    (hbtr : BufInitPubTR p k arch Sp Init MintOK c0)
    (hclos : PubClosT p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PubWordWF p k arch Sp Init MintOK c0 :=
  W2Pub.pubWordW_of (hV0 := hV0) hP hrunT h0 hagree hbp hbtr hclos hPS hSub hSig

end

end TermPlantW2

#print axioms TermPlantW2.plantInhW_of
#print axioms TermPlantW2.plantInh_ofP
#print axioms TermPlantW2.promWordW_of
#print axioms TermPlantW2.pubWordW_of

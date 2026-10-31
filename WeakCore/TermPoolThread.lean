import WeakCore.TermPoolMainAux
import WeakCore.TermPoolStepTgt
import WeakCore.TermOverCrProm
import WeakCore.TermFulW
import WeakCore.TermOwnNF

/-!
# Pool route, thread step

`poolThread`: from the twelve pool members (`PoolStaging`), the step context, the stepper's outputs
and the pre-state pool `PoolInv … pl`, the post-state credits `cr2` and pool `pl2` (F1T's re-split of
`crN` at `δc`/`δh`) with the post-state `PoolInv`, `OwnFreshZ` at `cr2`, and the idle threads'
`PromCrK` transfer to `cr2`.  TermMain's `sysInv_thread` uses it in place of `balT_D`/`knetT_F`/
`ridT_N` and `hcsP`.
-/

namespace TermPoolThread
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermStepper TermPool TermOverCrBII TermBal TermOwnFresh TermPoolStaging
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

theorem pSumAt_key_le (c : Cfg) (n : Nat) {f g : Ts → Res} {key : Key} (h : ∀ t, f t key ≤ g t key) :
    pSumAt c n f key ≤ pSumAt c n g key := by
  unfold pSumAt
  cases c.ths[n]? with
  | none => exact Nat.le_refl _
  | some th =>
    show Res.sum ((stOf c.mem c.pairs th).promises.map f) key ≤ Res.sum ((stOf c.mem c.pairs th).promises.map g) key
    generalize (stOf c.mem c.pairs th).promises = l
    induction l with
    | nil => exact Nat.le_refl _
    | cons a l ih =>
      simp only [List.map_cons, Res.sum, Res.add_apply]
      exact Nat.add_le_add (h a) ih

theorem le_of_add_le_left {a b d : Res} (h : a + b ≤ d) (key : Key) : a key ≤ d key := by
  have := Res.le_def.1 h key
  simp only [Res.add_apply] at this
  omega

theorem updD_key_le (cr : Nat → Ts → Res) (i : Nat) (cr' dc δ : Ts → Res) (hle : ∀ t key, dc t key ≤ δ t key)
    (n : Nat) (t : Ts) (key : Key) : updD cr i cr' dc n t key ≤ updD cr i cr' δ n t key := by
  by_cases hn : n = i
  · subst hn; rw [updD_self, updD_self]; exact Nat.le_refl _
  · rw [updD_other _ _ _ hn, updD_other _ _ _ hn]
    simp only [Res.add_apply]
    exact Nat.add_le_add_left (hle t key) _

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
  {plantOf : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Option Ts}
  {plantN : Cfg → GEnv → Nat → Address → WeakMem.Val → Ts → AllocLabel → Nat}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (F1T `hNew`) The new foreign items after a step: at every owned, published, unpublished cell
of a foreign thread, re-pinned pre items and deposits at `dh` cover each post unit (`FgnNewC`). -/
def FgnNewAt (p : Prog) (k : Promises.Knobs) (arch : Arch) (c c' : Cfg) (Eg : GEnv) (pl : Nat → Ts → Res)
    (i : Nat) (th : TTh) (r : Memory × List Ts × TTh) (E' : TEnv) (dh : Ts → Res) : Prop :=
  ∀ (j : Nat) (thj thj' : TTh) (Sj : AllocLabel → Prop) (l : AllocLabel) (cl : Cell), j ≠ i →
      c.ths[j]? = some thj → c'.ths[j]? = some thj' →
      (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl → cl.owner = some j → (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none → ¬ (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pubd l →
      FgnNewC p k arch c c' Eg pl i th r E' dh j thj thj' Sj l cl

/-- (OPEN: `fgnNew_of`) **`FgnNewAt` at every thread step**, at `dh := δh`, from the step context, the
stepper's output at `crS`, the pre-state pool and the drop list's targets.  A named gap of
`poolThread`/`sysInv_thread`: never a final premise. -/
def FgnNewT (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) : Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' C F : Res} {crS cr' db' δ : Ts → Res} {Gd : List TermPiece.GdE},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ → StepCrQ cr pl i r.2.2.promises crS →
    PoolInv Init MintOK c Eg Tot HP HS cr db pl → TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd →
    (∀ t, δ t = TermPlant.plantD1 Gd TermPiece.GdE.R (TermPlant.tgIn η.fp (TermHtgW1.Pδ0 c c' Eg i th)) t) →
    StepTgt p k arch c c' Eg i th r η cx E' Gd (TermPlant.tgIn η.fp (TermHtgW1.Pδ0 c c' Eg i th)) →
    FgnNewAt p k arch c c' Eg pl i th r E' (δh δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i)

/-- **The pool route at a thread step.** -/
theorem poolThread (PS : PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    (hMC : MintClosedT p k arch Sp Init MintOK c0) (hPN : PromNodupR p k arch Sp c0)
    (hAG : AllocGT p k arch Sp Init MintOK c0) (hTF : TicketFreeRun p k arch Sp c0)
    (hsc : TermInterf.StepScopeF p k arch Sp Init MintOK c0)
    {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {i : Nat} {th : TTh}
    {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx} {Rf Rs : Res}
    {E' : TEnv} {Tot' HP' HS' H' C F : Res} {crS cr' db' δ plh : Ts → Res} {Gd : List TermPiece.GdE} {rc : Nat → Nat}
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) th r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      crS (db i) δ) (hQ : StepCrQ cr pl i r.2.2.promises crS)
    (hδ : ∀ t, δ t = TermPlant.plantD1 Gd TermPiece.GdE.R (TermPlant.tgIn η.fp (TermHtgW1.Pδ0 c c' Eg i th)) t)
    (hPI : PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (hrc : RidOK c Tot HP HS (crPl cr pl) db rc) (hle : rc i ≤ η.rid)
    -- the stepper's outputs
    (hpa : PromAbove (stOf r.1 r.2.1 r.2.2)) (hBi : TermPlant.BiOut th E')
    (hSK : TermPlant.KeepQRSB (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) th crS cr' plh)
    (hIF : IniFixZ { gOf p k arch c i with zf := fun l => (CE η).pfr l ≠ none ∧ (CE η).ini l ≤ (CE η).rini l }
      (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hOF : TermPlant.OwnFrOp (CE η) cx th → r.1 = c.mem)
    (hF : EFoot (gOf p k arch c i) (CE η) E' (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2))
    (hSeen : SeenOK (CE η) E' Tot' H') (hRE : ThInvRE p E' r.2.2 Tot')
    (hm' : MemInv (gOf p k arch c i) E' (stOf r.1 r.2.1 r.2.2)) (hH' : MemHeld E' (stOf r.1 r.2.1 r.2.2) H')
    (hC' : TermPlant.PromCrK E' (stOf r.1 r.2.1 r.2.2) cr' db')
    (hMS : MintStep (gOf p k arch c i) η (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) C F)
    (hDr : TermPiece.Drop (CE η) (stOf c.mem c.pairs th) Gd)
    (hineq : Tot' + H' + pSum (stOf r.1 r.2.1 r.2.2) cr' + pSum (stOf c.mem c.pairs th) (db i) + C +
        Res.sum (Gd.map TermPiece.GdE.R) + pSum (stOf r.1 r.2.1 r.2.2) plh ≤
      Rf + Rs + (HP i + HS) + pSum (stOf c.mem c.pairs th) crS + pSum (stOf r.1 r.2.1 r.2.2) db' + F)
    (hHs : H' = HP' + HS')
    (hFs : ∀ t, δ t ≠ .zero → t ∈ TermPlant.nodupL η.fp)
    (hFd : Res.sum ((TermPlant.nodupL η.fp).map δ) ≤ Res.sum (Gd.map TermPiece.GdE.R))
    (hplM : ∀ t, plh t ≠ .zero → t ∈ r.2.2.promises) (hplK : ∀ t, TermPlant.CrKeys (plh t))
    (hPfr : PfrG { gOf p k arch c i with pf := fun l => TermOwnG0Defs.PubAt th l } (CE η) E')
    (hGc : TermPiece.PubShape cx th →
      TermPiece.GdCovT (CE η) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) Gd th)
    (hNP : ¬ TermPiece.PubShape cx th → Gd = [])
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hcl : ClaimAt th.term C F)
    (hOF' : OwnFreshZ c' (upd Tot i Tot') (upd HP i HP') HS' (updD cr i cr' δ))
    (hFN : FgnNewT p k arch Sp Init MintOK c0) :
    ∃ cr2 pl2 : Nat → Ts → Res, cr2 i = cr' ∧
      PoolInv Init MintOK c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') (upd Tot i Tot')
        (upd HP i HP') HS' cr2 (upd db i db') pl2 ∧
      OwnFreshZ c' (upd Tot i Tot') (upd HP i HP') HS' cr2 ∧
      (∀ n t l, cr2 n t (.own l) ≤ updD cr i cr' δ n t (.own l)) ∧
      ∀ j thj (Sj : AllocLabel → Prop), j ≠ i → c'.ths[j]? = some thj →
        TermPlant.PromCrK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
            (stOf c'.mem c'.pairs thj)
            (fun t => cr j t + δc δ cr c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i t) (db j) →
          TermPlant.PromCrK (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
            (stOf c'.mem c'.pairs thj) (cr2 j) (db j) := by
  have hsp := δc_add_δh_le δ cr pl c c' (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') i
  have hIq : IneqH Tot' HP' HS' C F Rf Rs (HP i + HS) (stOf c.mem c.pairs th) (stOf r.1 r.2.1 r.2.2) crS cr'
      (db i) db' plh δ := by
    refine ⟨TermPlant.nodupL η.fp, hFs, ?_⟩
    rw [← hHs]
    exact Res.le_def.2 fun key => by
      have h1 := Res.le_def.1 hineq key
      have h2 := Res.le_def.1 hFd key
      simp only [Res.add_apply] at h1 h2 ⊢
      omega
  have hST := TermPoolStepTgt.stepTgt_supply X Y (Z.toC _ _ _ (cr i) (db i)) hDr hGc hNP hm
  obtain ⟨cr2, pl2, hcr2, hpl2, hN, hT2, hK2, hP2, hCov2⟩ := PS.hF1T (plh := plh) X Y Z hQ hPI.cov hPI.tag hsp
    (crShiftP_δc δ cr c c' _ i) (δh_tag δ cr pl c c' _ i) (hFN X Y Z hQ hPI hDr hδ hST)
  have hOT := PS.hPoolTagOwnT X Y Z hQ hPI.cov hPI.tag (TermPlant.keepQRS_of_B hSK)
    (TermFulW.tctx_wpd hsc X Y hm hpa)
    (fun Sj l o tw a b d e f => TermOwnNF.nf_of X Y (Z.toC _ _ _ (cr i) (db i)) _ l o tw a b d e f)
  have hLe2 : ∀ n t l, cr2 n t (.own l) ≤ updD cr i cr' δ n t (.own l) := fun n t l => by
    rw [hK2 n t]
    exact updD_key_le cr i cr' _ δ (fun t key => le_of_add_le_left (hsp t) key) n t _
  refine ⟨cr2, pl2, hcr2, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, hLe2, hP2⟩
  · -- tags
    refine poolTag_iff.2 ⟨fun j thj t hj h0 => ?_, fun j thj Sj hj l cl hsto hown hpf hnp => ?_⟩
    · by_cases hji : j = i
      · subst hji
        have e : thj = r.2.2 := by rw [X.e3] at hj; exact (Option.some.inj hj).symm
        subst e
        rw [hpl2] at h0 ⊢
        exact hOT.1 t h0
      · exact hT2 j thj t hji hj h0
    · by_cases hji : j = i
      · subst hji
        have e : thj = r.2.2 := by rw [X.e3] at hj; exact (Option.some.inj hj).symm
        subst e
        rw [hpl2]
        exact hOT.2 Sj l cl hsto hown hpf hnp
      · exact hCov2 j thj Sj hji hj l cl hsto hown hpf hnp
  · -- cover
    rw [hN]
    intro j thj Sj hj l cl hsto hown hpf
    by_cases hji : j = i
    · subst hji
      have e : thj = r.2.2 := by rw [X.e3] at hj; exact (Option.some.inj hj).symm
      subst e
      have ec : crN cr pl j cr' (stOf r.1 r.2.1 r.2.2) plh
          (δc δ cr c c' (EgT Eg (gOf p k arch c j) th.nalloc r.2.2.nalloc E' c') j)
          (δh δ cr pl c c' (EgT Eg (gOf p k arch c j) th.nalloc r.2.2.nalloc E' c') j) j =
          fun t => cr' t + plStep pl j (stOf r.1 r.2.1 r.2.2) plh t := by
        funext t; simp only [crN, crPl, updD_self]
      rw [ec]
      exact openOverCrOwn_of PS.hOwnA PS.hOwnC pl X Y trivial hpa hPI.cov hPI.tag crS hQ Tot' H' C F cr' db' plh Gd E'
        hBi hSK hIF hOF hF hSeen hRE hm' hH' hC' hMS hDr hineq hplM hplK hPfr Sj l cl hsto hown hpf
    · have hj' : c.ths[j]? = some thj := by rw [← X.ho j hji]; exact hj
      exact PS.hFgnCov X Y Z hQ hPI.cov hPI.tag hDr hδ hST j thj Sj l cl hji hj' hsto hown hpf
  · -- balance
    rw [hN]
    exact PS.hPoolBalT hMC hPN X Y Z hQ hsp hPI hplM hIq
  · -- net keys
    rw [hN]
    exact PS.hPoolKnetT hAG hTF hPN X Y Z hQ hsp hPI hplM hplK (TermPoolMainAux.crKeys_dh δ cr pl c c' _ i X.ho)
      hIq hcl X.inv.ownF hrc hle
  · -- rid
    rw [hN]
    exact PS.hPoolRidT hTF hPN X Y Z hQ hsp hPI hplM hIq hcl hrc hle
  · -- own freshness at `cr2`
    intro q thq jj hq hjj
    obtain ⟨h1, h2⟩ := hOF' q thq jj hq hjj
    refine ⟨fun n hn => ?_, h2⟩
    have h3 := h1 n hn
    have h4 := pSumAt_key_le c' n (f := cr2 n) (g := updD cr i cr' δ n)
      (key := .own (freshLabel c'.lbase c'.n q jj)) fun t => hLe2 n t _
    simp only [Res.add_apply] at h3 ⊢
    omega

theorem ne_zero_of_key_le {a b : Res} (hle : ∀ key, a key ≤ b key) (h : a ≠ .zero) : b ≠ .zero := fun hb =>
  h (Res.ext fun key => by have := hle key; rw [hb] at this; simp only [Res.zero_apply] at this ⊢; omega)

theorem sum_key_le (l : List Ts) {f g : Ts → Res} {key : Key} (h : ∀ t, f t key ≤ g t key) :
    Res.sum (l.map f) key ≤ Res.sum (l.map g) key := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, Res.sum, Res.add_apply]
    exact Nat.add_le_add (h a) ih

/-- A step output stays one at a smaller transfer. -/
theorem TOut_mono {p : Prog} {g : G} {η : TEnv} {s : St} {th : TTh} {r : Memory × List Ts × TTh} {E' : TEnv}
    {Tot' HP' HS' C F : Res} {cr' db' : Ts → Res} {Rf Rs H : Res} {cr db δ δ' : Ts → Res}
    (Z : TOut p g η s th r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ) (hle : ∀ t key, δ' t key ≤ δ t key) :
    TOut p g η s th r E' Tot' HP' HS' C F cr' db' Rf Rs H cr db δ' := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ⟨s1, s2⟩, Fd, hFd, hin, a12⟩ := Z
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ⟨fun t h => s1 t (ne_zero_of_key_le (hle t) h),
    fun t h => s2 t (ne_zero_of_key_le (hle t) h)⟩, Fd, fun t h => hFd t (ne_zero_of_key_le (hle t) h), ?_, a12⟩
  exact Res.le_def.2 fun key => by
    have h1 := Res.le_def.1 hin key
    have h2 := sum_key_le Fd (f := δ') (g := δ) (key := key) fun t => hle t key
    simp only [Res.add_apply] at h1 ⊢
    omega

/-- `δc` is below the transfer, keywise. -/
theorem δc_key_le (δ : Ts → Res) (cr pl : Nat → Ts → Res) (c c' : Cfg) (Eg' : GEnv) (i : Nat) :
    ∀ t key, δc δ cr c c' Eg' i t key ≤ δ t key := fun t key =>
  le_of_add_le_left (δc_add_δh_le δ cr pl c c' Eg' i t) key

/-- The `SysInvN.pool` body as a `PoolInv`. -/
theorem poolInv_of {Init : Res} {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db : Nat → Ts → Res}
    (h : ∃ pl : Nat → Ts → Res, PoolTag Eg c pl ∧ TermOverCr.OverCrG Eg c (crPl cr pl) ∧
      (∃ M, MintOK M ∧ thSum c.ths.size (fun i => Tot i + pSumAt c i (crPl cr pl i) + HP i) + HS ≤
        Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))) ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS (crPl cr pl) db key) ∧
      (∃ rc, RidOK c Tot HP HS (crPl cr pl) db rc)) :
    ∃ pl, PoolInv Init MintOK c Eg Tot HP HS cr db pl :=
  let ⟨pl, a, b, d, e, f⟩ := h; ⟨pl, ⟨a, b, d, e, f⟩⟩

/-- A `PoolInv` as the `SysInvN.pool` body. -/
theorem field_of_poolInv {Init : Res} {MintOK : Res → Prop} {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res}
    {cr db pl : Nat → Ts → Res} (h : PoolInv Init MintOK c Eg Tot HP HS cr db pl) :
    ∃ pl : Nat → Ts → Res, PoolTag Eg c pl ∧ TermOverCr.OverCrG Eg c (crPl cr pl) ∧
      (∃ M, MintOK M ∧ thSum c.ths.size (fun i => Tot i + pSumAt c i (crPl cr pl i) + HP i) + HS ≤
        Init + M + thSum c.ths.size (fun i => pSumAt c i (db i))) ∧
      (∀ key, ExclKey key → KeyNet c Tot HP HS (crPl cr pl) db key) ∧
      (∃ rc, RidOK c Tot HP HS (crPl cr pl) db rc) :=
  ⟨pl, h.tag, h.cov, h.bal, h.knet, h.rid⟩

/-- **The pool route at a promise step**: the pool is unchanged, the promiser's credits are `cr'`. -/
theorem poolProm (PS : PoolStaging p k arch Sp Init MintOK c0 plantOf plantN)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db pl : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} {HP' HS' : Res} {cr' db' : Ts → Res}
    (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    (hspec : PlantSpec Eg (plantOf c Eg j a v w) j c.mem.size)
    (hPI : PoolInv Init MintOK c Eg Tot HP HS cr db pl)
    (hacct : PAcct (stOf c.mem c.pairs th) a v w (HP j + HS) (HP' + HS') (cr j) (db j) cr' db')
    (hS : ThSys p (gOf p k arch c j) (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)
      (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) (Tot j) HP' HS' cr' db')
    (hcr : ∀ t m, t ∈ th.promises → c.mem[t]? = some m → ∀ S : AllocLabel → Prop,
      ¬ WordUnit (Cut Eg j S) m.loc → cr' t = cr j t) :
    PoolInv Init MintOK (promise c j a v w) (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)
      Tot (upd HP j HP') HS' (upd cr j cr') (upd db j db') pl :=
  ⟨PS.hPoolTagP X hspec hPI.tag,
    TermOverCrProm.openOverCrProm_holds pl X hspec hPI.cov hPI.tag HP' HS' cr' db' hacct hcr hS,
    PS.hPoolBalP X hacct hPI, PS.hPoolKnetP X hacct hPI, PS.hPoolRidP X hacct hPI⟩

end

end TermPoolThread

#print axioms TermPoolThread.poolThread
#print axioms TermPoolThread.poolProm

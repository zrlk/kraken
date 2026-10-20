import WeakCore.TermOwnCFul
import WeakCore.TermOwnCH
import WeakCore.TermReadCls
import WeakCore.TermPredRd
import WeakCore.TermNewCoh

/-! # TermOwnCRead: case C of the post-demand trichotomy, the read cover (ownC)

`caseC_of : CaseCCov` from the `ReadClsF` and the open `PredRdF` (below).

A demanded unit `a = ⟨l, o⟩` whose coherence the step raises to an old message `K′` that is no own
promise: `ReadClsF` gives a non-affine piece at `a`; the unit is one word (`PromNoTwoOK` at the
lowest own promise `tw`); `freeQW_exists` pinned at the coherence message (`predAt_coh` under `WinG`),
which is typed:
* at `InitRr E′` units by the owner's invariant afterwards (`OwnOKSF`, `TermOwnCPin.pin_of_winG`);
* at `PredU E′` units by `MemOKP` afterwards, given that `K′`'s message is not `undef` (`PredRdF`).

`PredRdF` is open.  `OwnHidP` part 2 at `E′` gives only: `K′`'s word typed, or a message at `a` in
`(K′, f]` (`f` the frontier); under `WinG` that message is an own promise `≥ tw`, so `tw` is the
first write at `a` and `tw ≤ f`, which no invariant clause excludes.  (A `pub` read of the predicted
unit reads at a bound `≥ f`, hence skips `K′`; that is the read's typing, the side.)
-/

namespace TermOwnCRead

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermStep TermCut TermSys
open TermStepper TermMain TermInterf TermPool TermOverCrBII
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- (open) **A read at a predicted own unit does not land on a placeholder**: if the
stepper's coherence at a predicted unit of one of its own cells rises to an old message that is no
own promise (a read), that message is not `undef`. -/
def PredRdF (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (Init : Res) (MintOK : Res → Prop) (c0 : Cfg) :
    Prop :=
  ∀ {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {i : Nat}
    {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv} {cx : Cx}
    {Rf Rs : Res},
    TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r → EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs →
    PromAbove (stOf r.1 r.2.1 r.2.2) →
    ∀ (b : Address) (cl : Cell), (CE η).sto b.label = some cl → cl.owner = some i → PredU (CE η) b →
      (∀ q, TwoAtT cl.ty q → b.offset ≠ q ∧ b.offset ≠ q + 1) →
      th.vs.coh b < r.2.2.vs.coh b → r.2.2.vs.coh b < c.mem.size → r.2.2.vs.coh b ∉ th.promises →
      ∀ m, c.mem[r.2.2.vs.coh b]? = some m → m.val ≠ .undef

/-- A word inside a piece of an initialised unit has a cell value. -/
theorem vals_at {E : TEnv} {n : Nat} {T U : Ty} {vals : List Word} {q o : Nat} {us : List Acc}
    (hc : CellOK E n T vals) (hat : AtOff T q U) (hU : accs U = some us) (hq : q ≤ o)
    (ho : o < q + nWords us) : ∃ v, vals[o]? = some v := by
  have hlen : o < vals.length := by
    rcases hc with ⟨hwc, -⟩ | ⟨N', e', us', hT', hus', -, hlen, -⟩
    · obtain ⟨L, hL1, hL2⟩ := wc_some hwc
      have hb := AtOff_bound hat hL1 hU
      omega
    · have hj : o - q < nWords us := Nat.sub_lt_left_of_lt_add hq ho
      have h := TermSeenHid.off_lt_buf (j := o - q) hat hT' hus' hU hj
      have e2 : q + (o - q) = o := by omega
      rw [e2] at h
      rw [hlen]
      exact h
  exact ⟨_, List.getElem?_eq_getElem hlen⟩

#print axioms vals_at

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- **Case C** (`CaseCCov`). -/
theorem caseC_of (hRd : TermReadCls.ReadClsFE p k arch Sp Init MintOK c0)
    (hPR : PredRdF p k arch Sp Init MintOK c0) :
    TermOwnCTop.CaseCCov p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs X Y hPA E' hF hMI l cl hold ho hpf0 hs1 hpe o tw hPD
    hgt hlt hKn0
  -- the unit is no word unit
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 (show E'.pfr l ≠ none by rw [hpe]; exact hpf0)
  have hnwE' : ¬ WordUnit E' ⟨l, o⟩ := fun h => hPD.2.1 ⟨h, Vis_pfr hf⟩
  have hstoL : E'.sto l = (CE η).sto l := hs1.trans hold.symm
  have hnw : ¬ WordUnit (CE η) ⟨l, o⟩ := fun h => hnwE' ((WordUnit_congr (a := ⟨l, o⟩) hstoL).2 h)
  have hsG : Eg.sto l = some cl := by
    have h1 := hold
    rw [Y.1] at h1
    exact cutSto_sub h1
  have hclo : tb 0 cl.ty = true := (X.inv.clo l cl hsG).1
  -- the step's state facts
  obtain ⟨S0, ρ0, η0, cx0, Rf0, Rs0, hCE0, -, -, -, -, -, -, -, hm0, -, -⟩ := (X.inv.thr i th X.hth).env X.inv.clo
  have hsub : ∀ t, t ∈ r.2.2.promises → t ∈ th.promises :=
    fun t ht => (TermFul.tstep_fulfil (fun t ht => X.inv.plt i th t X.hth ht) (MemInv_nopair hm0) X.hr).1.subset ht
  have hback : ∀ t m, t ∈ th.promises → r.1[t]? = some m → c.mem[t]? = some m := by
    intro t m ht hm
    have hlt' : t < c.mem.size := X.inv.plt i th t X.hth ht
    have h := Array.getElem?_eq_getElem hlt'
    have h2 := (TermFul.tstep_grow X.hr).1 _ _ h
    rw [h]
    exact congrArg some (Option.some.inj (h2.symm.trans hm))
  -- the owner's invariant afterwards
  have hown' : cl.owner = some E'.tid := by
    rw [hF.2.1]
    show cl.owner = some η.tid
    rw [Y.2.1]
    exact ho
  obtain ⟨vals, hc, hL, -⟩ := hMI.2.1 l cl hs1 hown'
  have hlay : LayT cl.ty := LayT_of_CellOK hc
  -- the unit is one word (`PromNoTwoOK` at `tw`)
  have hlo := hPD.2.2.1
  obtain ⟨htw, ⟨mt, hmt, hmtl⟩, -⟩ := id hlo
  have htw0 := hsub tw htw
  have hmt0 := hback tw mt htw0 hmt
  have hno : ∀ q', TwoAtT cl.ty q' → o ≠ q' ∧ o ≠ q' + 1 := by
    intro q' h2
    have h := X.inv.promNoTwo i th tw mt cl X.hth htw0 hmt0 (by rw [hmtl]; exact hsG) q' h2
    rw [hmtl] at h
    exact h
  -- no epoch-pair unit (its words are a two-word unit)
  have hne : ¬ TermReadCls.EPairUnit (CE η) ⟨l, o⟩ := fun he => by
    obtain ⟨q', h2, h3⟩ := TermReadCls.epairUnit_twoAtT he hold hlay
    rcases h3 with h3 | h3
    · exact (hno q' h2).1 h3
    · exact (hno q' h2).2 h3
  -- the read's piece
  obtain ⟨q, U, us, hP, hU, hq0, hqo0, ha⟩ := hRd X Y hPA ⟨l, o⟩ cl hold ho hpf0 hnw hne hgt hlt hKn0
  have hq : q ≤ o := hq0
  have hqo : o < q + nWords us := hqo0
  have eo : q + (o - q) = o := by omega
  have hsing : ∀ i o2, InAcc us i (o - q) → InAcc us i o2 → o2 = o - q := fun i o2 hi h2 =>
    TermOverCrW.inAcc_single hP.1 hU hi (TermOwnCH.layT_shape hlay) (by rw [eo]; exact hno) o2 h2
  -- the typed pin
  have key : ∃ w, (∀ tw', TermPlant.LowOwn (stOf r.1 r.2.1 r.2.2) ⟨l, o⟩ tw' →
      PredAt (stOf r.1 r.2.1 r.2.2).mem ⟨l, o⟩ tw' w) ∧ WordOK E' cl.ty o w := by
    rcases hPD.1 with hI | hPU
    · obtain ⟨v, hv⟩ := vals_at hc hP.1 hU hq hqo
      exact TermOwnCPin.pin_of_winG hlo hPA hPD.2.2.2.1 hc hI hv (hL o v hv)
    · -- the coherence message (`CohAt` afterwards)
      obtain ⟨m', hm', hml'⟩ := TermRiseLoc.tstep_riseLoc X.hr hgt
      have hm'r : r.1[r.2.2.vs.coh ⟨l, o⟩]? = some m' := hm'
      have hcm' : c.mem[r.2.2.vs.coh ⟨l, o⟩]? = some m' := by
        have h := Array.getElem?_eq_getElem hlt
        have h2 := (TermFul.tstep_grow X.hr).1 _ _ h
        rw [h]
        exact congrArg some (Option.some.inj (h2.symm.trans hm'r))
      -- the unit is predicted before the step
      have hpi := TermOverCr5D.hpi_of_promIni (S := S) X.inv.promIni X.hth
      rw [← Y.1] at hpi
      have hI := hpi tw mt htw0 hmt0 cl (by rw [hmtl]; exact hold) (by rw [hmtl]; exact hpf0)
      rw [hmtl] at hI
      have hIW : IniW (CE η) ⟨l, o⟩ := by
        intro c1 N e us1 h1 h2 h3
        have h1' : (CE η).sto l = some c1 := h1
        rw [hold] at h1'
        cases h1'
        exact hI N e us1 h2 h3
      have hrc : (CE η).rc l ≤ E'.rc l := by
        have h1 := (hF.2.2.2.2.1 l).1
        have h2 := hF.2.2.2.2.2.2.2.2.2.1 l
        unfold TEnv.rc
        omega
      have hnIWr : ¬ IniWr (CE η) ⟨l, o⟩ := fun hw => hPU.2.2 fun c1 N e us1 h1 h2 h3 => by
        have h1' : (CE η).sto l = some c1 := by rw [← hstoL]; exact h1
        exact Nat.lt_of_lt_of_le (hw c1 N e us1 h1' h2 h3) (Nat.mul_le_mul_right _ hrc)
      have hnu := hPR X Y hPA ⟨l, o⟩ cl hold ho ⟨hpf0, hIW, hnIWr⟩ hno hgt hlt hKn0 m' hcm'
      have hKn' : r.2.2.vs.coh ⟨l, o⟩ ∉ r.2.2.promises := fun h => hKn0 (hsub _ h)
      have hok : WordOK E' cl.ty o (mw m') := by
        rcases hMI.1.1 _ m' cl hKn' hm' (by rw [hml']; exact hs1) with hu | hw
        · exact absurd hu hnu
        · have hoff : m'.loc.offset = o := by rw [hml']
          rw [hoff] at hw
          exact hw
      exact ⟨mw m', TermOwnCPin.predAt_coh hlo (TermOwnCPin.coh_lt_of_promAbove hPA hlo) hm' hml' hPD.2.2.2.1,
        hok⟩
  obtain ⟨w, hpin, hok⟩ := key
  obtain ⟨x, hx⟩ := TermFreeQW.freeQW_exists hs1 hlo hP hU hq hqo hsing (TermOwnCLoad.atOff_tb hP.1 hclo) ha
    hnwE' hpin hok
  exact ⟨x, TermOwnCOld.zeroIt_of_freeQW hx⟩

#print axioms caseC_of

/-- **The ownC member** from `StepScopeF` and `NewCohF`; `ReadClsFE` and `PredRdF` are
`TermReadCls.tctx_readCls` and `TermPredRd.tctx_predRd` (its `PredRdFE` is `PredRdF` verbatim). -/
theorem openOverCrOwnC_of2 (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (hNC : TermReadClsDefs.NewCohF p k arch Sp Init MintOK c0) :
    OpenOverCrOwnC p k arch Sp Init MintOK c0 :=
  TermOwnCTop.openOverCrOwnC_of hsc hNC (TermOwnCFul.caseB_of hsc)
    (caseC_of (TermReadCls.tctx_readCls hsc) (TermPredRd.tctx_predRd hsc))

#print axioms openOverCrOwnC_of2

end

end TermOwnCRead

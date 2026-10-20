import WeakCore.TermOverCrG
import WeakCore.TermOverCrC

/-!
# TermOverCrNP: the credited cover at a non-`PubShape` foreign step (Cfg layer, F3 R=0)

Along thread `i`'s step that is not a `pub` store at a non-word reference, every unit of an
idle thread `j`'s own frontier cell newly written by the step (a new message or a lost
footprint promise) is a word unit or an RMW atom (the `tctx_forWU`).  At a non-visible unit
it is an RMW atom, not in an epoch pair (`PromNoTwoOK`, `epair_twoAtT`), so a free atom (`FreeAt`) once its lowest own promise has a
non-`undef` predecessor (typed by `j`'s `MemOKP` and moved between cuts by `WordOK_cut`).  The
free items `freeL` then cover it (`hent_free`, `foreign_overCrPZ`).  At a predicted unit of an
unpublished cell the lowest own promise is the first write (`PredHoldG`), pinned at its own word
(typed by `PromTyAOK`); at an initialised unit
the predecessor is defined (`predNU_of_promAbove`, from `PromAboveG` and the owner's `OwnOKSF`);
at a predicted, not initialised unit with no defined message below
the lowest own promise, that promise is the first write (pinned at its own word); only such a unit
of a published cell with a defined message below is left.  That (`hpredNU`, narrowed)
and the window transport (`hWb`) stay explicit OPEN premises.
-/

namespace TermOverCrW
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
  TermInterf TermStepper
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- RMW atoms read only the cell. -/
theorem rmwAtom_congr {E E2 : TEnv} {a : Address} (h : E2.sto a.label = E.sto a.label)
    (hR : TermForWU.RmwAtom E a) : TermForWU.RmwAtom E2 a := by
  obtain ⟨c, o, S, us, hs, rest⟩ := hR
  exact ⟨c, o, S, us, h.trans hs, rest⟩

#print axioms rmwAtom_congr

/-- **An RMW atom is a free leaf or in an epoch pair.** -/
theorem rmw_leaf {E : TEnv} {l : AllocLabel} {o : Nat} {c : Cell}
    (hR : TermForWU.RmwAtom E ⟨l, o⟩) (hsto : E.sto l = some c) :
    (∃ U, AtOff c.ty o U ∧ Solid U ∧ accs U = some [Acc.one] ∧ tb 0 U = true ∧ Ty.affine U = false) ∨
    ∃ o' n P, AtOff c.ty o' (.epair (.lit n) P) ∧ o' ≤ o ∧ o < o' + 2 := by
  obtain ⟨c0, o0, S, us, hs0, hat, hus, h1, h2, hk⟩ := hR
  have hs1 : E.sto l = some c0 := hs0
  rw [hsto] at hs1
  cases hs1
  have h1' : o0 ≤ o := h1
  have h2' : o < o0 + nWords us := h2
  rcases hk with rfl | ⟨hU, hsol, hcl, haf⟩ | ⟨n, P, rfl⟩
  · have e : us = [Acc.one] := by simp [accs] at hus; exact hus.symm
    subst e
    have ho : o = o0 := by
      rw [TermForWU.nWords_one] at h2'; exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2') h1'
    rw [← ho] at hat
    exact .inl ⟨.int, hat, solid_int, rfl, rfl, rfl⟩
  · rw [hU] at hus
    cases hus
    have ho : o = o0 := by
      rw [TermForWU.nWords_one] at h2'; exact Nat.le_antisymm (Nat.lt_succ_iff.mp h2') h1'
    rw [← ho] at hat
    exact .inl ⟨S, hat, hsol, hU, hcl, haf⟩
  · refine .inr ⟨o0, n, P, hat, h1', ?_⟩
    have e : us = [Acc.two] := by simp [accs] at hus; exact hus.symm
    subst e
    rw [TermForWU.nWords_two] at h2'
    exact h2'

#print axioms rmw_leaf

/-- **A footprint promise an idle thread loses at a step of `q` was `q`'s, and `q` fulfilled
it** (`PromsOK` before and after). -/
theorem lostFp_stepper {Eg Eg2 : GEnv} {c c' : Cfg} {i q : Nat} {thi thq thq2 : TTh}
    (hP : PromsOK Eg c) (hP' : PromsOK Eg2 c')
    (hi : c.ths[i]? = some thi) (hiq : i ≠ q) (hq' : c'.ths[q]? = some thq2)
    (ho : ∀ j0, j0 ≠ q → c'.ths[j0]? = c.ths[j0]?) (hq : c.ths[q]? = some thq) {t : Ts}
    (hf : t ∈ Eg.fpOf i) (hf' : t ∉ Eg2.fpOf i) (hnp : t ∉ thi.promises) :
    t ∈ thq.promises ∧ t ∉ thq2.promises := by
  have hi' : c'.ths[i]? = some thi := by rw [ho i hiq]; exact hi
  have hall : t ∈ allProms c := (hP i thi hi t).1 (List.mem_append_right _ hf)
  have hnall : t ∉ allProms c' := fun h => by
    rcases List.mem_append.1 ((hP' i thi hi' t).2 h) with h1 | h1
    · exact hnp h1
    · exact hf' h1
  obtain ⟨j0, th0, hj0, ht0⟩ := TermStepper.mem_allProms.1 hall
  by_cases hjq : j0 = q
  · subst hjq
    rw [hq] at hj0
    cases hj0
    exact ⟨ht0, fun h => hnall (TermStepper.mem_allProms.2 ⟨j0, thq2, hq', h⟩)⟩
  · exact absurd (TermStepper.mem_allProms.2 ⟨j0, th0, by rw [ho j0 hjq]; exact hj0, ht0⟩) hnall

#print axioms lostFp_stepper

/-- **An epoch pair starts a two-word unit of its cell** (laid-out cell type). -/
theorem epair_twoAtT {T : Ty} {o : Nat} {n : Nat} {P : ECounter} (hlay : LayT T)
    (hat : AtOff T o (.epair (.lit n) P)) : TwoAtT T o := by
  obtain ⟨sb, S0, b0, hseg, hat0, hsb⟩ := seg_of_atOff hlay hat
    ⟨(fun _ _ h => by cases h), (fun _ _ h => by cases h), (fun _ h => by cases h)⟩
  have hL : ∃ L, accs S0 = some L := by
    rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us, jj, -, hus, -, -⟩
    · exact Option.ne_none_iff_exists'.1 hA
    · exact ⟨us, hus⟩
  obtain ⟨L, hL⟩ := hL
  obtain ⟨pre, post, e, hpre⟩ := AtOff_embed hat0 hL (show accs (Ty.epair (.lit n) P) = some [.two] from rfl)
  have htw : TwoAt L b0 := by
    refine ⟨pre.length, ?_, ?_⟩
    · rw [e]; simp
    · rw [e, ← hpre]; simp
  exact ⟨sb, S0, L, b0, hseg, hL, htw, hsb.symm⟩

#print axioms epair_twoAtT

/-- **No own promise on a wide unit** (`PromNoTwoOK`): neither word of a two-word unit of a component
(e.g. a piece) of a laid-out cell carries an outstanding promise, so no `LowOwn` there. -/
theorem noLowOwn_two {Eg : GEnv} {c : Cfg} {j : Nat} {thj : TTh} {l : AllocLabel} {cl : Cell}
    {b jj : Nat} {S : Ty} {us : List Acc} (hNT : PromNoTwoOK Eg c) (hj : c.ths[j]? = some thj)
    (hs : Eg.sto l = some cl) (hlay : LayT cl.ty) (hat : AtOff cl.ty b S)
    (hus : accs S = some us) (htw : TwoAt us jj) (tw : Ts) :
    ¬ TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, b + jj⟩ tw ∧
      ¬ TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, b + jj + 1⟩ tw := by
  have hT0 : (∃ L, accs cl.ty = some L) ∨ ∃ N e, cl.ty = .array (.lit N) e := by
    rcases hlay with hA | ⟨N, e, he, -⟩
    · exact Or.inl (Option.ne_none_iff_exists'.1 hA)
    · exact Or.inr ⟨N, e, he⟩
  have hT := twoAtT_of_comp hat hus htw hT0
  refine ⟨fun hlo => ?_, fun hlo => ?_⟩
  · obtain ⟨ht, ⟨m, hm, hml⟩, -⟩ := hlo
    have h := hNT j thj tw m cl hj ht hm (by rw [hml]; exact hs) _ hT
    rw [hml] at h
    exact h.1 rfl
  · obtain ⟨ht, ⟨m, hm, hml⟩, -⟩ := hlo
    have h := hNT j thj tw m cl hj ht hm (by rw [hml]; exact hs) _ hT
    rw [hml] at h
    exact h.2 rfl

#print axioms noLowOwn_two

/-- A typed word at a one-word component is not `undef`. -/
theorem wordOK_one_nundef {E : TEnv} {T U : Ty} {o : Nat} {w : Word} (h : WordOK E T o w)
    (hat : AtOff T o U) (hU : accs U = some [Acc.one]) : w.val ≠ .undef := by
  intro hw
  obtain ⟨w0, hvr, hle⟩ := TermTyped.wordOK_one h hat hU
  exact TermTyped.VR_one_nundef U hvr hU 0 w0 (TermFul.OneAt.here []) rfl (hle.1.trans hw)

#print axioms wordOK_one_nundef

/-- A value's word at a one-word component is not `undef`. -/
theorem valOf_nundefU {E : TEnv} {T U : Ty} {L : List Acc} {ws : List Word} {o : Nat}
    (hv : ValOf E T ws) (hL : accs T = some L) (hat : AtOff T o U) (hU : accs U = some [Acc.one])
    {w : Word} (hw : ws[o]? = some w) : w.val ≠ .undef := by
  have hnu := TermTyped.VR_one_nundef T hv.1 hL
  obtain ⟨pre, post, e, hn⟩ := AtOff_embed hat hL hU
  subst e
  exact hnu o w (hn ▸ TermSeenHid.oneAt_mid pre post) hw

#print axioms valOf_nundefU

/-- **The cell word of an own cell at an initialised one-word component is not `undef`**
(`TermSeenHid.own_val` at any one-word component). -/
theorem own_valU {E : TEnv} {l : AllocLabel} {cl : Cell} {vals : List Word} {o : Nat} {U : Ty}
    (hcell : CellOK E (E.rc l) cl.ty vals) (hat : AtOff cl.ty o U) (hU : accs U = some [Acc.one])
    (hr : InitRr E cl l o) :
    ∃ w, vals[o]? = some w ∧ w.val ≠ .undef := by
  rcases hcell with ⟨hwc, hv⟩ | ⟨N, e, us, hty, hus, -, hlen, hsl⟩
  · obtain ⟨L, hL⟩ : ∃ L, accs cl.ty = some L := by
      cases h : accs cl.ty with
      | none => simp [wc, h] at hwc
      | some L => exact ⟨L, rfl⟩
    have hlenL : vals.length = nWords L := by
      simp only [wc, hL, Option.map_some, Option.some.injEq] at hwc; exact hwc.symm
    have hb := AtOff_bound hat hL hU
    have h1 : nWords [Acc.one] = 1 := rfl
    have hlt : o < vals.length := by rw [hlenL]; omega
    exact ⟨vals[o], List.getElem?_eq_getElem hlt, valOf_nundefU hv hL hat hU (List.getElem?_eq_getElem hlt)⟩
  · rcases AtOff_arr_elem hat hty with h | ⟨us', j', o', hus', hj', ho, hat'⟩
    · rw [hty] at h; subst h; simp [accs] at hU
    · rw [hus] at hus'; cases hus'
      have hb := AtOff_bound hat' hus hU
      have h1 : nWords [Acc.one] = 1 := rfl
      have hrl := hr N e us hty hus
      have hjr : j' < E.rc l := by
        refine Nat.lt_of_not_le fun hle => ?_
        have := Nat.mul_le_mul_right (nWords us) hle
        omega
      have hv := hsl j' hjr
      have hN : (j' + 1) * nWords us ≤ N * nWords us := Nat.mul_le_mul_right _ hj'
      rw [Nat.succ_mul] at hN
      have hlt : o < vals.length := by rw [hlen]; omega
      have hw : ((vals.drop (j' * nWords us)).take (nWords us))[o']? = vals[o]? := by
        rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
        congr 1; omega
      exact ⟨vals[o], List.getElem?_eq_getElem hlt,
        valOf_nundefU hv hus hat' hU (by rw [hw]; exact List.getElem?_eq_getElem hlt)⟩

#print axioms own_valU

/-- A message at `a` below `tw` gives a predecessor of `tw` at `a`, at or above it. -/
theorem predAt_above {mem : Memory} {a : Address} {tw : Ts} :
    ∀ (n t : Nat) (m : Msg), tw - t = n → t < tw → mem[t]? = some m → m.loc = a →
      ∃ (t1 : Nat) (m1 : Msg), t ≤ t1 ∧ PredAt mem a tw (mw m1) ∧ t1 < tw ∧ mem[t1]? = some m1 ∧
        m1.loc = a := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro t m hn hlt hm hl
    by_cases hb : ∃ (t2 : Nat) (m2 : Msg), t < t2 ∧ t2 < tw ∧ mem[t2]? = some m2 ∧ m2.loc = a
    · obtain ⟨t2, m2, h1, h2, h3, h4⟩ := hb
      obtain ⟨t1, m1, h5, h6⟩ := ih (tw - t2) (by rw [← hn]; omega) t2 m2 rfl h2 h3 h4
      exact ⟨t1, m1, Nat.le_trans (Nat.le_of_lt h1) h5, h6⟩
    · exact ⟨t, m, Nat.le_refl _, ⟨t, m, hlt, hm, hl, rfl, fun t2 m2 h1 h2 h3 h4 => hb ⟨t2, m2, h1, h2, h3, h4⟩⟩,
        hlt, hm, hl⟩

#print axioms predAt_above

/-- **A defined predecessor at an initialised one-word unit of an own cell** from the owner's
invariant (`OwnOKSF`) and `PromAbove`: the lowest own promise `tw` lies above coherence, the
coherence message carries the cell word (not `undef`) or a typed word, and every message between
them is an own promise (below `tw`: impossible) or typed. -/
theorem predNU_of_promAbove {E : TEnv} {s : St} {l : AllocLabel} {cl : Cell} {o tw : Ts} {U : Ty}
    (hsto : E.sto l = some cl) (hown : cl.owner = some E.tid)
    (hOK : OwnOKPF E s.mem s.pairs s.vs s.promises) (hPA : PromAbove s)
    (hlo : TermPlant.LowOwn s ⟨l, o⟩ tw) (hat : AtOff cl.ty o U) (hU : accs U = some [Acc.one])
    (hIr : InitRr E cl l o) :
    ∃ w, PredAt s.mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef := by
  obtain ⟨vals, hcell, hlat, -⟩ := hOK l cl hsto hown
  obtain ⟨v, hv, hvnu⟩ := own_valU hcell hat hU hIr
  obtain ⟨⟨mc, hmc, hlc, hval⟩, -, hafter⟩ := hlat o v hv
  obtain ⟨htw, ⟨mq, hmq, hlq⟩, hlow⟩ := id hlo
  have hca : s.vs.coh ⟨l, o⟩ < tw := by
    have h := hPA tw htw mq hmq
    rw [hlq] at h
    exact h
  obtain ⟨t1, m1, hle, hpred, hlt1, hm1, hl1⟩ := predAt_above _ _ mc rfl hca hmc hlc
  refine ⟨mw m1, hpred, ?_⟩
  have htyp : ∀ m : Msg, m.loc = ⟨l, o⟩ → TypedAt E cl m → (mw m).val ≠ .undef := by
    intro m hl ht
    unfold TypedAt at ht
    rw [hl] at ht
    exact wordOK_one_nundef ht hat hU
  rcases Nat.eq_or_lt_of_le hle with e | hgt
  · rw [← e] at hm1
    rw [hmc] at hm1
    cases hm1
    rcases hval with ⟨hvv, -⟩ | ⟨-, ht⟩
    · show mc.val ≠ .undef
      rw [hvv]; exact hvnu
    · exact htyp mc hlc ht
  · rcases hafter t1 m1 hgt hm1 hl1 with hp | ⟨-, ht⟩
    · exact absurd (hlow t1 m1 hp hm1 hl1) (Nat.not_le.mpr hlt1)
    · exact htyp m1 hl1 ht

#print axioms predNU_of_promAbove

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (shared) **The free atoms of a foreign non-`PubShape` step**: at a unit of the owner `j`'s
frontier cell `l` newly reached by a message (new, or a lost footprint promise), the unit is a free
atom (`FreeAt`), the `undef`-predecessor case discharged by `hPN` (the parameter of the
`foreign_overCrNP*` family: `hpredNU`, or `UndefLowG` via `predNU_of_UL`). -/
theorem np_hfree {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOutC p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hnps : ¬ TermPiece.PubShape cx th)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    (hPA : TermOverCr.PromAboveG c)
    (hPN : ∀ o tw U, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermForWU.RmwAtom (Cut Eg j Sj) ⟨l, o⟩ → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      PredU (Cut Eg j Sj) ⟨l, o⟩ → Eg.pubd l → ¬ InitRr (Cut Eg j Sj) cl l o →
      AtOff cl.ty o U → Solid U → accs U = some [Acc.one] →
      (∃ t0 m0, t0 < tw ∧ c.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val ≠ .undef) →
      ∃ w, PredAt c.mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef) :
    ∀ o, TermOverCr.CovU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o → ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      ∀ t m, c'.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      (c.mem.size ≤ t ∨ (t ∈ (Cut Eg j Sj).fp ∧ t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧ t ∉ thj.promises ∧ c.mem[t]? = some m)) →
      FreeAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl o := by
  have hgf := gfoot_of X Y Z
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, hini2, hrini2, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hpreM := tctx_pre X
  have hP' := PromsOK_thread X.inv.proms X.inv.disj X.hth X.e3 X.ho (tctx_sub X)
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpfE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l =
      (Cut Eg j Sj).pfr l := hpfr2
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  have hiniE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l =
      (Cut Eg j Sj).ini l := hini2
  have hrcE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l =
      (Cut Eg j Sj).rc l := by
    show min ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l)
        ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').rini l) = min (Eg.ini l) (Eg.rini l)
    rw [hini2, hrini2]
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  have hstok : (Cut Eg i S).sto l = some cl := cutSto_some.2 ⟨hs, Or.inr ⟨f, hf⟩⟩
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hcpl : Ty.coupledOKIn [] cl.ty = true := MemInv_cplT hmi hpre_c hf
  have hlay : LayT cl.ty := (hmi.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hpre_c hf).1
  -- the free atoms
  have hsη : (CE η).sto l = (Cut Eg j Sj).sto l := by rw [Y.1]; exact hstok.trans hpre_c.symm
  have hown' : cl.owner ≠ some i := by rw [hown]; exact fun h => hji (Option.some.inj h)
  obtain ⟨hF1, hF2⟩ := TermForWU.tctx_forWU hsc X Y hm
  have hfree : ∀ o, TermOverCr.CovU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) cl l o → ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      ∀ t m, c'.mem[t]? = some m → m.loc = ⟨l, o⟩ →
      (c.mem.size ≤ t ∨ (t ∈ (Cut Eg j Sj).fp ∧
        t ∉ (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).fp ∧
        t ∉ thj.promises ∧ c.mem[t]? = some m)) →
      FreeAt (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl o := by
    intro o hIc hv t m hm1 hloc hsrc tw hlo
    have hstoη : (CE η).sto m.loc.label = some cl := by rw [hloc]; exact hsη.trans hpre_c
    have hWR : WordUnit (CE η) m.loc ∨ TermForWU.RmwAtom (CE η) m.loc := by
      rcases hsrc with hnew | ⟨hf1, hf1', hnp, hm0⟩
      · exact hF1 t m cl hnew hm1 hstoη hown' hnps
      · obtain ⟨h1, h2⟩ := lostFp_stepper X.inv.proms hP' hj hji X.e3 X.ho X.hth hf1 hf1' hnp
        exact hF2 t m cl h1 h2 hm0 hstoη hown' hnps
    rw [hloc] at hWR
    have hnw : ¬ WordUnit (Cut Eg j Sj) ⟨l, o⟩ := fun hw =>
      hv ⟨(WordUnit_congr (a := ⟨l, o⟩) hstoE).2 hw, Vis_pfr hpf2'⟩
    have hR : TermForWU.RmwAtom (Cut Eg j Sj) ⟨l, o⟩ := by
      rcases hWR with hw | hR0
      · exact absurd ((WordUnit_congr (a := ⟨l, o⟩) hsη).1 hw) hnw
      · exact rmwAtom_congr hsη.symm hR0
    rcases rmw_leaf hR hpre_c with ⟨U, hat, hsol, hU, hcl, haf⟩ | hep
    · by_cases hB : PredU (Cut Eg j Sj) ⟨l, o⟩ ∧ ¬ Eg.pubd l
      · -- (B) a predicted unit of an unpublished cell: `tw` is its first write (`PredHoldG`)
        obtain ⟨h0, hfw, hh0, -⟩ := X.inv.predHold j thj Sj ⟨l, o⟩ hj ⟨cl, hs, hown⟩ hB.2 hB.1
        obtain ⟨htw, ⟨mq, hmw, hml⟩, hlow⟩ := id hlo
        have hle : tw ≤ h0 := by
          obtain ⟨⟨m1, hm1, hl1, -⟩, -⟩ := id hfw
          exact hlow h0 m1 hh0 hm1 hl1
        have hge : h0 ≤ tw :=
          TermPredHold.holder_min hfw hmw hml (X.inv.promNU j thj tw mq hj htw hmw)
        have e : h0 = tw := Nat.le_antisymm hge hle
        subst e
        have hok := X.inv.promTy j thj h0 mq hj htw hmw cl (by rw [hml]; exact hs)
          (by rw [hml]; exact ⟨f, hf⟩)
        rw [hml] at hok
        exact ⟨U, mw mq, hnw, hat, hsol, hU, hcl, haf, .inr ⟨hB.1, hfw, mq, hmw, rfl⟩,
          WordOK_transferS (InclS_pub_cut Eg j Sj) (X.inv.shty l cl ⟨f, hf⟩ hs) hok⟩
      · have hqOf : ¬ InitRr (Cut Eg j Sj) cl l o → PredU (Cut Eg j Sj) ⟨l, o⟩ := fun hIr => by
          rcases hIc with hi | hq'
          · exact absurd (fun N e us h1 h2 => by
              have h3 := hi N e us h1 h2
              rw [hrcE] at h3
              exact h3) hIr
          · exact (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).1 hq'
        by_cases hA0 : ¬ InitRr (Cut Eg j Sj) cl l o ∧
            ∀ t0 m0, t0 < tw → c.mem[t0]? = some m0 → m0.loc = ⟨l, o⟩ → m0.val = .undef
        · -- (A0) a predicted unit with no defined message below `tw`: `tw` is the first write,
          -- pinned at its own word (`CrItemQ`'s predicted-unit arm; typed by `PromTyAOK`)
          obtain ⟨htw, ⟨mq, hmw, hml⟩, -⟩ := id hlo
          have hFW : FirstW c.mem ⟨l, o⟩ tw := ⟨⟨mq, hmw, hml, X.inv.promNU j thj tw mq hj htw hmw⟩, hA0.2⟩
          have hok := X.inv.promTy j thj tw mq hj htw hmw cl (by rw [hml]; exact hs)
            (by rw [hml]; exact ⟨f, hf⟩)
          rw [hml] at hok
          exact ⟨U, mw mq, hnw, hat, hsol, hU, hcl, haf, .inr ⟨hqOf hA0.1, hFW, mq, hmw, rfl⟩,
            WordOK_transferS (InclS_pub_cut Eg j Sj) (X.inv.shty l cl ⟨f, hf⟩ hs) hok⟩
        -- (A) an initialised unit: `PromAbove` and the owner's invariant (`predNU_of_promAbove`)
        obtain ⟨w, hpred, hnu⟩ : ∃ w, PredAt c.mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef := by
          by_cases hIr : InitRr (Cut Eg j Sj) cl l o
          · exact predNU_of_promAbove (E := Cut Eg j S0) hpre_c hown hmi.2.1 (hPA j thj hj) hlo hat hU hIr
          · have hq := hqOf hIr
            have hex : ∃ t0 m0, t0 < tw ∧ c.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val ≠ .undef :=
              (Classical.em _).elim id fun hn => False.elim <| hA0 ⟨hIr, fun t0 m0 h1 h2 h3 =>
                (Classical.em _).elim id fun h4 => False.elim <| hn ⟨t0, m0, h1, h2, h3, h4⟩⟩
            exact hPN o tw U hv hR hlo hq ((Classical.em _).elim id fun hn => False.elim <| hB ⟨hq, hn⟩) hIr hat hsol hU hex
        obtain ⟨t0, m0, hlt, hm0, hl0, hw0, -⟩ := id hpred
        have hnp : t0 ∉ thj.promises := fun h =>
          Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt (hlo.2.2 t0 m0 h hm0 hl0))
        rcases hmi.1.1 t0 m0 cl hnp hm0 (by rw [hl0]; exact hpre_c) with hu | hok
        · exact absurd (by rw [← hw0]; exact hu) hnu
        · rw [hl0, hw0] at hok
          exact ⟨U, w, hnw, hat, hsol, hU, hcl, haf, .inl hpred, WordOK_cut (X.inv.shty l cl ⟨f, hf⟩ hs) hok⟩
    · obtain ⟨o', n, P, hatE, h1, h2⟩ := hep
      obtain ⟨htw, ⟨mw, hmw, hml⟩, -⟩ := id hlo
      have hno := X.inv.promNoTwo j thj tw mw cl hj htw hmw (by rw [hml]; exact hs) o'
        (epair_twoAtT hlay hatE)
      rw [hml] at hno
      exact absurd hno (fun ⟨a, b⟩ => by
        rcases Nat.lt_or_ge o (o' + 1) with h3 | h3
        · exact a (Nat.le_antisymm (Nat.lt_succ_iff.mp h3) h1)
        · exact b (Nat.le_antisymm (Nat.lt_succ_iff.mp h2) h3))
  exact hfree

#print axioms np_hfree


/-- **(Cfg layer, F3 R=0) The credited cover of an idle thread's own frontier cell after a
non-`PubShape` step** of thread `i`.  Environment premises as in `foreign_overCrCfg`; the entry
premise is `hent_free`, its free atoms from `tctx_forWU` (`hsc`, `hm`, `hnps`).  What remains:
the plant transfer's targets (`hT`, `hTp`, `hTlab`, `hD`, `hwaD`) and the OPEN items `hpredNU` (the lowest own promise at a written RMW atom has
a non-`undef` predecessor) and `hWb` (G2 window transport). -/
theorem foreign_overCrNP {c c' : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res}
    {i : Nat} {th : TTh} {r : Memory × List Ts × TTh} {S : AllocLabel → Prop} {ρ : Nat → Nat} {η : TEnv}
    {cx : Cx} {Rf Rs : Res} {E' : TEnv} {Tot' HP' HS' C F : Res} {cr' db' δ : Ts → Res}
    (hsc : StepScopeF p k arch Sp Init MintOK c0)
    (X : TCtxX p k arch Sp Init MintOK c0 c c' Eg Tot HP HS cr db i th r) (Y : EnvAt p Eg i th (Tot i) S ρ η cx Rf Rs)
    (Z : TOut p (gOf p k arch c i) η (stOf c.mem c.pairs th) r E' Tot' HP' HS' C F cr' db' Rf Rs (HP i + HS)
      (cr i) (db i) δ)
    (hm : MemInv (gOf p k arch c i) (CE η) (stOf c.mem c.pairs th))
    (hnps : ¬ TermPiece.PubShape cx th)
    (hOC : TermOverCr.OverCrG Eg c cr)
    {j : Nat} {thj : TTh} {Sj : AllocLabel → Prop} (hji : j ≠ i) (hj : c.ths[j]? = some thj)
    {l : AllocLabel} {cl : Cell}
    (hc2 : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l = some cl)
    (hown : cl.owner = some j) (hpf2 : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').pfr l ≠ none)
    {tg : TermPiece.GdE → Option Ts} {Gd : List TermPiece.GdE}
    (hnd : (Gd.map TermPiece.GdE.key).Nodup)
    -- the plant transfer's targets
    (hTlab : ∀ g ∈ Gd, ∀ t m, tg g = some t → c'.mem[t]? = some m → m.loc.label = g.l)
    (hT : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → ∃ m R us, c'.mem[t]? = some m ∧ m.loc.label = g.l ∧
      PlantCr (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (stOf c'.mem c'.pairs thj) m t R ∧
      TermPiece.Piece cl.ty g.b g.S ∧ accs g.S = some us ∧ g.b ≤ m.loc.offset ∧ m.loc.offset < g.b + nWords us)
    (hTp : ∀ g ∈ Gd, g.l = l → ∀ t, tg g = some t → t ∈ thj.promises)
    (hD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd,
      TermOverCr.CrItemQ (Cut Eg j Sj) (stOf c.mem c.pairs thj)
        (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl y)
    (hwaD : ∀ y ∈ dnOf l tg (kfOf (Cut Eg j Sj) (stOf c.mem c.pairs thj) l) Gd, ∀ usS i o,
      accs y.2.2.1 = some usS → y.2.2.2.2.2 i = true → InAcc usS i o →
      ∃ t0, TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, y.2.1 + o⟩ t0)
    -- every thread's promises lie above its coherence (the `SysInvN` clause `PromAboveG`)
    (hPA : TermOverCr.PromAboveG c)
    -- OPEN (undef predecessor, narrowed): at a predicted, not initialised unit of a published cell
    -- with a defined message below the lowest own promise at a non-visible RMW atom, that promise has
    -- a defined predecessor
    (hpredNU : ∀ o tw, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      TermForWU.RmwAtom (Cut Eg j Sj) ⟨l, o⟩ → TermPlant.LowOwn (stOf c.mem c.pairs thj) ⟨l, o⟩ tw →
      PredU (Cut Eg j Sj) ⟨l, o⟩ → Eg.pubd l → ¬ InitRr (Cut Eg j Sj) cl l o →
      (∃ t0 m0, t0 < tw ∧ c.mem[t0]? = some m0 ∧ m0.loc = ⟨l, o⟩ ∧ m0.val ≠ .undef) →
      ∃ w, PredAt c.mem ⟨l, o⟩ tw w ∧ w.val ≠ .undef)
    -- OPEN (G2): the window conditions transport back along the step
    (hWb : ∀ o tw, TermOverCr.WinG (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) l o tw → TermOverCr.WinG (Cut Eg j Sj) (stOf c.mem c.pairs thj) l o tw) :
    TermOverCr.OverCrE (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj)
      (stOf c'.mem c'.pairs thj) (fun t => cr j t + TermPlant.plantD1 Gd TermPiece.GdE.R tg t) l cl := by
  have hgf := gfoot_of X Y (Z.toC _ _ _ _ _)
  have hfr := X.inv.gfresh X.hth r.2.2.nalloc
  obtain ⟨hpre_c, hs, -, hini2, hrini2, hpfr2⟩ := own_agree hgf hfr hji Sj hc2 hown
  have hpf : Eg.pfr l ≠ none := by rw [← hpfr2]; exact hpf2
  obtain ⟨f, hf⟩ := Option.ne_none_iff_exists'.1 hpf
  have hpreM := tctx_pre X
  have hstoE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).sto l =
      (Cut Eg j Sj).sto l := hc2.trans hpre_c.symm
  have hpfE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l =
      (Cut Eg j Sj).pfr l := hpfr2
  have hpf2' : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).pfr l = some f :=
    hpfr2.trans hf
  have hiniE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).ini l =
      (Cut Eg j Sj).ini l := hini2
  have hrcE : (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj).rc l =
      (Cut Eg j Sj).rc l := by
    show min ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').ini l)
        ((Eg.post (gOf p k arch c i) th.nalloc r.2.2.nalloc E').rini l) = min (Eg.ini l) (Eg.rini l)
    rw [hini2, hrini2]
  have hI := (Cut_other hgf (j := j) hji Sj).1.trans (Incl_cut_withFp _ (fpSync Eg c') j Sj)
  obtain ⟨S0, -, -, hmi, -⟩ := X.inv.thr j thj hj
  have hcpl : Ty.coupledOKIn [] cl.ty = true := MemInv_cplT hmi hpre_c hf
  have hfree := np_hfree hsc X Y (Z.toC _ _ _ _ _) hm hnps hji hj hc2 hown hpf2 hPA
    (fun o tw _ hv hR hlo hq hpb hIr _ _ _ hex => hpredNU o tw hv hR hlo hq hpb hIr hex)
  have hVU : ∀ o, ¬ VisU (Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) ⟨l, o⟩ →
      ¬ VisU (Cut Eg j Sj) ⟨l, o⟩ :=
    fun o h hv => h ((VisU_congr (a := ⟨l, o⟩) hstoE rfl hpfE).2 hv)
  have hent := hent_free (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    (l := l) (c := cl) (tg := tgL l tg) (Gd := Gd) rfl hpreM hVU
    (fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).1 h)
    (fun _ => Vis_pfr hpf2') hfree
  -- the cover with the targets at `l`
  have hlabC : ∀ t m, c.mem[t]? = some m → m.loc.label = l →
      TermPlant.plantD1 Gd TermPiece.GdE.R (tgL l tg) t = TermPlant.plantD1 Gd TermPiece.GdE.R tg t :=
    fun t m hm1 hl => by
      have hlt : t < c.mem.size := by
        rcases Nat.lt_or_ge t c.mem.size with h1 | h1
        · exact h1
        · rw [Array.getElem?_eq_none h1] at hm1; cases hm1
      exact plantD1_tgL hTlab (by rw [hpreM t hlt]; exact hm1) hl
  have hcovL := foreign_overCrPZ (E := Cut Eg j Sj) (s := stOf c.mem c.pairs thj)
    (E' := Cut (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c') j Sj) (s' := stOf c'.mem c'.pairs thj)
    (cr := cr j) (tg := tgL l tg) (Gd := Gd) (Fz := freeL (Cut Eg j Sj) (stOf c.mem c.pairs thj) l cl)
    hpreM rfl (fun t ht => X.inv.plt j thj t hj ht) hpre_c hstoE
    (fun S0 ws R0 hv => ValOfR_mono hI.prog rfl hI.sto hI.ini hv hI.pfr hI.box hI.rini)
    (Nat.le_of_eq hrcE) (Nat.le_of_eq hiniE) hpf hVU
    (fun o h => (predU_congr (a := ⟨l, o⟩) hstoE hpfE hiniE hrcE).2 h)
    (fun t m ht hm1 => X.inv.promNU j thj t m hj ht hm1) hWb hcpl (X.inv.stoNI l cl hs)
    (hOC j thj Sj hj l cl hpre_c hown hpf) hnd
    (fun g hg t ht => by
      obtain ⟨hgl, ht'⟩ := tgL_some ht
      exact hT g hg hgl t ht')
    (fun g hg t ht => by
      obtain ⟨hgl, ht'⟩ := tgL_some ht
      exact hTp g hg hgl t ht')
    (fun g _ t ht => (tgL_some ht).1)
    (fun y hy => by
      rw [dnOf_tgL] at hy
      have hy' := hD y hy
      obtain ⟨mh, _, hmh, hlab, _⟩ := id hy'
      refine crItemQ_mono ?_ hy'
      show _ ≤ _
      rw [hlabC y.1 mh hmh hlab]
      exact Res.le_refl _)
    (fun y hy => by
      rw [dnOf_tgL] at hy
      exact hwaD y hy)
    freeL_item freeL_zero freeL_wa freeL_holder hent
  refine overCrE_congrL (fun t m hm1 hl => ?_) hcovL
  show cr j t + _ = cr j t + _
  rw [plantD1_tgL hTlab hm1 hl]

#print axioms foreign_overCrNP


end

end TermOverCrW

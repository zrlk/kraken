/-
**PrivSlotFresh from PrivCoh**: the residual `TermPlantS.PrivSlotF` from the
memory clause `PrivCoh` (every non-promise message at an uninitialised unit of an own private
buffer is the coherence message, `.undef`), certification (`PromAbove`, `certified_promNotUndefX`)
and the held prefix (`PrefixHeld` at `Np`).

`PrivCoh` / `PrivU` are from TermStep; the hypothesis `hPC` (`MemInv` gives `PrivCoh`) is
the `FreshLP` projection `fun hm => hm.2.2.2.1.2`.
-/
import WeakCore.TermPlantS
namespace TermPlantP
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
open TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold
open TermPlantR TermPlantW TermPlantL TermPlantE TermPlantS
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (P1) **R1w from PrivCoh** at a `PrivU` word: the coherence message is the
placeholder; every other message is a promise above it (`PromAbove`), not `.undef`. -/
theorem privR1w {E : TEnv} {s : St} {a : Address} (hP : PrivCoh E s)
    (hO : OwnOKPF E s.mem s.pairs s.vs s.promises) (hA : PromAbove s) (hu : PrivU E a)
    (hnu : ∀ t m, t ∈ s.promises → s.mem[t]? = some m → m.loc = a → m.val ≠ .undef)
    (hex : ∃ t m, t ∈ s.promises ∧ s.mem[t]? = some m ∧ m.loc = a) :
    ∃ t0 m0, s.mem[t0]? = some m0 ∧ m0.loc = a ∧ m0.val = .undef ∧ t0 ∉ s.promises ∧
      (∃ t, AtA s.mem a t0 t = true) ∧
      ∀ t m, s.mem[t]? = some m → m.loc = a → t ≠ t0 → t0 < t ∧ m.val ≠ .undef ∧ t ∈ s.promises := by
  have hu' := hu
  obtain ⟨c, N, e, us, hc, ho, hpf, hT, hus, -, hin⟩ := hu
  obtain ⟨vals, hcell, hlat, -⟩ := hO a.label c hc ho
  have hlen : vals.length = N * nWords us := by
    rcases hcell with ⟨hwc, -⟩ | ⟨N', e', us', hT', hus', -, hl, -⟩
    · rw [hT] at hwc; simp [wc, accs] at hwc
    · rw [hT] at hT'; cases hT'; rw [hus] at hus'; cases hus'; exact hl
  have hlt : a.offset < vals.length := by rw [hlen]; exact hin
  have hv : vals[a.offset]? = some vals[a.offset] := List.getElem?_eq_getElem hlt
  obtain ⟨⟨m0, hm0, hl0, -⟩, hnp, -⟩ := hlat a.offset _ hv
  have ea : (⟨a.label, a.offset⟩ : Address) = a := rfl
  rw [ea] at hm0 hl0 hnp
  refine ⟨s.vs.coh a, m0, hm0, hl0, (hP _ m0 hnp hm0 (hl0 ▸ hu')).2, hnp, ?_, fun t m hm hl hne => ?_⟩
  · obtain ⟨t, m, ht, hm, hl⟩ := hex
    refine ⟨t, ?_⟩
    simp only [AtA, decide_eq_true_eq]
    exact ⟨⟨m, hm, hl⟩, fun e => hnp (e ▸ ht)⟩
  · by_cases ht : t ∈ s.promises
    · have h1 := hA t ht m hm
      rw [hl] at h1
      exact ⟨h1, hnu t m ht hm hl, ht⟩
    · exact absurd (hl ▸ (hP t m ht hm (hl ▸ hu')).1) hne

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (P2) **`PrivSlotF` from `PrivCoh`**: given that every `MemInv` carries `PrivCoh` (the clause,
folded into `FreshLP`), the residual PrivSlotFresh holds. -/
theorem privSlot_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    (hPC : ∀ {g : G} {E : TEnv} {s : St}, MemInv g E s → PrivCoh E s) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    TermPlantS.PrivSlotF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X l f hf hno cl N e us hcl _ hT hu i h1 h2
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hf
  obtain ⟨cl', hcl', ho, hnone, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hcl'; cases hcl'
  obtain ⟨S0, hSS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hSS0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hb : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  have hm1 : MemInv (gOf p k arch c j) (Cut Eg j S0)
      (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := MemInv_promSt hm
  have hpa1 : PromAbove (stOf (c.mem.push ⟨a, v, w⟩) c.pairs (thP th c.mem.size)) := by
    have h1 := TermTyped.certified_promAboveSt X.cert hpi.2.1
    rw [hpi.2.2] at h1
    exact h1
  -- certification: no promise is `.undef`
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have hsc := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).2
  have hnu : ∀ t m, t ∈ (thP th c.mem.size).promises → (c.mem.push ⟨a, v, w⟩)[t]? = some m →
      m.loc = ⟨l, i⟩ → m.val ≠ .undef := fun t m ht hm _ => by
    have ht' : t ∈ TermFul.promsOf (promise c j a v w) j := by
      rw [TermFul.promsOf_some hpi.2.1]; exact ht
    have hmt : (promise c j a v w).mem[t]? = some m := by rw [hpi.1]; exact hm
    exact (certified_promNotUndefX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX X.cert ht' hmt).1
  -- the word is below the planted count, hence in the buffer and held by a promise
  have hPsto : (TermPlantF.cutP Eg j).sto l = some cl := cutSto_own hcl ho
  have hNp : i < NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l * nWords us := by
    rw [← plantN_eq l X]
    rcases Nat.le_total (Eg.ini l) (TermPlantF.plantN c Eg j a v w l) with hle | hle
    · rw [Nat.max_eq_right hle] at h2; exact h2
    · rw [Nat.max_eq_left hle] at h2; omega
  have hkN : NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l ≤ N := NpZ_le hPsto hT
  have hin : i < N * nWords us :=
    Nat.lt_of_lt_of_le hNp (Nat.mul_le_mul_right _ hkN)
  have hex : ∃ t m, t ∈ (thP th c.mem.size).promises ∧ (c.mem.push ⟨a, v, w⟩)[t]? = some m ∧
      m.loc = ⟨l, i⟩ := by
    rcases PrefixHeld_NpZ hPsto N e us hT hu i hNp with hI | ⟨u, hu', m, hm, hl⟩
    · have := hI N e us hT hu
      have e1 : (TermPlantF.cutP Eg j).ini l = Eg.ini l := rfl
      rw [e1] at this; omega
    · refine ⟨u, m, List.mem_append_left _ hu', ?_, hl⟩
      rw [getElem_push_lt (hb u hu')]; exact hm
  have hU : PrivU (Cut Eg j S0) ⟨l, i⟩ := by
    refine ⟨cl, N, e, us, cutSto_own hcl ho, ho, hnone, hT, hu, ?_, hin⟩
    have e1 : (Cut Eg j S0).ini l = Eg.ini l := rfl
    have := (Cut Eg j S0).rc_le_ini l
    rw [e1] at this
    exact Nat.le_trans (Nat.mul_le_mul_right _ this) h1
  exact privR1w (hPC hm1) hm1.2.1 hpa1 hU hnu hex

end

/-! ## (P3) No new slots at buffers with a two-word unit -/

theorem oneAt_step : ∀ {us : List Acc} {j : Nat}, TermFul.OneAt us j → TermStep.OneAt us j
  | _, _, .here us => ⟨0, rfl, by simp [nWords]⟩
  | _, _, .cons u h => by
      obtain ⟨i, hi, rfl⟩ := oneAt_step h
      refine ⟨i + 1, by simpa using hi, ?_⟩
      simp only [List.take_succ_cons, nWords, List.map_cons, List.sum_cons]; omega

/-- A single-word write inside a buffer's slot lies at a `.one` unit of the element layout. -/
theorem slot_oneAt {N : Nat} {e U : Ty} {us us' : List Acc} {o j jj q : Nat}
    (hu : accs e = some us) (hat : AtOff (.array (.lit N) e) o U) (hus' : accs U = some us')
    (hj : TermFul.OneAt us' j) (hq : q < nWords us) (he : o + j = jj * nWords us + q) :
    TermStep.OneAt us q := by
  rcases AtOff_arr_elem hat rfl with hU | ⟨us0, jx, o1, hu0, -, ho, hat1⟩
  · subst hU; simp [accs] at hus'
  · rw [hu] at hu0; cases hu0
    obtain ⟨pre, post, hL, hpre⟩ := AtOff_embed hat1 hu hus'
    have h1 : TermStep.OneAt us (nWords pre + j) := by
      rw [hL]; exact OneAt_embed (oneAt_step hj)
    have hlt : nWords pre + j < nWords us := by
      obtain ⟨i, hi, hie⟩ := h1
      rw [hie]
      have := nWords_take_succ hi
      have hl : i + 1 ≤ us.length := (List.getElem?_eq_some_iff.1 hi).1
      have hm := nWords_take_mono (us := us) hl
      rw [List.take_length] at hm
      simp only [Acc.size] at this; omega
    have e2 : jx * nWords us + (nWords pre + j) = jj * nWords us + q := by rw [← he, ho, hpre]; omega
    have e3 : nWords pre + j = q := slot_eq hq hlt e2
    rw [← e3]; exact h1

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (P3) **No new slots past a two-word unit**: a planted buffer whose element layout has a
`.two` unit is not raised (`plantN ≤ ini`): the first word of that unit in slot `ini` would be
held by an outstanding promise, but certified promises lie at `.one` units (`SWOne_holds`). -/
theorem plantN_two (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : TermNoHold.CertRunP p k arch Sp Init MintOK c0)
    {c : Cfg} {Eg : GEnv} {Tot HP : Nat → Res} {HS : Res} {cr db : Nat → Ts → Res} {j : Nat} {th : TTh}
    {a : Address} {v : WeakMem.Val} {w : Ts} (X : PCtxX p k arch Sp Init MintOK c0 c Eg Tot HP HS cr db j th a v w)
    {l : AllocLabel} {f : Ts} {cl : Cell} {N : Nat} {e : Ty} {us : List Acc} {i : Nat}
    (hf : TermPlantF.plantOf c Eg j a v w l = some f) (hcl : Eg.sto l = some cl)
    (hT : cl.ty = .array (.lit N) e) (hu : accs e = some us) (h2 : us[i]? = some .two) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    TermPlantF.plantN c Eg j a v w l ≤ Eg.ini l := by
  apply Classical.byContradiction; intro hlt
  have hlt' : Eg.ini l + 1 ≤ TermPlantF.plantN c Eg j a v w l := by omega
  obtain ⟨⟨l', -, hR⟩, -⟩ := plantOf_some X hf
  obtain ⟨cl', hcl', ho, -⟩ := TermPlantF.plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hcl'; cases hcl'
  obtain ⟨S0, hSS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hSS0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hb : ∀ t, t ∈ th.promises → t < c.mem.size := fun t ht => X.inv.plt j th t X.hth ht
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have hsc := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).2
  -- the first word of the two-word unit in slot `ini`
  have hti : nWords (us.take i) + 2 ≤ nWords us := by
    have := nWords_take_succ h2
    have hl : i + 1 ≤ us.length := (List.getElem?_eq_some_iff.1 h2).1
    have hm := nWords_take_mono (us := us) hl
    rw [List.take_length] at hm
    simp only [Acc.size] at this; omega
  let q := nWords (us.take i)
  have hPsto : (TermPlantF.cutP Eg j).sto l = some cl := cutSto_own hcl ho
  have hNp : Eg.ini l * nWords us + q < NpZ (TermPlantF.cutP Eg j) (stOf c.mem c.pairs th) l * nWords us := by
    rw [← plantN_eq l X]
    have := Nat.mul_le_mul_right (nWords us) hlt'
    rw [Nat.succ_mul] at this; omega
  rcases PrefixHeld_NpZ hPsto N e us hT hu _ hNp with hI | ⟨u, hu', m, hmu, hl⟩
  · have := hI N e us hT hu
    have e1 : (TermPlantF.cutP Eg j).ini l = Eg.ini l := rfl
    rw [e1] at this; omega
  · have ht' : u ∈ TermFul.promsOf (promise c j a v w) j := by
      rw [TermFul.promsOf_some hpi.2.1]; exact List.mem_append_left _ hu'
    have hmt : (promise c j a v w).mem[u]? = some m := by
      rw [hpi.1]; show (c.mem.push ⟨a, v, w⟩)[u]? = some m
      rw [getElem_push_lt (hb u hu')]; exact hmu
    obtain ⟨c1, c2, th1, th2, ρ, η, cx, E2, -, -, -, -, -, -, hx1, hE, hTy, htv, hi, hmi, hscope, hpa, -, -, -, -, -,
      -, -, hsw, -⟩ := certified_promTypedX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX X.cert ht' hmt
    obtain ⟨cl2, o, U, us', j', hcl2, hat, hus', hj, hoff⟩ :=
      SWOne_holds p _ _ _ _ ρ η cx _ _ hE hTy htv hi hmi (TermTyped.scopeD_SW hscope hsw) hpa hsw
    have hcl0 : (Cut Eg j S0).sto m.loc.label = some cl := by rw [hl]; exact cutSto_own hcl ho
    rw [hx1.2.2.2.2.1 _ _ hcl0] at hcl2
    cases hcl2
    rw [hT] at hat
    have hq : q < nWords us := by omega
    have hoff' : o + j' = Eg.ini l * nWords us + q := by rw [← hoff, hl]
    exact TwoAt_not_OneAt ⟨i, h2, rfl⟩ (slot_oneAt hu hat hus' hj hq hoff')

end

end TermPlantP

#print axioms TermPlantP.privR1w
#print axioms TermPlantP.privSlot_of
#print axioms TermPlantP.slot_oneAt
#print axioms TermPlantP.plantN_two

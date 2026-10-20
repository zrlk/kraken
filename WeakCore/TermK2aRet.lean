import WeakCore.TermK2aOps

/-! # TermK2aRet (K-2a block B): the retyping operations and the frames

`fold`/`pack`/`packT` rebind the operand's words at the target type; `call`/`callc` enter a block
(binding the argument at the callee's rendition, pushing the caller's environment); `ret` pops.
The counted words of a retyped value are the operand's (`pubWords_subS`: subsumption, after any
closing substitution, keeps the counted words; they depend only on the signature, `pubWords_sig`). -/

namespace TermK2a
open CoreLang CoreTerm CoreTyping TermRun TermSound TermMem TermPtrRts
open WeakMem (Msg Memory Address Ts AllocLabel)

/-! ## Counted words read only the signature -/

theorem pubWords_rf (x : Ty) : (∀ ws, pubWords (rf x) ws = pubWords x ws) ∧ (∀ j p, pubArm (rf x) j p = pubArm x j p) := by
  cases x
  all_goals first
    | exact ⟨fun _ => rfl, fun _ _ => rfl⟩
    | exact ⟨fun ws => pubWords_refine _ _ ws, fun j p => by simp only [rf, pubArm]⟩

theorem armsOf_len_skel (t : Ty) : (armsOf (skel t)).length = (armsOf t).length := by
  rw [armsOf_skel, List.length_map]

theorem armsOf_len_er (t : Ty) : (armsOf (er t)).length = (armsOf t).length := by
  rw [armsOf_er, List.length_map]

theorem pubWords_er : ∀ (t : Ty),
    (∀ ws, pubWords (er t) ws = pubWords t ws) ∧ (∀ j p, pubArm (er t) j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      have hs := TermPtrRts.sNo_er (.prod a b)
      have hw := wc_er a
      simp only [er] at hs ⊢
      have h1 : ∀ ws, pubWords (.prod (er a) (er b)) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords, hs, hw, iha.1, ihb.1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have hs := TermPtrRts.sNo_er (.sum a b)
      have ht := tier_er (.sum a b)
      have hl := lnorm_er (.sum a b)
      simp only [er] at hs ht hl ⊢
      have hal := armsOf_len_er a
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, iha.2, ihb.2]
      · simp only [pubArm, hal, iha.2, ihb.2]
  | refine t ψ ih =>
      exact ⟨fun ws => by simp only [er]; rw [pubWords_refine, pubWords_refine, ih.1],
        fun j p => by simp only [er, pubArm, ih.2]⟩
  | iall t ih =>
      have hs := TermPtrRts.sNo_er (.iall t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | iex t ih =>
      have hs := TermPtrRts.sNo_er (.iex t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | mu t ih =>
      have hs := TermPtrRts.sNo_er (.mu t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | tex κ t ih =>
      have hs := TermPtrRts.sNo_er (.tex κ t)
      simp only [er] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | array i e _ =>
      have hs := TermPtrRts.sNo_er (.array i e)
      simp only [er] at hs ⊢
      have h1 : ∀ ws, pubWords (.array i (er e)) ws = pubWords (.array i e) ws := by
        intro ws; rw [pubWords.eq_def, pubWords.eq_def]; simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ => exact ⟨fun ws => by cases μ <;> simp [er, pubWords, sNo, mPub],
      fun j p => by cases μ <;> simp [er, pubArm, pubWords, sNo, mPub]⟩
  | ptrOpt μ u _ => exact ⟨fun ws => by cases μ <;> simp [er, pubWords, sNo, mPub],
      fun j p => by cases μ <;> simp [er, pubArm, pubWords, sNo, mPub]⟩
  | loc μ u _ => exact ⟨fun ws => by cases μ <;> simp [er, pubWords, sNo, mPub],
      fun j p => by cases μ <;> simp [er, pubArm, pubWords, sNo, mPub]⟩
  | _ => exact ⟨fun ws => by simp [er, pubWords, sNo], fun j p => by simp [er, pubArm, pubWords, sNo]⟩

theorem pubWords_skel : ∀ (t : Ty),
    (∀ ws, pubWords (skel t) ws = pubWords t ws) ∧ (∀ j p, pubArm (skel t) j p = pubArm t j p) := by
  intro t
  induction t with
  | prod a b iha ihb =>
      have hs := TermPtrRts.sNo_skel (.prod a b)
      have hw := wc_skel a
      simp only [skel] at hs ⊢
      have h1 : ∀ ws, pubWords (.prod (skel a) (skel b)) ws = pubWords (.prod a b) ws := by
        intro ws; simp only [pubWords, hs, hw, iha.1, ihb.1]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have hs := TermPtrRts.sNo_skel (.sum a b)
      have ht := tier_skel (.sum a b)
      have hl := lnorm_skel (.sum a b)
      simp only [skel] at hs ht hl ⊢
      have hal := armsOf_len_skel a
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · simp only [pubWords, hs, ht, hl, hal, iha.2, ihb.2]
      · simp only [pubArm, hal, iha.2, ihb.2]
  | refine t ψ ih =>
      exact ⟨fun ws => by simp only [skel]; rw [(pubWords_rf _).1, pubWords_refine, ih.1],
        fun j p => by simp only [skel]; rw [(pubWords_rf _).2]; simp only [pubArm, ih.2]⟩
  | iall t ih =>
      have hs := TermPtrRts.sNo_skel (.iall t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | iex t ih =>
      have hs := TermPtrRts.sNo_skel (.iex t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | mu t ih =>
      have hs := TermPtrRts.sNo_skel (.mu t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | tex κ t ih =>
      have hs := TermPtrRts.sNo_skel (.tex κ t)
      simp only [skel] at hs ⊢
      exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | array i e _ =>
      have hs := TermPtrRts.sNo_skel (.array i e)
      simp only [skel] at hs ⊢
      have h1 : ∀ ws, pubWords (.array (.lit 0) (skel e)) ws = pubWords (.array i e) ws := by
        intro ws; rw [pubWords.eq_def, pubWords.eq_def]; simp only [hs]
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | ptr μ u _ => exact ⟨fun ws => by cases μ <;> simp [skel, skelM, pubWords, sNo, mPub],
      fun j p => by cases μ <;> simp [skel, skelM, pubArm, pubWords, sNo, mPub]⟩
  | ptrOpt μ u _ => exact ⟨fun ws => by cases μ <;> simp [skel, skelM, pubWords, sNo, mPub],
      fun j p => by cases μ <;> simp [skel, skelM, pubArm, pubWords, sNo, mPub]⟩
  | loc μ u _ => exact ⟨fun ws => by cases μ <;> simp [skel, skelM, pubWords, sNo, mPub],
      fun j p => by cases μ <;> simp [skel, skelM, pubArm, pubWords, sNo, mPub]⟩
  | _ => exact ⟨fun ws => by simp [skel, pubWords, sNo], fun j p => by simp [skel, pubArm, pubWords, sNo]⟩

theorem pubWords_sig (t : Ty) (ws : List Word) : pubWords (sig t) ws = pubWords t ws := by
  unfold sig; rw [(pubWords_er _).1, (pubWords_skel _).1]

theorem pubArm_sig (t : Ty) (j : Nat) (p : List Word) : pubArm (sig t) j p = pubArm t j p := by
  unfold sig; rw [(pubWords_er _).2, (pubWords_skel _).2]


/-! ## Subsumption keeps the counted words (after any closing substitution) -/

/-- Same skeleton, same counted words and arms. -/
theorem pubWords_of_skel {t u : Ty} (h : skel t = skel u) :
    sNo t = sNo u ∧ (∀ ws, pubWords t ws = pubWords u ws) ∧ (∀ j p, pubArm t j p = pubArm u j p) ∧
      (armsOf t).length = (armsOf u).length := by
  refine ⟨?_, fun ws => ?_, fun j p => ?_, ?_⟩
  · rw [← TermPtrRts.sNo_skel t, h, TermPtrRts.sNo_skel]
  · rw [← (pubWords_skel t).1, h, (pubWords_skel u).1]
  · rw [← (pubWords_skel t).2, h, (pubWords_skel u).2]
  · rw [← armsOf_len_skel t, h, armsOf_len_skel]

theorem pubWords_subS {cx : Cx} {σ τ : Ty} (h : SubS cx σ τ) : ∀ (σs : List Ty) (c d : Nat),
    sNo (substTs σs c d σ) = sNo (substTs σs c d τ) ∧
    (∀ ws, pubWords (substTs σs c d σ) ws = pubWords (substTs σs c d τ) ws) ∧
    (∀ j p, pubArm (substTs σs c d σ) j p = pubArm (substTs σs c d τ) j p) ∧
    (armsOf (substTs σs c d σ)).length = (armsOf (substTs σs c d τ)).length := by
  induction h with
  | eq he => intro σs c d; exact pubWords_of_skel (skel_subst_eq (skel_tyEq he) σs c d d)
  | intS => intro σs c d; exact ⟨rfl, fun ws => by simp [substTs, pubWords, sNo],
      fun j p => by simp [substTs, pubArm, pubWords, sNo], by simp [substTs, armsOf]⟩
  | refine _ ih =>
      intro σs c d
      obtain ⟨h1, h2, h3, h4⟩ := ih σs c d
      refine ⟨by simp only [substTs, sNo, h1], fun ws => ?_, fun j p => ?_, by simp only [substTs, armsOf, h4]⟩
      · simp only [substTs]; rw [pubWords_refine, h2]
      · simp only [substTs, pubArm, h3]
  | iniWeak he _ =>
      intro σs c d
      obtain ⟨h1, h2, h3, h4⟩ := pubWords_of_skel (skel_subst_eq (skel_tyEq he) σs c d d)
      refine ⟨by simp only [substTs, sNo, h1], fun ws => ?_, fun j p => ?_, by simp only [substTs, armsOf, h4]⟩
      · simp only [substTs]; rw [pubWords_refine, pubWords_refine, h2]
      · simp only [substTs, pubArm, h3]
  | nonNull hm _ =>
      intro σs c d
      have e := TermPubOnly.mPub_meq hm
      refine ⟨by simp only [substTs, sNo, e], fun ws => ?_, fun j p => ?_, by simp [substTs, armsOf]⟩
      · cases hm <;> simp [substTs, pubWords, sNo, mPub]
      · cases hm <;> simp [substTs, pubArm, pubWords, sNo, mPub]
  | prod ha hb iha ihb =>
      rename_i a b a' b'
      intro σs c d
      obtain ⟨a1, a2, -, -⟩ := iha σs c d
      obtain ⟨b1, b2, -, -⟩ := ihb σs c d
      have hw := wc_sub ha σs c d
      have hP : ∀ ws, pubWords (substTs σs c d (.prod a b)) ws = pubWords (substTs σs c d (.prod a' b')) ws := by
        intro ws; simp only [substTs, pubWords, sNo, a1, b1, hw, a2, b2]; rfl
      refine ⟨by simp only [substTs, sNo, a1, b1], hP, fun j p => ?_, by simp [substTs, armsOf]⟩
      have := hP p
      simp only [substTs] at this ⊢
      simp only [pubArm]; exact this
  | sum ha hb iha ihb =>
      intro σs c d
      obtain ⟨a1, -, a3, a4⟩ := iha σs c d
      obtain ⟨b1, -, b3, b4⟩ := ihb σs c d
      have e := (info_sub (SubS.sum ha hb) σs c d).tier
      have el := lnorm_sub (SubS.sum ha hb) σs c d
      simp only [substTs] at e el ⊢
      have ht : (Ty.sum (substTs σs c d _) (substTs σs c d _)).tier =
          (Ty.sum (substTs σs c d _) (substTs σs c d _)).tier := e
      refine ⟨by simp only [sNo, a1, b1], fun ws => ?_, fun j p => ?_, by simp only [armsOf, List.length_append, a4, b4]⟩
      · simp only [pubWords, sNo, a1, b1, ht, el, a4, a3, b3]
        rfl
      · simp only [pubArm, a4, a3, b3]
  | cap => intro σs c d; exact ⟨rfl, fun ws => by simp [substTs, pubWords, sNo],
      fun j p => by simp [substTs, pubArm, pubWords, sNo], by simp [substTs, armsOf]⟩


/-! ## `fold`, `pack`, `packT`: the operand's counted words, at the target -/

theorem pubWords_iex_eq (B : Ty) (ws : List Word) : pubWords (.iex B) ws = pubWords B ws := by
  by_cases h : sNo B = true
  · rw [pubWords_of_sNo (t := .iex B) (by simpa [sNo] using h), pubWords_of_sNo h]
  · simp only [pubWords, sNo, h, Bool.false_eq_true, ite_false]

theorem pubWords_tex_eq (κ : Kind) (B : Ty) (ws : List Word) : pubWords (.tex κ B) ws = pubWords B ws := by
  by_cases h : sNo (.tex κ B) = true
  · have hb : sNo B = true := by simp only [sNo, Bool.and_eq_true] at h; exact h.2
    rw [pubWords_of_sNo h, pubWords_of_sNo hb]
  · simp only [pubWords, h, Bool.false_eq_true, ite_false]

theorem pubWords_foldOK {cx : Cx} {t τ : Ty} (h : FoldOK cx t τ) (σs : List Ty) (ws : List Word) :
    pubWords (close σs τ) ws = pubWords (close σs t) ws := by
  cases h with
  | ptr hm _ => cases hm <;> simp [close, substTs, pubWords, sNo, mPub]
  | ptrOpt hm _ => cases hm <;> simp [close, substTs, pubWords, sNo, mPub]
  | loc hm _ => cases hm <;> simp [close, substTs, pubWords, sNo, mPub]

theorem pubWords_pack {cx : Cx} {t body : Ty} {w : Idx} (h : SubS cx t (instT [w] 0 body)) (σs : List Ty)
    (ws : List Word) : pubWords (close σs (.iex body)) ws = pubWords (close σs t) ws := by
  have e1 := (pubWords_subS h σs 0 0).2.1 ws
  have e2 := (pubWords_of_skel (skel_subst_eq (skel_instT [w] body 0).symm σs 0 1 0)).2.1 ws
  unfold close
  simp only [substTs]
  rw [pubWords_iex_eq, e2, e1]

theorem pubWords_packT {cx : Cx} {t body σ : Ty} {κ : Kind} (hg : body.guardT 0 = true)
    (h : SubS cx t (Ty.substT 0 σ body)) (σs : List Ty) (ws : List Word) :
    pubWords (close σs (.tex κ body)) ws = pubWords (close σs t) ws := by
  have e1 := (pubWords_subS h σs 0 0).2.1 ws
  have e2 := sig_pack σs body 0 0 σ hg
  unfold close
  simp only [substTs]
  rw [pubWords_tex_eq, e1, ← pubWords_sig, ← e2, pubWords_sig]

/-- The operand's binding, counted at a target type counting the same words. -/
theorem valB_retype {σs : List Ty} {sto : Sto} {s : St} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh}
    {v : At} {t rt τ : Ty} {ws : List Word} (he : evalAt th.env v = some (rt, ws)) (hl : Lay σs t rt ws)
    (heq : pubWords (close σs τ) ws = pubWords (close σs t) ws) : ValB sto s lb N th (close σs τ) ws := by
  refine valB_of_cntOld ?_
  rw [heq, ← pubWords_Lay hl]
  exact cntOld_evalAt he

theorem valB_fold {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y : String} {v : At} {τ : Ty} {e : Expr}
    (hT : ThInvE p E th) (hterm : th.term = .let_ y (.fold v τ) e)
    (h : r ∈ evalOp g th.env th.σs s (.fold v τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | fold _ hu hfo _ =>
      obtain ⟨-, rt, ws, he, -, hl⟩ := use_FInv hu hF
      simp [evalOp, ol] at h
      obtain ⟨t', ws', he', rfl⟩ := h
      rw [he] at he'
      simp only [Option.some.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact valB_retype he hl (pubWords_foldOK hfo _ _)

theorem valB_pack {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y wn : String} {v : At} {τ : Ty}
    {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .let_ y (.pack v wn τ) e)
    (h : r ∈ evalOp g th.env th.σs s (.pack v wn τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | pack _ _ hu _ hsub _ =>
      obtain ⟨-, rt, ws, he, -, hl⟩ := use_FInv hu hF
      simp [evalOp, ol] at h
      obtain ⟨t', ws', he', rfl⟩ := h
      rw [he] at he'
      simp only [Option.some.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact valB_retype he hl (pubWords_pack hsub _ _)

theorem valB_packT {p : Prog} {E : TEnv} {g : G} {s s1 : St} {r : St × Ty × List Word}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {th : TTh} {y : String} {v : At} {σ τ : Ty}
    {e : Expr} (hT : ThInvE p E th) (hterm : th.term = .let_ y (.packT v σ τ) e)
    (h : r ∈ evalOp g th.env th.σs s (.packT v σ τ)) : ValB sto s1 lb N th r.2.1 r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | packT hg _ _ hu _ hsub _ =>
      obtain ⟨-, rt, ws, he, -, hl⟩ := use_FInv hu hF
      simp [evalOp, ol] at h
      obtain ⟨t', ws', he', rfl⟩ := h
      rw [he] at he'
      simp only [Option.some.injEq, Prod.mk.injEq] at he'
      obtain ⟨rfl, rfl⟩ := he'
      exact valB_retype he hl (pubWords_packT hg hsub _ _)


/-! ## Frames: `call`, `tail`, `callc` (enter), `ret` -/

/-- A step whose bindings are old ones or new bindings with old counted words. -/
theorem stepB_sub {sto : Sto} {mem : Memory} {pairs : List Ts} {a : AllocLabel} {N : AllocLabel → Prop}
    {th th' : TTh} (bs : List (String × Ty × List Word)) (hsub : ∀ b ∈ Binds th', b ∈ bs ∨ b ∈ Binds th)
    (hb : ∀ b ∈ bs, CntOld th (pubWords b.2.1 b.2.2)) : StepB sto mem pairs a N th th' := by
  intro b hm
  rcases hsub b hm with h | h
  · exact .inr (newW_of_cntOld (hb b h))
  · exact .inl h

theorem stepB_call {p : Prog} {E : TEnv} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop}
    {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (hp : g.p = p) (hP : ProgT p) (hT : ThInvE p E th) (hterm : th.term = .let_ x (.call f is a ts) e)
    (hr : r ∈ tstep g mem pairs th) : StepB sto mem pairs lb N th r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | @call _ _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub _ =>
      obtain ⟨us, hlen, rfl, rfl⟩ := TermTv.instantiate_ok hinst
      have hd := find_ok hfind
      have hDT := hP d (List.mem_of_find?_eq_some hd)
      obtain ⟨hwa, -, -, -, -⟩ := id hDT
      obtain ⟨-, rt0, ws, hea, -, hl⟩ := use_FInv hu hF
      have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
      simp only [tstep, hterm, callFrame, enter, hp, hd, hea, Option.bind, bind, pure,
        Option.map_some, ol, Option.toList_some, List.mem_singleton] at hr
      subst hr
      refine stepB_sub [(d.arg, close (ts.map (close th.σs)).reverse d.argTy, ws)] (fun b hb => ?_) ?_
      · simp only [Binds, List.flatMap_cons, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · intro b hb
        simp only [List.mem_singleton] at hb
        subst hb
        show CntOld th (pubWords (close (ts.map (close th.σs)).reverse d.argTy) ws)
        have e : pubWords (close th.σs t) ws = pubWords (close th.σs (substTs ts.reverse 0 0 (instT us 0 d.argTy))) ws :=
          (pubWords_subS hsub th.σs 0 0).2.1 ws
        rw [← (pubWords_of_skel Ea).2.1, ← e, ← pubWords_Lay hl]
        exact cntOld_evalAt hea

theorem stepB_tail {p : Prog} {E : TEnv} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop}
    {f : String} {is : List String} {a : At} {ts : List Ty}
    (hp : g.p = p) (hP : ProgT p) (hT : ThInvE p E th) (hterm : th.term = .tail f is a ts)
    (hr : r ∈ tstep g mem pairs th) : StepB sto mem pairs lb N th r.2.2 := by
  obtain ⟨ρ, η, cx, -, -, hTy, -, hF, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | @tail _ _ _ _ _ _ d at_ rt t hfind hinst hu _ hsub _ =>
      obtain ⟨us, hlen, rfl, rfl⟩ := TermTv.instantiate_ok hinst
      have hd := find_ok hfind
      have hDT := hP d (List.mem_of_find?_eq_some hd)
      obtain ⟨hwa, -, -, -, -⟩ := id hDT
      obtain ⟨-, rt0, ws, hea, -, hl⟩ := use_FInv hu hF
      have Ea := skel_call th.σs ts us d.argTy (hlen ▸ TvB_skel _ _ _ hwa)
      simp only [tstep, hterm, enter, hp, hd, hea, Option.bind, bind, pure,
        Option.map_some, ol, Option.toList_some, List.mem_singleton] at hr
      subst hr
      refine stepB_sub [(d.arg, close (ts.map (close th.σs)).reverse d.argTy, ws)] (fun b hb => ?_) ?_
      · simp only [Binds, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h
        · exact .inl h
        · exact .inr (.inr h)
      · intro b hb
        simp only [List.mem_singleton] at hb
        subst hb
        show CntOld th (pubWords (close (ts.map (close th.σs)).reverse d.argTy) ws)
        have e : pubWords (close th.σs t) ws = pubWords (close th.σs (substTs ts.reverse 0 0 (instT us 0 d.argTy))) ws :=
          (pubWords_subS hsub th.σs 0 0).2.1 ws
        rw [← (pubWords_of_skel Ea).2.1, ← e, ← pubWords_Lay hl]
        exact cntOld_evalAt hea

/-- `ret`: **takes the frame link `hlink` as a hypothesis** (discharges it at dispatch): the
counted words of the returned value at the frame's type are counted words at the returned atom's
runtime type, with the same values and no larger `rts`. -/
theorem stepB_ret {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop} {a : At}
    (hterm : th.term = .ret a)
    (hlink : ∀ (f : Frame) (rest : List Frame) (rt : Ty) (ws : List Word), th.stack = f :: rest →
      evalAt th.env a = some (rt, ws) →
      ∀ w ∈ pubWords f.ty ws, ∃ w0 ∈ pubWords rt ws, w0.val = w.val ∧ w0.rts ≤ w.rts)
    (hr : r ∈ tstep g mem pairs th) : StepB sto mem pairs lb N th r.2.2 := by
  simp only [tstep, hterm] at hr
  split at hr
  · rename_i f rest rt ws hst hea
    simp only [List.mem_singleton] at hr
    subst hr
    refine stepB_sub [(f.x, f.ty, ws)] (fun b hb => ?_) ?_
    · simp only [Binds, hst, List.flatMap_cons, List.mem_append, List.mem_cons] at hb ⊢
      rcases hb with (h | h) | h
      · exact .inl (.inl h)
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr h))
    · intro b hb
      simp only [List.mem_singleton] at hb
      subst hb
      have hold := cntOld_evalAt hea
      intro w hw l hn
      obtain ⟨w0, h0, hv, hr0⟩ := hlink f rest rt ws hst hea w hw
      have hn0 : Names l w0 := by
        obtain ⟨a', g', e, hl⟩ := hn
        exact ⟨a', g', hv ▸ e, hl⟩
      obtain ⟨b, hb, w1, h1, hn1, hr1⟩ := hold w0 h0 l hn0
      exact ⟨b, hb, w1, h1, hn1, Nat.le_trans hr1 hr0⟩
  · cases hr


theorem stepB_callc {p : Prog} {E : TEnv} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} {sto : Sto} {lb : AllocLabel} {N : AllocLabel → Prop}
    {x : String} {f a : At} {e : Expr}
    (hp : g.p = p) (hP : ProgT p) (hT : ThInvE p E th) (hterm : th.term = .let_ x (.callc f a) e)
    (hr : r ∈ tstep g mem pairs th) : StepB sto mem pairs lb N th r.2.2 := by
  obtain ⟨ρ, η, cx, -, hE, hTy, htv, hi, -⟩ := hT
  rw [hterm] at hTy
  cases hTy with
  | let_ hop _ =>
    cases hop with
    | @callc c₁ _ _ _ _ tf σ τ t htf hc hu _ hsub hb =>
      obtain ⟨σ', τ', rfl⟩ : ∃ a b, tf = .code a b := by cases tf <;> simp_all [codeOf]
      simp only [codeOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨h1, h2⟩ := hc
      subst σ' τ'
      obtain ⟨rtf, wsf, hef, hvf, hlf⟩ := peek_VR hi.2.1 htf
      simp only [VR] at hvf
      obtain ⟨i, D, hwv, hpi, hfd, htp, hidx, lσ, -⟩ := hvf
      obtain ⟨w, rfl, hw⟩ := map_singleton hwv
      rw [hE.1] at hpi hfd
      have hDT := hP D (List.mem_of_find?_eq_some hfd)
      obtain ⟨hwa, -, -, -, -⟩ := id hDT
      have hwa' : D.argTy.wf 0 0 = true := by simpa [htp, hidx] using hwa
      have htbf := TermTv.peek_tb htv htf
      simp only [TermClose.tb, Bool.and_eq_true] at htbf
      have hoσ : cx.opaqueOK σ = true :=
        sub_opaqueOK hsub (TermTv.peek_opaqueOK htv (use_inv (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1)
      have hD : ∀ v : Ty, v.wf 0 0 = true → sig (clD v) = sig (close [] v) := fun v hv =>
        (sig_close_cl [] (fun _ => 0) (fun _ => .void) v 0 0 (fun k hk =>
          absurd (TermTv.lt_of_guardT (TermTv.tb_of_wf v hv) (Nat.le_refl 0) k (by simpa using hk))
            (Nat.not_lt_zero _))).symm
      have Ea : sig (close th.σs σ) = sig (close [] D.argTy) := by
        rw [sig_WitL hi.2.2.2.1 ρ hoσ (TermTv.lt_of_guardT htbf.1 hi.2.2.2.2.1), lσ, hD _ hwa']
      obtain ⟨-, rt0, ws, hea, -, hl⟩ := use_FInv hu hi
      simp only [tstep, hterm, hef, hw, hp, hpi, callFrame, enter, hfd, hea, retOf, Option.bind, bind, pure,
        Option.map_some, ol, Option.toList_some, List.map_nil, List.reverse_nil, List.mem_singleton] at hr
      subst hr
      refine stepB_sub [(D.arg, close [] D.argTy, ws)] (fun b hb => ?_) ?_
      · simp only [Binds, List.flatMap_cons, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
        rcases hb with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · intro b hb
        simp only [List.mem_singleton] at hb
        subst hb
        show CntOld th (pubWords (close [] D.argTy) ws)
        have e : pubWords (close th.σs t) ws = pubWords (close th.σs σ) ws := (pubWords_subS hsub th.σs 0 0).2.1 ws
        rw [← pubWords_sig, ← Ea, pubWords_sig, ← e, ← pubWords_Lay hl]
        exact cntOld_evalAt hea

end TermK2a

#print axioms TermK2a.pubWords_rf
#print axioms TermK2a.armsOf_len_skel
#print axioms TermK2a.armsOf_len_er
#print axioms TermK2a.pubWords_er
#print axioms TermK2a.pubWords_skel
#print axioms TermK2a.pubWords_sig
#print axioms TermK2a.pubArm_sig
#print axioms TermK2a.pubWords_of_skel
#print axioms TermK2a.pubWords_subS
#print axioms TermK2a.pubWords_iex_eq
#print axioms TermK2a.pubWords_tex_eq
#print axioms TermK2a.pubWords_foldOK
#print axioms TermK2a.pubWords_pack
#print axioms TermK2a.pubWords_packT
#print axioms TermK2a.valB_retype
#print axioms TermK2a.valB_fold
#print axioms TermK2a.valB_pack
#print axioms TermK2a.valB_packT
#print axioms TermK2a.stepB_sub
#print axioms TermK2a.stepB_call
#print axioms TermK2a.stepB_tail
#print axioms TermK2a.stepB_ret
#print axioms TermK2a.stepB_callc

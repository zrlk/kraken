import WeakCore.TermOwnX2
import WeakCore.TermPubW
import WeakCore.TermOwnHeldQ

/-!
# TermOwnK1 (own-key layer, package): frame/control steps and the promise step

* `ownXStep_k1`: `OwnXStepPkg … 1`, every term whose package is 1 (`exprPkg = 1`).  Such a term is
  in `StepScopeR` (`scopeR_of_pkg1`, from `ScopeAt`), so `tstepR_step` rebuilds the resourceful frame
  at the **same** code view `CE η`, with the bound moved only as `TotStep` allows (no own key is
  minted), and `frame_keep` keeps memory, the promises and `MemInv` at `CE η`; the private holding
  carries over unchanged (`TermOwnHeldQ.memHeldOn_eqs`).
* `ownXStepP_all`: `OwnXStepP`, any `n`.  A promise at a private unit is skipped as
  `promises ++ FpAt`, so the private holding is unchanged (`memHeldP_promSt`); `MemInv_promSt`.
-/

namespace TermOwnK1
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermCert TermSound TermMem TermFul TermStep TermGlob
  TermCut TermSys TermTyped TermMain TermOwnX2 TermOwnHeldQ
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **A package-1 term in the run scope is in the frame scope** (`pack` is typed at an `iex`). -/
theorem scopeR_of_pkg1 {p : Prog} {σs : List Ty} {cx : Cx} {t : Expr} (hT : Typed p cx t)
    (hq : exprPkg t = 1) (hs : ScopeD σs cx t) : StepScopeR σs cx t := by
  rcases hs with hs | ⟨hs, -⟩
  · cases hT with
    | let_ hop _ =>
      cases hop
      all_goals first
        | (simp [exprPkg, opPkg] at hq; done)
        | exact trivial
        | exact (show False from hs).elim
        | exact hs
    | _ =>
      first
        | (simp [exprPkg] at hq; done)
        | exact trivial
        | exact hs
  · exact hs

/-- **The private holding survives a promise step**: a private unit is neither visible nor
predicted, so its skipped promises are `promises ++ FpAt`, and the new index is skipped too. -/
theorem memHeldP_promSt {E : TEnv} {s : St} {H : Res} {a : Address} {v : WeakMem.Val} {w : Ts}
    (h : MemHeldP E s H) : MemHeldP E (promSt s a v w) H := by
  obtain ⟨L, Rl, hnd, hc, hq, hH, hR⟩ := h
  refine ⟨L, Rl, hnd, hc, hq, hH, fun l hl => ⟨(hR l hl).1, fun c hc' => ?_⟩⟩
  obtain ⟨vals, hv, hok⟩ := (hR l hl).2 c hc'
  have hP : Priv E l := hq l hl
  refine ⟨vals, fun o y hy => ?_, hok⟩
  have hnV : ¬ VisU E ⟨l, o⟩ := fun h => h.2 hP
  have hnQ : ¬ PredU E ⟨l, o⟩ := fun h => h.1 hP.2
  have h0 := hv o y hy
  rw [PromAt_nword hnV hnQ] at h0
  rw [PromAt_nword hnV hnQ, promSt_mem, promSt_promises]
  refine LatestNP_congrP (fun t _ _ _ => ?_) (LatestNP_push_prom _ h0)
  simp only [List.mem_append]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)

/-- A frame-only step mints no own key: `TotStep` moves the bound at `own x` down or not at all. -/
theorem totStep_own_le {t : Expr} {η : TEnv} {T T' : Res} (h : TotStep t η T T') (x : AllocLabel) :
    T' (.own x) ≤ T (.own x) := by
  cases h with
  | same => exact Nat.le_refl _
  | fresh => simp [Res.add_apply, Res.one_apply]
  | claim n j _ hle =>
    have h1 := Res.le_def.1 hle (.own x)
    simp [Res.add_apply, Res.one_apply] at h1
    exact h1

/-- `StoNIE` along the weak footprint (`EFootW` keeps `noIallV` at fresh cells). -/
theorem stoNIE_efootW {g : G} {E E' : TEnv} {s s' : St} (hf : EFootW g E E' s s') (h : StoNIE E) :
    StoNIE E' := by
  intro l cl hl
  rcases hf.2.2.1 l with he | ⟨-, T, hT, ⟨-, -, hn⟩, -⟩
  · exact h l cl (he ▸ hl)
  · rw [hT] at hl; cases hl; exact hn

theorem stoNIE_footW {g : G} {E E' : TEnv} {s s' : St} (hf : FootW g E E' s s') (h : StoNIE E) : StoNIE E' :=
  stoNIE_efootW hf.1 h

/-- **K1: the frame/control package.** -/
theorem ownXStep_k1 {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel}
    [ProgRetIall p] [TermA4.ProgCkWC p] (hP : ProgT p) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) : ∀ n, OwnXStepPkg p k arch i x n 1 := by
  intro n E0 c0 c0' th hth hq hsc _ _ hI hs _
  obtain ⟨th0, E, Tot, HP, hth0, hT, hm, hHP, hb, hni, hsx, hle, hx0, hA⟩ := hI
  obtain rfl : th0 = th := Option.some.inj (hth0.symm.trans hth)
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hE, hTy, htv, hFI, hsum, hRP⟩ := hT
  subst hCE
  have hFI0 : FInv ρ η th0.σs (Resume p th0.stack) cx th0.env :=
    FInvR_FInv htv.2.2.2.2.2.2.2
      (fun E rd ws R h => ResumeR_Resume (fun _ h => h.2.2.2.2.2.2.2) th0.stack Rs E rd ws R h) hFI
  have hR := scopeR_of_pkg1 hTy.1 hq (hsc th0 hth (TermTyped.not_spawnT_of_steps hth hs) ρ η cx hE hTy.1 htv hFI0)
  obtain ⟨th1, r, hth1, hr, e1, e2, e3, -⟩ := threadSteps_inv hs
  obtain rfl : th1 = th0 := Option.some.inj (hth1.symm.trans hth)
  obtain ⟨Tot', hT', hts⟩ := (tstepR_step hP rfl (tstep_notDone hr) hR hTy.1 hTy.2 hFI hE htv hRP hPS hSub hSig).2 r hr
  obtain ⟨em, ep, hm'⟩ := frame_keep hR hTy.1 hTy.2 hFI hE htv hm r hr
  have hg := gOf_thread hs
  have h0 := totStep_own_le hts x
  rw [hsum] at h0
  refine ⟨r.2.2, CE η, Tot', HP, e3, hT', ?_, ?_, ?_, hni, hsx, by omega, hx0, ?_⟩
  · rw [hg, e1, e2]; exact hm'
  · rw [e1, e2]; exact memHeldOn_eqs hHP em ep
  · rw [hg]; exact hb
  · rw [e1, e2]; exact anchR_eqs hA em ep

/-- **K1: the promise step**, any bound. -/
theorem ownXStepP_all {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {x : AllocLabel} :
    ∀ n, OwnXStepP p k arch i x n := by
  intro n E0 c0 a v w h _ _
  obtain ⟨th, E, Tot, HP, hth, hT, hm, hHP, hb, hni, hsx, hle, hx0, hA⟩ := h
  obtain ⟨-, h2, h3⟩ := promise_inv (a := a) (v := v) (w := w) hth
  refine ⟨_, E, Tot, HP, h2, hT, ?_, ?_, ?_, hni, hsx, hle, hx0, anchR_prom hth hA⟩
  · rw [gOf_promise, h3]; exact MemInv_promSt hm
  · rw [h3]; exact memHeldP_promSt hHP
  · rw [gOf_promise]; exact hb

end TermOwnK1

#print axioms TermOwnK1.scopeR_of_pkg1
#print axioms TermOwnK1.memHeldP_promSt
#print axioms TermOwnK1.totStep_own_le
#print axioms TermOwnK1.stoNIE_efootW
#print axioms TermOwnK1.stoNIE_footW
#print axioms TermOwnK1.ownXStep_k1
#print axioms TermOwnK1.ownXStepP_all

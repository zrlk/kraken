import WeakCore.TermK2aMain
import WeakCore.TermK2aLdW
import WeakCore.TermK2aRmw
import WeakCore.TermK2aSum
import WeakCore.TermK2aLink
import WeakCore.TermLocal

/-!
# TermK2aDisp: the K-2a dispatch

Every in-scope thread step other than `ret` meets the step contract `StepOK` (`stepOK_disp`),
by cases on the typing derivation, in the shape of `TermStep.tstepMF_step`.  Pure, store and
allocation ops go through `A2`'s `valB_*` at the empty store typing (`stepOK_op`); loads and
read-modify-writes through the per-op load contracts; sums, `publish` and regions through
`TermK2aSum`.
-/

namespace TermK2aDisp

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermCert TermGlob TermTyped
open TermPtrRts TermOwnG0Defs TermK2a TermK2aLd TermK2aMain
open TermCut (GEnv)
open TermClose (cl tb arrFree_cl)
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **A `let` of a non-call op** whose every result is fine at the empty store typing meets the
step contract. -/
theorem stepOK_op {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {x : String} {op : Op} {e : Expr}
    {sto : Sto} {ga : AllocLabel} {Gl : AllocLabel → Prop}
    (hterm : th.term = .let_ x op e) (hc : Robust.isCallOp op = false)
    (hv : ∀ r ∈ evalOp g th.env th.σs (stOf mem pairs th) op,
      ValB (fun _ => none) (stOf mem pairs th) ga Gl th r.2.1 r.2.2) :
    ∀ r ∈ tstep g mem pairs th, StepOK sto (stOf mem pairs th) ga Gl Gl th r.2.2 := by
  intro r hr
  rw [TermLocal.tstep_let_gen hterm hc] at hr
  obtain ⟨⟨s', t, ws⟩, hm, rfl⟩ := List.mem_map.1 hr
  exact stepOK_of_stepB_nil (stepB_let (x := x) rfl rfl (hv _ hm))

/-- A non-capability term in the run scope is in the plain scope. -/
theorem scope_of {σs : List Ty} {cx : Cx} {t : Expr} (h : ScopeD σs cx t) (hn : ¬ CapT t) :
    StepScope cx t :=
  h.elim id fun h => (hn h.2).elim

theorem notCap_let {x : String} {op : Op} {e : Expr}
    (h : ∀ a b, op ≠ .borrow a b) (h2 : ∀ a, op ≠ .freeze a) (h3 : ∀ a, op ≠ .endBorrow a) :
    ¬ CapT (.let_ x op e) := by
  rintro ⟨x', e', ⟨a, b, he⟩ | ⟨a, he⟩ | ⟨a, he⟩⟩ <;> cases he
  · exact h a b rfl
  · exact h2 a rfl
  · exact h3 a rfl

/-- **The K-2a dispatch** (all terms but `ret`). -/
theorem stepOK_disp {p : Prog} {g : G} {E : TEnv} {sto : Sto} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ga : AllocLabel} {r : Memory × List Ts × TTh} {Gl : AllocLabel → Prop}
    (hp : g.p = p) (hP : ProgT p) (hI : ThInvE p E th) (hM : MemInv g E (stOf mem pairs th))
    (h1 : ∀ l c, E.sto l = some c → sto l = some c) (hLay : ∀ l c, sto l = some c → LayT c.ty)
    (hG : GranuleWP sto mem pairs th.promises)
    (hPf : ∀ l f, E.pfr l = some f → Gl l) (hBx : ∀ l B, E.box l = some B → Gl l)
    (hsc : ScopeOK p th) (hnr : ∀ a, th.term ≠ .ret a)
    (hfa : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l → l ≠ ga)
    (hGf : ∀ l, FreshIn g th.nalloc r.2.2.nalloc l →
      (∃ b ∈ r.2.2.env, ∃ w ∈ pubWords b.2.1 b.2.2, Names l w) → Gl l)
    (hnp : ¬ PubAt th ga) (hGp : ∀ l, PubAt th l → Gl l)
    (hArm : ∀ a x e₁ y e₂, th.term = .case a x e₁ y e₂ → ∀ ra rb ws, evalAt th.env a = some (.sum ra rb, ws) →
      (Ty.sum ra rb).tier = .boxed → TermK2aSum.BoxArmOK g (stOf mem pairs th) sto ga Gl Gl th (.sum ra rb) ws)
    (hr : r ∈ tstep g mem pairs th) (hA : PromAbove (stOf r.1 r.2.1 r.2.2)) :
    StepOK sto (stOf mem pairs th) ga Gl Gl th r.2.2 := by
  have hI0 := hI
  obtain ⟨ρ, η, cx, rfl, hE, hT, htv, hi, -⟩ := hI
  have hsd := hsc ρ η cx hE hT htv hi
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsd
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | atom => exact stepOK_op ht rfl (fun _ h => valB_atom h) r hr
    | pair => exact stepOK_op ht rfl (fun _ h => valB_pair hI0 ht h) r hr
    | addS => exact stepOK_op ht rfl (fun _ h => valB_add h) r hr
    | addI => exact stepOK_op ht rfl (fun _ h => valB_add h) r hr
    | subS => exact stepOK_op ht rfl (fun _ h => valB_sub h) r hr
    | pack => exact stepOK_op ht rfl (fun _ h => valB_pack hI0 ht h) r hr
    | packT => exact stepOK_op ht rfl (fun _ h => valB_packT hI0 ht h) r hr
    | rem => exact stepOK_op ht rfl (fun _ h => valB_rem h) r hr
    | nameI => exact stepOK_op ht rfl (fun _ h => valB_nameI h) r hr
    | bits => exact stepOK_op ht rfl (fun _ h => valB_bits h) r hr
    | bit1 => exact stepOK_op ht rfl (fun _ h => valB_bit1 h) r hr
    | vmatch => exact stepOK_op ht rfl (fun _ h => valB_vmatch h) r hr
    | band => exact stepOK_op ht rfl (fun _ h => valB_band h) r hr
    | cvt => exact stepOK_op ht rfl (fun _ h => valB_cvt h) r hr
    | toInt => exact stepOK_op ht rfl (fun _ h => valB_toInt h) r hr
    | asLanes => exact stepOK_op ht rfl (fun _ h => valB_asLanes h) r hr
    | fop => exact stepOK_op ht rfl (fun _ h => valB_fop h) r hr
    | fcmp => exact stepOK_op ht rfl (fun _ h => valB_fcmp h) r hr
    | fop1 => exact stepOK_op ht rfl (fun _ h => valB_fop1 h) r hr
    | lane => exact stepOK_op ht rfl (fun _ h => valB_lane h) r hr
    | setLane => exact stepOK_op ht rfl (fun _ h => valB_setLane h) r hr
    | inl => exact TermK2aSum.sum_inlTR ht hT hi sto hr hfa hGf hGf
    | inr => exact TermK2aSum.sum_inrTR ht hT hi sto hr hfa hGf hGf
    | new => exact stepOK_op ht rfl (fun _ h => valB_new h) r hr
    | publish | publishBuf => exact TermK2aSum.pub_publish ht hT hi sto hnp hGp hGp r hr
    | intoRgn | intoRgnBuf => exact stepOK_op ht rfl (fun _ h => valB_intoRgn h) r hr
    | newBuf => exact stepOK_op ht rfl (fun _ h => valB_newBuf h) r hr
    | idxOwn | idxShared => exact stepOK_op ht rfl (fun _ h => valB_idx h) r hr
    | bufInit => exact stepOK_op ht rfl (fun _ h => valB_bufInit h) r hr
    | null => exact stepOK_op ht rfl (fun _ h => valB_null h) r hr
    | fldOwn | fldShared => exact stepOK_op ht rfl (fun _ h => valB_fld h) r hr
    | fence => exact stepOK_op ht rfl (fun _ h => valB_fence h) r hr
    | zero => exact stepOK_op ht rfl (fun _ h => valB_zero h) r hr
    | spawn => exact stepOK_op ht rfl (fun _ h => by simp [evalOp] at h) r hr
    | call => exact stepOK_of_stepB_nil (stepB_call hp hP hI0 ht hr)
    | fnptr => exact stepOK_op ht rfl (fun _ h => valB_fnptr h) r hr
    | callc => exact stepOK_of_stepB_nil (stepB_callc hp hP hI0 ht hr)
    | xchgAt => exact stepOK_of_ldOK (TermK2aRmw.rmw_xchgAt ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadAt => exact stepOK_of_ldOK (TermK2aLdW.ld_at ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | xchgAtF => exact stepOK_of_ldOK (TermK2aRmw.rmw_xchgAtF ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadAtF => exact stepOK_of_ldOK (TermK2aLdW.ld_atF ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | ldlw => exact stepOK_of_ldOK (TermK2aLdW.ld_lw ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | ldl => exact stepOK_of_ldOK (TermK2aLdW.ld_l ht hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | stlw => exact stepOK_op ht rfl (fun _ h => valB_stlw h) r hr
    | stl => exact stepOK_op ht rfl (fun _ h => valB_stl h) r hr
    | fold => exact stepOK_op ht rfl (fun _ h => valB_fold hI0 ht h) r hr
    | mkWord => exact stepOK_op ht rfl (fun _ h => valB_mkWord hI0 ht h) r hr
    | mkWordGhost => exact stepOK_op ht rfl (fun _ h => valB_mkWord hI0 ht h) r hr
    | validate => exact stepOK_op ht rfl (fun _ h => valB_validate h) r hr
    | borrow => exact stepOK_op ht rfl (fun _ h => valB_borrow h) r hr
    | freeze => exact stepOK_op ht rfl (fun _ h => valB_freeze h) r hr
    | endBorrow => exact stepOK_op ht rfl (fun _ h => valB_endBorrow h) r hr
    | mkWord2 => exact stepOK_op ht rfl (fun _ h => valB_mkWord2 hI0 ht h) r hr
    | mkEPair => exact stepOK_op ht rfl (fun _ h => valB_mkEPair hI0 ht h) r hr
    | mkTicket => exact stepOK_op ht rfl (fun _ h => valB_mkTicket hI0 ht h) r hr
    | claim => exact stepOK_op ht rfl (fun _ h => valB_claim h) r hr
    | stpGive | stpKeep => exact stepOK_op ht rfl (fun _ h => valB_stp h) r hr
    | storeWordGive | storeWordKeep | storeWordHand | storeOwn | storePub | storeRgn | storeCap =>
        exact stepOK_op ht rfl (fun _ h => valB_store h) r hr
    | ldp hpk =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hs _ hpk
        · rw [hteq] at hpk
          rcases hμ with rfl | rfl
          · exact stepOK_of_ldOK
              (TermK2aLdW.ld_pOwn ht hu hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          · exact stepOK_of_ldOK
              (TermK2aLdW.ld_pPub ht hu hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · rw [hteq] at hpk
          exact stepOK_of_ldOK
            (TermK2aLdW.ld_pLoc ht hu hpk hμ hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | fetchCell hpk | fetchEpoch hpk | fetchShare hpk =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        obtain ⟨μ, u, hteq | hteq, hμ⟩ := hs _ hpk
        · rw [hteq] at hpk
          exact stepOK_of_ldOK (TermK2aRmw.rmw_fetch ht hpk hμ hT hi hE htv hM ga Gl r hr hA)
        · rw [hteq] at hpk
          exact stepOK_of_ldOK (TermK2aRmw.rmw_fetchLoc ht hpk hμ hT hi hE htv hM ga Gl r hr hA)
    | loadWord hpk hw =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact stepOK_of_ldOK
                    (TermK2aLdW.ld_wordOwn ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          | pub => exact stepOK_of_ldOK
                    (TermK2aLdW.ld_wordPub ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          | rgn r' => exact ((hs _ hpk) r' _ rfl).elim
        · cases μ with
          | own => exact stepOK_of_ldOK
                    (TermK2aLdW.ld_wordLoc ht hpk (.inl rfl) hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          | pub => exact stepOK_of_ldOK
                    (TermK2aLdW.ld_wordLoc ht hpk (.inr rfl) hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
          | rgn r' => exact ((hs _ hpk) r' _ rfl).elim
    | loadRgn hpk _ hc | loadCap hpk _ hc | loadTorn hpk _ hc =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        exact absurd hc (hs _ hpk _ _)
    | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact stepOK_of_ldOK (ld_own ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · exact stepOK_of_ldOK (ld_loc ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact stepOK_of_ldOK (ld_pub ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        · exact stepOK_of_ldOK (ld_pubLoc ht hpk hnw hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
    | xchg hpk hx =>
        have hs := scope_of hsd (notCap_let (by intros; simp) (by intros; simp) (by intros; simp))
        cases hx with
        | own _ hc =>
            rcases cell_cases hc with rfl | rfl
            · exact stepOK_of_ldOK
                (TermK2aRmw.rmw_xchgOwn ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
            · exact stepOK_of_ldOK
                (TermK2aRmw.rmw_xchgLoc ht hpk hT hi hE htv hM h1 hLay hG hPf hBx ga Gl r hr hA)
        | rgn _ hc => exact absurd hc (hs _ hpk _ _)
  | split => exact stepOK_of_stepB_nil (stepB_split ht hr)
  | unpack => exact stepOK_of_stepB_nil (stepB_unpack ht hr)
  | unpackT => exact stepOK_of_stepB_nil (stepB_unpackT hI0 ht hr)
  | ifnull => exact stepOK_of_stepB_nil (stepB_ifnull ht hr)
  | parity => exact stepOK_of_stepB_nil (stepB_parity ht hr)
  | ifeqPlain | ifeq | ifeqRec | ifeqZero => exact stepOK_of_stepB_nil (stepB_ifeq ht hr)
  | case => exact TermK2aSum.sum_caseTR ht hT hi htv sto (hArm _ _ _ _ _ ht) hr hfa hGf hGf
  | region | regionBuf => exact TermK2aSum.rgn_region ht sto Gl ga Gl r hr
  | openPub => exact TermK2aSum.rgn_openPub ht sto Gl ga Gl r hr
  | casCell | casShare | casTake | casEpoch => exact TermK2aRmw.rmw_casWord ht ga Gl r hr hA
  | caspMove | caspTake | caspE | caspBump => exact TermK2aRmw.rmw_casp ht ga Gl r hr hA
  | ret => exact (hnr _ ht).elim
  | tail => exact stepOK_of_stepB_nil (stepB_tail hp hP hI0 ht hr)

end TermK2aDisp

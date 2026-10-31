import WeakCore.WrIniInst
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
set_option autoImplicit false
set_option maxErrors 100000
-- PORTB TermSound.lean:11490 ThInvRE.thInvE
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem ThInvREB.thInvE {p : Prog} {E : TEnv} {th : TTh} {Tot : Res}
    (h : ThInvREB glb gnum gi p E th Tot) : ThInvEB glb gnum gi p E th := by
  have hT : ∀ c : Cx, TvOK c → noIallV c.ret = true := fun _ h => h.2.2.2.2.2.2.2
  obtain ⟨ρ, η, cx, Rf, Rs, hCE, hEO, hTy, hTv, hF, -, hpw, hDy⟩ := h
  exact ⟨ρ, η, cx, hCE, hEO, hTy.1, hTv,
    FInvR_FInvB (hT cx hTv) (fun E rd ws R h => ResumeR_ResumeB hT th.stack Rs E rd ws R h) hF, hpw, hDy⟩
end
end TermSound.Flat

-- PORTB TermSound.lean:15663 VR_ren0
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VRzE_pubTop_sto {bk : Prop} {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {ws : List Word} {w : Word}
    {x : WeakMem.Address}
    (hv : ws.map (·.val) = [w].map (·.val)) (hw : w.val = .loc x 0)
    (hs : η.sto x.label = none) (hp : t.pubHead = true) (h : VRz ρ η bk t rt ws) : False := by
  cases t with
  | ptr μ u =>
      simp only [VRz, hv, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      obtain ⟨a, c, ha, _, hc, _⟩ := h; cases ha; rw [hs] at hc; cases hc
  | ptrOpt μ u =>
      simp only [VRz, hv, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      rcases h with h | ⟨a, c, ha, _, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | loc μ u =>
      simp only [VRz, hv, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      rcases h with ⟨h, _⟩ | ⟨a, c, _, ha, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | _ => simp [Ty.pubHead] at hp
theorem VRFE_pubTop_sto {bk : Prop} {ρ : Nat → Nat} {η : TEnv} {t : Ty} {rt : Shp} {w : Word} {x : WeakMem.Address}
    (hr : ∀ k S ws, ¬ η.rels k S ws) (hw : w.val = .loc x 0) (hs : η.sto x.label = none)
    (hp : η.pubTop t = true) (h : VRF bk ρ η t rt [w]) : False := by
  cases t with
  | tvar k =>
      simp only [VRF, VRb2, TEnv.get] at h
      obtain ⟨w0, hle, h | ⟨h, -⟩⟩ := h
      · exact hr _ _ _ h
      · have hv : w0.map (·.val) = [w].map (·.val) := hle.vals
        exact VRzE_pubTop_sto hv hw (by simpa [CE] using hs) hp h
  | ptr μ u =>
      simp only [VRF, VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      obtain ⟨a, c, ha, _, hc, _⟩ := h; cases ha; rw [hs] at hc; cases hc
  | ptrOpt μ u =>
      simp only [VRF, VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      rcases h with h | ⟨a, c, ha, _, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | loc μ u =>
      simp only [VRF, VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      rcases h with ⟨h, _⟩ | ⟨a, c, _, ha, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | _ => simp [TEnv.pubTop, Ty.pubHead] at hp
end
end TermSound.Flat
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
theorem push0_rels_none {η : TEnv} {s : Ty} (hr : ∀ k S ws, ¬ η.rels k S ws) :
    ∀ k S ws, ¬ (η.push0 s).rels k S ws := by
  intro k S ws h
  cases k with
  | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h)
theorem VRF_pp_box {w : Word} {x : WeakMem.Address} (hw : w.val = .loc x 0) (bx : WeakMem.AllocLabel → Option Box) :
    ∀ (t : Ty) (bk : Prop) (η : TEnv) (ρ : Nat → Nat) (PT : Nat → Shp → List Word → Nat → Bool) (R : Shp) (s : Nat),
      (∀ k S ws, ¬ η.rels k S ws) → η.sto x.label = none → (∀ l B, η.box l = some B → bx l = some B) → bh R →
      VRb2 ρ η bk t (vsh s R) [w] → pp PT bx t (vsh s R) [w] 0 = false := by
  intro t
  induction t with
  | tvar k =>
    intro bk η ρ PT R s hr _ _ _ h
    simp only [VRb2, TEnv.get] at h
    obtain ⟨_, _, h | ⟨-, _, _, h⟩⟩ := h <;> exact absurd h (hr _ _ _)
  | ptr μ u _ =>
    intro bk η ρ PT R s _ hs _ _ h
    cases μ with
    | pub =>
      exfalso
      simp only [VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      obtain ⟨a, c, ha, _, hc, _⟩ := h; cases ha; rw [hs] at hc; cases hc
    | _ => rfl
  | ptrOpt μ u _ =>
    intro bk η ρ PT R s _ hs _ _ h
    cases μ with
    | pub =>
      exfalso
      simp only [VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      rcases h with h | ⟨a, c, ha, _, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
    | _ => rfl
  | loc μ u _ =>
    intro bk η ρ PT R s _ hs _ _ h
    cases μ with
    | pub =>
      exfalso
      simp only [VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
      rcases h with ⟨h, _⟩ | ⟨a, c, _, ha, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
    | _ => rfl
  | tid =>
    intro bk η ρ PT R s _ hs _ _ h
    exfalso
    simp only [VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at h
    obtain ⟨l, c, hv, hc, -⟩ := h
    cases hv
    have : η.sto l = none := hs
    rw [this] at hc; cases hc
  | refine t ψ ih =>
    intro bk η ρ PT R s hr hs hbx hR h
    simp only [VRb2] at h; simp only [pp]; exact ih bk η ρ PT R s hr hs hbx hR h.1
  | iall t ih =>
    intro bk η ρ PT R s hr hs hbx hR h
    simp only [VRb2] at h; simp only [pp]; exact ih bk η (vcons 0 ρ) PT R s hr hs hbx hR (h 0)
  | mu t ih =>
    intro bk η ρ PT R s hr hs hbx hR h
    simp only [VRb2] at h; simp only [pp]
    exact ih bk _ ρ (shPT PT) R s (push0_rels_none hr) hs hbx hR h
  | iex t ih =>
    intro bk η ρ PT R s hr hs hbx hR h
    cases R with
    | iex n0 R' =>
      simp only [VRb2, vsh] at h ⊢
      obtain ⟨n, rb, w', he, h⟩ := h
      cases he
      simp only [pp]
      exact ih bk η _ PT R' s hr hs hbx hR h
    | _ => simp [VRb2, vsh] at h
  | tex κ t ih =>
    intro bk η ρ PT R s hr hs hbx hR h
    cases R with
    | tex n0 R' =>
      simp only [VRb2, vsh] at h ⊢
      obtain ⟨n, rb, s', he, -, -, h⟩ := h
      cases he
      simp only [pp]
      exact ih bk _ ρ (shPT PT) R' s (push0_rels_none hr) hs hbx hR h
    | _ => simp [VRb2, vsh] at h
  | prod a b _ _ =>
    intro bk η ρ PT R s _ _ _ hR h
    simp only [VRb2] at h
    obtain ⟨ra, rb, he, -⟩ := h
    cases R with
    | prod a' b' => exact absurd hR (by simp [bh])
    | _ => simp [vsh] at he
  | sum a b iha ihb =>
    intro bk η ρ PT R s hr hs hbx hR h
    cases R with
    | sum n0 R0 =>
      simp only [VRb2, vsh] at h
      obtain ⟨n, Ra, Rb, he, hc⟩ := h
      cases he
      have htb : (Ty.sum Ra Rb).tier = .boxed := hR
      rcases hc with ⟨-, x', s', B, hv, -, hB, hn, -, -, hA, hB'⟩ | ⟨j, p, hd, -, -⟩
      · have hx : x' = x := by
          simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, hw] at hv
          cases hv; rfl
        subst hx
        have hs' : s' = s := by simp at hn; omega
        subst hs'
        simp only [vsh, pp, htb, if_true, List.map_cons, List.map_nil, hw, hbx _ _ hB]
        by_cases hlt : B.tag - s' < (armsOf Ra).length
        · simp only [hlt, if_true]
          by_cases hbr : isBoxed Ra = true
          · simp only [hbr, if_true]; exact iha _ η ρ PT (shp Ra) s' hr hs hbx (bh_shp Ra hbr) ((hA hlt).1 hbr)
          · simp only [hbr]; rfl
        · simp only [hlt, if_false]
          by_cases hbr : isBoxed Rb = true
          · simp only [hbr, if_true]
            exact ihb _ η ρ PT (shp Rb) (s' + (armsOf Ra).length) hr hs hbx (bh_shp Rb hbr) ((hB' (by omega)).1 hbr)
          · simp only [hbr]; rfl
      · rw [htb] at hd; simp [decodeArm] at hd
    | _ => simp [VRb2, vsh] at h
  | _ => intro bk η ρ PT R s _ _ _ _ _; rfl
theorem VRF_PubPosE_box {bk : Prop} {η : TEnv} {t : Ty} {w1 w2 : Word} {x1 x2 : WeakMem.Address} {B1 B2 : Box}
    {R : Shp} {s1 s2 : Nat} {ρ : Nat → Nat} (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0)
    (hb1 : η.box x1.label = some B1) (hb2 : η.box x2.label = some B2) (ht : B1.tag + s2 = B2.tag + s1)
    (hr : ∀ k S ws, ¬ η.rels k S ws) (hs : η.sto x1.label = none) (hR : bh R) (h : VRb2 ρ η bk t (vsh s1 R) [w1])
    (hp : PubPosE η t (vsh s2 R) [w2]) : False := by
  obtain ⟨bx, hbx, hq⟩ := PubPosE_ren h1 h2 hb1 hb2 ht hR hp
  rw [VRF_pp_box h1 bx t bk η ρ _ R s1 hr hs hbx hR h] at hq
  cases hq
theorem VR_ren0B (w1 w2 : Word) (x1 x2 : WeakMem.Address) (B1 B2 : Box)
    (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0) (ho2 : x2.offset = 0)
    (hpay : WLe B1.pay B2.pay) :
    ∀ (t : Ty) (η : TEnv) (ρ : Nat → Nat) (R : Shp) (s1 s2 : Nat),
      B1.tag + s2 = B2.tag + s1 →
      (∀ k S ws, ¬ η.rels k S ws) → bh R →
      η.box x1.label = some B1 → η.box x2.label = some B2 → η.sto x1.label = none →
      η.ini x1.label ≤ η.ini x2.label → min (η.ini x1.label) (η.rini x1.label) ≤ η.rini x2.label → (BoxSeen η x2.label B2 ∨ B2.fr ≤ w2.view) →
      (VRF False) ρ η t (vsh s1 R) [w1] → (VRF False) ρ η t (vsh s2 R) [w2] := by
  intro t
  induction t with
  | unit | array | share | cap | tok | tok2 | tokE => intros; simp [VRF, VRb2]
  
  | word2 | epair =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp [VRF, VRb2] at h
  | word r P =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp only [VRF, VRb2] at h ⊢
      refine ⟨h.1, fun hg => ?_⟩
      obtain ⟨n, hn, _⟩ := h.2 hg
      simp [h1] at hn
  | iall b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VRF, VRb2] at h ⊢
      exact fun n => ih η (vcons n ρ) R s1 s2 ht hr hR hb1 hb2 hs hi hri hm (h n)
  | void => intros; simp_all [VRF, VRb2]
  | int => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VRF, VRb2, h1] at h
  | tid =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VRF, VRb2] at h
      obtain ⟨l, c, he, hc, -⟩ := h
      simp only [List.map_cons, List.map_nil, h1, List.cons.injEq] at he
      have hl : x1.label = l := by cases he.1; rfl
      rw [hl, hc] at hs; cases hs
  | intS => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VRF, VRb2, h1] at h
  | opq => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VRF, VRb2, h1] at h
  | code => intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h; simp [VRF, VRb2, h1] at h
  | tvar k => intro η ρ R s1 s2 _ hr _ _ _ _ _ _ _ h; simp only [VRF, VRb2, TEnv.get] at h; obtain ⟨_, _, h | ⟨-, _, _, h⟩⟩ := h <;> exact absurd h (hr _ _ _)
  | ptr _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VRF, VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at h
      obtain ⟨a, c, ha, _, hc, _⟩ := h; cases ha; rw [hs] at hc; cases hc
  | ptrOpt _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VRF, VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at h
      rcases h with h | ⟨a, c, ha, _, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | loc _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ hs _ _ _ h
      simp only [VRF, VRb2, List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at h
      rcases h with ⟨h, _⟩ | ⟨a, c, _, ha, hc, _⟩
      · cases h
      · cases ha; rw [hs] at hc; cases hc
  | fix _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp only [VRF, VRb2] at h; obtain ⟨_, n, hn, _⟩ := h; simp [h1] at hn
  | lanes _ _ =>
      intro η ρ R s1 s2 _ _ _ _ _ _ _ _ _ h
      simp only [VRF, VRb2] at h; obtain ⟨_, n, hn⟩ := h; simp [h1] at hn
  | refine t ψ ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VRF, VRb2] at h ⊢
      refine ⟨ih η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h.1, IniR_ren h1 h2 (TEnv.selIni_le_at η t hi hri) ψ h.2.1,
        fun hp => (VRF_PubPosE_box h1 h2 hb1 hb2 ht hr hs hR h.1 hp).elim⟩
  | mu b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VRF, VRb2] at h ⊢
      refine ih _ ρ R s1 s2 ht ?_ hR hb1 hb2 hs hi hri hm h
      intro k S ws hk
      cases k with
      | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
      | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)
  | prod a b _ _ =>
      intro η ρ R s1 s2 _ _ hR _ _ _ _ _ _ h
      simp only [VRF, VRb2] at h
      obtain ⟨ra, rb, hr, _⟩ := h
      cases R <;> simp_all [vsh, bh]
  | iex b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VRF, VRb2] at h ⊢
      obtain ⟨n, rb, w, hrt, hv⟩ := h
      cases R with
      | iex m r0 =>
          simp only [vsh, Shp.iex.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          exact ⟨m, vsh s2 r0, w, rfl, ih η _ r0 s1 s2 ht hr hR hb1 hb2 hs hi hri hm hv⟩
      | _ => simp [vsh] at hrt
  | tex κ b ih =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VRF, VRb2] at h ⊢
      obtain ⟨n, rb, s, hrt, hc, hk, hv⟩ := h
      cases R with
      | tex m r0 =>
          simp only [vsh, Shp.tex.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          refine ⟨m, vsh s2 r0, s, rfl, hc, hk, ih _ ρ r0 s1 s2 ht ?_ hR hb1 hb2 hs hi hri hm hv⟩
          intro k S ws hk
          cases k with
          | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
          | succ k => exact hr k S ws (by simpa [TEnv.push0, TEnv.ins, TEnv.insR] using hk)
      | _ => simp [vsh] at hrt
  | sum a b iha ihb =>
      intro η ρ R s1 s2 ht hr hR hb1 hb2 hs hi hri hm h
      simp only [VRF, VRb2] at h ⊢
      obtain ⟨n, Ra, Rb, hrt, h⟩ := h
      cases R with
      | sum m R0 =>
          simp only [vsh, Shp.sum.injEq] at hrt
          obtain ⟨rfl, rfl⟩ := hrt
          simp only [bh] at hR
          rcases h with ⟨htr, x, s, B, hw, ho, hb, hn, ⟨hsB, hwa⟩, hmo, hA, hB⟩ | ⟨j, p, hd, _, _⟩
          · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, h1] at hw
            cases hw
            rw [hb1] at hb; cases hb
            have hn' : s = s1 := by simp at hn; omega
            subst s
            have hpl : B1.pay.length = B2.pay.length := by simpa using congrArg List.length hpay.vals
            refine ⟨_, Ra, Rb, rfl, Or.inl ⟨htr, x2, s2, B2, by simp [h2], ho2, hb2, rfl,
              ⟨by omega, by rw [show B2.tag - s2 = B1.tag - s1 by omega, ← hpl]; exact hwa⟩,
              by rcases hm with hm | hm; exact Or.inl hm; exact Or.inr (by simpa using hm), fun hj => ?_, fun hj => ?_⟩⟩
            · have e : B2.tag - s2 = B1.tag - s1 := by omega
              rw [e] at hj ⊢
              refine ⟨fun hx => iha η ρ (shp Ra) s1 s2 ht hr (bh_shp Ra hx) hb1 hb2 hs hi hri hm ((hA hj).1 hx),
                fun hx => ?_⟩
              obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hA hj).2 hx
              obtain ⟨q', hq', hw'⟩ := ofArm_wle hpay hq
              exact ⟨q', hq', ShapeC_vals hw'.vals hs1, hw1, Valid_vals _ _ _ hw'.vals hv1, VR_upB (bkG := False) _ _ _ _ hw' hv⟩
            · have e : B2.tag - s2 = B1.tag - s1 := by omega
              rw [e] at hj ⊢
              refine ⟨fun hx => ihb η ρ (shp Rb) (s1 + (armsOf Ra).length) (s2 + (armsOf Ra).length) (by omega)
                hr (bh_shp Rb hx) hb1 hb2 hs hi hri hm ((hB hj).1 hx), fun hx => ?_⟩
              obtain ⟨q, hq, hs1, hw1, hv1, hv⟩ := (hB hj).2 hx
              obtain ⟨q', hq', hw'⟩ := ofArm_wle hpay hq
              exact ⟨q', hq', ShapeC_vals hw'.vals hs1, hw1, Valid_vals _ _ _ hw'.vals hv1, VR_upB (bkG := False) _ _ _ _ hw' hv⟩
          · rw [hR] at hd; simp [decodeArm] at hd
      | _ => simp [vsh] at hrt
end
end TermSound.Flat

-- PORTB TermSound.lean:15829 VR_ren
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_renB {η : TEnv} (hc : CohBW η) {ρ : Nat → Nat} {t : Ty} {R : Shp} {s1 s2 : Nat}
    {w1 w2 : Word} {x1 x2 : WeakMem.Address} {B1 B2 : Box}
    (h1 : w1.val = .loc x1 0) (h2 : w2.val = .loc x2 0) (ho2 : x2.offset = 0)
    (hb1 : η.box x1.label = some B1) (hb2 : η.box x2.label = some B2) (hs : η.sto x1.label = none)
    (hi : η.ini x1.label ≤ η.ini x2.label) (ht : B1.tag + s2 = B2.tag + s1) (hpay : WLe B1.pay B2.pay)
    (hm : BoxSeen η x2.label B2 ∨ B2.fr ≤ w2.view) (hR : bh R)
    (h : (VRF False) ρ η t (vsh s1 R) [w1]) (hri : min (η.ini x1.label) (η.rini x1.label) ≤ η.rini x2.label) : (VRF False) ρ η t (vsh s2 R) [w2] := by
  have c := fun S ws => VR_closeB hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  exact (c _ _).2 (VR_ren0B w1 w2 x1 x2 B1 B2 h1 h2 ho2 hpay _ (CE η) ρ R s1 s2 ht (fun _ _ _ h => h) hR
    hb1 hb2 hs hi hri hm ((c _ _).1 h))
end
end TermSound.Flat

-- PORTB TermSound.lean:15843 VR_seen
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_seenB {η : TEnv} (hc : CohBW η) {ρ : Nat → Nat} {t : Ty} {S : Shp} {ws : List Word}
    (h : (VRF False) ρ η.unsee t S ws) : (VRF False) ρ η t S ws := by
  have c1 := VR_closeB hc.unsee ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have c2 := VR_closeB hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  refine c2.2 ?_
  have h1 : (VRF False) ρ (CE η.unsee) (cl ρ η.wit 0 0 t) S ws := c1.1 h
  exact VR_monoB (bkG := False) _ (CE η.unsee) (CE η) ρ S ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl
    (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ h => h.elim) (fun _ _ h => h) h1
end
end TermSound.Flat

-- PORTB TermSound.lean:15854 VR_store
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_storeB {η : TEnv} (hc : CohBW η) {V : WeakMem.Ts} {ρ : Nat → Nat} {t : Ty} {S : Shp}
    {ws : List Word} (hS : ∀ l, η.seen l → ∃ f, η.pfr l = some f ∧ f ≤ V) (hL : LocAbove V ws)
    (h : (VRF False) ρ η t S ws) : (VRF False) ρ η.unsee t S ws := by
  have c1 := VR_closeB hc.unsee ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have c2 := VR_closeB hc ρ t [] 0 ρ ρ S ws (fun _ => rfl) (fun _ hk => absurd hk (Nat.not_lt_zero _))
  refine c1.2 ?_
  exact VR_unseeB (bkG := False) V _ (CE η) (CE η.unsee) ρ S ws (fun _ _ _ h => h) (fun _ _ _ h => h) rfl rfl rfl
    (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun l hl => Or.inr (hS l hl))
    (fun _ _ h => h) hL (c2.1 h)
end
end TermSound.Flat

-- PORTB TermSound.lean:16245 VR_boxL
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_boxLB {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    {q : List Word} (hS : (Ty.sum Ra Rb).tier = .boxed) (hRa : isBoxed Ra = false)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : B.tag < (armsOf Ra).length) (hq : ofArm Ra B.tag B.pay = some q) (hv : (VRF False) ρ η.unsee a (shp Ra) q)
    (hs : ShapeC Ra q) (hwc : wc Ra ≠ none) (hvd : Valid Ra q)
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    (VRF False) ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun _ => ⟨fun h => ?_, fun _ => ?_⟩, fun h => ?_⟩⟩
  · rw [isBoxed_lnorm] at h; rw [hRa] at h; cases h
  · exact ⟨q, by rw [Nat.sub_zero]; exact ofArm_lnorm hq, ShapeC_wc (wc_lnorm Ra).symm hs,
      by rw [wc_lnorm]; exact hwc, Valid_lnorm _ _ hvd, by rw [shp_lnorm]; exact hv⟩
  · rw [armsOf_lnorm, List.length_map] at h; omega
end
end TermSound.Flat

-- PORTB TermSound.lean:16261 VR_boxR
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_boxRB {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    {q : List Word} (hS : (Ty.sum Ra Rb).tier = .boxed) (hRb : isBoxed Rb = false)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : (armsOf Ra).length ≤ B.tag) (hq : ofArm Rb (B.tag - (armsOf Ra).length) B.pay = some q)
    (hv : (VRF False) ρ η.unsee b (shp Rb) q) (hs : ShapeC Rb q) (hwc : wc Rb ≠ none) (hvd : Valid Rb q)
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    (VRF False) ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun h => ?_, fun _ => ⟨fun h => ?_, fun _ => ?_⟩⟩⟩
  · rw [armsOf_lnorm, List.length_map] at h; omega
  · rw [isBoxed_lnorm] at h; rw [hRb] at h; cases h
  · refine ⟨q, ?_, ShapeC_wc (wc_lnorm Rb).symm hs, by rw [wc_lnorm]; exact hwc, Valid_lnorm _ _ hvd,
      by rw [shp_lnorm]; exact hv⟩
    rw [Nat.sub_zero, armsOf_lnorm, List.length_map]; exact ofArm_lnorm hq
end
end TermSound.Flat

-- PORTB TermSound.lean:16523 VR_boxLB
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_boxLBB {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    (hS : (Ty.sum Ra Rb).tier = .boxed) (hRa : isBoxed Ra = true)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : B.tag < (armsOf Ra).length) (hv : (VRF False) ρ η a (vsh 0 (shp Ra)) [w])
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    (VRF False) ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun _ => ⟨fun _ => ?_, fun h => ?_⟩, fun h => ?_⟩⟩
  · rw [shp_lnorm]; exact hv
  · rw [isBoxed_lnorm, hRa] at h; cases h
  · rw [armsOf_lnorm, List.length_map] at h; omega
end
end TermSound.Flat

-- PORTB TermSound.lean:16537 VR_boxRB
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem VR_boxRBB {ρ : Nat → Nat} {η : TEnv} {a b Ra Rb : Ty} {w : Word} {x : WeakMem.Address} {B : Box}
    (hS : (Ty.sum Ra Rb).tier = .boxed) (hRb : isBoxed Rb = true)
    (hw : w.val = .loc x 0) (hx : x.offset = 0) (hB : η.box x.label = some B) (hown : BoxSeen η x.label B ∨ B.fr ≤ w.view)
    (hj : (armsOf Ra).length ≤ B.tag) (hv : (VRF False) ρ η b (vsh (armsOf Ra).length (shp Rb)) [w])
    (hwa : ((armsOf (.sum Ra Rb))[B.tag]?).bind wc = some B.pay.length) :
    (VRF False) ρ η (.sum a b) (shp (.sum Ra Rb)) [w] := by
  refine ⟨_, _, _, rfl, Or.inl ⟨tier_lsum hS, x, 0, B, by simp [hw], hx, hB, wc_boxed hS,
    ⟨Nat.zero_le _, by rw [Nat.sub_zero]; exact armsWc_lnorm hwa⟩,
    hown.imp id (fun h w' hw' => by rw [List.mem_singleton] at hw'; subst hw'; exact h), fun h => ?_, fun _ => ⟨fun _ => ?_, fun h => ?_⟩⟩⟩
  · rw [armsOf_lnorm, List.length_map] at h; omega
  · rw [shp_lnorm, armsOf_lnorm, List.length_map, Nat.zero_add]; exact hv
  · rw [isBoxed_lnorm, hRb] at h; cases h
end
end TermSound.Flat

-- PORTB TermSound.lean:16603 case_arm_nb
namespace TermSound.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
set_option linter.unusedSimpArgs false
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv
open TermRun in
open TermClose in
theorem case_arm_nbB {ρ : Nat → Nat} {η : TEnv} {u ra : Ty} {j : Nat} {pay p1 q : List Word}
    (hc : CohBW η) (hra : isBoxed ra = false) (hsg : sig ra = sig (cl ρ η.wit 0 0 u))
    (hq : ofArm (lnorm ra) j pay = some q) (hs : ShapeC (lnorm ra) q) (hw : wc (lnorm ra) ≠ none)
    (hvd : Valid (lnorm ra) q) (hvr : (VRF False) ρ η.unsee u (shp (lnorm ra)) q) (hp : WLe pay p1) :
    ∃ q1, ofArm ra j p1 = some q1 ∧ ShapeC ra q1 ∧ wc ra ≠ none ∧ Valid ra q1 ∧ (VRF False) ρ η u (shp ra) q1 := by
  obtain ⟨q1, hq1, hw1⟩ := ofArm_wle hp hq
  have e := hw1.vals
  have hs1 : ShapeC ra q1 := ShapeC_wc (wc_lnorm ra) (ShapeC_vals e hs)
  have hwc : wc ra ≠ none := by rw [← wc_lnorm]; exact hw
  have hvd1 : Valid (lnorm ra) q1 := Valid_vals _ _ _ e hvd
  have hvr1 : (VRF False) ρ η.unsee u (shp ra) q1 := by rw [← shp_lnorm]; exact VR_upB (bkG := False) _ _ _ _ hw1 hvr
  have hlT : lnorm (cl ρ η.wit 0 0 u) = lnorm ra := by rw [← lnorm_sig (cl ρ η.wit 0 0 u), ← hsg, lnorm_sig]
  have hsT : shp (cl ρ η.wit 0 0 u) = shp ra := by rw [← shp_sig (cl ρ η.wit 0 0 u), ← hsg, shp_sig]
  have c1 := VR_closeB hc.unsee ρ u [] 0 ρ ρ (shp ra) q1 (fun _ => rfl)
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  have hvT : (VRF False) ρ (CE η.unsee) (cl ρ η.wit 0 0 u) (shp (cl ρ η.wit 0 0 u)) q1 := by
    rw [hsT]; exact c1.1 hvr1
  have hV := Valid_of_VRB (bkG := False) _ (CE η.unsee) ρ q1 (fun _ _ _ h => h) (by rw [hlT]; exact hvd1) hvT
  have hVr : Valid ra q1 := Valid_of_sig hsg.symm hV
  refine ⟨q1, ofArm_back hq1 ?_, hs1, hwc, hVr, VR_seenB hc hvr1⟩
  intro x w hx hk hp1 hnl
  subst hp1
  exact null_arm hVr hs1 hra hx hk hq1 hnl
end
end TermSound.Flat

-- PORTB TermStep.lean:2775 ThInvM
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ThInvMB (p : Prog) (g : G) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E, ThInvEB g.lbase g.n g.i p E th ∧ MemInvB g E (stOf mem pairs th) ∧ g.boxFence = true ∧ TyOKE g E ∧ RecFresh g g.i th.nalloc
end
end TermStep.Flat

-- PORTB TermStep.lean:3155 ThInvMFA
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ThInvMFAB (p : Prog) (g : G) (ρ : Nat → Nat) (η : TEnv) (th0 : TTh) (E : TEnv) (s : St) (mem : Memory)
    (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', FreshArr g ρ η th0 E' (mem, pairs, th) ∧ EFootPB g E E' s (stOf mem pairs th) ∧ ThInvEB g.lbase g.n g.i p E' th ∧
    MemInvB g E' (stOf mem pairs th)
end
end TermStep.Flat

-- PORTB TermStep.lean:3167 ThInvMFS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def ThInvMFSB (p : Prog) (g : G) (E : TEnv) (s : St) (mem : Memory) (pairs : List Ts) (th : TTh) : Prop :=
  ∃ E', (∀ l, E'.sto l = E.sto l) ∧ EFootPB g E E' s (stOf mem pairs th) ∧ ThInvEB g.lbase g.n g.i p E' th ∧
    MemInvB g E' (stOf mem pairs th)
end
end TermStep.Flat

-- PORTB TermStep.lean:3176 ThInvMFS_congr
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ThInvMFSB.toF {p : Prog} {g : G} {E : TEnv} {s : St} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvMFSB p g E s mem pairs th) : ThInvMFB p g E s mem pairs th :=
  let ⟨E', _, h1, h2, h3⟩ := h
  ⟨E', h1, h2, h3⟩
theorem ThInvMFAB.toF {p : Prog} {g : G} {ρ : Nat → Nat} {η : TEnv} {th0 : TTh} {E : TEnv} {s : St}
    {mem : Memory} {pairs : List Ts} {th : TTh} (h : ThInvMFAB p g ρ η th0 E s mem pairs th) :
    ThInvMFB p g E s mem pairs th :=
  let ⟨E', _, h1, h2, h3⟩ := h
  ⟨E', h1, h2, h3⟩
theorem TyOKE_footB {W : Ty → Prop} {g : G} {E E' : TEnv} {s s' : St} (hF : EFootBB W g E E' s s')
    (hT : TyOKE g E) (hR : RecFresh g g.i s.nalloc) : TyOKE g E' := by
  intro l t c ht hc
  rcases hF.2.2.1 l with h | ⟨⟨j, hj, -, rfl⟩, -⟩
  · rw [h] at hc
    exact hT l t c ht hc
  · exact absurd ht (hR j hj t)
theorem ThInvMFB.toMT {p : Prog} {g : G} {E : TEnv} {s : St} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvMFB p g E s mem pairs th) (hbf : g.boxFence = true) (hT : TyOKE g E) (hR : RecFresh g g.i s.nalloc)
    (hn : s.nalloc ≤ th.nalloc) : ThInvMB p g mem pairs th :=
  let ⟨E', hF, h1, h2⟩ := h
  ⟨E', h1, h2, hbf, TyOKE_footB hF hT hR, RecFresh_mono hR hn⟩
theorem ThInvMFPB.toF {p : Prog} {g : G} {E : TEnv} {s : St} {th0 : TTh} {mem : Memory} {pairs : List Ts}
    {th : TTh} (h : ThInvMFPB p g E s th0 mem pairs th) : ThInvMFB p g E s mem pairs th :=
  let ⟨E', h1, h2, h3, _⟩ := h
  ⟨E', h1, h2, h3⟩
end
end TermStep.Flat
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ThInvMFS_congrB {p : Prog} {g : G} {E : TEnv} {s1 s : St} {mem : Memory} {pairs : List Ts} {th : TTh}
    (h : ThInvMFSB p g E s1 mem pairs th) (hn : s1.nalloc = s.nalloc) (hv : s1.vs.vWr = s.vs.vWr)
    (hz : s1.mem.size = s.mem.size) (hpr : s1.promises = s.promises) (hme : s1.mem = s.mem) :
    ThInvMFSB p g E s mem pairs th :=
  let ⟨E', hs, hf, h1, h2⟩ := h
  ⟨E', hs, EFoot_congrB hf hn hv hz hpr hme, h1, h2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:5519 liftS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem liftSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {E : TEnv}
    (hm : MemInvB g E (stOf mem pairs th))
    (h : tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEB g.lbase g.n g.i p E r.2.2)
    (hs : ∀ r ∈ tstep g mem pairs th, Same (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2)) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSB p g E (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  ⟨h.1, fun r hr => ⟨E, fun _ => rfl, EFoot_reflB, h.2 r hr, MemInv_sameB hm (hs r hr)⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:5700 tstepM_pure
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_pureB {x : String} {op : Op} {e : Expr}
    (hterm : th.term = .let_ x op e) (hA : PureOp op) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_pureB (hDy := hDy) hterm hA hP hT hi hE htv hRP hPS) (same_pure hterm hA)
end
end TermStep.Flat

-- PORTB TermStep.lean:5707 tstepM_ifeq
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ifeqB {a b : At} {yes no : Expr}
    (hterm : th.term = .ifeq a b yes no) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_ifeqB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_ifeq hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5713 tstepM_parity
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_parityB {a : At} {k : String} {ev₀ od : Expr}
    (hterm : th.term = .parity a k ev₀ od) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_parityB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_parity hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5719 tstepM_split
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_splitB {a : At} {x y : String} {e : Expr}
    (hterm : th.term = .split a x y e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_splitB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_split hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5725 tstepM_unpack
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_unpackB {a : At} {i x : String} {e : Expr}
    (hterm : th.term = .unpack a i x e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_unpackB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_unpack hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5731 tstepM_unpackT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_unpackTB {a : At} {α x : String} {e : Expr}
    (hterm : th.term = .unpackT a α x e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_unpackTB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_unpackT hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5737 tstepM_ifnull
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ifnullB {a : At} {y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .ifnull a e₁ y e₂) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_ifnullB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_ifnull hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5743 tstepM_inlS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inlSB {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum t τ)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  refine liftSB hm (tstep_inlB (hDy := hDy) hterm hP hnb hT hi hE htv hRP hPS) (same_inl hterm fun t ws hea => ?_)
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
      cases hop with
      | inl _ hu _ =>
          obtain ⟨-, rt, ws', hea', -, hl⟩ := use_FInvB (bkG := False) hu hi
          rw [hea, Option.some.injEq, Prod.mk.injEq] at hea'
          obtain ⟨rfl, rfl⟩ := hea'
          rw [tier_of_eskel (u := close th.σs (.sum _ τ)) (by show Ty.sum (etok (skel t)) _ = _; rw [hl.2.1]; rfl)]
          exact hnb _ _ hu
end
end TermStep.Flat

-- PORTB TermStep.lean:5771 tstepM_inrS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inrSB {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs (.sum τ t)).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  refine liftSB hm (tstep_inrB (hDy := hDy) hterm hP hnb hT hi hE htv hRP hPS) (same_inr hterm fun t ws hea => ?_)
  rw [hterm] at hT
  cases hT with
  | let_ hop _ =>
      cases hop with
      | inr _ hu _ =>
          obtain ⟨-, rt, ws', hea', -, hl⟩ := use_FInvB (bkG := False) hu hi
          rw [hea, Option.some.injEq, Prod.mk.injEq] at hea'
          obtain ⟨rfl, rfl⟩ := hea'
          rw [tier_of_eskel (u := close th.σs (.sum τ _)) (by show Ty.sum _ (etok (skel t)) = _; rw [hl.2.1]; rfl)]
          exact hnb _ _ hu
end
end TermStep.Flat

-- PORTB TermStep.lean:5799 tstepM_caseS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_caseSB {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂)
    (hnb : ∀ t c₁, cx.use a = .ok (t, c₁) → (close th.σs t).tier ≠ .boxed)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  refine liftSB hm (tstep_caseB (hDy := hDy) hterm hnb hT hi hE htv hRP hPS) ?_
  rw [hterm] at hT
  obtain ⟨ra, rb, ws, j, p', hea, hS, has, -, -⟩ := case_stepB hT hi hnb htv
  obtain ⟨hta, htb⟩ := tier_sum hS
  intro r hr
  by_cases hj : j < (armsOf ra).length
  · simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_true, injM_nb hta, List.append_nil, List.mem_map,
      Option.mem_toList, Option.map_eq_some_iff] at hr
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hr
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · simp only [tstep, hterm, hea, projM_nb hS, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, hj, ite_false, injM_nb htb, List.append_nil, List.mem_map,
      Option.mem_toList, Option.map_eq_some_iff] at hr
    obtain ⟨_, ⟨_, _, rfl⟩, rfl⟩ := hr
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:5832 tstepM_ret
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_retB {a : At}
    (hterm : th.term = .ret a) (hst : th.stack ≠ []) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hn : 0 < g.n) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_retB hterm hst hT hi hE (supI_of_memInvB hm hn) htv) (same_ret hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5839 tstepM_call
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_callB {x f : String} {is : List String} {a : At} {ts : List Ty} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.call f is a ts) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_callB (hDy := hDy) hp hP hterm hT hi hE htv KindSound.zero_close hrt hRP) (same_call hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5848 tstepM_tail
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_tailB {f : String} {is : List String} {a : At} {ts : List Ty}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .tail f is a ts) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hrt : ∀ σ ∈ ts, rgnFree σ = true ∧ noIallV σ = true) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_tailB (hDy := hDy) hp hP hterm hT hi hE htv KindSound.zero_close hrt hRP hPS hSub) (same_tail hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5857 tstepM_fnptr
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_fnptrB {x f : String} {e : Expr}
    (hp : g.p = p) (hP : ProgT p)
    (hterm : th.term = .let_ x (.fnptr f) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_fnptrB (hDy := hDy) hp hP hterm hT hi hE htv hRP hPS) (same_fnptr hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5865 tstepM_callc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_callcB {x : String} {f a : At} {e : Expr}
    (hp : g.p = p) [ProgRetIall p] (hP : ProgT p)
    (hterm : th.term = .let_ x (.callc f a) e) (hT : Typed p cx th.term)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hSig : PwSig) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_callcB (hDy := hDy) hp hP hterm hT hi hE htv hRP hSig) (same_callc hterm)
end
end TermStep.Flat

-- PORTB TermStep.lean:5899 tstepM_newA
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newAB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFAB p g ρ η th (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | new hu _ hb =>
  obtain ⟨tv, c₁, hu, hb⟩ : ∃ tv c₁, cx.use a = .ok (tv, c₁) ∧ c₁.bind x (.ptr .own tv) = .ok c' :=
    ⟨_, _, hu, hb⟩
  obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
  have ho : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have htb := (use_TvOK hu htv).2.1
  have hsig : sig rt = sig (cl ρ η.wit 0 0 tv) := lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl
  obtain ⟨us, hus⟩ : ∃ us, accs rt = some us := by
    cases h : accs rt with
    | none => exact absurd (by simp [wc, h]) hl.2.2.1
    | some us => exact ⟨us, rfl⟩
  have hlen : ws.length = nWords us := hl.1 us hus
  have hwcT : wc (cl ρ η.wit 0 0 tv) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have hvc : (VRF False) (fun _ => 0) (CE η) (cl ρ η.wit 0 0 tv) (shp (cl ρ η.wit 0 0 tv)) ws := by
    rw [← shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ tv [] 0 ρ (fun _ => 0) (shp rt) ws (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).1 hv
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := hm
  obtain ⟨hnone, hfresh, -, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hval : ValOfB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) (cl ρ η.wit 0 0 tv)
      (ws.map (bumpW (stOf mem pairs th).vs.vRelSt)) :=
    ValOf_monoB (η₁ := CE η) (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
      rfl rfl (fun l c h => allocE_sub hnone h) (fun _ => Nat.le_refl _)
      (EnvValB.store (η := CE η) ⟨hvc, Valid_of_sig hsig hl.2.2.2.1⟩ hsn)
  have hx : ExtB η (η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto) :=
    Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := CE η) hnone h) (fun _ => Nat.le_refl _)
  have key : ∀ r ∈ tstep g mem pairs th, ∃ s' pw,
      (s', pw) ∈ alloc g.k g.arch (freshLabel g.lbase g.n g.i th.nalloc) us ws (stOf mem pairs th) ∧
      ∃ tys, r = (s'.mem, s'.pairs,
        { withS { th with term := e, env := (x, .ptr .own rt, [pw]) :: th.env } s' with tys := tys }) := by
    intro r hr
    obtain ⟨s1, t1, ws1, hm1, tys, rfl⟩ := TermRun.tstep_new_mem hterm hr
    simp only [evalOp, hea, hus, List.mem_map] at hm1
    obtain ⟨⟨s2, pw⟩, hal, he⟩ := hm1
    cases he
    exact ⟨_, _, hal, tys, rfl⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := freshLabel g.lbase g.n g.i th.nalloc)
      (s := stOf mem pairs th) hlen
    simp only [tstep, hterm, evalOp, hea, hus, ne_eq, List.map_eq_nil_iff]
    exact List.ne_nil_of_mem hr
  · intro r hr
    obtain ⟨s', pw, hal, tys, rfl⟩ := key r hr
    obtain ⟨hmo', hoo', hpw⟩ := alloc_okPB hwcT hlen hval hfresh hnone hpl hpo.1 hpo.2.1 hpf0 hmo hoo ⟨s', pw⟩ hal
    obtain ⟨hg, -, hna, hpl', hful⟩ := alloc_growsP hpl ⟨s', pw⟩ hal
    obtain ⟨hwr, hhid⟩ := alloc_hidPB (s := stOf mem pairs th) hval
      (ShapeC_of_wc hwcT (by rw [List.length_map]; exact hlen))
      (by obtain ⟨_, h, -⟩ := wc_some hwcT; simp [h]) hfresh hpl ⟨s', pw⟩ hal
    simp only at hmo' hoo' hpw hg hna hwr hhid hpl' hful
    subst hpw
    have hwA : ∀ T o w, WordOKB (CE η) T o w →
        WordOKB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) T o w :=
      fun T o w h => WordOK_monoB (η₁ := CE η)
        (η₂ := allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv))
        rfl rfl (fun l c h' => allocE_sub hnone h') (fun _ => Nat.le_refl _)
        (fun _ _ h' => h') (fun _ h' => h') h
    have hoh' : OwnHidPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem s'.vs
        s'.promises := by
      refine ⟨fun l c hc ho o hi => ?_, fun l c hc ho hlt => ?_⟩
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          rw [allocE_eq] at hc; cases hc; exact hhid o
        · rw [allocE_ne hl] at hc
          exact HiddenP_growsAtB (hoh.1 l c hc ho o hi) (hwA _ _) hwr hg hl hful
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
            (Nat.not_lt_zero _)
        · rw [allocE_ne hl] at hc
          obtain ⟨f, hf, hs, hH⟩ := hoh.2 l c hc ho hlt
          exact ⟨f, hf, fun hz => hs (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
            fun o hi => HiddenP_growsAtB (hH o hi) (hwA _ _) (Nat.le_refl _) hg hl hful⟩
    have hpd' : PubDefPB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s'.mem
        s'.promises := by
      intro l c f hc hown hf o hi
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at hc; cases hc; exact (hown rfl).elim
      · rw [allocE_ne hl] at hc
        exact HiddenP_growsAtB (hpd l c f hc hown hf o hi) (hwA _ _) (Nat.le_refl _) hg hl hful
    have hpi' : PubInvB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      refine PubInv_growB (hbs := fun l hb h => by
          by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
          · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
          · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (alloc_pairs _ hal) hful rfl rfl (fun l c h => allocE_sub hnone h)
        (fun _ => Nat.le_refl _) rfl rfl (fun c h => by rw [allocE_eq] at h; rw [← Option.some.inj h]; rfl)
        (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq (hfr.1 th.nalloc (Nat.le_refl _)).2.2.1))
          (Nat.not_lt_zero _)) (hrcg := fun _ h => ⟨h, Nat.le_refl _⟩)
      · by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
        · subst hl; exact Or.inr hpf0
        · rw [allocE_ne hl] at h; exact Or.inl h
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · subst hl
        rw [allocE_eq] at h
        cases h
        refine Or.inr ?_
        rcases hseg with ⟨-, rfl, -⟩ | ⟨N, us0, j0, hT, -, -, -⟩
        · obtain ⟨vals, hcell, -⟩ := hoo' _ _ allocE_eq rfl
          rcases hcell with ⟨hwc, hv⟩ | hb
          · exact ⟨vals, hv, Option.some.inj (hwc.symm.trans (wc_of_accs hu'))⟩
          · obtain ⟨N, e0, us0, hT, -⟩ := hb
            exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
        · exact absurd hwcT (by rw [show cl ρ η.wit 0 0 tv = _ from hT]; simp [wc, accs])
      · rw [allocE_ne hl] at h; exact Or.inl ⟨h, hini⟩
    refine ⟨allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv),
      (by
        intro l c N u hf hc hty
        obtain ⟨j, hj, -, rfl⟩ := hf
        by_cases hl : freshLabel g.lbase g.n g.i j = freshLabel g.lbase g.n g.i th.nalloc
        · rw [hl, allocE_eq] at hc
          cases hc
          have h2 : cl ρ η.wit 0 0 tv = .array (.lit N) u := hty
          exact absurd hwcT (by rw [h2]; simp [wc, accs])
        · rw [allocE_ne hl] at hc
          have h0 : (CE η).sto (freshLabel g.lbase g.n g.i j) = none := (hfr.1 j hj).1
          rw [h0] at hc
          cases hc),
      EFoot_freshB rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ tv,
        mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) tv 0 0 (use_mg hu htv),
        noIallV_cl (WitAF.ni hi.2.2.2.2.2.2.1) tv 0 0 (hniA tv _ hu), trivial⟩ (alloc_newT hal hwcT) (alloc_undefT hal hwcT) l) (fun _ => .inl rfl)
        (fun _ => ⟨Nat.le_refl _, .inl rfl⟩),
      ⟨ρ, η.withStoB (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)).sto, c', rfl,
        ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, ?_⟩
    · refine bind_FInvB hb (FInv_extB hE.2.1 hx hi1) ?_ ?_
      · simp only [VRF, VRb2]
        exact ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, ⟨cl ρ η.wit 0 0 tv, some η.tid⟩, by simp [cst, Promises.TVal.mk0], rfl,
          by simp [TEnv.withStoB, allocE, CE], .refl, rfl,
          show accs (cl ρ η.wit 0 0 tv) ≠ none from fun h => by simp [wc, h] at hwcT⟩
      · refine ⟨fun us h => by simp [accs] at h; subst h; rfl, ?_, by simp [wc, accs],
          ⟨⟨freshLabel g.lbase g.n g.i th.nalloc, 0⟩, by simp [cst, Promises.TVal.mk0]⟩, ?_⟩
        · show Ty.ptr (skelM .own) (etok (skel rt)) = Ty.ptr _ _
          rw [hl.2.1]; rfl
        · show Ty.ptr (modeC 0 .own) (etok (lyt 0 rt)) = Ty.ptr _ _
          rw [hl.2.2.2.2]; rfl
    have hopub' : OwnPubV (allocE (CE η) (freshLabel g.lbase g.n g.i th.nalloc) (cl ρ η.wit 0 0 tv)) s' := by
      intro l c f hc ho hf
      by_cases hl : l = freshLabel g.lbase g.n g.i th.nalloc
      · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
      · rw [allocE_ne hl] at hc
        exact ((hopub.alloc hpl hal) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
          fun a ha hi c1 N1 e1 us1 h1 => hi c1 N1 e1 us1 (by rw [allocE_ne (fun e => hl (ha.symm.trans e))]; exact h1))
    · refine ⟨hmo', hoo', hpl', ⟨fun j hj => ?_, PrivCoh_growsAtB hfr.2
          (fun a hu hl => by
            obtain ⟨c, N, e, us, hc, rest⟩ := hu
            exact ⟨c, N, e, us, by rw [allocE_ne hl] at hc; exact hc, rest⟩)
          hoo' hg hful (fun t m _ _ hu hl => by
            obtain ⟨c, N, e, us, hc, -, -, hT, -⟩ := hu
            rw [hl, allocE_eq] at hc; cases hc
            simp only at hT; rw [hT] at hwcT; simp [wc, accs] at hwcT)⟩, ?_, hoh', hpd', hopub', hpi',
        BoxInv_alloc hbi rfl hpl hpo.1 hal rfl rfl (fun _ hl => allocE_ne hl) (fun _ _ => rfl),
        PromOK_alloc hpo hpl hal⟩
      rotate_left 1
      · have e : s'.vs.vRelSt = (stOf mem pairs th).vs.vRelSt := alloc_relSt _ hal
        exact (SeenLE.mono hsn (Nat.le_of_eq e.symm) : SeenLE (CE η) s'.vs.vRelSt)
      · have hj' : th.nalloc ≤ j := by
          have : s'.nalloc ≤ j := hj
          rw [hna] at this; exact Nat.le_of_succ_le this
        obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
        have hne : freshLabel g.lbase g.n g.i j ≠ freshLabel g.lbase g.n g.i th.nalloc := fun h => by
          have := freshLabel_inj_k hn h; subst this
          have : s'.nalloc ≤ th.nalloc := hj
          rw [hna] at this; exact absurd this (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
        refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, f4, f5⟩
        change s'.mem[t]? = some m at ht
        by_cases hlt : t < (stOf mem pairs th).mem.size
        · rw [hg.2.1 t hlt] at ht
          have hp := f2 t m ht hl
          refine Classical.byContradiction fun hn' => ?_
          obtain ⟨m', hm', e⟩ := hful t hp hn'
          rw [ht] at hm'; cases hm'
          exact hne (hl.symm.trans e)
        · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
end
end TermStep.Flat

-- PORTB TermStep.lean:6083 tstepM_new
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {T : Option Ty} {e : Expr}
    (hterm : th.term = .let_ x (.new a T) e)
    (hniA : ∀ t c₁, cx.use a = .ok (t, c₁) → noIallV t = true) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  (tstepM_newAB (hDy := hDy) (hterm := hterm) (hniA := hniA) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS)).imp id
    fun h r hr => (h r hr).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:7158 fld_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem fld_stepB {p : Prog} {cx c' : Cx} {x : String} {i : Nat} {a : At} {ρ : Nat → Nat} {η : TEnv}
    {σs : List Ty} {env : Env} {K : TEnv → List Word → Prop} {g : G} {s : St}
    (hT : OpT p cx x (.fld i a) c') (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx) (hw : ∀ k, Clo (η.wit k)) :
    ∃ rt ws, evalOp g env σs s (.fld i a) = [(s, rt, ws)] ∧ FInvB g.lbase g.n g.i ρ η σs K c' ((x, rt, ws) :: env) := by
  cases hT with
  | fldOwn hp hc hunf hop hu hb =>
      obtain ⟨rt, ws, he, hv, hl⟩ :=
        fld_coreB (bkG := False) (g := g) (s := s) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hw hp hc hunf hop
      exact ⟨rt, ws, he, bind_FInvB hb (use_FInvB (bkG := False) hu hi).1 hv hl⟩
  | fldShared hp hc _ hunf hop hb =>
      obtain ⟨rt, ws, he, hv, hl⟩ :=
        fld_coreB (bkG := False) (g := g) (s := s) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hw hp hc hunf hop
      exact ⟨rt, ws, he, bind_FInvB hb hi hv hl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:7173 tstep_fld
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_fldB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {i : Nat} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.fld i a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEB g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      obtain ⟨rt, ws, hev, hf⟩ := fld_stepB (g := g) (s := stOf mem pairs th) hop hi htv (fun k => (hE.2.1 k).1)
      have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) (.fld i a)).map
          fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
        simp [tstep, hterm]
      rw [key, hev]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      exact ⟨ρ, η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, hf, retPw_skel hPS hRP (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:7194 tstepM_fld
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_fldB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {i : Nat} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.fld i a) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT' := hT
  rw [hterm] at hT'
  cases hT' with
  | let_ hop _ =>
      obtain ⟨rt, ws, hev, -⟩ := fld_stepB (g := g) (s := stOf mem pairs th) hop hi htv (fun k => (hE.2.1 k).1)
      exact liftB hm (tstep_fldB (hDy := hDy) hterm hP hT hi hE htv hRP hPS) (same_let hterm (fun _ _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun r hr => by
          rw [hev, List.mem_singleton] at hr; subst hr; exact same_of_eq rfl))
end
end TermStep.Flat

-- PORTB TermStep.lean:7320 idx_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem idx_stepB {p : Prog} {cx c' : Cx} {x : String} {b i : At} {ρ : Nat → Nat} {η : TEnv}
    {σs : List Ty} {env : Env} {K : TEnv → List Word → Prop} {g : G} {s : St}
    (hT : OpT p cx x (.idx b i) c') (hi : FInvB g.lbase g.n g.i ρ η σs K cx env) (htv : TvOK cx) :
    ∃ rt ws, evalOp g env σs s (.idx b i) = [(s, rt, ws)] ∧ FInvB g.lbase g.n g.i ρ η σs K c' ((x, rt, ws) :: env) := by
  cases hT with
  | idxOwn hp hbuf hint hlt hltk hop hu hb =>
      obtain ⟨rt, ws, he, hv, hl⟩ :=
        idx_coreB (bkG := False) (g := g) (s := s) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
      exact ⟨rt, ws, he, bind_FInvB hb (use_FInvB (bkG := False) hu hi).1 hv hl⟩
  | idxShared hp hbuf _ hint hlt hltk hop hb =>
      obtain ⟨rt, ws, he, hv, hl⟩ :=
        idx_coreB (bkG := False) (g := g) (s := s) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
      exact ⟨rt, ws, he, bind_FInvB hb hi hv hl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:7335 tstep_idx
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_idxB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.idx b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEB g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
      rename_i c₁
      obtain ⟨rt, ws, hev, hf⟩ := idx_stepB (g := g) (s := stOf mem pairs th) hop hi htv
      have key : tstep g mem pairs th = (evalOp g th.env th.σs (stOf mem pairs th) (.idx b i)).map
          fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
        simp [tstep, hterm]
      rw [key, hev]
      refine ⟨by simp, ?_⟩
      intro r hr
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hr
      subst hr
      exact ⟨ρ, η, c₁, rfl, hE, he, OpT_TvOK hP hop htv, hf, retPw_skel hPS hRP (skel_subst_eq (OpT_retSk hop) th.σs 0 0 0), hDy.letW hterm rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:7356 tstepM_idx
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_idxB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.idx b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT' := hT
  rw [hterm] at hT'
  cases hT' with
  | let_ hop _ =>
      obtain ⟨rt, ws, hev, -⟩ := idx_stepB (g := g) (s := stOf mem pairs th) hop hi htv
      exact liftB hm (tstep_idxB (hDy := hDy) hterm hP hT hi hE htv hRP hPS) (same_let hterm (fun _ _ _ _ h => by cases h)
        (fun _ _ h => by cases h) (fun r hr => by
          rw [hev, List.mem_singleton] at hr; subst hr; exact same_of_eq rfl))
end
end TermStep.Flat

-- PORTB TermStep.lean:8670 tstepM_loadOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hnwc : wordOf (close th.σs (.ptr .own u)) = none := by
    rw [close_ptr]; exact wordOf_ptr_of_wordFree (wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv (bind_opaqueOK hb)
  have hwr : wordOf (Ty.ptr .own ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [close_ptr, hX] at hnwc; simp [wordOf] at hnwc
    | _ => rfl
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (bind_opaqueOK hb) hea rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:8723 tstepM_storeOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u)) (hnw : wordOf (Ty.ptr .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeB hm hsto hown husA hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:8785 tstepM_xchgOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .own u) = some (.own, u))
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h =>
    hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have husA : accs c.ty = some us := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords us) := by rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ⟨lab, 0⟩ false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ⟨lab, 0⟩ false us 0 (stOf mem pairs th) → PromAbove r1.1 →
      MemInvB g (CE η) r1.1 :=
    fun r1 h hp1 => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := false)
    us wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeB (hm1 (s1, old) h1 hp1) hsto hown husA hval hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:9083 tstepM_loadLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadWord hp hw _ _ => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | loadPub hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadRgn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadCap hp _ hc _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadTorn hp _ hc _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | loadOwn hp _ hc haf hb =>
  obtain ⟨t, u', hp, hc, haf, hb⟩ : ∃ t u', cx.peek a = .ok t ∧ cellOf t = some (.own, u') ∧
      affine cx.ke u' = false ∧ cx.bind x u' = .ok c' := ⟨_, _, hp, hc, haf, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  obtain ⟨rt, ws, hea, hv, hl⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hnb : ∀ n e, ¬ Fd (.array (.lit n) e) (cl ρ η.wit 0 0 u) := fun n e hF => by
    have := Fd_arrFree hF haf'; simp [Ty.arrFree] at this
  obtain ⟨ad, c, hws, hsto, hat, hmode, hini⟩ :=
    cell_targetB (bkG := False) (rfl : cellOf (.loc .own u) = some (.own, u)) hnb hv
  obtain ⟨pw, rfl, hpw⟩ := map_singleton hws
  have hsk := hl.2.1
  obtain ⟨μr, ru, rfl, -, hsku⟩ : ∃ μr ru, rt = .loc μr ru ∧ skelM μr = skelM .own ∧
      etok (skel ru) = etok (skel (close th.σs u)) := by
    simp only [close, substTs, skel, etok] at hsk
    obtain ⟨μr, ru, rfl, h1, h2⟩ := eskel_eq_loc hsk
    exact ⟨μr, ru, rfl, h1, h2⟩
  have hwf := wordFree_close hi.2.2.2.2.2.1 u (wordFreeIn_of_affine u haf)
  have hwr : wordOf (Ty.loc μr ru) = none := by
    cases ru with
    | word r P =>
        obtain ⟨r', hX⟩ := eskel_word (show etok (skel (close th.σs u)) = .word (.lit 0) P by rw [← hsku]; rfl)
        rw [hX] at hwf; simp [Ty.wordFree, Ty.wordFreeIn] at hwf
    | _ => rfl
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have hsig : sig ru = sig (cl ρ η.wit 0 0 u) := by
    have h1 : sig ru = sig (close th.σs u) := sig_of_eskel hsku
    rw [h1]; exact sig_WitL hi.2.2.2.1 ρ (bind_opaqueOK hb) (lt_of_guardT htb hi.2.2.2.2.1)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := acq)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (cell_lyt hl.2.2.2.2 rfl rfl).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htb (cell_lyt hl.2.2.2.2 rfl rfl).2)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ru, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, hwr, Option.isSome_none,
      Bool.false_eq_true, ↓reduceIte, hus, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:9855 tstepM_storeLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u)) (hnw : wordOf (Ty.loc .own u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | storeWordGive hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordKeep hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storeWordHand hp hw => exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
  | storePub hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeRgn hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeCap hp _ hc => exfalso; rw [hpk] at hp; cases hp; simp [cellOf] at hc
  | storeOwn hp _ hc hwf hu hsub hb =>
  obtain ⟨t, u', tv, c₁, hp, hc, hwf, hu, hsub, hb⟩ : ∃ t u' tv c₁, cx.peek a = .ok t ∧
      cellOf t = some (.own, u') ∧ Ty.wordFreeIn cx.ke u' = true ∧ cx.use v = .ok (tv, c₁) ∧
      SubS c₁ tv u' ∧ c₁.bind x .unit = .ok c' :=
    ⟨_, _, _, _, hp, hc, hwf, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hsigu : sig (close th.σs u) = sig (cl ρ η.wit 0 0 u) :=
    sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1)
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig hsigu]; exact (Lay_canon hsub hlv).2.2.2.1
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => hwcu (by rw [h]; simp [wc, accs])
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi hpk htv ho hwcu
  obtain ⟨us, hus⟩ : ∃ us, accs ru = some us := by
    have : wc ru ≠ none := by rw [wc_of_sig hsig]; exact hwcu
    cases h : accs ru with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB hm hsto hown hat hini hna hval hwUA hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:9918 tstepM_xchgLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a v : At} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.xchg a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc .own u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchg hp hx hu hsub hb =>
  obtain ⟨t, u', o, tv, c₁, hp, hx, hu, hsub, hb⟩ : ∃ t u' o tv c₁, cx.peek a = .ok t ∧
      XchgCell cx t u' o ∧ cx.use v = .ok (tv, c₁) ∧ (SubS c₁ tv u' ∨ SubS c₁ tv o) ∧
      c₁.bind x o = .ok c' := ⟨_, _, _, _, _, hp, hx, hu, hsub, hb⟩
  rw [hpk] at hp; cases hp
  cases hx with
  | rgn _ hc _ _ _ => simp [cellOf] at hc
  | own _ hc _ =>
  simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc; subst hc
  have hsub : SubS c₁ tv u := hsub.elim id id
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  have htb : tb cx.ke.length u = true :=
    tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .own u) = some (.own, u))
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ n e, cl ρ η.wit 0 0 u ≠ .array (.lit n) e := fun n e h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have hwcu : wc (cl ρ η.wit 0 0 u) ≠ none := by
    rw [← wc_of_sig (sig_WitL hi.2.2.2.1 ρ ho (lt_of_guardT htb hi.2.2.2.2.1))]
    exact (Lay_canon hsub hlv).2.2.2.1
  obtain ⟨ad, c, pw, μr, ru, hea, hpw, hsto, hat, hini, hown, hsku, hsig⟩ := locViewB hi hpk htv ho hwcu
  obtain ⟨us, hus, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2)
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw ad false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch pw ad false us wsv 0 s1).map fun s2 => (s2, ru, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw ad false us 0 (stOf mem pairs th) → PromAbove r1.1 → MemInvB g (CE η) r1.1 :=
    fun r1 h hp1 => by
      obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
      exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := false)
    us wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (hm1 (s1, old) h1 hp1) hsto hown hat hini hna hval hwUA hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10068 tstepM_loadAt
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadAtB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.loadAt b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAt hp hbuf hint hlt hltk _ hb =>
  obtain ⟨t, u, n, k, j, hp, hbuf, hint, hlt, hltk, hb⟩ : ∃ t u n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧ cx.bind x u = .ok c' :=
    ⟨_, _, _, _, _, hp, hbuf, hint, hlt, hltk, hb⟩
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, hini, hsku, hsig, htbS, -⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk (bind_opaqueOK hb)
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) htbS (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, ur, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10108 tstepM_xchgAt
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgAtB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAt b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAt hp hbuf _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, n, k, j, tv, c₁, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv u ∧ c₁.bind x u = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hint, hlt, hltk, hu, hsub, hb⟩
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, c, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, hini, hsku, hsig, htb, -⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk ho
  have haf' : (cl ρ η.wit 0 0 u).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af u 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 u ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us)) (arch := g.arch) (pw := w) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  rw [hus] at hus'; cases hus'
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsig hus
  have hwUA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2).symm.trans hus
  have hwU : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 s1).map fun s2 => (s2, ur, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us)) false us 0 (stOf mem pairs th) → PromAbove r1.1 →
      MemInvB g (CE η) r1.1 := fun r1 h hp1 => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := w)
    (a := offs ad (ev ρ j * nWords us)) (rel := false) us wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j * nWords us)) (hm1 (s1, old) h1 hp1) hsto hown hat hini hna hval hwUA hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10295 tstepM_loadAtF
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadAtFB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.loadAtF b i q) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadAtF hp hbuf hct hop hint hlt hltk _ hb =>
  obtain ⟨t, u, c, n, k, j, hp, hbuf, hct, hop, hint, hlt, hltk, hb⟩ : ∃ t u c n k j, cx.peek b = .ok t ∧
      bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧ IntIdx cx i j ∧
      LtI cx j n ∧ LtI cx j k ∧ cx.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hb⟩
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hmode, -, hsku, hsig, htbS, hiniF⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat' (hiniF o _ hato) hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 (bind_opaqueOK hb) (tb_compTy q u c hct htbS) (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco))
  have key : tstep g mem pairs th =
      (loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, cR, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hj, addrOf, hwv, hbe, hus, hco, hcs, List.map_map]; rfl
  rw [key]
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hr0), fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl', rfl⟩ := hr
  obtain ⟨hvr, hlay, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl' (hpr0)
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl') (loadUnits_vWr _ _ _ _ hl')⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10339 tstepM_xchgAtF
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_xchgAtFB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {q : List Nat} {e : Expr}
    (hterm : th.term = .let_ x (.xchgAtF b i q v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | xchgAtF hp hbuf hct hop _ hint hlt hltk hu hsub hb =>
  obtain ⟨t, u, c, n, k, j, tv, c₁, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩ : ∃ t u c n k j tv c₁,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ compTy u q = some c ∧ cx.opaqueOK u = true ∧
      IntIdx cx i j ∧ LtI cx j n ∧ LtI cx j k ∧
      cx.use v = .ok (tv, c₁) ∧ SubS c₁ tv c ∧ c₁.bind x c = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hct, hop, hint, hlt, hltk, hu, hsub, hb⟩
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK c = true := sub_opaqueOK hsub hotv
  obtain ⟨rt, w, ad, cc, μr, ur, us, rti, wi, hea, hwv, hei, hj, hbe, hus, hsto, hat, hown, -, hsku, hsig, htbu, hiniF⟩ :=
    slot_viewB (bkG := False) hi.1 hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hint hlt hltk hop
  have htb : tb cx.ke.length c = true := tb_compTy q u c hct htbu
  obtain ⟨cR, o, hco, hskc, hsgc, -, hato⟩ := compOff_rt q u c ur us hct hsku hsig hus
  have haf' : (cl ρ η.wit 0 0 c).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af c 0 0 (bind_arrFree hb)
  have hna : ∀ N e', cl ρ η.wit 0 0 c ≠ .array (.lit N) e' := fun N e' h => by
    rw [h] at haf'; simp [Ty.arrFree] at haf'
  have hat' : AtOff cc.ty (offs ad (ev ρ j * nWords us + o)).offset (cl ρ η.wit 0 0 c) := by
    have h2 := AtOff_trans hat hato
    simpa [offs, Nat.add_assoc] using h2
  have hiniC := hiniF o _ hato
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨cs, hcs, ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j * nWords us + o)) (arch := g.arch) (pw := w)
    (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown hat' hiniC hna hskc hsgc
      (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco)
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco))
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsub ho htb hvv hlv hsgc hcs
  have hwUA : accs (cl ρ η.wit 0 0 c) = some cs := (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho htb (compOff_lyt q u c ur cR o hct hsku (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2 hco)).symm.trans hcs
  have hwU : wc (cl ρ η.wit 0 0 c) = some (nWords cs) := by rw [← wc_of_sig hsgc]; simp [wc, hcs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us + o)) false cs wsv 0 s1).map fun s2 => (s2, cR, old)).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hj, addrOf, hwv, hbe, hus, hco, hcs]
  rw [key]
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch w (offs ad (ev ρ j * nWords us + o)) false cs 0 (stOf mem pairs th) → PromAbove r1.1 →
      MemInvB g (CE η) r1.1 := fun r1 h hp1 => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp1
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := w)
    (a := offs ad (ev ρ j * nWords us + o)) (rel := false) cs wsv 0 r0.1 hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, List.mem_map_of_mem hs2⟩)),
    fun r hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  rw [List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  have hp2 : PromAbove s2 :=
    hpr0
  have hp1 : PromAbove s1 := storeUnits_promAbove hs2 hp2
  obtain ⟨hvr, hlay, -⟩ := hld (s1, old) h1 hp1
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j * nWords us + o)) (hm1 (s1, old) h1 hp1) hsto hown hat' hiniC hna hval hwUA hlen s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:10938 tstepM_bufInitB
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_bufInitBB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hZ : ZOK g (CE η) th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ∃ E', EFootPB g (CE η) E' (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) ∧ ThInvEB g.lbase g.n g.i p E' r.2.2 ∧
        MemInvB g E' (stOf r.1 r.2.1 r.2.2) ∧ BufInitBump th b i E' := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | bufInit hu hbuf hint heq hlt hu2 hsub hb =>
  obtain ⟨t, tv, u, n, k, j, c₁, c₂, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩ : ∃ t tv u n k j c₁ c₂,
      cx.use b = .ok (t, c₁) ∧ bufOf t = some (.own, n, u, k) ∧ IntIdx c₁ i j ∧ EqI c₁ j k ∧
      LtI c₁ k n ∧ c₁.use v = .ok (tv, c₂) ∧ SubS c₂ tv u ∧
      c₂.bind x (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1)))) = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hu, hbuf, hint, heq, hlt, hu2, hsub, hb⟩
  have ht : t = .refine (.loc .own (.array n u)) (.ini k) := by
    unfold bufOf at hbuf; split at hbuf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hbuf
      obtain ⟨h1, rfl, rfl, rfl⟩ := hbuf; subst h1; rfl
    · simp at hbuf
  subst ht
  have htu := use_TvOK hu htv
  obtain ⟨hi1, rb, wsb, hea, hvb, hlb⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨hi2, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu2 hi1
  have hJK : ev ρ j = ev ρ k := heq ρ hi1.1
  have hKN : ev ρ k < ev ρ n := hlt ρ hi1.1
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hi1.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hvb0 := hvb
  simp only [VRF, VRb2] at hvb
  obtain ⟨hv, hir⟩ := hvb
  rcases hv with ⟨-, e0, he0⟩ | ⟨ad, c, U, hws, hsto, hat0, hFU, hmode, hini0⟩
  · have he0 := Fd_nonmu he0 (fun b => by simp [cl])
    simp only [cl, clI_zero, Ty.array.injEq, Idx.lit.injEq] at he0
    omega
  obtain rfl := Fd_nonmu hFU (fun b => by simp [cl])
  obtain ⟨w, rfl, hwv⟩ := map_singleton hws
  have hKi : ev ρ k ≤ η.ini ad.label := by
    simp only [IniR] at hir; exact Nat.le_trans (hir.1 ad (by simp [hwv])) (TEnv.selIni_le_ini _ _ _)
  have hKm : ev ρ k ≤ η.rc ad.label := by
    simp only [IniR] at hir; have h := hir.1 ad (by simp [hwv]); rw [TEnv.selIni_loc] at h; exact h
  have hat := hat0
  have hini := hini0
  simp only [cl, clI_zero] at hat hini
  
  have hs' : etok (skel rb) = rf (.loc (skelM .own) (.array (.lit 0) (etok (skel (close th.σs u))))) := by
    rw [hlb.2.1]; rfl
  obtain ⟨μr, nr, ur, ψ, rfl, -, hsu⟩ := buf_runtime' hs'
  
  have htb1 : tb c₁.ke.length u = true := by
    have h := htu.2.1
    rw [← htu.2.2] at h
    simp [tb] at h
    exact h
  have ho : c₁.opaqueOK u = true :=
    sub_opaqueOK hsub (peek_opaqueOK htu.1 (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu2).1)
  have hsig : sig ur = sig (cl ρ η.wit 0 0 u) := by
    have e1 : sig ur = sig (close th.σs u) := sig_of_eskel hsu
    rw [e1]; exact sig_WitL hi1.2.2.2.1 ρ ho (lt_of_guardT htb1 hi1.2.2.2.2.1)
  obtain ⟨us0, hus0⟩ : ∃ us, accs (cl ρ η.wit 0 0 u) = some us := by
    rcases AtOff_lay hat with h | ⟨n', e', he', h⟩
    · simp [accs] at h
    · simp only [Ty.array.injEq] at he'; rw [he'.2]
      exact Option.ne_none_iff_exists'.1 h
  obtain ⟨us, hus⟩ : ∃ us, accs ur = some us := by
    have : wc ur ≠ none := by rw [wc_of_sig hsig]; simp [wc, hus0]
    cases h : accs ur with
    | none => simp [wc, h] at this
    | some us => exact ⟨us, rfl⟩
  have hweA : accs (cl ρ η.wit 0 0 u) = some us := (accs_rtWB hE.2.1 hi1.2.2.2.1 hi1.2.2.2.2.1 ho htb1 (buf_lyt hlb.2.2.2.2 rfl).2).symm.trans hus
  have hwe : wc (cl ρ η.wit 0 0 u) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨hval, hlen⟩ := ownStoreValB (cx := c₁) hE.2.1 hi1.2.2.2.1 hi1.2.2.2.2.1 hi2.1 hsub ho htb1 hvv hlv hsig hus
  
  let ini' := bumpIni η.ini ad.label (ev ρ j + 1)
  let rini' := bumpIni η.rini ad.label (ev ρ j + 1)
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  have hile : ∀ l, η.ini l ≤ ini' l := bumpIni_le η.ini ad.label (ev ρ j + 1)
  have hx : ExtB η (η.withStoB η.sto ini' (Ri := rini')) := Ext_withStoB hE.2.1 (fun l c h => h) hile (Ri := rini') (hRi := hri')
  let rtR : Ty := Ty.refine (Ty.loc μr (Ty.array nr ur)) (Pred.ini (Idx.lit (ev ρ j + 1)))
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch w (offs ad (ev ρ j * nWords us)) false us wsv 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, rtR, [w]) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, numOf, hwi, addrOf, hwv, bufElem, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := w)
    (a := offs ad (ev ρ j * nWords us)) (rel := false) us wsv 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr hpa => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  have hvr : (VRF False) ρ (η.withStoB η.sto ini' (Ri := rini')) (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      (shp rtR) [w] := by
    have h1 := VR_extB hE.2.1 hx hvb0
    simp only [VRF, VRb2] at h1 ⊢
    refine ⟨h1.1, fun a ha => ?_, fun hp => by obtain ⟨_, _, h⟩ := hp; simp [pp] at h⟩
    have hav : a = ad := by simp [hwv] at ha; exact ha.symm
    subst hav
    show ev ρ (.add k (.lit 1)) ≤ min (bumpIni η.ini a.label (ev ρ j + 1) a.label)
      (bumpIni η.rini a.label (ev ρ j + 1) a.label)
    rw [bumpIni_self, bumpIni_self]; simp [ev]; omega
  have hlay : Lay th.σs (.refine (.loc .own (.array n u)) (.ini (.add k (.lit 1))))
      rtR [w] := Lay_repred hlb
  exact ⟨CE (η.withStoB η.sto ini' (Ri := rini')), EFoot_iniB (harr := .inr (ArrAt_of_bufB hm hsto hmode hat)) rfl rfl rfl rfl rfl rfl ⟨c, hsto, hmode⟩
      (hz := by
        by_cases hzl : g.zf ad.label
        · by_cases hpf : (CE η).pfr ad.label = none
          · exact .inr (.inl hpf)
          · have hlo : ev ρ j < η.ini ad.label ∧ ev ρ j < η.rini ad.label := by
              by_cases hrc : (CE η).rc ad.label ≤ ev ρ j
              · exact hZ _ ⟨x, b, i, v, e, _, w, ad, 0, hterm, hea, hwv, rfl⟩ hzl x b i v e hterm _ w ad _ wi (ev ρ j)
                  hea hwv hei (by simp [numOf, hwi]) rfl hpf hrc
              · have h := hKm; change ¬ (min (η.ini ad.label) (η.rini ad.label) ≤ ev ρ j) at hrc
                unfold TEnv.rc at h; omega
            refine .inr (.inr ⟨?_, ?_⟩)
            · show bumpIni η.ini ad.label (ev ρ j + 1) ad.label = η.ini ad.label
              rw [bumpIni_self]; omega
            · show bumpIni η.rini ad.label (ev ρ j + 1) ad.label = η.rini ad.label
              rw [bumpIni_self]; omega
        · exact .inl hzl)
      (hfz := fun _ => by
        show bumpIni η.ini ad.label (ev ρ j + 1) ad.label = η.ini ad.label ∨ η.ini ad.label ≤ η.rini ad.label
        have h := hKm; unfold TEnv.rc at h; rw [bumpIni_self]; omega)
      (fun l => ite_ini_cases _ _ _ l)
      (riniW_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hini hweA
        (show ev ρ j ≤ η.rc ad.label by omega) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) s' hs'), ⟨ρ, η.withStoB η.sto ini' (Ri := rini'), c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv',
      bind_FInvB hb (FInv_extB hE.2.1 hx hi2) hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_bufInitB (E := CE η) (E' := CE (η.withStoB η.sto ini' (Ri := rini'))) hm hsto hmode hat hini hweA
      (by omega) (show ev ρ j ≤ η.rc ad.label by omega) hval hlen rfl rfl rfl (bumpIni_self _ _ _)
      (fun l' h => bumpIni_other _ _ _ l' h) (bumpIni_self _ _ _) (fun l' h => bumpIni_other _ _ _ l' h) rfl rfl (fun _ _ h => h) rfl (fun l => hri' l) s' hs' hpa,
    fun rt' w' ad' rti' wi' n' he' hw' hei' hn' => by
      rw [hea] at he'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at he'
      obtain ⟨-, rfl⟩ := he'
      rw [hwv] at hw'
      cases hw'
      rw [hei] at hei'
      simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at hei'
      obtain ⟨-, rfl⟩ := hei'
      have hn : n' = ev ρ j := by simp [numOf, hwi] at hn'; exact hn'.symm
      subst hn
      show ev ρ j + 1 ≤ bumpIni η.ini ad.label (ev ρ j + 1) ad.label ∧
        ev ρ j + 1 ≤ bumpIni η.rini ad.label (ev ρ j + 1) ad.label
      rw [bumpIni_self, bumpIni_self]; exact ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:11091 tstepM_bufInit
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_bufInitB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.bufInit b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hZ : ZOK g (CE η) th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨h1, h2⟩ := tstepM_bufInitBB (hDy := hDy) hterm hP hT hi hE htv hm hZ hRP hPS
  exact ⟨h1, fun r hr hpa => let ⟨E', a1, a2, a3, _⟩ := h2 r hr hpa; ⟨E', a1, a2, a3⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:12452 tstepM_newBufA
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newBufAB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFAB p g ρ η th (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | newBuf hwf hsc hop haf hint hb =>
  rename_i k
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wsi, hei, hvi, -⟩ := peek_VRB (bkG := False) hi.2.1 hpi
  obtain ⟨wi, rfl, hwi⟩ := map_singleton (VR_intSB (bkG := False) hti hvi)
  have hlay : accs (close th.σs τ) ≠ none := accs_close hwf hi.2.2.2.2.1 haf hi.2.2.2.2.2.1.2.2
  obtain ⟨us, hus⟩ : ∃ us, accs (close th.σs τ) = some us := Option.ne_none_iff_exists'.1 hlay
  
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hi.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hi.2.2.2.1 ρ hop hr
  have hwT : wc (cl ρ η.wit 0 0 τ) = some (nWords us) := by rw [← wc_of_sig hsig]; simp [wc, hus]
  obtain ⟨usT, husT⟩ : ∃ usT, accs (cl ρ η.wit 0 0 τ) = some usT := by
    cases h : accs (cl ρ η.wit 0 0 τ) with
    | none => simp [wc, h] at hwT
    | some usT => exact ⟨usT, rfl⟩
  have hnw : nWords usT = nWords us := by rw [wc_of_accs husT] at hwT; exact Option.some.inj hwT
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  
  let z : Option (List WeakMem.Val) := if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none
  have hzv : ∀ zs, z = some zs → ValOfB η (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ wc (cl ρ η.wit 0 0 τ) = some zs.length := by
    intro zs h
    simp only [z] at h
    split at h
    · exact zero_valOfB hi.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.1 ρ hop hr haf ‹_› h
    · cases h
  have hstat : zeroableIn [] cx.ke τ = true → z.isSome = true := by
    intro h
    have hR := KindSound.zero_close cx.ke th.σs τ hi.2.2.2.2.2.1.2.1 h
    obtain ⟨zs, hzs, -⟩ := zpB _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
    simp [z, hR, hzs]
  
  let K := ev ρ k
  let lbl := freshLabel g.lbase g.n g.i th.nalloc
  let iv : Nat := if z.isSome then K else 0
  let ini' := bumpIni η.ini lbl iv
  let rini' := bumpIni η.rini lbl iv
  have hri' : ∀ l, η.rini l ≤ rini' l := bumpIni_le _ _ _
  let E0 := CE (η.withStoB η.sto ini' (Ri := rini'))
  let T := Ty.array (.lit K) (cl ρ η.wit 0 0 τ)
  let E' := allocE E0 lbl T
  let η' := η.withStoB E'.sto ini' (Ri := rini')
  obtain ⟨hmo, hoo, hpl, hfr, hsn, hoh, hpd, hopub, hpi, hbi, hpo⟩ := id hm
  obtain ⟨hnone, hfresh, hi0, -, hpf0⟩ := hfr.1 th.nalloc (Nat.le_refl _)
  have hnone0 : E0.sto lbl = none := hnone
  have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun l c h => allocE_sub (η := E0) hnone0 h) (bumpIni_le _ _ _)
    (Ri := rini') (hRi := hri')
  let rtR : Ty := .refine (.loc .own (.array (.lit K) (close th.σs τ))) (.ini (.lit iv))
  let R := allocBuf lbl (K * nWords us) z (stOf mem pairs th)
  have key : tstep g mem pairs th =
      [(R.1.mem, R.1.pairs, withS { th with term := e, env := (x, rtR, [R.2]) :: th.env } R.1)] := by
    simp only [tstep, hterm, evalOp, hei, numOf, hus, Option.bind_eq_bind, Option.bind_some, hwi]; rfl
  rw [key]
  refine ⟨by simp, fun r hr' => ?_⟩
  simp only [List.mem_singleton] at hr'
  subst hr'
  have hpw : R.2 = cst (.loc ⟨lbl, 0⟩ 0) := rfl
  
  have hsub0 : ∀ l c, (CE η).sto l = some c → E0.sto l = some c := fun l c h => h
  have hile0 : ∀ l, (CE η).ini l ≤ E0.ini l := bumpIni_le η.ini lbl iv
  have hmo0 : MemOKPB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).promises :=
    MemOKP_monoB hmo rfl rfl hsub0 hile0 (fun t m c h hc => hc)
  have hmono0 : ∀ {U : Ty} {vs : List Word}, ValOfB (CE η) U vs → ValOfB E0 U vs :=
    fun h => ValOf_monoB (η₁ := CE η) (η₂ := E0) rfl rfl hsub0 hile0 h
  have hoo0 : OwnOKPFB E0 (stOf mem pairs th).mem (stOf mem pairs th).pairs (stOf mem pairs th).vs
      (stOf mem pairs th).promises := by
    intro l c hc ho
    have hne : l ≠ lbl := fun h => by rw [h] at hc; rw [hnone0] at hc; cases hc
    exact OwnCellF_envB (hoo l c hc ho) hmono0 (bumpIni_other _ _ _ _ hne) rfl hmo.2.2 (bumpIni_other _ _ _ _ hne)
  have hi0' : η.ini lbl = 0 := hi0
  have hini : E0.ini lbl ≤ K := by
    show bumpIni η.ini lbl iv lbl ≤ K
    rw [bumpIni_self, hi0']
    refine Nat.max_le.2 ⟨Nat.zero_le _, ?_⟩
    simp only [iv]; split <;> omega
  have hini0 : 0 < E0.ini lbl → z ≠ none := by
    intro h hz0
    have : E0.ini lbl = 0 := by
      show bumpIni η.ini lbl iv lbl = 0
      rw [bumpIni_self, hi0']; simp [iv, hz0]
    omega
  have hzE : ∀ zs, z = some zs → ValOfB E' (cl ρ η.wit 0 0 τ) (zs.map cst) ∧ zs.length = nWords usT :=
    fun zs h => ⟨ValOf_monoB (η₁ := η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (hzv zs h).1,
      by have := (hzv zs h).2; rw [hwT] at this; rw [hnw]; exact (Option.some.inj this).symm⟩
  have hab := allocBuf_okPB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
    (s := stOf mem pairs th) (η := E0) husT hzE
    hini hini0 hfresh hnone0 hpl hpo.2.1 hmo0 hoo0 hpf0
  rw [hnw] at hab
  obtain ⟨hmo', hoo', -⟩ := hab
  obtain ⟨hg, hpr, hna⟩ := allocBuf_grows lbl (K * nWords us) z (stOf mem pairs th)
  have hwE : ∀ T o w, WordOKB (CE η) T o w → WordOKB E' T o w := fun T o w h =>
    WordOK_monoB (η₁ := CE η) (η₂ := E') rfl rfl (fun l c h' => allocE_sub (η := E0) hnone0 h')
      (bumpIni_le _ _ _) (fun _ _ h' => h') (fun _ h' => h') h
  have hiniE : ∀ l c o, l ≠ lbl → InitR E' c l o → InitR (CE η) c l o := fun l c o hl hi N1 e1 us1 h1 h2 => by
    have := hi N1 e1 us1 h1 h2
    rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  have hoh' : OwnHidPB E' R.1.mem R.1.vs R.1.promises := by
    refine ⟨?_, ?_⟩
    · intro l c hc ho o hi
      by_cases hl : l = lbl
      · rw [hl] at hc hi
        have hcT : c = ⟨T, some η.tid⟩ := by
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at hc; exact (Option.some.inj hc).symm
        subst hcT
        rw [hl]
        unfold HiddenPB
        intro t m hP hm hloc hnok
        exfalso
        rcases Option.eq_none_or_eq_some z with hzc | ⟨zs, hzc⟩
        · 
          have h0 : E'.ini lbl = 0 := by
            show bumpIni η.ini lbl iv lbl = 0
            rw [bumpIni_self, hi0']; simp [iv, hzc]
          have := hi K (cl ρ η.wit 0 0 τ) usT rfl husT
          rw [show E'.rc lbl = 0 by have := E'.rc_le_ini lbl; omega, Nat.zero_mul] at this; exact Nat.not_lt_zero _ this
        · 
          apply hnok
          by_cases hlt : t < (stOf mem pairs th).mem.size
          · rw [hg.2.1 t hlt] at hm
            exact (hP (hfresh t m hm (by rw [hloc]))).elim
          · have hw := allocBuf_newOKB (lbl := lbl) (N := K) (e := cl ρ η.wit 0 0 τ) (us := usT) (z := z)
              (s := stOf mem pairs th) (η := E0) husT hzE zs hzc t m (by omega) (by rw [hnw]; exact hm)
            rw [hloc] at hw; exact hw
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        exact HiddenP_growsAtB (hoh.1 l c hc ho o (fun N1 e1 us1 h1 h2 => by
            have := hi N1 e1 us1 h1 h2; rw [hrc] at this; exact this))
          (hwE _ _) (allocBuf_vWr_le _ _ _ _) hg hl
          (fun t h1 h2 => absurd h1 h2)
    · intro l c hc ho hlt
      by_cases hl : l = lbl
      · exfalso
        have h1 : E'.ini lbl ≤ E'.rini lbl := by
          show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl
          rw [bumpIni_self, bumpIni_self, hi0']; omega
        have h2 : E'.rc lbl = E'.ini lbl := Nat.min_eq_left h1
        rw [hl] at hlt; omega
      · rw [allocE_ne hl] at hc
        have hrc : E'.rc l = (CE η).rc l := TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)
        have hie : E'.ini l = (CE η).ini l := bumpIni_other _ _ _ _ hl
        obtain ⟨f, hf, hsn', hH⟩ := hoh.2 l c hc ho (by rw [hrc, hie] at hlt; exact hlt)
        exact ⟨f, hf, fun hz => hsn' (fun hz0 => hz ((ZW.stoAt (allocE_ne hl)).2 hz0)),
          fun o hi => HiddenP_growsAtB (hH o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
          (fun t h1 h2 => absurd h1 h2)⟩
  have hpd' : PubDefPB E' R.1.mem R.1.promises := by
    intro l c f hc hown hf o hi
    by_cases hl : l = lbl
    · rw [hl] at hc
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at hc; cases hc; exact (hown rfl).elim
    · rw [allocE_ne hl] at hc
      exact HiddenP_growsAtB (hpd l c f hc hown hf o (hiniE l c o hl hi)) (hwE _ _) (Nat.le_refl _) hg hl
        (fun t h1 h2 => absurd h1 h2)
  have hopub' : OwnPubV E' R.1 := by
    intro l c f hc ho hf
    by_cases hl : l = lbl
    · rw [hl] at hf; exact absurd (hf.symm.trans hpf0) (by simp)
    · rw [allocE_ne hl] at hc
      exact ((hopub.allocBuf hpl lbl (K * nWords us) z) l c f hc ho hf).imp id (Or.imp id fun hw => hw.congrE
        fun a ha hi c1 N1 e1 us1 h1 h2 h3 => by
          have hne : a.label ≠ lbl := fun e => hl (ha.symm.trans e)
          have := hi c1 N1 e1 us1 (by rw [allocE_ne hne]; exact h1) h2 h3
          rwa [show E'.rc a.label = (CE η).rc a.label from
            TEnv.rc_congr (bumpIni_other _ _ _ _ hne) (bumpIni_other _ _ _ _ hne)] at this)
  have hrcl : E'.rc lbl = E'.ini lbl := Nat.min_eq_left (show bumpIni η.ini lbl iv lbl ≤ bumpIni η.rini lbl iv lbl by
    rw [bumpIni_self, bumpIni_self, hi0']; omega)
  have hpi' : PubInvB E' R.1 := by
    refine PubInv_growB (E := CE η) (hbs := fun l hb h => by
        by_cases hl : l = lbl
        · subst hl; exact absurd (hbi.1 th.nalloc (Nat.le_refl _)) hb
        · rw [allocE_ne hl]; exact h) hpi hmo.2.2 hg (fun _ h => h) (fun t h1 h2 => absurd h1 h2) rfl rfl
      (fun l c h => allocE_sub (η := E0) hnone0 (hsub0 l c h)) hile0 rfl rfl
      (fun c h => by
        have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
        rw [h2] at h; rw [← Option.some.inj h]; rfl)
      (fun l c h => ?_) (fun l c b S us' h hseg hu' hini => ?_) (hpl := fun _ _ hlt => absurd hlt (by rw [hrcl]; exact Nat.lt_irrefl _))
      (hrcg := fun l h => by
        by_cases hl : l = lbl
        · rw [hl, hrcl] at h; exact absurd h (Nat.lt_irrefl _)
        · exact ⟨by rwa [TEnv.rc_congr (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl),
            show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl] at h,
            Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl)⟩)
      (hfi := fun l c h ho => by
        by_cases hl : l = lbl
        · rw [hl] at h
          have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
          rw [h2] at h; rw [← Option.some.inj h] at ho; exact absurd rfl ho
        · exact Nat.le_of_eq (show E'.ini l = (CE η).ini l from bumpIni_other _ _ _ _ hl))
    · by_cases hl : l = lbl
      · exact Or.inr (by rw [hl]; exact hpf0)
      · rw [allocE_ne hl] at h; exact Or.inl h
    by_cases hl : l = lbl
    · rw [hl] at h
      have h2 : E'.sto lbl = some ⟨T, some η.tid⟩ := allocE_eq
      rw [h2] at h; cases h
      refine Or.inr ?_
      rcases hseg with ⟨-, rfl, -⟩ | ⟨N1, us1, j1, hT1, -, -, -⟩
      · simp [T, accs] at hu'
      · have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N1) S := hT1
        simp only [Ty.array.injEq, Idx.lit.injEq] at hT2
        obtain ⟨-, rfl⟩ := hT2
        rw [husT] at hu'; obtain rfl := Option.some.inj hu'
        obtain ⟨-, jb, -, hjb, -⟩ := hini K (cl ρ η.wit 0 0 τ) rfl
        have hpos : 0 < E0.ini lbl := by
          rw [hl] at hjb; exact Nat.lt_of_le_of_lt (Nat.zero_le _) hjb
        obtain ⟨zs, hzs⟩ := Option.ne_none_iff_exists'.1 (hini0 hpos)
        obtain ⟨h1, h2⟩ := hzE zs hzs
        exact ⟨zs.map cst, h1, by rw [List.length_map]; exact h2⟩
    · rw [allocE_ne hl] at h
      refine Or.inl ⟨h, fun N1 e1 h1 => ?_⟩
      have := hini N1 e1 h1
      rw [show E'.ini l = η.ini l from bumpIni_other _ _ _ _ hl] at this; exact this
  refine ⟨E', (by
    intro l c N u hf hc hty
    refine ⟨x, n, τ, e, hterm, ?_⟩
    obtain ⟨j, hj, -, rfl⟩ := hf
    by_cases hl : freshLabel g.lbase g.n g.i j = lbl
    · have hc2 : E'.sto lbl = some ⟨T, some E0.tid⟩ := allocE_eq
      rw [hl, hc2] at hc
      cases hc
      have h2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) u := hty
      injection h2 with _ h3
      exact h3.symm
    · have hc2 : E'.sto (freshLabel g.lbase g.n g.i j) = E0.sto (freshLabel g.lbase g.n g.i j) := allocE_ne hl
      have h0 : E0.sto (freshLabel g.lbase g.n g.i j) = none := (hfr.1 j hj).1
      rw [hc2, h0] at hc
      cases hc),
    EFoot_freshB rfl rfl rfl rfl (lt_of_eq_succ hna) (fun l => allocE_sto_cases (T := T) ⟨Clo_cl (fun k => (hE.2.1 k).1) ρ (.array (.lit K) τ),
    mg_cl (fun k => (hE.2.1 k).1.1) (WitAF.mg hi.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [mg] using mg_of_wf τ hwf),
    noIallV_cl (WitAF.ni hi.2.2.2.2.2.2.1) (.array (.lit K) τ) 0 0 (by simpa [noIallV] using hniA), trivial⟩
        (allocBuf_newT (lbl := lbl) (K := K) (z := z) (s := stOf mem pairs th) (e := cl ρ η.wit 0 0 τ) husT hnw)
        (allocBuf_undefT (lbl := lbl) (K := K) (z := z) (s := stOf mem pairs th) (e := cl ρ η.wit 0 0 τ) husT hnw
          (fun h0 => by
            cases hzz : zeroableIn [] [] (close th.σs τ) with
            | false =>
              show (if zeroableIn [] [] (close th.σs τ) = true then zeroWords (close th.σs τ) else none) = none
              simp [hzz]
            | true =>
              exact absurd ((zrel_zero _ _ [] [] (zrel_WitL hi.2.2.2.1 (fun k => (hE.2.1 k).1) ρ hop hr) hsig
                knone_nil).1 hzz) (by rw [h0]; simp))) l) (fun _ => .inl rfl)
      (fun l => ite_ini_cases _ _ _ l)
      (hrw := RiniW_of_ne fun l c h => bumpIni_other _ _ _ _ fun e => by
        subst e; cases h.symm.trans hnone0),
    ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', bind_FInvB hb (FInv_extB hE.2.1 hx hi) ?_ ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    hmo', hoo', fun t ht => Nat.lt_of_lt_of_le (hpl t ht) hg.1,
      ⟨fun j hj => ?_, PrivCoh_allocBufB hfr.2
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, ho, hp, hT, hus1, hle, hlt⟩ := hu
          refine ⟨c, N, e, us1, by rw [allocE_ne hl] at hc; exact hc, ho, hp, hT, hus1, ?_, hlt⟩
          rwa [TEnv.rc_congr (η' := E') (η := CE η) (bumpIni_other _ _ _ _ hl) (bumpIni_other _ _ _ _ hl)] at hle)
        hoo' hfresh
        (fun a hu hl => by
          obtain ⟨c, N, e, us1, hc, -, -, hT, hus1, hle, hlt⟩ := hu
          rw [hl, show E'.sto lbl = some ⟨T, some η.tid⟩ from allocE_eq] at hc; cases hc
          have hT2 : Ty.array (.lit K) (cl ρ η.wit 0 0 τ) = .array (.lit N) e := hT
          simp only [Ty.array.injEq, Idx.lit.injEq] at hT2; obtain ⟨rfl, rfl⟩ := hT2
          refine Classical.byContradiction fun hz => ?_
          have hs : z.isSome = true := Option.ne_none_iff_isSome.1 hz
          have hrc : K ≤ E'.rc lbl := by
            show K ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
            have hiv : iv = K := by simp only [iv, hs, ↓reduceIte]
            rw [bumpIni_self, bumpIni_self, hiv]
            exact Nat.le_min.2 ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩
          rw [hl] at hle
          have := Nat.mul_le_mul_right (nWords us1) hrc
          exact absurd (Nat.lt_of_lt_of_le hlt (Nat.le_trans this hle)) (Nat.lt_irrefl _))⟩, hsn, hoh', hpd', hopub', hpi',
      BoxInv_allocBuf hbi rfl rfl rfl (fun l hl => by rw [allocE_ne hl]; rfl) (fun l hl => bumpIni_other _ _ _ _ hl),
        PromOK_eq hpo rfl rfl⟩
  · 
    simp only [VRF, VRb2]
    refine ⟨Or.inr ⟨⟨lbl, 0⟩, ⟨T, some η.tid⟩, _, by simp [hpw, cst, Promises.TVal.mk0],
      (show E'.sto lbl = _ from allocE_eq), ?_, .refl, rfl, ?_⟩, ?_⟩
    · simp only [cl, clI_zero]; exact AtOff.here (Or.inr ⟨K, _, rfl, by simp [husT]⟩)
    · intro N' e' h; left; exact ⟨by simp only [cl, clI_zero]; rfl, rfl⟩
    · refine ⟨fun a ha => ?_, fun hp => by obtain ⟨_, _, h⟩ := hp; simp [pp] at h⟩
      have hav : a = ⟨lbl, 0⟩ := by simp [hpw, cst, Promises.TVal.mk0] at ha; exact ha.symm
      subst hav
      show ev ρ _ ≤ min (bumpIni η.ini lbl iv lbl) (bumpIni η.rini lbl iv lbl)
      refine Nat.le_min.2 ⟨?_, ?_⟩
      · rw [bumpIni_self]
        split
        · rename_i hzs
          have h1 := hstat hzs
          have h2 : iv = K := by simp only [iv, h1, ite_true]
          rw [h2]; exact Nat.le_max_right _ _
        · exact Nat.zero_le _
      · rw [bumpIni_self]
        split
        · rename_i hzs
          have h1 := hstat hzs
          have h2 : iv = K := by simp only [iv, h1, ite_true]
          rw [h2]; exact Nat.le_max_right _ _
        · exact Nat.zero_le _
  · refine ⟨fun us' h => by simp [rtR, accs] at h; subst h; rfl, ?_, by simp [rtR, wc, accs], ?_, ?_⟩
    · simp [rtR, skel, close, substTs, skelM, rf]; rfl
    · simp only [rtR, Valid]; exact Or.inr ⟨⟨lbl, 0⟩, by simp [hpw, cst, Promises.TVal.mk0]⟩
    · simp [rtR, close, substTs, lyt, anyB_zero, idxC, ofMs, modeC]; rfl
  · have hj' : th.nalloc ≤ j := by
      have h1 : R.1.nalloc ≤ j := hj
      rw [hna] at h1; exact Nat.le_of_succ_le h1
    obtain ⟨f1, f2, f4, f5⟩ := hfr.1 j hj'
    have hne : freshLabel g.lbase g.n g.i j ≠ lbl := fun h => by
      have := freshLabel_inj_k hn h; subst this
      have h1 : R.1.nalloc ≤ th.nalloc := hj
      rw [hna] at h1; exact absurd h1 (by show ¬ th.nalloc + 1 ≤ th.nalloc; omega)
    refine ⟨by rw [allocE_ne hne]; exact f1, fun t m ht hl => ?_, ?_,
      ⟨by show bumpIni η.rini lbl iv (freshLabel g.lbase g.n g.i j) = 0; rw [bumpIni_other _ _ _ _ hne]; exact f5.1, f5.2⟩⟩
    · change R.1.mem[t]? = some m at ht
      by_cases hlt : t < (stOf mem pairs th).mem.size
      · rw [hg.2.1 t hlt] at ht; exact f2 t m ht hl
      · have := hg.2.2 t m (by omega) ht; exact absurd (hl.symm.trans this) hne
    · show bumpIni η.ini lbl iv (freshLabel g.lbase g.n g.i j) = 0
      rw [bumpIni_other _ _ _ _ hne]; exact f4
end
end TermStep.Flat

-- PORTB TermStep.lean:12782 tstepM_newBuf
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_newBufB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {n : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.newBuf n τ) e) (hniA : noIallV τ = true) (hP : ProgT p)
    (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  (tstepM_newBufAB (hDy := hDy) (hterm := hterm) (hniA := hniA) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hRP := hRP) (hPS := hPS)).imp id
    fun h r hr => (h r hr).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:13216 tstepM_inlBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inlBSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  have hj : j < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  have harmS : (armsOf (.sum rt (close th.σs τ)))[j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed (.sum rt (close th.σs τ)) = true := by simp [isBoxed, sumHead, hS]
  have hRa : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hstoL : η.sto lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num j) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum rt (close th.σs τ), [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := lbl) (us := .one :: us)
      (ws := cst (.num j) :: p0) (s := s) (by simp [nWords, Acc.size] at hnw ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    let B : Box := ⟨j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm hn hbf hal hnw.symm
    simp only at hpw
    subst hpw
    obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
    have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
    have eqw : VEq ws q' := eq1.symm.trans eq'.vals
    have hv2 : (VRF False) ρ η'.unsee t (shp rt) q' :=
      VR_extB hE.2.1.unsee (Ext_unseeB hx) (VR_storeB hE.2.1 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
        (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VR_upB (bkG := False) _ _ _ _ hwq hv))
    have hvr : (VRF False) ρ η' (.sum t τ) (shp (.sum rt (close th.σs τ))) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxLB (B := B) hS hRa rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) hj hq' hv2
        (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
        (by show ((armsOf (.sum rt (close th.σs τ)))[j]?).bind wc = some (p0.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hnw, List.length_map])
    refine ⟨CE η', fun _ => rfl, by rw [hCE]; exact EFoot_seeBoxB (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)),
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPw_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (Lay_box ⟨hshape, hsk, hwc, hval, hly⟩ hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13536 tstepM_inrBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inrBSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = false)
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  obtain ⟨hshape, hsk, hwc, hval, hly⟩ := hl
  obtain ⟨j, p0, arm, us, has, harm, hus, hnw, q1, hq1, eq1⟩ := asArm_box rt ws hval hshape hwc hrb
  let τc := close th.σs τ
  let n := (armsOf τc).length
  have harmS : (armsOf (.sum τc rt))[n + j]? = some arm := by
    simp only [armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed (.sum τc rt) = true := by simp [isBoxed, sumHead, τc, hS]
  have hRb : isBoxed rt = false := hrb
  let s := stOf mem pairs th
  let lbl := freshLabel g.lbase g.n g.i s.nalloc
  let V := s.vs.vRelSt
  have hbnone : η.box lbl = none := hm.2.2.2.2.2.2.2.2.2.1.1 s.nalloc (Nat.le_refl _)
  have hstoL : η.sto lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).1
  have hpfL : η.pfr lbl = none := (hm.2.2.2.1.1 s.nalloc (Nat.le_refl _)).2.2.2.2
  have key : tstep g mem pairs th =
      (alloc g.k g.arch lbl (.one :: us) (cst (.num (n + j)) :: p0) s).map fun (s', pw) =>
        ((if g.boxFence then fenceS s' .st else s').mem, (if g.boxFence then fenceS s' .st else s').pairs,
          withS { th with term := e, env := (x, .sum τc rt, [pw]) :: th.env }
            (if g.boxFence then fenceS s' .st else s')) := by
    simp only [tstep, hterm, evalOp, hea, projM_nbB hrb, has, ol, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil, injM_box (t := Ty.sum (close th.σs τ) rt) (j := (armsOf (close th.σs τ)).length + j) hSb (by rw [harmS]; exact hus), List.map_map]
    rfl
  rw [key]
  refine ⟨?_, ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch) (lbl := lbl) (us := .one :: us)
      (ws := cst (.num (n + j)) :: p0) (s := s) (by simp [nWords, Acc.size] at hnw ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · intro r hr
    rw [List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    let B : Box := ⟨n + j, p0.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm hn hbf hal hnw.symm
    simp only at hpw
    subst hpw
    obtain ⟨q', hq', eq'⟩ := ofArm_wle (WLe_bump V p0) hq1
    have hwq : WLe ws q' := WLe_trans (asArm_ofArm_wle has hq1 eq1) eq'
    have eqw : VEq ws q' := eq1.symm.trans eq'.vals
    have hv2 : (VRF False) ρ η'.unsee t (shp rt) q' :=
      VR_extB hE.2.1.unsee (Ext_unseeB hx) (VR_storeB hE.2.1 (V := V) (fun l hl => hm.2.2.2.2.1 l hl)
        (LocAbove_ofArm hq' (LocAbove_bump V p0)) (VR_upB (bkG := False) _ _ _ _ hwq hv))
    have hvr : (VRF False) ρ η' (.sum τ t) (shp (.sum τc rt)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxRB (B := B) hS hRb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) (Nat.le_add_right _ _)
        (by show ofArm rt (n + j - n) _ = _; rw [Nat.add_sub_cancel_left]; exact hq') hv2
        (ShapeC_vals eqw hshape) hwc (Valid_vals _ _ _ eqw hval)
        (by show ((armsOf (.sum τc rt))[n + j]?).bind wc = some (p0.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hnw, List.length_map])
    refine ⟨CE η', fun _ => rfl, by rw [hCE]; exact EFoot_seeBoxB (nalloc_alloc_box hm.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)),
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPw_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (TermSound.Lay_boxR ⟨hshape, hsk, hwc, hval, hly⟩ hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13652 tstepM_inlBBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inlBBSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inl τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum t τ) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum t τ) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum rt (close th.σs τ)).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hv
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let S := Ty.sum rt (close th.σs τ)
  have harmS : (armsOf S)[B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_left hj]; exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S r1.2.1 r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num B0.tag) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  unfold PAx at hpx
  rw [key] at hpx
  rw [key]
  refine ⟨?_, ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨r1, h1, hp1⟩ := hne h0
    have hlen : r1.2.2.length = nWords us := by rw [← ((hpr r1 h1).2 hp1).2.1.length, hnw]
    obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i r1.1.nalloc) (us := .one :: us)
      (ws := cst (.num B0.tag) :: r1.2.2) (s := r1.1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    have hmem : ((injM g r1.1 S r1.2.1 r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1)) ≠ [] := by
      rw [hinj r1 h1 hp1, List.map_map]; exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
    intro hnil; rw [List.flatMap_eq_nil_iff] at hnil; exact hmem (hnil r1 h1)
  · intro r hr hpr0
    rw [List.mem_flatMap] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have hp1 : PromAbove r1.1 := by
      obtain ⟨f1, f2⟩ := (hpr r1 h1).1
      have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
      have hpa' := hpr0
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
      exact injM_pa hpl1 hr2 hpa'
    obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
    rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨s1, j1, p1⟩ := r1
    simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
    have hm1 : MemInvB g (CE η) s1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
    have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
    simp only at hpw
    subst hpw
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    have hv0 : (VRF False) ρ η' t (vsh 0 (shp rt)) [w] := by rw [vsh_zero rt hrb]; exact VR_extB hE.2.1 hx hv
    have hv1 : (VRF False) ρ η' t (vsh 0 (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_renB (B1 := B0) (B2 := B) hx.1 hw rfl rfl
        (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
        (by simpa [η', TEnv.withStoB] using hsto0)
        (by simp [η', TEnv.withStoB, hini0]) rfl (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
        (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
        (by simp [η', TEnv.withStoB, hini0])
    have hvr : (VRF False) ρ η' (.sum t τ) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxLBB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) hj hv1
        (by show ((armsOf S)[B0.tag]?).bind wc = some (p1.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hlen, List.length_map])
    refine ⟨CE η', fun _ => rfl, EFoot_congrB (s1 := s1) (by rw [hCE]; exact EFoot_seeBoxB (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1,
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPw_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (Lay_box hl hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13773 tstepM_inrBBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_inrBBSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {x : String} {τ : Ty} {a : At} {e : Expr} {t : Ty} {c₁ : Cx}
    {rt : Ty} {ws : List Word} (hterm : th.term = .let_ x (.inr τ a) e) (hn : 0 < g.n)
    (hc' : ∀ c', c₁.bind x (.sum τ t) = .ok c' → Typed p c' e ∧ TvOK c')
    (hb : ∃ c', c₁.bind x (.sum τ t) = .ok c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (rt, ws)) (hv : (VRF False) ρ η t (shp rt) ws) (hl : Lay th.σs t rt ws)
    (hS : (Ty.sum (close th.σs τ) rt).tier = .boxed) (hrb : isBoxed rt = true)
    (hsg : sig rt = sig (cl ρ η.wit 0 0 t))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨c', hb⟩ := hb
  obtain ⟨he, htv'⟩ := hc' c' hb
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hv
  have hj : B0.tag < (armsOf rt).length := (List.getElem?_eq_some_iff.mp harm).1
  let n := (armsOf (close th.σs τ)).length
  let S := Ty.sum (close th.σs τ) rt
  have harmS : (armsOf S)[n + B0.tag]? = some arm := by
    simp only [S, armsOf]; rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact harm
  have hSb : isBoxed S = true := by simp [S, isBoxed, sumHead, hS]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := rt) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have key : tstep g mem pairs th = (projM g s rt [w]).flatMap fun r1 =>
      (injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1) := by
    simp only [tstep, hterm, evalOp, hea, List.map_flatMap, List.map_map]; rfl
  have hinj : ∀ r1 ∈ projM g s rt [w], PromAbove r1.1 → injM g r1.1 S (n + r1.2.1) r1.2.2 =
      (alloc g.k g.arch (freshLabel g.lbase g.n g.i r1.1.nalloc) (.one :: us) (cst (.num (n + B0.tag)) :: r1.2.2) r1.1).map
        fun (s', pw) => (if g.boxFence then fenceS s' .st else s', [pw]) := by
    intro r1 h1 hp
    rw [((hpr r1 h1).2 hp).1]; exact injM_box hSb (by rw [harmS]; exact hus)
  unfold PAx at hpx
  rw [key] at hpx
  rw [key]
  refine ⟨?_, ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨r1, h1, hp1⟩ := hne h0
    have hlen : r1.2.2.length = nWords us := by rw [← ((hpr r1 h1).2 hp1).2.1.length, hnw]
    obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i r1.1.nalloc) (us := .one :: us)
      (ws := cst (.num (n + B0.tag)) :: r1.2.2) (s := r1.1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    have hmem : ((injM g r1.1 S (n + r1.2.1) r1.2.2).map fun r2 =>
        (r2.1.mem, r2.1.pairs, withS { th with term := e, env := (x, S, r2.2) :: th.env } r2.1)) ≠ [] := by
      rw [hinj r1 h1 hp1, List.map_map]; exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
    intro hnil; rw [List.flatMap_eq_nil_iff] at hnil; exact hmem (hnil r1 h1)
  · intro r hr hpr0
    rw [List.mem_flatMap] at hr
    obtain ⟨r1, h1, hr⟩ := hr
    have hp1 : PromAbove r1.1 := by
      obtain ⟨f1, f2⟩ := (hpr r1 h1).1
      have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
      have hpa' := hpr0
      obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr
      exact injM_pa hpl1 hr2 hpa'
    obtain ⟨-, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
    rw [hinj r1 h1 hp1, List.map_map, List.mem_map] at hr
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr
    obtain ⟨s1, j1, p1⟩ := r1
    simp only at hWp e1 e2 e3 e4 e5 e6 e7 hal ⊢
    have hm1 : MemInvB g (CE η) s1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
    have hlen : p1.length = nWords us := by rw [← hWp.length, hnw]
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
    simp only at hpw
    subst hpw
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨n + B0.tag, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    have hv0 : (VRF False) ρ η' t (vsh 0 (shp rt)) [w] := by rw [vsh_zero rt hrb]; exact VR_extB hE.2.1 hx hv
    have hv1 : (VRF False) ρ η' t (vsh n (shp rt)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_renB (B1 := B0) (B2 := B) hx.1 hw rfl rfl
        (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
        (by simpa [η', TEnv.withStoB] using hsto0)
        (by simp [η', TEnv.withStoB, hini0]) (show B0.tag + n = (n + B0.tag) + 0 by omega) (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS)
        (by rw [vsh_zero rt hrb] at *; exact bh_shp rt hrb) hv0
        (by simp [η', TEnv.withStoB, hini0])
    have hvr : (VRF False) ρ η' (.sum τ t) (shp S) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_boxRBB (B := B) hS hrb rfl rfl (by simp [η', TEnv.withStoB]) (Or.inl hBS) (Nat.le_add_right _ _) hv1
        (by show ((armsOf S)[n + B0.tag]?).bind wc = some (p1.map (bumpW V)).length
            rw [harmS]; simp [wc, hus, hlen, List.length_map])
    refine ⟨CE η', fun _ => rfl, EFoot_congrB (s1 := s1) (by rw [hCE]; exact EFoot_seeBoxB (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm))) e5 e7 (congrArg Array.size e1) e4 e1,
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv', ?_, retPw_eq hRP1 (bind_ret hb), hDy.letW hterm rfl⟩, ?_⟩
    · exact bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hvr (TermSound.Lay_boxR hl hS)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:13898 tstepM_inlTS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inlTSB {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    have htv' := OpT_TvOK hP hop htv
    cases hop with
    | inl _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum t τ) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      have hsk : (Ty.sum rt (close th.σs τ)).tier = (close th.σs (.sum _ τ)).tier :=
        tier_of_eskel (by show Ty.sum (etok (skel rt)) _ = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum t τ) = .ok c'' → Typed p c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨he, htv'⟩
      by_cases hS : (Ty.sum rt (close th.σs τ)).tier = .boxed
      · cases hrb : isBoxed rt with
        | false => exact paW <| tstepM_inlBSB (hDy := hDy) (hbf := hbf) (hRP1 := retPw_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb hE hm
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepM_inlBBSB (hDy := hDy) (hbf := hbf) (hRP1 := retPw_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb
              (lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl) hE hm hpx
      · refine paW <| tstepM_inlSB (hDy := hDy) hterm hP (fun t' c₁' hu' => ?_) hT hi hE htv hm hRP hPS
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← hsk]; exact hS
end
end TermStep.Flat

-- PORTB TermStep.lean:13933 tstepM_inlT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inlTB {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inl τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  (tstepM_inlTSB (hDy := hDy) (hRP := hRP) (hPS := hPS) (hterm := hterm) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hbf := hbf) (hpx := hpx)).imp id
    fun h r hr hp => (h r hr hp).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:13943 tstepM_inrTS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inrTSB {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
    rename_i c'
    have htv' := OpT_TvOK hP hop htv
    cases hop with
    | inr _ hu hb =>
      obtain ⟨t, c₁, hu, hb⟩ : ∃ t c₁, cx.use a = .ok (t, c₁) ∧ c₁.bind x (.sum τ t) = .ok c' :=
        ⟨_, _, hu, hb⟩
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      have hsk : (Ty.sum (close th.σs τ) rt).tier = (close th.σs (.sum τ _)).tier :=
        tier_of_eskel (by show Ty.sum _ (etok (skel rt)) = _; rw [hl.2.1]; rfl)
      have hc' : ∀ c'', c₁.bind x (.sum τ t) = .ok c'' → Typed p c'' e ∧ TvOK c'' := fun c'' h => by
        rw [hb] at h; cases h; exact ⟨he, htv'⟩
      by_cases hS : (Ty.sum (close th.σs τ) rt).tier = .boxed
      · cases hrb : isBoxed rt with
        | false => exact paW <| tstepM_inrBSB (hDy := hDy) (hbf := hbf) (hRP1 := retPw_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb hE hm
        | true =>
            have ho : cx.opaqueOK _ = true :=
              peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
            have htb := (use_TvOK hu htv).2.1
            exact tstepM_inrBBSB (hDy := hDy) (hbf := hbf) (hRP1 := retPw_eq hRP (use_ret hu)) hterm hn hc' ⟨c', hb⟩ hi1 hea hv hl hS hrb
              (lay_closed hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl) hE hm hpx
      · refine paW <| tstepM_inrSB (hDy := hDy) hterm hP (fun t' c₁' hu' => ?_) hT hi hE htv hm hRP hPS
        rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
        rw [← hsk]; exact hS
end
end TermStep.Flat

-- PORTB TermStep.lean:13978 tstepM_inrT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_inrTB {x : String} {τ : Ty} {a : At} {e : Expr}
    (hterm : th.term = .let_ x (.inr τ a) e) (hP : ProgT p) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  (tstepM_inrTSB (hDy := hDy) (hRP := hRP) (hPS := hPS) (hterm := hterm) (hP := hP) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hbf := hbf) (hpx := hpx)).imp id
    fun h r hr hp => (h r hr hp).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:13996 case_armNBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem case_armNBSB {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 q1 : List Word}
    (hb : c₁.bind xv u = .ok c') (he : Typed p c' e') (htv : TvOK c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env) (hE : EnvOKB p η) (hm1 : MemInvB g (CE η) s1)
    (hty : isBoxed ty = false) (hq : ofArm ty j p1 = some q1) (hlay : Lay th.σs u ty q1)
    (hvr : (VRF False) ρ η u (shp ty) q1) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e') :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1,
      ThInvMFSB p g (CE η) s1 r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) := by
  rw [injM_nbB hty, hq]
  refine ⟨by simp [ol], fun r2 hr2 => ?_⟩
  simp [ol] at hr2; subst hr2
  exact ⟨CE η, fun _ => rfl, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv, by simpa [withS] using bind_FInvB hb hi1 hvr hlay, retPw_eq hRP1 (bind_ret hb), hDy⟩, hm1⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:14023 case_armBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem case_armBSB {p : Prog} {g : G} {th : TTh} {ρ : Nat → Nat} {η : TEnv} {s1 : St} {xv : String}
    {e' : Expr} {u ty : Ty} {c₁ c' : Cx} {j : Nat} {p1 : List Word} {us : List Acc} {w : Word}
    {x0 : Address} {B0 : Box} {s0 : Nat}
    (hb : c₁.bind xv u = .ok c') (he : Typed p c' e') (htv : TvOK c')
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env) (hE : EnvOKB p η) (hm1 : MemInvB g (CE η) s1)
    (hn : 0 < g.n) (hbf : g.boxFence = true) (hty : isBoxed ty = true) (hus : (armsOf ty)[j]?.bind accs = some us)
    (hlen : p1.length = nWords us) (hw : w.val = .loc x0 0) (hB0 : η.box x0.label = some B0)
    (hsto0 : η.sto x0.label = none) (hini0 : η.ini x0.label = 0) (ht : B0.tag = j + s0)
    (hWp : WLe B0.pay p1) (hv : (VRF False) ρ η u (vsh s0 (shp ty)) [w]) (hlay : ∀ pw, Lay th.σs u ty [pw]) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs e') :
    injM g s1 ty j p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ty j p1,
      ThInvMFSB p g (CE η) s1 r2.1.mem r2.1.pairs (withS { th with term := e', env := (xv, ty, r2.2) :: th.env } r2.1) := by
  rw [injM_box hty hus]
  refine ⟨?_, fun r2 hr2 => ?_⟩
  · obtain ⟨r, hr⟩ := alloc_nonempty (k := g.k) (arch := g.arch)
      (lbl := freshLabel g.lbase g.n g.i s1.nalloc) (us := .one :: us)
      (ws := cst (.num j) :: p1) (s := s1) (by simp [nWords, Acc.size] at hlen ⊢; omega)
    exact List.ne_nil_of_mem (List.mem_map_of_mem hr)
  · rw [List.mem_map] at hr2
    obtain ⟨⟨s', pw⟩, hal, rfl⟩ := hr2
    obtain ⟨hm', hpw⟩ := MemInv_boxFB (us := us) hm1 hn hbf hal hlen
    simp only at hpw
    subst hpw
    let lbl := freshLabel g.lbase g.n g.i s1.nalloc
    let V := s1.vs.vRelSt
    let B : Box := ⟨j, p1.map (bumpW V), (CE η).tid, s'.vs.vWr⟩
    have hbnone : η.box lbl = none := hm1.2.2.2.2.2.2.2.2.2.1.1 s1.nalloc (Nat.le_refl _)
    have hstoL : η.sto lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).1
    have hpfL : η.pfr lbl = none := (hm1.2.2.2.1.1 s1.nalloc (Nat.le_refl _)).2.2.2.2
    have hne0 : x0.label ≠ lbl := fun e => by rw [e, hbnone] at hB0; cases hB0
    let η' := η.withStoB η.sto (P := fun l => if l = lbl then some s'.vs.vWr else η.pfr l)
      (S := fun l => l = lbl ∨ η.seen l) (Bx := fun l => if l = lbl then some B else η.box l)
    have hx : ExtB η η' := Ext_withStoB hE.2.1 (fun _ _ h => h) (fun _ => Nat.le_refl _) (hS := fun _ h => Or.inr h)
      (hP := fun l f h => by
        have hne : l ≠ lbl := fun e => by rw [e, hpfL] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
      (hB := fun l B' h => by
        have hne : l ≠ lbl := fun e => by rw [e, hbnone] at h; cases h
        simp only [hne, ↓reduceIte]; exact h)
    have hCE : CE η' = seeBoxE (CE η) lbl B s'.vs.vWr := rfl
    have hBS : BoxSeen η' lbl B := ⟨by simp [η', TEnv.withStoB], s'.vs.vWr, by simp [η', TEnv.withStoB], Nat.le_refl _⟩
    have hv0 : (VRF False) ρ η' u (vsh s0 (shp ty)) [w] := VR_extB hE.2.1 hx hv
    have hv1 : (VRF False) ρ η' u (vsh 0 (shp ty)) [cst (.loc ⟨lbl, 0⟩ 0)] :=
      VR_renB (B1 := B0) (B2 := B) hx.1 hw rfl rfl
        (by simp [η', TEnv.withStoB, hne0, hB0]) (by simp [η', TEnv.withStoB])
        (by simpa [η', TEnv.withStoB] using hsto0)
        (by simp [η', TEnv.withStoB, hini0]) (by show B0.tag + 0 = j + s0; omega)
        (WLe_trans hWp (WLe_bump V p1)) (Or.inl hBS) (bh_shp ty hty) hv0
        (by simp [η', TEnv.withStoB, hini0])
    rw [vsh_zero ty hty] at hv1
    refine ⟨CE η', fun _ => rfl, by rw [hCE]; exact EFoot_seeBoxB (nalloc_alloc_box hm1.2.2.1 hal) rfl hpfL hstoL (alloc_size_fr hal) (by first | exact Nat.le_refl _ | (simp only [hbf, ↓reduceIte]; exact Nat.le_refl _) | (simp only [hbf, ↓reduceIte, stOf, withS]; exact Nat.le_refl _)) (alloc_size_len _ hal (by first | exact hlen | exact hnw.symm)),
      ⟨ρ, η', c', rfl, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, he, htv, ?_, retPw_eq hRP1 (bind_ret hb), hDy⟩, ?_⟩
    · simpa [withS] using bind_FInvB hb (FInv_extB hE.2.1 hx hi1) hv1 (hlay _)
    · rw [hCE]; exact hm'
end
end TermStep.Flat

-- PORTB TermStep.lean:14095 tstepM_caseBS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_caseBSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr} {u v : Ty} {c₁ c₂ c₃ : Cx}
    {ra rb : Ty} {ws : List Word} (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hb1 : c₁.bind x u = .ok c₂) (he1 : Typed p c₂ e₁) (htv1 : TvOK c₂)
    (hb2 : c₁.bind y v = .ok c₃) (he2 : Typed p c₃ e₂) (htv2 : TvOK c₃)
    (hi1 : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env)
    (hea : evalAt th.env a = some (.sum ra rb, ws)) (hv : (VRF False) ρ η (.sum u v) (shp (.sum ra rb)) ws)
    (hl : Lay th.σs (.sum u v) (.sum ra rb) ws) (hS : (Ty.sum ra rb).tier = .boxed)
    (hsg : sig (.sum ra rb) = sig (cl ρ η.wit 0 0 (.sum u v)))
    (hE : EnvOKB p η) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP1 : RetPw th.σs th.stack c₁.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hbi := hm.2.2.2.2.2.2.2.2.2.1
  have hrb : isBoxed (.sum ra rb) = true := by simp [isBoxed, sumHead, hS]
  obtain ⟨w, x0, B0, arm, us, rfl, hw, hx0, hB0, harm, hus, hnw, hsto0, hini0, hsee0⟩ :=
    boxed_operandB hE.2.1 hbi hrb hsg hv
  
  have hv' := hv
  simp only [VRF, VRb2, shp] at hv'
  obtain ⟨n0, Ra, Rb, hR, hv'⟩ := hv'
  simp only [lnorm, Shp.sum.injEq, Ty.sum.injEq] at hR
  obtain ⟨rfl, rfl, rfl⟩ := hR
  have htl : (Ty.sum (lnorm ra) (lnorm rb)).tier = .boxed := by
    rw [← hS]; exact tier_lnorm (.sum ra rb)
  have hv3 := hv'.resolve_right (fun ⟨j, p, hd, _, _⟩ => by rw [htl] at hd; simp [decodeArm] at hd)
  obtain ⟨-, x1, s0, B, hx1, -, hB, hn1, -, -, hA, hB'⟩ := hv3
  rw [wc_boxed hS] at hn1
  have hs0 : s0 = 0 := by simp at hn1; omega
  subst hs0
  simp only [List.map_cons, List.map_nil, hw, List.cons.injEq, and_true] at hx1
  cases hx1
  rw [hB0, Option.some.injEq] at hB
  subst hB
  have la : (armsOf (lnorm ra)).length = (armsOf ra).length := by rw [armsOf_lnorm, List.length_map]
  simp only [Nat.sub_zero, Nat.zero_add, la, isBoxed_lnorm, shp_lnorm] at hA hB'
  
  have hsg2 : Ty.sum (sig ra) (sig rb) = Ty.sum (sig (cl ρ η.wit 0 0 u)) (sig (cl ρ η.wit 0 0 v)) := hsg
  simp only [Ty.sum.injEq] at hsg2
  have hs := hl.2.1
  simp only [close, substTs, skel, etok, Ty.sum.injEq] at hs
  obtain ⟨hsa, hsb⟩ := hs
  obtain ⟨-, -, -, -, hly⟩ := hl
  simp only [close, substTs, lyt, etok, Ty.sum.injEq] at hly
  have layB : ∀ (ty : Ty) (t : Ty), isBoxed ty = true → etok (skel ty) = etok (skel (close th.σs t)) →
      etok (lyt 0 ty) = etok (lyt 0 (close th.σs t)) → ∀ pw, Lay th.σs t ty [pw] := by
    intro ty t hty hk hy pw
    refine ⟨fun us hu => ?_, hk, by rw [wc_isBoxed ty hty]; simp, Valid_boxed ty _ hty, hy⟩
    have h1 := wc_isBoxed ty hty
    simp only [wc, hu, Option.map_some, Option.some.injEq] at h1
    simp [h1]
  let s := stOf mem pairs th
  obtain ⟨hne, hpr⟩ := projM_own (g := g) (s := s) (t := .sum ra rb) hbi hsee0 hrb hw hx0 hB0 harm hus hnw.symm
  have hlen : ∀ p1 : List Word, WLe B0.pay p1 → p1.length = nWords us := fun p1 h => h.length.symm.trans hnw.symm
  by_cases hj : B0.tag < (armsOf ra).length
  · have hArm : ∀ s1 p1, MemInvB g (CE η) s1 → WLe B0.pay p1 →
        injM g s1 ra B0.tag p1 ≠ [] ∧ ∀ r2 ∈ injM g s1 ra B0.tag p1,
          ThInvMFSB p g (CE η) s1 r2.1.mem r2.1.pairs (withS { th with term := e₁, env := (x, ra, r2.2) :: th.env } r2.1) := by
      intro s1 p1 hm1 hWp
      cases hty : isBoxed ra with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hA hj).2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ := case_arm_nbB hE.2.1 hty hsg2.1 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBSB (hDy := hDy.leftW (fun _ => by rw [hterm]; rfl) rfl) (hRP1 := hRP1) hb1 he1 htv1 hi1 hE hm1 hty hq1 ⟨hs1, hsa, hw1, hv1, hly.1⟩ hvr1
      | true =>
          have harmA : (armsOf ra)[B0.tag]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_left hj]
          exact case_armBSB (hDy := hDy.leftW (fun _ => by rw [hterm]; rfl) rfl) (hbf := hbf) (hRP1 := hRP1) (s0 := 0) hb1 he1 htv1 hi1 hE hm1 hn hty (by rw [harmA]; exact hus) (hlen p1 hWp)
            hw hB0 hsto0 hini0 (by omega) hWp ((hA hj).1 hty) (layB ra u hty hsa hly.1)
    simp only [PAx, tstep, hterm, hea] at hpx ⊢
    refine ⟨?_, fun r hr hpr0 => ?_⟩
    · rcases hpx with h0 | ⟨r, hr, -⟩
      rotate_left
      · exact List.ne_nil_of_mem hr
      obtain ⟨r1, h1, hp1⟩ := hne h0
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      intro hnil
      rw [List.flatMap_eq_nil_iff] at hnil
      have h2 := hnil _ h1
      simp only [hj, ite_true, List.map_eq_nil_iff] at h2
      exact (hArm s1 p1 hm1 hWp).1 h2
    · rw [List.mem_flatMap] at hr
      obtain ⟨r1, h1, hr⟩ := hr
      have hp1 : PromAbove r1.1 := by
        obtain ⟨f1, f2⟩ := (hpr r1 h1).1
        have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
        have hpa' := hpr0
        try simp only at hr
        split at hr
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      simp only [hj, ite_true, List.mem_map] at hr
      obtain ⟨r2, hr2, rfl⟩ := hr
      exact ThInvMFS_congrB ((hArm s1 p1 hm1 hWp).2 r2 hr2) e5 e7 (congrArg Array.size e1) e4 e1
  · have hj' : (armsOf ra).length ≤ B0.tag := by omega
    have hArm : ∀ s1 p1, MemInvB g (CE η) s1 → WLe B0.pay p1 →
        injM g s1 rb (B0.tag - (armsOf ra).length) p1 ≠ [] ∧
          ∀ r2 ∈ injM g s1 rb (B0.tag - (armsOf ra).length) p1,
          ThInvMFSB p g (CE η) s1 r2.1.mem r2.1.pairs (withS { th with term := e₂, env := (y, rb, r2.2) :: th.env } r2.1) := by
      intro s1 p1 hm1 hWp
      cases hty : isBoxed rb with
      | false =>
          obtain ⟨q, hq, hsq, hwq, hvd, hvr⟩ := (hB' hj').2 hty
          obtain ⟨q1, hq1, hs1, hw1, hv1, hvr1⟩ := case_arm_nbB hE.2.1 hty hsg2.2 hq hsq hwq hvd (by rw [shp_lnorm]; exact hvr) hWp
          exact case_armNBSB (hDy := hDy.rightW (fun _ => by rw [hterm]; rfl) rfl) (hRP1 := hRP1) hb2 he2 htv2 hi1 hE hm1 hty hq1 ⟨hs1, hsb, hw1, hv1, hly.2⟩ hvr1
      | true =>
          have harmB : (armsOf rb)[B0.tag - (armsOf ra).length]? = some arm := by
            rw [← harm]; simp only [armsOf]; rw [List.getElem?_append_right hj']
          exact case_armBSB (hDy := hDy.rightW (fun _ => by rw [hterm]; rfl) rfl) (hbf := hbf) (hRP1 := hRP1) (s0 := (armsOf ra).length) hb2 he2 htv2 hi1 hE hm1 hn hty
            (by rw [harmB]; exact hus) (hlen p1 hWp)
            hw hB0 hsto0 hini0 (by omega) hWp ((hB' hj').1 hty) (layB rb v hty hsb hly.2)
    simp only [PAx, tstep, hterm, hea] at hpx ⊢
    refine ⟨?_, fun r hr hpr0 => ?_⟩
    · rcases hpx with h0 | ⟨r, hr, -⟩
      rotate_left
      · exact List.ne_nil_of_mem hr
      obtain ⟨r1, h1, hp1⟩ := hne h0
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      intro hnil
      rw [List.flatMap_eq_nil_iff] at hnil
      have h2 := hnil _ h1
      simp only [hj, ite_false, List.map_eq_nil_iff] at h2
      exact (hArm s1 p1 hm1 hWp).1 h2
    · rw [List.mem_flatMap] at hr
      obtain ⟨r1, h1, hr⟩ := hr
      have hp1 : PromAbove r1.1 := by
        obtain ⟨f1, f2⟩ := (hpr r1 h1).1
        have hpl1 : PromLt r1.1 := fun t ht => by rw [f1]; exact hm.2.2.1 t (by rw [← f2]; exact ht)
        have hpa' := hpr0
        try simp only at hr
        split at hr
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
        · obtain ⟨r2, hr2, rfl⟩ := List.mem_map.1 hr; exact injM_pa hpl1 hr2 hpa'
      obtain ⟨htag, hWp, e1, e2, e3, e4, e5, e6, e7⟩ := (hpr r1 h1).2 hp1
      have hm1 := MemInv_loadB hm e1 e2 (LoadCoh_rdB hm.2.1 hsto0 hB0 e3) e4 e5 e6 e7
      obtain ⟨s1, j1, p1⟩ := r1
      simp only at htag hWp hm1
      subst htag
      simp only [hj, ite_false, List.mem_map] at hr
      obtain ⟨r2, hr2, rfl⟩ := hr
      exact ThInvMFS_congrB ((hArm s1 p1 hm1 hWp).2 r2 hr2) e5 e7 (congrArg Array.size e1) e4 e1
end
end TermStep.Flat

-- PORTB TermStep.lean:14266 tstepM_caseTS
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_caseTSB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFSB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | case hu hb1 he1 hb2 he2 =>
    obtain ⟨u, v, c₁, c₂, c₃, hu, hb1, he1, hb2, he2⟩ : ∃ u v c₁ c₂ c₃,
        cx.use a = .ok (.sum u v, c₁) ∧ c₁.bind x u = .ok c₂ ∧ Typed p c₂ e₁ ∧
        c₁.bind y v = .ok c₃ ∧ Typed p c₃ e₂ := ⟨_, _, _, _, _, hu, hb1, he1, hb2, he2⟩
    obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
    have hs := hl.2.1
    simp only [close, substTs, skel, etok] at hs
    obtain ⟨ra, rb, rfl, -, -⟩ := eskel_eq_sum hs
    by_cases hS : (Ty.sum ra rb).tier = .boxed
    · have htv12 := case_TvOK hu hb1 hb2 htv
      have ho : cx.opaqueOK _ = true :=
        peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
      have htb := (use_TvOK hu htv).2.1
      have hsg := lay_closed (ρ := ρ) hi.2.2.2.1 hi.2.2.2.2.1 ho htb hl
      exact tstepM_caseBSB (hDy := hDy) (hbf := hbf) (hRP1 := retPw_eq hRP (use_ret hu)) hterm hn hb1 he1 htv12.1 hb2 he2 htv12.2 hi1 hea hv hl hS hsg hE hm hpx
    · refine paW <| tstepM_caseSB (hDy := hDy) hterm (fun t' c₁' hu' => ?_) hT hi hE htv hm hRP hPS
      rw [hu, Except.ok.injEq, Prod.mk.injEq] at hu'; obtain ⟨rfl, rfl⟩ := hu'
      rw [← tier_of_eskel hl.2.1]; exact hS
end
end TermStep.Flat

-- PORTB TermStep.lean:14296 tstepM_caseT
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_caseTB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx}
    {ρ : Nat → Nat} {η : TEnv} {a : At} {x y : String} {e₁ e₂ : Expr}
    (hterm : th.term = .case a x e₁ y e₂) (hn : 0 < g.n)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  (tstepM_caseTSB (hDy := hDy) (hRP := hRP) (hPS := hPS) (hterm := hterm) (hn := hn) (hT := hT) (hi := hi) (hE := hE) (htv := htv) (hm := hm) (hbf := hbf) (hpx := hpx)).imp id
    fun h r hr hp => (h r hr hp).toF
end
end TermStep.Flat

-- PORTB TermStep.lean:17627 tstepM_loadWordOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadWordOwnB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P)))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hro), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  exact ⟨CE η, EFoot_reflB, ⟨vcons n ρ, η, c', rfl, hE, he, htv', bind_FInvB hb (push_FInvB x n hi) hvr' (Lay_int w rfl), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:17671 tstepM_loadWordPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadWordPubB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P)))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk
      (by simp [Cx.opaqueOK, Ty.guardT]) hi hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq us 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, addrOf, hpw, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg hvr
  exact ⟨CE η, EFoot_reflB, ⟨vcons n ρ, η, c', rfl, hE, he, htv', bind_FInvB hb (push_FInvB x n hi) hvr' (Lay_int w rfl), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:17722 StoreBind
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
def StoreBindB (ρ : Nat → Nat) (η : TEnv) (σs : List Ty) (xt : Ty) : Prop :=
  (VRF False) ρ η xt (shp .unit) [] ∧ Lay σs xt .unit []
end
end TermStep.Flat

-- PORTB TermStep.lean:17729 storeWordOwn_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem storeWordOwn_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr .own (.word r P))) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hj : IntIdx c₁ v j) (hst : InState c₁ P j c₂ k')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hj
  obtain ⟨rt, w, hev, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us0, -, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  have hpwf : pwf P = true := by
    obtain ⟨_, hvr0, -⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
  have hlen : [w].length = nWords [Acc.one] := rfl
  have husA : accs c.ty = some [Acc.one] := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords [Acc.one]) := by
    rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.one] [w] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩,
    MemInv_storeB hm hsto hown husA hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:18865 storeWordPub_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem storeWordPub_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.ptr .pub (.word r P))) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hj : IntIdx c₁ v j) (hst : InState c₁ P j c₂ k')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hj
  obtain ⟨rt, w, hev, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  have ho : cx.opaqueOK (.word r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hpwf : pwf P = true := by
    obtain ⟨ru0, pw0, lab0, us0, -, -, -, -, hne, hld, hstw⟩ :=
      loadPub_coreB (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi hpk htv ho
  obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word r'' P) = some [.one] := by simp [accs, hg]
  have hlr : accs (Ty.word r'' P) = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  have husc : accs c.ty = some [.one] := by rw [← hlr, hus]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord_valB (r := r) hpwf hi1.1 hst hwv)
  have hlen : [w].length = nWords [Acc.one] := rfl
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, addrOf, hpw, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.one] [w] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  refine ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩, ?_⟩
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeFB hm hsto hown husc hval hlen s' hs'
  · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
    exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
      (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs'
end
end TermStep.Flat

-- PORTB TermStep.lean:18915 tstepM_storeWord
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact storeWordOwn_coreB (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
    · exact storeWordPub_coreB (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact storeWordOwn_coreB (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
    · exact storeWordPub_coreB (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact storeWordOwn_coreB (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩ hi hE htv hm hRP
    · exact storeWordPub_coreB (hDy := hDy) hterm hpk hg hu hj hst hb he htv' ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:19064 FInv_fenceCx
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem FInv_fenceCxB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {cx : Cx}
    {env : Env} (f : Fence) (h : FInvB glb gnum gi ρ η σs K cx env) : FInvB glb gnum gi ρ η σs K (fenceCx cx f) env := by
  cases f <;> exact h
end
end TermStep.Flat

-- PORTB TermStep.lean:19072 tstepM_fence
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_fenceB {x : String} {f : Fence} {e : Expr}
    (hterm : th.term = .let_ x (.fence f) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fence hb =>
  have key : tstep g mem pairs th =
      [((fenceS (stOf mem pairs th) (toWFence f)).mem, (fenceS (stOf mem pairs th) (toWFence f)).pairs,
        withS { th with term := e, env := (x, .unit, []) :: th.env } (fenceS (stOf mem pairs th) (toWFence f)))] := by
    simp only [tstep, hterm, evalOp]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ η .unit (shp .unit) [] := by simp [VRF, VRb2]
  have hlay : Lay th.σs .unit .unit [] := by
    refine ⟨fun us h => ?_, rfl, by simp [wc, accs], by simp [Valid], rfl⟩
    simp [accs] at h; subst h; rfl
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb (FInv_fenceCxB f hi) hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_fenceGB _ hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19101 tstepM_null
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_nullB {x : String} {μ : Mode} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.null μ τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | null hwf hb =>
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .ptrOpt μ (close th.σs τ), [cst .null]) :: th.env }
          (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ η (.ptrOpt μ τ) (shp (.ptrOpt μ (close th.σs τ))) [cst .null] := by simp only [VRF, VRb2]; exact Or.inl rfl
  have hlay : Lay th.σs (.ptrOpt μ τ) (.ptrOpt μ (close th.σs τ)) [cst .null] := by
    refine ⟨fun us h => ?_, ?_, by simp [wc, accs], by simp only [Valid]; exact Or.inl rfl, ?_⟩
    · simp [accs] at h; subst h; rfl
    · simp [close, substTs, skel]
    · simp [close, substTs, lyt]
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19141 tstepM_mkWord
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_mkWordB {x rn : String} {P : Proto} {v tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkWord rn P v tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hng : P.ghost = false) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWordGhost _ _ _ _ _ _ _ hg => rw [hng] at hg; cases hg
  | mkWord _ hpwf hu _ hv hst _ _ _ hb =>
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hv
  obtain ⟨rt, w, hea, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .word (.lit 0) P, [w]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hng, hea]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r', (VRF False) ρ η (.word r' P) (shp (.word (.lit 0) P)) [w] := by
    intro r'
    simp only [VRF, VRb2]
    refine ⟨hpwf, fun _ => ?_⟩
    obtain ⟨cl', hcl', hent⟩ := hst
    exact ⟨_, by simp [hwv], _, cl', _, hcl', hent ρ hi1.1⟩
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 (hvr _) (Lay_word _ _ _ hng w), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19179 tstepM_zero
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_zeroB {x : String} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.zero τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | zero hwf hsc hz hb =>
  have ho := bind_opaqueOK hb
  have haf := bind_arrFree hb
  have hr : ∀ k, τ.guardT k = false → k < th.σs.length := lt_of_guardT (tb_of_wf τ hwf) hi.2.2.2.2.1
  have hsig : sig (close th.σs τ) = sig (cl ρ η.wit 0 0 τ) := sig_WitL hi.2.2.2.1 ρ ho hr
  have hafT : (cl ρ η.wit 0 0 τ).arrFree = true := arrFree_cl hi.2.2.2.2.2.2.1.af τ 0 0 haf
  have hafR : (close th.σs τ).arrFree = true := by rw [← arrFree_sig, hsig, arrFree_sig]; exact hafT
  have hR := KindSound.zero_close cx.ke th.σs τ hi.2.2.2.2.2.1.2.1 hz
  obtain ⟨zs, hzs, -⟩ := zpB _ _ (Nat.lt_succ_self _) [] [] hafR knone_nil hR
  obtain ⟨hval, hwc⟩ := zero_valOfB hi.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.2.2.2.2.2.1 ρ ho hr haf hR hzs
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, close th.σs τ, zs.map cst) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hzs]; rfl
  rw [key]
  refine ⟨by simp, fun r hr' => ?_⟩
  simp only [List.mem_singleton] at hr'
  subst hr'
  obtain ⟨hvr0, hV0⟩ := ValOfB.env hval
  have hwcr : wc (close th.σs τ) = some zs.length := by rw [wc_of_sig hsig]; exact hwc
  have hvr : (VRF False) ρ η τ (shp (close th.σs τ)) (zs.map cst) := by
    rw [shp_of_sig hsig]
    exact (VR_closeB hE.2.1 ρ τ [] 0 ρ (fun _ => 0) (shp (cl ρ η.wit 0 0 τ)) _ (fun k => rfl)
      (fun k hk => absurd hk (Nat.not_lt_zero _))).2 hvr0
  have hlay : Lay th.σs τ (close th.σs τ) (zs.map cst) := by
    refine ⟨fun us h => ?_, rfl, by simp [hwcr], Valid_of_sig hsig.symm hV0, rfl⟩
    simp [wc, h] at hwcr; simp; omega
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi hvr hlay, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19245 tstepM_fold
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_foldB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.fold a τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fold hwf hu hfo hb =>
  rename_i c₁ t
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, close th.σs τ, wsv) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hev]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hW : ∀ k, Clo (η.wit k) := fun k => (hE.2.1 k).1
  have hsat : Sat c₁.facts ρ := hi1.1
  suffices h : (VRF False) ρ η τ (shp (close th.σs τ)) wsv ∧ Lay th.σs τ (close th.σs τ) wsv from
    ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 h.1 h.2, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
  cases hfo with
  | @ptr μ ν u s hme hte =>
      have hg := wf_mu_guard (Or.inl hwf)
      have hcl := cl_tyEq0 hte η.wit 0 (fun _ => hsat)
      simp only [VRF, VRb2] at hvv
      obtain ⟨ad, c, h1, h2, h3, h4, h5, h6⟩ := hvv
      refine ⟨⟨ad, c, h1, h2, h3, Fd_foldS hW hg h4 hcl, by cases hme <;> exact h5, h6⟩,
        fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
      · simp [close, substTs, accs] at h; subst h; exact single_len h1
      · simp only [close, substTs, Valid]; exact ⟨_, h1⟩
  | @ptrOpt μ ν u s hme hte =>
      have hg := wf_mu_guard (Or.inr (Or.inl hwf))
      have hcl := cl_tyEq0 hte η.wit 0 (fun _ => hsat)
      simp only [VRF, VRb2] at hvv
      rcases hvv with hn | ⟨ad, c, h1, h2, h3, h4, h5, h6⟩
      · refine ⟨Or.inl hn, fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len hn
        · simp only [close, substTs, Valid]; exact Or.inl hn
      · refine ⟨Or.inr ⟨ad, c, h1, h2, h3, Fd_foldS hW hg h4 hcl, by cases hme <;> exact h5, h6⟩,
          fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len h1
        · simp only [close, substTs, Valid]; exact Or.inr ⟨_, h1⟩
  | @loc μ ν u s hme hte =>
      have hg := wf_mu_guard (Or.inr (Or.inr hwf))
      have hcl := cl_tyEq0 hte η.wit 0 (fun _ => hsat)
      simp only [VRF, VRb2] at hvv
      rcases hvv with ⟨hn, e0, he0⟩ | ⟨ad, c, U, h1, h3, h4, hF, h5, h6⟩
      · refine ⟨Or.inl ⟨hn, e0, Fd_foldS hW hg he0 hcl⟩, fun us h => ?_, rfl,
          by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len hn
        · simp only [close, substTs, Valid]; exact Or.inl hn
      · refine ⟨Or.inr ⟨ad, c, U, h1, h3, h4, Fd_foldS hW hg hF hcl, by cases hme <;> exact h5,
            by rw [← modeIni_meq hme]; exact h6⟩, fun us h => ?_, rfl, by simp [close, substTs, wc, accs], ?_, rfl⟩
        · simp [close, substTs, accs] at h; subst h; exact single_len h1
        · simp only [close, substTs, Valid]; exact Or.inr ⟨_, h1⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19406 tstepM_ldlw
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_ldlwB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl : At} {e : Expr}
    (hterm : th.term = .let_ x (.ldlw b wi jl) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldlw hp hbuf hlo hint hlt hltk hpj hij hb =>
  obtain ⟨t, u, n, k, jw, tj, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩ : ∃ t u n k jw tj q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi.2.1 hpj hoj
  have hJ := hlt ρ hi.1
  have hJk := hltk ρ hi.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).filterMap fun (s1, old) =>
        (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (m % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hni, hnj, addrOf, hwv, hbe, lanesOf]
  
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filterMap.2 ⟨r0, hr0,
      (?_ : _ = some (r0.1, Ty.fix sg w, [cst (.num (laneN w y0 (m % w.lanes)))]))⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 ⊢; rw [hy0]; rfl
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv',
    bind_FInvB hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19493 tstepM_ldl
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_ldlB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i : At} {e : Expr}
    (hterm : th.term = .let_ x (.ldl b i) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldl hp hbuf hlo hint hlt hltk hb =>
  obtain ⟨t, u, n, k, j, q, hp, hbuf, hlo, hint, hlt, hltk, hb⟩ : ∃ t u n k j q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧ cx.bind x (.fix q.1 q.2) = .ok c' :=
    ⟨_, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  simp only at hu hb hlt hltk
  subst hu
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).filterMap
        fun (s1, old) => (numOf old).map fun y => (s1, Ty.fix sg w, [cst (.num (laneN w y (ev ρ j % w.lanes)))])).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hni, addrOf, hwv, hbe, lanesOf]
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_filterMap.2 ⟨r0, hr0,
      (?_ : _ = some (r0.1, Ty.fix sg w, [cst (.num (laneN w y0 (ev ρ j % w.lanes)))]))⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 ⊢; rw [hy0]; rfl
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_filterMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨-, -, f1, f2, f3, f4, f5⟩ := hld (s1, old) h1 hpr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv',
    bind_FInvB hb hi (fix_VRB (bkG := False) sg w _) (fix_Lay _ sg w _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h1) (loadUnits_vWr _ _ _ _ h1)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19585 tstepM_stlw
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_stlwB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b wi jl v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stlw b wi jl v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stlw hp hbuf hlo hint hlt hltk hpj hij hpv hfx hb =>
  obtain ⟨t, u, n, k, jw, tj, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩ :
      ∃ t u n k jw tj tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx wi jw ∧
      LtI cx jw n ∧ LtI cx jw k ∧ cx.peek jl = .ok tj ∧ (intOf tj).isSome = true ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpj, hij, hpv, hfx, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  obtain ⟨oj, hoj⟩ := Option.isSome_iff_exists.1 hij
  obtain ⟨rtj, wj, m, hej, hwj⟩ := atom_intB hi.2.1 hpj hoj
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ := hlt ρ hi.1
  have hJk := hltk ρ hi.1
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ jw) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ jw * nWords [Acc.one] = ev ρ jw := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ jw)) (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ jw) := by simp [numOf, hwi]
  have hnj : numOf [wj] = some m := by simp [numOf, hwj]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ jw)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ jw)) false [.one]
            [cst (.num (setLaneN w y (m % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hej, hev, hni, hnj, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw)
      (a := offs ad (ev ρ jw)) (rel := false) [.one] [cst (.num (setLaneN w y0 (m % w.lanes) yv))] 0 r0.1
      (by simp [nWords, Acc.size])
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, (?_ : (s2, Ty.unit, ([] : List Word)) ∈ _)⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 hs2 ⊢; rw [hy0]; exact List.mem_map_of_mem hs2
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ jw)) (hm1 (s1, old) h1 (storeUnits_promAbove hs2 hpr)) hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:19690 tstepM_stl
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_stlB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {b i v : At} {e : Expr}
    (hterm : th.term = .let_ x (.stl b i v) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hpx : PAx g mem pairs th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | stl hp hbuf hlo hint hlt hltk hpv hfx hb =>
  obtain ⟨t, u, n, k, j, tv, q, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩ : ∃ t u n k j tv q,
      cx.peek b = .ok t ∧ bufOf t = some (.own, n, u, k) ∧ lanesOf u = some q ∧ IntIdx cx i j ∧
      LtI cx j (.smul q.2.lanes n) ∧ LtI cx j (.smul q.2.lanes k) ∧
      cx.peek v = .ok tv ∧ fixOf tv = some q ∧ cx.bind x .unit = .ok c' :=
    ⟨_, _, _, _, _, _, _, hp, hbuf, hlo, hint, hlt, hltk, hpv, hfx, hb⟩
  obtain ⟨sg, w⟩ := q
  have hu := lanes_of hlo
  have htv0 := fix_of hfx
  simp only at hu htv0 hlt hltk
  subst hu htv0
  have ho : cx.opaqueOK (.lanes sg w) = true := by simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ti, hpi, hti⟩ := hint
  obtain ⟨rti, wwi, hei, hwi, -⟩ := atom_numB hi.2.1 hpi hti
  obtain ⟨rv, wsv, hev, hvv, -⟩ := peek_VRB (bkG := False) hi.2.1 hpv
  simp only [VRF, VRb2] at hvv
  obtain ⟨-, yv, hyv, -⟩ := hvv
  obtain ⟨wv, rfl, hwv'⟩ := map_singleton hyv
  have hJ0 : ev ρ j < w.lanes * ev ρ n := by simpa [ev] using hlt ρ hi.1
  have hJk0 : ev ρ j < w.lanes * ev ρ k := by simpa [ev] using hltk ρ hi.1
  have hJ : ev ρ j / w.lanes < ev ρ n :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJ0)
  have hJk : ev ρ j / w.lanes < ev ρ k :=
    (Nat.div_lt_iff_lt_mul (Wd.lanes_pos w)).2 (by rw [Nat.mul_comm]; exact hJk0)
  obtain ⟨rt, pw, ad, c, μr, ur, us, hea, hwv, hbe, hus, hsto, hat, hmode, hini, hsku, hsig⟩ :=
    slot_viewNB (bkG := False) (ev ρ j / w.lanes) hi.2.1 hi.2.2.2.1 hi.2.2.2.2.1 htv hp hbuf hJ hJk ho
  obtain ⟨rfl, rfl⟩ := lane_rt hsku hus
  have e1 : ev ρ j / w.lanes * nWords [Acc.one] = ev ρ j / w.lanes := by simp [nWords, Acc.size]
  rw [e1] at hat hini
  have hna : ∀ N e', cl ρ η.wit 0 0 (.lanes sg w) ≠ .array (.lit N) e' := fun N e' h => by simp [cl] at h
  obtain ⟨us', hus', ⟨r0, hr0⟩, hld, hstw⟩ := locLoadB (ad := offs ad (ev ρ j / w.lanes)) (arch := g.arch)
    (pw := pw) (acq := false) (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hmode hat hini hna hsku hsig
      (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2
        (accs_rtWB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 ho (by simp [tb]) (peek_buf_lytB hi.2.1 hp hbuf hea hbe).2)
  simp [accs] at hus'; subst hus'
  have hni : numOf [wwi] = some (ev ρ j) := by simp [numOf, hwi]
  have hnv : numOf [wv] = some yv := by simp [numOf, hwv']
  have hnum : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → ∃ y, numOf r1.2 = some y := fun r1 h hp => by
    obtain ⟨hvr, -⟩ := hld r1 h hp
    simp only [VRF, VRb2] at hvr
    obtain ⟨-, y, hy⟩ := hvr
    obtain ⟨w0, h0, hw0⟩ := map_singleton hy
    exact ⟨y, by rw [h0]; simp [numOf, hw0]⟩
  have hm1 : ∀ r1, r1 ∈ loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th) →
      PromAbove r1.1 → MemInvB g (CE η) r1.1 := fun r1 h hp => by
    obtain ⟨_, _, f1, f2, f3, f4, f5⟩ := hld r1 h hp
    exact MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ h) (loadUnits_vWr _ _ _ _ h)
  have hwUA : accs (cl ρ η.wit 0 0 (.lanes sg w)) = some [Acc.one] := by simp [cl, accs]
  have hwU : wc (cl ρ η.wit 0 0 (.lanes sg w)) = some (nWords [Acc.one]) := by simp [cl, wc, accs]
  have key : tstep g mem pairs th =
      ((loadUnits g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one] 0 (stOf mem pairs th)).flatMap fun (s1, old) =>
        match numOf old with
        | some y => (storeUnits g.k g.arch pw (offs ad (ev ρ j / w.lanes)) false [.one]
            [cst (.num (setLaneN w y (ev ρ j % w.lanes) yv))] 0 s1).map fun s2 => (s2, Ty.unit, ([] : List Word))
        | none => []).map
        fun (s', t, ws) => (s'.mem, s'.pairs, withS { th with term := e, env := (x, t, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hei, hev, hni, hnv, addrOf, hwv, hbe, lanesOf]
    rfl
  unfold PAx at hpx
  rw [key] at hpx ⊢
  refine ⟨?_, fun r hr hpr0 => ?_⟩
  · rcases hpx with h0 | ⟨r, hr, -⟩
    rotate_left
    · exact List.ne_nil_of_mem hr
    obtain ⟨y0, hy0⟩ := hnum r0 hr0 (PromAbove_nil (by rw [(loadUnits_frame _ _ _ r0 hr0).2.2.1]; exact h0))
    obtain ⟨s2, hs2⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw)
      (a := offs ad (ev ρ j / w.lanes)) (rel := false) [.one] [cst (.num (setLaneN w y0 (ev ρ j % w.lanes) yv))] 0 r0.1
      (by simp [nWords, Acc.size])
    refine List.ne_nil_of_mem (List.mem_map_of_mem (List.mem_flatMap.2 ⟨r0, hr0, (?_ : (s2, Ty.unit, ([] : List Word)) ∈ _)⟩))
    obtain ⟨s0, o0⟩ := r0; simp only at hy0 hs2 ⊢; rw [hy0]; exact List.mem_map_of_mem hs2
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨s', t', ws'⟩, hr, rfl⟩ := hr
  rw [List.mem_flatMap] at hr
  obtain ⟨⟨s1, old⟩, h1, h2⟩ := hr
  simp only at h2
  obtain ⟨y, hy⟩ : ∃ y, numOf old = some y := by
    cases hn : numOf old with
    | none => simp [hn] at h2
    | some y => exact ⟨y, rfl⟩
  rw [hy, List.mem_map] at h2
  obtain ⟨s2, hs2, he2⟩ := h2
  simp only [Prod.mk.injEq] at he2
  obtain ⟨rfl, rfl, rfl⟩ := he2
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_storeAtB (a := offs ad (ev ρ j / w.lanes)) (hm1 (s1, old) h1 (storeUnits_promAbove hs2 hpr)) hsto hmode hat hini hna
      (lanes_EnvValB sg w _) hwUA (by simp [nWords, Acc.size]) s2 hs2⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20269 LendCx_FInv
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem LendCx_FInvB {ρ : Nat → Nat} {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop}
    {cx c₂ : Cx} {env : Env} {acq rel : Bool} {r : Idx} {t : String} {P : Proto} {c c' : Nat} {k k' : Idx}
    (h : LendCx cx acq rel r t P c k c' k' c₂) (hi : FInvB glb gnum gi ρ η σs K cx env) :
    FInvB glb gnum gi ρ η σs K c₂ ((t, .unit, []) :: env) := by
  cases h with
  | none _ hb => exact bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _)
  | up _ _ hb => exact bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl)
  | down _ _ _ _ hu hb => exact bind_FInvB hb (use_FInvB (bkG := False) hu hi).1 (unit_VRB (bkG := False)) (unit_Lay _)
end
end TermStep.Flat

-- PORTB TermStep.lean:20290 casWord_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casWord_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r i j k' : Idx} {P : Proto} {c₂ : Nat}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hie : IntIdx cx e i) (hj : IntIdx cx v j) (hst : InState cx P j c₂ k')
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPw th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨te, hte, hio⟩ := hie
  obtain ⟨rte, ew, hee, -, -⟩ := atom_numB hi.2.1 hte hio
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
  obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := casWordCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ hg hst hnwv hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ⟨lab, 0⟩ (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, addrOf, hpw]; rfl
  rw [key] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb]
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb]
    obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20337 tstepM_casWord
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casWordB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r : Idx} {P : Proto}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp hnw => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | casShare hp hw _ hie hj _ _ hst _ _ _ _ hlend hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWord_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, LendCx_TvOK hlend htv, LendCx_FInvB hlend hi, retPw_eq hRP (LendCx_ret hlend)⟩
      hfail hi hE htv hm hRP
  | casTake hp hw _ hie hj _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hi' := bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl)
    have htv' := (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1
    split at hok
    · exact casWord_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPw_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
    · exact casWord_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPw_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
  | casEpoch hp hw _ _ hie hj _ hst _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWord_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
        bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPw_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:20492 casCell_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casCell_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c₂ : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u te tv : Ty}
    (hpk : cx.peek w = .ok (.ptr .pub u)) (hone : u.rawWords = some 1)
    (hpe : cx.peek e = .ok te) (hu : cx.use v = .ok (tv, c₁))
    (hsube : SubS c₁ te u) (hsubv : SubS c₁ tv u) (hb : c₁.bind t .unit = .ok c₂)
    (hok : Typed p c₂ ok) (hfail : Typed p c₁ fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    
    (hRP : RetPw th.σs th.stack cx.ret) (hkey : ∀ pw ew nw b, evalAt th.env w = some (.ptr .pub b, [pw]) → (∃ r, evalAt th.env e = some (r, [ew])) →
        (∃ r, evalAt th.env v = some (r, [nw])) → ∀ lab, pw.val = .loc ⟨lab, 0⟩ 0 →
      tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ⟨lab, 0⟩ (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩)) (hterm : th.term = .cas acq rel w e v t ok fail) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.ptr .pub u) = some (.pub, u))
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi hpk htv ho
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have htv1 := (use_TvOK hu htv).1
  have hlr : accs ru = accs (cl ρ η.wit 0 0 u) :=
    pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  have hus : accs ru = some [.one] := by rw [hlr]; exact accs_cl_one hone
  have husc : accs c.ty = some [.one] := by rw [(Fd_lay hcty).2.2.1]; exact accs_cl_one hone
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsubv ho htb hvv hlv hsig hus
  obtain ⟨nw, rfl⟩ := len_one hlen
  replace hval := (Fd_EnvValB (CE η) hcty).2 hval
  obtain ⟨rte, wse, hee, hve, hle⟩ := peek_VRB (bkG := False) hi.2.1 hpe
  obtain ⟨-, hlene⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsube ho htb hve hle hsig hus
  obtain ⟨ew, rfl⟩ := len_one hlene
  obtain ⟨ru', pw', lab', us', hea', hpw', hus', -, hne, hld, hstw⟩ :=
    loadPub_coreB (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
  have e1 := Option.some.inj (hea.symm.trans hea')
  simp only [Prod.mk.injEq, List.cons.injEq, and_true, Ty.ptr.injEq, true_and] at e1
  obtain ⟨rfl, rfl⟩ := e1
  obtain rfl : lab = lab' := by
    rw [hpw] at hpw'; simp only [Val.loc.injEq, WeakMem.Address.mk.injEq] at hpw'; exact hpw'.1.1
  obtain rfl : us' = [.one] := Option.some.inj (hus'.symm.trans hus)
  rw [hkey pw ew nw ru hea ⟨_, hee⟩ ⟨_, hev⟩ lab hpw] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨-, -, hm1⟩ := hld s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb']
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c₁, rfl, hE, hfail, htv1, hi1, retPw_eq hRP (use_ret hu), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb']
    have hm2 : MemInvB g (CE η) s2 := by
      have hlen1 : [nw].length = nWords [Acc.one] := rfl
      have hm1' := MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view)
      by_cases hown : c.owner = some η.tid
      · exact MemInv_storeFB hm1' hsto hown husc hval hlen1 s2 hs2
      · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
        exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm1' hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
          (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen1 s2 hs2
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c₂, rfl, hE, hok, (bind_TvOK hb htv1 (by simp [tb]) (by simp [mg])).1,
      bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB hm2 (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20564 tstepM_casCell
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casCellB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u : Ty}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.ptr .pub u)) (hnw : wordOf (Ty.ptr .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp _ hc hone _ hpe hu hsube hsubv _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨_, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
      subst hc
      exact casCell_coreB (hterm := hterm) (hDy := hDy) hpk hone hpe hu hsube hsubv hb hok hfail hi hE htv hm hRP
        (fun pw ew nw b hea he hv lab hpw => by
          obtain ⟨_, hee⟩ := he
          obtain ⟨_, hev⟩ := hv
          simp only [tstep, hterm, hea, hee, hev, addrOf, hpw]; rfl)
    · simp [cellOf] at hc
  | casShare hp hw | casTake hp hw | casEpoch hp hw =>
    exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
end
end TermStep.Flat

-- PORTB TermStep.lean:20742 casWordLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casWordLoc_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r i j k' : Idx} {P : Proto} {c₂ : Nat}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hie : IntIdx cx e i) (hj : IntIdx cx v j) (hst : InState cx P j c₂ k')
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPw th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨te, hte, hio⟩ := hie
  obtain ⟨rte, ew, hee, -, -⟩ := atom_numB hi.2.1 hte hio
  obtain ⟨tv, htvk, hjo⟩ := hj
  obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := wordLocCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ hg hst hnwv hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, hea, hee, hev, haddr]; rfl
  rw [key] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨hm1, hst2⟩ := hcell s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb]
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb]
    obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20786 tstepM_casWordLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casWordLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {μ : Mode} {r : Idx} {P : Proto}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp hnw => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | casShare hp hw _ hie hj _ _ hst _ _ _ _ hlend hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, LendCx_TvOK hlend htv, LendCx_FInvB hlend hi, retPw_eq hRP (LendCx_ret hlend)⟩
      hfail hi hE htv hm hRP
  | casTake hp hw _ hie hj _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    have hi' := bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl)
    have htv' := (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1
    split at hok
    · exact casWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPw_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
    · exact casWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst ⟨_, hok, htv', hi', retPw_eq hRP (by have h := bind_ret hb; exact h)⟩ hfail hi hE htv hm hRP
  | casEpoch hp hw _ _ hie hj _ hst _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact casWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hie hj hst
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
        bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPw_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:20820 casCellLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem casCellLoc_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c₂ : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u te tv : Ty}
    (hpk : cx.peek w = .ok (.loc .pub u)) (hone : u.rawWords = some 1)
    (hpe : cx.peek e = .ok te) (hu : cx.use v = .ok (tv, c₁))
    (hsube : SubS c₁ te u) (hsubv : SubS c₁ tv u) (hb : c₁.bind t .unit = .ok c₂)
    (hok : Typed p c₂ ok) (hfail : Typed p c₁ fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hRP : RetPw th.σs th.stack cx.ret) (hkey : ∀ pw ew nw ad rt, evalAt th.env w = some (rt, [pw]) → (∃ r, evalAt th.env e = some (r, [ew])) →
        (∃ r, evalAt th.env v = some (r, [nw])) → addrOf pw = some ad →
      tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad (.cas ew.val)
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS (if (th'.regs 1).val == ew.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩)) (hterm : th.term = .cas acq rel w e v t ok fail) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hotv : cx.opaqueOK tv = true :=
    peek_opaqueOK htv (use_invB (ρ := ρ) (η := η) (σs := th.σs) (env := th.env) hu).1
  have ho : cx.opaqueOK u = true := sub_opaqueOK hsubv hotv
  have htb : tb cx.ke.length u = true := tb_cellOf (peek_tb htv hpk) (rfl : cellOf (.loc .pub u) = some (.pub, u))
  obtain ⟨hi1, rv, wsv, hev, hvv, hlv⟩ := use_FInvB (bkG := False) hu hi
  have htv1 := (use_TvOK hu htv).1
  have hus1 : accs (cl ρ η.wit 0 0 u) = some [.one] := accs_cl_one hone
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, -, hsig, hne, hld, hsto, hstw⟩ :=
    locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk (.inr rfl) ho hus1 hi hE htv hm
  obtain ⟨hval, hlen⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsubv ho htb hvv hlv hsig hus
  obtain ⟨nw, rfl⟩ := len_one hlen
  obtain ⟨rte, wse, hee, hve, hle⟩ := peek_VRB (bkG := False) hi.2.1 hpe
  obtain ⟨-, hlene⟩ := ownStoreValB hE.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi1.1 hsube ho htb hve hle hsig hus
  obtain ⟨ew, rfl⟩ := len_one hlene
  rw [hkey pw ew nw ad _ hea ⟨_, hee⟩ ⟨_, hev⟩ haddr] at ⊢
  refine ⟨fun h => stepRmw_ne_nil (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, hpS, hcase⟩ := stepRmw_splitP (s := stOf mem pairs th) hin
  obtain ⟨-, -, hm1⟩ := hld s1 [rd] hl1 (hpS (fun t ht m hm => hpr t ht m hm))
  rcases hcase with ⟨hne', hsame⟩ | ⟨heq, s2, hs2, hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = false := by rw [hrd]; simpa using hne'
    simp only [hb']
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c₁, rfl, hE, hfail, htv1, hi1, retPw_eq hRP (use_ret hu), hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb' : ((th'.regs 1).val == ew.val) = true := by rw [hrd]; simpa using heq
    simp only [hb']
    have hm2 : MemInvB g (CE η) s2 :=
      hsto _ [nw] (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) (max (Promises.pairTop (stOf mem pairs th).pairs rd.rts) rd.view))
        hval rfl s2 hs2
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c₂, rfl, hE, hok, (bind_TvOK hb htv1 (by simp [tb]) (by simp [mg])).1,
      bind_FInvB hb hi1 (unit_VRB (bkG := False)) (unit_Lay _), retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch (MemInv_setRelB hm2 (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20874 tstepM_casCellLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_casCellLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {acq rel : Bool} {w e v : At} {t : String} {ok fail : Expr}
    {u : Ty}
    (hterm : th.term = .cas acq rel w e v t ok fail)
    (hpk : cx.peek w = .ok (.loc .pub u)) (hnw : wordOf (Ty.loc .pub u) = none)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | casCell hp _ hc hone _ hpe hu hsube hsubv _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨_, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
      subst hc
      exact casCellLoc_coreB (hterm := hterm) (hDy := hDy) hpk hone hpe hu hsube hsubv hb hok hfail hi hE htv hm hRP
        (fun pw ew nw ad rt hea he hv haddr => by
          obtain ⟨_, hee⟩ := he
          obtain ⟨_, hev⟩ := hv
          simp only [tstep, hterm, hea, hee, hev, haddr]; rfl)
    · simp [cellOf] at hc
  | casShare hp hw | casTake hp hw | casEpoch hp hw =>
    exfalso; rw [hpk] at hp; cases hp; rw [hnw] at hw; cases hw
end
end TermStep.Flat

-- PORTB TermStep.lean:20901 tstepM_loadWordLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_loadWordLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {acq : Bool} {a : At} {μ : Mode} {r : Idx} {P : Proto}
    {e : Expr} (hterm : th.term = .let_ x (.load acq a) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | loadOwn hp hnw _ _ _ | loadPub hp hnw _ _ _ _ | loadRgn hp hnw _ _ _ _ | loadCap hp hnw _ _ _ _ _
  | loadTorn hp hnw _ _ _ _ => exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | loadWord hp hw hg hb =>
  rw [hpk] at hp; cases hp
  simp only [wordOf, Option.some.injEq] at hw; subst hw
  have hg' : P.ghost = false := hg
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg']
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
  obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, cellOf, haddr, wordOf, Option.isSome_some,
      ↓reduceIte, hus, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w, n, rfl, hvr'⟩ := word_bindB (bkG := False) hg' hvr
  exact ⟨CE η, EFoot_reflB, ⟨vcons n ρ, η, c', rfl, hE, he, htv', bind_FInvB hb (push_FInvB x n hi) hvr' (Lay_int w rfl), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20941 storeWordLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem storeWordLoc_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx c₁ c' : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v tk : At}
    {μ : Mode} {r r' i j k' : Idx} {P : Proto} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.store rel a v (some tk)) e)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = false)
    (hu : cx.use tk = .ok (.tok r' (some (P, i)), c₁)) (hj : IntIdx c₁ v j) (hst : InState c₁ P j c₂ k')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv, htvk, hio⟩ := hj
  obtain ⟨rt, w, hev, hwv, -⟩ := atom_numB hi1.2.1 htvk hio
  have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
  obtain ⟨ad, pw, μr, ru, hea, haddr, hus, hsku, -, hne, hld, hsto, hstw⟩ :=
    locCellB (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
  have hpwf : pwf P = true := by
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  have hval := storeWord_valB (η := η) (r := r) hpwf hi1.1 hst hwv
  have hlen : [w].length = nWords [Acc.one] := rfl
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.one] [w] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev, cellOf, haddr, hus, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    [.one] [w] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩,
    hsto _ [w] hm hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:20979 tstepM_storeWordLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word r P))) (hμ : μ = .own ∨ μ = .pub)
    (hg : P.ghost = false)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | storeOwn hp hnw | storePub hp hnw | storeRgn hp hnw | storeCap hp hnw =>
    exfalso; rw [hpk] at hp; cases hp; simp [wordOf] at hnw
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact storeWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact storeWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hu hj hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [wordOf, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact storeWordLoc_coreB (hDy := hDy) hterm hpk hμ hg hu hj hst hb he htv' ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:21033 tstepM_mkWordGhost
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_mkWordGhostB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x rn : String} {P : Proto} {v tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkWord rn P v tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th))
    (hg : P.ghost = true) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord _ _ _ _ _ _ _ hng _ _ => rw [hg] at hng; cases hng
  | mkWordGhost _ hpwf hu _ _ _ _ _ _ hb =>
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .prod (.word (.lit 0) P) (.tok (.lit 0) none), []) :: th.env }
          (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hg]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r' j', (VRF False) ρ η (.prod (.word r' P) (.tok r' (some (P, j'))))
      (shp (.prod (.word (.lit 0) P) (.tok (.lit 0) none))) [] := by
    intro r' j'
    simp [VRF, VRb2, shp, hpwf, hg, wc, accs, Shp.wc, nWords]
  have hl2 := fun r' j' => Lay_pair (Lay_wordGhost th.σs r' P hg) (Lay_tokGhost th.σs r' P j')
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 (hvr _ _) (hl2 _ _), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21068 ghostRef
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem ghostRefB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {t : Ty} {μ : Mode} {r : Idx} {P : Proto}
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) :
    ∃ rt pw b μ' ru, evalAt th.env a = some (rt, [pw]) ∧ cellOf rt = some (μ', ru) ∧
      addrOf pw = some b ∧ accs ru = some [] := by
  rcases ht with rfl | rfl
  · rcases hμ with rfl | rfl
    · obtain ⟨lab, c, pw, ru, hea, hpw, -, -, -, -, hsku, -⟩ :=
        ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
      obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
      exact ⟨_, pw, ⟨lab, 0⟩, _, _, hea, rfl, by simp [addrOf, hpw], by simp [accs, hg]⟩
    · obtain ⟨lab, c, pw, ru, f, hea, hpw, -, -, -, -, -, hsku, -⟩ :=
        pubPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
      obtain ⟨r'', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
      exact ⟨_, pw, ⟨lab, 0⟩, _, _, hea, rfl, by simp [addrOf, hpw], by simp [accs, hg]⟩
  · obtain ⟨ad, pw, μr, ru, hea, haddr, hus, -⟩ := locCellB (acq := false) (rel := false) (us := [])
      hpk hμ (by simp [Cx.opaqueOK, Ty.guardT]) (by simp [cl, accs, hg]) hi hE htv hm
    exact ⟨_, pw, ad, _, _, hea, rfl, haddr, hus⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21093 tstepM_storeWordGhost
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordGhostB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub) (hg : P.ghost = true)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨rt, pw, b, μ', ru, hea, hc, hab, hus⟩ := ghostRefB hpk ht hμ hg hi hE htv hm
  have hnw : wordOf t ≠ none := by rcases ht with rfl | rfl <;> simp [wordOf]
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  have fin : ∀ {c₁ : Cx} {xt : Ty} {j : Idx}, FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c₁ th.env →
      IntIdx c₁ v j → c₁.bind x xt = .ok c' → StoreBindB ρ η th.σs xt →
      tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
    intro c₁ xt j hi1 hj hb htag
    obtain ⟨tv, htvk, hio⟩ := hj
    obtain ⟨rv, w, hev, -, -⟩ := atom_numB hi1.2.1 htvk hio
    have key : tstep g mem pairs th =
        [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
          withS { th with term := e, env := (x, .unit, []) :: th.env } (stOf mem pairs th))] := by
      simp only [tstep, hterm, evalOp, hea, hev, hc, hab, hus, storeUnits, List.map]
    rw [key]
    refine ⟨by simp, fun r hr => ?_⟩
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
  cases hop with
  | storeOwn hp hnw' | storePub hp hnw' | storeRgn hp hnw' | storeCap hp hnw' =>
    exfalso; rw [hpk] at hp; cases hp; exact hnw hnw'
  | storeWordGive hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    exact fin (use_FInvB (bkG := False) hu hi).1 hj hb ⟨unit_VRB (bkG := False), unit_Lay _⟩
  | storeWordHand hp hw hu _ hj _ _ hst _ _ _ _ _ _ hb =>
    exact fin (use_FInvB (bkG := False) hu hi).1 hj hb ⟨unit_VRB (bkG := False), unit_Lay _⟩
  | storeWordKeep hp hw hu _ hj _ _ hst _ _ _ _ _ hb =>
    exact fin (use_FInvB (bkG := False) hu hi).1 hj hb ⟨by simp [VRF, VRb2], tok_Lay _ _ _ _⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21193 tstepM_storeWordAny
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_storeWordAnyB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {rel : Bool} {a v : At} {tok : Option At}
    {t : Ty} {μ : Mode} {r : Idx} {P : Proto} {e : Expr}
    (hterm : th.term = .let_ x (.store rel a v tok) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok t) (ht : t = .ptr μ (.word r P) ∨ t = .loc μ (.word r P))
    (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  cases hg : P.ghost
  · rcases ht with rfl | rfl
    · exact tstepM_storeWordB (hDy := hDy) hterm hP hpk hμ hg hT hi hE htv hm hRP
    · exact tstepM_storeWordLocB (hDy := hDy) hterm hP hpk hμ hg hT hi hE htv hm hRP
  · exact tstepM_storeWordGhostB (hDy := hDy) hterm hP hpk ht hμ hg hT hi hE htv hm hRP hPS
end
end TermStep.Flat

-- PORTB TermStep.lean:21238 tstepM_mkWord2
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_mkWord2B {x rn : String} {P : Proto2} {v0 v1 tk : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkWord2 rn P v0 v1 tk) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkWord2 _ hpwf hu _ hv0 hv1 hst _ _ hb =>
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .word2 (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r', (VRF False) ρ η (.word2 r' P) (shp (.word2 (.lit 0) P)) [w0, w1] := by
    intro r'
    simp only [VRF, VRb2]
    refine ⟨hpwf, _, _, by simp [hwv0, hwv1]; exact ⟨rfl, rfl⟩, ?_⟩
    obtain ⟨cl', hcl', hent⟩ := hst
    obtain ⟨h0, h1, h2⟩ := hent ρ hi1.1
    exact ⟨_, cl', _, _, hcl', h0, h1, h2⟩
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi1 (hvr _) (Lay_word2 _ _ _ w0 w1), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21274 tstepM_mkEPair
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_mkEPairB {x rn : String} {P : ECounter} {v0 v1 : At} {e : Expr}
    (hterm : th.term = .let_ x (.mkEPair rn P v0 v1) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | mkEPair _ hpwf hv0 hv1 hb =>
  obtain ⟨tv0, htvk0, hio0⟩ := hv0
  obtain ⟨tv1, htvk1, hio1⟩ := hv1
  obtain ⟨rt0, w0, hea0, hwv0, -⟩ := atom_numB hi.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hea1, hwv1, -⟩ := atom_numB hi.2.1 htvk1 hio1
  have key : tstep g mem pairs th =
      [((stOf mem pairs th).mem, (stOf mem pairs th).pairs,
        withS { th with term := e, env := (x, .epair (.lit 0) P, [w0, w1]) :: th.env } (stOf mem pairs th))] := by
    simp only [tstep, hterm, evalOp, hea0, hea1]; rfl
  rw [key]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : ∀ r', (VRF False) ρ η (.epair r' P) (shp (.epair (.lit 0) P)) [w0, w1] := by
    intro r'
    simp only [VRF, VRb2]
    exact ⟨hpwf, _, _, by simp [hwv0, hwv1]; exact ⟨rfl, rfl⟩⟩
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by simpa [withS] using bind_FInvB hb hi (hvr _) (Lay_epair _ _ _ w0 w1), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21350 tstepM_ldpOwn
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ldpOwnB {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .own u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ := ownPtr_viewB hi hpk htv hoq
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us, hus, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := acq) (s := stOf mem pairs th)
    hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl hoq hea rfl)
  obtain ⟨hru, hpr⟩ := pair_ru .own hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hro), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, f1, f2, f3, f4, f5⟩ := hld (s', wsr) hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  exact ⟨CE η, EFoot_reflB, ⟨vcons m1 (vcons m0 ρ), η, c', rfl, hE, he, htv',
    bind_FInvB hb (push_FInvB n1 m1 (push_FInvB n0 m0 hi)) hvr' (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl)), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩,
    MemInv_loadB hm f1 f2 f3 f4 f5 (loadUnits_relSt _ _ _ _ hl) (loadUnits_vWr _ _ _ _ hl)⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21393 tstepM_ldpPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ldpPubB {x w n0 n1 : String} {acq : Bool} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.ptr .pub u))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ru, pw, lab, us, hea, hpw, hus, hsku, hne, hld, hstw⟩ :=
    loadPub_coreB (acq := acq) (g := g) (mem := mem) (pairs := pairs) hpk hoq hi hE htv hm
  obtain ⟨hru, hpr⟩ := pair_ru .pub hu hsku
  rw [hru] at hus; cases hus
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ⟨lab, 0⟩ acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, addrOf, hpw, ↓reduceIte, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  exact ⟨CE η, EFoot_reflB, ⟨vcons m1 (vcons m0 ρ), η, c', rfl, hE, he, htv',
    bind_FInvB hb (push_FInvB n1 m1 (push_FInvB n0 m0 hi)) hvr' (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl)), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21444 stpOwn_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem stpOwn_coreB {x : String} {rel : Bool} {a v0 v1 tk : At} {c₁ c' : Cx}
    {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr .own (.word2 r P)))
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hj0 : IntIdx c₁ v0 j0) (hj1 : IntIdx c₁ v1 j1)
    (hst : InState2 c₁ P j0 j1 c₂ k0' k1')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hj0
  obtain ⟨tv1, htvk1, hio1⟩ := hj1
  obtain ⟨rt0, w0, hev0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hev1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  obtain ⟨lab, c, pw, ru, hea, hpw, hsto, hcty, hacc, hown, hsku, hsig⟩ :=
    ownPtr_viewB hi hpk htv (by simp [Cx.opaqueOK, Ty.guardT])
  have hna : ∀ N e', c.ty ≠ .array (.lit N) e' := fun N e' h => hacc (by rw [h]; simp [accs])
  obtain ⟨us0, -, ⟨ro, hro⟩, hld, hstw⟩ := ownLoadB (arch := g.arch) (pw := pw) (acq := false)
    (s := stOf mem pairs th) hE.2.1 hm.2.1 hm.2.2.2.2.2.2.2.2.2.2 hm.2.2.2.2.2.2.2.2.1 hsto hown (Fd_lay hcty).1 (Fd_lay hcty).2.1
    (fun ws => ((Fd_lay hcty).2.2.2 ws).1) (fun R ws => (Fd_VRB η hcty).1) hna hsku
    (peek_cell_lytB hi.2.1 hpk hea rfl rfl).2 hsig
    (by rw [(Fd_lay hcty).2.2.1]; exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl)
  have hpwf : pwf2 P = true := by
    obtain ⟨_, hvr0, -⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word2 r'' P) = some [.two] := by simp [accs]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
  have hlen : [w0, w1].length = nWords [Acc.two] := rfl
  have husA : accs c.ty = some [Acc.two] := ((Fd_lay hcty).2.2.1.trans (pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl (by simp [Cx.opaqueOK, Ty.guardT]) hea rfl).symm).trans hus
  have hus' : wc c.ty = some (nWords [Acc.two]) := by
    rw [(Fd_lay hcty).2.1, ← wc_of_sig hsig]; simp [wc, hus]
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.two] [w0, w1] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩,
    MemInv_storeB hm hsto hown husA hval hlen s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:21493 stpPub_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem stpPub_coreB {x : String} {rel : Bool} {a v0 v1 tk : At} {c₁ c' : Cx}
    {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.ptr .pub (.word2 r P)))
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hj0 : IntIdx c₁ v0 j0) (hj1 : IntIdx c₁ v1 j1)
    (hst : InState2 c₁ P j0 j1 c₂ k0' k1')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hj0
  obtain ⟨tv1, htvk1, hio1⟩ := hj1
  obtain ⟨rt0, w0, hev0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hev1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  have ho : cx.opaqueOK (.word2 r P) = true := by simp [Cx.opaqueOK, Ty.guardT]
  have hpwf : pwf2 P = true := by
    obtain ⟨ru0, pw0, lab0, us0, -, -, -, -, hne, hld, hstw⟩ :=
      loadPub_coreB (acq := false) (g := g) (mem := mem) (pairs := pairs) hpk ho hi hE htv hm
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨lab, c, pw, ru, f, hea, hpw, hsto, hcty, hf, -, hacc, hsku, hsig⟩ := pubPtr_viewB hi hpk htv ho
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hus : accs (Ty.word2 r'' P) = some [.two] := by simp [accs]
  have hlr : accs (Ty.word2 r'' P) = accs c.ty := by
    rw [(Fd_lay hcty).2.2.1]
    exact pub_accsB hi.2.2.2.1 hi.2.2.2.2.1 (fun k => (hE.2.1 k).1) hi.2.1 htv hpk rfl ho hea rfl
  have husc : accs c.ty = some [.two] := by rw [← hlr, hus]
  have hval := (Fd_EnvValB (CE η) hcty).2 (storeWord2_valB (r := r) hpwf hi1.1 hst hwv0 hwv1)
  have hlen : [w0, w1].length = nWords [Acc.two] := rfl
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ⟨lab, 0⟩ rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, addrOf, hpw, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ⟨lab, 0⟩) (rel := rel)
    [.two] [w0, w1] 0 (stOf mem pairs th) hlen
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  refine ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩, ?_⟩
  by_cases hown : c.owner = some η.tid
  · exact MemInv_storeFB hm hsto hown husc hval hlen s' hs'
  · have hna : ∀ N e, c.ty ≠ .array (.lit N) e := fun N e he => by rw [he] at husc; simp [accs] at husc
    exact MemInv_storePubAtB (a := ⟨lab, 0⟩) hm hsto hown hf (.here (Or.inl (by rw [husc]; simp)))
      (IniAt_of_ne fun N e he => hna N e he) hna hval husc hlen s' hs'
end
end TermStep.Flat

-- PORTB TermStep.lean:21544 tstepM_stp
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_stpB {x : String} {rel : Bool} {a v0 v1 tk : At} {μ : Mode} {r : Idx} {P : Proto2}
    {e : Expr}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | stpGive hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact stpOwn_coreB (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
    · exact stpPub_coreB (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | stpKeep hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    rcases hμ with rfl | rfl
    · exact stpOwn_coreB (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨by simp [VRF, VRb2], Lay_etok_unit rfl⟩ hi hE htv hm hRP
    · exact stpPub_coreB (hDy := hDy) hterm hpk hu hj0 hj1 hst hb he htv' ⟨by simp [VRF, VRb2], Lay_etok_unit rfl⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:22092 casp_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem casp_coreB {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {tw : Ty} {i0 i1 j0 j1 : Idx}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ tw)) (hμ : μ = .own ∨ μ = .pub)
    (htw : (∃ r P, tw = .word2 r P) ∨ (∃ r P, tw = .epair r P))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hnv : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      (∃ R ws, (VRF False) ρ η tw R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 tw) [n0, n1])
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPw th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨te0, hte0, hio0⟩ := hie0
  obtain ⟨rt0, x0, hee0, -, -⟩ := atom_numB hi.2.1 hte0 hio0
  obtain ⟨te1, hte1, hio1⟩ := hie1
  obtain ⟨rt1, x1, hee1, -, -⟩ := atom_numB hi.2.1 hte1 hio1
  obtain ⟨tv0, htv0, hjo0⟩ := hj0
  obtain ⟨rtv0, n0, hev0, hn0, -⟩ := atom_numB hi.2.1 htv0 hjo0
  obtain ⟨tv1, htv1, hjo1⟩ := hj1
  obtain ⟨rtv1, n1, hev1, hn1, -⟩ := atom_numB hi.2.1 htv1 hjo1
  obtain ⟨lab, pw, rw, hea, hpw, hne, hcell⟩ := caspCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ htw (hnv n0 n1 hn0 hn1) hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw n0 n1) 1 2 ⟨lab, 0⟩ x0.val x1.val
          (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
        (mem', pairs', withS (if (th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1, th'.regs 2]⟩) := by
    simp only [tstep, hterm, hea, hee0, hee1, hev0, hev1, addrOf, hpw]; rfl
  rw [key] at ⊢
  obtain ⟨hx0, hx1⟩ := loadUnits_two_msg hne
  refine ⟨fun h => stepRmwPair_ne_nil hx0 hx1 (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd0, rd1, hl1, hr0, hr1, hcase⟩ := stepRmwPair_split (k := g.k) (s := stOf mem pairs th) hin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmc⟩ := stepRmwPair_mem hin (by decide) (MemInv_nopairB hm)
  have hp3 : th'.promises = th.promises := by
    rcases hmc with ⟨_, _, h⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h
  have hs1p : s1.promises = th.promises :=
    (TermMem.loadUnits_frame [.two] 0 (stOf mem pairs th) (s1, [rd0, rd1]) hl1).2.2.1
  obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
  rcases hcase with ⟨hne', hsame⟩ | ⟨h0, h1, s2, hs2, hsame⟩ | ⟨h0, h1, tw', pm, htw', hpm, hpl, hsame⟩
  rotate_right
  · exfalso
    have e := hsame.2.2.2.1
    rw [lockS_prom] at e
    simp only [pairFulS] at e
    rw [hp3, hs1p] at e
    rw [hs1p] at htw'
    have hl := congrArg List.length e
    have h1 := List.length_erase_of_mem htw'
    have h2 := List.length_erase_le (l := th.promises.erase tw') (a := tw' + 1)
    have h3 := List.length_pos_of_mem htw'
    omega
  · have hp1 : PromAbove s1 := PromAbove_lockS (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 hp1
    have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = false := by
      rw [hr0, hr1]
      cases e0 : (rd0.val == x0.val) <;> cases e1 : (rd1.val == x1.val) <;> simp_all
    simp only [hb]
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = true := by
      rw [hr0, hr1]; simp [h0, h1]
    simp only [hb]
    have hp2 : PromAbove s2 :=
      PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 (fun t ht m hm => (storeUnits_promAbove (s := bumpRel (lockR g.arch (stOf mem pairs th) s1) _) hs2 hp2) t ht m hm)
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22170 tstepM_casp
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_caspB {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {u : Ty}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  have hw2 : ∀ {r : Idx} {P : Proto2} {j0 j1 k0' k1' : Idx} {c₂ : Nat},
      u = .word2 r P → InState2 cx P j0 j1 c₂ k0' k1' →
      ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
        (∃ R ws, (VRF False) ρ η u R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 u) [n0, n1] := by
    intro r P j0 j1 k0' k1' c₂ hu' hst n0 n1 hn0 hn1 ⟨R, ws, hvr⟩
    subst hu'
    have hpwf : pwf2 P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeWord2_valB hpwf hi.1 hst hn0 hn1
  cases hT0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp [word2Of] at hwn
    simp only [epairOf, Option.some.injEq, Prod.mk.injEq] at hwe; obtain ⟨rfl, rfl⟩ := hwe
    refine casp_coreB (hDy := hDy) hterm hpk hμ (Or.inr ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 ⟨R, ws, hvr⟩ => ?_)
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPw_eq hRP (bind_ret hb)⟩
      hfail hi hE htv hm hRP
    have hpwf : pwfE P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeEPair_valB hpwf ⟨_, _, hn0, hn1⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreB (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPw_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspMove hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreB (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPw_eq hRP (bind_ret hb)⟩
        hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspTake hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreB (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPw_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
end
end TermStep.Flat

-- PORTB TermStep.lean:22246 tstepM_ldpLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_ldpLocB {x w n0 n1 : String} {acq : Bool} {μ : Mode} {u : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.ldp acq (.var w) n0 n1) e) (hP : ProgT p)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hpk : cx.peek (.var w) = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | ldp hp _ hb =>
  rw [hpk] at hp; cases hp
  have hoq : cx.opaqueOK u = true := by
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩ <;> simp [Cx.opaqueOK, Ty.guardT]
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, -, hstw⟩ :=
    locCellB (acq := acq) (rel := false) (g := g) (mem := mem) (pairs := pairs) hpk hμ hoq
      (pair_accs_cl hu) hi hE htv hm
  obtain ⟨-, hpr⟩ := pair_ru_loc μr hu hsku
  have key : tstep g mem pairs th =
      (loadUnits g.arch pw ad acq [.two] 0 (stOf mem pairs th)).map fun (s', ws) =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .prod .int .int, ws) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hpr, haddr, ↓reduceIte, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => hne (List.map_eq_nil_iff.1 h), fun r0 hr hpr0 => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨⟨s', wsr⟩, hl, rfl⟩ := hr
  obtain ⟨hvr, -, hm'⟩ := hld s' wsr hl (hpr0)
  obtain ⟨w0, w1, m0, m1, rfl, hvr'⟩ := pair_bindB (bkG := False) hu hvr
  exact ⟨CE η, EFoot_reflB, ⟨vcons m1 (vcons m0 ρ), η, c', rfl, hE, he, htv',
    bind_FInvB hb (push_FInvB n1 m1 (push_FInvB n0 m0 hi)) hvr' (Lay_pair (Lay_int w0 rfl) (Lay_int w1 rfl)), retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22284 stpLoc_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem stpLoc_coreB {x : String} {rel : Bool} {a v0 v1 tk : At} {c₁ c' : Cx}
    {μ : Mode} {r r' i0 i1 j0 j1 k0' k1' : Idx} {P : Proto2} {c₂ : Nat} {e : Expr} {xt : Ty}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hu : cx.use tk = .ok (.tok2 r' P i0 i1, c₁)) (hj0 : IntIdx c₁ v0 j0) (hj1 : IntIdx c₁ v1 j1)
    (hst : InState2 c₁ P j0 j1 c₂ k0' k1')
    (hb : c₁.bind x xt = .ok c') (he : Typed p c' e) (htv' : TvOK c')
    (htag : StoreBindB ρ η th.σs xt)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨hi1, -⟩ := use_FInvB (bkG := False) hu hi
  obtain ⟨tv0, htvk0, hio0⟩ := hj0
  obtain ⟨tv1, htvk1, hio1⟩ := hj1
  obtain ⟨rt0, w0, hev0, hwv0, -⟩ := atom_numB hi1.2.1 htvk0 hio0
  obtain ⟨rt1, w1, hev1, hwv1, -⟩ := atom_numB hi1.2.1 htvk1 hio1
  obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
    locCellB (acq := false) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
      (by simp [Cx.opaqueOK, Ty.guardT]) (pair_accs_cl (wit := η.wit) (Or.inl ⟨r, P, rfl⟩)) hi hE htv hm
  have hpwf : pwf2 P = true := by
    obtain ⟨_, hvr0⟩ := hstw
    simp only [VRF, VRb2] at hvr0; exact hvr0.1
  obtain ⟨r'', rfl⟩ := eskel_word2 (show etok (skel ru) = .word2 (.lit 0) P by rw [hsku]; rfl)
  have hval := storeWord2_valB (η := η) (r := r) hpwf hi1.1 hst hwv0 hwv1
  have key : tstep g mem pairs th =
      (storeUnits g.k g.arch pw ad rel [.two] [w0, w1] 0 (stOf mem pairs th)).map fun s' =>
        (s'.mem, s'.pairs, withS { th with term := e, env := (x, .unit, []) :: th.env } s') := by
    simp only [tstep, hterm, evalOp, hea, hev0, hev1, word2Of, haddr, List.map_map]; rfl
  rw [key]
  obtain ⟨s0, hs0⟩ := storeUnits_nonempty (k := g.k) (arch := g.arch) (pw := pw) (a := ad) (rel := rel)
    [.two] [w0, w1] 0 (stOf mem pairs th) rfl
  refine ⟨List.ne_nil_of_mem (List.mem_map_of_mem hs0), fun r hr => ?_⟩
  rw [List.mem_map] at hr
  obtain ⟨s', hs', rfl⟩ := hr
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', bind_FInvB hb hi1 htag.1 htag.2, retPw_eq hRP ((bind_ret hb).trans (use_ret hu)), hDy.letW hterm rfl⟩, hsto _ _ hm hval rfl s' hs'⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22322 tstepM_stpLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_stpLocB {x : String} {rel : Bool} {a v0 v1 tk : At} {μ : Mode} {r : Idx} {P : Proto2}
    {e : Expr}
    (hterm : th.term = .let_ x (.stp rel a v0 v1 tk) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ (.word2 r P))) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  cases hop with
  | stpGive hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact stpLoc_coreB (hDy := hDy) hterm hpk hμ hu hj0 hj1 hst hb he htv' ⟨unit_VRB (bkG := False), unit_Lay _⟩ hi hE htv hm hRP
  | stpKeep hp hw hu _ hj0 hj1 _ _ hst _ _ _ _ hb =>
    rw [hpk] at hp; cases hp
    simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
    exact stpLoc_coreB (hDy := hDy) hterm hpk hμ hu hj0 hj1 hst hb he htv' ⟨by simp [VRF, VRb2], Lay_etok_unit rfl⟩ hi hE htv hm hRP
end
end TermStep.Flat

-- PORTB TermStep.lean:22383 casp_coreLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem casp_coreLocB {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {tw : Ty} {i0 i1 j0 j1 : Idx}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.loc μ tw)) (hμ : μ = .own ∨ μ = .pub)
    (htw : (∃ r P, tw = .word2 r P) ∨ (∃ r P, tw = .epair r P))
    (hie0 : IntIdx cx e0 i0) (hie1 : IntIdx cx e1 i1) (hj0 : IntIdx cx v0 j0) (hj1 : IntIdx cx v1 j1)
    (hnv : ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
      (∃ R ws, (VRF False) ρ η tw R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 tw) [n0, n1])
    (hok : ∃ c', Typed p c' ok ∧ TvOK c' ∧ FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) c' ((t, .unit, []) :: th.env) ∧ RetPw th.σs th.stack c'.ret)
    (hfail : Typed p cx fail)
    (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  obtain ⟨te0, hte0, hio0⟩ := hie0
  obtain ⟨rt0, x0, hee0, -, -⟩ := atom_numB hi.2.1 hte0 hio0
  obtain ⟨te1, hte1, hio1⟩ := hie1
  obtain ⟨rt1, x1, hee1, -, -⟩ := atom_numB hi.2.1 hte1 hio1
  obtain ⟨tv0, htv0, hjo0⟩ := hj0
  obtain ⟨rtv0, n0, hev0, hn0, -⟩ := atom_numB hi.2.1 htv0 hjo0
  obtain ⟨tv1, htv1, hjo1⟩ := hj1
  obtain ⟨rtv1, n1, hev1, hn1, -⟩ := atom_numB hi.2.1 htv1 hjo1
  obtain ⟨ad, pw, rw, hea, haddr, hne, hcell⟩ := caspLocCellB (acq := acq) (rel := rel) (g := g) (mem := mem)
    (pairs := pairs) hpk hμ htw (hnv n0 n1 hn0 hn1) hi hE htv hm
  have key : tstep g mem pairs th =
      (Promises.stepRmwPair g.arch mem pairs (mth (stOf mem pairs th) pw n0 n1) 1 2 ad x0.val x1.val
          (dataE 1 n0) (dataE 2 n1) [0] acq rel).map fun (mem', pairs', th') =>
        (mem', pairs', withS (if (th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val then
            { th with term := ok, env := (t, .unit, []) :: th.env } else { th with term := fail })
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1, th'.regs 2]⟩) := by
    simp only [tstep, hterm, hea, hee0, hee1, hev0, hev1, haddr]; rfl
  rw [key] at ⊢
  obtain ⟨hx0, hx1⟩ := loadUnits_two_msg hne
  refine ⟨fun h => stepRmwPair_ne_nil hx0 hx1 (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd0, rd1, hl1, hr0, hr1, hcase⟩ := stepRmwPair_split (k := g.k) (s := stOf mem pairs th) hin
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hmc⟩ := stepRmwPair_mem hin (by decide) (MemInv_nopairB hm)
  have hp3 : th'.promises = th.promises := by
    rcases hmc with ⟨_, _, h⟩ | ⟨_, _, _, _, h, _⟩ <;> exact h
  have hs1p : s1.promises = th.promises :=
    (TermMem.loadUnits_frame [.two] 0 (stOf mem pairs th) (s1, [rd0, rd1]) hl1).2.2.1
  obtain ⟨c', hok', htv', hi', hrpk⟩ := hok
  rcases hcase with ⟨hne', hsame⟩ | ⟨h0, h1, s2, hs2, hsame⟩ | ⟨h0, h1, tw', pm, htw', hpm, hpl, hsame⟩
  rotate_right
  · exfalso
    have e := hsame.2.2.2.1
    rw [lockS_prom] at e
    simp only [pairFulS] at e
    rw [hp3, hs1p] at e
    rw [hs1p] at htw'
    have hl := congrArg List.length e
    have h1 := List.length_erase_of_mem htw'
    have h2 := List.length_erase_le (l := th.promises.erase tw') (a := tw' + 1)
    have h3 := List.length_pos_of_mem htw'
    omega
  · have hp1 : PromAbove s1 := PromAbove_lockS (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 hp1
    have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = false := by
      rw [hr0, hr1]
      cases e0 : (rd0.val == x0.val) <;> cases e1 : (rd1.val == x1.val) <;> simp_all
    simp only [hb]
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, cx, rfl, hE, hfail, htv, hi, hRP, hDy.rightW (fun _ => by rw [hterm]; rfl) rfl⟩, MemInv_sameB (MemInv_lockSB g.arch hm1) hsame⟩
  · have hb : ((th'.regs 1).val == x0.val && (th'.regs 2).val == x1.val) = true := by
      rw [hr0, hr1]; simp [h0, h1]
    simp only [hb]
    have hp2 : PromAbove s2 :=
      PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
    obtain ⟨hm1, hst2⟩ := hcell s1 [rd0, rd1] hl1 (fun t ht m hm => (storeUnits_promAbove (s := bumpRel (lockR g.arch (stOf mem pairs th) s1) _) hs2 hp2) t ht m hm)
    exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, hok', htv', hi', hrpk, hDy.leftW (fun _ => by rw [hterm]; rfl) rfl⟩,
      MemInv_sameB (MemInv_lockSB g.arch
        (MemInv_setRelB (hst2 _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22458 tstepM_caspLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_caspLocB {acq rel : Bool} {w e0 e1 v0 v1 : At} {t : String} {ok fail : Expr}
    {μ : Mode} {u : Ty}
    (hterm : th.term = .casp acq rel w e0 e1 v0 v1 t ok fail)
    (hpk : cx.peek w = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hu : (∃ r P, u = .word2 r P) ∨ (∃ r P, u = .epair r P))
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  have hw2 : ∀ {r : Idx} {P : Proto2} {j0 j1 k0' k1' : Idx} {c₂ : Nat},
      u = .word2 r P → InState2 cx P j0 j1 c₂ k0' k1' →
      ∀ n0 n1 : Word, n0.val = .num (ev ρ j0) → n1.val = .num (ev ρ j1) →
        (∃ R ws, (VRF False) ρ η u R ws) → EnvValB (CE η) (cl ρ η.wit 0 0 u) [n0, n1] := by
    intro r P j0 j1 k0' k1' c₂ hu' hst n0 n1 hn0 hn1 ⟨R, ws, hvr⟩
    subst hu'
    have hpwf : pwf2 P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeWord2_valB hpwf hi.1 hst hn0 hn1
  cases hT0 with
  | caspE hp hwn hwe _ hie0 hie1 hj0 hj1 _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp [word2Of] at hwn
    simp only [epairOf, Option.some.injEq, Prod.mk.injEq] at hwe; obtain ⟨rfl, rfl⟩ := hwe
    refine casp_coreLocB (hDy := hDy) hterm hpk hμ (Or.inr ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1
      (fun n0 n1 hn0 hn1 ⟨R, ws, hvr⟩ => ?_)
      ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPw_eq hRP (bind_ret hb)⟩
      hfail hi hE htv hm hRP
    have hpwf : pwfE P = true := by simp only [VRF, VRb2] at hvr; exact hvr.1
    exact storeEPair_valB hpwf ⟨_, _, hn0, hn1⟩
  | caspBump hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreLocB (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPw_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspMove hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreLocB (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1, bind_FInvB hb hi (unit_VRB (bkG := False)) (unit_Lay _), retPw_eq hRP (bind_ret hb)⟩
        hfail hi hE htv hm hRP
    · simp [word2Of] at hw
  | caspTake hp hw hie0 hie1 hj0 hj1 _ _ hst _ _ _ _ _ hb hok hfail =>
    rw [hpk] at hp; cases hp
    rcases hu with ⟨r, P, rfl⟩ | ⟨r, P, rfl⟩
    · simp only [word2Of, Option.some.injEq, Prod.mk.injEq] at hw; obtain ⟨rfl, rfl⟩ := hw
      exact casp_coreLocB (hDy := hDy) hterm hpk hμ (Or.inl ⟨_, _, rfl⟩) hie0 hie1 hj0 hj1 (hw2 rfl hst)
        ⟨_, hok, (bind_TvOK hb htv (by simp [tb]) (by simp [mg])).1,
          bind_FInvB hb hi (by simp [VRF, VRb2]) (Lay_etok_unit rfl), retPw_eq hRP (bind_ret hb)⟩ hfail hi hE htv hm hRP
    · simp [word2Of] at hw
end
end TermStep.Flat

-- PORTB TermStep.lean:22797 fetch_core
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem fetch_coreB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At} {e : Expr}
    {ad : Address} {pw nw : Word} {rt rv : Ty} {dd : Nat}
    {Q : List Word → Prop} {SOK : Word → Prop}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e)
    (hea : evalAt th.env a = some (rt, [pw])) (haddr : addrOf pw = some ad)
    (hev : evalAt th.env v = some (rv, [nw])) (hnw : nw.val = .num dd)
    (hne : loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) ≠ [])
    (hcell : ∀ s1 ws, (s1, ws) ∈ loadUnits g.arch pw ad acq [.one] 0 (stOf mem pairs th) → PromAbove s1 →
      MemInvB g (CE η) s1 ∧ Q ws ∧ ∀ s1', MemInvB g (CE η) s1' → ∀ w, SOK w →
        ∀ s2, s2 ∈ storeUnits g.k g.arch pw ad rel [.one] [w] 0 s1' → MemInvB g (CE η) s2)
    (hpost : ∀ rd, Q [rd] → SOK (cst (o.kind.apply rd.val (.num dd))) ∧
      ∃ ρ' cx', Typed p cx' e ∧ TvOK cx' ∧
        FInvB g.lbase g.n g.i ρ' η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx' ((x, fetchRtTy rt, [rd]) :: th.env) ∧ RetPw th.σs th.stack cx'.ret)
    (hDy : DyFr p annNew (progTgts p) η th.σs th.term) (hE : EnvOKB p η) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hd : dataE 1 nw = .const nw.val := by simp [dataE, hnw]
  have key : tstep g mem pairs th =
      (Promises.stepRmw g.k g.arch mem pairs (mth (stOf mem pairs th) pw nw nw) 1 ad o.kind
          (dataE 1 nw) [0] acq rel).map fun (mem', th') =>
        (mem', pairs, withS { th with term := e, env := (x, fetchRtTy rt, [th'.regs 1]) :: th.env }
          ⟨mem', pairs, th'.vs, th'.promises, th.nalloc, th.undefs + countUndef [th'.regs 1]⟩) := by
    simp only [tstep, hterm, evalOp, hea, hev, haddr, List.map_map]; rfl
  rw [key] at ⊢
  refine ⟨fun h => stepRmw_ne_nil_any (loadUnits_one_msg hne) (List.map_eq_nil_iff.1 h), fun r hr hpr0 => ?_⟩
  have hpr := hpr0
  rw [List.mem_map] at hr
  obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := hr
  obtain ⟨s1, rd, hl1, hrd, s2, hs2, hsame⟩ :=
    stepRmw_splitF (s := stOf mem pairs th) (FetchOp.kind_isFetch o) hd hin
  have hp2 : PromAbove s2 :=
    PromAbove_lockS (s := setRel s2 (lockR g.arch (stOf mem pairs th) s1).vs) (PromAbove_same hsame (fun t ht m hm => hpr t ht m hm))
  have hp1' : PromAbove (bumpRel (lockR g.arch (stOf mem pairs th) s1) _) := storeUnits_promAbove hs2 hp2
  have hp1 : PromAbove s1 := fun t ht m hm => hp1' t ht m hm
  obtain ⟨hm1, hq, hst⟩ := hcell s1 [rd] hl1 hp1
  obtain ⟨hsok, ρ', cx', he', htv', hi', hrpk⟩ := hpost rd hq
  rw [hnw] at hs2
  subst hrd
  exact ⟨CE η, EFoot_reflB, ⟨ρ', η, cx', rfl, hE, he', htv', hi', hrpk, hDy.letW hterm rfl⟩,
    MemInv_sameB (MemInv_lockSB g.arch
      (MemInv_setRelB (hst _ (MemInv_bumpRelB (MemInv_lockRB g.arch (stOf mem pairs th) hm1) _) _ hsok s2 hs2) (MemInv_lockRB g.arch (stOf mem pairs th) hm1).2.2.2.2.1)) hsame⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:22869 VR_fetchEpoch
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem VR_fetchEpochB {ρ : Nat → Nat} {η : TEnv} {r r' : Idx} {P : Proto} {rd : Word} {n : Nat}
    (hn : rd.val = .num n) : (VRF False) ρ η (fetchEpochTy r P) (shp (fetchEpochTy r' P)) [rd] := by
  simp only [fetchEpochTy, VRF, VRb2, shp]
  refine ⟨_, _, n, rfl, _, _, rfl, fun k hk => ?_⟩
  simp [Shp.wc, wc, accs] at hk
  subst hk
  simp [VRF, VRb2, hn, ev, vcons, vins, nWords, Acc.size]
end
end TermStep.Flat

-- PORTB TermStep.lean:22882 tstepM_fetch
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_fetchB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.ptr μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨lab, pw, ru, hea, hpw, hnwr, hne, hcell⟩ :=
        pubIntCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInvB (bkG := False) hu hi
      have hvi := VR_subB (bkG := False) hi1.1 hsub _ _ hvv
      simp only [VRF, VRb2] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      have hrt : fetchRtTy (.ptr .pub ru) = .int := by
        cases ru <;> simp [fetchRtTy, wordOf]
        exact (hnwr _ _ rfl).elim
      refine fetch_coreB (hDy := hDy) hterm hea (by simp [addrOf, hpw]) hev hnwv hne hcell (fun rd hq => ?_) hE
      obtain ⟨n, hn⟩ := hq
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
      obtain ⟨m, hm'⟩ := FetchOp.apply_num o n dd
      refine ⟨⟨m, by simp [cst, Promises.TVal.mk0, hn, hm']⟩, ρ, c', he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
      rw [hrt]
      exact bind_FInvB hb hi1 (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    obtain ⟨lab, pw, μ', r', hea, hpw, hne, hcell⟩ :=
      wordCellFB (bkG := False) (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    have hrt : fetchRtTy (.ptr μ' (.word r' P)) = fetchEpochTy r' P := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreB (hDy := hDy) hterm hea (by simp [addrOf, hpw]) hev hnwv hne hcell (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + 1)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_epoch hpwf hep (n + 1)), ρ, c', he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (VR_fetchEpochB hn) (Lay_fetchEpoch _ r r' P rd)
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inl rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    obtain ⟨lab, pw, μ', r', hea, hpw, hne, hcell⟩ :=
      wordCellFB (bkG := False) (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ hg hi hE htv hm
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    have hrt : fetchRtTy (.ptr μ' (.word r' P)) = .int := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreB (hDy := hDy) hterm hea (by simp [addrOf, hpw]) hev hnwv hne hcell (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, hin⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + d)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_fetch hok hin), ρ, c', he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
end
end TermStep.Flat

-- PORTB TermStep.lean:22981 tstepM_fetchLoc
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_fetchLocB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {o : FetchOp} {acq rel : Bool} {a v : At}
    {e : Expr} {μ : Mode} {u : Ty}
    (hterm : th.term = .let_ x (.fetch o acq rel a v) e) (hP : ProgT p)
    (hpk : cx.peek a = .ok (.loc μ u)) (hμ : μ = .own ∨ μ = .pub)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  rw [hterm] at hT0
  cases hT0 with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | fetchCell hp _ hc hu hsub hb =>
    rw [hpk] at hp; cases hp
    rcases hc with hc | ⟨r, hc, -⟩
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      have hus1 : accs (cl ρ η.wit 0 0 .int) = some [.one] := by simp [cl, accs]
      obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
        locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
          (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
      obtain ⟨hi1, rv, wsv, hev, hvv, -⟩ := use_FInvB (bkG := False) hu hi
      have hvi := VR_subB (bkG := False) hi1.1 hsub _ _ hvv
      simp only [VRF, VRb2] at hvi
      obtain ⟨dd, hdd⟩ := hvi
      obtain ⟨nw, rfl, hnwv⟩ := map_singleton hdd
      have hrt : fetchRtTy (.loc μr ru) = .int := by
        cases ru <;> simp [fetchRtTy, wordOf]
        simp [skel, etok, close, substTs] at hsku
      refine fetch_coreB (hDy := hDy) (Q := fun ws => ∃ n, ws.map (·.val) = [.num n])
        (SOK := fun w => ∃ m, w.val = .num m) hterm hea haddr hev hnwv hne
        (fun s1 ws hl hp1 => ?_) (fun rd hq => ?_) hE
      · obtain ⟨hvr, -, hm1⟩ := hld s1 ws hl hp1
        refine ⟨hm1, by simpa [VRF, VRb2] using hvr, fun s1' hm1' w ⟨m, hw⟩ s2 hs2 => ?_⟩
        exact hsto s1' [w] hm1' (intValB (ρ := ρ) hw) rfl s2 hs2
      · obtain ⟨n, hn⟩ := hq
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
        obtain ⟨m, hm'⟩ := FetchOp.apply_num o n dd
        refine ⟨⟨m, by simp [cst, Promises.TVal.mk0, hn, hm']⟩, ρ, c', he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
        rw [hrt]
        exact bind_FInvB hb hi1 (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
    · simp only [cellOf, Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, -⟩ := hc
      rcases hμ with h | h <;> cases h
  | fetchEpoch hp hw hep _ hj heq hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      have := pwf_epochOK hpwf hep
      unfold epochOK at this; simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
      exact this.1.2
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
      locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    have hj1 := heq ρ hi.1
    simp only [ev] at hj1
    rw [hj1] at hnwv
    have hrt : fetchRtTy (.loc μr (.word r' P)) = fetchEpochTy r' P := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreB (hDy := hDy) (Q := fun ws => (VRF False) ρ η (.word r P) (shp (.word r' P)) ws)
      (SOK := fun w => EnvValB (CE η) (cl ρ η.wit 0 0 (.word r P)) [w]) hterm hea haddr hev hnwv hne
      (fun s1 ws hl hp1 => ⟨(hld s1 ws hl hp1).2.2, (hld s1 ws hl hp1).1,
        fun s1' hm1' w hw s2 hs2 => hsto s1' [w] hm1' hw rfl s2 hs2⟩) (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, -⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + 1)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_epoch hpwf hep (n + 1)), ρ, c', he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (VR_fetchEpochB hn) (Lay_fetchEpoch _ r r' P rd)
  | fetchShare hp hw hep hj heq hok hb =>
    rw [hpk] at hp; cases hp
    cases u <;> simp [wordOf] at hw
    obtain ⟨rfl, rfl⟩ := hw
    rename_i r P
    have hpwf := wordRef_pwfB hpk (.inr rfl) hμ hi hE htv hm
    have hg : P.ghost = false := by
      unfold fetchOK at hok; simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
      exact hok.1.1.1.1
    have hus1 : accs (cl ρ η.wit 0 0 (.word r P)) = some [.one] := by simp [cl, accs, hg]
    obtain ⟨ad, pw, μr, ru, hea, haddr, -, hsku, -, hne, hld, hsto, hstw⟩ :=
      locCellB (acq := acq) (rel := rel) (g := g) (mem := mem) (pairs := pairs) hpk hμ
        (by simp [Cx.opaqueOK, Ty.guardT]) hus1 hi hE htv hm
    obtain ⟨r', rfl⟩ := eskel_word (show etok (skel ru) = .word (.lit 0) P by rw [hsku]; rfl)
    obtain ⟨tv, htvk, hjo⟩ := hj
    obtain ⟨rtv, nw, hev, hnwv, -⟩ := atom_numB hi.2.1 htvk hjo
    rename_i d
    have hjd := heq ρ hi.1
    simp only [ev] at hjd
    rw [hjd] at hnwv
    have hrt : fetchRtTy (.loc μr (.word r' P)) = .int := by simp [fetchRtTy, wordOf, hep]
    refine fetch_coreB (hDy := hDy) (Q := fun ws => (VRF False) ρ η (.word r P) (shp (.word r' P)) ws)
      (SOK := fun w => EnvValB (CE η) (cl ρ η.wit 0 0 (.word r P)) [w]) hterm hea haddr hev hnwv hne
      (fun s1 ws hl hp1 => ⟨(hld s1 ws hl hp1).2.2, (hld s1 ws hl hp1).1,
        fun s1' hm1' w hw s2 hs2 => hsto s1' [w] hm1' hw rfl s2 hs2⟩) (fun rd hq => ?_) hE
    simp only [VRF, VRb2] at hq
    obtain ⟨n, hn, hin⟩ := hq.2 hg
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hn
    refine ⟨wordValB hpwf (m := n + d)
      (by simp [cst, Promises.TVal.mk0, hn, FetchOp.kind, WeakMem.RmwKind.apply])
      (InP_fetch hok hin), ρ, c', he, htv', ?_, retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0)⟩
    rw [hrt]
    exact bind_FInvB hb hi (by simp [VRF, VRb2, hn]) (Lay_int rd rfl)
end
end TermStep.Flat

-- PORTB TermStep.lean:23149 region_tok_VR
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem region_tok_VRB {ρ : Nat → Nat} {η : TEnv} : (VRF False) ρ η (.tok (.var 0) none) (shp (.tok (.lit 0) none)) [] := by
  simp [VRF, VRb2]
end
end TermStep.Flat

-- PORTB TermStep.lean:23155 openPub_cap_VR
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem openPub_cap_VRB {ρ : Nat → Nat} {η : TEnv} : (VRF False) ρ η (.cap .pub (.var 0)) (shp (.cap .pub (.lit 0))) [] := by
  simp [VRF, VRb2]
end
end TermStep.Flat

-- PORTB TermStep.lean:23208 region_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem region_stepB {p : Prog} {cx : Cx} {a : At} {rn pn tn : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {env : Env}
    (hT : Typed p cx (.region a rn pn tn e)) (hi : FInvB glb gnum gi ρ η σs K cx env) (htv : TvOK cx) (w : Nat) :
    ∃ c, Typed p c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧
      ((∃ μ u ws, evalAt env a = some (.ptr μ u, ws) ∧
        FInvB glb gnum gi (vcons w ρ) η σs K c ((tn, .tok (.lit 0) none, []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: env)) ∨
       (∃ μ u ψ ws, evalAt env a = some (.refine (.loc μ u) ψ, ws) ∧
        FInvB glb gnum gi (vcons w ρ) η σs K c
          ((tn, .tok (.lit 0) none, []) :: (pn, .refine (.loc (.rgn (.lit 0)) u) ψ, ws) :: env))) := by
  cases hT with
  | region hu _ hb1 hb2 he =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      obtain ⟨μ', u', rfl, -, -⟩ := eskel_eq_ptr (by simpa [close, substTs, skel, etok] using hl.2.1)
      refine ⟨_, he, region_TvOK hu (fun h => by simpa [tb] using h) (fun h => by simpa [mg] using h) hb1 hb2 htv,
        by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu], .inl ⟨μ', u', ws, hea, ?_⟩⟩
      exact bind_FInvB hb2 (bind_FInvB hb1 (push_FInvB rn w hi1) (region_ptr_VRB (bkG := False) w hv) (region_ptr_Lay hl))
        region_tok_VRB region_tok_Lay
  | regionBuf hu _ hb1 hb2 he =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      obtain ⟨μ', u', ψ', rfl⟩ := eskel_eq_refloc (by simpa [close, substTs, skel, rf, etok] using hl.2.1)
      refine ⟨_, he, regionBuf_TvOK hu hb1 hb2 htv, by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu], .inr ⟨μ', u', ψ', ws, hea, ?_⟩⟩
      exact bind_FInvB hb2 (bind_FInvB hb1 (push_FInvB rn w hi1) (region_buf_VRB (bkG := False) w hv) (region_buf_Lay hl))
        region_tok_VRB region_tok_Lay
end
end TermStep.Flat

-- PORTB TermStep.lean:23234 openPub_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem openPub_stepB {p : Prog} {cx : Cx} {a : At} {rn pn cn : String} {e : Expr} {ρ : Nat → Nat}
    {η : TEnv} {σs : List Ty} {K : TEnv → List Word → Prop} {env : Env}
    (hT : Typed p cx (.openPub a rn pn cn e)) (hi : FInvB glb gnum gi ρ η σs K cx env) (htv : TvOK cx) (w : Nat) :
    ∃ c, Typed p c e ∧ TvOK c ∧ skel c.ret = skel cx.ret ∧ ∃ μ u ws, evalAt env a = some (.ptr μ u, ws) ∧
        FInvB glb gnum gi (vcons w ρ) η σs K c ((cn, .cap .pub (.lit 0), []) :: (pn, .ptr (.rgn (.lit 0)) u, ws) :: env) := by
  cases hT with
  | openPub hu hb1 hb2 he =>
      obtain ⟨hi1, rt, ws, hea, hv, hl⟩ := use_FInvB (bkG := False) hu hi
      obtain ⟨μ', u', rfl, -, -⟩ := eskel_eq_ptr (by simpa [close, substTs, skel, etok] using hl.2.1)
      refine ⟨_, he, openPub_TvOK hu hb1 hb2 htv, by rw [bind_ret hb2, bind_ret hb1, push_ret, skel_shiftI, use_ret hu], μ', u', ws, hea, ?_⟩
      exact bind_FInvB hb2 (bind_FInvB hb1 (push_FInvB rn w hi1) (region_ptr_VRB (bkG := False) w hv) (region_ptr_Lay hl))
        openPub_cap_VRB openPub_cap_Lay
end
end TermStep.Flat

-- PORTB TermStep.lean:23290 tstep_region
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_regionB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEB g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  have hx := Ext_bumpRB hE.2.1
  obtain ⟨c, hc, hvc, hk, ⟨μ, u, ws, hea, hf⟩ | ⟨μ, u, ψ, ws, hea, hf⟩⟩ := region_stepB hT hi htv (ridNext η)
  all_goals
    simp only [tstep, hterm, hea]
    refine ⟨by simp, ?_⟩
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact ⟨_, bumpRB η, c, CE_bumpRB η, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, hc, hvc, FInv_extB hE.2.1 hx (by simpa [withS] using hf), retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:23307 tstep_openPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstep_openPubB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {a : At} {rn pn cn : String} {e : Expr}
    (hterm : th.term = .openPub a rn pn cn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvEB g.lbase g.n g.i p (CE η) r.2.2 := by
  rw [hterm] at hT
  have hx := Ext_bumpRB hE.2.1
  obtain ⟨c, hc, hvc, hk, μ, u, ws, hea, hf⟩ := openPub_stepB hT hi htv (ridNext η)
  simp only [tstep, hterm, hea]
  refine ⟨by simp, ?_⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  exact ⟨_, bumpRB η, c, CE_bumpRB η, ⟨hE.1, hx.1, hx.2.2.2.2.2.2.2.2.2.2.1⟩, hc, hvc, FInv_extB hE.2.1 hx (by simpa using hf), retPw_skel hPS hRP (skel_subst_eq hk th.σs 0 0 0), hDy.sameW (fun _ => by rw [hterm]; rfl) rfl⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:33135 tstepM_region
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
variable {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_regionB {a : At} {rn pn tn : String} {e : Expr}
    (hterm : th.term = .region a rn pn tn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  ⟨(tstep_regionB (hDy := hDy) hterm hT hi hE htv hRP hPS).1, fun r hr =>
    ⟨CE η, EFoot_reflB, (tstep_regionB (hDy := hDy) hterm hT hi hE htv hRP hPS).2 r hr, by
      rw [fence_region hterm r hr]; exact MemInv_fenceGB _ hm⟩⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:33143 tstepM_openPub
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
variable {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
variable {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
theorem tstepM_openPubB {a : At} {rn pn cn : String} {e : Expr}
    (hterm : th.term = .openPub a rn pn cn e) (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 :=
  liftB hm (tstep_openPubB (hDy := hDy) hterm hT hi hE htv hRP hPS) (same_openPub hterm)
end
end TermStep.Flat

-- ♭ mirror of W TermStep tstepM_isTy (ADD4 isTy op), resource-free layer.
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_isTyB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv} {x : String} {a : At} {τ : Ty} {e : Expr}
    (hterm : th.term = .let_ x (.isTy a τ) e) (hP : ProgT p)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hRP : RetPw th.σs th.stack cx.ret)
    (hPS : PwSkel) (hTy : TyOKE g (CE η)) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  rw [hterm] at hT
  cases hT with
  | let_ hop he =>
  rename_i c'
  have htv' := OpT_TvOK hP hop htv
  have hRk := OpT_retSk hop
  cases hop with
  | isTy hpk hsl hwf htg _ hb =>
  obtain ⟨rt, ws, hea, hvr0, hlay0⟩ := peek_VRB (bkG := False) hi.2.1 hpk
  obtain ⟨pw, ad, cl0, hlast, hpv, ho, hsto, hmo, hacc⟩ := slot_wordB hsl hvr0 hlay0.2.2.1
  obtain ⟨w, hw, hk⟩ := isTy_key (g := g) (mem := mem) (pairs := pairs) hterm hea hlast hpv (close_wf0 th.σs hwf)
  rw [hk]
  refine ⟨by simp, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  subst hr
  have hvr : (VRF False) ρ η (.ptrOpt .pub τ) (shp (.ptrOpt .pub (close th.σs τ))) [w] := by
    simp only [VRF, VRb2]; exact isTy_valB htg hTy hpv ho hsto hmo hacc hw
  exact ⟨CE η, EFoot_reflB, ⟨ρ, η, c', rfl, hE, he, htv', by
      simpa [withS] using bind_FInvB hb hi hvr (isTy_lay (isTy_null_or hpv hw)),
    retPw_skel hPS hRP (skel_subst_eq hRk th.σs 0 0 0), hDy.letW hterm rfl⟩, hm⟩
end
end TermStep.Flat

-- PORTB TermStep.lean:33244 tstepMF_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepMF_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th)
    (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) (hTy : TyOKE g (CE η)) (hZ : ZOK g (CE η) th := by exact fun _ _ h => False.elim h)
    (hPb : ∀ y a e rt ws ad, th.term = .let_ y (.publish a) e → evalAt th.env a = some (rt, ws) →
      ws.map (·.val) = [.loc ad 0] → g.pf ad.label := by exact fun _ _ _ _ _ _ _ _ _ => trivial) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) →
      ThInvMFB p g (CE η) (stOf mem pairs th) r.1 r.2.1 r.2.2 := by
  have hT0 := hT
  generalize ht : th.term = t0 at hT0 hsc
  cases hT0 with
  | let_ hop _ =>
    cases hop with
    | spawn => exact False.elim hsc
    | ext => exact False.elim hsc
    | isTy => exact paW <| tstepM_isTyB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS hTy
    | atom | pair | addS | addI | subS | pack | rem | nameI | bits | bit1 | vmatch | band
    | cvt | toInt | asLanes | fop | fcmp | fop1 | lane | setLane =>
        exact paW <| tstepM_pureB (hDy := hDy) ht trivial hP hT hi hE htv hm hRP hPS
    | packT => exact paW <| tstepM_pureB (hDy := hDy) ht hsc hP hT hi hE htv hm hRP hPS
    | inl => exact tstepM_inlTB (hDy := hDy) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP hPS
    | inr => exact tstepM_inrTB (hDy := hDy) (hbf := hbf) ht hP hn hT hi hE htv hm hpx hRP hPS
    | new => exact paW <| tstepM_newB (hDy := hDy) ht hsc hP hn hT hi hE htv hm hRP hPS
    | publish | publishBuf =>
        exact paW <| (tstepM_publishB (hDy := hDy) (hPb := hPb) ht hP hT hi hE htv hm hsc (fun rt ws ad => hwin _ _ _ rt ws ad ht) hRP hPS).imp
          id fun h r hr => (h r hr).toF
    | intoRgn | intoRgnBuf => exact False.elim hsc
    | newBuf => exact paW <| tstepM_newBufB (hDy := hDy) ht hsc hP hn hT hi hE htv hm hRP hPS
    | idxOwn | idxShared => exact paW <| tstepM_idxB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | bufInit => exact tstepM_bufInitB (hDy := hDy) ht hP hT hi hE htv hm hZ hRP hPS
    | null => exact paW <| tstepM_nullB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | fldOwn | fldShared => exact paW <| tstepM_fldB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | fence => exact paW <| tstepM_fenceB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | zero => exact paW <| tstepM_zeroB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | call => exact paW <| tstepM_callB (hDy := hDy) hp hP ht hT hi hE htv hm hsc hRP
    | fnptr => exact paW <| tstepM_fnptrB (hDy := hDy) hp hP ht hT hi hE htv hm hRP hPS
    | callc => exact paW <| tstepM_callcB (hDy := hDy) hp hP ht hT hi hE htv hm hRP hSig
    | xchgAt => exact tstepM_xchgAtB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | loadAt => exact tstepM_loadAtB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | xchgAtF => exact tstepM_xchgAtFB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | loadAtF => exact tstepM_loadAtFB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | ldlw => exact tstepM_ldlwB (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | ldl => exact tstepM_ldlB (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | stlw => exact tstepM_stlwB (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | stl => exact tstepM_stlB (hDy := hDy) ht hP hT hi hE htv hm hpx hRP hPS
    | fold => exact paW <| tstepM_foldB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | mkWord _ _ _ _ _ _ _ hng _ _ => exact paW <| tstepM_mkWordB (hDy := hDy) ht hP hT hi hE htv hm hng hRP hPS
    | mkWordGhost _ _ _ _ _ _ _ hg _ _ => exact paW <| tstepM_mkWordGhostB (hDy := hDy) ht hP hT hi hE htv hm hg hRP hPS
    | validate | borrow | freeze | endBorrow =>
        exact False.elim hsc
    | mkWord2 => exact paW <| tstepM_mkWord2B (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | mkEPair => exact paW <| tstepM_mkEPairB (hDy := hDy) ht hP hT hi hE htv hm hRP hPS
    | ldp hpk =>
        obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc _ hpk
        · rw [hteq] at hpk
          rcases hμ with rfl | rfl
          · exact tstepM_ldpOwnB (hDy := hDy) ht hP hu hpk hT hi hE htv hm hRP hPS
          · exact tstepM_ldpPubB (hDy := hDy) ht hP hu hpk hT hi hE htv hm hRP hPS
        · rw [hteq] at hpk
          exact tstepM_ldpLocB (hDy := hDy) ht hP hu hpk hμ hT hi hE htv hm hRP hPS
    | stpGive hpk | stpKeep hpk =>
        obtain ⟨μ, r, P, hteq | hteq, hμ⟩ := hsc _ hpk
        · rw [hteq] at hpk
          exact paW <| tstepM_stpB (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP
        · rw [hteq] at hpk
          exact paW <| tstepM_stpLocB (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP
    | mkTicket | claim => exact False.elim hsc
    | fetchCell hpk | fetchEpoch hpk | fetchShare hpk =>
        obtain ⟨μ, u, hteq | hteq, hμ⟩ := hsc _ hpk
        · rw [hteq] at hpk
          exact tstepM_fetchB (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP hPS
        · rw [hteq] at hpk
          exact tstepM_fetchLocB (hDy := hDy) ht hP hpk hμ hT hi hE htv hm hRP hPS
    | loadWord hpk hw =>
        obtain ⟨μ, hteq | hteq⟩ := wordOf_cases hw <;> subst hteq
        · cases μ with
          | own => exact tstepM_loadWordOwnB (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
          | pub => exact tstepM_loadWordPubB (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
          | rgn r' => exact ((hsc _ hpk) r' _ rfl).elim
        · cases μ with
          | own => exact tstepM_loadWordLocB (hDy := hDy) ht hP hpk (.inl rfl) hT hi hE htv hm hRP hPS
          | pub => exact tstepM_loadWordLocB (hDy := hDy) ht hP hpk (.inr rfl) hT hi hE htv hm hRP hPS
          | rgn r' => exact ((hsc _ hpk) r' _ rfl).elim
    | storeWordGive hpk hw | storeWordKeep hpk hw | storeWordHand hpk hw =>
        obtain ⟨μ, hteq⟩ := wordOf_cases hw
        cases μ with
        | own => exact paW <| tstepM_storeWordAnyB (hDy := hDy) ht hP hpk hteq (.inl rfl) hT hi hE htv hm hRP hPS
        | pub => exact paW <| tstepM_storeWordAnyB (hDy := hDy) ht hP hpk hteq (.inr rfl) hT hi hE htv hm hRP hPS
        | rgn r' => rcases hteq with rfl | rfl <;> exact ((hsc _ hpk) r' _ rfl).elim
    | loadRgn hpk _ hc | loadCap hpk _ hc | loadTorn hpk _ hc => exact absurd hc (hsc _ hpk _ _)
    | storeRgn hpk _ hc | storeCap hpk _ hc => exact absurd hc (hsc _ hpk _ _)
    | loadOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact tstepM_loadOwnB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact tstepM_loadLocB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | loadPub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact tstepM_loadPubB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact tstepM_loadPubLocB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | storeOwn hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact paW <| tstepM_storeOwnB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact paW <| tstepM_storeLocB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | storePub hpk hnw hc =>
        rcases cell_cases hc with rfl | rfl
        · exact paW <| tstepM_storePubB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
        · exact paW <| tstepM_storePubLocB (hDy := hDy) ht hP hpk hnw hT hi hE htv hm hRP hPS
    | xchg hpk hx =>
        cases hx with
        | own _ hc =>
            rcases cell_cases hc with rfl | rfl
            · exact tstepM_xchgOwnB (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
            · exact tstepM_xchgLocB (hDy := hDy) ht hP hpk hT hi hE htv hm hRP hPS
        | rgn _ hc => exact absurd hc (hsc _ hpk _ _)
  | split => exact paW <| tstepM_splitB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | unpack => exact paW <| tstepM_unpackB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | unpackT => exact paW <| tstepM_unpackTB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | ifnull => exact paW <| tstepM_ifnullB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | parity => exact paW <| tstepM_parityB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | ifeqPlain | ifeq | ifeqRec | ifeqZero => exact paW <| tstepM_ifeqB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | case => exact tstepM_caseTB (hDy := hDy) (hbf := hbf) ht hn hT hi hE htv hm hpx hRP hPS
  | region | regionBuf => exact paW <| tstepM_regionB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | openPub => exact paW <| tstepM_openPubB (hDy := hDy) ht hT hi hE htv hm hRP hPS
  | casCell hpk | casShare hpk | casTake hpk | casEpoch hpk =>
      rcases hsc _ hpk with ⟨μ, r, P, hteq, hμ⟩ | ⟨u, rfl | rfl, hnw⟩
      · cases hg : P.ghost
        · rcases hteq with rfl | rfl
          · exact tstepM_casWordB (hDy := hDy) ht hpk hμ hg hT hi hE htv hm hRP
          · exact tstepM_casWordLocB (hDy := hDy) ht hpk hμ hg hT hi hE htv hm hRP
        · exact (cas_ghost_absurd (by rw [← ht]; exact hT) hpk hteq
            (wordRef_pwfB hpk hteq hμ hi hE htv hm) hg).elim
      · exact tstepM_casCellB (hDy := hDy) ht hpk hnw hT hi hE htv hm hRP
      · exact tstepM_casCellLocB (hDy := hDy) ht hpk hnw hT hi hE htv hm hRP
  | caspMove hpk | caspTake hpk | caspE hpk | caspBump hpk =>
      obtain ⟨μ, u, hteq | hteq, hμ, hu⟩ := hsc _ hpk
      · rw [hteq] at hpk
        exact tstepM_caspB (hDy := hDy) ht hpk hμ hu hT hi hE htv hm hRP
      · rw [hteq] at hpk
        exact tstepM_caspLocB (hDy := hDy) ht hpk hμ hu hT hi hE htv hm hRP
  | ret =>
      have hst : th.stack ≠ [] := by
        intro h; simp [isDone, ht, h] at hnd
      exact paW <| tstepM_retB ht hst hT hi hE htv hm hn
  | tail => exact paW <| tstepM_tailB (hDy := hDy) hp hP ht hT hi hE htv hm hsc hRP hPS hSub
end
end TermStep.Flat

-- PORTB TermStep.lean:33393 tstepM_step
namespace TermStep.Flat
open TermSound.Flat TermMem.Flat TermTear.Flat TermStep.Flat TermCut.Flat TermTyped.Flat TermBlkZ.Flat TermInterf.Flat TermPubW.Flat TermOwnX2.Flat TermOwnHeldQ.Flat TermOwnK1.Flat TermOwnK2.Flat TermOwnK3.Flat TermOwnK4.Flat
section
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)
theorem tstepM_stepB {p : Prog} {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {cx : Cx} {ρ : Nat → Nat} {η : TEnv}
    [ProgRetIall p] (hP : ProgT p) (hp : g.p = p) (hn : 0 < g.n) (hnd : isDone th = false)
    (hsc : StepScope cx th.term)
    (hT : Typed p cx th.term) (hi : FInvB g.lbase g.n g.i ρ η th.σs (ResumeB g.lbase g.n g.i p th.stack) cx th.env)
    (hE : EnvOKB p η) (htv : TvOK cx) (hm : MemInvB g (CE η) (stOf mem pairs th)) (hbf : g.boxFence = true)
    (hpx : PAx g mem pairs th) (hwin : PubWinT (CE η) (stOf mem pairs th) th) (hRP : RetPw th.σs th.stack cx.ret) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig)
    (hTy : TyOKE g (CE η)) (hRc : RecFresh g g.i th.nalloc) (hDy : DyFr p annNew (progTgts p) η th.σs th.term) :
    tstep g mem pairs th ≠ [] ∧ ∀ r ∈ tstep g mem pairs th, PromAbove (stOf r.1 r.2.1 r.2.2) → ThInvMB p g r.1 r.2.1 r.2.2 :=
  let h := tstepMF_stepB (hDy := hDy) (g := gZ0 g) (hbf := hbf) hP hp hn hnd hsc hT hi hE htv hm hpx hwin hRP hPS hSub hSig hTy
  ⟨h.1, fun r hr hpa => (h.2 r hr hpa).toMT hbf hTy hRc (TermNallocF.tstep_nallocLe hr)⟩
end
end TermStep.Flat


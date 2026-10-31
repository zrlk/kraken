import WeakCore.LiftUpClosed
variable {glb gnum gi : Nat}  -- free supply geometry of the threaded family
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! ContE twin (plan (A)): the resource-free lift `VR_lift`, same `gc`, same relabel as `VRR_lift`. -/

/-- The resource-free tvar oracle condition (twin of `TvL`). -/
def TvLV (T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (η₁ η₂ : TEnv) : Prop :=
  ∀ k rt ws' ws, WLe ws' ws →
    (η₁.get k rt ws' ∨ (VRz (fun _ => 0) (CE η₁) False (η₁.wit k) rt ws' ∧ ∃ S0 w0, η₁.rels k S0 w0)) →
    ∃ ws'', WLe ws'' (rlI (T k rt ws) ws) ∧ η₂.get k rt ws''

section
variable {σ : WeakMem.AllocLabel → WeakMem.AllocLabel}
theorem TvLV.push0 {T : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel} {η₁ η₂ : TEnv}
    (h : TvLV T η₁ η₂) (s : Ty) : TvLV (shT σ T) (η₁.push0 s) (η₂.push0 s) := by
  intro k rt ws' ws hw hor
  cases k with
  | zero =>
    exfalso
    rcases hor with h0 | ⟨-, S0, w0, h0⟩ <;> simp [TEnv.get, TEnv.push0, TEnv.ins, TEnv.insR] at h0
  | succ k =>
    have hor' : η₁.get k rt ws' ∨ (VRz (fun _ => 0) (CE η₁) False (η₁.wit k) rt ws' ∧ ∃ S0 w0, η₁.rels k S0 w0) := by
      rcases hor with h0 | ⟨h1, S0, w0, h0⟩
      · left; simpa [TEnv.get, TEnv.push0, TEnv.ins, TEnv.insR] using h0
      · right; refine ⟨h1, S0, w0, ?_⟩
        simpa [TEnv.push0, TEnv.ins, TEnv.insR] using h0
    obtain ⟨ws'', h1, h2⟩ := h k rt ws' ws hw hor'
    exact ⟨ws'', h1, by simpa [TEnv.get, TEnv.push0, TEnv.ins, TEnv.insR] using h2⟩
end

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

/-- **VR_lift** (resource-free twin of `VRR_lift`): ♭ reading at `η₁` ⇒ W reading at `η₂` of the `gc`-relabeled words, resource
`Res.sw τ`.  `T` is the tvar oracle at `η₁`, `TU` the one at `η₁.unsee` (box payloads).  No `PayLift`. -/
theorem VR_lift (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l)
    (t : Ty) : ∀ (T TU : Nat → Shp → List Word → Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
    (ρ : Nat → Nat) (η₁ η₂ E : TEnv) (rt : Shp) (ws : List Word),
    LiftOKQ cpy σ τ Cp bv η₁ η₂ → LiftCini cpy Cp η₁ η₂ → SameV E η₁ →
    TvLV T η₁ η₂ → TvLV TU η₁.unsee η₂.unsee →
    (∀ k rt ws, ExS cpy σ Cp bv E ws (T k rt ws)) → (∀ k rt ws, ExS cpy σ Cp bv E.unsee ws (TU k rt ws)) →
    (NeC cpy σ bv → TDp cpy T (PTop η₁)) → (NeC cpy σ bv → TDp cpy TU (PTop η₁.unsee)) →
    (VRF False) ρ η₁ t rt ws →
    VR ρ η₂ t rt (rlI (gc cpy σ Cp bv T TU E t rt ws) ws) := by
  induction t with
  | intS i =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]; exact vals_rl_num.2 h
  | int =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]; obtain ⟨n, hn⟩ := h; exact ⟨n, vals_rl_num.2 hn⟩
  | opq o =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]; obtain ⟨n, hn⟩ := h; exact ⟨n, vals_rl_num.2 hn⟩
  | tid =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    obtain ⟨l, c, h1, h2, h3, h4⟩ := h
    rw [rlI_single h1]
    by_cases hx : exmW Cp E ws
    · -- (b′)/T1: an exempt tid head goes to its copy (widened to tid heads)
      rw [pubG_of_exm hx]
      obtain ⟨a', ha', hc, -⟩ := hx
      rw [h1] at ha'
      have e := (List.cons.inj ha').1
      injection e with e1
      have hc' : Cp l := by rw [← e1] at hc; exact hc
      obtain ⟨c₂, hs2, hty⟩ := hm.csto _ _ hc' h2
      exact ⟨cpy l, c₂, vals_rl_loc h1, hs2, by rw [hty]; exact h3, modeOK_cpy hm hc' _⟩
    · simp only [pubG_of_nexm hx]
      refine ⟨σ l, c, vals_rl_loc h1, hm.sto _ _ h2, h3, ?_⟩
      obtain ⟨q, hq, hs | hv | ⟨ho, -⟩⟩ := h4
      · exact ⟨q, hm.pfr _ _ hq, Or.inl (hm.seen _ hs)⟩
      · exact ⟨q, hm.pfr _ _ hq, Or.inr (mem_map_rl_view hv)⟩
      · -- the ungated owner disjunct: the owned tid cell is a copy label (`cown`), so non-exemption
        -- makes the word fresh
        have hCp : Cp l := hm.cown l c h2 ho ⟨q, hq⟩
        have hF : FreshW E ws := (Classical.em (FreshW E ws)).elim id
          (fun hn => (hx ⟨⟨l, 0⟩, h1, hCp, hn⟩).elim)
        obtain ⟨q', hq', hs'⟩ := hF ⟨l, 0⟩ h1
        rw [hE.2.1] at hq'; rw [hE.2.2] at hs'
        exact ⟨q', hm.pfr _ _ hq', hs'.imp (hm.seen _) (fun hv => mem_map_rl_view hv)⟩
  | fix sg w =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]; obtain ⟨hrt, n, hn, hl⟩ := h; exact ⟨hrt, n, vals_rl_num.2 hn, hl⟩
  | lanes sg w =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]; obtain ⟨hrt, n, hn⟩ := h; exact ⟨hrt, n, vals_rl_num.2 hn⟩
  | refine t ψ ih =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h
    have h0 := h
    simp only [VRF, VRb2] at h; simp only [VR, gc]
    obtain ⟨h1, h2, -⟩ := h
    refine ⟨ih T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h1, ?_⟩
    rcases Classical.em (∃ a : WeakMem.Address, ws.map (·.val) = [.loc a 0]) with ⟨a, ha⟩ | hn
    · obtain ⟨w, rfl, hw⟩ := single_of_vals ha
      rcases gc0 (TU := TU) hTx t rt hw with hg | ⟨hg, hc, hF⟩ | ⟨k, hg⟩
      · exact IniR_rlI ψ [w] h2 (fun a' _ => by rw [hg]; exact selIni_lift hm t a'.label σ (Or.inl rfl))
      · have hne : NeC cpy σ bv := ⟨fun e => hsc _ hc (congrFun e _), fun k e => hbc _ k hc (congrFun e _)⟩
        have hdp : PubPos η₁ t rt [w] = true := by
          have := gc_pp hne.1 hne.2 t T TU E (PTop η₁) rt [w] 0 (hTd hne) hg
          rwa [hE.1] at this
        rcases D5bTmp_holds ρ η₁ t ψ rt [w] h0 hdp with hFr | hr
        · exfalso
          obtain ⟨f, hf, hs⟩ := hFr a (by simp [hw])
          refine hF ⟨f, by rw [hE.2.1]; exact hf, ?_⟩
          rcases hs with hs | hv
          · exact Or.inl (by rw [hE.2.2]; exact hs)
          · exact Or.inr (hv w List.mem_cons_self)
        · refine IniR_rlI ψ [w] hr (fun a' ha' => ?_)
          have e : a' = a := by simp [hw] at ha'; exact ha'.symm
          subst e; rw [hg]; exact selIni_cpy hm hci t hc
      · exact IniR_rlI ψ [w] h2 (fun a' _ => by rw [hg]; exact selIni_lift hm t a'.label _ (Or.inr ⟨k, rfl⟩))
    · exact IniR_rlI ψ ws h2 (fun a' ha' => absurd ⟨a', ha'⟩ hn)
  | iex b ih =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h
    obtain ⟨n, rb, w, hrt, hv⟩ := h; subst hrt; simp only [VR, gc]
    exact ⟨n, rb, w, rfl, ih T TU (vcons w ρ) η₁ η₂ E rb ws hm hci hE hT hTU hTx hTUx hTd hTUd hv⟩
  | prod a b iha ihb =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h
    obtain ⟨ra, rb, hrt, hf⟩ := h; subst hrt
    simp only [VR]
    refine ⟨ra, rb, rfl, fun n hn => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hf n hn
    have hG : gc cpy σ Cp bv T TU E (.prod a b) (.prod ra rb) ws = fun i => if i < n then
        gc cpy σ Cp bv T TU E a ra (ws.take n) i else gc cpy σ Cp bv T TU E b rb (ws.drop n) (i - n) := by
      simp only [gc, hn]
    rw [hG]
    refine ⟨by rw [rlI_length]; exact h1, ?_, ?_⟩
    · rw [rlI_take, rlI_congr_lt _ (gc cpy σ Cp bv T TU E a ra (ws.take n)) (ws.take n) (fun i hi => by
        simp only [List.length_take] at hi; simp only [show i < n by omega, if_true])]
      exact iha T TU ρ η₁ η₂ E ra (ws.take n) hm hci hE hT hTU hTx hTUx hTd hTUd h2
    · rw [rlI_drop]
      have e : (fun i => (fun i => if i < n then gc cpy σ Cp bv T TU E a ra (ws.take n) i else
          gc cpy σ Cp bv T TU E b rb (ws.drop n) (i - n)) (i + n)) = gc cpy σ Cp bv T TU E b rb (ws.drop n) := by
        funext i; simp only []; rw [if_neg (by omega), Nat.add_sub_cancel]
      rw [e]; exact ihb T TU ρ η₁ η₂ E rb (ws.drop n) hm hci hE hT hTU hTx hTUx hTd hTUd h3
  | sum a b iha ihb =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h
    obtain ⟨n, Ra, Rb, hrt, hc⟩ := h; subst hrt; simp only [VR]
    refine ⟨n, Ra, Rb, rfl, ?_⟩
    rcases hc with ⟨htier, x, s, B, h1, h2, h3, h4, h5, h6, hA, hB⟩ | ⟨j, p, hd, hA, hB⟩
    · subst h4
      obtain ⟨w0, rfl, hw0⟩ := single_of_vals h1
      have h3E : E.box x.label = some B := by rw [hE.1]; exact h3
      -- packaging: once the pointer's label map `g` and the box payload `P` are known
      have pack : ∀ (g : WeakMem.AllocLabel → WeakMem.AllocLabel) (P : List Word), P.length = B.pay.length →
          η₂.box (g x.label) = some { B with pay := P } →
          ((η₂.seen (g x.label) ∧ ∃ f, η₂.pfr (g x.label) = some f ∧ B.fr ≤ f) ∨ ∀ w ∈ [rl g w0], B.fr ≤ w.view) →
          (B.tag - s < (armsOf Ra).length →
            (isBoxed Ra = true → VR ρ η₂ a (vsh s (shp Ra)) [rl g w0]) ∧
            (isBoxed Ra = false → ∃ q, ofArm Ra (B.tag - s) P = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
              Valid Ra q ∧ VR ρ η₂.unsee a (shp Ra) q)) →
          ((armsOf Ra).length ≤ B.tag - s →
            (isBoxed Rb = true → VR ρ η₂ b (vsh (s + (armsOf Ra).length) (shp Rb)) [rl g w0]) ∧
            (isBoxed Rb = false → ∃ q, ofArm Rb (B.tag - s - (armsOf Ra).length) P = some q ∧
              ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VR ρ η₂.unsee b (shp Rb) q)) →
          ((Ty.sum Ra Rb).tier = .boxed ∧ ∃ x' s' B', [rl g w0].map (·.val) = [.loc x' 0] ∧ x'.offset = 0 ∧
            η₂.box x'.label = some B' ∧ some (s + 1) = some (s' + 1) ∧
            (s' ≤ B'.tag ∧ ((armsOf (.sum Ra Rb))[B'.tag - s']?).bind wc = some B'.pay.length) ∧
            ((η₂.seen x'.label ∧ ∃ f, η₂.pfr x'.label = some f ∧ B'.fr ≤ f) ∨ ∀ w ∈ [rl g w0], B'.fr ≤ w.view) ∧
            (B'.tag - s' < (armsOf Ra).length →
              (isBoxed Ra = true → VR ρ η₂ a (vsh s' (shp Ra)) [rl g w0]) ∧
              (isBoxed Ra = false → ∃ q, ofArm Ra (B'.tag - s') B'.pay = some q ∧ ShapeC Ra q ∧ wc Ra ≠ none ∧
                Valid Ra q ∧ VR ρ η₂.unsee a (shp Ra) q)) ∧
            ((armsOf Ra).length ≤ B'.tag - s' →
              (isBoxed Rb = true → VR ρ η₂ b (vsh (s' + (armsOf Ra).length) (shp Rb)) [rl g w0]) ∧
              (isBoxed Rb = false → ∃ q, ofArm Rb (B'.tag - s' - (armsOf Ra).length) B'.pay = some q ∧
                ShapeC Rb q ∧ wc Rb ≠ none ∧ Valid Rb q ∧ VR ρ η₂.unsee b (shp Rb) q))) := by
        intro g P hP hb hptr hA' hB'
        exact ⟨htier, ⟨g x.label, x.offset⟩, s, { B with pay := P }, vals_rl_loc (ws := [w0]) h1, h2, hb, rfl,
          ⟨h5.1, by rw [hP]; exact h5.2⟩, hptr, hA', hB'⟩
      by_cases hl : B.tag - s < (armsOf Ra).length
      · by_cases hbx : isBoxed Ra = true
        · -- arm boxed: the IH reads the same pointer at the arm
          have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              gc cpy σ Cp bv T TU E a (vsh s (shp Ra)) [w0] := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbx]
          have ih1 := iha T TU ρ η₁ η₂ E _ [w0] hm hci hE hT hTU hTx hTUx hTd hTUd ((hA hl).1 hbx)
          rw [rlI_one] at ih1; rw [hG, rlI_one]
          obtain ⟨P, hP, hb, hptr⟩ := boxptr_lift hm hE h3 h6 (gc0 (TU := TU) hTx a _ hw0)
          exact Or.inl (pack _ P hP hb hptr (fun _ => ⟨fun _ => ih1, fun e => absurd hbx (by rw [e]; simp)⟩)
            (fun h' => absurd hl (by omega)))
        · -- arm unboxed: the pointer goes to the variant
          have hbf : isBoxed Ra = false := by simpa using hbx
          obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hA hl).2 hbf
          have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              fun _ y => bv y (PCode.enc σ cpy bv (shIA Ra (gc cpy σ Cp bv TU TU E.unsee a (shp Ra) q))
                B.pay.length) := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbf, q1, Bool.false_eq_true, if_false]
          rw [hG, rlI_one]
          have hxq := gc_ExS (cpy := cpy) (σ := σ) (Cp := Cp) (bv := bv) a TU TU E.unsee (shp Ra) q hTUx
          refine Or.inl (pack _ _ (rlI_length _ _) (hm.vbox _ _ _ h3)
            (h6.imp (fun ⟨hs, f, hf, hle⟩ => ⟨hm.vseen _ _ hs, f, hm.vpfr _ _ _ hf, hle⟩)
              (fun hv => rlI_views (fun _ => fun y => bv y _) (ws := [w0]) hv))
            (fun _ => ⟨fun e => absurd e (by rw [hbf]; simp), fun _ => ⟨_, ofArm_variant hxq q1, ShapeC_rlI q2, q3,
              Valid_rlI _ _ _ q4,
              iha TU TU ρ η₁.unsee η₂.unsee E.unsee (shp Ra) q hm.unsee hci.unsee hE.unsee hTU hTU hTUx hTUx hTUd hTUd q5⟩⟩)
            (fun h' => absurd hl (by omega)))
      · have hl' : (armsOf Ra).length ≤ B.tag - s := Nat.le_of_not_lt hl
        by_cases hbx : isBoxed Rb = true
        · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              gc cpy σ Cp bv T TU E b (vsh (s + (armsOf Ra).length) (shp Rb)) [w0] := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbx, if_false]
          have ih1 := ihb T TU ρ η₁ η₂ E _ [w0] hm hci hE hT hTU hTx hTUx hTd hTUd ((hB hl').1 hbx)
          rw [rlI_one] at ih1; rw [hG, rlI_one]
          obtain ⟨P, hP, hb, hptr⟩ := boxptr_lift hm hE h3 h6 (gc0 (TU := TU) hTx b _ hw0)
          exact Or.inl (pack _ P hP hb hptr (fun h' => absurd h' hl)
            (fun _ => ⟨fun _ => ih1, fun e => absurd hbx (by rw [e]; simp)⟩))
        · have hbf : isBoxed Rb = false := by simpa using hbx
          obtain ⟨q, q1, q2, q3, q4, q5⟩ := (hB hl').2 hbf
          have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum (some (s + 1)) (.sum Ra Rb)) [w0] =
              fun _ y => bv y (PCode.enc σ cpy bv (shIA Rb (gc cpy σ Cp bv TU TU E.unsee b (shp Rb) q))
                B.pay.length) := by
            simp only [gc, htier, if_true, h1, h3E, hl, hbf, q1, Bool.false_eq_true, if_false]
          rw [hG, rlI_one]
          have hxq := gc_ExS (cpy := cpy) (σ := σ) (Cp := Cp) (bv := bv) b TU TU E.unsee (shp Rb) q hTUx
          refine Or.inl (pack _ _ (rlI_length _ _) (hm.vbox _ _ _ h3)
            (h6.imp (fun ⟨hs, f, hf, hle⟩ => ⟨hm.vseen _ _ hs, f, hm.vpfr _ _ _ hf, hle⟩)
              (fun hv => rlI_views (fun _ => fun y => bv y _) (ws := [w0]) hv))
            (fun h' => absurd h' hl)
            (fun _ => ⟨fun e => absurd e (by rw [hbf]; simp), fun _ => ⟨_, ofArm_variant hxq q1, ShapeC_rlI q2, q3,
              Valid_rlI _ _ _ q4,
              ihb TU TU ρ η₁.unsee η₂.unsee E.unsee (shp Rb) q hm.unsee hci.unsee hE.unsee hTU hTU hTUx hTUx hTUd hTUd q5⟩⟩))
    · have ht : ¬ (Ty.sum Ra Rb).tier = .boxed := fun e => by rw [e] at hd; simp [decodeArm] at hd
      refine Or.inr ⟨j, rlI (shI (Ty.sum Ra Rb).tier (gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws)) p,
        by rw [decodeArm_rlI, hd]; rfl, fun hj => ?_, fun hj => ?_⟩
      · obtain ⟨q, q1, q2⟩ := hA hj
        refine ⟨_, by rw [ofArm_rlI, q1]; rfl, ?_⟩
        have key : rlI (unA Ra (shI (Ty.sum Ra Rb).tier (gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws))) q
            = rlI (gc cpy σ Cp bv T TU E a (shp Ra) q) q := by
          by_cases hp : p = []
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws = fun _ => σ := by
              simp only [gc, ht, if_false, hd, hp, if_true]
            rw [hG, unA_shI_cst]
            subst hp
            rw [rlI_noloc _ q (ofArm_nil_noloc q1), rlI_noloc _ q (ofArm_nil_noloc q1)]
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws =
                unI (Ty.sum Ra Rb).tier (shIA Ra (gc cpy σ Cp bv T TU E a (shp Ra) q)) := by
              simp only [gc, ht, if_false, hd, hp, hj, if_true, q1]
            rw [hG, shI_unI]
            exact rlI_congr _ _ q (unA_shIA_loc q1 _)
        rw [key]; exact iha T TU ρ η₁ η₂ E (shp Ra) q hm hci hE hT hTU hTx hTUx hTd hTUd q2
      · obtain ⟨q, q1, q2⟩ := hB hj
        refine ⟨_, by rw [ofArm_rlI, q1]; rfl, ?_⟩
        have hj' : ¬ j < (armsOf Ra).length := Nat.not_lt.mpr hj
        have key : rlI (unA Rb (shI (Ty.sum Ra Rb).tier (gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws))) q
            = rlI (gc cpy σ Cp bv T TU E b (shp Rb) q) q := by
          by_cases hp : p = []
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws = fun _ => σ := by
              simp only [gc, ht, if_false, hd, hp, if_true]
            rw [hG, unA_shI_cst]
            subst hp
            rw [rlI_noloc _ q (ofArm_nil_noloc q1), rlI_noloc _ q (ofArm_nil_noloc q1)]
          · have hG : gc cpy σ Cp bv T TU E (.sum a b) (.sum n (.sum Ra Rb)) ws =
                unI (Ty.sum Ra Rb).tier (shIA Rb (gc cpy σ Cp bv T TU E b (shp Rb) q)) := by
              simp only [gc, ht, if_false, hd, hp, hj', if_true, q1]
            rw [hG, shI_unI]
            exact rlI_congr _ _ q (unA_shIA_loc q1 _)
        rw [key]; exact ihb T TU ρ η₁ η₂ E (shp Rb) q hm hci hE hT hTU hTx hTUx hTd hTUd q2
  | tvar k =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    obtain ⟨ws', hw, hor⟩ := h; exact hT k rt ws' ws hw hor
  | code sg tau e =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]
    obtain ⟨i, d, h1, h2⟩ := h
    refine ⟨i, d, vals_rl_num.2 h1, ?_⟩
    rw [hm.prog, hm.wit]; exact h2
  | void => intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h
  | tex κ b ih =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h
    obtain ⟨n, rb, s, hrt, hc, hw, hv⟩ := h; subst hrt; simp only [VR, gc]
    exact ⟨n, rb, s, rfl, hc, hw, ih (shT σ T) (shT σ TU) ρ (η₁.push0 s) (η₂.push0 s) E rb ws (hm.push0 s)
      (hci.push0 s) hE (hT.push0 s) (hTU.push0 s) (ExS_shT hTx) (ExS_shT hTUx) (TDp.push0 hTd s) (TDp.push0 hTUd s) hv⟩
  | mu b ih =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [hm.wit]
    exact ih (shT σ T) (shT σ TU) ρ _ _ E rt ws (hm.push0 _) (hci.push0 _) hE (hT.push0 _) (hTU.push0 _)
      (ExS_shT hTx) (ExS_shT hTUx) (TDp.push0 hTd _) (TDp.push0 hTUd _) h
  | iall b ih =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    exact fun n => ih T TU (vcons n ρ) η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd (h n)
  | word r P =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]
    obtain ⟨hp, hg⟩ := h
    exact ⟨hp, fun e => by obtain ⟨n, hn, hi⟩ := hg e; exact ⟨n, vals_rl_num.2 hn, hi⟩⟩
  | word2 r P =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]
    obtain ⟨hp, n0, n1, hn, hi⟩ := h
    exact ⟨hp, n0, n1, vals_rl_pair.2 hn, hi⟩
  | epair e P =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR, gc]
    rw [rlI_cst]
    obtain ⟨hp, n0, n1, hn⟩ := h
    exact ⟨hp, n0, n1, vals_rl_pair.2 hn⟩
  | ptr μ u _ =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR]
    obtain ⟨a, c, h1, h2, h3, h4, hmo, h5⟩ := h
    rw [gc_ptr]; exact (ref_lift hm hE h1 h2 h3 h4 hmo h5).1
  | ptrOpt μ u _ =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR]
    rw [gc_ptrOpt]
    rcases h with hn | ⟨a, c, h1, h2, h3, h4, hmo, h5⟩
    · exact Or.inl (vals_rlI_null hn)
    · exact Or.inr (ref_lift hm hE h1 h2 h3 h4 hmo h5).1
  | loc μ u _ =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h; simp only [VRF, VRb2] at h; simp only [VR]
    rw [gc_loc]
    rcases h with ⟨hn, e, he⟩ | ⟨a, c, U, h1, h3, h4, h5, hmo, hI⟩
    · exact Or.inl ⟨vals_rlI_null hn, e, by rw [hm.wit]; exact he⟩
    · exact Or.inr (loc_lift hm hci hE h1 h3 h4 h5 hmo hI).1
  | _ =>
    intro T TU ρ η₁ η₂ E rt ws hm hci hE hT hTU hTx hTUx hTd hTUd h
    simp only [VR]
end

theorem CohW_unsee {η : TEnv} (h : Coh η) : Coh η.unsee := fun k => ⟨(h k).1, (h k).2.2, (h k).2.2⟩

section
variable {cpy σ τ : WeakMem.AllocLabel → WeakMem.AllocLabel} {Cp : WeakMem.AllocLabel → Prop}
  {bv : WeakMem.AllocLabel → Nat → WeakMem.AllocLabel}

theorem TvLV_ce0 (η₁ η₂ : TEnv) : TvLV (fun _ _ _ _ => σ) (CE η₁) (CE η₂) := by
  intro k rt ws' ws hw hor
  rcases hor with h | ⟨-, S0, w0, h⟩ <;> exact (h : False).elim

theorem TvLV_ce0u (η₁ η₂ : TEnv) : TvLV (fun _ _ _ _ => σ) (CE η₁).unsee (CE η₂).unsee := by
  intro k rt ws' ws hw hor
  rcases hor with h | ⟨-, S0, w0, h⟩ <;> exact (h : False).elim

/-- **TvLV_top**: the resource-free variable oracle at a coherent pair (twin of `TvL_top`). -/
theorem TvLV_top (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l) {η₁ η₂ : TEnv}
    (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hB : CohBW η₁) (hW : Coh η₂) : TvLV (Ttop cpy σ Cp bv η₁) η₁ η₂ := by
  intro k rt ws' ws hw hor
  have h0 : (VRF False) (fun _ => 0) (CE η₁) (η₁.wit k) rt ws' := by
    rcases hor with h | ⟨h, -⟩
    · exact ((hB k).2.1 (fun _ => 0) rt ws').1 h
    · exact VRz_VRb2 _ _ _ _ _ _ h
  have h1 := VR_upB _ _ _ _ hw h0
  have h2 := VR_lift hsc hbc (η₁.wit k) (fun _ _ _ _ => σ) (fun _ _ _ _ => σ) (fun _ => 0) (CE η₁) (CE η₂) η₁ rt ws
    hm.ce hci.ce ⟨rfl, rfl, rfl⟩ (TvLV_ce0 η₁ η₂) (TvLV_ce0u η₁ η₂) (fun _ _ ws => ExS_cst η₁ ws)
    (fun _ _ ws => ExS_cst η₁.unsee ws) (fun hn => TDp.cst hn.1 _) (fun hn => TDp.cst hn.1 _) h1
  refine ⟨_, WLe_refl _, ?_⟩
  exact ((hW k).2.1 (fun _ => 0) rt _).2 (by rw [hm.wit]; exact h2)

theorem TvLV_unsee (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l) {η₁ η₂ : TEnv}
    (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hB : CohBW η₁) (hW : Coh η₂) : TvLV (Ttop cpy σ Cp bv η₁.unsee) η₁.unsee η₂.unsee :=
  TvLV_top hsc hbc hm.unsee hci.unsee hB.unsee (CohW_unsee hW)

/-- **VR_liftTop** (ContE twin of `VRR_liftTop`): the same word relabel. -/
theorem VR_liftTop (hsc : ∀ l, Cp l → σ l ≠ cpy l) (hbc : ∀ l k, Cp l → bv l k ≠ cpy l) {η₁ η₂ : TEnv}
    (hm : LiftOKQ cpy σ τ Cp bv η₁ η₂) (hci : LiftCini cpy Cp η₁ η₂)
    (hB : CohBW η₁) (hW : Coh η₂) {ρ : Nat → Nat} {t : Ty} {rt : Shp} {ws : List Word}
    (h : (VRF False) ρ η₁ t rt ws) :
    VR ρ η₂ t rt (rlI (gc cpy σ Cp bv (Ttop cpy σ Cp bv η₁) (Ttop cpy σ Cp bv η₁.unsee) η₁ t rt ws) ws) :=
  VR_lift hsc hbc t _ _ ρ η₁ η₂ η₁ rt ws hm hci ⟨rfl, rfl, rfl⟩ (TvLV_top hsc hbc hm hci hB hW)
    (TvLV_unsee hsc hbc hm hci hB hW) (Ttop_ExS η₁) (Ttop_ExS η₁.unsee) (TDp_top η₁) (TDp_top η₁.unsee) h
end

end TermSound.Flat

import WeakCore.TermK2aLd

/-!
# K-2a: counted words name labels the reading view reaches (view-exact `labsIn_pubVR`)

`TermPtrRts.labsIn_pubVR` with the label set replaced by a view-indexed predicate `Q`: every
counted reference word of a value of `T` names a label with a frontier that the word's own view
reaches (or `seen`), or a box.  The arm transfer keeps views exactly (`decodeArm_labsV`,
`ofArm_labsV`, and the reverse roundtrip `roundtrip_rev`, which re-decodes an encoded fitting payload
to a word list whose pointer views are no larger).
-/

namespace TermK2aLabsV

open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermTyped

/-- A label with a frontier reached by the view (or seen), or a box. -/
def QV (η : TEnv) (l : AllocLabel) (v : Ts) : Prop :=
  (∃ f, η.pfr l = some f ∧ (η.seen l ∨ f ≤ v)) ∨ ∃ B, η.box l = some B

/-! ## 1. View-exact transport -/

theorem LabsV_sub {Q : AllocLabel → Ts → Prop} {ws ws' : List Word} (h : LabsV Q ws) (hs : ∀ w ∈ ws', w ∈ ws) :
    LabsV Q ws' := fun w hw => h w (hs w hw)

/-- A decoded payload's references are the value's (label and view). -/
theorem decodeArm_labsVf {Q : AllocLabel → Ts → Prop} {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat}
    {p : List Word} (h : decodeArm tr as ws = some (j, p)) (hG : LabsV Q ws) : LabsV Q p := by
  unfold decodeArm at h
  split at h
  · rename_i w
    split at h
    · rename_i a g hv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨⟨j', x⟩, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro w' hw' a' g' hv'
      rw [List.mem_singleton] at hw'; subst hw'
      simp only [WeakMem.Val.loc.injEq] at hv'
      obtain ⟨rfl, -⟩ := hv'
      exact hG w (List.mem_singleton.2 rfl) a g hv
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      · obtain ⟨-, rfl⟩ := h; intro _ hw; cases hw
      · obtain ⟨-, rfl⟩ := h; intro _ hw _ _ hv; rw [List.mem_singleton] at hw; subst hw; cases hv
    · cases h
  · rename_i t w
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h
      · intro _ hw; cases hw
      · exact LabsV_sub hG fun w' hw => by rw [List.mem_singleton] at hw; subst hw; simp
    · cases h
  · cases h

/-- The counted words' references are the value's (label and view). -/
theorem labsV_pubWords {Q : AllocLabel → Ts → Prop} : ∀ (R : Ty),
    (∀ ws, LabsV Q ws → LabsV Q (pubWords R ws)) ∧ (∀ j p, LabsV Q p → LabsV Q (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, LabsV Q ws → LabsV Q (pubWords (.prod a b) ws) := by
        intro ws h
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs]; exact h
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · intro w hw
            rcases List.mem_append.1 hw with hw | hw
            · exact iha.1 _ (LabsV_sub h (fun _ hx => List.mem_of_mem_take hx)) w hw
            · exact ihb.1 _ (LabsV_sub h (fun _ hx => List.mem_of_mem_drop hx)) w hw
          · intro w hw; cases hw
      exact ⟨h1, fun j p hp => by simp only [pubArm]; exact h1 p hp⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, LabsV Q p → LabsV Q (pubArm (.sum a b) j p) := by
        intro j p hp
        simp only [pubArm]
        split
        · exact iha.2 _ _ hp
        · exact ihb.2 _ _ hp
      refine ⟨fun ws h => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact h
        · split
          · rename_i j p hd
            have hp := decodeArm_labsVf hd h
            split
            · exact iha.2 _ _ hp
            · exact ihb.2 _ _ hp
          · intro w hw; cases hw
  | refine t ψ ih =>
      exact ⟨fun ws h => by rw [pubWords_refine]; exact ih.1 ws h, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
  | iall t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | iex t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | mu t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | tex κ t ih =>
      refine ⟨fun ws h => ?_, fun j p hp => by simp only [pubArm]; exact ih.2 j p hp⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs]; exact h
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 ws h
  | _ =>
      refine ⟨fun ws h => ?_, fun j p hp => ?_⟩
      · rw [pubWords.eq_def]; simp only []
        split
        · exact h
        · intro w hw; cases hw
      · simp only [pubArm]; rw [pubWords.eq_def]; simp only []
        split
        · exact hp
        · intro w hw; cases hw

/-- The counted words of pointwise-`WLe` words are pointwise `WLe`. -/
theorem pubWords_wle : ∀ (R : Ty),
    (∀ ws ws', WLe ws ws' → WLe (pubWords R ws) (pubWords R ws')) ∧
    (∀ j p p', WLe p p' → WLe (pubArm R j p) (pubArm R j p')) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws ws', WLe ws ws' → WLe (pubWords (.prod a b) ws) (pubWords (.prod a b) ws') := by
        intro ws ws' e
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact WLe.append (iha.1 _ _ (WLe.take _ e)) (ihb.1 _ _ (WLe.drop _ e))
          · trivial
      exact ⟨h1, fun j p p' e => by simp only [pubArm]; exact h1 p p' e⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p p', WLe p p' → WLe (pubArm (.sum a b) j p) (pubArm (.sum a b) j p') := by
        intro j p p' e
        simp only [pubArm]
        split
        · exact iha.2 _ _ _ e
        · exact ihb.2 _ _ _ e
      refine ⟨fun ws ws' e => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact e
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none =>
            cases hd' : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws' with
            | none => trivial
            | some x =>
              obtain ⟨j, p⟩ := x
              obtain ⟨p', hp', -⟩ := decodeArm_vals e.vals.symm hd'
              rw [hd] at hp'; cases hp'
          | some x =>
            obtain ⟨j, p⟩ := x
            obtain ⟨p', hp', ep⟩ := decodeArm_wle e hd
            simp only [hp']
            split
            · exact iha.2 _ _ _ ep
            · exact ihb.2 _ _ _ ep
  | refine t ψ ih =>
      exact ⟨fun ws ws' e => by rw [pubWords_refine, pubWords_refine]; exact ih.1 _ _ e,
        fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
  | iall t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | iex t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | mu t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | tex κ t ih =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => by simp only [pubArm]; exact ih.2 _ _ _ e⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs, pubWords_of_sNo hs]; exact e
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _ _ e
  | _ =>
      refine ⟨fun ws ws' e => ?_, fun j p p' e => ?_⟩
      · rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact e
        · trivial
      · simp only [pubArm]; rw [pubWords.eq_def, pubWords.eq_def]; simp only []
        split
        · exact e
        · trivial

/-- An upward-closed `Q` survives growing pointer views. -/
theorem LabsV_wle {Q : AllocLabel → Ts → Prop} (hm : ∀ l v v', v ≤ v' → Q l v → Q l v') :
    ∀ {ws ws' : List Word}, WLe ws ws' → LabsV Q ws → LabsV Q ws'
  | [], [], _, _ => fun _ hw => by cases hw
  | w :: ws, w' :: ws', h, hl => by
      intro x hx a g hv
      rcases List.mem_cons.1 hx with rfl | hx
      · have hv0 : w.val = .loc a g := h.1.1.trans hv
        exact hm _ _ _ (h.1.2 a g hv0) (hl w (by simp) a g hv0)
      · exact LabsV_wle hm h.2 (fun y hy => hl y (List.mem_cons_of_mem _ hy)) x hx a g hv
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- **Roundtrip, reversed**: re-decoding an encoded fitting payload gives words whose pointer views
are no larger than the payload's (`roundtrip_wle`, the other way). -/
theorem roundtrip_rev {t a : Ty} {j : Nat} {p q : List Word} (ht : t.tier ≠ .boxed)
    (ha : (armsOf t)[j]? = some a) (hp : PayOK a p) (he : encodeArm t.tier (armsOf t) j p = some q) :
    ∃ p', decodeArm t.tier (armsOf t) q = some (j, p') ∧ WLe p' p := by
  have hm := getElem?_mem ha
  obtain ⟨⟨k, hk, hk1⟩, hn⟩ := arm_of_tier ht hm
  have hA := atom_of_mem t a hm
  obtain ⟨hl, hptr, hopt⟩ := hp
  cases htr : t.tier with
  | boxed => exact absurd htr ht
  | wide =>
      rw [htr] at he
      rw [hk] at hl; simp at hl
      match p, hl, he with
      | [], hl, he =>
          simp [encodeArm] at he; subst he
          subst hl
          refine ⟨[], ?_, trivial⟩
          simp [decodeArm, bind, Option.bind, ha, hk, pure]
      | [w], hl, he =>
          simp [encodeArm] at he; subst he
          subst hl
          refine ⟨[w], ?_, WLe_refl _⟩
          simp [decodeArm, bind, Option.bind, ha, hk, pure]
      | _ :: _ :: _, hl, _ => simp at hl; omega
  | niche =>
      rw [htr] at he
      simp only [encodeArm, bind, Option.bind, ha] at he
      cases hkd : armK a with
      | ptr =>
          obtain ⟨w, adr, rfl, hw⟩ := hptr hkd
          simp [hkd, hw] at he; subst he
          have hpi : isPtrish a = true := by simp [isPtrish, hkd]
          refine ⟨[{ w with val := .loc adr 0 }], ?_, ⟨hw.symm, fun _ _ _ => Nat.le_refl _⟩, trivial⟩
          simp [decodeArm, bind, Option.bind, ptr_index _ 0 j a ha hpi, pure]
      | opt =>
          obtain ⟨w, rfl, hw⟩ := hopt hkd
          have hpi : isPtrish a = true := by simp [isPtrish, hkd]
          rcases hw with hw | ⟨adr, hw⟩
          · simp [hkd, hw] at he; subst he
            refine ⟨[cst .null], ?_, ⟨by rw [cst_val, hw], fun a g h => by rw [cst_val] at h; cases h⟩, trivial⟩
            simp [decodeArm, bind, Option.bind, ha, hkd, pure]
          · simp [hkd, hw] at he; subst he
            refine ⟨[{ w with val := .loc adr 0 }], ?_, ⟨hw.symm, fun _ _ _ => Nat.le_refl _⟩, trivial⟩
            simp [decodeArm, bind, Option.bind, ptr_index _ 0 j a ha hpi, pure]
      | nil =>
          have := atom_nil hA hkd
          rw [this] at hl; simp at hl
          have hl := hl.symm; rw [List.length_eq_zero_iff] at hl; subst hl
          simp [hkd] at he; subst he
          refine ⟨[], ?_, trivial⟩
          simp [decodeArm, bind, Option.bind, ha, hkd, pure]
      | wide => exact absurd hkd (hn htr)

/-- Through a shallow-pub type: the payload's references are the value's (`ofArm_labsV`). -/
theorem labsV_pubArm_sNo {Q : AllocLabel → Ts → Prop} {A : Ty} {j : Nat} {p q : List Word}
    (h : ofArm A j p = some q) (hs : sNo A = true) (hl : LabsV Q (pubWords A q)) : LabsV Q (pubArm A j p) := by
  rw [pubWords_of_sNo hs] at hl
  exact (labsV_pubWords A).2 j p (ofArm_labsV h hl)

/-! ## 2. The view-exact `labsIn_pubVR` (generic `Q`) -/

/-- `labsIn_VR` at a shallow-pub type: every `loc` word names a cell with a frontier or a box
(`VR` at a `pub` reference reads `η.pfr`, `ModeOK`). -/
theorem labsV_VR_sNo {Q : AllocLabel → Ts → Prop} : ∀ (T : Ty) (ρ : Nat → Nat) (η : TEnv) (R : Ty) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → (∀ l f v, η.pfr l = some f → (η.seen l ∨ f ≤ v) → Q l v) → (∀ l B v, η.box l = some B → Q l v) →
    shp R = shp T → sNo T = true → wc R = some ws.length → Valid R ws → VR ρ η T (shp R) ws → LabsV Q ws := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp only [sNo, Bool.and_eq_true] at hsn
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨ra, rb, hr, hv⟩ := hv
    simp only [shp, Shp.prod.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    cases R0 with
    | prod Ra Rb =>
      simp only [shp, Shp.prod.injEq] at e1
      obtain ⟨ea, eb⟩ := e1
      rw [wc_prod] at hwc
      cases ha : wc Ra with
      | none => simp [ha] at hwc
      | some na =>
        cases hb : wc Rb with
        | none => simp [ha, hb] at hwc
        | some nb =>
          simp [ha, hb] at hwc
          obtain ⟨hle, hva, hvb⟩ := hv na (by rw [← ea, shp_wc]; exact ha)
          obtain ⟨Va, Vb⟩ := hval0 na ha
          intro w hw
          rw [← List.take_append_drop na ws] at hw
          rcases List.mem_append.1 hw with h | h
          · exact iha ρ η Ra _ hrel hS hB ea hsn.1 (by rw [ha, List.length_take]; congr 1; omega) Va
              (by rw [ea]; exact hva) w h
          · exact ihb ρ η Rb _ hrel hS hB eb hsn.2 (by rw [hb, List.length_drop]; congr 1; omega) Vb
              (by rw [eb]; exact hvb) w h
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | sum a b iha ihb =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp only [sNo, Bool.and_eq_true] at hsn
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    cases R0 with
    | sum A B =>
      simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at e1
      obtain ⟨-, eA, eB⟩ := e1
      rw [← eA, ← eB] at hcase
      have hsA : shp A = shp a := by rw [← shp_lnorm A, eA, shp_lnorm]
      have hsB : shp B = shp b := by rw [← shp_lnorm B, eB, shp_lnorm]
      have hlenA : (armsOf (lnorm A)).length = (armsOf A).length := by
        rw [armsOf_lnorm, List.length_map]
      have htl : (Ty.sum (lnorm A) (lnorm B)).tier = (Ty.sum A B).tier := tier_lnorm (.sum A B)
      rcases hcase with ⟨-, x, s, Bx, hvals, -, hbox, -⟩ | ⟨j, p, hd, hA, hB2⟩
      · intro w hw y g hx
        have hm := locPub_mem_val hvals hw
        rw [hx] at hm
        simp at hm
        obtain ⟨rfl, -⟩ := hm
        exact hB _ _ _ hbox
      · rcases hval0 with htb | ⟨j', p', arm, hd', -, -, ⟨q0, he, hveq⟩, hA', hB'⟩
        · rw [htl, htb] at hd; simp [decodeArm] at hd
        · have hd2 := decodeArm_mono (arms_lnorm (.sum A B)) hd'
          rw [htl] at hd
          have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
          simp only [Prod.mk.injEq] at hjp
          obtain ⟨rfl, rfl⟩ := hjp
          refine decodeArm_labsV hd' he hveq ?_
          by_cases hj : j < (armsOf A).length
          · obtain ⟨q, hq, hvq⟩ := hA (by rw [hlenA]; exact hj)
            obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
            have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
            subst hqq
            have hwcq : wc A = some q'.length := by
              cases hu : accs A with
              | none => simp [wc, hu] at hwq
              | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
            rw [shp_lnorm] at hvq
            exact ofArm_labsV hq' (iha ρ η A q' hrel hS hB hsA hsn.1 hwcq hvalq hvq)
          · have hj2 : (armsOf A).length ≤ j := Nat.le_of_not_lt hj
            obtain ⟨q, hq, hvq⟩ := hB2 (by rw [hlenA]; exact hj2)
            obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB' hj2
            rw [hlenA] at hq
            have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
            subst hqq
            have hwcq : wc B = some q'.length := by
              cases hu : accs B with
              | none => simp [wc, hu] at hwq
              | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
            rw [shp_lnorm] at hvq
            exact ofArm_labsV hq' (ihb ρ η B q' hrel hS hB hsB hsn.2 hwcq hvalq hvq)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | refine t ψ ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    exact ih ρ η R ws hrel hS hB hshp hsn hwc hval hv.1
  | iall t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    exact ih (vcons 0 ρ) η R ws hrel hS hB hshp hsn hwc hval (hv 0)
  | mu t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    exact ih ρ (η.push0 (TermClose.cl ρ η.wit 0 0 (.mu t))) R ws (locPub_push0_rels hrel _) hS hB hshp hsn hwc hval hv
  | iex t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    cases R0 with
    | iex Rb =>
      simp only [shp, Shp.iex.injEq] at e1
      rw [wc_iex] at hwc
      exact ih (vcons w ρ) η Rb ws hrel hS hB e1.2 hsn hwc hval0 (by rw [e1.2]; exact hv)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | tex κ t ih =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp only [sNo, Bool.and_eq_true] at hsn
    obtain ⟨R0, e1, e2, e3, n1, n2, n3⟩ := unwrapR R ws
    have hval0 := e3 hval
    rw [hshp] at e1 hv
    rw [← e2] at hwc
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    cases R0 with
    | tex κ' Rb =>
      simp only [shp, Shp.tex.injEq] at e1
      rw [wc_tex] at hwc
      exact ih ρ (η.push0 s) Rb ws (locPub_push0_rels hrel s) hS hB e1.2 hsn.2 hwc hval0 (by rw [e1.2]; exact hv)
    | refine t ψ => exact absurd rfl (n1 t ψ)
    | mu t => exact absurd rfl (n2 t)
    | iall t => exact absurd rfl (n3 t)
    | _ => simp [shp] at e1
  | tvar k =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    obtain ⟨ws', -, hg⟩ := hv
    exact absurd hg (hrel _ _ _)
  | ptr μ u =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    cases μ with
    | pub =>
      obtain ⟨a, c, h1, -, -, -, ⟨f, hf, hmo⟩, -⟩ := hv
      have hm := locPub_mem_val h1 hw
      rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
      exact hS _ _ _ hf (hmo.imp_right (· w hw))
    | _ => simp [sNo, mPub] at hsn
  | ptrOpt μ u =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    cases μ with
    | pub =>
      rcases hv with h0 | ⟨a, c, h1, -, -, -, ⟨f, hf, hmo⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact hS _ _ _ hf (hmo.imp_right (· w hw))
    | _ => simp [sNo, mPub] at hsn
  | loc μ u =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    cases μ with
    | pub =>
      rcases hv with ⟨h0, -⟩ | ⟨a, c, U, h1, -, -, -, ⟨f, hf, hmo⟩, -⟩
      · have hm := locPub_mem_val h0 hw
        rw [hx] at hm; simp at hm
      · have hm := locPub_mem_val h1 hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact hS _ _ _ hf (hmo.imp_right (· w hw))
    | _ => simp [sNo, mPub] at hsn
  | void =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv
    simp [VR] at hv
  | intS i =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    have hm := locPub_mem_val hv hw
    rw [hx] at hm; simp at hm
  | int =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | fix sg wd =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | lanes sg wd =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | code a b _ _ =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨i, d, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | word r P =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    have hlen : wc (.word r P) = some ws.length := by rw [← shp_wc, ← hshp, shp_wc]; exact hwc
    cases hg : P.ghost with
    | true =>
      simp [wc, accs, hg, nWords] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw
    | false =>
      obtain ⟨n, hn, -⟩ := hv.2 hg
      have hm := locPub_mem_val hn hw
      rw [hx] at hm; simp at hm
  | word2 r P =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn, -⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | epair r P =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw x g hx
    obtain ⟨-, n0, n1, hn⟩ := hv
    have hm := locPub_mem_val hn hw
    rw [hx] at hm; simp at hm
  | array i t _ =>
    intro ρ η R ws hrel hS hB hshp hsn hwc
    have hlen : wc (.array i t) = some ws.length := by rw [← shp_wc, ← hshp, shp_wc]; exact hwc
    simp [wc, accs] at hlen
  | unit | share _ | cap _ _ | tok _ _ | tok2 _ _ _ _ | tokE _ _ _ =>
    intro ρ η R ws hrel hS hB hshp hsn hwc hval hv w hw
    have hlen := hwc
    rw [← shp_wc, hshp, shp_wc] at hlen
    simp [wc, accs, nWords] at hlen
    rw [List.eq_nil_of_length_eq_zero hlen.symm] at hw; simp at hw


/-- **Arm payloads**: what a payload counts at its arm is what its injection counts (decoding an
encoded fitting payload gives back the arm and the payload's values, `roundtrip`). -/
theorem labsV_pubArm {Q : AllocLabel → Ts → Prop}
    (hmono : ∀ l v v', v ≤ v' → Q l v → Q l v') : ∀ (A : Ty) (j : Nat) (p q : List Word), ofArm A j p = some q →
    (sumHead A = true → ∃ arm, (armsOf A)[j]? = some arm ∧ PayOK arm p) →
    LabsV Q (pubWords A q) → LabsV Q (pubArm A j p) := by
  intro A
  induction A with
  | sum a b _ _ =>
      intro j p q h hpay hl
      by_cases hs : sNo (.sum a b) = true
      · exact labsV_pubArm_sNo h hs hl
      · obtain ⟨arm, ha, hp⟩ := hpay rfl
        have he : encodeArm (Ty.sum a b).tier (armsOf (.sum a b)) j p = some q := by
          simpa only [ofArm, sumHead, ite_true] using h
        have ht : (Ty.sum a b).tier ≠ .boxed := fun hb => by rw [hb] at he; simp [encodeArm] at he
        obtain ⟨p', hd, ep⟩ := roundtrip_rev ht ha hp he
        have hd2 := decodeArm_mono (arms_lnorm (.sum a b)) hd
        have hl2 : LabsV Q (pubArm (.sum a b) j p') := by
          have e1 : pubWords (.sum a b) q = pubArm (.sum a b) j p' := by
            simp only [pubWords, hs, Bool.false_eq_true, ite_false, ht, hd2, pubArm]
          rw [← e1]; exact hl
        exact LabsV_wle hmono ((pubWords_wle _).2 j p' p ep) hl2
  | refine t ψ ih =>
      intro j p q h hpay hl
      rw [ofArm_refine] at h; rw [pubWords_refine] at hl
      simp only [pubArm]; exact ih j p q h hpay hl
  | iall t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.iall t) = true
      · exact labsV_pubArm_sNo h hs hl
      · rw [ofArm_iall] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | iex t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.iex t) = true
      · exact labsV_pubArm_sNo h hs hl
      · rw [ofArm_iex] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | mu t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.mu t) = true
      · exact labsV_pubArm_sNo h hs hl
      · rw [ofArm_mu] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | tex κ t ih =>
      intro j p q h hpay hl
      by_cases hs : sNo (.tex κ t) = true
      · exact labsV_pubArm_sNo h hs hl
      · rw [ofArm_tex] at h; simp only [pubWords, hs, Bool.false_eq_true, ite_false] at hl
        simp only [pubArm]; exact ih j p q h hpay hl
  | _ =>
      intro j p q h _ hl
      unfold ofArm at h
      simp only [sumHead, Bool.false_eq_true, ite_false] at h
      split at h
      · cases h; simp only [pubArm]; exact hl
      · cases h

/-- The shallow-pub case of `labsV_pubVRg`. -/
theorem labsV_pub_sNo {Q : AllocLabel → Ts → Prop} {T : Ty} {ρ : Nat → Nat} {η : TEnv} {R : Ty} {ws : List Word}
    (hrel : ∀ k r vs, ¬ η.rels k r vs) (hP : ∀ l f v, η.pfr l = some f → (η.seen l ∨ f ≤ v) → Q l v) (hB : ∀ l B v, η.box l = some B → Q l v)
    (hsig : sig R = sig T) (hs : sNo R = true) (hwc : wc R = some ws.length) (hval : Valid R ws)
    (hv : VR ρ η T (shp R) ws) : LabsV Q (pubWords R ws) := by
  rw [pubWords_of_sNo hs]
  exact labsV_VR_sNo T ρ η R ws hrel hP hB (shp_of_sig hsig) (by rw [← sNo_sig T, ← hsig, sNo_sig]; exact hs)
    hwc hval hv

/-- **EnvPub names**: in an env with no type-variable values, the counted words of a
value of `T` held at a runtime type `R` of `T`'s signature (valid, of its word count) name only cells
with a frontier or boxes: a counted reference is `pub` (`ModeOK` reads `η.pfr`), a boxed sum reads
`η.box`; `own`/region references are not counted. -/
theorem labsV_pubVRg {Q : AllocLabel → Ts → Prop}
    (hmono : ∀ l v v', v ≤ v' → Q l v → Q l v') : ∀ (T : Ty) (ρ : Nat → Nat) (η : TEnv) (R : Ty) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) → (∀ l f v, η.pfr l = some f → (η.seen l ∨ f ≤ v) → Q l v) → (∀ l B v, η.box l = some B → Q l v) →
    sig R = sig T → wc R = some ws.length → Valid R ws → VR ρ η T (shp R) ws → LabsV Q (pubWords R ws) := by
  intro T
  induction T with
  | prod a b iha ihb =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨Ra, Rb, rfl, ha, hb⟩ := sig_inv_prod hsig
    obtain ⟨ra, rb, hr, hv⟩ := hv
    simp only [shp, Shp.prod.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    rw [wc_prod] at hwc
    cases hwa : wc Ra with
    | none => simp [hwa] at hwc
    | some na =>
      cases hwb : wc Rb with
      | none => simp [hwa, hwb] at hwc
      | some nb =>
        simp [hwa, hwb] at hwc
        obtain ⟨hle, hva, hvb⟩ := hv na (by rw [shp_wc]; exact hwa)
        obtain ⟨Va, Vb⟩ := hval na hwa
        simp only [pubWords, hs', Bool.false_eq_true, ite_false, hwa]
        intro w hw
        rcases List.mem_append.1 hw with h | h
        · exact iha ρ η Ra _ hrel hP hB ha (by rw [hwa, List.length_take]; congr 1; omega) Va hva w h
        · exact ihb ρ η Rb _ hrel hP hB hb (by rw [hwb, List.length_drop]; congr 1; omega) Vb hvb w h
  | sum a b iha ihb =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨A, B, rfl, hA, hB'⟩ := sig_inv_sum hsig
    obtain ⟨n, Ra, Rb, hr, hcase⟩ := hv
    simp only [shp, lnorm, Shp.sum.injEq, Ty.sum.injEq] at hr
    obtain ⟨-, rfl, rfl⟩ := hr
    have htl : (Ty.sum (lnorm A) (lnorm B)).tier = (Ty.sum A B).tier := tier_lnorm (.sum A B)
    have hlenA : (armsOf (lnorm A)).length = (armsOf A).length := by rw [armsOf_lnorm, List.length_map]
    by_cases hbx : (Ty.sum A B).tier = .boxed
    · simp only [pubWords, hs', Bool.false_eq_true, ite_false, hbx, ite_true]
      rcases hcase with ⟨-, x, s, Bx, hvals, -, hbox, -⟩ | ⟨j, p, hd, -, -⟩
      · intro w hw y g hx
        have hm := locPub_mem_val hvals hw
        rw [hx] at hm; simp at hm; obtain ⟨rfl, -⟩ := hm
        exact hB _ _ _ hbox
      · rw [htl, hbx] at hd; simp [decodeArm] at hd
    · rcases hcase with ⟨htb, -⟩ | ⟨j, p, hd, hA2, hB2⟩
      · rw [htl] at htb; exact absurd htb hbx
      rcases hval with htb | ⟨j', p', arm, hd', harm, hpay, -, hA', hB''⟩
      · exact absurd htb hbx
      have hd2 := decodeArm_mono (arms_lnorm (.sum A B)) hd'
      rw [htl] at hd
      have hjp : (j, p) = (j', p') := Option.some.inj (hd.symm.trans hd2)
      simp only [Prod.mk.injEq] at hjp
      obtain ⟨rfl, rfl⟩ := hjp
      have hd3 : decodeArm (Ty.sum A B).tier (armsOf (lnorm (.sum A B))) ws = some (j, p) := hd2
      simp only [pubWords, hs', Bool.false_eq_true, ite_false, hbx, hd3]
      by_cases hj : j < (armsOf A).length
      · simp only [hj, ite_true]
        obtain ⟨q, hq, hvq⟩ := hA2 (by rw [hlenA]; exact hj)
        obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hA' hj
        have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
        subst hqq
        have hwcq : wc A = some q'.length := by
          cases hu : accs A with
          | none => simp [wc, hu] at hwq
          | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
        rw [shp_lnorm] at hvq
        have hl := iha ρ η A q' hrel hP hB hA hwcq hvalq hvq
        refine labsV_pubArm hmono A j p q' hq' (fun _ => ⟨arm, ?_, hpay⟩) hl
        rw [← List.getElem?_append_left hj]; exact harm
      · simp only [hj, ite_false]
        have hj2 : (armsOf A).length ≤ j := Nat.le_of_not_lt hj
        obtain ⟨q, hq, hvq⟩ := hB2 (by rw [hlenA]; exact hj2)
        obtain ⟨q', hq', hsq, hwq, hvalq⟩ := hB'' hj2
        rw [hlenA] at hq
        have hqq : q' = q := Option.some.inj ((ofArm_lnorm hq').symm.trans hq)
        subst hqq
        have hwcq : wc B = some q'.length := by
          cases hu : accs B with
          | none => simp [wc, hu] at hwq
          | some us => simp only [wc, hu, Option.map_some]; rw [hsq us hu]
        rw [shp_lnorm] at hvq
        have hl := ihb ρ η B q' hrel hP hB hB' hwcq hvalq hvq
        refine labsV_pubArm hmono B _ p q' hq' (fun _ => ⟨arm, ?_, hpay⟩) hl
        rw [← List.getElem?_append_right hj2]; exact harm
  | refine t ψ ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    rw [TermPtrRts.sig_refine] at hsig
    rcases rf_cases (sig t) with e | ⟨u, e⟩
    · exfalso; apply hs
      have h1 : sig t = .int := by cases ht : sig t <;> simp_all [rf]
      rw [← sNo_sig, hsig, e]; rfl
    · rw [e] at hsig
      have hu : u = sig t := rf_eq_refine e
      subst hu
      obtain ⟨R', ψ', rfl, hR'⟩ := sig_inv_refine hsig
      rw [pubWords_refine]
      exact ih ρ η R' ws hrel hP hB hR' (by rw [← hwc]; simp only [wc, accs]) hval hv.1
  | iall t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_iall hsig
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    exact ih (vcons 0 ρ) η R' ws hrel hP hB hR' (by rw [← hwc]; simp only [wc, accs]) hval (hv 0)
  | iex t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_iex hsig
    obtain ⟨n, rb, w, hr, hv⟩ := hv
    simp only [shp, Shp.iex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    rw [wc_iex] at hwc
    exact ih (vcons w ρ) η R' ws hrel hP hB hR' hwc hval hv
  | mu t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_mu hsig
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    exact ih ρ _ R' ws (locPub_push0_rels hrel _) hP hB hR' (by rw [← hwc]; simp only [wc, accs]) hval hv
  | tex κ t ih =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    obtain ⟨R', rfl, hR'⟩ := sig_inv_tex hsig
    obtain ⟨n, rb, s, hr, -, -, hv⟩ := hv
    simp only [shp, Shp.tex.injEq] at hr
    obtain ⟨-, rfl⟩ := hr
    simp only [pubWords, hs', Bool.false_eq_true, ite_false]
    rw [wc_tex] at hwc
    exact ih ρ (η.push0 s) R' ws (locPub_push0_rels hrel s) hP hB hR' hwc hval hv
  | _ =>
    intro ρ η R ws hrel hP hB hsig hwc hval hv
    by_cases hs : sNo R = true
    · exact labsV_pub_sNo hrel hP hB hsig hs hwc hval hv
    have hs' : sNo R = false := by simpa using hs
    rw [pubWords_nonstruct hs' (by rw [hsig]; rfl)]
    intro w hw; cases hw

/-! ## (EnvPub) A typed binding extends `EnvLbl` -/
/-! ## 3. At `QV η` -/

theorem QV_mono {η : TEnv} : ∀ l v v', v ≤ v' → QV η l v → QV η l v' := by
  intro l v v' hle h
  rcases h with ⟨f, hf, hs | hfv⟩ | hb
  · exact .inl ⟨f, hf, .inl hs⟩
  · exact .inl ⟨f, hf, .inr (Nat.le_trans hfv hle)⟩
  · exact .inr hb

theorem labsV_pubVR : ∀ (T : Ty) (ρ : Nat → Nat) (η : TEnv) (R : Ty) (ws : List Word),
    (∀ k r vs, ¬ η.rels k r vs) →
    sig R = sig T → wc R = some ws.length → Valid R ws → VR ρ η T (shp R) ws →
    LabsV (QV η) (pubWords R ws) := by
  intro T ρ η R ws hrel hsig hwc hval hv
  exact labsV_pubVRg QV_mono T ρ η R ws hrel (fun l f _ hf h => .inl ⟨f, hf, h⟩) (fun l B _ hB => .inr ⟨B, hB⟩)
    hsig hwc hval hv

/-! ## 4. The positional corollary -/

/-- Every word of `l` with a nonzero read timestamp has the read timestamp and view of a word of
`ws`, and names every label that word names. -/
def NRV (ws l : List Word) : Prop :=
  ∀ w ∈ l, w.rts ≠ 0 → ∃ w0 ∈ ws, w0.rts = w.rts ∧ w0.view = w.view ∧ ∀ x, Names x w0 → Names x w

theorem nrv_refl (ws : List Word) : NRV ws ws := fun w hw _ => ⟨w, hw, rfl, rfl, fun _ h => h⟩

theorem nrv_nil (ws : List Word) : NRV ws [] := fun _ h => by simp at h

theorem nrv_trans {a b c : List Word} (h1 : NRV a b) (h2 : NRV b c) : NRV a c := by
  intro w hw hr
  obtain ⟨w1, hw1, e1, v1, n1⟩ := h2 w hw hr
  obtain ⟨w0, hw0, e0, v0, n0⟩ := h1 w1 hw1 (by rw [e1]; exact hr)
  exact ⟨w0, hw0, e0.trans e1, v0.trans v1, fun x h => n1 x (n0 x h)⟩

theorem nrv_take (ws : List Word) (n : Nat) : NRV ws (ws.take n) :=
  fun w hw _ => ⟨w, List.mem_of_mem_take hw, rfl, rfl, fun _ h => h⟩

theorem nrv_drop (ws : List Word) (n : Nat) : NRV ws (ws.drop n) :=
  fun w hw _ => ⟨w, List.mem_of_mem_drop hw, rfl, rfl, fun _ h => h⟩

theorem nrv_append {ws a b : List Word} (h1 : NRV ws a) (h2 : NRV ws b) : NRV ws (a ++ b) := by
  intro w hw
  rcases List.mem_append.1 hw with h | h
  · exact h1 w h
  · exact h2 w h

/-- A decoded payload's timestamped words are the value's (read timestamp, view, labels). -/
theorem decodeArm_nrv {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : decodeArm tr as ws = some (j, p)) : NRV ws p := by
  unfold decodeArm at h
  split at h
  · rename_i w
    split at h
    · rename_i a g hv
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
      obtain ⟨⟨j', x⟩, -, h⟩ := h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      intro w' hw' _
      rw [List.mem_singleton] at hw'; subst hw'
      refine ⟨w, List.mem_singleton.2 rfl, rfl, rfl, fun x hn => ?_⟩
      obtain ⟨a', g', hv', hl⟩ := hn
      rw [hv] at hv'; simp only [WeakMem.Val.loc.injEq] at hv'; obtain ⟨rfl, -⟩ := hv'
      exact ⟨a, 0, rfl, hl⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      · obtain ⟨-, rfl⟩ := h; intro _ hw; cases hw
      · obtain ⟨-, rfl⟩ := h; intro _ hw hr; rw [List.mem_singleton] at hw; subst hw; exact absurd rfl hr
    · cases h
  · rename_i t w
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at h
      obtain ⟨arm, -, h⟩ := h
      split at h <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨-, rfl⟩ := h
      · intro _ hw; cases hw
      · intro w' hw _; rw [List.mem_singleton] at hw; subst hw; exact ⟨w', by simp, rfl, rfl, fun _ h => h⟩
    · cases h
  · cases h

/-- The counted words' timestamped words are the value's (read timestamp, view, labels). -/
theorem pubWords_nrv : ∀ (R : Ty), (∀ ws, NRV ws (pubWords R ws)) ∧ (∀ j p, NRV p (pubArm R j p)) := by
  intro R
  induction R with
  | prod a b iha ihb =>
      have h1 : ∀ ws, NRV ws (pubWords (.prod a b) ws) := by
        intro ws
        by_cases hs : sNo (.prod a b) = true
        · rw [pubWords_of_sNo hs]; exact nrv_refl ws
        · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
          split
          · exact nrv_append (nrv_trans (nrv_take ws _) (iha.1 _)) (nrv_trans (nrv_drop ws _) (ihb.1 _))
          · exact nrv_nil ws
      exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum a b iha ihb =>
      have h2 : ∀ j p, NRV p (pubArm (.sum a b) j p) := by
        intro j p
        simp only [pubArm]
        split
        · exact iha.2 _ _
        · exact ihb.2 _ _
      refine ⟨fun ws => ?_, h2⟩
      by_cases hs : sNo (.sum a b) = true
      · rw [pubWords_of_sNo hs]; exact nrv_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]
        split
        · exact nrv_refl ws
        · cases hd : decodeArm (Ty.sum a b).tier (armsOf (lnorm (.sum a b))) ws with
          | none => exact nrv_nil ws
          | some x =>
            obtain ⟨j, p⟩ := x
            have hp : NRV ws p := decodeArm_nrv hd
            simp only []
            split
            · exact nrv_trans hp (iha.2 _ _)
            · exact nrv_trans hp (ihb.2 _ _)
  | refine t ψ ih =>
      exact ⟨fun ws => by rw [pubWords_refine]; exact ih.1 _, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
  | iall t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iall t) = true
      · rw [pubWords_of_sNo hs]; exact nrv_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | iex t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.iex t) = true
      · rw [pubWords_of_sNo hs]; exact nrv_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | mu t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.mu t) = true
      · rw [pubWords_of_sNo hs]; exact nrv_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | tex κ t ih =>
      refine ⟨fun ws => ?_, fun j p => by simp only [pubArm]; exact ih.2 _ _⟩
      by_cases hs : sNo (.tex κ t) = true
      · rw [pubWords_of_sNo hs]; exact nrv_refl ws
      · simp only [pubWords, hs, Bool.false_eq_true, ite_false]; exact ih.1 _
  | _ =>
      refine ⟨fun ws => ?_, fun j p => ?_⟩
      · rw [pubWords.eq_def]; simp only []
        split
        · exact nrv_refl ws
        · exact nrv_nil ws
      · simp only [pubArm]; rw [pubWords.eq_def]; simp only []
        split
        · exact nrv_refl p
        · exact nrv_nil p

theorem wle_tag : ∀ (k : Nat) (ws : List Word), WLe ws (TermCntLoc.tag k ws)
  | _, [] => trivial
  | k, w :: ws => by
      rw [TermCntLoc.tag_cons]
      exact ⟨⟨rfl, fun _ _ _ => Nat.le_refl _⟩, wle_tag (k + 1) ws⟩

theorem mem_tag0 {ws : List Word} {t : Word} (h : t ∈ TermCntLoc.tag 0 ws) :
    ∃ (i : Nat) (w : Word), ws[i]? = some w ∧ t = { w with rts := i + 1 } := by
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem h
  have hlen : i < ws.length := by simpa [TermCntLoc.tag] using hi
  refine ⟨i, ws[i], List.getElem?_eq_getElem hlen, ?_⟩
  rw [← e]; simp [TermCntLoc.tag]

/-- **Positional form** (for K1c): the word at a counted position, naming a label, names a label
whose frontier its view reaches (or `seen`), or a box. -/
theorem labsV_cnt {η : TEnv} {R T : Ty} {ρ : Nat → Nat} {ws : List Word}
    (hrel : ∀ k r vs, ¬ η.rels k r vs) (hsig : sig R = sig T) (hwc : wc R = some ws.length)
    (hval : Valid R ws) (hv : VR ρ η T (shp R) ws) :
    ∀ i ∈ cntIdx R ws, ∀ w0 a g, ws[i]? = some w0 → w0.val = .loc a g → QV η a.label w0.view := by
  intro i hi w0 a g hw0 hv0
  rw [TermCntLoc.cntIdx_eq] at hi
  unfold TermCntLoc.cntK at hi
  rw [List.mem_filterMap] at hi
  obtain ⟨n, hn, hrf⟩ := hi
  rw [List.mem_map] at hn
  obtain ⟨w', hw', rfl⟩ := hn
  unfold TermCntLoc.rf at hrf
  split at hrf
  · cases hrf
  rename_i hne
  obtain ⟨t, ht, htr, htv, htn⟩ := (pubWords_nrv R).1 _ w' hw' hne
  obtain ⟨k, wk, hk, rfl⟩ := mem_tag0 ht
  have e1 : (k + 1 : Nat) = (w'.rts : Nat) := htr
  have e2 : (w'.rts : Nat) - 1 = i := Option.some.inj hrf
  obtain rfl : k = i := by rw [← e2, ← e1, Nat.add_sub_cancel]
  rw [hk] at hw0
  obtain rfl := Option.some.inj hw0
  obtain ⟨a', g', hv', hl⟩ := htn _ ⟨a, g, hv0, rfl⟩
  have hL := labsV_pubVR T ρ η R (TermCntLoc.tag 0 ws) hrel hsig
    (by rw [hwc, (wle_tag 0 ws).length])
    (Valid_vals R ws _ (wle_tag 0 ws).vals hval) (VR_up T (shp R) ws _ (wle_tag 0 ws) hv) w' hw' a' g' hv'
  rw [hl, ← htv] at hL
  exact hL

end TermK2aLabsV

#print axioms TermK2aLabsV.labsV_pubVR
#print axioms TermK2aLabsV.labsV_cnt

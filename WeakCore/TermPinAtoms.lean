import WeakCore.TermPiece

/-! # TermPinAtoms (PIN P1a): the atomic components of a buffer element and block additivity

The pin clause (`TermPinDefs.SlotPinG`) splits memory's share of a predicted slot atom by atom.
* `AtomL T As`: the atomic components of `T` (neither a pair nor a `μ`) with their word offsets, in
  layout order: the descent of `AtOff` through pairs and `μ` unfoldings (zero-width atoms included).
* `VRR_atoms` / `VRR_of_atoms`, `Valid_atoms` / `Valid_of_atoms`, `ValOfR_atoms`: a value of `T` with
  resources `R` is exactly a list of values of its atoms whose resources sum to `R` (block additivity).
-/

namespace TermPinAtoms
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- (PIN) **The atomic components** of a type with their word offsets, in layout order (the descent of
`AtOff`: pairs and closed `μ` unfoldings; zero-width atoms included). -/
inductive AtomL : Ty → List (Nat × Ty) → Prop
  | atom {t : Ty} : AtomT t → AtomL t [(0, t)]
  | prod {a b : Ty} {A B : List (Nat × Ty)} {us : List Acc} : accs a = some us → AtomL a A → AtomL b B →
      AtomL (.prod a b) (A ++ B.map (TermPiece.sh (nWords us)))
  | mu {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} {L : List (Nat × Ty)} : (∀ k, Clo (W k)) →
      s.unguarded 0 = false → AtomL (cl ρ W 0 0 (unfold1 (.mu s))) L → AtomL (cl ρ W 0 0 (.mu s)) L

/-- Indexing an appended list of shifted atoms. -/
theorem getElem?_atoms {A B : List (Nat × Ty)} {n k : Nat} {p : Nat × Ty}
    (h : (A ++ B.map (TermPiece.sh n))[k]? = some p) :
    (k < A.length ∧ A[k]? = some p) ∨
      (A.length ≤ k ∧ ∃ q, B[k - A.length]? = some q ∧ p = (n + q.1, q.2)) := by
  rcases Nat.lt_or_ge k A.length with hk | hk
  · left; rw [List.getElem?_append_left hk] at h; exact ⟨hk, h⟩
  · right
    rw [List.getElem?_append_right hk, List.getElem?_map] at h
    cases hq : B[k - A.length]? with
    | none => rw [hq] at h; cases h
    | some q => rw [hq] at h; cases h; exact ⟨hk, q, rfl, rfl⟩

theorem wc_prod_split {a b : Ty} {us : List Acc} (ha : accs a = some us) {n : Nat} (h : wc (.prod a b) = some n) :
    ∃ ub, accs b = some ub ∧ n = nWords us + nWords ub := by
  cases hb : accs b with
  | none => simp [wc, accs, ha, hb] at h
  | some ub => refine ⟨ub, rfl, ?_⟩; simp [wc, accs, ha, hb, nWords_append] at h; omega

theorem wc_mu_unfold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (hg : s.unguarded 0 = false) :
    wc (cl ρ W 0 0 (unfold1 (.mu s))) = wc (cl ρ W 0 0 (.mu s)) := by
  rw [wc_of_sig (sig_cl_unfold hg)]; rfl

theorem shp_mu_unfold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (hg : s.unguarded 0 = false) :
    shp (cl ρ W 0 0 (unfold1 (.mu s))) = shp (cl ρ W 0 0 (.mu s)) := by
  rw [shp_of_sig (sig_cl_unfold hg)]; rfl

/-- **Block additivity, splitting**: a value's resources split over its atoms. -/
theorem VRR_atoms (E : TEnv) {ρ₀ : Nat → Nat} {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {ws : List Word} {R : Res}, wc T = some ws.length → VRR ρ₀ (CE E) T (shp T) ws R →
      ∃ Rs : List Res, Rs.length = As.length ∧ R = Res.sum Rs ∧
        ∀ (k o : Nat) (U : Ty) (Rk : Res), As[k]? = some (o, U) → Rs[k]? = some Rk →
          ∃ n, wc U = some n ∧ o + n ≤ ws.length ∧ VRR ρ₀ (CE E) U (shp U) ((ws.drop o).take n) Rk := by
  induction hA with
  | @atom t _ =>
      intro ws R hwc hv
      refine ⟨[R], rfl, by simp [Res.sum], fun k o U Rk hk hR => ?_⟩
      cases k with
      | succ k => simp at hk
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk hR
        obtain ⟨rfl, rfl⟩ := hk
        subst hR
        exact ⟨ws.length, hwc, by omega, by simpa using hv⟩
  | @prod a b A B us ha _ _ iha ihb =>
      intro ws R hwc hv
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hwc
      simp only [VRR] at hv
      obtain ⟨ra, rb, e, Ra, Rb, hR, -, hsplit⟩ := hv
      simp only [shp, Shp.prod.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      obtain ⟨-, hva, hvb⟩ := hsplit _ (by rw [shp_wc]; exact hwa)
      have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      obtain ⟨RA, hlA, hRA, hA'⟩ := iha (by rw [hla]; exact hwa) hva
      obtain ⟨RB, hlB, hRB, hB'⟩ := ihb (by rw [hlb]; exact hwb) hvb
      refine ⟨RA ++ RB, by simp [hlA, hlB], by rw [hR, hRA, hRB, Res.sum_append], fun k o U Rk hk hRk => ?_⟩
      rcases getElem?_atoms hk with ⟨hkA, hkA'⟩ | ⟨hkA, ⟨o', U'⟩, hq, he⟩
      · rw [List.getElem?_append_left (by omega)] at hRk
        obtain ⟨n, hn, hon, hvn⟩ := hA' k o U Rk hkA' hRk
        rw [hla] at hon
        refine ⟨n, hn, by omega, ?_⟩
        rw [take_drop_take hon] at hvn; exact hvn
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        rw [List.getElem?_append_right (by omega), hlA] at hRk
        obtain ⟨n, hn, hon, hvn⟩ := hB' _ o' U Rk hq hRk
        rw [hlb] at hon
        refine ⟨n, hn, by omega, ?_⟩
        rw [drop_drop'] at hvn; exact hvn
  | @mu ρ W s L hW hg _ ih =>
      intro ws R hwc hv
      have hv' := (VRR_cl_unfold E hW hg).2 hv
      rw [← shp_mu_unfold hg] at hv'
      exact ih (by rw [wc_mu_unfold hg]; exact hwc) hv'

/-- Every atom lies inside the type's words. -/
theorem AtomL_bound {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {w : Nat}, wc T = some w → ∀ (k o : Nat) (U : Ty), As[k]? = some (o, U) → ∃ n, wc U = some n ∧ o + n ≤ w := by
  induction hA with
  | @atom t _ =>
      intro w hw k o U hk
      cases k with
      | succ k => simp at hk
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨w, hw, by omega⟩
  | @prod a b A B us ha _ _ iha ihb =>
      intro w hw k o U hk
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hw
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      rcases getElem?_atoms hk with ⟨-, hkA⟩ | ⟨-, ⟨o', U'⟩, hq, he⟩
      · obtain ⟨n, hn, hon⟩ := iha hwa k o U hkA
        exact ⟨n, hn, by omega⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨n, hn, hon⟩ := ihb hwb _ o' U hq
        exact ⟨n, hn, by omega⟩
  | @mu ρ W s L hW hg _ ih =>
      intro w hw
      exact ih (by rw [wc_mu_unfold hg]; exact hw)

/-- **Block additivity, assembling**: values of the atoms assemble into a value of the type, holding
the sum. -/
theorem VRR_of_atoms (E : TEnv) {ρ₀ : Nat → Nat} {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {ws : List Word} (Rs : List Res), wc T = some ws.length → Rs.length = As.length →
      (∀ (k o : Nat) (U : Ty) (Rk : Res), As[k]? = some (o, U) → Rs[k]? = some Rk →
        ∃ n, wc U = some n ∧ VRR ρ₀ (CE E) U (shp U) ((ws.drop o).take n) Rk) →
      VRR ρ₀ (CE E) T (shp T) ws (Res.sum Rs) := by
  induction hA with
  | @atom t _ =>
      intro ws Rs hwc hl h
      match Rs, hl with
      | [R], _ =>
        obtain ⟨n, hn, hv⟩ := h 0 0 t R rfl rfl
        rw [hwc] at hn; obtain rfl := Option.some.inj hn
        simpa [Res.sum] using hv
  | @prod a b A B us ha hA0 hB0 iha ihb =>
      intro ws Rs hwc hl h
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hwc
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      simp only [List.length_append, List.length_map] at hl
      have hva := iha (Rs.take A.length) (by rw [hla]; exact hwa) (by simp; omega) fun k o U Rk hk hRk => by
        have hkA : k < A.length := by
          rcases Nat.lt_or_ge k A.length with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none h1] at hk; cases hk
        have hk' : (A ++ B.map (TermPiece.sh (nWords us)))[k]? = some (o, U) := by
          rw [List.getElem?_append_left hkA]; exact hk
        have hRk' : Rs[k]? = some Rk := by rw [List.getElem?_take_of_lt hkA] at hRk; exact hRk
        obtain ⟨n, hn, hv⟩ := h k o U Rk hk' hRk'
        obtain ⟨n', hn', hon⟩ := AtomL_bound hA0 hwa k o U hk
        rw [hn] at hn'; obtain rfl := Option.some.inj hn'
        refine ⟨n, hn, ?_⟩
        rw [take_drop_take hon]; exact hv
      have hvb := ihb (Rs.drop A.length) (by rw [hlb]; exact hwb) (by simp; omega) fun k o U Rk hk hRk => by
        have hkB : k < B.length := by
          rcases Nat.lt_or_ge k B.length with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none h1] at hk; cases hk
        have hk' : (A ++ B.map (TermPiece.sh (nWords us)))[A.length + k]? = some (nWords us + o, U) := by
          rw [List.getElem?_append_right (by omega), List.getElem?_map, Nat.add_sub_cancel_left, hk]; rfl
        have hRk' : Rs[A.length + k]? = some Rk := by rw [List.getElem?_drop] at hRk; exact hRk
        obtain ⟨n, hn, hv⟩ := h _ _ U Rk hk' hRk'
        refine ⟨n, hn, ?_⟩
        rw [drop_drop']; exact hv
      have e : ws = ws.take (nWords us) ++ ws.drop (nWords us) := (List.take_append_drop _ _).symm
      have hsum : Res.sum Rs = Res.sum (Rs.take A.length) + Res.sum (Rs.drop A.length) := by
        rw [← Res.sum_append, List.take_append_drop]
      rw [hsum]
      conv => arg 5; rw [e]
      exact VRR_prod_mk hva hvb hla hwa
  | @mu ρ W s L hW hg _ ih =>
      intro ws Rs hwc hl h
      have hv := ih Rs (by rw [wc_mu_unfold hg]; exact hwc) hl h
      rw [shp_mu_unfold hg] at hv
      exact (VRR_cl_unfold E hW hg).1 hv

theorem Valid_mu_unfold {ρ : Nat → Nat} {W : Nat → Ty} {s : Ty} (hg : s.unguarded 0 = false) {ws : List Word} :
    Valid (cl ρ W 0 0 (unfold1 (.mu s))) ws ↔ Valid (cl ρ W 0 0 (.mu s)) ws := by
  have e1 : cl ρ W 0 0 (.mu s) = .mu (cl ρ W 1 0 s) := rfl
  rw [e1]
  simp only [Valid]
  exact ⟨Valid_of_sig (sig_cl_unfold hg), Valid_of_sig (sig_cl_unfold hg).symm⟩

/-- `Valid` splits over the atoms. -/
theorem Valid_atoms {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {ws : List Word}, wc T = some ws.length → Valid T ws →
      ∀ (k o : Nat) (U : Ty), As[k]? = some (o, U) → ∃ n, wc U = some n ∧ Valid U ((ws.drop o).take n) := by
  induction hA with
  | @atom t _ =>
      intro ws hwc hv k o U hk
      cases k with
      | succ k => simp at hk
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨ws.length, hwc, by simpa using hv⟩
  | @prod a b A B us ha hA0 hB0 iha ihb =>
      intro ws hwc hv k o U hk
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hwc
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      simp only [Valid] at hv
      obtain ⟨hva, hvb⟩ := hv _ hwa
      rcases getElem?_atoms hk with ⟨-, hkA⟩ | ⟨-, ⟨o', U'⟩, hq, he⟩
      · obtain ⟨n, hn, hvn⟩ := iha (by rw [hla]; exact hwa) hva k o U hkA
        obtain ⟨n', hn', hon⟩ := AtomL_bound hA0 hwa k o U hkA
        rw [hn] at hn'; obtain rfl := Option.some.inj hn'
        refine ⟨n, hn, ?_⟩
        rw [take_drop_take hon] at hvn; exact hvn
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨n, hn, hvn⟩ := ihb (by rw [hlb]; exact hwb) hvb _ o' U hq
        refine ⟨n, hn, ?_⟩
        rw [drop_drop'] at hvn; exact hvn
  | @mu ρ W s L hW hg _ ih =>
      intro ws hwc hv
      exact ih (by rw [wc_mu_unfold hg]; exact hwc) ((Valid_mu_unfold hg).2 hv)

/-- `Valid` assembles from the atoms. -/
theorem Valid_of_atoms {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    ∀ {ws : List Word}, wc T = some ws.length →
      (∀ (k o : Nat) (U : Ty), As[k]? = some (o, U) → ∃ n, wc U = some n ∧ Valid U ((ws.drop o).take n)) →
      Valid T ws := by
  induction hA with
  | @atom t _ =>
      intro ws hwc h
      obtain ⟨n, hn, hv⟩ := h 0 0 t rfl
      rw [hwc] at hn; obtain rfl := Option.some.inj hn
      simpa using hv
  | @prod a b A B us ha hA0 hB0 iha ihb =>
      intro ws hwc h
      obtain ⟨ub, hb, hlen⟩ := wc_prod_split ha hwc
      have hwa : wc a = some (nWords us) := by simp [wc, ha]
      have hwb : wc b = some (nWords ub) := by simp [wc, hb]
      have hla : (ws.take (nWords us)).length = nWords us := by simp; omega
      have hlb : (ws.drop (nWords us)).length = nWords ub := by simp; omega
      simp only [Valid]
      intro n hn
      rw [hwa] at hn; obtain rfl := Option.some.inj hn
      refine ⟨iha (by rw [hla]; exact hwa) fun k o U hk => ?_, ihb (by rw [hlb]; exact hwb) fun k o U hk => ?_⟩
      · have hkA : k < A.length := by
          rcases Nat.lt_or_ge k A.length with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none h1] at hk; cases hk
        obtain ⟨m, hm, hv⟩ := h k o U (by rw [List.getElem?_append_left hkA]; exact hk)
        obtain ⟨m', hm', hon⟩ := AtomL_bound hA0 hwa k o U hk
        rw [hm] at hm'; obtain rfl := Option.some.inj hm'
        refine ⟨m, hm, ?_⟩
        rw [take_drop_take hon]; exact hv
      · have hkB : k < B.length := by
          rcases Nat.lt_or_ge k B.length with h1 | h1
          · exact h1
          · rw [List.getElem?_eq_none h1] at hk; cases hk
        have hk' : (A ++ B.map (TermPiece.sh (nWords us)))[A.length + k]? = some (nWords us + o, U) := by
          rw [List.getElem?_append_right (by omega), List.getElem?_map, Nat.add_sub_cancel_left, hk]; rfl
        obtain ⟨m, hm, hv⟩ := h _ _ U hk'
        refine ⟨m, hm, ?_⟩
        rw [drop_drop']; exact hv
  | @mu ρ W s L hW hg _ ih =>
      intro ws hwc h
      exact (Valid_mu_unfold hg).1 (ih (by rw [wc_mu_unfold hg]; exact hwc) h)

/-- **Block additivity for `ValOfR`**: a value of `T` holding `R` is exactly a list of values of its
atoms whose resources sum to `R`. -/
theorem ValOfR_atoms (η : TEnv) {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) {ws : List Word} {R : Res}
    (hwc : wc T = some ws.length) :
    ValOfR η T ws R ↔ ∃ Rs : List Res, Rs.length = As.length ∧ R = Res.sum Rs ∧
      ∀ (k o : Nat) (U : Ty) (Rk : Res), As[k]? = some (o, U) → Rs[k]? = some Rk →
        ∃ n, wc U = some n ∧ ValOfR η U ((ws.drop o).take n) Rk := by
  constructor
  · rintro ⟨hv, hV⟩
    obtain ⟨Rs, hl, hR, h⟩ := VRR_atoms η.unsee hA hwc hv
    refine ⟨Rs, hl, hR, fun k o U Rk hk hRk => ?_⟩
    obtain ⟨n, hn, -, hvn⟩ := h k o U Rk hk hRk
    obtain ⟨n', hn', hVn⟩ := Valid_atoms hA hwc hV k o U hk
    rw [hn] at hn'; obtain rfl := Option.some.inj hn'
    exact ⟨n, hn, hvn, hVn⟩
  · rintro ⟨Rs, hl, rfl, h⟩
    refine ⟨VRR_of_atoms η.unsee hA Rs hwc hl fun k o U Rk hk hRk => ?_, Valid_of_atoms hA hwc fun k o U hk => ?_⟩
    · obtain ⟨n, hn, hv⟩ := h k o U Rk hk hRk
      exact ⟨n, hn, hv.1⟩
    · have hkl : k < Rs.length := by
        rw [hl]
        rcases Nat.lt_or_ge k As.length with h1 | h1
        · exact h1
        · rw [List.getElem?_eq_none h1] at hk; cases hk
      obtain ⟨n, hn, hv⟩ := h k o U Rs[k] hk (List.getElem?_eq_getElem hkl)
      exact ⟨n, hn, hv.2⟩

/-- Every atom is a laid-out component (`AtOff`) of the type, and atomic. -/
theorem AtomL_atOff {T : Ty} {As : List (Nat × Ty)} (hA : AtomL T As) :
    accs T ≠ none → ∀ (k o : Nat) (U : Ty), As[k]? = some (o, U) → AtOff T o U ∧ AtomT U := by
  induction hA with
  | @atom t ht =>
      intro hn k o U hk
      cases k with
      | succ k => simp at hk
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact ⟨.here (Or.inl hn), ht⟩
  | @prod a b A B us ha _ _ iha ihb =>
      intro hn k o U hk
      have hnb : accs b ≠ none := by
        intro h; apply hn; simp [accs, h]
      rcases getElem?_atoms hk with ⟨-, hkA⟩ | ⟨-, ⟨o', U'⟩, hq, he⟩
      · obtain ⟨h1, h2⟩ := iha (by rw [ha]; simp) k o U hkA
        exact ⟨.fst h1, h2⟩
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨h1, h2⟩ := ihb hnb _ o' U hq
        exact ⟨.snd ha h1, h2⟩
  | @mu ρ W s L hW hg _ ih =>
      intro hn k o U hk
      obtain ⟨h1, h2⟩ := ih (by rw [accs_cl_unfold_eq hW hg]; exact hn) k o U hk
      exact ⟨.mu hW hg h1, h2⟩

/-- The atoms of a laid-out type with a `μ`-free pair skeleton. -/
theorem atomL_exists (e : Ty) (hs : TermBlkZ.SkFree e = true) (hn : accs e ≠ none) : ∃ As, AtomL e As := by
  induction e with
  | prod a b iha ihb =>
    simp only [TermBlkZ.SkFree, Bool.and_eq_true] at hs
    have hna : accs a ≠ none := by
      intro h; apply hn; simp [accs, h]
    have hnb : accs b ≠ none := by
      intro h; apply hn; simp [accs, h]
    obtain ⟨ua, hua⟩ := Option.ne_none_iff_exists'.1 hna
    obtain ⟨A, hA⟩ := iha hs.1 hna
    obtain ⟨B, hB⟩ := ihb hs.2 hnb
    exact ⟨_, .prod hua hA hB⟩
  | mu t _ => simp [TermBlkZ.SkFree] at hs
  | _ => exact ⟨_, .atom ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩⟩

/-- The atoms of a closed laid-out type whose `μ` bodies are guarded (`mg`), by induction on the
skeleton size (a guarded unfolding keeps it; `TermBlkZ.zwl_existsM`'s descent). -/
theorem atomL_existsM : ∀ (n : Nat) (e : Ty), TermBlkZ.skN e < n → Clo e → mg e = true → accs e ≠ none →
    ∃ As, AtomL e As
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, e, hn, hc, hm, hne => by
    cases e with
    | prod a b =>
      simp only [TermBlkZ.skN] at hn
      simp only [mg, Bool.and_eq_true] at hm
      obtain ⟨hca, hcb⟩ := TermBlkZ.Clo_prod hc
      have hna : accs a ≠ none := by
        intro h; apply hne; simp [accs, h]
      have hnb : accs b ≠ none := by
        intro h; apply hne; simp [accs, h]
      obtain ⟨ua, hua⟩ := Option.ne_none_iff_exists'.1 hna
      obtain ⟨A, hA⟩ := atomL_existsM n a (by omega) hca hm.1 hna
      obtain ⟨B, hB⟩ := atomL_existsM n b (by omega) hcb hm.2 hnb
      exact ⟨_, .prod hua hA hB⟩
    | mu s =>
      have hm0 := hm
      simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hcU, haU, -⟩ := TermBlkZ.mu_unfold_facts hc hm.1
      have hsk : TermBlkZ.skN (unfold1 (.mu s)) < n := by
        show TermBlkZ.skN (Ty.substT 0 (.mu s) s) < n
        rw [TermBlkZ.skN_substT s 0 _ hm.1]; simp only [TermBlkZ.skN] at hn; omega
      obtain ⟨L, hL⟩ := atomL_existsM n _ hsk hcU (mg_unfold1 hm0) (by rw [haU]; exact hne)
      have hW : ∀ k : Nat, Clo ((fun _ : Nat => Ty.void) k) := fun _ => Clo_void
      have hU : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (unfold1 (.mu s)) = unfold1 (.mu s) := by
        rw [TermStep.cl_unfold1 hW, hc.2]
      have hM : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (.mu s) = .mu s := hc.2 _ _ _ _
      have h1 := AtomL.mu (ρ := fun _ : Nat => 0) (W := fun _ : Nat => Ty.void) (s := s) hW hm.1 (by rw [hU]; exact hL)
      rw [hM] at h1
      exact ⟨L, h1⟩
    | _ => exact ⟨_, .atom ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩⟩

/-- The atoms, for a `μ`-free skeleton or a closed guarded type (`TermBlkZ.zwl_existsG`'s cases). -/
theorem atomL_existsG (e : Ty) (hs : TermBlkZ.SkFree e = true ∨ (Clo e ∧ mg e = true)) (hn : accs e ≠ none) :
    ∃ As, AtomL e As := by
  rcases hs with hs | ⟨hc, hm⟩
  · exact atomL_exists e hs hn
  · exact atomL_existsM (TermBlkZ.skN e + 1) e (Nat.lt_succ_self _) hc hm hn

end TermPinAtoms

#print axioms TermPinAtoms.AtomL_bound
#print axioms TermPinAtoms.VRR_atoms
#print axioms TermPinAtoms.VRR_of_atoms
#print axioms TermPinAtoms.Valid_atoms
#print axioms TermPinAtoms.Valid_of_atoms
#print axioms TermPinAtoms.ValOfR_atoms
#print axioms TermPinAtoms.AtomL_atOff
#print axioms TermPinAtoms.atomL_existsG

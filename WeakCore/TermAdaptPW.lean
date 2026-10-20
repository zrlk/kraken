import WeakCore.TermCntEmb

/-!
# TermAdaptPW: `adapt` is invisible to counted words (K1a, for the `fulCntR_of`)

At a closing `cl ρ W 0 0`, `adapt r` only turns `own` reference modes into `rgn (lit n)` modes
(`mr_cl_adapt`), and every layout reading (`info`, `accs`, `wc`, `sNo`, `lnorm`, `armsOf`,
`pubWords`, `pubArm`) ignores a reference's mode (`MR`).
-/

namespace TermAdaptPW
open CoreLang CoreTerm CoreTyping TermRun TermTv TermSound TermMem TermStep TermPtrRts TermCntLoc
open TermClose (cl clM clI Clo)

/-- Types equal up to `own` ↦ `rgn (lit n)` at reference modes. -/
inductive MR : Ty → Ty → Prop
  | refl (t : Ty) : MR t t
  | ptr (n : Nat) (t : Ty) : MR (.ptr .own t) (.ptr (.rgn (.lit n)) t)
  | ptrOpt (n : Nat) (t : Ty) : MR (.ptrOpt .own t) (.ptrOpt (.rgn (.lit n)) t)
  | loc (n : Nat) (t : Ty) : MR (.loc .own t) (.loc (.rgn (.lit n)) t)
  | prod {a a' b b' : Ty} : MR a a' → MR b b' → MR (.prod a b) (.prod a' b')
  | sum {a a' b b' : Ty} : MR a a' → MR b b' → MR (.sum a b) (.sum a' b')
  | array (i : Idx) {t t' : Ty} : MR t t' → MR (.array i t) (.array i t')
  | iex {t t' : Ty} : MR t t' → MR (.iex t) (.iex t')
  | iall {t t' : Ty} : MR t t' → MR (.iall t) (.iall t')
  | mu {t t' : Ty} : MR t t' → MR (.mu t) (.mu t')
  | tex (κ : Kind) {t t' : Ty} : MR t t' → MR (.tex κ t) (.tex κ t')
  | refine (ψ : Pred) {t t' : Ty} : MR t t' → MR (.refine t ψ) (.refine t' ψ)

/-! ## Closing an `adapt` -/

theorem clI_lit (ρ : Nat → Nat) : ∀ (r : Idx) (d : Nat), (∀ k, k < d → r.mentions k = false) →
    ∃ n, clI ρ d r = .lit n := by
  intro r
  induction r with
  | lit n => intro d _; exact ⟨n, rfl⟩
  | var j =>
    intro d h
    have hj : ¬ j < d := fun hj => by have := h j hj; simp [Idx.mentions] at this
    exact ⟨ρ (j - d), by simp [clI, hj]⟩
  | add i j ihi ihj =>
    intro d h
    obtain ⟨a, ha⟩ := ihi d (fun k hk => by have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.1)
    obtain ⟨b, hb⟩ := ihj d (fun k hk => by have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.2)
    exact ⟨a + b, by simp only [clI, ha, hb, TermClose.addF]⟩
  | sub i j ihi ihj =>
    intro d h
    obtain ⟨a, ha⟩ := ihi d (fun k hk => by have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.1)
    obtain ⟨b, hb⟩ := ihj d (fun k hk => by have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.2)
    exact ⟨a - b, by simp only [clI, ha, hb, TermClose.subF]⟩
  | smul m i ih =>
    intro d h
    obtain ⟨a, ha⟩ := ih d (fun k hk => by have := h k hk; simp only [Idx.mentions] at this; exact this)
    exact ⟨m * a, by simp only [clI, ha, TermClose.smulF]⟩

theorem mentions_shift0 : ∀ (r : Idx) (d : Nat), (∀ k, k < d → r.mentions k = false) →
    ∀ k, k < d + 1 → (r.shift 0).mentions k = false := by
  intro r
  induction r with
  | lit n => intro _ _ _ _; rfl
  | var j =>
    intro d h k hk
    simp only [Idx.shift, Nat.zero_le, ge_iff_le, ↓reduceIte, Idx.mentions, beq_eq_false_iff_ne]
    intro e
    have := h j (by omega)
    simp [Idx.mentions] at this
  | add i j ihi ihj =>
    intro d h k hk
    simp only [Idx.shift, Idx.mentions, Bool.or_eq_false_iff]
    refine ⟨ihi d (fun k hk => ?_) k hk, ihj d (fun k hk => ?_) k hk⟩
    · have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.1
    · have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.2
  | sub i j ihi ihj =>
    intro d h k hk
    simp only [Idx.shift, Idx.mentions, Bool.or_eq_false_iff]
    refine ⟨ihi d (fun k hk => ?_) k hk, ihj d (fun k hk => ?_) k hk⟩
    · have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.1
    · have := h k hk; simp only [Idx.mentions, Bool.or_eq_false_iff] at this; exact this.2
  | smul m i ih =>
    intro d h k hk
    simp only [Idx.shift, Idx.mentions]
    exact ih d (fun k hk => by have := h k hk; simp only [Idx.mentions] at this; exact this) k hk

/-- **Closing an `adapt`** (at a region index closed by the closing) relates by `MR`. -/
theorem mr_cl_adapt (ρ : Nat → Nat) (W : Nat → Ty) : ∀ (u : Ty) (r : Idx) (c d : Nat),
    (∀ k, k < d → r.mentions k = false) → MR (cl ρ W c d u) (cl ρ W c d (adapt r u)) := by
  intro u
  induction u with
  | ptr μ t _ =>
    intro r c d h
    cases μ with
    | own =>
      obtain ⟨n, hn⟩ := clI_lit ρ r d h
      simp only [adapt, cl, clM, hn]
      exact MR.ptr n _
    | pub => exact MR.refl _
    | rgn _ => exact MR.refl _
  | ptrOpt μ t _ =>
    intro r c d h
    cases μ with
    | own =>
      obtain ⟨n, hn⟩ := clI_lit ρ r d h
      simp only [adapt, cl, clM, hn]
      exact MR.ptrOpt n _
    | pub => exact MR.refl _
    | rgn _ => exact MR.refl _
  | loc μ t _ =>
    intro r c d h
    cases μ with
    | own =>
      obtain ⟨n, hn⟩ := clI_lit ρ r d h
      simp only [adapt, cl, clM, hn]
      exact MR.loc n _
    | pub => exact MR.refl _
    | rgn _ => exact MR.refl _
  | prod a b iha ihb => intro r c d h; simp only [adapt, cl]; exact MR.prod (iha r c d h) (ihb r c d h)
  | sum a b iha ihb => intro r c d h; simp only [adapt, cl]; exact MR.sum (iha r c d h) (ihb r c d h)
  | array i t ih => intro r c d h; simp only [adapt, cl]; exact MR.array _ (ih r c d h)
  | iex t ih =>
    intro r c d h; simp only [adapt, cl]; exact MR.iex (ih (r.shift 0) c (d + 1) (mentions_shift0 r d h))
  | iall t ih =>
    intro r c d h; simp only [adapt, cl]; exact MR.iall (ih (r.shift 0) c (d + 1) (mentions_shift0 r d h))
  | mu t ih => intro r c d h; simp only [adapt, cl]; exact MR.mu (ih r (c + 1) d h)
  | tex κ t ih => intro r c d h; simp only [adapt, cl]; exact MR.tex κ (ih r (c + 1) d h)
  | refine t ψ ih => intro r c d h; simp only [adapt, cl]; exact MR.refine _ (ih r c d h)
  | _ => intro r c d _; exact MR.refl _

/-! ## Readings that ignore reference modes -/

theorem mr_idx {t t' : Ty} (h : MR t t') : ∀ k, t.idxMentions k = t'.idxMentions k := by
  induction h with
  | refl => intro k; rfl
  | ptr | ptrOpt | loc => intro k; simp [Ty.idxMentions, Mode.mentions, Idx.mentions]
  | prod _ _ iha ihb | sum _ _ iha ihb => intro k; simp only [Ty.idxMentions, iha, ihb]
  | array _ _ ih | refine _ _ ih | mu _ ih | tex _ _ ih => intro k; simp only [Ty.idxMentions, ih]
  | iex _ ih | iall _ ih => intro k; simp only [Ty.idxMentions, ih]

theorem mr_ty {t t' : Ty} (h : MR t t') : ∀ k, t.tyMentions k = t'.tyMentions k := by
  induction h with
  | refl => intro k; rfl
  | ptr | ptrOpt | loc => intro k; simp [Ty.tyMentions]
  | prod _ _ iha ihb | sum _ _ iha ihb => intro k; simp only [Ty.tyMentions, iha, ihb]
  | array _ _ ih | refine _ _ ih | mu _ ih | tex _ _ ih => intro k; simp only [Ty.tyMentions, ih]
  | iex _ ih | iall _ ih => intro k; simp only [Ty.tyMentions, ih]

theorem mr_countT {t t' : Ty} (h : MR t t') : ∀ k, t.countT k = t'.countT k := by
  induction h with
  | refl => intro k; rfl
  | ptr | ptrOpt | loc => intro k; rfl
  | prod _ _ iha ihb => intro k; simp only [Ty.countT, iha, ihb]
  | sum ha hb _ _ => intro k; simp only [Ty.countT, mr_ty (MR.sum ha hb)]
  | array i ha _ => intro k; simp only [Ty.countT, mr_ty (MR.array i ha)]
  | refine _ _ ih | tex _ _ ih | iex _ ih | iall _ ih => intro k; simp only [Ty.countT, ih]
  | mu ha ih => intro k; simp only [Ty.countT, ih, mr_ty ha]

theorem mr_countI {t t' : Ty} (h : MR t t') : ∀ k, t.countI k = t'.countI k := by
  induction h with
  | refl => intro k; rfl
  | ptr | ptrOpt | loc => intro k; simp [Ty.countI, Ty.idxMentions, Mode.mentions, Idx.mentions]
  | prod _ _ iha ihb => intro k; simp only [Ty.countI, iha, ihb]
  | sum ha hb _ _ => intro k; simp only [Ty.countI, mr_idx (MR.sum ha hb)]
  | array i ha _ => intro k; simp only [Ty.countI, mr_idx (MR.array i ha)]
  | refine _ _ ih | tex _ _ ih | iex _ ih | iall _ ih => intro k; simp only [Ty.countI, ih]
  | mu ha ih => intro k; simp only [Ty.countI, ih, mr_idx ha, mr_countT ha]

theorem mr_info {t t' : Ty} (h : MR t t') : ∀ ρ, info ρ t = info ρ t' := by
  induction h with
  | refl => intro ρ; rfl
  | ptr | ptrOpt | loc => intro ρ; rfl
  | prod _ _ iha ihb | sum _ _ iha ihb => intro ρ; simp only [info, iha, ihb]
  | array => intro ρ; rfl
  | refine _ _ ih | tex _ _ ih | iex _ ih | iall _ ih | mu _ ih => intro ρ; simp only [info, ih]

theorem mr_tier {t t' : Ty} (h : MR t t') : t.tier = t'.tier := by
  simp only [Ty.tier, mr_info h]

theorem mr_rawWords {t t' : Ty} (h : MR t t') : t.rawWords = t'.rawWords := by
  simp only [Ty.rawWords, Ty.width, mr_info h]

theorem mr_accs {t t' : Ty} (h : MR t t') : accs t = accs t' := by
  induction h with
  | refl => rfl
  | ptr | ptrOpt | loc => rfl
  | prod _ _ iha ihb => simp only [accs, iha, ihb]
  | sum ha hb _ _ => simp only [accs, mr_tier (MR.sum ha hb)]
  | array => rfl
  | refine _ _ ih | iall _ ih | mu _ ih => simp only [accs, ih]
  | iex ha ih => simp only [accs, ih, mr_countI ha, mr_rawWords (MR.iex ha)]
  | tex κ ha ih => simp only [accs, ih, mr_countT ha, mr_rawWords (MR.tex κ ha)]

theorem mr_wc {t t' : Ty} (h : MR t t') : wc t = wc t' := by
  simp only [wc, mr_accs h]

theorem mr_sNo {t t' : Ty} (h : MR t t') : sNo t = sNo t' := by
  induction h with
  | refl => rfl
  | ptr | ptrOpt | loc => rfl
  | prod _ _ iha ihb | sum _ _ iha ihb => simp only [sNo, iha, ihb]
  | array _ _ ih | refine _ _ ih | iex _ ih | iall _ ih | mu _ ih | tex _ _ ih => simp only [sNo, ih]

theorem mr_lnorm {t t' : Ty} (h : MR t t') : lnorm t = lnorm t' := by
  induction h with
  | refl => rfl
  | ptr | ptrOpt | loc => rfl
  | prod _ _ iha ihb | sum _ _ iha ihb => simp only [lnorm, iha, ihb]
  | array => rfl
  | refine _ _ ih | iex _ ih | iall _ ih | mu _ ih | tex _ _ ih => simp only [lnorm, ih]

theorem mr_armsLen {t t' : Ty} (h : MR t t') : (armsOf t).length = (armsOf t').length := by
  induction h with
  | refl => rfl
  | ptr | ptrOpt | loc => rfl
  | prod => rfl
  | sum _ _ iha ihb => simp only [armsOf, List.length_append, iha, ihb]
  | array => rfl
  | refine _ _ ih | iex _ ih | iall _ ih | mu _ ih | tex _ _ ih => simp only [armsOf]; exact ih

theorem mr_pub {t t' : Ty} (h : MR t t') :
    (∀ ws, pubWords t ws = pubWords t' ws) ∧ (∀ j p, pubArm t j p = pubArm t' j p) := by
  induction h with
  | refl => exact ⟨fun _ => rfl, fun _ _ => rfl⟩
  | ptr | ptrOpt | loc =>
    exact ⟨fun ws => by simp [pubWords, sNo, mPub], fun j p => by simp [pubArm, pubWords, sNo, mPub]⟩
  | @prod a a2 b b2 ha hb iha ihb =>
    have hs := mr_sNo (MR.prod ha hb)
    have hw := mr_wc ha
    have h1 : ∀ ws, pubWords (.prod a b) ws = pubWords (.prod a2 b2) ws := by
      intro ws
      simp only [pubWords, hs, hw, iha.1, ihb.1]
    exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | sum ha hb iha ihb =>
    have hs := mr_sNo (MR.sum ha hb)
    have ht := mr_tier (MR.sum ha hb)
    have hl := mr_lnorm (MR.sum ha hb)
    have hal := mr_armsLen ha
    refine ⟨fun ws => ?_, fun j p => ?_⟩
    · simp only [pubWords, hs, ht, hl, hal, iha.2, ihb.2]
    · simp only [pubArm, hal, iha.2, ihb.2]
  | @array i e e2 ha _ =>
    have hs := mr_sNo (MR.array i ha)
    have h1 : ∀ ws, pubWords (.array i e) ws = pubWords (.array i e2) ws := by
      intro ws
      rw [pubWords.eq_def, pubWords.eq_def]
      simp only [hs]
    exact ⟨h1, fun j p => by simp only [pubArm]; exact h1 p⟩
  | refine ψ ha ih =>
    have hs := mr_sNo (MR.refine ψ ha)
    exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | iex ha ih =>
    have hs := mr_sNo (MR.iex ha)
    exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | iall ha ih =>
    have hs := mr_sNo (MR.iall ha)
    exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | mu ha ih =>
    have hs := mr_sNo (MR.mu ha)
    exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩
  | tex κ ha ih =>
    have hs := mr_sNo (MR.tex κ ha)
    exact ⟨fun ws => by simp only [pubWords, hs, ih.1], fun j p => by simp only [pubArm, ih.2]⟩

/-! ## The adapters -/

/-- **`adapt` keeps counted words** (at a closing that closes the region index). -/
theorem pubWords_cl_adaptG (u : Ty) (r : Idx) (ρ : Nat → Nat) (W : Nat → Ty) (c d : Nat)
    (hr : ∀ k, k < d → r.mentions k = false) :
    (∀ L, pubWords (cl ρ W c d (adapt r u)) L = pubWords (cl ρ W c d u) L) ∧
    (∀ j p, pubArm (cl ρ W c d (adapt r u)) j p = pubArm (cl ρ W c d u) j p) ∧
    wc (cl ρ W c d (adapt r u)) = wc (cl ρ W c d u) := by
  have h := mr_cl_adapt ρ W u r c d hr
  exact ⟨fun L => ((mr_pub h).1 L).symm, fun j p => ((mr_pub h).2 j p).symm, (mr_wc h).symm⟩

/-- **The form** (`fulCntR_of`): at `cl ρ W 0 0`, `adapt` keeps counted words and the word count. -/
theorem pubWords_cl_adapt0 (u : Ty) (r : Idx) (ρ : Nat → Nat) (W : Nat → Ty) :
    (∀ L, pubWords (cl ρ W 0 0 (adapt r u)) L = pubWords (cl ρ W 0 0 u) L) ∧
    wc (cl ρ W 0 0 (adapt r u)) = wc (cl ρ W 0 0 u) := by
  have h := pubWords_cl_adaptG u r ρ W 0 0 (fun k hk => absurd hk (Nat.not_lt_zero k))
  exact ⟨h.1, h.2.2⟩

end TermAdaptPW

#print axioms TermAdaptPW.pubWords_cl_adaptG
#print axioms TermAdaptPW.pubWords_cl_adapt0

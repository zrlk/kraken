import WeakCore.TermPaid

/-!
# TermBlkZ: the designated debit of a resource-free slot

(H) producer: at a buffer slot whose value (on its units' first writes) holds nothing,
and whose element type has a `μ`-free skeleton (`SkFree`), the non-word part of a
designated debit (`BlkDb`) is `.zero`.
-/

namespace TermBlkZ

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep
open WeakMem (Msg Memory Address Ts AllocLabel)

/-- A type whose pair skeleton has no `μ` (pairs descend; `μ` is excluded; anything else
is an atom of the skeleton). -/
def SkFree : Ty → Bool
  | .prod a b => SkFree a && SkFree b
  | .mu _ => false
  | _ => true

theorem atom_case {e : Ty} (ha : AtomT e) (hn : accs e ≠ none) :
    ∃ Us : List Ty, ZwL e Us ∧ ∀ U ∈ Us, ∃ o, AtOff e o U ∧ wc U = some 0 := by
  obtain ⟨us, hus⟩ := Option.ne_none_iff_exists'.1 hn
  have hw := wc_of_accs hus
  cases hk : nWords us with
  | zero =>
    rw [hk] at hw
    refine ⟨[e], .zero ha hw, fun U hU => ?_⟩
    simp only [List.mem_singleton] at hU; subst hU
    exact ⟨0, .here (Or.inl hn), hw⟩
  | succ n =>
    rw [hk] at hw
    exact ⟨[], .pos ha hw, fun U hU => by simp at hU⟩

theorem zwl_exists (e : Ty) (hs : SkFree e = true) (hn : accs e ≠ none) :
    ∃ Us : List Ty, ZwL e Us ∧ ∀ U ∈ Us, ∃ o, AtOff e o U ∧ wc U = some 0 := by
  induction e with
  | prod a b iha ihb =>
    simp only [SkFree, Bool.and_eq_true] at hs
    have hna : accs a ≠ none := by
      intro h; apply hn; simp [accs, h]
    have hnb : accs b ≠ none := by
      intro h; apply hn; simp [accs, h]
    obtain ⟨ua, hua⟩ := Option.ne_none_iff_exists'.1 hna
    obtain ⟨A, hA, hA2⟩ := iha hs.1 hna
    obtain ⟨B, hB, hB2⟩ := ihb hs.2 hnb
    refine ⟨A ++ B, .prod hA hB, fun U hU => ?_⟩
    rcases List.mem_append.1 hU with h | h
    · obtain ⟨o, ho, hw⟩ := hA2 U h; exact ⟨o, .fst ho, hw⟩
    · obtain ⟨o, ho, hw⟩ := hB2 U h; exact ⟨_, .snd hua ho, hw⟩
  | mu t _ => simp [SkFree] at hs
  | _ => exact atom_case ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩ hn

/-- The size of a type's pair-and-`μ` skeleton. -/
def skN : Ty → Nat
  | .prod a b => skN a + skN b + 1
  | .mu t => skN t + 1
  | _ => 0

/-- Substituting at a guarded variable keeps the skeleton. -/
theorem skN_substT (t : Ty) : ∀ (j : Nat) (s : Ty), t.unguarded j = false → skN (Ty.substT j s t) = skN t := by
  induction t with
  | tvar k =>
    intro j s h
    simp only [Ty.unguarded, beq_eq_false_iff_ne, ne_eq] at h
    simp only [Ty.substT, beq_iff_eq, h, ite_false]
    split <;> rfl
  | prod a b iha ihb =>
    intro j s h
    simp only [Ty.unguarded, Bool.or_eq_false_iff] at h
    simp only [Ty.substT, skN, iha j s h.1, ihb j s h.2]
  | mu t ih =>
    intro j s h
    simp only [Ty.unguarded] at h
    simp only [Ty.substT, skN, ih (j + 1) _ h]
  | _ => intros; simp [Ty.substT, skN]

theorem Clo_prod {a b : Ty} (h : Clo (.prod a b)) : Clo a ∧ Clo b := by
  have h1 := h.1
  simp only [tb, Bool.and_eq_true] at h1
  refine ⟨⟨h1.1, fun ρ W e f => ?_⟩, ⟨h1.2, fun ρ W e f => ?_⟩⟩
  · have := h.2 ρ W e f; simp only [cl, Ty.prod.injEq] at this; exact this.1
  · have := h.2 ρ W e f; simp only [cl, Ty.prod.injEq] at this; exact this.2

/-- A closed guarded `μ`: its unfolding is closed, has its layout, and its components are its own. -/
theorem mu_unfold_facts {s : Ty} (hc : Clo (.mu s)) (hg : s.unguarded 0 = false) :
    Clo (unfold1 (.mu s)) ∧ accs (unfold1 (.mu s)) = accs (.mu s) ∧
      ∀ o U, AtOff (unfold1 (.mu s)) o U → AtOff (.mu s) o U := by
  have hW : ∀ k : Nat, Clo ((fun _ : Nat => Ty.void) k) := fun _ => Clo_void
  have hU : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (unfold1 (.mu s)) = unfold1 (.mu s) := by
    rw [TermStep.cl_unfold1 hW, hc.2]
  have hM : cl (fun _ : Nat => 0) (fun _ : Nat => Ty.void) 0 0 (.mu s) = .mu s := hc.2 _ _ _ _
  refine ⟨?_, ?_, fun o U h => ?_⟩
  · have := Clo_cl hW (fun _ : Nat => 0) (unfold1 (.mu s)); rwa [hU] at this
  · have := TermStep.accs_cl_unfold_eq (ρ := fun _ : Nat => 0) hW hg; rwa [hU, hM] at this
  · have := AtOff.mu (ρ := fun _ : Nat => 0) (W := fun _ : Nat => Ty.void) (s := s) hW hg (by rw [hU]; exact h)
    rwa [hM] at this

/-- (R2) **Zero-width components of a closed type whose `μ` bodies are guarded** (`mg`), by
induction on the skeleton size (a guarded unfolding keeps it). -/
theorem zwl_existsM : ∀ (n : Nat) (e : Ty), skN e < n → Clo e → mg e = true → accs e ≠ none →
    ∃ Us : List Ty, ZwL e Us ∧ ∀ U ∈ Us, ∃ o, AtOff e o U ∧ wc U = some 0
  | 0, _, h, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, e, hn, hc, hm, hne => by
    cases e with
    | prod a b =>
      simp only [skN] at hn
      simp only [mg, Bool.and_eq_true] at hm
      obtain ⟨hca, hcb⟩ := Clo_prod hc
      have hna : accs a ≠ none := by
        intro h; apply hne; simp [accs, h]
      have hnb : accs b ≠ none := by
        intro h; apply hne; simp [accs, h]
      obtain ⟨ua, hua⟩ := Option.ne_none_iff_exists'.1 hna
      obtain ⟨A, hA, hA2⟩ := zwl_existsM n a (by omega) hca hm.1 hna
      obtain ⟨B, hB, hB2⟩ := zwl_existsM n b (by omega) hcb hm.2 hnb
      refine ⟨A ++ B, .prod hA hB, fun U hU => ?_⟩
      rcases List.mem_append.1 hU with h | h
      · obtain ⟨o, ho, hw⟩ := hA2 U h; exact ⟨o, .fst ho, hw⟩
      · obtain ⟨o, ho, hw⟩ := hB2 U h; exact ⟨_, .snd hua ho, hw⟩
    | mu s =>
      have hm0 := hm
      simp only [mg, Bool.and_eq_true, Bool.not_eq_true'] at hm
      obtain ⟨hcU, haU, hat⟩ := mu_unfold_facts hc hm.1
      have hsk : skN (unfold1 (.mu s)) < n := by
        show skN (Ty.substT 0 (.mu s) s) < n
        rw [skN_substT s 0 _ hm.1]; simp only [skN] at hn; omega
      obtain ⟨Us, hZ, hZ2⟩ := zwl_existsM n _ hsk hcU (mg_unfold1 hm0) (by rw [haU]; exact hne)
      refine ⟨Us, .mu hZ, fun U hU => ?_⟩
      obtain ⟨o, ho, hw⟩ := hZ2 U hU
      exact ⟨o, hat o U ho, hw⟩
    | _ => exact atom_case ⟨fun _ _ h => Ty.noConfusion h, fun _ h => Ty.noConfusion h⟩ hne

/-- (R2) The zero-width components, for a `μ`-free skeleton or a closed guarded type. -/
theorem zwl_existsG (e : Ty) (hs : SkFree e = true ∨ (Clo e ∧ mg e = true)) (hn : accs e ≠ none) :
    ∃ Us : List Ty, ZwL e Us ∧ ∀ U ∈ Us, ∃ o, AtOff e o U ∧ wc U = some 0 := by
  rcases hs with hs | ⟨hc, hm⟩
  · exact zwl_exists e hs hn
  · exact zwl_existsM (skN e + 1) e (Nat.lt_succ_self _) hc hm hn

theorem sum_map_zero {α : Type} (l : List α) : Res.sum (l.map fun _ => Res.zero) = Res.zero := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- (H) **The designated debit of a resource-free slot.**  At a buffer of literal length
whose element type has a `μ`-free skeleton, an address inside the buffer whose slot is a
value (on its units' first writes) holding nothing has a zero `BlkDb`. -/
theorem blkDb_zero_of {E : TEnv} {mem : Memory} {a : Address} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} (hc : E.sto a.label = some c) (hT : c.ty = .array (.lit N) e)
    (hu : accs e = some us) (hsk : SkFree e = true ∨ (Clo e ∧ mg e = true)) (hlt : a.offset < N * nWords us)
    (hslot : ∀ j, j < N → j * nWords us ≤ a.offset → a.offset < j * nWords us + nWords us →
      ∃ ws : List Word, ws.length = nWords us ∧
        (∀ i x, ws[i]? = some x → ∃ h m, FirstW mem ⟨a.label, j * nWords us + i⟩ h ∧
          mem[h]? = some m ∧ x = mw m) ∧
        ValOfR E e ws .zero) :
    BlkDb E mem a .zero := by
  have hwe := wc_of_accs hu
  -- the block part
  have hb : BlkZ E mem a .zero := by
    rcases Classical.em (∃ U, BlkStart E a U) with ⟨U, hB⟩ | hnB
    · left
      have hB0 := hB
      obtain ⟨c1, N1, e1, us1, j, o, w, hc1, hT1, hu1, -, hj, hoff, hat, -, hwU, hw0, -⟩ := hB0
      rw [hc] at hc1; cases hc1
      rw [hT] at hT1; cases hT1
      rw [hu] at hu1; cases hu1
      obtain ⟨uU, huU, hwU2⟩ := Option.map_eq_some_iff.1 hwU
      have hob := AtOff_bound hat hu huU
      obtain ⟨ws, hl, hfw, hv⟩ := hslot j hj (by rw [hoff]; omega)
        (by rw [hoff]; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (hwU2 ▸ hw0)) hob) _)
      obtain ⟨n, Rq, Rr, hn, hon, hR, hq, -⟩ := VRR_at E.unsee hat hv.1 (by rw [hwe, hl])
      rw [(Res.add_eq_zero hR.symm).1] at hq
      rw [hwU] at hn; cases hn
      refine ⟨U, w, (ws.drop o).take w, hB, hwU, by simp; omega, fun o1 x hx => ?_, E, fun _ _ h => h, hq⟩
      simp only [List.getElem?_take, List.getElem?_drop] at hx
      split at hx
      · obtain ⟨h, m, hF, hm, hx⟩ := hfw (o + o1) x hx
        refine ⟨h, m, ?_, hm, hx⟩
        rw [hoff, Nat.add_assoc]; exact hF
      · cases hx
    · exact Or.inr ⟨fun U h => hnB ⟨U, h⟩, rfl⟩
  -- the zero-width part
  have hz : ZwZ E a .zero := by
    rcases Classical.em (SlotStart E a) with hS | hnS
    · have hS0 := hS
      obtain ⟨c1, N1, e1, us1, hc1, hT1, hu1, hpos, -, hmod⟩ := hS0
      rw [hc] at hc1; cases hc1
      rw [hT] at hT1; cases hT1
      rw [hu] at hu1; cases hu1
      obtain ⟨Us, hZ, hZ2⟩ := zwl_existsG e hsk (by rw [hu]; simp)
      have hdm := Nat.div_add_mod a.offset (nWords us)
      rw [hmod, Nat.add_zero, Nat.mul_comm] at hdm
      have hjN : a.offset / nWords us < N := (Nat.div_lt_iff_lt_mul hpos).2 hlt
      obtain ⟨ws, hl, -, hv⟩ := hslot (a.offset / nWords us) hjN
        (Nat.le_of_eq hdm) (Nat.lt_of_le_of_lt (Nat.le_of_eq hdm.symm) (Nat.lt_add_of_pos_right hpos))
      refine Or.inl ⟨hS, c, N, e, us, Us, Us.map (fun _ => Res.zero), E, hc, hT, hu, hZ, by simp,
        (sum_map_zero Us).symm, fun _ _ h => h, fun i U Ri hU hRi => ?_⟩
      simp only [List.getElem?_map, hU, Option.map_some, Option.some.injEq] at hRi
      subst hRi
      obtain ⟨o, hat, hw0⟩ := hZ2 U (List.mem_of_getElem? hU)
      obtain ⟨n, Rq, Rr, hn, -, hR, hq, -⟩ := VRR_at E.unsee hat hv.1 (by rw [hwe, hl])
      rw [hw0] at hn; cases hn
      rw [(Res.add_eq_zero hR.symm).1] at hq
      simpa using hq
    · exact Or.inr ⟨hnS, rfl⟩
  exact ⟨.zero, .zero, hb, hz, Res.ext fun k => by cases k <;> simp [noOwnR]⟩

/-- First-write words: units with a first write give a word list read at them. -/
theorem fw_words {mem : Memory} {l : AllocLabel} : ∀ (n base : Nat),
    (∀ i, i < n → ∃ h, FirstW mem ⟨l, base + i⟩ h) →
    ∃ ws : List Word, ws.length = n ∧
      ∀ i x, ws[i]? = some x → ∃ h m, FirstW mem ⟨l, base + i⟩ h ∧ mem[h]? = some m ∧ x = mw m
  | 0, _, _ => ⟨[], rfl, fun _ _ hx => by simp at hx⟩
  | n + 1, base, hf => by
    obtain ⟨h, hF⟩ := hf 0 (Nat.zero_lt_succ _)
    obtain ⟨m, hm, -, -⟩ := hF.1
    obtain ⟨ws, hl, hw⟩ := fw_words n (base + 1) fun i hi => by
      obtain ⟨h1, h1F⟩ := hf (i + 1) (Nat.succ_lt_succ hi)
      exact ⟨h1, by rw [Nat.add_assoc, Nat.add_comm 1 i]; exact h1F⟩
    refine ⟨mw m :: ws, by simp [hl], fun i x hx => ?_⟩
    cases i with
    | zero => simp at hx; exact ⟨h, m, hF, hm, hx.symm⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hx
      obtain ⟨h1, m1, h1F, h1m, hx1⟩ := hw i x hx
      refine ⟨h1, m1, ?_, h1m, hx1⟩
      have e : base + (i + 1) = base + 1 + i := by omega
      rw [show i.succ = i + 1 from rfl, e]; exact h1F

/-- (H) **The designated debit of a resource-free slot** (the form the raise uses): every
unit of the slot has a first write, and any word list read at them is a value holding
nothing. -/
theorem blkDb_zero {E : TEnv} {mem : Memory} {a : Address} {c : Cell} {N : Nat} {e : Ty}
    {us : List Acc} (hc : E.sto a.label = some c) (hT : c.ty = .array (.lit N) e)
    (hu : accs e = some us) (hsk : SkFree e = true ∨ (Clo e ∧ mg e = true)) (hlt : a.offset < N * nWords us)
    (hfw : ∀ j, j < N → j * nWords us ≤ a.offset → a.offset < j * nWords us + nWords us →
      ∀ i, i < nWords us → ∃ h, FirstW mem ⟨a.label, j * nWords us + i⟩ h)
    (hval : ∀ j, j < N → j * nWords us ≤ a.offset → a.offset < j * nWords us + nWords us →
      ∀ ws : List Word, ws.length = nWords us →
        (∀ i x, ws[i]? = some x → ∃ h m, FirstW mem ⟨a.label, j * nWords us + i⟩ h ∧
          mem[h]? = some m ∧ x = mw m) →
        ValOfR E e ws .zero) :
    BlkDb E mem a .zero :=
  blkDb_zero_of hc hT hu hsk hlt fun j hj h1 h2 => by
    obtain ⟨ws, hl, hw⟩ := fw_words (nWords us) (j * nWords us) (hfw j hj h1 h2)
    exact ⟨ws, hl, hw, hval j hj h1 h2 ws hl hw⟩

/-! ## (R1 groundwork) A value of an own-free type holds no own-handle key -/

theorem push0_rrs_own {η : TEnv} {s : Ty} {l : Nat} (hr : ∀ k S vs Y, η.rrs k S vs Y → Y (.own l) = 0) :
    ∀ k S vs Y, (η.push0 s).rrs k S vs Y → Y (.own l) = 0
  | 0, _, _, _, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | k + 1, S, vs, Y, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h; exact hr k S vs Y h

theorem push0_urrs_own {η : TEnv} {s : Ty} {l : Nat} (hr : ∀ k S vs Y, η.urrs k S vs Y → Y (.own l) = 0) :
    ∀ k S vs Y, (η.push0 s).urrs k S vs Y → Y (.own l) = 0
  | 0, _, _, _, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h
  | k + 1, S, vs, Y, h => by simp [TEnv.push0, TEnv.ins, TEnv.insR] at h; exact hr k S vs Y h

/-- **A value of an own-free type holds no own-handle key** (at environments whose type
variables denote own-free resources). -/
theorem VRR_own_zero (l : Nat) : ∀ (t : Ty) (ke : KEnv) (η : TEnv) (ρ : Nat → Nat) (rt : Shp) (ws : List Word)
    (X : Res), Ty.noOwnIn ke t = true →
    (∀ k S vs Y, η.rrs k S vs Y → Y (.own l) = 0) → (∀ k S vs Y, η.urrs k S vs Y → Y (.own l) = 0) →
    VRR ρ η t rt ws X → X (.own l) = 0
  | .tvar k, _, η, ρ, rt, ws, X, _, hr, _, hv => by
      simp only [VRR] at hv
      obtain ⟨w0, -, h1⟩ := hv; exact hr k rt _ X h1
  | .refine t ψ, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRR] at hv
      exact VRR_own_zero l t ke η ρ rt ws X hn hr hur hv.1
  | .iex b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRR] at hv
      obtain ⟨n, rb, w, -, h2⟩ := hv
      exact VRR_own_zero l b ke η (vcons w ρ) rb ws X hn hr hur h2
  | .prod a b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn, Bool.and_eq_true] at hn
      simp only [VRR] at hv
      obtain ⟨ra, rb, -, Ra, Rb, hR, hz, hf⟩ := hv
      cases hw : ra.wc with
      | none => rw [hz hw]; rfl
      | some n =>
        obtain ⟨-, e2, e3⟩ := hf n hw
        rw [hR, Res.add_apply, VRR_own_zero l a ke η ρ _ _ _ hn.1 hr hur e2,
          VRR_own_zero l b ke η ρ _ _ _ hn.2 hr hur e3]
  | .sum a b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn, Bool.and_eq_true] at hn
      simp only [VRR] at hv
      obtain ⟨n, Ra, Rb, -, ⟨-, x, s, B, -, -, -, -, -, -, hA, hA'⟩ | ⟨j, p, -, h2, h3⟩⟩ := hv
      · by_cases hj : B.tag - s < (armsOf Ra).length
        · cases hb : isBoxed Ra with
          | true => exact VRR_own_zero l a ke η ρ _ _ _ hn.1 hr hur ((hA hj).1 hb)
          | false =>
            obtain ⟨q, -, -, -, -, hv⟩ := (hA hj).2 hb
            exact VRR_own_zero l a ke η.unsee ρ _ _ _ hn.1 hur hur hv
        · have hj' : (armsOf Ra).length ≤ B.tag - s := Nat.le_of_not_lt hj
          cases hb : isBoxed Rb with
          | true => exact VRR_own_zero l b ke η ρ _ _ _ hn.2 hr hur ((hA' hj').1 hb)
          | false =>
            obtain ⟨q, -, -, -, -, hv⟩ := (hA' hj').2 hb
            exact VRR_own_zero l b ke η.unsee ρ _ _ _ hn.2 hur hur hv
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, -, hv⟩ := h2 hj
          exact VRR_own_zero l a ke η ρ _ _ _ hn.1 hr hur hv
        · obtain ⟨q, -, hv⟩ := h3 (Nat.le_of_not_lt hj)
          exact VRR_own_zero l b ke η ρ _ _ _ hn.2 hr hur hv
  | .code a b, _, η, ρ, rt, ws, X, _, _, _, hv => by
      simp only [VRR] at hv; rw [hv.2]; rfl
  | .tex κ b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn, Bool.and_eq_true] at hn
      simp only [VRR] at hv
      obtain ⟨n, rb, s, -, -, -, h3⟩ := hv
      exact VRR_own_zero l b (some κ :: ke) (η.push0 s) ρ rb ws X hn.2 (push0_rrs_own hr) (push0_urrs_own hur) h3
  | .ptr μ u, ke, η, ρ, rt, ws, X, hn, _, _, hv => by
      have hμ := noOwnIn_ptr_mode hn
      simp only [VRR] at hv
      rw [hv.2]
      cases μ with
      | own => exact absurd rfl hμ
      | _ => rfl
  | .ptrOpt μ u, ke, η, ρ, rt, ws, X, hn, _, _, hv => by
      have hμ := noOwnIn_ptrOpt_mode hn
      simp only [VRR] at hv
      rw [hv.2]
      cases μ with
      | own => exact absurd rfl hμ
      | _ => rfl
  | .loc μ u, ke, η, ρ, rt, ws, X, hn, _, _, hv => by
      have hμ := noOwnIn_loc_mode hn
      simp only [VRR] at hv
      rw [hv.2]
      cases μ with
      | own => exact absurd rfl hμ
      | _ => rfl
  | .mu b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRR] at hv
      exact VRR_own_zero l b (none :: ke) _ ρ rt ws X hn (push0_rrs_own hr) (push0_urrs_own hur) hv
  | .iall b, ke, η, ρ, rt, ws, X, hn, hr, hur, hv => by
      simp only [Ty.noOwnIn] at hn
      simp only [VRR] at hv
      exact VRR_own_zero l b ke η (vcons 0 ρ) rt ws X hn hr hur (hv 0)
  | .intS _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv.2]; rfl
  | .int, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv.2]; rfl
  | .fix _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv.2]; rfl
  | .lanes _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv.2]; rfl
  | .unit, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv]; rfl
  | .void, _, _, _, _, _, _, _, _, _, hv => by simp [VRR] at hv
  | .array _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv]; rfl
  | .share _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv]; rfl
  | .cap _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv]; rfl
  | .word _ _, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRR] at hv
      rcases hv.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [wdW] <;> split <;> rfl
  | .tok _ st, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRR] at hv; rw [hv]; cases st <;> simp
  | .word2 _ _, _, _, _, _, _, _, _, _, _, hv => by
      simp only [VRR] at hv
      rcases hv.2 with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp
  | .tok2 _ _ _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv]; rfl
  | .epair _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv.2]; rfl
  | .tokE _ _ _, _, _, _, _, _, _, _, _, _, hv => by simp only [VRR] at hv; rw [hv]; rfl

/-- **`noOwnR` is the identity on memory values of own-free types.** -/
theorem noOwnR_valOfR {E : TEnv} {T : Ty} {ws : List Word} {R : Res} (hT : Ty.noOwnIn [] T = true)
    (h : ValOfR E T ws R) : noOwnR R = R := by
  funext k
  cases k with
  | own l =>
    show 0 = R (.own l)
    exact (VRR_own_zero l T [] (CE E.unsee) (fun _ => 0) (shp T) ws R hT (fun _ _ _ _ h => False.elim h)
      (fun _ _ _ _ h => False.elim h) h.1).symm
  | _ => rfl

#print axioms zwl_exists
#print axioms VRR_own_zero
#print axioms noOwnR_valOfR
#print axioms skN_substT
#print axioms zwl_existsM
#print axioms zwl_existsG
#print axioms blkDb_zero_of
#print axioms blkDb_zero

end TermBlkZ

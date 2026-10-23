import WeakCore.TermCut

/-! # TermOwnKey: an own-handle key in a value's resources names an own cell (B2, ownPub)

`VRR ρ η T rt ws R` with `R (.own l) ≠ 0` forces `η.sto l = some c` with `c.owner = some η.tid`:
the only source of an own key is an `own` reference (`ownW`), whose `ModeOK .own` is ownership.
Type variables read `η.rrs` (`η.urrs` under `unsee`), so the statement assumes the same of them
(`OwnRR`); `push0` adds an empty relation. -/

namespace TermOwnKey
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermStep TermCut
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- Thread `η.tid` owns `l`. -/
def OwnL (η : TEnv) (l : Nat) : Prop := ∃ c, η.sto l = some c ∧ c.owner = some η.tid

/-- Every type-variable relation of `η` (and its memory reading) carries `own l` only at an own `l`. -/
def OwnRR (η : TEnv) : Prop :=
  (∀ k S ws R l, η.rrs k S ws R → R (.own l) ≠ 0 → OwnL η l) ∧
  (∀ k S ws R l, η.urrs k S ws R → R (.own l) ≠ 0 → OwnL η l)

theorem OwnRR.unsee {η : TEnv} (h : OwnRR η) : OwnRR η.unsee := ⟨h.2, h.2⟩

theorem OwnRR.push0 {η : TEnv} (h : OwnRR η) (s : Ty) : OwnRR (η.push0 s) := by
  constructor
  · intro k S ws R l hk h0
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k =>
      simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
      exact h.1 k S ws R l hk h0
  · intro k S ws R l hk h0
    cases k with
    | zero => simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
    | succ k =>
      simp [TEnv.push0, TEnv.ins, TEnv.insR] at hk
      exact h.2 k S ws R l hk h0

theorem ownW_ne {μ : Mode} {ws : List Word} {l : Nat} (h : ownW μ ws (.own l) ≠ 0) :
    μ = .own ∧ ∃ a g, ws.map (·.val) = [.loc a g] ∧ a.label = l := by
  cases μ with
  | own =>
    refine ⟨rfl, ?_⟩
    rcases hv : ws.map (·.val) with _ | ⟨v, _ | ⟨v2, vs⟩⟩
    · simp [ownW, hv] at h
    · cases v with
      | loc a g =>
        refine ⟨a, g, hv, ?_⟩
        simp only [ownW, hv, Res.one_apply] at h
        by_cases e : a.label = l
        · exact e
        · exact absurd (by rw [ite_eq_right_iff.2 (fun h' => absurd (Key.own.inj h').symm e)]) h
      | _ => simp [ownW, hv] at h
    · simp [ownW, hv] at h
  | _ => simp [ownW] at h

theorem add_ne {A B : Res} {k : Key} (h : (A + B) k ≠ 0) : A k ≠ 0 ∨ B k ≠ 0 := by
  simp only [Res.add_apply] at h
  by_cases hA : A k = 0
  · right; omega
  · left; exact hA

/-- **The value lemma.** -/
theorem VRR_ownL : ∀ (T : Ty) {ρ : Nat → Nat} {η : TEnv} {rt : Shp} {ws : List Word} {R : Res} {l : Nat},
    OwnRR η → VRR ρ η T rt ws R → R (.own l) ≠ 0 → OwnL η l := by
  intro T
  induction T with
  | refine t ψ ih => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; exact ih hO h.1 h0
  | iex b ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨n, rb, w, -, h⟩ := h; exact ih hO h h0
  | prod a b iha ihb =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨ra, rb, -, Ra, Rb, rfl, hn, h⟩ := h
      cases hw : ra.wc with
      | none => rw [hn hw] at h0; exact absurd rfl h0
      | some n =>
        obtain ⟨-, h1, h2⟩ := h n hw
        rcases add_ne h0 with h0 | h0
        · exact iha hO h1 h0
        · exact ihb hO h2 h0
  | sum a b iha ihb =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨n, Ra, Rb, -, h | ⟨j, p, -, h1, h2⟩⟩ := h
      · obtain ⟨-, x, s, B, -, -, -, -, -, -, hL, hR⟩ := h
        by_cases hj : B.tag - s < (armsOf Ra).length
        · obtain ⟨q1, q2⟩ := hL hj
          cases hb : isBoxed Ra
          · obtain ⟨q, -, -, -, -, h5⟩ := q2 hb
            have := iha hO.unsee h5 h0; exact this
          · exact iha hO (q1 hb) h0
        · obtain ⟨q1, q2⟩ := hR (by omega)
          cases hb : isBoxed Rb
          · obtain ⟨q, -, -, -, -, h5⟩ := q2 hb
            have := ihb hO.unsee h5 h0; exact this
          · exact ihb hO (q1 hb) h0
      · by_cases hj : j < (armsOf Ra).length
        · obtain ⟨q, -, h⟩ := h1 hj; exact iha hO h h0
        · obtain ⟨q, -, h⟩ := h2 (by omega); exact ihb hO h h0
  | tvar k =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨ws', -, h⟩ := h
      exact hO.1 k rt ws' R l h h0
  | ptr μ u ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨⟨a, c, hw, -, hs, -, hm, -⟩, rfl⟩ := h
      obtain ⟨rfl, a', g, hw', rfl⟩ := ownW_ne h0
      rw [hw] at hw'; cases hw'
      exact ⟨c, hs, hm⟩
  | ptrOpt μ u ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨hv, rfl⟩ := h
      obtain ⟨rfl, a', g, hw', rfl⟩ := ownW_ne h0
      rcases hv with hw | ⟨a, c, hw, -, hs, -, hm, -⟩
      · rw [hw] at hw'; cases hw'
      · rw [hw] at hw'; cases hw'
        exact ⟨c, hs, hm⟩
  | loc μ u ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨hv, rfl⟩ := h
      obtain ⟨rfl, a', g, hw', rfl⟩ := ownW_ne h0
      rcases hv with ⟨hw, -⟩ | ⟨a, c, U, hw, hs, -, -, hm, -⟩
      · rw [hw] at hw'; cases hw'
      · rw [hw] at hw'; cases hw'
        exact ⟨c, hs, hm⟩
  | tex κ b ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨n, rb, s, -, -, -, h⟩ := h
      have := ih (hO.push0 s) h h0; exact this
  | mu b ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      have := ih (hO.push0 _) h h0; exact this
  | iall b ih =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      exact ih hO (h 0) h0
  | word r P =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := h <;> simp [wdW] at h0 <;> split at h0 <;> simp at h0
  | tok r st =>
      intro ρ η rt ws R l hO h h0; simp only [VRR] at h
      subst h; cases st <;> simp at h0
  | unit => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; subst h; exact absurd rfl h0
  | void => intro ρ η rt ws R l hO h h0; simp only [VRR] at h
  | int | tid => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; rw [h.2] at h0; exact absurd rfl h0
  | intS i => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; rw [h.2] at h0; exact absurd rfl h0
  | fix sg w => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; rw [h.2] at h0; exact absurd rfl h0
  | lanes sg w => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; rw [h.2] at h0; exact absurd rfl h0
  | code σ τ _ _ => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; rw [h.2] at h0; exact absurd rfl h0
  | array i τ _ => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; subst h; exact absurd rfl h0
  | share r => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; subst h; simp at h0
  | cap s r => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; subst h; exact absurd rfl h0
  | word2 r P => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := h <;> simp at h0
  | tok2 r P i0 i1 => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; subst h; simp at h0
  | epair r P => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; rw [h.2] at h0; exact absurd rfl h0
  | tokE r P e => intro ρ η rt ws R l hO h h0; simp only [VRR] at h; subst h; simp at h0

/-- `CE` forgets the relations. -/
theorem OwnRR_CE (η : TEnv) : OwnRR (CE η) :=
  ⟨fun _ _ _ _ _ h => (h : False).elim, fun _ _ _ _ _ h => (h : False).elim⟩

/-- A coherent environment's relations are its witnesses' (`CohR`). -/
theorem OwnRR_of_cohR {η : TEnv} (hr : CohR η) : OwnRR η := by
  constructor
  · intro k S ws R l hk h0
    have h := ((hr k).1 (fun _ => 0) S ws R).1 hk
    have := VRR_ownL _ (OwnRR_CE η) h h0
    exact this
  · intro k S ws R l hk h0
    have h := ((hr k).2 (fun _ => 0) S ws R).1 hk
    have := VRR_ownL _ (OwnRR_CE η.unsee) h h0
    exact this

theorem sum_ne {k : Key} : ∀ {Rs : List Res}, Res.sum Rs k ≠ 0 → ∃ R ∈ Rs, R k ≠ 0
  | [], h => absurd rfl h
  | R :: Rs, h => by
      rw [Res.sum_cons] at h
      rcases add_ne h with h | h
      · exact ⟨R, List.mem_cons_self .., h⟩
      · obtain ⟨R', hm, h'⟩ := sum_ne h; exact ⟨R', List.mem_cons_of_mem _ hm, h'⟩

/-! ### Memory's holding -/

theorem ValOfR_ownL {E : TEnv} {T : Ty} {ws : List Word} {R : Res} {l : Nat} (h : ValOfR E T ws R)
    (h0 : R (.own l) ≠ 0) : OwnL E l := by
  have := VRR_ownL _ (OwnRR_CE E.unsee) h.1 h0
  exact this

theorem CellOKR_ownL {E : TEnv} {n nr : Nat} {T : Ty} {vals : List Word} {R : Res} {l : Nat}
    (h : CellOKR E n nr T vals R) (h0 : R (.own l) ≠ 0) : OwnL E l := by
  rcases h with ⟨-, h⟩ | ⟨N, e, us, Rs, -, -, -, -, hlen, rfl, hj⟩
  · exact ValOfR_ownL h h0
  · obtain ⟨Rj, hm, h1⟩ := sum_ne h0
    obtain ⟨j, hjl, hjv⟩ := List.getElem_of_mem hm
    have hj' := hj j Rj (by omega) (by rw [List.getElem?_eq_getElem hjl, hjv])
    by_cases hz : nWords us = 0 ∧ nr ≤ j
    · rw [hj'.1 hz.2 hz.1] at h1; exact absurd rfl h1
    · have hor : j < nr ∨ 0 < nWords us := by
        rcases Nat.lt_or_ge j nr with h | h
        · exact .inl h
        · right; rcases Nat.eq_zero_or_pos (nWords us) with h' | h'
          · exact absurd ⟨h', h⟩ hz
          · exact h'
      exact ValOfR_ownL (hj'.2 hor) h1

theorem HeldEntry_ownL {E : TEnv} {s : St} {l' : AllocLabel} {R : Res} {l : Nat} (h : HeldEntry E s l' R)
    (h0 : R (.own l) ≠ 0) : OwnL E l := by
  obtain ⟨hn, hs⟩ := h
  cases hc : E.sto l' with
  | none => rw [hn hc] at h0; exact absurd rfl h0
  | some c =>
    obtain ⟨vals, -, hok⟩ := hs c hc
    exact CellOKR_ownL hok h0

/-- **Memory's holding** carries own keys of the thread's own cells only. -/
theorem MemHeld_ownL {E : TEnv} {s : St} {H : Res} {l : Nat} (h : MemHeld E s H) (h0 : H (.own l) ≠ 0) :
    OwnL E l := by
  obtain ⟨L, Rl, -, -, rfl, hR⟩ := h
  obtain ⟨R, hm, h1⟩ := sum_ne h0
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hm
  exact HeldEntry_ownL (hR l' hl') h1

theorem MemHeldOn_ownL {Q : AllocLabel → Prop} {E : TEnv} {s : St} {H : Res} {l : Nat}
    (h : MemHeldOn Q E s H) (h0 : H (.own l) ≠ 0) : OwnL E l := by
  obtain ⟨L, Rl, -, -, -, rfl, hR⟩ := h
  obtain ⟨R, hm, h1⟩ := sum_ne h0
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 hm
  exact HeldEntry_ownL (hR l' hl') h1

/-- At a cut, an own cell is a global cell owned by the thread. -/
theorem OwnL_cut {Eg : GEnv} {i : Nat} {S : AllocLabel → Prop} {l : Nat} (h : OwnL (Cut Eg i S) l) :
    ∃ c, Eg.sto l = some c ∧ c.owner = some i := by
  obtain ⟨c, hc, ho⟩ := h
  exact ⟨c, (cutSto_some.1 hc).1, ho⟩

end TermOwnKey

#print axioms TermOwnKey.VRR_ownL
#print axioms TermOwnKey.OwnRR_of_cohR
#print axioms TermOwnKey.MemHeld_ownL
#print axioms TermOwnKey.MemHeldOn_ownL
#print axioms TermOwnKey.OwnL_cut

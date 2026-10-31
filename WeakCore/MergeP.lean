import WeakCore.WrIniInst
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! Multi-label merge: `f` sends every copy label to its original and fixes every other label. -/

def rlv (f : WeakMem.AllocLabel → WeakMem.AllocLabel) : WeakMem.Val → WeakMem.Val
  | .loc a g => .loc ⟨f a.label, a.offset⟩ g
  | v => v

def rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (w : Word) : Word := { w with val := rlv f w.val }

/-- `η₁` (W, the query env) is `η₂` (♭) plus copy cells at the labels `m` with `f m ≠ m`. -/
structure MergeOKP (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (η₁ η₂ : TEnv) : Prop where
  orig : ∀ m, f m ≠ m → f (f m) = f m
  wit : η₁.wit = η₂.wit
  prog : η₁.prog = η₂.prog
  tid : η₁.tid = η₂.tid
  sto : ∀ m c, f m = m → η₁.sto m = some c → η₂.sto m = some c
  ini : ∀ m, f m = m → η₁.ini m ≤ η₂.ini m
  rini : ∀ m, f m = m → η₁.rini m ≤ η₂.rini m
  pfr : ∀ m q, f m = m → η₁.pfr m = some q → η₂.pfr m = some q
  seen : ∀ m, f m = m → η₁.seen m → η₂.seen m
  box : ∀ m B, f m = m → η₁.box m = some B → η₂.box m = some B
  cl : ∀ m, f m ≠ m → ∃ c c', η₂.sto (f m) = some c ∧ η₁.sto m = some c' ∧ c'.ty = c.ty ∧
    c'.owner = none ∧ c.owner = some η₂.tid      -- (5) unit clause dropped: ♭ tid flag
  inil : ∀ m, f m ≠ m → η₁.ini m ≤ η₂.rc (f m)
  rinil : ∀ m, f m ≠ m → η₁.rini m ≤ η₂.rc (f m)
  pfrl : ∀ m, f m ≠ m → ∃ q, η₂.pfr (f m) = some q
  seenl : ∀ m, f m ≠ m → ¬ η₁.seen m
  boxl : ∀ m, f m ≠ m → η₁.box m = none
  boxfree : ∀ m B w a g, η₁.box m = some B → w ∈ B.pay → w.val = .loc a g → f a.label = a.label

def VRRMergeStmtP : Prop :=
  ∀ (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (t : Ty) (η₁ η₂ : TEnv) (ρ : Nat → Nat) (rt : Shp)
    (ws : List Word) (X : Res),
    MergeOKP f η₁ η₂ →
    (∀ k S vs Y, η₁.rrs k S vs Y → η₂.rrs k S (vs.map (rl f)) Y) →
    (∀ k S vs Y, η₁.urrs k S vs Y → η₂.urrs k S (vs.map (rl f)) Y) →
    VRR ρ η₁ t rt ws X → VRRB ρ η₂ t rt (ws.map (rl f)) X

section
variable {f : WeakMem.AllocLabel → WeakMem.AllocLabel}

theorem vals_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word) :
    (ws.map (rl f)).map (·.val) = (ws.map (·.val)).map (rlv f) := by
  simp [rl, List.map_map, Function.comp_def]

theorem rlv_num {v : WeakMem.Val} {n : Nat} : rlv f v = .num n ↔ v = .num n := by
  cases v <;> simp [rlv]

theorem rlv_null {v : WeakMem.Val} : rlv f v = .null ↔ v = .null := by
  cases v <;> simp [rlv]

theorem rl_val_loc {w : Word} {a : WeakMem.Address} {g : Nat}
    (hv : w.val = .loc a g) : (rl f w).val = .loc ⟨f a.label, a.offset⟩ g := by simp [rl, rlv, hv]

theorem rl_val_num {w : Word} {j : Nat} (hv : w.val = .num j) : (rl f w).val = .num j := by simp [rl, rlv, hv]

theorem rl_with_loc {w : Word} {a : WeakMem.Address} {g : Nat} (hv : w.val = .loc a g) (s : Nat) :
    rl f { w with val := .loc a s } = { rl f w with val := .loc ⟨f a.label, a.offset⟩ s } := by
  simp [rl, rlv, hv]

theorem decodeArm_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (tr : Tier) (as : List Ty) (ws : List Word) :
    decodeArm tr as (ws.map (rl f)) = (decodeArm tr as ws).map (fun x => (x.1, x.2.map (rl f))) := by
  rcases ws with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> cases tr <;> simp only [decodeArm, List.map] <;>
    try rfl
  · cases hv : w.val with
    | loc a g =>
      simp only [rl_val_loc (f := f) hv]
      cases ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
      | none => rfl
      | some q => simp [rl_with_loc (f := f) hv]
    | num j =>
      simp only [rl_val_num hv]
      cases as[j]? with
      | none => rfl
      | some arm =>
        simp only [bind, Option.bind]
        generalize armK arm = K
        cases K <;> simp [cst, Promises.TVal.mk0, rl, rlv]
    | _ => simp [rl, hv, rlv]
  · cases hv : w.val with
    | num j =>
      simp only [rl_val_num hv]
      cases as[j]? with
      | none => rfl
      | some arm => simp only [bind, Option.bind]; split <;> simp
    | loc a g => simp only [rl_val_loc (f := f) hv]; rfl
    | _ => simp [rl, hv, rlv]

theorem encodeArm_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (tr : Tier) (as : List Ty) (j : Nat) (p : List Word) :
    encodeArm tr as j (p.map (rl f)) = (encodeArm tr as j p).map (List.map (rl f)) := by
  cases tr with
  | niche =>
    simp only [encodeArm]
    cases as[j]? with
    | none => rfl
    | some arm =>
      simp only [bind, Option.bind]
      generalize armK arm = K
      rcases p with _ | ⟨w, _ | ⟨w2, p⟩⟩
      · cases K <;> simp [cst, Promises.TVal.mk0, rl, rlv]
      · cases hv : w.val with
        | loc a g =>
          cases K <;> simp [rl_val_loc (f := f) hv, hv, rl_with_loc (f := f) hv]
        | null =>
          have hn : (rl f w).val = .null := by simp [rl, rlv, hv]
          cases K <;> simp [hn, hv, cst, Promises.TVal.mk0, rl, rlv] <;> split <;> simp [rl, rlv]
        | num n =>
          cases K <;> simp [rl_val_num hv, hv]
        | _ =>
          cases K <;> simp [rl, rlv, hv]
      · cases K <;> simp
  | wide =>
    simp only [encodeArm]
    rcases p with _ | ⟨w, _ | ⟨w2, p⟩⟩ <;> simp [cst, Promises.TVal.mk0, rl, rlv]
  | boxed => rfl

theorem ofArm_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) (t : Ty) (j : Nat) (p : List Word) :
    ofArm t j (p.map (rl f)) = (ofArm t j p).map (List.map (rl f)) := by
  simp only [ofArm]; split
  · exact encodeArm_rl f _ _ _ _
  · split <;> rfl

theorem WLe_rl (f : WeakMem.AllocLabel → WeakMem.AllocLabel) : ∀ {ws ws' : List Word}, WLe ws ws' →
    WLe (ws.map (rl f)) (ws'.map (rl f))
  | [], [], _ => trivial
  | w :: ws, w' :: ws', ⟨⟨h1, h2⟩, h3⟩ => by
    refine ⟨⟨by simp [rl, h1], fun a g h => ?_⟩, WLe_rl f h3⟩
    cases hv : w.val with
    | loc a0 g0 => exact h2 a0 g0 hv
    | _ => simp [rl, rlv, hv] at h

theorem rl_of_fix {w : Word} (h : ∀ a g, w.val = .loc a g → f a.label = a.label) : rl f w = w := by
  cases w with
  | mk v vw rt =>
    cases v with
    | loc a g => have := h a g rfl; simp [rl, rlv, this]
    | _ => simp [rl, rlv]

theorem map_rlv_single_num {vs : List WeakMem.Val} {n : Nat} :
    vs.map (rlv f) = [.num n] ↔ vs = [.num n] := by
  rcases vs with _ | ⟨v, _ | ⟨v2, vs⟩⟩ <;> simp [rlv_num]

theorem map_rlv_pair_num {vs : List WeakMem.Val} {n0 n1 : Nat} :
    vs.map (rlv f) = [.num n0, .num n1] ↔ vs = [.num n0, .num n1] := by
  rcases vs with _ | ⟨v, _ | ⟨v2, _ | ⟨v3, vs⟩⟩⟩ <;> simp [rlv_num]

theorem map_rlv_null {vs : List WeakMem.Val} : vs.map (rlv f) = [.null] ↔ vs = [.null] := by
  rcases vs with _ | ⟨v, _ | ⟨v2, vs⟩⟩ <;> simp [rlv_null]

theorem vals_rl_num {ws : List Word} {n : Nat} :
    (ws.map (rl f)).map (·.val) = [.num n] ↔ ws.map (·.val) = [.num n] := by
  rw [vals_rl]; exact map_rlv_single_num

theorem vals_rl_pair {ws : List Word} {n0 n1 : Nat} :
    (ws.map (rl f)).map (·.val) = [.num n0, .num n1] ↔ ws.map (·.val) = [.num n0, .num n1] := by
  rw [vals_rl]; exact map_rlv_pair_num

theorem vals_rl_null {ws : List Word} :
    (ws.map (rl f)).map (·.val) = [.null] ↔ ws.map (·.val) = [.null] := by
  rw [vals_rl]; exact map_rlv_null

theorem WordHolds_rl {P : Proto} {ws : List Word} :
    WordHolds P ((ws.map (rl f)).map (·.val)) ↔ WordHolds P (ws.map (·.val)) := by
  constructor
  · rintro ⟨hg, n, c, cl, k, hv, h⟩; exact ⟨hg, n, c, cl, k, vals_rl_num.1 hv, h⟩
  · rintro ⟨hg, n, c, cl, k, hv, h⟩; exact ⟨hg, n, c, cl, k, vals_rl_num.2 hv, h⟩

theorem Word2Holds_rl {P : Proto2} {ws : List Word} :
    Word2Holds P ((ws.map (rl f)).map (·.val)) ↔ Word2Holds P (ws.map (·.val)) := by
  constructor
  · rintro ⟨n0, n1, c, cl, k0, k1, hv, h⟩; exact ⟨n0, n1, c, cl, k0, k1, vals_rl_pair.1 hv, h⟩
  · rintro ⟨n0, n1, c, cl, k0, k1, hv, h⟩; exact ⟨n0, n1, c, cl, k0, k1, vals_rl_pair.2 hv, h⟩

theorem vals_rl_loc {ws : List Word} {a : WeakMem.Address} {g : Nat} (h : ws.map (·.val) = [.loc a g]) :
    (ws.map (rl f)).map (·.val) = [.loc ⟨f a.label, a.offset⟩ g] := by
  rw [vals_rl, h]; rfl

theorem IniR_rl {ρ : Nat → Nat} {i₁ i₂ : WeakMem.AllocLabel → Nat} (hl : ∀ m, i₁ m ≤ i₂ (f m)) :
    ∀ (ψ : Pred) (ws : List Word), IniR ρ i₁ ψ ws → IniR ρ i₂ ψ (ws.map (rl f))
  | .ini k, ws, h => by
    intro b hb
    rw [vals_rl] at hb
    rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
    · simp at hb
    · cases hv : w.val with
      | loc a g =>
        simp only [List.map, hv, rlv] at hb
        have ha := h a (by simp [hv]; simp at hb; exact hb.2)
        simp at hb; obtain ⟨rfl, -⟩ := hb; exact Nat.le_trans ha (hl _)
      | _ => simp [hv, rlv] at hb
    · simp at hb
  | .and p q, ws, h => ⟨IniR_rl hl p ws h.1, IniR_rl hl q ws h.2⟩
  | .tt, _, _ => trivial
  | .le _ _, _, _ => trivial
  | .eq _ _, _, _ => trivial

theorem ownW_rl (μ : Mode) {ws : List Word}
    (h : μ = .own → ∀ a g, ws.map (·.val) = [.loc a g] → f a.label = a.label) :
    ownW μ (ws.map (rl f)) = ownW μ ws := by
  cases μ with
  | own =>
    have h' := h rfl
    simp only [ownW]
    rw [vals_rl]
    rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩
    · rfl
    · cases hv : w.val with
      | loc a g =>
        have := h' a g (by simp [hv])
        simp [rlv, hv, this]
      | _ => simp [rlv, hv]
    · simp
  | _ => rfl

end
end TermSound.Flat

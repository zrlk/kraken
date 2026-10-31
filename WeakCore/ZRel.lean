import WeakCore.MergeR
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

/-! Per-position relabeling (lift side, L2): word `i` is relabeled by `G i`. -/

def rlI : (Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) → List Word → List Word
  | _, [] => []
  | G, w :: ws => rl (G 0) w :: rlI (fun i => G (i + 1)) ws

def shI : Tier → (Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) → (Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
  | .wide, G => fun i => G (i + 1)
  | _, G => G

def unI : Tier → (Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) → (Nat → WeakMem.AllocLabel → WeakMem.AllocLabel)
  | .wide, G => fun i => G (i - 1)
  | _, G => G

section
variable {G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel}

@[simp] theorem rlI_nil (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) : rlI G [] = [] := rfl
@[simp] theorem rlI_cons (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (w : Word) (ws : List Word) :
    rlI G (w :: ws) = rl (G 0) w :: rlI (fun i => G (i + 1)) ws := rfl

@[simp] theorem rlI_length : ∀ (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (ws : List Word),
    (rlI G ws).length = ws.length
  | _, [] => rfl
  | G, _ :: ws => by simp [rlI_length _ ws]

theorem rlI_take : ∀ (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (n : Nat) (ws : List Word),
    (rlI G ws).take n = rlI G (ws.take n)
  | _, 0, _ => by simp
  | _, _ + 1, [] => by simp
  | G, n + 1, w :: ws => by simp [rlI_take _ n ws]

theorem rlI_drop : ∀ (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) (n : Nat) (ws : List Word),
    (rlI G ws).drop n = rlI (fun i => G (i + n)) (ws.drop n)
  | _, 0, _ => by simp
  | _, _ + 1, [] => by simp
  | G, n + 1, w :: ws => by
    simp only [rlI_cons, List.drop_succ_cons]; rw [rlI_drop _ n ws]
    first | rfl | (congr 1; funext i; congr 1; omega) | (congr 1; funext i; congr 1)

theorem rl_cst (g : WeakMem.AllocLabel → WeakMem.AllocLabel) (v : WeakMem.Val) (hv : ∀ a s, v ≠ .loc a s) :
    rl g (cst v) = cst v := by
  cases v <;> simp_all [rl, rlv, cst, Promises.TVal.mk0]


theorem decodeArm_rlI (tr : Tier) (as : List Ty) (ws : List Word) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) :
    decodeArm tr as (rlI G ws) = (decodeArm tr as ws).map (fun x => (x.1, rlI (shI tr G) x.2)) := by
  rcases ws with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> cases tr <;> simp only [rlI, decodeArm, shI] <;>
    try rfl
  · cases hv : w.val with
    | loc a g =>
      simp only [rl_val_loc (f := G 0) hv]
      cases ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
      | none => rfl
      | some q => simp [rl_with_loc (f := G 0) hv]
    | num j =>
      simp only [rl_val_num (f := G 0) hv]
      cases as[j]? with
      | none => rfl
      | some arm =>
        simp only [bind, Option.bind]
        generalize armK arm = K
        cases K <;> simp [cst, Promises.TVal.mk0, rl, rlv]
    | _ => simp [rl, hv, rlv]
  · cases hv : w.val with
    | num j =>
      simp only [rl_val_num (f := G 0) hv]
      cases as[j]? with
      | none => rfl
      | some arm => simp only [bind, Option.bind]; split <;> simp
    | loc a g => simp only [rl_val_loc (f := G 0) hv]; rfl
    | _ => simp [rl, hv, rlv]

theorem encodeArm_rlI (tr : Tier) (as : List Ty) (j : Nat) (p : List Word) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) :
    encodeArm tr as j (rlI G p) = (encodeArm tr as j p).map (rlI (unI tr G)) := by
  cases tr with
  | niche =>
    simp only [encodeArm, unI]
    cases as[j]? with
    | none => rfl
    | some arm =>
      simp only [bind, Option.bind]
      generalize armK arm = K
      rcases p with _ | ⟨w, _ | ⟨w2, p⟩⟩
      · cases K <;> simp [cst, Promises.TVal.mk0, rl, rlv]
      · simp only [rlI_cons, rlI_nil]
        cases hv : w.val with
        | loc a g =>
          cases K <;> simp [rl_val_loc (f := G 0) hv, hv, rl_with_loc (f := G 0) hv]
        | null =>
          have hn : (rl (G 0) w).val = .null := by simp [rl, rlv, hv]
          cases K <;> simp [hn, hv, cst, Promises.TVal.mk0, rl, rlv] <;> split <;> simp [rl, rlv]
        | num n =>
          cases K <;> simp [rl_val_num (f := G 0) hv, hv]
        | _ =>
          cases K <;> simp [rl, rlv, hv]
      · cases K <;> simp
  | wide =>
    simp only [encodeArm, unI]
    rcases p with _ | ⟨w, _ | ⟨w2, p⟩⟩ <;> simp [cst, Promises.TVal.mk0, rl, rlv]
  | boxed => rfl

def unA (t : Ty) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel :=
  if sumHead t then unI t.tier G else G

theorem ofArm_rlI (t : Ty) (j : Nat) (p : List Word) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel) :
    ofArm t j (rlI G p) = (ofArm t j p).map (rlI (unA t G)) := by
  simp only [ofArm, unA]; split
  · exact encodeArm_rlI _ _ _ _ _
  · split <;> rfl

theorem VEq_rlI : ∀ (q ws : List Word) (G₁ G₂ : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel), VEq q ws →
    (∀ i w a g, ws[i]? = some w → w.val = .loc a g → G₁ i = G₂ i) → VEq (rlI G₁ q) (rlI G₂ ws)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, h, _ => by simp [VEq] at h
  | _ :: _, [], _, _, h, _ => by simp [VEq] at h
  | x :: q, y :: ws, G₁, G₂, h, hg => by
    simp only [VEq, List.map_cons, List.cons.injEq] at h
    simp only [VEq, rlI_cons, List.map_cons, List.cons.injEq]
    refine ⟨?_, VEq_rlI q ws _ _ h.2 (fun i w a g h1 h2 => hg (i + 1) w a g (by simpa using h1) h2)⟩
    cases hy : y.val with
    | loc a g => rw [hg 0 y a g rfl hy]; simp [rl, h.1, hy]
    | _ => simp [rl, rlv, h.1, hy]

theorem ShapeC_rlI {t : Ty} {ws : List Word} (h : ShapeC t ws) : ShapeC t (rlI G ws) :=
  fun us hu => by simpa using h us hu

theorem decode_enc_agree {tr : Tier} {as : List Ty} {ws p : List Word} {j : Nat}
    (hd : decodeArm tr as ws = some (j, p)) :
    ∀ i w a g, ws[i]? = some w → w.val = .loc a g → unI tr (shI tr G) i = G i := by
  intro i w a g h1 h2
  cases tr with
  | wide =>
    rcases ws with _ | ⟨t, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> simp only [decodeArm] at hd <;> try cases hd
    cases i with
    | zero =>
      simp at h1; subst h1
      simp only [h2] at hd; cases hd
    | succ i => cases i with
      | zero => rfl
      | succ i => simp at h1
  | _ => rfl

theorem vals_rlI_loc {ws : List Word} {a : WeakMem.Address} {g : Nat} (h : ws.map (·.val) = [.loc a g]) :
    (rlI G ws).map (·.val) = [.loc ⟨G 0 a.label, a.offset⟩ g] := by
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩ <;> simp at h; simp [rl, rlv, h]

theorem vals_rlI_null {ws : List Word} (h : ws.map (·.val) = [.null]) : (rlI G ws).map (·.val) = [.null] := by
  rcases ws with _ | ⟨w, _ | ⟨w2, ws⟩⟩ <;> simp at h; simp [rl, rlv, h]

theorem Valid_rlI (t : Ty) : ∀ (ws : List Word) (G : Nat → WeakMem.AllocLabel → WeakMem.AllocLabel),
    Valid t ws → Valid t (rlI G ws) := by
  induction t with
  | ptr μ u _ =>
    intro ws G h; obtain ⟨a, ha⟩ := h; exact ⟨_, vals_rlI_loc ha⟩
  | ptrOpt μ u _ =>
    intro ws G h; rcases h with h | ⟨a, ha⟩
    · exact Or.inl (vals_rlI_null h)
    · exact Or.inr ⟨_, vals_rlI_loc ha⟩
  | loc μ u _ =>
    intro ws G h; rcases h with h | ⟨a, ha⟩
    · exact Or.inl (vals_rlI_null h)
    · exact Or.inr ⟨_, vals_rlI_loc ha⟩
  | prod a b iha ihb =>
    intro ws G h n hn
    obtain ⟨h1, h2⟩ := h n hn
    exact ⟨by rw [rlI_take]; exact iha _ _ h1, by rw [rlI_drop]; exact ihb _ _ h2⟩
  | sum a b iha ihb =>
    intro ws G h
    rcases h with h | ⟨j, p, arm, hd, harm, ⟨hp1, hp2, hp3⟩, ⟨q, hq, hv⟩, hA, hB⟩
    · exact Or.inl h
    refine Or.inr ⟨j, rlI (shI (Ty.sum a b).tier G) p, arm, by rw [decodeArm_rlI, hd]; rfl, harm,
      ⟨by simpa using hp1, ?_, ?_⟩,
      ⟨rlI (unI (Ty.sum a b).tier (shI (Ty.sum a b).tier G)) q, by rw [encodeArm_rlI, hq]; rfl,
        VEq_rlI q ws _ _ hv (decode_enc_agree hd)⟩, fun hj => ?_, fun hj => ?_⟩
    · intro hk; obtain ⟨w, adr, rfl, hw⟩ := hp2 hk
      exact ⟨_, _, rfl, rl_val_loc hw⟩
    · intro hk; obtain ⟨w, rfl, hw⟩ := hp3 hk
      refine ⟨_, rfl, ?_⟩
      rcases hw with hw | ⟨adr, hw⟩
      · exact Or.inl (by simp [rl, rlv, hw])
      · exact Or.inr ⟨_, rl_val_loc hw⟩
    · obtain ⟨q, h1, h2, h3, h4⟩ := hA hj
      exact ⟨_, by rw [ofArm_rlI, h1]; rfl, ShapeC_rlI h2, h3, iha _ _ h4⟩
    · obtain ⟨q, h1, h2, h3, h4⟩ := hB hj
      exact ⟨_, by rw [ofArm_rlI, h1]; rfl, ShapeC_rlI h2, h3, ihb _ _ h4⟩
  | refine t ψ ih => intro ws G h; exact ih ws G h
  | iall t ih => intro ws G h; exact ih ws G h
  | iex t ih => intro ws G h; exact ih ws G h
  | mu t ih => intro ws G h; exact ih ws G h
  | tex κ t ih => intro ws G h; exact ih ws G h
  | void => intro ws G h; exact h
  | _ => intro ws G h; trivial

theorem Lay_rlI {σs : List Ty} {t rt : Ty} {ws : List Word} (h : Lay σs t rt ws) : Lay σs t rt (rlI G ws) :=
  ⟨ShapeC_rlI h.1, h.2.1, h.2.2.1, Valid_rlI rt ws G h.2.2.2.1, h.2.2.2.2⟩

theorem Lay_rl {σs : List Ty} {t rt : Ty} {ws : List Word} {f : WeakMem.AllocLabel → WeakMem.AllocLabel}
    (h : Lay σs t rt ws) : Lay σs t rt (ws.map (rl f)) :=
  ⟨ShapeC_rl h.1, h.2.1, h.2.2.1, Valid_rl f rt ws h.2.2.2.1, h.2.2.2.2⟩
end
end TermSound.Flat

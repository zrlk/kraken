import WeakCore.MergeStmt
namespace TermSound.Flat
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound

theorem vals_lr (l' l : WeakMem.AllocLabel) (ws : List Word) :
    (ws.map (lr l' l)).map (·.val) = (ws.map (·.val)).map (lrv l' l) := by
  simp [lr, List.map_map, Function.comp_def]

theorem lrv_num {l' l : WeakMem.AllocLabel} {v : WeakMem.Val} {n : Nat} : lrv l' l v = .num n ↔ v = .num n := by
  cases v <;> simp [lrv] <;> split <;> simp

theorem lrv_null {l' l : WeakMem.AllocLabel} {v : WeakMem.Val} : lrv l' l v = .null ↔ v = .null := by
  cases v <;> simp [lrv] <;> split <;> simp

theorem lr_val_loc {l' l : WeakMem.AllocLabel} {w : Word} {a : WeakMem.Address} {g : Nat}
    (hv : w.val = .loc a g) : ∃ b, (lr l' l w).val = .loc b g ∧ b.offset = a.offset := by
  by_cases h : a.label = l'
  · exact ⟨⟨l, a.offset⟩, by simp [lr, lrv, hv, h], rfl⟩
  · exact ⟨a, by simp [lr, lrv, hv, h], rfl⟩

theorem lr_val_num {l' l : WeakMem.AllocLabel} {w : Word} {j : Nat} (hv : w.val = .num j) :
    (lr l' l w).val = .num j := by simp [lr, lrv, hv]

theorem decodeArm_lr (l' l : WeakMem.AllocLabel) (tr : Tier) (as : List Ty) (ws : List Word) :
    decodeArm tr as (ws.map (lr l' l)) = (decodeArm tr as ws).map (fun x => (x.1, x.2.map (lr l' l))) := by
  rcases ws with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, ws⟩⟩⟩ <;> cases tr <;> simp only [decodeArm, List.map] <;>
    try rfl
  · cases hv : w.val with
    | loc a g =>
      obtain ⟨b, hb, -⟩ := lr_val_loc (l' := l') (l := l) hv
      have e : (lr l' l { w with val := .loc a 0 }) = { lr l' l w with val := .loc b 0 } := by
        by_cases h : a.label = l'
        · simp [lr, lrv, hv, h] at hb ⊢; subst hb; rfl
        · simp [lr, lrv, hv, h] at hb ⊢; subst hb; rfl
      simp only [hb]
      cases ((enumFrom as 0).filter (fun p => isPtrish p.2))[g]? with
      | none => rfl
      | some q => simp [e]
    | num j =>
      simp only [lr_val_num hv]
      cases as[j]? with
      | none => rfl
      | some arm =>
        simp only [bind, Option.bind]
        generalize armK arm = K
        cases K <;> simp [cst, Promises.TVal.mk0, lr, lrv]
    | _ => simp [lr, hv, lrv]
  · cases hv : w.val with
    | num j =>
      simp only [lr_val_num hv]
      cases as[j]? with
      | none => rfl
      | some arm => simp only [bind, Option.bind]; split <;> simp
    | loc a g => obtain ⟨b, hb, -⟩ := lr_val_loc (l' := l') (l := l) hv; simp only [hb]; rfl
    | _ => simp [lr, hv, lrv]

theorem encodeArm_lr (l' l : WeakMem.AllocLabel) (tr : Tier) (as : List Ty) (j : Nat) (p : List Word) :
    encodeArm tr as j (p.map (lr l' l)) = (encodeArm tr as j p).map (List.map (lr l' l)) := by
  cases tr with
  | niche =>
    simp only [encodeArm]
    cases as[j]? with
    | none => rfl
    | some arm =>
      simp only [bind, Option.bind]
      generalize armK arm = K
      rcases p with _ | ⟨w, _ | ⟨w2, p⟩⟩
      · cases K <;> simp [cst, Promises.TVal.mk0, lr, lrv]
      · cases hv : w.val with
        | loc a g =>
          obtain ⟨b, hb, -⟩ := lr_val_loc (l' := l') (l := l) hv
          have e : ∀ s, (lr l' l { w with val := .loc a s }) = { lr l' l w with val := .loc b s } := by
            intro s
            by_cases h : a.label = l'
            · simp [lr, lrv, hv, h] at hb ⊢; subst hb; rfl
            · simp [lr, lrv, hv, h] at hb ⊢; subst hb; rfl
          cases K <;> simp [hb, hv, e]
        | null =>
          have hn : (lr l' l w).val = .null := by simp [lr, lrv, hv]
          cases K <;> simp [hn, hv, cst, Promises.TVal.mk0, lr, lrv] <;> split <;> simp [lr, lrv]
        | num n =>
          cases K <;> simp [lr_val_num hv, hv]
        | _ =>
          cases K <;> simp [lr, lrv, hv]
      · cases K <;> simp
  | wide =>
    simp only [encodeArm]
    rcases p with _ | ⟨w, _ | ⟨w2, p⟩⟩ <;> simp [cst, Promises.TVal.mk0, lr, lrv]
  | boxed => rfl

theorem ofArm_lr (l' l : WeakMem.AllocLabel) (t : Ty) (j : Nat) (p : List Word) :
    ofArm t j (p.map (lr l' l)) = (ofArm t j p).map (List.map (lr l' l)) := by
  simp only [ofArm]; split
  · exact encodeArm_lr l' l _ _ _ _
  · split <;> rfl

theorem WLe_lr (l' l : WeakMem.AllocLabel) : ∀ {ws ws' : List Word}, WLe ws ws' →
    WLe (ws.map (lr l' l)) (ws'.map (lr l' l))
  | [], [], _ => trivial
  | w :: ws, w' :: ws', ⟨⟨h1, h2⟩, h3⟩ => by
    refine ⟨⟨by simp [lr, h1], fun a g h => ?_⟩, WLe_lr l' l h3⟩
    cases hv : w.val with
    | loc a0 g0 => exact h2 a0 g0 hv
    | _ => simp [lr, lrv, hv] at h

end TermSound.Flat

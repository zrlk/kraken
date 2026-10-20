import WeakCore.TermViewInvB

/-!
# TermViewInvC: environments, sum encodings, `injM` / `projM`
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem WV_with {n : Nat} {w : Word} (h : WV n w) (v : Val) : WV n { w with val := v } := h

theorem lookupE_V {n : Nat} {env : Env} {x : String} {t : Ty} {ws : List Word} (he : EnvV n env)
    (h : lookupE env x = some (t, ws)) : WsV n ws := by
  unfold lookupE at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨e, hf, he'⟩ := h
  have hm := List.mem_of_find?_eq_some hf
  have := he e hm
  rw [he'] at this
  exact this

theorem evalAt_V {n : Nat} {env : Env} {a : At} {t : Ty} {ws : List Word} (he : EnvV n env)
    (h : evalAt env a = some (t, ws)) : WsV n ws := by
  cases a with
  | var x => exact lookupE_V he h
  | lit k =>
      simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact WsV_cons (WV_cst _ _) (WsV_nil _)
  | unit =>
      simp only [evalAt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact WsV_nil _

theorem encodeArm_V {n : Nat} {tr : Tier} {as : List Ty} {j : Nat} {p q : List Word}
    (h : encodeArm tr as j p = some q) (hp : WsV n p) : WsV n q := by
  unfold encodeArm at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨arm, -, h⟩ := h
    split at h
    · rename_i w
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact WsV_cons (WV_with (hp _ (by simp)) _) (WsV_nil _)
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          exact WsV_cons (WV_cst _ _) (WsV_nil _)
        · cases h
      · cases h
    · rename_i w
      split at h
      · simp only [Option.some.injEq] at h; subst h
        exact WsV_cons (WV_with (hp _ (by simp)) _) (WsV_nil _)
      · split at h
        · simp only [Option.some.injEq] at h; subst h
          exact WsV_cons (WV_cst _ _) (WsV_nil _)
        · cases h
      · cases h
    · simp only [Option.some.injEq] at h; subst h
      exact WsV_cons (WV_cst _ _) (WsV_nil _)
    · cases h
  · split at h
    · simp only [Option.some.injEq] at h; subst h
      exact WsV_cons (WV_cst _ _) (WsV_cons (WV_cst _ _) (WsV_nil _))
    · rename_i w
      simp only [Option.some.injEq] at h; subst h
      exact WsV_cons (WV_cst _ _) (WsV_cons (hp _ (by simp)) (WsV_nil _))
    · cases h
  · cases h

theorem decodeArm_V {n : Nat} {tr : Tier} {as : List Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : decodeArm tr as ws = some (j, p)) (hw : WsV n ws) : WsV n p := by
  unfold decodeArm at h
  split at h
  · rename_i w
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨_, -, h⟩ := h
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact WsV_cons (WV_with (hw _ (by simp)) _) (WsV_nil _)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact WsV_nil _
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact WsV_cons (WV_cst _ _) (WsV_nil _)
      · cases h
    · cases h
  · rename_i t w
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨arm, -, h⟩ := h
      split at h
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact WsV_nil _
      · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact WsV_cons (hw _ (by simp)) (WsV_nil _)
    · cases h
  · cases h

theorem ofArm_V {n : Nat} {t : Ty} {j : Nat} {p q : List Word} (h : ofArm t j p = some q) (hp : WsV n p) :
    WsV n q := by
  unfold ofArm at h
  split at h
  · exact encodeArm_V h hp
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact hp
    · cases h

theorem asArm_V {n : Nat} {t : Ty} {ws : List Word} {j : Nat} {p : List Word} (h : asArm t ws = some (j, p))
    (hw : WsV n ws) : WsV n p := by
  unfold asArm at h
  split at h
  · exact decodeArm_V h hw
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact hw

theorem injM_V {g : G} {s s' : St} {t : Ty} {j : Nat} {p q : List Word} (h : (s', q) ∈ injM g s t j p)
    (hs : StV s) (hp : WsV s.mem.size p) : StV s' ∧ s.mem.size ≤ s'.mem.size ∧ WsV s'.mem.size q := by
  unfold injM at h
  split at h
  · split at h
    · simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨⟨s1, pw⟩, hin, rfl, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := alloc_V hin hs (WsV_cons (WV_cst _ _) hp)
      split
      · obtain ⟨f1, f2⟩ := fenceS_V h1 .st
        refine ⟨f1, by rw [f2]; exact h2, ?_⟩
        rw [f2]; exact WsV_cons h3 (WsV_nil _)
      · exact ⟨h1, h2, WsV_cons h3 (WsV_nil _)⟩
    · cases h
  · cases hq : ofArm t j p with
    | none => simp [hq, ol] at h
    | some q' =>
      simp only [hq, ol, Option.map_some, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hs, Nat.le_refl _, ofArm_V hq hp⟩

theorem projM_V {g : G} {s s' : St} {t : Ty} {ws : List Word} {j : Nat} {p : List Word}
    (h : (s', j, p) ∈ projM g s t ws) (hs : StV s) (hw : WsV s.mem.size ws) :
    StV s' ∧ s'.mem = s.mem ∧ WsV s.mem.size p := by
  unfold projM at h
  split at h
  · split at h
    · rename_i pw
      split at h
      · rename_i b _
        simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, tw⟩, hin1, h⟩ := h
        have hpw := hw pw (by simp)
        obtain ⟨h1, h2, -⟩ := loadUnits_V _ _ _ _ _ hin1 hs hpw
        split at h
        · split at h
          · split at h
            · simp only [List.mem_map, Prod.mk.injEq] at h
              obtain ⟨⟨s2, p2⟩, hin2, rfl, rfl, rfl⟩ := h
              have hpw1 : WV s1.mem.size pw := by rw [h2]; exact hpw
              obtain ⟨g1, g2, g3⟩ := loadUnits_V _ _ _ _ _ hin2 h1 hpw1
              refine ⟨g1, g2.trans h2, ?_⟩
              rw [← h2]; exact g3
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases hq : asArm t ws with
    | none => simp [hq, ol] at h
    | some jp =>
      obtain ⟨j', p'⟩ := jp
      simp only [hq, ol, Option.map_some, Option.toList_some, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hs, rfl, asArm_V hq hw⟩

end TermViewInv

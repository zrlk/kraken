import WeakCore.TermViewInvD0

/-!
# TermViewInvE3: `evalOp` cases for lane / exchange / slot loads and stores
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem e3_pw {n : Nat} {env : Env} {a : At} {t : Ty} {pw : Word} (he : EnvV n env)
    (h : evalAt env a = some (t, [pw])) : WV n pw :=
  evalAt_V he h pw (by simp)

theorem e3_load {arch : Arch} {pw : Word} {a : Address} {acq : Bool} {us : List Acc} {k : Nat}
    {s s1 : St} {old : List Word} (h : (s1, old) ∈ loadUnits arch pw a acq us k s) (hs : StV s)
    (hp : WV s.mem.size pw) : Concl s s1 old := by
  obtain ⟨h1, h2, h3⟩ := loadUnits_V us k s s1 old h hs hp
  exact ⟨h1, by rw [h2]; exact Nat.le_refl _, by rw [h2]; exact h3⟩

theorem e3_ldst {kn : Promises.Knobs} {arch : Arch} {pw : Word} {a b : Address} {us cs : List Acc}
    {s s1 s2 : St} {old xs : List Word}
    (h1 : (s1, old) ∈ loadUnits arch pw a false us 0 s)
    (h2 : s2 ∈ storeUnits kn arch pw b false cs xs 0 s1) (hs : StV s)
    (hp : WV s.mem.size pw) (hx : WsV s.mem.size xs) : Concl s s2 old := by
  obtain ⟨g1, g2, g3⟩ := loadUnits_V us 0 s s1 old h1 hs hp
  have hp1 : WV s1.mem.size pw := by rw [g2]; exact hp
  have hx1 : WsV s1.mem.size xs := by rw [g2]; exact hx
  obtain ⟨k1, k2⟩ := storeUnits_V cs xs 0 s1 s2 h2 g1 hp1 hx1
  refine ⟨k1, by rw [← g2]; exact k2, ?_⟩
  exact WsV.mono g3 (by rw [← g2]; exact k2)

theorem eo_xchg {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.xchg a v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hv
    split at h
    · split at h
      · simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨s1, old⟩, hin, s2, hst, rfl, rfl, rfl⟩ := h
        exact e3_ldst hin hst hs (e3_pw he hb) (evalAt_V he hv)
      · simp at h
    · simp at h
  · simp at h

theorem eo_ldl {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.ldl b i)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi
    split at h
    · split at h
      · simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨⟨s1, old⟩, hin, x, -, rfl, rfl, rfl⟩ := h
        obtain ⟨c1, c2, -⟩ := e3_load hin hs (e3_pw he hb)
        exact ⟨c1, c2, WsV_single (WV_cst _ _)⟩
      · simp at h
    · simp at h
  · simp at h

theorem eo_ldlw {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b wi j : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.ldlw b wi j)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi hj
    split at h
    · split at h
      · simp only [List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq] at h
        obtain ⟨⟨s1, old⟩, hin, x, -, rfl, rfl, rfl⟩ := h
        obtain ⟨c1, c2, -⟩ := e3_load hin hs (e3_pw he hb)
        exact ⟨c1, c2, WsV_single (WV_cst _ _)⟩
      · simp at h
    · simp at h
  · simp at h

theorem eo_stl {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.stl b i v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi hv
    split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, old⟩, hin, h⟩ := h
        split at h
        · simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨s2, hst, rfl, rfl, rfl⟩ := h
          obtain ⟨c1, c2, -⟩ := e3_ldst hin hst hs (e3_pw he hb) (WsV_single (WV_cst _ _))
          exact ⟨c1, c2, WsV_nil _⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem eo_stlw {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b wi j v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.stlw b wi j v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi hj hv
    split at h
    · split at h
      · simp only [List.mem_flatMap] at h
        obtain ⟨⟨s1, old⟩, hin, h⟩ := h
        split at h
        · simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨s2, hst, rfl, rfl, rfl⟩ := h
          obtain ⟨c1, c2, -⟩ := e3_ldst hin hst hs (e3_pw he hb) (WsV_single (WV_cst _ _))
          exact ⟨c1, c2, WsV_nil _⟩
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem eo_xchgAt {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.xchgAt b i v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi hv
    split at h
    · split at h
      · simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨s1, old⟩, hin, s2, hst, rfl, rfl, rfl⟩ := h
        exact e3_ldst hin hst hs (e3_pw he hb) (evalAt_V he hv)
      · simp at h
    · simp at h
  · simp at h

theorem eo_loadAt {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.loadAt b i)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi
    split at h
    · split at h
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨s1, old⟩, hin, rfl, rfl, rfl⟩ := h
        exact e3_load hin hs (e3_pw he hb)
      · simp at h
    · simp at h
  · simp at h

theorem eo_xchgAtF {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i : At} {p : List Nat} {v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.xchgAtF b i p v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi hv
    split at h
    · split at h
      · split at h
        · simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
          obtain ⟨⟨s1, old⟩, hin, s2, hst, rfl, rfl, rfl⟩ := h
          exact e3_ldst hin hst hs (e3_pw he hb) (evalAt_V he hv)
        · simp at h
      · simp at h
    · simp at h
  · simp at h

theorem eo_loadAtF {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i : At} {p : List Nat}
    (h : (s', t, ws) ∈ evalOp g env σs s (.loadAtF b i p)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i hb hi
    split at h
    · split at h
      · split at h
        · simp only [List.mem_map, Prod.mk.injEq] at h
          obtain ⟨⟨s1, old⟩, hin, rfl, rfl, rfl⟩ := h
          exact e3_load hin hs (e3_pw he hb)
        · simp at h
      · simp at h
    · simp at h
  · simp at h

#print axioms eo_xchg
#print axioms eo_ldl
#print axioms eo_ldlw
#print axioms eo_stl
#print axioms eo_stlw
#print axioms eo_xchgAt
#print axioms eo_loadAt
#print axioms eo_xchgAtF
#print axioms eo_loadAtF

end TermViewInv

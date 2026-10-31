import WeakCore.TermViewInvD0

/-!
# TermViewInvE2: `evalOp` cases for sums, allocation, publication, memory access, buffers
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem eo_inl {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {other : Ty} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.inl other a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 ws0 hx
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨s1, j, p⟩, h1, ⟨s2, q⟩, h2, he'⟩ := h
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, -, rfl⟩ := he'
    obtain ⟨a1, a2, a3⟩ := projM_V h1 hs (evalAt_V he hx)
    obtain ⟨b1, b2, b3⟩ := injM_V h2 a1 (by rw [a2]; exact a3)
    exact ⟨b1, by rw [← a2]; exact b2, b3⟩
  · cases h

theorem eo_inr {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {other : Ty} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.inr other a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 ws0 hx
    simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨⟨s1, j, p⟩, h1, ⟨s2, q⟩, h2, he'⟩ := h
    simp only [Prod.mk.injEq] at he'
    obtain ⟨rfl, -, rfl⟩ := he'
    obtain ⟨a1, a2, a3⟩ := projM_V h1 hs (evalAt_V he hx)
    obtain ⟨b1, b2, b3⟩ := injM_V h2 a1 (by rw [a2]; exact a3)
    exact ⟨b1, by rw [← a2]; exact b2, b3⟩
  · cases h

theorem eo_new {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {a : At} {T : Option Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.new a T)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · cases h
  · rename_i t0 ws0 hx
    split at h
    · cases h
    · simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨⟨s1, pw⟩, h1, rfl, -, rfl⟩ := h
      obtain ⟨a1, a2, a3⟩ := alloc_V h1 hs (evalAt_V he hx)
      exact ⟨a1, a2, WsV_single a3⟩

theorem eo_publish {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.publish a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨t0, ws0⟩, hx, h⟩ := h
  have hw := evalAt_V he hx
  split at h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_fence hs _ hw
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_fence hs _ hw
  · cases h

theorem eo_intoRgn {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {r : String} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.intoRgn r a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨t0, ws0⟩, hx, h⟩ := h
  have hw := evalAt_V he hx
  split at h
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_fence hs _ hw
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_fence hs _ hw
  · cases h

theorem eo_fence {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {f : Fence}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fence f)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact concl_fence hs _ (WsV_nil _)

theorem eo_load {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {acq : Bool} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.load acq a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 pw hx
    split at h
    · rename_i u b _ hb
      split at h
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨s1, ws1⟩, h1, rfl, -, rfl⟩ := h
        have hpw := evalAt_V he hx pw (by simp)
        obtain ⟨a1, a2, a3⟩ := loadUnits_V _ _ _ _ _ h1 hs hpw
        exact ⟨a1, by rw [a2]; exact Nat.le_refl _, by rw [a2]; exact a3⟩
      · cases h
    · cases h
  · cases h

theorem eo_store {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {rel : Bool} {a v : At} {tok : Option At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.store rel a v tok)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 pw t1 ws1 hx hv
    split at h
    · split at h
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨s1, h1, rfl, -, rfl⟩ := h
        have hpw := evalAt_V he hx pw (by simp)
        obtain ⟨a1, a2⟩ := storeUnits_V _ _ _ _ _ h1 hs hpw (evalAt_V he hv)
        exact ⟨a1, a2, WsV_nil _⟩
      · cases h
    · cases h
  · cases h

theorem eo_ldp {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {acq : Bool} {a : At} {n0 n1 : String}
    (h : (s', t, ws) ∈ evalOp g env σs s (.ldp acq a n0 n1)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 pw hx
    split at h
    · split at h
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨⟨s1, ws1⟩, h1, rfl, -, rfl⟩ := h
        have hpw := evalAt_V he hx pw (by simp)
        obtain ⟨a1, a2, a3⟩ := loadUnits_V _ _ _ _ _ h1 hs hpw
        exact ⟨a1, by rw [a2]; exact Nat.le_refl _, by rw [a2]; exact a3⟩
      · cases h
    · cases h
  · cases h

theorem eo_stp {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {rel : Bool} {a v0 v1 tok : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.stp rel a v0 v1 tok)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 pw t1 w0 t2 w1 hx hv0 hv1
    split at h
    · simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨s1, h1, rfl, -, rfl⟩ := h
      have hpw := evalAt_V he hx pw (by simp)
      obtain ⟨a1, a2⟩ := storeUnits_V _ _ _ _ _ h1 hs hpw
        (WsV_append (evalAt_V he hv0) (evalAt_V he hv1))
      exact ⟨a1, a2, WsV_nil _⟩
    · cases h
  · cases h

theorem eo_fetch {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {o : FetchOp} {acq rel : Bool} {a v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fetch o acq rel a v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 pw t1 nw hx hv
    split at h
    · simp only [List.mem_map, Prod.mk.injEq] at h
      obtain ⟨⟨mem', th'⟩, h1, rfl, -, rfl⟩ := h
      have hpw := evalAt_V he hx pw (by simp)
      have hnw := evalAt_V he hv nw (by simp)
      obtain ⟨a1, a2, a3, a4, -⟩ := stepRmw_V hs.1 hs.2 (mth_regs hpw hnw hnw) h1
      exact ⟨⟨a1, a3⟩, a2, WsV_single a4⟩
    · cases h
  · cases h

theorem eo_newBuf {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {n : At} {τ : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.newBuf n τ)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨⟨t0, ws0⟩, hx, k, hk, us, hus, h⟩ := h
  obtain ⟨rfl, -, rfl⟩ := h
  obtain ⟨a1, a2, a3⟩ := allocBuf_V (lbl := freshLabel g.lbase g.n g.i s.nalloc)
    (n := k * nWords us) (z := if zeroableIn [] [] (close σs τ) = true then zeroWords (close σs τ) else none) hs
  exact ⟨a1, a2, WsV_single a3⟩

theorem eo_bufInit {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word}
    {b i v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.bufInit b i v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · rename_i t0 pw t1 iws t2 xs hx hi hv
    split at h
    · split at h
      · simp only [List.mem_map, Prod.mk.injEq] at h
        obtain ⟨s1, h1, rfl, -, rfl⟩ := h
        have hpw := evalAt_V he hx pw (by simp)
        obtain ⟨a1, a2⟩ := storeUnits_V _ _ _ _ _ h1 hs hpw (evalAt_V he hv)
        exact ⟨a1, a2, WsV_single (hpw.mono a2)⟩
      · cases h
    · cases h
  · cases h

#print axioms eo_inl
#print axioms eo_inr
#print axioms eo_new
#print axioms eo_publish
#print axioms eo_intoRgn
#print axioms eo_fence
#print axioms eo_load
#print axioms eo_store
#print axioms eo_ldp
#print axioms eo_stp
#print axioms eo_fetch
#print axioms eo_newBuf
#print axioms eo_bufInit

end TermViewInv

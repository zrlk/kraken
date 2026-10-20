import WeakCore.TermViewInvD0

/-!
# TermViewInvF: a thread step keeps `MsgV` and the thread's `ThV`
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- A thread: its environment, every saved frame's environment, and its scalar views. -/
def ThV (n : Nat) (th : TTh) : Prop :=
  EnvV n th.env ∧ (∀ fr ∈ th.stack, EnvV n fr.env) ∧ VSB n th.vs

theorem ThV.mono {n n' : Nat} {th : TTh} (h : ThV n th) (hn : n ≤ n') : ThV n' th :=
  ⟨h.1.mono hn, fun fr hf => (h.2.1 fr hf).mono hn, h.2.2.mono hn⟩

/-- Every operation keeps `StV` and yields `WV` words (`evalOp_V`, assembled from the `eo_*`). -/
def OpV : Prop := ∀ {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {op : Op},
  (s', t, ws) ∈ evalOp g env σs s op → StV s → EnvV s.mem.size env → Concl s s' ws

theorem EnvV_cons {n : Nat} {x : String} {t : Ty} {ws : List Word} {env : Env} (hw : WsV n ws) (he : EnvV n env) :
    EnvV n ((x, t, ws) :: env) := by
  intro e hm
  rcases List.mem_cons.1 hm with rfl | hm
  · exact hw
  · exact he e hm

theorem WsV_take {n : Nat} {ws : List Word} (h : WsV n ws) (k : Nat) : WsV n (ws.take k) :=
  fun w hw => h w (List.mem_of_mem_take hw)

theorem WsV_drop {n : Nat} {ws : List Word} (h : WsV n ws) (k : Nat) : WsV n (ws.drop k) :=
  fun w hw => h w (List.mem_of_mem_drop hw)

theorem enter_V {n : Nat} {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') (ht : ThV n th) : ThV n th' := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨d, -, ⟨t, ws⟩, hev, rfl⟩ := h
  exact ⟨EnvV_cons (evalAt_V ht.1 hev) (fun _ h => by cases h), ht.2.1, ht.2.2⟩

theorem callFrame_env {g : G} {th : TTh} {f : String} {ts : List Ty} {x : String} {e : Expr} {fr : Frame}
    (h : callFrame g th f ts x e = some fr) : fr.env = th.env := by
  unfold callFrame at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨d, -, rfl⟩ := h
  rfl

theorem ThV_push {n : Nat} {th : TTh} {fr : Frame} (ht : ThV n th) (hf : fr.env = th.env) :
    ThV n { th with stack := fr :: th.stack } := by
  refine ⟨ht.1, ?_, ht.2.2⟩
  intro fr' hm
  rcases List.mem_cons.1 hm with rfl | hm
  · rw [hf]; exact ht.1
  · exact ht.2.1 fr' hm

theorem tstep_V (hop : OpV) {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) (hm : MsgV mem) (ht : ThV mem.size th) :
    MsgV r.1 ∧ mem.size ≤ r.1.size ∧ ThV r.1.size r.2.2 := by
  have hs : StV (stOf mem pairs th) := ⟨hm, ht.2.2⟩
  unfold tstep at h
  cases hterm : th.term with
  | let_ x op e =>
    rw [hterm] at h
    cases op
    case call f is a ts =>
      simp only [mem_ol, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
      obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := h
      exact ⟨hm, Nat.le_refl _, enter_V hen (ThV_push ht (callFrame_env hfr))⟩
    case callc f a =>
      simp only at h
      split at h
      · rename_i tf w _
        split at h
        · split at h
          · simp only [mem_ol, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
            obtain ⟨th', ⟨fr, hfr, hen⟩, rfl⟩ := h
            refine ⟨hm, Nat.le_refl _, enter_V hen ?_⟩
            refine ⟨ht.1, ?_, ht.2.2⟩
            intro fr' hm'
            rcases List.mem_cons.1 hm' with rfl | hm'
            · show EnvV _ fr.env; rw [callFrame_env hfr]; exact ht.1
            · exact ht.2.1 fr' hm'
          · cases h
        · cases h
      · cases h
    all_goals
      simp only [List.mem_map] at h
      obtain ⟨⟨s', t, ws⟩, hin, rfl⟩ := h
      obtain ⟨h1, h2, h3⟩ := hop hin hs ht.1
      exact ⟨h1.1, h2, EnvV_cons h3 (ht.1.mono h2), fun fr hf => (ht.2.1 fr hf).mono h2, h1.2⟩
  | split a x y e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i u w ws hev
      split at h
      · rw [List.mem_singleton] at h; subst h
        have hw := evalAt_V ht.1 hev
        exact ⟨hm, Nat.le_refl _, EnvV_cons (WsV_drop hw _) (EnvV_cons (WsV_take hw _) ht.1), ht.2.1, ht.2.2⟩
      · cases h
    · cases h
  | unpack a i x e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i b ws hev
      rw [List.mem_singleton] at h; subst h
      exact ⟨hm, Nat.le_refl _, EnvV_cons (evalAt_V ht.1 hev) ht.1, ht.2.1, ht.2.2⟩
    · cases h
  | unpackT a α x e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i _ b ws hev
      rw [List.mem_singleton] at h; subst h
      exact ⟨hm, Nat.le_refl _, EnvV_cons (evalAt_V ht.1 hev) ht.1, ht.2.1, ht.2.2⟩
    · cases h
  | region a r' p' t' e =>
    rw [hterm] at h
    simp only at h
    obtain ⟨f1, f2⟩ := fenceS_V hs .st
    split at h
    · rename_i _ u ws hev
      rw [List.mem_singleton] at h; subst h
      refine ⟨by rw [f2]; exact hm, by rw [f2]; exact Nat.le_refl _, ?_⟩
      rw [f2]
      exact ⟨EnvV_cons (WsV_nil _) (EnvV_cons (evalAt_V ht.1 hev) ht.1), ht.2.1, f1.2⟩
    · rename_i _ u ψ ws hev
      rw [List.mem_singleton] at h; subst h
      refine ⟨by rw [f2]; exact hm, by rw [f2]; exact Nat.le_refl _, ?_⟩
      rw [f2]
      exact ⟨EnvV_cons (WsV_nil _) (EnvV_cons (evalAt_V ht.1 hev) ht.1), ht.2.1, f1.2⟩
    · cases h
  | openPub a r' p' c' e =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i _ u ws hev
      rw [List.mem_singleton] at h; subst h
      exact ⟨hm, Nat.le_refl _, EnvV_cons (WsV_nil _) (EnvV_cons (evalAt_V ht.1 hev) ht.1), ht.2.1, ht.2.2⟩
    · cases h
  | case a x e₁ y e₂ =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i u w ws hev
      simp only [List.mem_flatMap, List.mem_map] at h
      obtain ⟨⟨s1, j, p⟩, hp1, ⟨s2, q⟩, hq, rfl⟩ := h
      obtain ⟨g1, g2, g3⟩ := projM_V hp1 hs (evalAt_V ht.1 hev)
      have hp' : WsV s1.mem.size p := by rw [g2]; exact g3
      split at hq
      all_goals
        obtain ⟨k1, k2, k3⟩ := injM_V hq g1 hp'
        have hle : mem.size ≤ s2.mem.size := by
          have := g2 ▸ k2
          exact this
        exact ⟨k1.1, hle, EnvV_cons k3 (ht.1.mono hle), fun fr hf => (ht.2.1 fr hf).mono hle, k1.2⟩
    · cases h
  | ifnull a e₁ y e₂ =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i μ u w hev
      split at h
      · rw [List.mem_singleton] at h; subst h; exact ⟨hm, Nat.le_refl _, ht⟩
      · rw [List.mem_singleton] at h; subst h
        exact ⟨hm, Nat.le_refl _, EnvV_cons (evalAt_V ht.1 hev) ht.1, ht.2.1, ht.2.2⟩
      · cases h
    · cases h
  | parity a k ev od =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · rw [List.mem_singleton] at h; subst h; exact ⟨hm, Nat.le_refl _, ht⟩
      · cases h
    · cases h
  | ifeq a b yes no =>
    rw [hterm] at h
    simp only at h
    split at h
    · split at h
      · rw [List.mem_singleton] at h; subst h; exact ⟨hm, Nat.le_refl _, ht⟩
      · cases h
    · cases h
  | cas acq rel w e v t ok fail =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i _ pw _ ew _ nw hw he hv
      split at h
      · simp only [List.mem_map] at h
        obtain ⟨⟨mem', th'⟩, hin, rfl⟩ := h
        have hpw : WV mem.size pw := evalAt_V ht.1 hw pw (by simp)
        have hnw : WV mem.size nw := evalAt_V ht.1 hv nw (by simp)
        obtain ⟨h1, h2, h3, -, -⟩ := stepRmw_V (th := mth (stOf mem pairs th) pw nw nw) hm (show VSB mem.size th.vs from hs.2) (mth_regs hpw hnw hnw) hin
        refine ⟨h1, h2, ?_⟩
        dsimp only
        split
        · exact ⟨EnvV_cons (WsV_nil _) (ht.1.mono h2), fun fr hf => (ht.2.1 fr hf).mono h2, h3⟩
        · exact ⟨ht.1.mono h2, fun fr hf => (ht.2.1 fr hf).mono h2, h3⟩
      · cases h
    · cases h
  | casp acq rel w e0 e1 v0 v1 t ok fail =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i _ pw _ x0 _ x1 _ n0 _ n1 hw h0 h1 hv0 hv1
      split at h
      · simp only [List.mem_map] at h
        obtain ⟨⟨mem', pairs', th'⟩, hin, rfl⟩ := h
        have hpw : WV mem.size pw := evalAt_V ht.1 hw pw (by simp)
        have hn0 : WV mem.size n0 := evalAt_V ht.1 hv0 n0 (by simp)
        have hn1 : WV mem.size n1 := evalAt_V ht.1 hv1 n1 (by simp)
        obtain ⟨k1, k2, k3, -, -, -⟩ := stepRmwPair_V (th := mth (stOf mem pairs th) pw n0 n1) hm (show VSB mem.size th.vs from hs.2) (mth_regs hpw hn0 hn1) hin
        refine ⟨k1, k2, ?_⟩
        dsimp only
        split
        · exact ⟨EnvV_cons (WsV_nil _) (ht.1.mono k2), fun fr hf => (ht.2.1 fr hf).mono k2, k3⟩
        · exact ⟨ht.1.mono k2, fun fr hf => (ht.2.1 fr hf).mono k2, k3⟩
      · cases h
    · cases h
  | ret a =>
    rw [hterm] at h
    simp only at h
    split at h
    · rename_i f rest _ ws hst hev
      rw [List.mem_singleton] at h; subst h
      refine ⟨hm, Nat.le_refl _, EnvV_cons (evalAt_V ht.1 hev) (ht.2.1 f (by rw [hst]; simp)), ?_, ht.2.2⟩
      intro fr hf
      exact ht.2.1 fr (by rw [hst]; exact List.mem_cons_of_mem _ hf)
    · cases h
  | tail f is a ts =>
    rw [hterm] at h
    simp only [mem_ol, Option.map_eq_some_iff] at h
    obtain ⟨th', hen, rfl⟩ := h
    exact ⟨hm, Nat.le_refl _, enter_V hen ht⟩

end TermViewInv

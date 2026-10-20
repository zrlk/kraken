import WeakCore.TermViewInvD0

/-!
# TermViewInvE1: `evalOp` preserves the view invariant (pure / non-memory cases)
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem eo_atom {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.atom a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (evalAt_V he hp)
theorem eo_pair {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.pair a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, q, hq, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_append (evalAt_V he hp) (evalAt_V he hq))
theorem eo_add {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.add a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, -, q, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_same hs (WsV_single (WV_addW _ _))
  · simp at h
theorem eo_sub {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.sub a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, -, q, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_same hs (WsV_single (WV_subW _ _))
  · simp at h
theorem eo_null {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {μ : Mode} {target : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.null μ target)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_fold {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At} {target : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fold a target)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (evalAt_V he hp)
theorem eo_fld {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {i : Nat} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fld i a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨p, hp, h⟩ := h
  have hw := evalAt_V he hp
  split at h
  · rename_i w heq
    rw [heq] at hw
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨c, -, h⟩ := h
    split at h
    · split at h
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, rfl⟩ := h
          exact concl_same hs (WsV_single (WV_with (WsV_of_eq hw rfl) _))
        · simp at h
      · simp only [Option.bind_eq_some_iff] at h
        obtain ⟨_, -, h⟩ := h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -, rfl⟩ := h
          exact concl_same hs (WsV_single (WV_with (WsV_of_eq hw rfl) _))
        · simp at h
    · simp at h
  · simp at h
theorem eo_mkWord {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {r : String} {P : Proto} {v tok : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.mkWord r P v tok)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_same hs (WsV_nil _)
  · simp only [mem_ol, Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨p, hp, rfl, -, rfl⟩ := h
    exact concl_same hs (evalAt_V he hp)
theorem eo_mkWord2 {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {r : String} {P : Proto2} {v0 v1 tok : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.mkWord2 r P v0 v1 tok)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, q, hq, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_append (evalAt_V he hp) (evalAt_V he hq))
theorem eo_mkEPair {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {r : String} {P : ECounter} {v0 v1 : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.mkEPair r P v0 v1)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, q, hq, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_append (evalAt_V he hp) (evalAt_V he hq))
theorem eo_mkTicket {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {r : String} {N P : Proto} {v tok : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.mkTicket r N P v tok)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_append (evalAt_V he hp) (evalAt_V he hp))
theorem eo_claim {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a tok : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.claim a tok)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_nil _)
theorem eo_pack {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At} {w : String} {target : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.pack a w target)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (evalAt_V he hp)
theorem eo_packT {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At} {σ : Ty} {target : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.packT a σ target)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (evalAt_V he hp)
theorem eo_validate {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {x : String}
    (h : (s', t, ws) ∈ evalOp g env σs s (.validate x)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (lookupE_V he hp)
theorem eo_call {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {f : String} {is : List String} {a : At} {ts : List Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.call f is a ts)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp [evalOp] at h
theorem eo_borrow {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {sc : Cap} {tk : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.borrow sc tk)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_nil _)
theorem eo_freeze {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {tk : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.freeze tk)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_nil _)
theorem eo_endBorrow {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {tk : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.endBorrow tk)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_nil _)
theorem eo_fnptr {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {f : String}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fnptr f)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp] at h
  split at h
  · simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_same hs (WsV_single (WV_cst _ _))
  · simp at h
theorem eo_callc {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {f a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.callc f a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp [evalOp] at h
theorem eo_rem {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a n : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.rem a n)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
  split at h
  · simp at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_nameI {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.nameI a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨p, hp, rfl, -, rfl⟩ := h
  exact concl_same hs (evalAt_V he hp)
theorem eo_cvt {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {sg : Bool} {w : Wd} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.cvt sg w a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_toInt {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.toInt a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_asLanes {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {sg : Bool} {w : Wd} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.asLanes sg w a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_fop {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {o : FOp} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fop o a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_fcmp {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {o : FCmp} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fcmp o a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_fop1 {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {o : FOp1} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.fop1 o a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_lane {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a j : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.lane a j)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_setLane {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a j v : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.setLane a j v)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_bits {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {o : BitOp} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.bits o a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_bit1 {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {o : BitOp1} {a : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.bit1 o a)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_vmatch {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {lo hi b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.vmatch lo hi b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_band {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a m : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.band a m)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨_, -, _, -, _, -, _, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_single (WV_cst _ _))
theorem eo_zero {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {τ : Ty}
    (h : (s', t, ws) ∈ evalOp g env σs s (.zero τ)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq,
    Prod.mk.injEq, Option.map_eq_some_iff] at h
  obtain ⟨z, -, rfl, -, rfl⟩ := h
  exact concl_same hs (WsV_map_cst _)
theorem eo_idx {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {b i : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.idx b i)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws := by
  simp only [evalOp, mem_ol, Option.bind_eq_bind, Option.bind_eq_some_iff, pure] at h
  obtain ⟨p, hp, h⟩ := h
  have hw := evalAt_V he hp
  split at h
  · rename_i w heq
    rw [heq] at hw
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      exact concl_same hs (WsV_single (WV_with (WsV_of_eq hw rfl) _))
    · simp at h
  · simp at h
end TermViewInv

#print axioms TermViewInv.eo_atom
#print axioms TermViewInv.eo_pair
#print axioms TermViewInv.eo_add
#print axioms TermViewInv.eo_sub
#print axioms TermViewInv.eo_null
#print axioms TermViewInv.eo_fold
#print axioms TermViewInv.eo_fld
#print axioms TermViewInv.eo_mkWord
#print axioms TermViewInv.eo_mkWord2
#print axioms TermViewInv.eo_mkEPair
#print axioms TermViewInv.eo_mkTicket
#print axioms TermViewInv.eo_claim
#print axioms TermViewInv.eo_pack
#print axioms TermViewInv.eo_packT
#print axioms TermViewInv.eo_validate
#print axioms TermViewInv.eo_call
#print axioms TermViewInv.eo_borrow
#print axioms TermViewInv.eo_freeze
#print axioms TermViewInv.eo_endBorrow
#print axioms TermViewInv.eo_fnptr
#print axioms TermViewInv.eo_callc
#print axioms TermViewInv.eo_rem
#print axioms TermViewInv.eo_nameI
#print axioms TermViewInv.eo_cvt
#print axioms TermViewInv.eo_toInt
#print axioms TermViewInv.eo_asLanes
#print axioms TermViewInv.eo_fop
#print axioms TermViewInv.eo_fcmp
#print axioms TermViewInv.eo_fop1
#print axioms TermViewInv.eo_lane
#print axioms TermViewInv.eo_setLane
#print axioms TermViewInv.eo_bits
#print axioms TermViewInv.eo_bit1
#print axioms TermViewInv.eo_vmatch
#print axioms TermViewInv.eo_band
#print axioms TermViewInv.eo_zero
#print axioms TermViewInv.eo_idx

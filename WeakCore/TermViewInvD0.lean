import WeakCore.TermViewInvC

/-!
# TermViewInvD0: the per-operation statement

`Concl s s' ws`: the post-state keeps `StV`, memory grows, and the result words are `WV`.
Each `evalOp` case is a lemma `eo_<op>` of the shape

```
theorem eo_pair {g : G} {env : Env} {σs : List Ty} {s s' : St} {t : Ty} {ws : List Word} {a b : At}
    (h : (s', t, ws) ∈ evalOp g env σs s (.pair a b)) (hs : StV s) (he : EnvV s.mem.size env) :
    Concl s s' ws
```
-/

namespace TermViewInv
open CoreLang CoreTerm TermRun
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

theorem mem_ol {α : Type} {x : α} {o : Option α} : x ∈ ol o ↔ o = some x := by
  cases o <;> simp [ol, eq_comm]

/-- The per-operation conclusion. -/
abbrev Concl (s s' : St) (ws : List Word) : Prop := StV s' ∧ s.mem.size ≤ s'.mem.size ∧ WsV s'.mem.size ws

theorem concl_same {s : St} {ws : List Word} (hs : StV s) (hw : WsV s.mem.size ws) : Concl s s ws :=
  ⟨hs, Nat.le_refl _, hw⟩

theorem concl_fence {s : St} {ws : List Word} (hs : StV s) (f : WeakMem.Fence) (hw : WsV s.mem.size ws) :
    Concl s (fenceS s f) ws := by
  obtain ⟨h1, h2⟩ := fenceS_V hs f
  exact ⟨h1, by rw [h2]; exact Nat.le_refl _, by rw [h2]; exact hw⟩

theorem WV_addW {n : Nat} (x y : Word) : WV n (addW x y) := by
  unfold addW; split <;> exact WV_cst _ _

theorem WV_subW {n : Nat} (x y : Word) : WV n (subW x y) := by
  unfold subW; split <;> exact WV_cst _ _

theorem WsV_single {n : Nat} {w : Word} (h : WV n w) : WsV n [w] := WsV_cons h (WsV_nil _)

theorem WsV_map_cst {n : Nat} (vs : List Val) : WsV n (vs.map cst) := by
  intro w hw
  obtain ⟨v, -, rfl⟩ := List.mem_map.1 hw
  exact WV_cst _ _

theorem WsV_of_eq {n : Nat} {ws : List Word} (h : WsV n ws) {w : Word} (hw : ws = [w]) : WV n w :=
  h w (by rw [hw]; simp)

/-- Concl composes: a later step from a state reached by an earlier one. -/
theorem Concl.trans {s s1 s2 : St} {ws1 ws2 : List Word} (h1 : Concl s s1 ws1) (h2 : Concl s1 s2 ws2) :
    Concl s s2 ws2 :=
  ⟨h2.1, Nat.le_trans h1.2.1 h2.2.1, h2.2.2⟩

end TermViewInv

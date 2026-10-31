import WeakCore.TermPtrKey
import WeakCore.TermInterf
import WeakCore.TermPromClos

/-!
# TermPtrRtsThr: the staging package `PtrRtsGL` across a thread step

* `alloc_noFulfil` — a thread step that allocates (raises `nalloc`) discharges no promise (an
  allocation keeps every promise: `alloc_keep`/`allocBuf_keep`/`injM_keep`; every other operation
  leaves `nalloc` unchanged).
-/

namespace TermPtrRtsThr

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermMain TermInterf TermPlantF TermPromClos TermCert TermFul TermTyped
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- No promise discharged across `s → s'` when `nalloc` rises. -/
def NoFulA (s s' : St) : Prop :=
  s.nalloc < s'.nalloc → ∀ t, t ∈ s.promises → t < s.mem.size → t ∈ s'.promises

theorem noFulA_keep {s s' : St} (h : KeepR s s') : NoFulA s s' := fun _ t ht hl => h.2.2 t ht hl

theorem noFulA_eq {s s' : St} (h : s'.nalloc = s.nalloc) : NoFulA s s' := fun hl => by
  rw [h] at hl; exact absurd hl (Nat.lt_irrefl _)

theorem evalOp_noFulA {g : G} {env : Env} {σs : List Ty} {s : St} {op : Op}
    {r : St × Ty × List Word} (h : r ∈ evalOp g env σs s op) : NoFulA s r.1 := by
  cases op <;> simp only [evalOp] at h
  all_goals (try simp only [ol, bind, Option.bind, pure, Option.map] at h)
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h
       first | exact noFulA_eq rfl | exact noFulA_keep allocBuf_keep)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact noFulA_eq (loadUnits_nallocT _ _ _ _ hx)
         | exact noFulA_eq (storeUnits_nallocT _ _ _ _ _ hx)
         | exact noFulA_keep (alloc_keep hx)
         | exact noFulA_eq rfl)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       first
         | exact noFulA_keep ((keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy))
         | exact noFulA_eq ((storeUnits_nallocT _ _ _ _ _ hy).trans (loadUnits_nallocT _ _ _ _ hx)))
    | (simp only [List.mem_flatMap] at h
       obtain ⟨x, hx, h⟩ := h
       split at h
       · simp only [List.mem_map] at h
         obtain ⟨y, hy, rfl⟩ := h
         exact noFulA_eq ((storeUnits_nallocT _ _ _ _ _ hy).trans (loadUnits_nallocT _ _ _ _ hx))
       · simp at h)
    | (simp only [List.mem_filterMap] at h
       obtain ⟨x, hx, h⟩ := h
       cases hn : numOf x.2 <;> simp [hn] at h
       subst h; exact noFulA_eq (loadUnits_nallocT _ _ _ _ hx))
    | (simp only [Option.toList, List.mem_cons, List.not_mem_nil, or_false] at h
       subst h; dsimp only; exact noFulA_keep allocBuf_keep)

/-- **`alloc_noFulfil`**: a thread step raising the allocation count discharges no promise. -/
theorem alloc_noFulfil {g : G} {mem : Memory} {pairs : List Ts} {th : TTh}
    {r : Memory × List Ts × TTh} (h : r ∈ tstep g mem pairs th) :
    NoFulA (stOf mem pairs th) (stOf r.1 r.2.1 r.2.2) := by
  simp only [tstep] at h
  split at h
  all_goals (repeat' (first | (split at h) | (dsimp only at h; split at h)))
  all_goals first
    | (simp at h; done)
    | (simp only [List.mem_singleton] at h; subst h; exact noFulA_eq rfl)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff, Option.bind_eq_some_iff] at h
       obtain ⟨th', ⟨fr, -, he⟩, rfl⟩ := h
       exact noFulA_eq (enter_nallocT he).2)
    | (simp only [ol, Option.mem_toList, Option.map_eq_some_iff] at h
       obtain ⟨th', he, rfl⟩ := h
       exact noFulA_eq (enter_nallocT he).2)
    | (simp only [List.mem_map] at h
       obtain ⟨x, hx, rfl⟩ := h
       first
         | exact evalOp_noFulA hx
         | exact noFulA_eq rfl)
    | (simp only [List.mem_flatMap, List.mem_map] at h
       obtain ⟨x, hx, y, hy, rfl⟩ := h
       exact noFulA_keep ((keepR_eq (projM_keep hx).1 (projM_keep hx).2.2).trans (injM_keep hy)))
    | (simp only [List.mem_map] at h  -- new arm: record write
       obtain ⟨x, hx, rfl⟩ := h
       try dsimp only
       split
       all_goals
         first
           | exact evalOp_noFulA hx
           | exact noFulA_eq rfl)

end TermPtrRtsThr

#print axioms TermPtrRtsThr.alloc_noFulfil

import WeakCore.TermRun
/-! # TermTidLbl — (E2) a thread step keeps the thread's `ThreadId` box label (`tstep_tidLbl`). -/
namespace TermTidLbl
open TermRun CoreLang CoreTerm
open WeakMem (Memory Ts)

theorem enter_tidLbl {g : G} {th th' : TTh} {f : String} {ts : List Ty} {a : At}
    (h : enter g th f ts a = some th') : th'.tidLbl = th.tidLbl := by
  unfold enter at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨_, -, ⟨_, _⟩, -, rfl⟩ := h
  rfl

theorem tstep_tidLbl {g : G} {mem : Memory} {pairs : List Ts} {th : TTh} {r : Memory × List Ts × TTh}
    (hr : r ∈ tstep g mem pairs th) : r.2.2.tidLbl = th.tidLbl := by
  obtain ⟨m, ps, th'⟩ := r
  unfold tstep at hr
  dsimp only at hr
  repeat' split at hr
  all_goals first
    | (simp at hr; done)
    | (simp only [List.mem_singleton, Prod.mk.injEq] at hr; obtain ⟨-, -, rfl⟩ := hr; rfl)
    | (simp only [List.mem_map, Prod.mk.injEq] at hr; obtain ⟨_, -, -, -, rfl⟩ := hr; rfl)
    | (unfold ol at hr
       rw [Option.mem_toList] at hr
       simp only [Option.map_eq_some_iff, Option.bind_eq_some_iff, Prod.mk.injEq] at hr
       first
         | (obtain ⟨a, ⟨_, -, he⟩, -, -, rfl⟩ := hr; exact (enter_tidLbl he).trans rfl)
         | (obtain ⟨_, he, -, -, rfl⟩ := hr; exact enter_tidLbl he)
         | (obtain ⟨a, ⟨_, -, he⟩, -, -, h3⟩ := hr; subst h3; have := enter_tidLbl he; exact this))
    | (simp only [List.mem_map, List.mem_flatMap, Prod.mk.injEq] at hr
       first
         | (obtain ⟨_, -, -, -, rfl⟩ := hr; first | rfl | (simp only [withS]; split <;> rfl))
         | (obtain ⟨_, -, _, -, -, -, rfl⟩ := hr; first | rfl | (simp only [withS]; split <;> rfl)))
    | skip

end TermTidLbl

/-! (hygiene) axiom reports. -/
#print axioms TermTidLbl.enter_tidLbl
#print axioms TermTidLbl.tstep_tidLbl

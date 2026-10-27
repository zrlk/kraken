import WeakCore.TermLiveCert
/-! # TermLiveCertMoves — `movesPF` is exactly `machineE`'s thread-label moves

From a configuration whose thread `i` has no promise out, `movesPF … c i` contains every `mstepE … c (i, .thr)`
successor (`movesPF_complete`), and each of its elements with no promise of `i` out is one (`movesPF_sound`: a
promise-free successor is certified by `Solo.refl`). No bounded certification is involved. -/

namespace TermLiveCert
open CoreLang CoreTerm TermRun TermLiveMach TermLiveL3 TermProgress TermLiveProps TermSpawnStep TermExtStep
open WeakMem (Arch Address Val)

/-- A missing thread has no move. -/
theorem movesPF_none {p : Prog} {k : Promises.Knobs} {arch : Arch} {V : List Nat} {c : Cfg} {i : Nat} (h : c.ths[i]? = none) :
    movesPF p k arch V c i = [] := by
  simp [movesPF, threadSteps, extSuccs, TermSpawnSuccs.spawnSuccsAt, h]

theorem movesPF_out {p : Prog} {k : Promises.Knobs} {arch : Arch} {V : List Nat} {c : Cfg} {i : Nat} (h : c.ths.size ≤ i) :
    movesPF p k arch V c i = [] :=
  movesPF_none (Array.getElem?_eq_none h)

/-- An extern move of `extSuccs` at certification fuel `0` is an `ExtBy` move of the same thread. -/
theorem extSuccs0_extBy {p : Prog} {k : Promises.Knobs} {arch : Arch} {c e : Cfg} {i : Nat}
    {V : List Nat} (h : e ∈ extSuccs p k arch { solo := 0, io := V } c i) : ExtBy p k arch c i e := by
  unfold extSuccs at h
  cases hth : c.ths[i]? with
  | none => simp [hth] at h
  | some th =>
    simp only [hth] at h
    cases hterm : th.term with
    | let_ x op e' =>
      simp only [hterm] at h
      cases op with
      | ext n a =>
        simp only at h
        split at h
        · simp at h
        · rename_i hg
          cases hev : evalAt th.env a with
          | none => simp [hev] at h
          | some rw =>
            obtain ⟨rt, ws⟩ := rw
            simp only [hev, List.mem_map, List.mem_filter] at h
            obtain ⟨rs, ⟨hm, hc⟩, rfl⟩ := h
            refine ⟨x, n, a, e', th, rt, ws, rs, hth, hterm, fun hn => ?_, ?_, hev, extRs_admits hm,
              certB_sound _ _ _ hc, rfl⟩
            · cases hp : th.promises with
              | nil => rfl
              | cons t ts => exact absurd (by simp [hp, decide_eq_true hn]) hg
            · cases hd : decide (ExtEnabled n th) with
              | true => exact of_decide_eq_true hd
              | false => exact absurd (by simp [hd]) hg
      | _ => simp at h
    | _ => simp [hterm] at h

/-- A spawn move of `spawnSuccsAt` is a `SpawnBy` move of the same thread at the configuration's capacity. -/
theorem spawnSuccsAt_spawnBy {c e : Cfg} {i : Nat} (h : e ∈ TermSpawnSuccs.spawnSuccsAt c i) :
    SpawnBy c.cap c i e := by
  unfold TermSpawnSuccs.spawnSuccsAt at h
  split at h
  · rename_i th hth
    split at h
    · rename_i x f a T ts e' hterm
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at hc
        split at h
        · rename_i rt ws hev
          simp only [List.mem_singleton] at h
          subst h
          exact ⟨x, f, a, T, ts, e', th, rt, ws, hth, hterm, hc.1, hc.2, hev, rfl⟩
        · cases h
      · cases h
    · cases h
  · cases h

/-- **Soundness.** A move of `movesPF` after which thread `i` has no promise out is a `machineE` thread move. -/
theorem movesPF_sound {p : Prog} {k : Promises.Knobs} {arch : Arch} {V : List Nat} {c e : Cfg} {i : Nat}
    (h : e ∈ movesPF p k arch V c i) (he : noPromises e i = true) : mstepE p k arch c (i, .thr) e := by
  simp only [movesPF, List.mem_append] at h
  rcases h with (h | h) | h
  · exact Or.inl ⟨h, e, Solo.refl _, he⟩
  · exact Or.inr (Or.inr (extSuccs0_extBy h))
  · exact Or.inr (Or.inl (spawnSuccsAt_spawnBy h))

/-- **Completeness.** From a configuration where thread `i` has no promise out, every `machineE` thread move of
`i` is in `movesPF`. -/
theorem movesPF_complete {p : Prog} {k : Promises.Knobs} {arch : Arch} {V : List Nat} {c e : Cfg} {i : Nat}
    (hc : noPromises c i = true) (h : mstepE p k arch c (i, .thr) e)
    (hV : ∀ th x w a e', c.ths[i]? = some th → th.term = .let_ x (.ext (.devChoice w) a) e' →
      ∃ v, v ∈ V ∧ (e.ths[i]?).bind (·.env.head?) = some (x, (ExtName.devChoice w).sig.2, [cst (.num v)])) :
    e ∈ movesPF p k arch V c i := by
  simp only [movesPF, List.mem_append]
  rcases h with ⟨h1, -⟩ | ⟨x, f, a, T, ts, e', th, rt, ws, h1, h2, h3, h4, h5, rfl⟩ |
      ⟨x, n, a, e', th, rt, ws, rs, h1, h2, h3, hen, h4, hadm, h5, rfl⟩
  · exact Or.inl (Or.inl h1)
  · right
    simp [TermSpawnSuccs.spawnSuccsAt, h1, h2, h3, h4, h5]
  · left; right
    have hp : th.promises = [] := by simpa [noPromises, h1] using hc
    have hrs : rs ∈ extRs { solo := 0, io := V } n i ws c.trace := by
      cases n
      case devChoice w =>
        obtain ⟨v, hv, rfl⟩ := hadm
        obtain ⟨v', hv', hhd⟩ := hV th x w a e' h1 h2
        have hi : i < c.ths.size := (Array.getElem?_eq_some_iff.mp h1).1
        simp [wake, extCfg, hi, cst, Promises.TVal.mk0] at hhd
        subst hhd
        simp only [extRs, List.mem_map, List.mem_filter]
        exact ⟨v, ⟨hv', by simpa using hv⟩, rfl⟩
      all_goals exact (mem_resultsL _ _ _ _ _).2 hadm
    unfold extSuccs
    simp only [h1, h2, hp, List.isEmpty_nil, Bool.not_true, Bool.and_false, decide_eq_true hen, Bool.or_false,
      Bool.false_eq_true, ↓reduceIte, h4]
    exact List.mem_map.mpr ⟨rs, List.mem_filter.mpr ⟨hrs, by simp [certB, extCfg_noPromises h1, hp]⟩, rfl⟩

/-- (D4) **Env soundness.** A move of `wakesPF` from a configuration where thread `i` has no promise out is a
`machineE` environment move (a spurious wake). -/
theorem wakesPF_sound {p : Prog} {k : Promises.Knobs} {arch : Arch} {c e : Cfg} {i : Nat}
    (hc : noPromises c i = true) (h : e ∈ wakesPF p k arch c i) : mstepE p k arch c (i, .env) e := by
  unfold wakesPF wakeSuccs at h
  cases hth : c.ths[i]? with
  | none => simp [hth] at h
  | some th =>
    have hp : th.promises = [] := by simpa [noPromises, hth] using hc
    simp only [hth] at h
    cases hterm : th.term with
    | let_ x op e' =>
      simp only [hterm] at h
      cases op with
      | ext n a =>
        clear hp
        cases n
        case park =>
          simp only at h
          cases hpm : th.permit
          · simp only [hpm, Bool.false_eq_true, ↓reduceIte] at h
            cases hev : evalAt th.env a with
            | none => simp [hev] at h
            | some rw =>
              obtain ⟨rt, ws⟩ := rw
              rw [hev] at h
              dsimp only at h
              obtain ⟨hm, hcB⟩ := List.mem_filter.mp h
              rw [List.mem_singleton] at hm
              subst hm
              exact ⟨x, a, e', th, rt, ws, hth, hterm, hpm, hev, certB_sound _ _ _ hcB, rfl⟩
          · simp [hpm] at h
        all_goals simp at h
      | _ => simp at h
    | _ => simp [hterm] at h

/-- (D4) **Env completeness.** From a configuration where thread `i` has no promise out, every `machineE`
environment move of `i` is in `wakesPF`. -/
theorem wakesPF_complete {p : Prog} {k : Promises.Knobs} {arch : Arch} {c e : Cfg} {i : Nat}
    (hc : noPromises c i = true) (h : mstepE p k arch c (i, .env) e) : e ∈ wakesPF p k arch c i := by
  obtain ⟨x, a, e', th, rt, ws, h1, h2, hpm, h4, -, rfl⟩ := h
  have hp : th.promises = [] := by simpa [noPromises, h1] using hc
  unfold wakesPF wakeSuccs
  simp only [h1, h2, hpm, Bool.false_eq_true, ↓reduceIte, h4]
  simp [certB, extCfg_noPromises h1, hp]

end TermLiveCert

#print axioms TermLiveCert.movesPF_sound
#print axioms TermLiveCert.movesPF_complete
#print axioms TermLiveCert.movesPF_out
#print axioms TermLiveCert.wakesPF_sound
#print axioms TermLiveCert.wakesPF_complete

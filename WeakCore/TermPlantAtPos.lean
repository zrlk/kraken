import WeakCore.TermMainDefs
import WeakCore.TermLiveProps
import WeakCore.TermCert

/-! # TermPlantAtPos: outstanding promises are never message `0`

A reachable-configuration lemma (not a `SysInvN` clause): from a configuration with no
outstanding promise, every outstanding promise of every thread along a run is a positive index.
Thread steps only remove promises (`TermCert.tstep_appUp`); a promise step adds `c.mem.size`,
which is positive since the promised step requires `w < c.mem.size`.
-/

namespace TermPlantAtPos
open CoreLang CoreTerm TermRun TermStep TermMain
open WeakMem (Ts Arch Address)

/-- Every outstanding promise is a positive message index. -/
def PromPos (c : Cfg) : Prop := ∀ (i : Nat) (th : TTh), c.ths[i]? = some th → ∀ t ∈ th.promises, 0 < t

theorem promPos_init {c : Cfg} (h : AllNoProm c) : PromPos c := by
  intro i th hi t ht
  rw [h i th hi] at ht
  cases ht

theorem promPos_thread {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (h : c' ∈ threadSteps p k arch c i) (hc : PromPos c) : PromPos c' := by
  unfold threadSteps at h
  split at h
  · simp at h
  · rename_i th0 hth
    simp only [List.mem_map] at h
    obtain ⟨⟨mem, pairs, th'⟩, hin, rfl⟩ := h
    have hA := TermCert.tstep_appUp hin
    have hsub : ∀ t ∈ th'.promises, t ∈ th0.promises := hA.2.2.1
    intro j th hj t ht
    simp only [TermLiveProps.getElem?_set!] at hj
    by_cases e : i = j
    · subst e
      simp only [TermLiveProps.lt_of_get hth, ↓reduceIte, Option.some.injEq] at hj
      subst hj
      exact hc _ _ hth t (hsub t ht)
    · simp only [e, ↓reduceIte] at hj
      exact hc _ _ hj t ht

theorem promPos_promise {c : Cfg} {i : Nat} {a : Address} {v : WeakMem.Val} {w : Ts}
    (hw : w < c.mem.size) (hc : PromPos c) : PromPos (promise c i a v w) := by
  unfold promise
  split
  · exact hc
  · rename_i th0 hth
    intro j th hj t ht
    simp only [TermLiveProps.getElem?_set!] at hj
    by_cases e : i = j
    · subst e
      simp only [TermLiveProps.lt_of_get hth, ↓reduceIte, Option.some.injEq] at hj
      subst hj
      simp only [List.mem_append, List.mem_singleton] at ht
      cases ht with
      | inl ht => exact hc _ _ hth t ht
      | inr ht => subst ht; exact Nat.lt_of_le_of_lt (Nat.zero_le w) hw
    · simp only [e, ↓reduceIte] at hj
      exact hc _ _ hj t ht

theorem promPos_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (h : Step p k arch c c') (hc : PromPos c) : PromPos c' := by
  cases h with
  | thread i hs _ => exact promPos_thread hs hc
  | prom i a v w _ hw _ => exact promPos_promise hw hc

/-- **PromPos along runs**, given the `Sp`-arm. -/
theorem promPos_steps {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c c' : Cfg}
    (hSp : ∀ c c', Sp c c' → PromPos c → PromPos c')
    (h : TermSpawnStep.StepsG p k arch Sp c c') (hc : PromPos c) : PromPos c' :=
  TermSpawnStep.stepsG_pres (fun _ _ hs h1 => promPos_step hs h1) hSp h hc

/-- (2b, closed form) `PromPos` along every `StepsG … Sp` run from `c0`. -/
def PromPosR (p : Prog) (k : Promises.Knobs) (arch : Arch) (Sp : Cfg → Cfg → Prop) (c0 : Cfg) : Prop :=
  ∀ {c : Cfg}, TermSpawnStep.StepsG p k arch Sp c0 c → PromPos c

/-- From an initial configuration without promises (`Sp := ⊥`: `fun _ _ h => h.elim`). -/
theorem promPosR_of {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 : Cfg}
    (hSp : ∀ c c', Sp c c' → PromPos c → PromPos c') (h0 : AllNoProm c0) : PromPosR p k arch Sp c0 :=
  fun h => promPos_steps hSp h (promPos_init h0)
#print axioms TermPlantAtPos.promPosR_of


theorem promPos_run {p : Prog} {k : Promises.Knobs} {arch : Arch} {Sp : Cfg → Cfg → Prop} {c0 c : Cfg}
    (h : TermSpawnStep.StepsG p k arch Sp c0 c) (h0 : PromPosR p k arch Sp c0) : PromPos c := h0 h

end TermPlantAtPos

#print axioms TermPlantAtPos.promPos_steps
#print axioms TermPlantAtPos.promPos_run

import WeakCore.TermOverCrW
import WeakCore.TermTyped
import WeakCore.TermLiveProps
import WeakCore.TermUndefInv

/-! # TermPromAboveG: every thread's promises are above its coherence (derived clause)

`PromAbove` (`TermStep`) per thread, at every configuration.  The stepping thread gets it from
certification (`TermTyped.certified_promAboveSt`); every other thread keeps its state, and
memory only grows (`TermLiveProps.threadSteps_ext`, `promise_ext`), so its promises (old
messages, `AllPromLt`) name the same messages.
-/

namespace TermPromAboveG
open CoreLang CoreTerm TermRun TermStep TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

open TermOverCr (PromAboveG)

/-- Initially (no promises). -/
theorem promAboveG_noProm {c : Cfg} (h : AllNoProm c) : PromAboveG c := by
  intro j th hj t ht
  have e : th.promises = [] := h j th hj
  have ht' : t ∈ th.promises := ht
  rw [e] at ht'
  cases ht'

/-- An idle thread keeps `PromAbove` when memory only grows. -/
theorem promAbove_idle {mem mem' : Memory} {pairs pairs' : List Ts} {th : TTh}
    (he : Promises.Sim.MemExt mem mem') (hlt : ∀ t, t ∈ th.promises → t < mem.size)
    (h : PromAbove (stOf mem pairs th)) : PromAbove (stOf mem' pairs' th) := by
  intro t ht m hm
  have ht' : t ∈ th.promises := ht
  have hl := hlt t ht'
  have h1 : mem[t]? = some mem[t] := Array.getElem?_eq_getElem hl
  have h2 := TermUndefInv.memExt_get he t _ h1
  have h3 : (stOf mem' pairs' th).mem[t]? = some mem[t] := h2
  rw [h3] at hm
  have e : mem[t] = m := Option.some.inj hm
  have h4 : (stOf mem pairs th).mem[t]? = some m := by rw [← e]; exact h1
  exact h t ht m h4

/-- **The transfer**: thread `i` steps into a certified configuration, every other thread is
unchanged and memory only grows. -/
theorem promAboveG_step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (he : Promises.Sim.MemExt c.mem c'.mem)
    (hoth : ∀ j th, j ≠ i → c'.ths[j]? = some th → c.ths[j]? = some th)
    (hcert : Certified p k arch c' i) (hlt : AllPromLt c) (h : PromAboveG c) : PromAboveG c' := by
  intro j th hj
  by_cases hji : j = i
  · subst hji
    exact TermTyped.certified_promAboveSt hcert hj
  · have hj0 := hoth j th hji hj
    exact promAbove_idle he (fun t ht => hlt j th t hj0 ht) (h j th hj0)

theorem threadSteps_oth {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg} {i : Nat}
    (hs : c' ∈ threadSteps p k arch c i) (j : Nat) (th : TTh) (hji : j ≠ i)
    (hj : c'.ths[j]? = some th) : c.ths[j]? = some th := by
  unfold threadSteps at hs
  split at hs
  · simp at hs
  · simp only [List.mem_map] at hs
    obtain ⟨⟨mem, pairs, th'⟩, -, rfl⟩ := hs
    rw [TermLiveProps.getElem?_set!] at hj
    have hij : ¬ i = j := fun h => hji h.symm
    simp only [hij, ↓reduceIte] at hj
    exact hj

theorem promise_oth {c : Cfg} {i : Nat} {a : Address} {v : WeakMem.Val} {w : Ts} (j : Nat)
    (th : TTh) (hji : j ≠ i) (hj : (promise c i a v w).ths[j]? = some th) : c.ths[j]? = some th := by
  unfold promise at hj
  split at hj
  · exact hj
  · rw [TermLiveProps.getElem?_set!] at hj
    have hij : ¬ i = j := fun h => hji h.symm
    simp only [hij, ↓reduceIte] at hj
    exact hj

/-- **`PromAboveG` along a machine step.** -/
theorem promAboveG_Step {p : Prog} {k : Promises.Knobs} {arch : Arch} {c c' : Cfg}
    (hs : Step p k arch c c') (hlt : AllPromLt c) (h : PromAboveG c) : PromAboveG c' := by
  cases hs with
  | thread i hs hc =>
      exact promAboveG_step (TermLiveProps.threadSteps_ext hs) (threadSteps_oth hs) hc hlt h
  | prom i a v w _ _ hc =>
      exact promAboveG_step (TermLiveProps.promise_ext c i a v w) (fun j th => promise_oth j th) hc
        hlt h

end TermPromAboveG

#print axioms TermPromAboveG.promAboveG_Step
#print axioms TermPromAboveG.promAboveG_noProm

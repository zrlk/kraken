/-
Observable faults and clean halting (`Kraken/Litmus/KNOWN_GAPS.md`,
"Faults and wild jumps are invisible to theorems").

`succsL` drops a faulting outcome into its fault list, so a run that faults
never becomes final, and `Thread.halted` (`exec = none`) also holds at a pc
with no directive, so `Config.final` counts a jump out of the text as
termination. This file names the two things a theorem about final
configurations does not see, without changing `halted`, `final`, `succs` or
`succsL`:

- `Config.FaultStep A c tid m`: the next instruction of thread `tid` at `c`
  has a fault outcome `m` (exactly the `.error m` outcomes `succsL` collects,
  `FaultStep.mem_succsL`);
- `Config.FaultFree A fuel init`: no reachable configuration has one;
- `Thread.cleanHalted atEnd t`: halted *at its end address*; `atEnd` is the
  ISA's "pc = endPc" test (the `ISA` interface has no pc, so it is a
  parameter; the per-ISA instances are `s.st.2 == s.endPc`, see
  `SLR/SwpFaults.lean`, `SLR/X64SpinFaults.lean`);
- `Config.cleanFinal`, `Config.WildFree A fuel init atEnd`: every halted
  thread of every reachable configuration halted cleanly.

No generic theorem is proved about them here; the two N = 2 lock instances
are checked with the explorer (`SLR/SwpFaults.lean`, `SLR/X64SpinFaults.lean`).
-/
import Kraken.Promising.Machine

namespace Kraken.Promising

variable {I : ISA}

/-! ## Clean halting -/

/-- The thread has halted at its end address (`atEnd`, the ISA's
"pc = endPc"), not by reaching a pc without a directive. -/
def Thread.cleanHalted (atEnd : I.State → Bool) (t : Thread I) : Prop :=
  t.halted = true ∧ atEnd t.st = true

/-- A final configuration in which every thread halted at its end address. -/
def Config.cleanFinal (atEnd : I.State → Bool) (c : Config I) : Prop :=
  c.final = true ∧ ∀ t ∈ c.threads, atEnd t.st = true

theorem Config.cleanFinal.final {atEnd : I.State → Bool} {c : Config I}
    (h : c.cleanFinal atEnd) : c.final = true := h.1

/-! ## Faulting steps -/

section Faults

variable (A : Arch)

/-- The fault messages of the next instruction of thread `tid` at `c`: the
`.error` outcomes of `stepThread`, in order (none if the thread does not
exist or has halted). -/
def Config.faultsAt (c : Config I) (tid : Nat) : List String :=
  match stepThread A c tid with
  | none => []
  | some outs => outs.filterMap fun | .error m => some m | .ok _ => none

/-- Thread `tid`'s next instruction at `c` has the fault outcome `m`. -/
def Config.FaultStep (c : Config I) (tid : Nat) (m : String) : Prop :=
  ∃ outs, stepThread A c tid = some outs ∧ (.error m : Except String (Outcome I)) ∈ outs

/-- No reachable configuration has a faulting step. -/
def Config.FaultFree (fuel : Nat) (init : Config I) : Prop :=
  ∀ c, Reachable A fuel init c → ∀ tid m, ¬ c.FaultStep A tid m

/-- Every halted thread of every reachable configuration halted at its end
address: no wild jump counts as termination. -/
def Config.WildFree (fuel : Nat) (init : Config I) (atEnd : I.State → Bool) : Prop :=
  ∀ c, Reachable A fuel init c → ∀ t ∈ c.threads, t.halted = true → t.cleanHalted atEnd

variable {A}

theorem Config.faultStep_iff_mem_faultsAt {c : Config I} {tid : Nat} {m : String} :
    c.FaultStep A tid m ↔ m ∈ c.faultsAt A tid := by
  unfold Config.FaultStep Config.faultsAt
  cases stepThread A c tid with
  | none => simp
  | some outs =>
    simp only [Option.some.injEq, exists_eq_left', List.mem_filterMap]
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨o, ho, he⟩
      cases o with
      | error m' => cases he; exact ho
      | ok _ => cases he

theorem Config.FaultStep.lt_size {c : Config I} {tid : Nat} {m : String}
    (h : c.FaultStep A tid m) : tid < c.threads.size := by
  obtain ⟨outs, hs, -⟩ := h
  simp only [stepThread] at hs
  cases ht : c.threads[tid]? with
  | none => simp [ht] at hs
  | some t => exact (Array.getElem?_eq_some_iff.mp ht).1

/-- The accumulator of `succsL`'s folds. -/
private abbrev SuccAcc (I : ISA) := List (Config I × List TraceEv) × Bool × List String × CertCache I

/-- A list fold whose accumulator only grows keeps a member. -/
private theorem foldl_keeps {α β γ : Type} (proj : α → List γ) (f : α → β → α) (m : γ)
    (hmono : ∀ a b, m ∈ proj a → m ∈ proj (f a b)) :
    ∀ (l : List β) (a : α), m ∈ proj a → m ∈ proj (l.foldl f a)
  | [], _, h => h
  | b :: l, a, h => foldl_keeps proj f m hmono l (f a b) (hmono a b h)

/-- …and has a member once some element adds it. -/
private theorem foldl_adds {α β γ : Type} (proj : α → List γ) (f : α → β → α) (m : γ)
    (hmono : ∀ a b, m ∈ proj a → m ∈ proj (f a b)) (b₀ : β) (hadd : ∀ a, m ∈ proj (f a b₀)) :
    ∀ (l : List β) (a : α), b₀ ∈ l → m ∈ proj (l.foldl f a)
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_keeps proj f m hmono l _ (hadd a)
    · exact foldl_adds proj f m hmono b₀ hadd l (f a b) h

/-- Every fault of a step is in `succsL`'s fault list: `FaultStep` names
exactly the outcomes `succsL` drops (it also reports certification faults,
which are not steps). -/
theorem Config.FaultStep.mem_succsL {c : Config I} {tid : Nat} {m : String}
    (h : c.FaultStep A tid m) (cache : CertCache I) (fuel : Nat) (maxPromises : Option Nat) :
    m ∈ (succsL A cache c fuel maxPromises).2.2.1 := by
  have hlt := h.lt_size
  obtain ⟨outs, hs, ho⟩ := h
  unfold succsL
  refine foldl_adds (fun x : SuccAcc I => x.2.2.1) _ m ?_ tid ?_ _ _ (List.mem_range.mpr hlt)
  · -- the outer step only appends to the fault list
    rintro ⟨next, bound, faults, cache⟩ t hm
    simp only
    split
    · simp only [List.mem_append]; exact Or.inl hm
    · rename_i outs' _
      simp only [List.mem_append]; left
      refine foldl_keeps (fun x : SuccAcc I => x.2.2.1) _ m ?_ outs' _ hm
      rintro ⟨next, bound, faults, cache⟩ o hm
      simp only
      split
      · simp [hm]
      · split
        · exact hm
        · split <;> exact hm
  · -- at `tid`, the inner fold appends `m`
    rintro ⟨next, bound, faults, cache⟩
    simp only [hs, List.mem_append]; left
    refine foldl_adds (fun x : SuccAcc I => x.2.2.1) _ m ?_ (.error m) ?_ outs _ ho
    · rintro ⟨next, bound, faults, cache⟩ o hm
      simp only
      split
      · simp [hm]
      · split
        · exact hm
        · split <;> exact hm
    · rintro ⟨next, bound, faults, cache⟩
      simp

/-- Every fault of a step is in `succs`'s fault list. -/
theorem Config.FaultStep.mem_succs {c : Config I} {tid : Nat} {m : String}
    (h : c.FaultStep A tid m) (fuel : Nat) : m ∈ (succs A c fuel).2.2 := by
  simpa [succs] using h.mem_succsL {} fuel none

end Faults

end Kraken.Promising

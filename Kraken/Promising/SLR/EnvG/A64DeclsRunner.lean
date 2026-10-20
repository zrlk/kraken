/-
**The runner's exact configuration, declarations
and initial memory included.** `A64Whole.runnerIs`
(`EnvG/A64WholeRunner.lean`) compares the runner's prepared threads with the
whole-image concretes' states up to their `decls` and leaves the initial
memory out; the runner-exact companions (`*Runner.lean`) start from the
runner's configuration itself, so their check covers:

- `A64Whole.sameAsRunnerD t s`: executable, end, pc, the whole register
  file, the private memory, the **declarations**, and no promise;
- `A64Whole.runnerIsD src ss initMem`: the runner's threads are `ss` in
  order, its initial memory (`Memory.init`) is exactly `initMem`, and it has
  no message.

`runnerIs` is untouched; the old concretes keep using it.

It also has the glue the companions share, so that each one reuses its
verbatim proof's start facts unchanged:

- `A64Whole.WithDeclsD ds P s`: the thread `s` has declarations `ds`, and
  `s` with its declarations dropped satisfies the start predicate `P` (one of
  the existing `Start…` structures, which ask `decls = {}`);
- `QA64MD.of_noDecls`: `QA64M` at `s.noDecls` (hence `QA64CAdj` and the
  other `decls = {}` invariants, which unfold to it) is `QA64MD ds` at `s`;
- `RelPureSpec.holdsD_of_noDecls`, `RelPureSpec.holdsD_init`: the purity
  specification's start facts likewise.
-/
import Kraken.Promising.SLR.EnvG.A64WholeRunner
import Kraken.Promising.SLR.EnvG.A64DeclsLink

namespace Kraken.Promising.SLR.EnvG.A64Whole

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- **A start predicate with declarations**: `s` has the declarations `ds`,
and `s` with its declarations dropped satisfies `P`. -/
def WithDeclsD (ds : Decls) (P : AArch64.State → Prop) (s : AArch64.State) : Prop :=
  s.decls = ds ∧ P s.noDecls

/-- A start state without declarations, given declarations `ds`. -/
theorem withDeclsD_of {ds : Decls} {P : AArch64.State → Prop} {s : AArch64.State} (h0 : s.decls = {})
    (h : P s) : WithDeclsD ds P { s with decls := ds } := by
  refine ⟨rfl, ?_⟩
  obtain ⟨⟩ := s
  simp only at h0
  subst h0
  exact h

end Kraken.Promising.SLR.EnvG.A64Whole

namespace Kraken.Promising.AArch64.EnvG

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **`QA64MD` from the `decls = {}` invariant at the thread with its
declarations dropped.** -/
theorem QA64MD.of_noDecls {ds : Decls} {E : SharedEnv} {e e' : Kraken.Executable Directive} {endPc : Int64}
    {post : MachineState × E.State → Prop} {st : State} {σ : E.State} (hd : st.decls = ds)
    (h : QA64M E e e' endPc post st.noDecls σ) : QA64MD ds E e e' endPc post st σ :=
  ⟨h.1, hd, h.2.2.1, h.2.2.2⟩

/-- **`HoldsD` from `Holds` at the thread with its declarations dropped.** -/
theorem RelPureSpec.holdsD_of_noDecls {A : Arch} {rel : Loc → Pred} {sp : RelPureSpec A rel} {ds : Decls}
    {s : State} (hd : s.decls = ds) (h : sp.Holds s.noDecls) : sp.HoldsD ds s :=
  ⟨h.1, h.2.1, hd, h.2.2.2⟩

/-- **The purity start facts with declarations**, from the verbatim ones at
the threads with their declarations dropped. -/
theorem RelPureSpec.holdsD_init {A : Arch} {rel : Loc → Pred} {sp : Nat → RelPureSpec A rel} {ds : Decls}
    {ss : List State} (hd : ∀ s ∈ ss, s.decls = ds)
    (h : ∀ tid s, (ss.map State.noDecls)[tid]? = some s → (sp tid).Holds s) :
    ∀ tid s, ss[tid]? = some s → (sp tid).HoldsD ds s := fun tid s hs =>
  holdsD_of_noDecls (hd s (List.mem_of_getElem? hs)) (h tid s.noDecls (by simp [List.getElem?_map, hs]))

end Kraken.Promising.AArch64.EnvG

namespace Kraken.Promising.SLR.EnvG.A64Whole

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- A runner's thread is the state `s` in everything a runner-exact theorem
reads: executable, end, pc, registers, private memory, declarations, and
it has no promise. -/
def sameAsRunnerD (t : Thread isa) (s : AArch64.State) : Bool :=
  t.st.exe == s.exe && t.st.endPc == s.endPc && t.st.st.2 == s.st.2 &&
    t.st.st.1.regs == s.st.1.regs && t.st.st.1.dmem == s.st.1.dmem && t.st.decls == s.decls && t.prom.isEmpty

/-- The runner's configuration for the `.kl` source `src` is
`Config.init ss initMem` in everything a runner-exact theorem reads. -/
def runnerIsD (src : String) (ss : List AArch64.State) (initMem : List (Loc × Val)) : Bool :=
  match Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram with
  | .error _ => false
  | .ok pr => pr.config.threads.toList.length == ss.length &&
      (pr.config.threads.toList.zip ss).all (fun (t, s) => sameAsRunnerD t s) &&
      pr.config.mem.init == initMem && pr.config.mem.msgs.isEmpty

/-- The runner's declarations and initial memory for the `.kl` source
`src`, for inspection. -/
def runnerDeclsInit (src : String) : Except String (Decls × List (Loc × Val)) := do
  let pr ← Kraken.Litmus.parseProgram src >>= Kraken.Litmus.AArch64.prepareProgram
  let ds := match pr.config.threads.toList with
    | t :: _ => t.st.decls
    | [] => {}
  return (ds, pr.config.mem.init)

end Kraken.Promising.SLR.EnvG.A64Whole

import WeakCore.TermOwnG0Defs

/-!
# TermK5Defs: the post-publish provenance of the run's counts (S1b)

`PfrProvE H E0 st cc E`: for each own cell `l` of the start env with no publish frontier, either the
run `st → cc` has not published `l` (`SoloNP`), or it published `l` at a configuration `c1` (thread
`th1` at a `publish` naming `l`), and every unit added at `l` beyond the start count has a witness
index at most `th1.vs.vWr`.
-/

namespace TermK5Defs
open CoreLang CoreTerm TermRun TermSound TermMem TermOwnG0Defs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

def PfrProvE (p : Prog) (k : Promises.Knobs) (arch : Arch) (j : Nat) (H : AllocLabel → Nat → Ts → Prop)
    (E0 : TEnv) (st cc : Cfg) (E : TEnv) : Prop :=
  ∀ l c, E0.sto l = some c → c.owner = some E0.tid → E0.pfr l = none →
    (E.pfr l = none ∧ SoloNP p k arch j l st cc) ∨
    ∃ F c1 th1 c1', E.pfr l = some F ∧ SoloNP p k arch j l st c1 ∧ c1.ths[j]? = some th1 ∧
      PubAt th1 l ∧ c1' ∈ threadSteps p k arch c1 j ∧ Solo p k arch j c1' cc ∧
      ∀ N e us, c.ty = .array (.lit N) e → accs e = some us →
        ∀ o, o < E.ini l * nWords us → ¬ o < E0.ini l * nWords us → ∃ τ, τ ≤ th1.vs.vWr ∧ H l o τ

end TermK5Defs

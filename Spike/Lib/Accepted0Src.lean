/-
**The source side of an `Accepted0` program**, ISA-neutral:

- `body0_noMem`: an `Accepted0` body (`Scc.Lower.body0`) has no load, store,
  exchange or spawn (`MemOp`): its `let`s bind an atom or a checked `+`;
- `accepted0_noMem`: so has every code block of an `Accepted0 [d]`
  (`ProgNoS MemOp [d]`, the premise of `reach_noMem`).

Each ISA's `hsafe` (`SrcSafe`) at every fragment follows, the
generalization of `ret0_safe` from `ret0Src` to every `Accepted0 [d]`:
`A64Consumer.safe_of_accepted0` (`Spike/Lib/A64Accepted0Safe.lean`) and
`X64Consumer.safe_of_accepted0` (`Spike/Lib/X64Accepted0Safe.lean`).
-/
import Scc.Lower.Spec
import Spike.Lib.Ret0Src

namespace Spike.Lib.Accepted0Src

open CoreLang CoreTerm A9NoSpawn TermRun Spike.Lib.Ret0Src

/-- **An `Accepted0` body has no memory operation**: a `let` of an atom or a
checked `+` is not a `MemOp`. -/
theorem body0_noMem {e : Expr} : ∀ {scope : List String}, Scc.Lower.body0 scope e = true → NoS MemOp e := by
  induction e with
  | let_ x op e ih =>
    intro scope h
    cases op <;> simp only [Scc.Lower.body0, Bool.and_eq_true, Bool.false_eq_true] at h
    all_goals exact ⟨by simp [MemOp], ih h.2⟩
  | ret a => intro _ _; trivial
  | _ => intro scope h; simp [Scc.Lower.body0] at h

/-- **An `Accepted0` program has no memory operation** (`reach_noMem`'s
premise). -/
theorem accepted0_noMem {d : Decl} (hd : Scc.Lower.Accepted0 [d] = true) : ProgNoS MemOp [d] := by
  intro d' hd'
  simp only [List.mem_singleton] at hd'
  subst hd'
  simp only [Scc.Lower.Accepted0, Bool.and_eq_true] at hd
  exact body0_noMem hd.1.2

end Spike.Lib.Accepted0Src

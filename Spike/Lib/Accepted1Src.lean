/-
**The source side of a one-block `Accepted1` program**, ISA-neutral, the
twin of `Spike/Lib/Accepted0Src.lean`:

- `body1_noMem`: a call-free `Accepted1` body (`Scc.Lower.body1 []`) has no
  load, store, exchange or spawn (`MemOp`): its `let`s bind an atom, a
  checked `+` or a saturating `-` (with no earlier code block, no call);
- `accepted1main_noMem`: so has the code block of an `Accepted1 [d]`
  (`ProgNoS MemOp [d]`, the premise of `reach_noMem`).

Each ISA's `hsafe` (`SrcSafe`) follows: `A64Consumer.safe_of_accepted1main`
(`Spike/Lib/A64Accepted1Safe.lean`).
-/
import Scc.Lower.InvProg1
import Spike.Lib.Ret0Src

namespace Spike.Lib.Accepted1Src

open CoreLang CoreTerm A9NoSpawn TermRun Spike.Lib.Ret0Src

/-- **A call-free `Accepted1` body has no memory operation**: a `let` of an
atom, a checked `+` or a saturating `-` is not a `MemOp`, and an `if`'s
branches are bodies too. -/
theorem body1_noMem {e : Expr} : ∀ {scope : List String}, Scc.Lower.body1 [] scope e = true → NoS MemOp e := by
  induction e with
  | let_ x op e ih =>
    intro scope h
    cases op <;> simp only [Scc.Lower.body1, Scc.Lower.callee1, Bool.and_eq_true, Bool.false_eq_true] at h
    all_goals first | exact ⟨by simp [MemOp], ih h.2⟩ | simp at h
  | ifeq a b yes no ihy ihn =>
    intro scope h
    simp only [Scc.Lower.body1, Bool.and_eq_true] at h
    exact ⟨ihy h.1.2, ihn h.2⟩
  | ret a => intro _ _; trivial
  | _ => intro scope h; simp [Scc.Lower.body1] at h

/-- **A one-block `Accepted1` program has no memory operation**
(`reach_noMem`'s premise). -/
theorem accepted1main_noMem {d : Decl} (hd : Scc.Lower.Accepted1 [d] = true) : ProgNoS MemOp [d] := by
  intro d' hd'
  simp only [List.mem_singleton] at hd'
  subst hd'
  exact body1_noMem (Scc.Lower.Inv.accepted1_main hd).2.2.2.2.2.2

end Spike.Lib.Accepted1Src

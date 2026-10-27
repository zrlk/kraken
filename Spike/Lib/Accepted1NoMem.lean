/-
**The source side of an `Accepted1` program with calls**, ISA-neutral: the
many-code-block twin of `Spike/Lib/Accepted1Src.lean`.

- `body1_noMemE`: an `Accepted1` body (`Scc.Lower.body1 earlier`) has no
  load, store, exchange or spawn (`MemOp`) for any `earlier`: a call is not
  a `MemOp`;
- `decls1_noMem`, `accepted1_noMem`: so has every code block of an
  `Accepted1` program (`ProgNoS MemOp p`, the premise of `reach_noMem`).

Each ISA's `hsafe` at any call depth (`SrcSafeS`) follows:
`X64ConsumerS.safeS_of_accepted1` (`Spike/Lib/X64Accepted1SafeS.lean`).
-/
import Scc.Lower.InvProg1
import Spike.Lib.Ret0Src

namespace Spike.Lib.Accepted1Src

open CoreLang CoreTerm A9NoSpawn TermRun Spike.Lib.Ret0Src

/-- **An `Accepted1` body has no memory operation**, whatever code blocks
it may call: a `let` of an atom, a checked `+`, a saturating `-` or a call is
not a `MemOp`, and an `if`'s branches are bodies too. -/
theorem body1_noMemE {earlier : List String} {e : Expr} :
    ∀ {scope : List String}, Scc.Lower.body1 earlier scope e = true → NoS MemOp e := by
  induction e with
  | let_ x op e ih =>
    intro scope h
    cases op <;> simp only [Scc.Lower.body1, Bool.and_eq_true, Bool.false_eq_true] at h
    all_goals first | exact ⟨by simp [MemOp], ih h.2⟩ | simp at h
  | ifeq a b yes no ihy ihn =>
    intro scope h
    simp only [Scc.Lower.body1, Bool.and_eq_true] at h
    exact ⟨ihy h.1.2, ihn h.2⟩
  | ret a => intro _ _; trivial
  | _ => intro scope h; simp [Scc.Lower.body1] at h

/-- **Every code block passing `decls1` has no memory operation.** -/
theorem decls1_noMem : ∀ {earlier : List String} {p : Prog}, Scc.Lower.decls1 earlier p = true →
    ∀ d ∈ p, NoS MemOp d.body
  | _, [], _, _, hd => by simp at hd
  | _, d :: ds, h, d', hd' => by
    simp only [Scc.Lower.decls1, Scc.Lower.decl1, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hd' with rfl | hd'
    · exact body1_noMemE h.1.2
    · exact decls1_noMem h.2 d' hd'

/-- **An `Accepted1` program has no memory operation** (`reach_noMem`'s
premise). -/
theorem accepted1_noMem {p : Prog} (hp : Scc.Lower.Accepted1 p = true) : ProgNoS MemOp p := by
  simp only [Scc.Lower.Accepted1, Bool.and_eq_true] at hp
  exact decls1_noMem hp.1.2

end Spike.Lib.Accepted1Src

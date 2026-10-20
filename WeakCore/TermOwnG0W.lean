import WeakCore.TermOwnG0Defs

/-!
# TermOwnG0W: the G-0 window

`G0WinW … r wt`: before a `publish` naming the root `r`, every certified configuration of the
planting promise's run has `vWr ≤ wt`. `TermOwnG0Defs.G0Win` is the case `wt = w`.
-/

namespace TermOwnG0W

open CoreLang CoreTerm TermRun TermStep TermOwnG0Defs
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)

/-- **The G-0 window** of a root `r` at bound `wt` for the planting promise `promise cP i a0 v0 w`. -/
def G0WinW (p : Prog) (k : Promises.Knobs) (arch : Arch) (cP : Cfg) (i : Nat) (a0 : Address)
    (v0 : WeakMem.Val) (w : Ts) (r : AllocLabel) (wt : Ts) : Prop :=
  ∀ c th, SoloNP p k arch i r (promise cP i a0 v0 w) c → Certified p k arch c i → c.ths[i]? = some th →
    th.vs.vWr ≤ wt

theorem G0WinW_of_G0Win {p : Prog} {k : Promises.Knobs} {arch : Arch} {cP : Cfg} {i : Nat} {a0 : Address}
    {v0 : WeakMem.Val} {w : Ts} {r : AllocLabel} (h : G0Win p k arch cP i a0 v0 w r) :
    G0WinW p k arch cP i a0 v0 w r w := h

/-- `G0Win` is `G0WinW` at `wt = w` (definitional). -/
theorem g0WinW_of_g0Win {p : Prog} {k : Promises.Knobs} {arch : Arch} {cP : Cfg} {i : Nat}
    {a0 : Address} {v0 : WeakMem.Val} {w : Ts} {r : AllocLabel} :
    G0Win p k arch cP i a0 v0 w r ↔ G0WinW p k arch cP i a0 v0 w r w :=
  Iff.rfl

end TermOwnG0W

#print axioms TermOwnG0W.G0WinW_of_G0Win
#print axioms TermOwnG0W.g0WinW_of_g0Win

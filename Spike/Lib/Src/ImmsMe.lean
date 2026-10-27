import Scc.Lower.Spec2
import Scc.Sem.SrcOut
import Scc.Sem.Correct

/-!
**The theorem's immediate table** (ISA-neutral): `imms2Of p`, plus one
entry for the start before the setup block. At `SrcSem.setupTerm`, the term
thread 0 starts at when `main` takes a setup block's result, word 0 of `me`
is the first TCB, `scc_rt_pinned + 8` (`Λ.pinned.lo + 8`, the pinned region
being `scc_rt_pinned`'s by `regionsTied`). At load no register or slot holds
that word yet (the runtime computes it before it enters `main`'s wrapper),
so the start places `me` at that immediate. Every other key is `imms2Of p`'s.

- `imms2Me`: the table; `setupK`, the start's continuation, has the same entry.
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm

/-- **The immediate table of the `Accepted2` theorems** at layout `Λ`:
`imms2Of p`, except at the setup start's term (`SrcSem.setupTerm`) of a
program with a setup block, where word 0 of `me` is the first TCB,
`Λ.pinned.lo + 8`.

The word is not folded into an instruction: the runtime computes the TCB address before `main`'s wrapper runs. The
entry is still sound: an `.imm n` placement requires `ValRep` between the source word and `n` (`WordPlaceRep`), and
the source start leaves `me`'s word free (`setupInit`), so the proof's choice of the first TCB is the source value.
Once thread 0 calls `rodata`, its pending frame's key is the continuation `setupK` (`frameTerms`), not
`setupTerm`; the table has the same entry there, so `me` stays placed while `rodata` runs. Neither key is a term of
an `Accepted2` block: `body2` has no `.tail` case, and the textual `print` blocks tail-call only `printL`. -/
def imms2Me (Λ : Scc.Sem.Layout) (p : Prog) (e : Expr) (x : String) (k : Nat) : Option Nat :=
  match e, x, k with
  | .let_ "r" (.call "rodata" [] (.var "u") [])
      (.let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a") [])), "me", 0 =>
    if (Scc.Lower.setupOf p).isSome then some (Λ.pinned.lo + 8) else Scc.Lower.imms2Of p e x k
  | .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a") []), "me", 0 =>
    if (Scc.Lower.setupOf p).isSome then some (Λ.pinned.lo + 8) else Scc.Lower.imms2Of p e x k
  | _, _, _ => Scc.Lower.imms2Of p e x k

/-- **The setup start's continuation**: thread 0's pending frame's term while `rodata` runs (`setupTerm`'s body
after its call). -/
def setupK : Expr :=
  .let_ "a" (.pair (.var "r") (.var "me")) (.tail "main" [] (.var "a"))

/-- At the setup start's term, word 0 of `me` is the first TCB. -/
theorem imms2Me_setup {Λ : Scc.Sem.Layout} {p : Prog} {s : Ty} (hs : Scc.Lower.setupOf p = some s) :
    imms2Me Λ p Scc.Sem.SrcSem.setupTerm "me" 0 = some (Λ.pinned.lo + 8) := by
  simp [imms2Me, Scc.Sem.SrcSem.setupTerm, hs]

/-- At the setup start's continuation, word 0 of `me` is the first TCB. -/
theorem imms2Me_setupK {Λ : Scc.Sem.Layout} {p : Prog} {s : Ty} (hs : Scc.Lower.setupOf p = some s) :
    imms2Me Λ p setupK "me" 0 = some (Λ.pinned.lo + 8) := by
  simp [imms2Me, setupK, hs]

/-- **Elsewhere it is `imms2Of p`**: at any other key, or in a program
without a setup block. -/
theorem imms2Me_of_ne {Λ : Scc.Sem.Layout} {p : Prog} {e : Expr} {x : String} {k : Nat}
    (h : (Scc.Lower.setupOf p).isSome → (e = Scc.Sem.SrcSem.setupTerm ∨ e = setupK) → x = "me" → k = 0 → False) :
    imms2Me Λ p e x k = Scc.Lower.imms2Of p e x k := by
  unfold imms2Me; split
  · split
    · exact (h (by assumption) (.inl rfl) rfl rfl).elim
    · rfl
  · split
    · exact (h (by assumption) (.inr rfl) rfl rfl).elim
    · rfl
  · rfl

/-- **Without a setup block it is `imms2Of p`.** -/
theorem imms2Me_of_none {Λ : Scc.Sem.Layout} {p : Prog} (hs : Scc.Lower.setupOf p = none) :
    imms2Me Λ p = Scc.Lower.imms2Of p := by
  funext e x k; exact imms2Me_of_ne fun h => by simp [hs] at h

/--
info: 'Spike.Lib.LowerNode.imms2Me_of_ne' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms imms2Me_of_ne

end Spike.Lib.LowerNode

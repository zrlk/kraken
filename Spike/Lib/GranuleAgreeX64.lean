import Scc.Emit.GranuleX64
import Scc.Cert.Rt.OffsX64

/-!
# The granule pass's flow agrees with the loader's block check (x64, untrusted)

There is one definition of "falls through": the loader's block check
`Scc.Cert.Rt.X64.fallsThrough` (via `Spike.Lib.X64.classify`). The granule
pass (`Scc.Emit.Granule.insX64`, which may not import Spike) spells its cut
set out syntactically; this module proves it is that definition's
no-fall-through set, except for `call`:

* `term_noFall`: an instruction the pass treats as ending the flow ends a
  block that the loader treats as not falling through;
* `noFall_term`: a block the loader treats as not falling through ends in an
  instruction the pass treats as ending the flow, or in a `call`.

The one difference, `call`, is in the conservative direction: the pass never
cuts after a call (the code after it is reached by the return), so it only
keeps more blocks together.
-/

namespace Spike.Lib.GranuleAgreeX64
open Scc.Emit.Granule Spike.Lib.X64

/-- **The pass's flow ends ⇒ the loader's block does not fall through.** -/
theorem term_noFall {d : Directive} (h : insX64 d = some .term) (blk : List (Directive × Nat))
    (n : Nat) : Scc.Cert.Rt.X64.fallsThrough (blk ++ [(d, n)]) = false := by
  unfold insX64 at h
  split at h <;> (try cases h) <;> simp [Scc.Cert.Rt.X64.fallsThrough, classify]

/-- **The loader's block does not fall through ⇒ the pass's flow ends, or the
block ends in a `call`.** -/
theorem noFall_term {blk : List (Directive × Nat)} {d : Directive} {n : Nat}
    (h : Scc.Cert.Rt.X64.fallsThrough (blk ++ [(d, n)]) = false) :
    insX64 d = some .term ∨ ∃ L, classify d = some (.call L) := by
  simp only [Scc.Cert.Rt.X64.fallsThrough, List.getLast?_append, List.getLast?_singleton,
    Option.some_or] at h
  split at h
  · rename_i L hc
    have := (classify_sound hc).1
    subst this; left; rfl
  · rename_i hc
    have := (classify_sound hc).1
    subst this; left; rfl
  · rename_i L hc; exact .inr ⟨L, hc⟩
  · cases h

end Spike.Lib.GranuleAgreeX64

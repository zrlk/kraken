import Scc.Emit.GranuleA64
import Scc.Cert.Rt.OffsA64

/-!
# The granule pass's flow agrees with the loader's block check (AArch64, untrusted)

There is one definition of "falls through": the loader's block check
`Scc.Cert.Rt.A64.fallsThrough` (via `Spike.Lib.A64.Flow.classify`). The
granule pass (`Scc.Emit.Granule.insA64`, which may not import Spike) spells
its cut set out syntactically; this module proves it is exactly that
definition's no-fall-through set (`term_noFall`, `noFall_term`): on AArch64
there is no difference (`bl` falls through for both).
-/

namespace Spike.Lib.GranuleAgreeA64
open Scc.Emit.Granule Spike.Lib.A64.Flow

/-- **The pass's flow ends ⇒ the loader's block does not fall through.** -/
theorem term_noFall {d : Directive} (h : insA64 d = some .term) (blk : List Directive) :
    Scc.Cert.Rt.A64.fallsThrough (blk ++ [d]) = false := by
  unfold insA64 at h
  split at h <;> (try cases h) <;> simp [Scc.Cert.Rt.A64.fallsThrough, classify]

/-- **The loader's block does not fall through ⇒ the pass's flow ends.** -/
theorem noFall_term {blk : List Directive} {d : Directive}
    (h : Scc.Cert.Rt.A64.fallsThrough (blk ++ [d]) = false) : insA64 d = some .term := by
  simp only [Scc.Cert.Rt.A64.fallsThrough, List.getLast?_append, List.getLast?_singleton,
    Option.some_or] at h
  split at h
  · rename_i L hc
    have := (classify_sound hc).1
    subst this; rfl
  · rename_i r hc
    have := (classify_sound hc).1
    subst this; rfl
  · cases h

end Spike.Lib.GranuleAgreeA64

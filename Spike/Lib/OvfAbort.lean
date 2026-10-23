/-
**The overflow abort at the consumers' source**, ISA-free: the source facts
an abort path's overflow exit carries (`AbortPath.at_` of
`Spike/Lib/A64Consumer.lean` and `Spike/Lib/X64Consumer.lean`), and the
justification they give for `SrcSem.source P p`.

* `EnvSmall`: every number bound in an environment fits in 64 bits;
* `noBigNumT_of_envSmall`: a thread with one frame and a small environment
  has no big number (`NoBigNumT`, the budget part of the overflow kind);
* `abortJustified_overflow_source`: `abortJustified_overflow`
  (`Spike/Lib/Src.lean`) for `SrcSem.source P p`, whose steps add the gate
  `mainExit c = []`: thread 0 at a `let` is not at `main`'s `ret`.
-/
import Spike.Lib.Src
import Scc.Sem.SrcExt

namespace Spike.Lib

open CoreLang CoreTerm
open Scc.Sem (SrcSem AbortJustified NoBigNumT Budget frameEnvs)
open Scc.Sem.SrcSem (mainExit)

/-- **A small environment**: every number bound in `env` fits in 64 bits. -/
def EnvSmall (env : TermRun.Env) : Prop :=
  ∀ b ∈ env, ∀ w ∈ b.2.2, ∀ n, w.val = .num n → n < 2 ^ 64

/-- **One frame with a small environment has no big number.** -/
theorem noBigNumT_of_envSmall {s : TermRun.Cfg} {i : Nat} {th : TermRun.TTh} (hi : s.ths[i]? = some th)
    (hst : th.stack = []) (he : EnvSmall th.env) : NoBigNumT i s := by
  intro th' hth' e hmem
  rw [hi] at hth'
  cases Option.some.inj hth'
  simp only [frameEnvs, hst, List.map_nil, List.mem_singleton] at hmem
  subst hmem
  exact he

/-- **The overflow abort is justified for `SrcSem.source P p`** at a
configuration whose thread 0 is `OvfReady`, has one frame with a small
environment, and no promises: `abortJustified_overflow` for `sourceG P p`,
and the gate `mainExit s = []` since thread 0's term is a `let`. -/
theorem abortJustified_overflow_source {P : SrcSem.SrcParams} {p : Prog} {B : Budget} {tr : List Scc.Sem.Ev}
    {s : TermRun.Cfg} {th : TermRun.TTh} (hi : s.ths[0]? = some th) (hc : OvfReady (Ctl.of th))
    (hσ : th.σs = []) (hst : th.stack = []) (hp : th.promises = []) (he : EnvSmall th.env) :
    AbortJustified B (SrcSem.source P p) tr s 0 .overflow := by
  obtain ⟨es, s', hs, hb, hnb⟩ := abortJustified_overflow (p := p) (k := P.k) (arch := P.arch)
    (Sp := fun i c c' => SrcSem.SpawnBy P.cap i c c' ∨ P.hooks.ext i c c') (obsTrace := SrcSem.srcObs P.hooks.trace)
    (init := P.init) (B := B) (tr := tr) hi hc hσ hst hp (noBigNumT_of_envSmall hi hst he)
  refine ⟨es, s', ⟨?_, hs⟩, hb, hnb⟩
  obtain ⟨x, a, b, e, -, -, -, -, -, -, ht, -⟩ := hc
  unfold mainExit
  rw [hi]
  simp only [Ctl.of] at ht
  simp only [ht]

end Spike.Lib

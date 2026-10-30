/-
**`W2` before a frame pop from `W2` after it** (AArch64): at a state `s`
where the source pair `(c, fs)` (frames above `main`'s depth 0, e.g. a
callee's `ret` with its caller's frame) and the pair `(c'', [])` it pops to
share the machine state, `W2` at `(s, c'', [])` gives `W2` at `(s, c, fs)`,
given the pair's own facts (its runs free of `ZBad`, `FrOk2`; its placement,
`PlacedSE`) and the popped control neither at an allocation nor at an
overflow. The state's facts carry over; the write obligation at the popped
pair's own (empty) run shows the state writes off the arena's heap and
counter (the popped control allocates nothing), the abort sites are the
write abort's only (no overflow nor heap abort at the popped control) and
no output `write(1, …)` (none at no frame).

- `w2_ofPopped`: `W2` at `(s, c, fs)` from `W2` at `(s, c'', [])`.
-/
import Spike.Lib.LowerA64.SFactsA2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.LowerNode (FrOk2 ZBad runOk2_of)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl : Lbl}
  {lsize : Lsize} {s : State}

/-- **`W2` before a pop from `W2` after it**: at the state `s`, `W2` at the
popped pair `(c'', [])` (`hW`), the popped control not at an allocation
(`hnb`, a buffer; `hnn`, a box) nor at an overflow (`hov`), the pair `(c, fs)` above depth 0
(`hne`) free of `ZBad` (`hf`) and placed (`hpl`). -/
theorem w2_ofPopped (hp : ProgNoS ZBad p) {c c'' : Ctl} {fs : List TermRun.Frame}
    (hW : W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c'' [])
    (hnb : ∀ x a τ e, c''.term ≠ .let_ x (.newBuf a τ) e) (hnn : ∀ x a e, c''.term ≠ .let_ x (.new a) e)
    (hov : ¬ OvfReady c'')
    (hne : fs ≠ []) (hf : FrOk2 c fs) (hpl : PlacedSE Λ lbl s c fs) :
    W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs := by
  refine w2_of hp hf hW.st hW.ab (fun h => absurd h hne) hpl ?_ ?_ ?_
  · intro c' fs' _ hsys
    have hw := hW.wr c'' [] (.refl _) hsys
    refine ⟨fun L hL => ?_, fun hL => ?_⟩
    · rcases hw.arena L hL with h | h | h | ⟨_, x, a, τ, e, _, _, _, _, ht, _⟩ | ⟨-, _, x, a, e, _, _, _, ht, _⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · exact absurd ht (hnb x a τ e)
      · exact absurd ht (hnn x a e)
    · obtain ⟨_, _, _, x, τ, e, _, _, _, _, hsite, _⟩ := hw.ctr hL
      rcases hsite with ⟨a, _, _, ht, _⟩ | ⟨-, a, _, ht, _⟩
      · exact absurd ht (hnb x a τ e)
      · exact absurd ht (hnn x a e)
  · intro k a hk hpc
    obtain ⟨h1, h2⟩ := hW.abort k a hk hpc
    refine ⟨?_, h2⟩
    rcases h1 with h | ⟨_, h, _⟩ | ⟨_, h⟩
    · exact .inl h
    · exact absurd h hov
    · obtain ⟨x, a', τ, e, _, _, _, _, ht, _⟩ := h 0 fun hn => by
        obtain ⟨x, a', τ, e, ht⟩ := hn
        exact absurd ht (hnb x a' τ e)
      exact absurd ht (hnb x a' τ e)
  · intro hs b n hd
    exact absurd rfl (hW.svc1 hs b n hd).1

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.w2_ofPopped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.w2_ofPopped

/-
**`Correct` is monotone in the layout's immediate table** (ISA-neutral).

`Layout.imms` enters `Scc.Sem.Correct` only through `Components.env_imm`
(a word placed at an immediate `n` is one the table gives `n` for), in
positive position: a larger table is a weaker requirement. So a simulation
at a table `i` is one at any table `i'` that answers `some n` wherever `i`
does, provided the target's loader and code marks do not read the table
(both canonical targets' do not: `Spike/Lib/ImmsMonoA64.lean`,
`Spike/Lib/ImmsMonoX64.lean`).

- `components_imms_mono`: `Components` at `Λ` gives `Components` at
  `{Λ with imms := i'}`;
- `sim_imms_mono`, `correct_imms_mono`: the same for `Sim` and `Correct`,
  given that `T.load` and `T.marks` agree on the two layouts.
-/
import Scc.Sem.CorrectE

namespace Spike.Lib.ImmsMono

open Scc.Sem

/-- `i'` answers `some n` wherever `i` does. -/
def ImmsSub (i i' : CoreTerm.Expr → String → Nat → Option Nat) : Prop :=
  ∀ e x k n, i e x k = some n → i' e x k = some n

/-- **`Components` is monotone in the immediate table.** -/
theorem components_imms_mono {M : ExtMachine} {Λ : Layout} {w : Witness M} {t : M.Cfg} {s : TermRun.Cfg}
    (h : Components M Λ w t s) {i' : CoreTerm.Expr → String → Nat → Option Nat} (hi : ImmsSub Λ.imms i') :
    Components M { Λ with imms := i' } w t s :=
  { h with env_imm := fun i th d e x k n h1 h2 h3 => hi _ _ _ _ (h.env_imm i th d e x k n h1 h2 h3) }

/-- **`Sim` is monotone in the immediate table**, for a target whose loader
and code marks do not read it (`hload`, `hmarks`). -/
def sim_imms_mono {T : Target} {S : SrcSem} {Λ : Layout} {B : Budget} {asm : T.Asm} (h : Sim T S Λ B asm)
    {i' : CoreTerm.Expr → String → Nat → Option Nat} (hi : ImmsSub Λ.imms i')
    (hload : T.load asm { Λ with imms := i' } = T.load asm Λ)
    (hmarks : T.marks asm { Λ with imms := i' } = T.marks asm Λ) :
    Sim T S { Λ with imms := i' } B asm where
  R := h.R
  layout :=
    let hw := h.layout
    ⟨hw.inSpace, hw.aligned, hw.disjoint, hw.abortInj, hw.image, hw.symIn, hw.symAbove, hw.symNodup, hw.pos⟩
  start := by rw [hload]; exact h.start
  progress := by
    rw [hload, hmarks]
    intro t0 tr t h0 hr
    exact h.progress t0 tr t h0 hr
  sim := by rw [hload, hmarks]; exact h.sim
  abort := by
    rw [hload, hmarks]
    intro t0 tr t tid es t' k h0 hr hs hk
    obtain ⟨s, w, i, hR, hRt, hC, hw, hJ⟩ := h.abort t0 tr t tid es t' k h0 hr hs hk
    exact ⟨s, w, i, hR, hRt, components_imms_mono hC hi, hw, hJ⟩
  explicit t s hR :=
    let ⟨w, hw⟩ := h.explicit t s hR
    ⟨w, components_imms_mono hw hi⟩

/-- **`Correct` is monotone in the immediate table**, for a target whose
loader and code marks do not read it. -/
theorem correct_imms_mono {T : Target} {S : SrcSem} {Λ : Layout} {B : Budget} {asm : T.Asm}
    (h : Correct T S Λ B asm) {i' : CoreTerm.Expr → String → Nat → Option Nat} (hi : ImmsSub Λ.imms i')
    (hload : T.load asm { Λ with imms := i' } = T.load asm Λ)
    (hmarks : T.marks asm { Λ with imms := i' } = T.marks asm Λ) :
    Correct T S { Λ with imms := i' } B asm :=
  let ⟨hs⟩ := h
  ⟨sim_imms_mono hs hi hload hmarks⟩

end Spike.Lib.ImmsMono

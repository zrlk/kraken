/-
**The setup call's post's control facts** (AArch64; the twin of
`Spike/Lib/LowerX64/PostSOf.lean`): at the program's start before a setup
block (`setupTerm`, the start control `th02` under `setupOf p = some _`),
every control of the setup call's post `SPostC` is the call's rest
`let a = (r, me); tail main a` at the returned words: no `ret`, no load,
store or allocation, free of `ZBad`, not at an overflow (`CFactsC`,
`MainCtlC` at no frame; `h0InA_setup_assembled`'s `hPostS`).

- `th02_term_setup`: the start's term under a setup block is `setupTerm`;
- `postS_setupTerm`: `hPostS` at a start at `setupTerm`;
- `postS_setupTerm_noNew`: its controls are at no box allocation.
-/
import Spike.Lib.LowerA64.H0InAssembledA

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Spike.Lib.A64Consumer (CFactsC)
open Spike.Lib.LowerNode (FrOk2 ZBad)

/-- **The start's term under a setup block is `setupTerm`.** -/
theorem th02_term_setup {p : Prog} {ty : Ty} (hs : Scc.Lower.setupOf p = some ty) (meW : TermRun.Word) :
    (th02 p meW).term = Scc.Sem.SrcSem.setupTerm := by
  simp [th02, hs]

/-- **The setup call's post's controls' facts** (`hPostS`): at a start
control at `setupTerm`, every `SPostC` control is the call's rest, which is
no `ret`, reads, writes and allocates nothing, is free of `ZBad` and is no
addition. -/
theorem postS_setupTerm {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ty : Ty} {c0 : Ctl}
    (hc : c0.term = Scc.Sem.SrcSem.setupTerm) :
    ∀ c rs, SPostC p lbl ty c0 c rs → CFactsC c ∧ MainCtlC c [] := by
  rintro c rs ⟨cE, fr, cr, a', t, ws, ⟨x, f, a, e, d, t', ws', ht, -, -, -, rfl⟩, -, -, -, rfl⟩
  rw [hc] at ht
  simp only [Scc.Sem.SrcSem.setupTerm, Expr.let_.injEq] at ht
  obtain ⟨rfl, -, rfl⟩ := ht
  refine ⟨⟨fun _ h => ?_, fun _ _ _ _ _ h => ?_, fun _ _ _ _ h => ?_⟩, ⟨⟨?_, fun _ h => ?_⟩, ?_⟩⟩
  · cases h
  · rcases h with h | ⟨_, h⟩ <;> cases h
  · cases h
  · simp [A9NoSpawn.NoS, ZBad]
  · cases h
  · rintro ⟨_, _, _, _, _, _, _, _, _, _, h, -⟩
    cases h

/-- **The setup call's post's controls are at no box allocation**
(`postS_setupTerm`'s companion: the call's rest is no `new`). -/
theorem postS_setupTerm_noNew {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ty : Ty} {c0 : Ctl}
    (hc : c0.term = Scc.Sem.SrcSem.setupTerm) :
    ∀ c rs, SPostC p lbl ty c0 c rs → ∀ x a T e, c.term ≠ .let_ x (.new a T) e := by
  rintro c rs ⟨cE, fr, cr, a', t, ws, ⟨x, f, a, e, d, t', ws', ht, -, -, -, rfl⟩, -, -, -, rfl⟩
  rw [hc] at ht
  simp only [Scc.Sem.SrcSem.setupTerm, Expr.let_.injEq] at ht
  obtain ⟨rfl, -, rfl⟩ := ht
  intro _ _ _ _ h
  cases h

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.th02_term_setup' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.th02_term_setup

/-- info: 'Spike.Lib.LowerA64.postS_setupTerm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.postS_setupTerm

/-- info: 'Spike.Lib.LowerA64.postS_setupTerm_noNew' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.postS_setupTerm_noNew

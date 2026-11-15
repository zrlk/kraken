/-
**The constructs' segments at a smaller walk and a larger aborts'
fragment** (x86-64; the twin of `Spike/Lib/LowerA64/G1H1Mono.lean`):
`CallC2`, `LaneC`, `NewBufC` and `PrintCallC`
(`Spike/Lib/LowerX64/Body2.lean`) read the walk `T` only as a premise (the
construct's term, and the resumption facts `PtC2`) and the aborts `Ab`
only in their exits (`ContC`), so each holds at any `T' ⊆ T` and
`Ab ⊆ Ab'`; the abort node `abortN2` reads `T` in its source's facts.

- `ContC.monoAb`: the exits (the resumption facts by a private lemma);
- `CallC2.monoTA`, `LaneC.monoTA`, `NewBufC.monoTA`, `PrintCallC.monoTA`:
  the four constructs;
- `at_abortN2_monoT`: a state at the abort node at `T'` is one at `T`.
-/
import Spike.Lib.LowerX64.Body2

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 (At)

section Mono

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {lcx : Scc.Lower.Ctx} {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
  {Bl : Int64 → Nat → Label → Nat → Prop}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : FragS isa}
  {K : State → State → Prop} {ms : List TermRun.Frame → MemSide isa} {fp ra : BitVec 64} {tp : UInt64}
  {fs : List TermRun.Frame} {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T T' : Expr → Prop}
  {Ab Ab' : FragS isa} {Lk : Expr × List (String × Scc.Lower.LitV) → Prop}

/-- **The resumption facts at a larger walk predicate**: `PtC2` reads the
walk only at the lowering walk's terms (private: the allocator's instance
at a placement has its own public copy). -/
private theorem ptC2_monoTW {lab : Label → Int64} {kk : Nat} {pc : Int64} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)} {t : Expr} (hT : ∀ t, T' t → T t)
    (h : PtC2 lcx fr Cd Bl lab i T' Lk kk pc env n lits cs bufs t) :
    PtC2 lcx fr Cd Bl lab i T Lk kk pc env n lits cs bufs t := by
  obtain ⟨l, k, r, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨l, k, r, h1, h2, h3, fun q hq => ⟨(h4 q hq).1, hT _ (h4 q hq).2.1, (h4 q hq).2.2⟩, h5, h6, h7⟩

/-- **A construct's exits at a larger aborts' fragment.** -/
theorem ContC.monoAb {c0 : Ctl} {pc' : Int64} {e : Expr} {env' : Scc.Lower.Env}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hA : ∀ s c fs', Ab s c fs' → Ab' s c fs') :
    ∀ s c fs', ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab pc' e env' lits cs bufs s c fs' →
      ContC p lbl lsize i fr exe endPc R F fp ra tp c0 fs Ab' pc' e env' lits cs bufs s c fs' :=
  fun s c fs' h => h.imp_right (hA s c fs')

/-- **A plain call's segment at a smaller walk and larger aborts.** -/
theorem CallC2.monoTA (H : CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk)
    (hT : ∀ t, T' t → T t) (hA : ∀ s c fs', Ab s c fs' → Ab' s c fs') :
    CallC2 p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T' Ab' Lk := by
  intro c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs hc0 hT' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hpt
  exact (H c0 pc pc' kk kk' env n x g is a ts e t w lits cs bufs hc0 (hT _ hT') h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    h11 (ptC2_monoTW hT hpt)).mono_post (ContC.monoAb hA)

/-- **A lane store's segment at a smaller walk and larger aborts.** -/
theorem LaneC.monoTA (H : LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hT : ∀ t, T' t → T t) (hA : ∀ s c fs', Ab s c fs' → Ab' s c fs') :
    LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T' Ab' := by
  intro c0 pc pc' kk kk' env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs hc0 hT' h1 h2 h3 h4 h5 h6
    h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20
  exact (H c0 pc pc' kk kk' env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs hc0 (hT _ hT') h1 h2
    h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20).mono_post (ContC.monoAb hA)

/-- **A buffer allocation's segment at a smaller walk and larger aborts.** -/
theorem NewBufC.monoTA (H : NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab Lk)
    (hT : ∀ t, T' t → T t) (hA : ∀ s c fs', Ab s c fs' → Ab' s c fs') :
    NewBufC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T' Ab' Lk := by
  intro c0 pc pc' kk kk' env n x cn τ e tk kv en em hh lits cs bufs hc0 hT' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    h12 h13 hpt
  exact (H c0 pc pc' kk kk' env n x cn τ e tk kv en em hh lits cs bufs hc0 (hT _ hT') h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 (ptC2_monoTW hT hpt)).mono_post (ContC.monoAb hA)

/-- **An output call's segment at a smaller walk and larger aborts.** -/
theorem PrintCallC.monoTA (H : PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab)
    (hT : ∀ t, T' t → T t) (hA : ∀ s c fs', Ab s c fs' → Ab' s c fs') :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T' Ab' := by
  intro c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs hc0 hT' h1 h2 h3 h4 h5 h6 h7 h8 h9
    h10 h11 h12 h13 h14
  exact (H c0 pc pc' kk kk' env n x g is a ts e xe dg t b o m cw lits cs bufs hc0 (hT _ hT') h1 h2 h3 h4 h5 h6
    h7 h8 h9 h10 h11 h12 h13 h14).mono_post (ContC.monoAb hA)

/-- **A state at the abort node at a smaller walk is one at the larger**
(`AbJ2` reads the walk at the source's term only). -/
theorem at_abortN2_monoT {lab : String → Int64} {c0 : Ctl} {s : State} {c : Ctl} (hT : ∀ t, T' t → T t)
    (h : At exe endPc R F (abortN2 i T' p lbl fr lab fp ra c0) s c) :
    At exe endPc R F (abortN2 i T p lbl fr lab fp ra c0) s c := by
  obtain ⟨h1, h2, h3, h4, σ, hab, hF, ⟨⟨sv, lits, hS, hE, hI, hL, hT'⟩, hfj⟩, hrun⟩ := h
  exact ⟨h1, h2, h3, h4, σ, hab, hF, ⟨⟨sv, lits, hS, hE, hI, hL, hT _ hT'⟩, hfj⟩, hrun⟩

end Mono

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.CallC2.monoTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.CallC2.monoTA

/-- info: 'Spike.Lib.LowerX64.LaneC.monoTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.LaneC.monoTA

/-- info: 'Spike.Lib.LowerX64.NewBufC.monoTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.NewBufC.monoTA

/-- info: 'Spike.Lib.LowerX64.PrintCallC.monoTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.PrintCallC.monoTA

/-- info: 'Spike.Lib.LowerX64.at_abortN2_monoT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.at_abortN2_monoT

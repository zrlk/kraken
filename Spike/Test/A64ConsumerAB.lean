/-
**The memory side `msOfAB`** (`Spike/Lib/A64ConsumerAB.lean`): its byte step
is `print`'s, its abort justification the write abort phase's, a row under
`msOfA` carries over, and the bridge lemmas rest on the standard axioms only.
-/
import Spike.Lib.A64ConsumerAB
import Spike.Lib.A64WriteAb

namespace Spike.Lib.A64ConsumerA.Test

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

/-- With the write abort phase of `WriteAb`, a refusal's justification is
that every refused result resumes in `WriteAb.Ab`. -/
example (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (ar : Arena) (I : InvS) (lab : Label → Int64) (lbl : Lbl) (lsize : Lsize)
    (fs : List TermRun.Frame) (s : State) (c : Ctl) :
    (msOfAB Λ μ p rd G own ar I (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize fs).we s c ↔
      ∀ r, Kernel.writeRefused r = true → Spike.Lib.A64.WriteAb.Ab lab (abi.ret s r) :=
  Iff.rfl

/-- `msOfAB` keeps `msOfA`'s kernel model. -/
example (Λ : Scc.Sem.Layout) (μ : Marks) (p : Prog) (rd : TermRun.Word → Prop) (G : Loc → Val → Prop)
    (own : OwnS) (ar : Arena) (I : InvS) (Ab : State → Prop) (lbl : Lbl) (lsize : Lsize)
    (fs : List TermRun.Frame) :
    (msOfAB Λ μ p rd G own ar I Ab lbl lsize fs).K = some abi :=
  rfl

/-- info: 'Spike.Lib.A64ConsumerA.Out.msOfAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Out.msOfAB

/-- info: 'Spike.Lib.A64ConsumerA.byteOut_emit_msOfAB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms byteOut_emit_msOfAB

/-- info: 'Spike.Lib.A64ConsumerA.refused_ab_of_emit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms refused_ab_of_emit

end Spike.Lib.A64ConsumerA.Test

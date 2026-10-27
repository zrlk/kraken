/-
**`Correct` for a one-thread program on the canonical AArch64 target**,
the source side of the memory rows discharged: `correctK`
(`Spike/Lib/A64Consumer.lean`) with `SrcMem` from `srcMem`
(`Spike/Lib/Consumer1.lean`). The remaining hypotheses are `correctK`'s
(see its module docstring: the accepted parse and load boundary, the node
obligations, and the open hypotheses).
-/
import Spike.Lib.A64Consumer

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : Inv} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : Own}

open Scc.Cert.Link in
/-- **`correctK` with the source steps of the memory rows proved**
(`srcMem`). -/
theorem correctA64 {B : Budget} {asm : String} {prog : Program} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (T.marks asm Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk (T.marks asm Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk (T.marks asm Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (T.marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctK (B := B) hpa hd himg hss hw hst hload hP hinit hN (srcMem P p) hsafe hT htk0 hown0 hps hsvc hrd hwf hG0
    hGpl hA hab0


/-- The canonical target on parsed texts, with one thread slot. -/
abbrev TPar : Target := parsedTarget (kernel 1) Entry.linux

/-- The target on parsed texts at the entry state `E`, with one thread slot
(`TPar` is it at `Entry.linux`). -/
abbrev TParE (E : Entry) : Target := parsedTarget (kernel 1) E

open Scc.Cert.Link in
/-- **`correctA64` on parsed texts**: `Correct` over the target on parsed
texts (`TPar`, `parsedTarget`) at `(prog, secs)`, with no parse equation
(`correctKOn`, the load by `rfl`). `correct_of_parsed` carries it to a text
parsing to these values. -/
theorem correctA64P {B : Budget} {prog : Program} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, TPar.load (prog, secs) Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (TPar.marks (prog, secs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (TPar.marks (prog, secs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, TPar.load (prog, secs) Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk (TPar.marks (prog, secs) Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk (TPar.marks (prog, secs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, TPar.load (prog, secs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (TPar.marks (prog, secs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct TPar (SrcSem.source P p) Λ B (prog, secs) :=
  correctKOn (B := B) (ld := TPar.load) (rs := TPar.resolve) (asm := (prog, secs)) rfl himg hss hw hst hload hP hinit hN (srcMem P p) hsafe hT htk0 hown0 hps hsvc hrd hwf hG0
    hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctA64` on parsed texts**: `Correct` over the target on parsed
texts (`(TParE E)`, `parsedTarget`) at `(prog, secs)`, with no parse equation
(`correctKOn`, the load by `rfl`). `correct_of_parsed` carries it to a text
parsing to these values. -/
theorem correctA64PE {E : Entry} {B : Budget} {prog : Program} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, (TParE E).load (prog, secs) Λ = some t0) (hP : HookOK P p) (hinit : P.init
        (s0 P.cap))
    (hN : Nodes Λ p ((TParE E).marks (prog, secs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p ((TParE E).marks (prog, secs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TParE E).load (prog, secs) Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk ((TParE E).marks (prog, secs) Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk ((TParE E).marks (prog, secs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TParE E).load (prog, secs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath ((TParE E).marks (prog, secs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct (TParE E) (SrcSem.source P p) Λ B (prog, secs) :=
  correctKOn (B := B) (ld := (TParE E).load) (rs := (TParE E).resolve) (asm := (prog,
      secs)) rfl himg hss hw hst hload hP
    hinit hN (srcMem P p) hsafe hT htk0 hown0 hps hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.A64Consumer

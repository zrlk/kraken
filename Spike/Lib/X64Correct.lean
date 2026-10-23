/-
**`Correct` for a one-thread program on the canonical x86-64 target**,
the source side of the memory rows discharged: `correctK`
(`Spike/Lib/X64Consumer.lean`) with `SrcMem` from `srcMem`
(`Spike/Lib/Consumer1.lean`, ISA-free). The twin of
`Spike/Lib/A64Correct.lean`; the remaining hypotheses are `correctK`'s (see
its module docstring: the accepted parse and load boundary, the node
obligations, and the open hypotheses `PromShared`, `WriteNoProm`).
-/
import Spike.Lib.X64Consumer

namespace Spike.Lib.X64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : Inv} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop}
  {G : Loc → Val → Prop} {own : Own}

open Scc.Cert.Link in
/-- **`correctK` with the source steps of the memory rows proved**
(`srcMem`). -/
theorem correctX64 {B : Budget} {asm : Asm} {cells : List (Directive × Nat)} {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (hpa : cellsOf asm = some cells) (hd : dataSections asm.text = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (T.marks asm Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk (T.marks asm Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk (T.marks asm Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (T.marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctK (B := B) hpa hd himg hss hw hst hload hP hinit hN (srcMem P p) hsafe hT htk0 hown0 hps hsvc hrd hwf hG0
    hGpl hA hab0


/-- The canonical target on parsed texts, with one thread slot. -/
abbrev TPar : Target := parsedTarget (kernel 1) Entry.linux

/-- The target on parsed texts at the entry state `E`, with one thread slot
(`TPar` is it at `Entry.linux`). -/
abbrev TParE (E : Entry) : Target := parsedTarget (kernel 1) E

open Scc.Cert.Link in
/-- **`correctX64` on parsed texts**: `Correct` over the target on parsed
texts (`TPar`, `parsedTarget`) at `(cells, secs, offs)`, with no parse equation
(`correctKOn`, the load by `rfl`). `correct_of_parsed` carries it to a text
parsing to these values. -/
theorem correctX64P {B : Budget} {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List (String × Nat)}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, TPar.load (cells, secs, offs) Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (TPar.marks (cells, secs, offs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (TPar.marks (cells, secs, offs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, TPar.load (cells, secs, offs) Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk (TPar.marks (cells, secs, offs) Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk (TPar.marks (cells, secs, offs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, TPar.load (cells, secs, offs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (TPar.marks (cells, secs, offs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct TPar (SrcSem.source P p) Λ B (cells, secs, offs) :=
  correctKOn (B := B) (ld := TPar.load) (rs := TPar.resolve) (asm := (cells, secs, offs)) rfl himg hss hw hst hload hP hinit hN (srcMem P p) hsafe hT htk0 hown0 hps hsvc hrd hwf hG0
    hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctX64P` at any entry state `E`**: `Correct` over the target on
parsed texts at `E` (`TParE E`); `correctX64P` is it at `Entry.linux`. -/
theorem correctX64PE {E : Entry} {B : Budget} {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List
    (String × Nat)}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, (TParE E).load (cells, secs, offs) Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none)
        (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p ((TParE E).marks (cells, secs, offs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p ((TParE E).marks (cells, secs, offs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TParE E).load (cells, secs, offs) Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hps : PromShared Λ P p G own I rS Tk ((TParE E).marks (cells, secs, offs) Λ))
    (hsvc : WriteNoProm Λ P p G own I rS Tk ((TParE E).marks (cells, secs, offs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TParE E).load (cells, secs, offs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath ((TParE E).marks (cells, secs, offs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct (TParE E) (SrcSem.source P p) Λ B (cells, secs, offs) :=
  correctKOn (B := B) (ld := (TParE E).load) (rs := (TParE E).resolve) (asm := (cells, secs, offs)) rfl himg hss hw
    hst hload hP hinit hN (srcMem P p) hsafe hT htk0 hown0 hps hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.X64Consumer

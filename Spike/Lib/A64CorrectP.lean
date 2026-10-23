/-
**`Correct` on the canonical AArch64 target with `PromShared` discharged**:
`correctA64` and `correctA64P` (`Spike/Lib/A64Correct.lean`) with the
hypothesis `PromShared` supplied by `promShared_a64`
(`Spike/Lib/A64PromShared.lean`), whose premises are the theorems' own (the
node obligations, the source's memory rows, `TakePath`, the layout). The
remaining per-program open hypothesis is `WriteNoProm`.
-/
import Spike.Lib.A64Correct
import Spike.Lib.A64PromShared

namespace Spike.Lib.A64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : Inv} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : Own}

open Scc.Cert.Link in
/-- **`correctA64` without `PromShared`**: the hypothesis by
`promShared_a64` from the theorem's own premises. -/
theorem correctA64' {B : Budget} {asm : String} {prog : Program} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hpa : textProgram asm = .ok prog)
    (hd : dataSections asm = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, T.load asm Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none) (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (T.marks asm Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) t0.1.mem)
    (hsvc : WriteNoProm Λ P p G own I rS Tk (T.marks asm Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (T.marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctA64 (B := B) hpa hd himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (A64PromShared.promShared_a64 hP hN (srcMem P p) hsafe hrd hwf hGpl hT) hsvc hrd hwf hG0 hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctA64P` without `PromShared`**: the hypothesis by
`promShared_a64` from the theorem's own premises. -/
theorem correctA64P' {B : Budget} {prog : Program} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, TPar.load (prog, secs) Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none)
    (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (TPar.marks (prog, secs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (TPar.marks (prog, secs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, TPar.load (prog, secs) Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) t0.1.mem)
    (hsvc : WriteNoProm Λ P p G own I rS Tk (TPar.marks (prog, secs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, TPar.load (prog, secs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (TPar.marks (prog, secs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct TPar (SrcSem.source P p) Λ B (prog, secs) :=
  correctA64P (B := B) himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (A64PromShared.promShared_a64 hP hN (srcMem P p) hsafe hrd hwf hGpl hT) hsvc hrd hwf hG0 hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctA64PE` without `PromShared`** (`correctA64P'` at any entry
state `E`). -/
theorem correctA64PE' {E : Entry} {B : Budget} {prog : Program} {secs : DataSecs} {code : String → Option Nat}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, (TParE E).load (prog, secs) Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none)
    (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p ((TParE E).marks (prog, secs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p ((TParE E).marks (prog, secs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TParE E).load (prog, secs) Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) t0.1.mem)
    (hsvc : WriteNoProm Λ P p G own I rS Tk ((TParE E).marks (prog, secs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TParE E).load (prog, secs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath ((TParE E).marks (prog, secs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata))) :
    Correct (TParE E) (SrcSem.source P p) Λ B (prog, secs) :=
  correctA64PE (B := B) himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (A64PromShared.promShared_a64 hP hN (srcMem P p) hsafe hrd hwf hGpl hT) hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.A64Consumer

/-
**`Correct` on the canonical x86-64 target with `PromShared` and
`WriteNoProm` discharged**. The twin of `Spike/Lib/A64CorrectNW.lean`:
`correctX64'` and `correctX64P'` (`Spike/Lib/X64CorrectP.lean`) with the
hypothesis `WriteNoProm` from `NoWrite` (`writeNoProm_of_noWrite`,
`Spike/Lib/X64SegInst.lean`).
-/
import Spike.Lib.X64CorrectP
import Spike.Lib.X64SegInst

namespace Spike.Lib.X64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : Inv} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : Own}

open Scc.Cert.Link in
/-- **`correctX64` without `PromShared` and `WriteNoProm`**:
`PromShared` as in the primed form, `WriteNoProm` from `NoWrite`
(`writeNoProm_of_noWrite`). -/
theorem correctX64'' {B : Budget} {asm : Asm} {cells : List (Directive × Nat)} {secs : DataSecs}
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
    (hnw : NoWrite I)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (T.marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctX64' (B := B) hpa hd himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (writeNoProm_of_noWrite hnw) hrd hwf hG0 hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctX64P` without `PromShared` and `WriteNoProm`**:
`PromShared` as in the primed form, `WriteNoProm` from `NoWrite`
(`writeNoProm_of_noWrite`). -/
theorem correctX64P'' {B : Budget} {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List (String × Nat)}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (cells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)) c0)
    (hload : ∃ t0, TPar.load (cells, secs, offs) Λ = some t0) (hP : P.hooks = SrcSem.SrcHooks.none)
    (hinit : P.init (s0 P.cap))
    (hN : Nodes Λ p (TPar.marks (cells, secs, offs) Λ) rd G own I) (hsafe : SrcSafe P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePath Λ p (TPar.marks (cells, secs, offs) Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, TPar.load (cells, secs, offs) Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) t0.1.mem)
    (hnw : NoWrite I)
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, TPar.load (cells, secs, offs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (TPar.marks (cells, secs, offs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct TPar (SrcSem.source P p) Λ B (cells, secs, offs) :=
  correctX64P' (B := B) himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (writeNoProm_of_noWrite hnw) hrd hwf hG0 hGpl hA hab0

end Spike.Lib.X64Consumer

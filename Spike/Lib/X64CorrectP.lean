/-
**`Correct` on the canonical x86-64 target with `PromShared` discharged**.
The twin of `Spike/Lib/A64CorrectP.lean`:

- `promShared_x64`: `PromShared` from the node obligations, as
  `promShared_a64` (`Spike/Lib/A64PromShared.lean`): `Pre`'s core
  (`PreCore`) is the certification run's invariant (`stepG_of`, with
  `core_ins`, `core_sys`, `core_site`), and a certified promise from `Pre`
  lands in it (`pre_core_promise`).
- `correctX64'`, `correctX64P'`: `correctX64` and `correctX64P`
  (`Spike/Lib/X64Correct.lean`) with `PromShared` by `promShared_x64` from
  the theorems' own premises. The remaining per-program open hypothesis is
  `WriteNoProm`.
-/
import Spike.Lib.X64Correct
import Spike.Lib.X64PromShared

namespace Spike.Lib.X64PromShared

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer

variable {Λ : Scc.Sem.Layout} {P : SrcSem.SrcParams} {p : CoreTerm.Prog} {G : Loc → Val → Prop} {own : Own}
  {I : Inv} {rS : Range} {Tk : State → Prop}

/-- **`PromShared` from the node obligations**: `Pre`'s core (`PreCore`) is
the certification run's invariant (`stepG_of`): an instruction step keeps
it (`core_ins`: off the transfer sites by the node obligations), and so do a
system call's certification step (`core_sys`) and the take site's
(`core_site`, by `TakePath.site`'s local run); a certified promise from
`Pre` lands in it (`pre_core_promise`). -/
theorem promShared_x64 {μ : Marks} {rd : TermRun.Word → Prop} (hP : P.hooks = SrcSem.SrcHooks.none)
    (hN : Nodes Λ p μ rd G own I) (hS : SrcMem P p) (hsafe : SrcSafe P p I) (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hT : TakePath Λ p μ I rS Tk) :
    PromShared Λ P p G own I rS Tk μ :=
  promShared_of
    (stepG_of (Core := PreCore Λ P p G own I) (fun _ _ _ h => h.msgs)
      (core_ins hP hN hS hsafe hrd hwf hGpl)
      (fun _ _ _ _ _ _ h hsi hs hso ho => (core_sys hP hN hT h hsi hs hso ho).imp fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_site hP hN hT h hsi hso ho).imp fun _ h => h.2))
    (fun _ s _ _ hpre hth hw hc => ⟨s, pre_core_promise hpre hth hw hc⟩)

end Spike.Lib.X64PromShared

namespace Spike.Lib.X64Consumer

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : Inv} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : Own}

open Scc.Cert.Link in
/-- **`correctX64` without `PromShared`**: the hypothesis by
`promShared_x64` from the theorem's own premises. -/
theorem correctX64' {B : Budget} {asm : Asm} {cells : List (Directive × Nat)} {secs : DataSecs}
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
    (hsvc : WriteNoProm Λ P p G own I rS Tk (T.marks asm Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (T.marks asm Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctX64 (B := B) hpa hd himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (X64PromShared.promShared_x64 hP hN (srcMem P p) hsafe hrd hwf hGpl hT) hsvc hrd hwf hG0 hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctX64P` without `PromShared`**: the hypothesis by
`promShared_x64` from the theorem's own premises. -/
theorem correctX64P' {B : Budget} {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List (String × Nat)}
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
    (hsvc : WriteNoProm Λ P p G own I rS Tk (TPar.marks (cells, secs, offs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, TPar.load (cells, secs, offs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath (TPar.marks (cells, secs, offs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct TPar (SrcSem.source P p) Λ B (cells, secs, offs) :=
  correctX64P (B := B) himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (X64PromShared.promShared_x64 hP hN (srcMem P p) hsafe hrd hwf hGpl hT) hsvc hrd hwf hG0 hGpl hA hab0

open Scc.Cert.Link in
/-- **`correctX64PE` without `PromShared`** (`correctX64P'` at any entry
state `E`). -/
theorem correctX64PE' {E : Entry} {B : Budget} {cells : List (Directive × Nat)} {secs : DataSecs} {offs : List
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
    (hsvc : WriteNoProm Λ P p G own I rS Tk ((TParE E).marks (cells, secs, offs) Λ))
    (hrd : ∀ w, rd w) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TParE E).load (cells, secs, offs) Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPath ((TParE E).marks (cells, secs, offs) Λ) I Ab)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo cells (loadSyms Λ secs.rodata))) :
    Correct (TParE E) (SrcSem.source P p) Λ B (cells, secs, offs) :=
  correctX64PE (B := B) himg hss hw hst hload hP hinit hN hsafe hT htk0 hown0
    (X64PromShared.promShared_x64 hP hN (srcMem P p) hsafe hrd hwf hGpl hT) hsvc hrd hwf hG0 hGpl hA hab0

end Spike.Lib.X64Consumer

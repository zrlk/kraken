/-
**The arena consumers' `Correct` without the certification premises at a
`write`** (x86-64), the twin of `Spike/Lib/A64ConsumerAW.lean`: `write` is
a certification dead end (`Spike/Lib/X64WriteDead.lean`), so
`WriteNoPromA` (`hsvc`) and, with the output extern, `PromSharedA`
(`hps`), `PromSharedAE` (`hpsE`) and `WriteNoPromAE` (`hsvcE`) follow from
the node obligations and the take path. Each `_w` theorem is its namesake
with those premises discharged.

- `correctKOnA_w`, `correctKA_w` (`Spike/Lib/X64ConsumerACorrect.lean`);
- `correctKOnA'_w`, `correctKA'_w`, `correctKA_of'_w`, `correctKAE'_w`
  (`Spike/Lib/X64ConsumerAStart.lean`);
- `correctKOnAE_w`, `correctKAEmitE'_w` (`Spike/Lib/X64ConsumerAEStart.lean`).
-/
import Spike.Lib.X64WriteDead

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.DmemPriv (PrivInv)
open Spike.Lib.LowerNode (SrcNumSP PrintLd)
open Scc.Cert.Link

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry} {Top : Ctl → Prop}

/-- **`correctKOnA` with `hsvc` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKOnA_w {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {tcells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)} {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (hl : ld asm Λ = loadParsed (kernel 1) E Λ tcells secs offs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init (s0 P.cap))
    (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem) (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm :=
  correctKOnA hB hl himg hss hw hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 (writeNoPromA_b hN hT) hrd hwf hG0
    hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`correctKA` with `hsvc` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKA_w {B : Budget} (hB : B.cells = ar.cells) {asm : Asm} {tcells : List (Directive × Nat)}
    {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (hpa : cellsOf asm = some tcells) (hd : dataSections asm.text = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0) (hload : ∃ t0, T.load asm Λ = some t0)
    (hP : HookOK P p) (hinit : P.init (s0 P.cap)) (hN : NodesA Λ p (T.marks asm Λ) rd G own ar I)
    (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem) (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS (T.marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, T.load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0) (hc0 : ∀ t0, T.load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKA hB hpa hd himg hss hw hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 (writeNoPromA_b hN hT) hrd hwf hG0
    hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`correctKOnA'` with `hsvc` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKOnA'_w {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {tcells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)} {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ tcells secs offs)
    (himg : imageOk Λ secs code = true) (hss : Scc.Sem.StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0) (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0)
    (hP : HookOK P p) (hinit : P.init s0') (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I)
    (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem) (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm :=
  correctKOnA' hB hl himg hss hw hs hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 (writeNoPromA_b hN hT) (.of_all hrd)
    hwf hG0
    hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`correctKA'` with `hsvc` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKA'_w {B : Budget} (hB : B.cells = ar.cells) {asm : Asm} {tcells : List (Directive × Nat)}
    {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} (hpa : cellsOf asm = some tcells) (hd : dataSections asm.text = some secs)
    (himg : imageOk Λ secs code = true) (hss : Scc.Sem.StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env,
      none⟩ []) (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0) (hload : ∃ t0, T.load asm Λ = some t0)
    (hP : HookOK P p) (hinit : P.init s0') (hN : NodesA Λ p (T.marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem) (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS (T.marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, T.load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0) (hc0 : ∀ t0, T.load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKA' hB hpa hd himg hss hw hs hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 (writeNoPromA_b hN hT) hrd hwf
    hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`correctKA_of'` with `hsvc` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKA_of'_w {B : Budget} (hB : B.cells = ar.cells) {asm : Asm} {tcells : List (Directive × Nat)}
    {secs : DataSecs}
    {code : String → Option Nat} {lsize : Lsize} {name : WeakMem.AllocLabel → String}
    (hpa : cellsOf asm = some tcells) (hd : dataSections asm.text = some secs) (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn (tcells.map (·.1)) = true)
    (hst : I Λ.static lsize (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) c0 [])
    (hfr0 : AllocInv.FreshInv Λ.static (s0 P.cap).lbase (s0 P.cap).n 0 0) (hload : ∃ t0, T.load asm Λ = some t0)
    (hP : HookOK P p) (hinit : P.init (s0 P.cap)) (hN : NodesA Λ p (T.marks asm Λ) rd G own ar I)
    (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p (T.marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, T.load asm Λ = some t0 →
      OwnInit (own (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem) (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, T.load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS (T.marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt Entry.linux Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, T.load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0) (hc0 : ∀ t0, T.load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct T (SrcSem.source P p) Λ B asm :=
  correctKA_of' hB hpa hd himg hss hw hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 (writeNoPromA_b hN hT) hrd hwf
    hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`correctKAE'` with `hsvc` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKAE'_w {B : Budget} (hB : B.cells = ar.cells) {asm : Asm} {tcells : List (Directive × Nat)}
    {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} (hpa : cellsOf asm = some tcells) (hd : dataSections asm.text = some secs)
    (himg : imageOk Λ secs code = true) (hss : Scc.Sem.StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (target (kernel 1) E).load asm Λ = some t0) (hP : HookOK P p) (hinit : P.init s0')
    (hN : NodesA Λ p ((target (kernel 1) E).marks asm Λ) rd G own ar I) (hsafe : SrcSafeS P p I) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p ((target (kernel 1) E).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem) (hrd : ∀ w, rd w)
    (hwf : Λ.WF) (hG0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS ((target (kernel 1) E).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0) :
    Correct (target (kernel 1) E) (SrcSem.source P p) Λ B asm :=
  correctKAE' hB hpa hd himg hss hw hs hst hfr0 hload hP hinit hN hsafe hT htk0 hown0 (writeNoPromA_b hN hT) hrd hwf
    hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0

/-- **`correctKOnAE` with `hps`, `hpsE`, `hsvc`, `hsvcE` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKOnAE_w {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {tcells : List (Directive × Nat)} {secs : DataSecs}
    {offs : List (String × Nat)} {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ tcells secs offs)
    (himg : imageOk Λ secs code = true) (hss : Scc.Sem.StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0) (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0)
    (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p) (hnum : SrcNumSP P p PrintLd) (hinit : P.init s0')
    {ab : Option (State → Prop)} (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I ab)
    (hE : EmitA Λ p I Top) (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hcompE : CompAE Λ P p G own I Top rS Tk ((TOn A ld rs).marks asm Λ) ar) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hEnt : E.clear Λ = true) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm :=
  correctKOnAE hB hl himg hss hw hs hst hfr0 hload hP hW hnum hinit hN hE hsafe hT htk0 hown0
    (promSharedA_b hP hN hsafe hrd hwf hGpl hok hT) (promSharedAE_b hN hT) (writeNoPromA_b hN hT)
    (writeNoPromAE_b hN hT) hcompE hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0 hEnt

/-- **`correctKAEmitE'` with `hps`, `hpsE`, `hsvc`, `hsvcE` discharged** (`write` a certification
dead end, `Spike/Lib/X64WriteDead.lean`). -/
theorem correctKAEmitE'_w {B : Budget} (hB : B.cells = ar.cells) {asm : Asm} {tcells : List (Directive × Nat)}
    {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh} {lsize : Lsize}
    {name : WeakMem.AllocLabel → String} (hpa : cellsOf asm = some tcells) (hd : dataSections asm.text = some secs)
    (himg : imageOk Λ secs code = true) (hss : Scc.Sem.StaticSyms Λ secs code lsize name)
    (hw : wideIn (tcells.map (·.1)) = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (target (kernel 1) E).load asm Λ = some t0) (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hinit : P.init s0') {ab : Option (State → Prop)}
    (hN : NodesA Λ p ((target (kernel 1) E).marks asm Λ) rd G own ar I ab) (hE : EmitA Λ p I Top)
    (hsafe : SrcSafeS P p I) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p ((target (kernel 1) E).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hcompE : CompAE Λ P p G own I Top rS Tk ((target (kernel 1) E).marks asm Λ) ar) (hrd : SrcRd P p rd)
    (hwf : Λ.WF) (hG0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) {Ab : State → Prop}
    (hA : AbortPathS ((target (kernel 1) E).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo tcells (loadSyms Λ secs.rodata))) (hok : ar.OK)
    (hstat : Λ.static = fun _ => none) (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap)
    (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (target (kernel 1) E).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hEnt : E.clear Λ = true) :
    Correct (target (kernel 1) E) (SrcSem.source P p) Λ B asm :=
  correctKAEmitE' hB hpa hd himg hss hw hs hst hfr0 hload hP hW hnum hinit hN hE hsafe hT htk0 hown0
    (promSharedA_b hP hN hsafe hrd hwf hGpl hok hT) (promSharedAE_b hN hT) (writeNoPromA_b hN hT)
    (writeNoPromAE_b hN hT) hcompE hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0 hEnt

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64ConsumerA.correctKOnA_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKOnA_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKA_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKA_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKOnA'_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKOnA'_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKA'_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKA'_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKA_of'_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKA_of'_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKAE'_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKAE'_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKOnAE_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKOnAE_w

/-- info: 'Spike.Lib.X64ConsumerA.correctKAEmitE'_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms correctKAEmitE'_w

end Spike.Lib.X64ConsumerA

/-
**`Correct` through `print`'s `write` at `Top := PrintTop`** on AArch64 (the
twin of `Spike/Lib/X64ConsumerAEPrint.lean`;
`Spike/Lib/A64ConsumerAEStart.lean`'s `correctKOnAE` with its `print`
premises discharged): the components in the middle of the output `write`
(`CompAE`) from `r_componentsAE` (`PrintTop` at the extern's model terms,
`printTop_ext`), the emit rows (`EmitA`) from the node obligations
(`emitA_of_nodes`).

- `compAE_printTop`: `CompAE … PrintTop`;
- `correctKOnAEP`: `correctKOnAE` at `Top := PrintTop`, given in place of
  `hE` and `hcompE` the abort predicate of the node obligations, `printL` at
  `printLD` (`hd`) and the source at `print`'s loop top at every output
  `write` (`hsv`, e.g. `Svc1S` of `nodes2_of_segInW2`); the certification
  premises at the output `write` (`hps`, `hpsE`, `hsvc`, `hsvcE`) from
  `write` being a certification dead end (`Spike/Lib/A64WriteDead.lean`).
-/
import Spike.Lib.A64ConsumerAEComp
import Spike.Lib.A64EmitOfNodes
import Spike.Lib.PrintTopExt
import Spike.Lib.A64WriteDead

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.LowerNode (SrcNumSP PrintLd)
open Spike.Lib.PrintSvc (PrintSvc PrintTop)

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {E : Entry}

/-- **The components in the middle of the output `write` at `PrintTop`**:
`r_componentsAE`, `PrintTop`'s controls at the extern's model terms or
reading no variable (`printTop_ext`). -/
theorem compAE_printTop (hwf : Λ.WF) {rS : Range} {Tk : State → Prop} :
    CompAE Λ P p G own I PrintTop rS Tk μ ar :=
  r_componentsAE hwf fun _ h => Spike.Lib.PrintSvc.printTop_ext h

open Scc.Cert.Link in
/-- **`Correct` through `print`'s `write` at `Top := PrintTop`**
(`correctKOnAE`): the components by `compAE_printTop`, the emit rows by
`emitA_of_nodes` from the node obligations at the abort predicate `Ab'`,
`printL` at `printLD` (`hd`) and the source at `print`'s loop top at every
pair at an output `write` (`hsv`); `hps`, `hpsE`, `hsvc`, `hsvcE` by
`promSharedA_b`, `promSharedAE_b`, `writeNoPromA_b`, `writeNoPromAE_b`. -/
theorem correctKOnAEP {B : Budget} (hB : B.cells = ar.cells) {A : Type} {ld : A → Scc.Sem.Layout → Option T.M.Cfg}
    {rs : A → Scc.Sem.Layout → String → Option Nat} {asm : A} {prog : Program} {secs : DataSecs}
    {code : String → Option Nat} {s0' : TermRun.Cfg} {th0 : TermRun.TTh}
    {lsize : Lsize} {name : WeakMem.AllocLabel → String} (hl : ld asm Λ = loadParsed (kernel 1) E Λ prog secs)
    (himg : imageOk Λ secs code = true)
    (hss : Scc.Sem.StaticSyms Λ secs code lsize name) (hw : wideIn prog = true) (hs : StartOk s0' th0)
    (hst : I Λ.static lsize (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) ⟨th0.term, th0.env, none⟩ [])
    (hfr0 : AllocInv.FreshInv Λ.static s0'.lbase s0'.n 0 0)
    (hload : ∃ t0, (TOn A ld rs).load asm Λ = some t0) (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hinit : P.init s0')
    {Ab' : State → Prop} (hN : NodesA Λ p ((TOn A ld rs).marks asm Λ) rd G own ar I (some Ab'))
    (hd : p.find? (·.name == "printL") = some PrintSrc.printLD)
    (hsv : ∀ lbl lsize s c fs, I lbl lsize s c fs → abi.atSys s = true → ∀ b n,
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 b n) → PrintSvc c fs)
    (hsafe : SrcSafeS P p I)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p ((TOn A ld rs).marks asm Λ) I rS Tk)
    (htk0 : ¬ Tk (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hown0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 →
      OwnInit (own (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)) []) t0.1.mem)
    (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hG0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → MemInv G t0.1.mem)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    {Ab : State → Prop} (hA : AbortPathS ((TOn A ld rs).marks asm Λ) I Ab ar.cells ar.ctr)
    (hab0 : ¬ Ab (threadAt E Λ.code.lo prog (loadSyms Λ secs.rodata)))
    (hok : ar.OK) (hstat : Λ.static = fun _ => none)
    (hsub : (Range.mk ar.heap (16 * ar.cells)).Sub Λ.heap) (hal : ar.heap % 16 = 0)
    (hz0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → ∀ a, (AllocRow.freeR ar.heap ar.cells 0).contains a →
      t0.1.mem.initVal (wordLoc a) = 0)
    (hc0 : ∀ t0, (TOn A ld rs).load asm Λ = some t0 → t0.1.mem.initVal (wordLoc ar.ctr) = 0)
    (hEnt : E.clear Λ = true) :
    Correct (TOn A ld rs) (SrcSem.source P p) Λ B asm :=
  correctKOnAE hB hl himg hss hw hs hst hfr0 hload hP hW hnum hinit hN (emitA_of_nodes hN hT hd hsv) hsafe hT htk0
    hown0 (promSharedA_b hP hN hsafe hrd hwf hGpl hok hT) (promSharedAE_b hN hT) (writeNoPromA_b hN hT)
    (writeNoPromAE_b hN hT) (compAE_printTop hwf) hrd hwf hG0 hGpl hA hab0 hok hstat hsub hal hz0 hc0 hEnt

/--
info: 'Spike.Lib.A64ConsumerA.correctKOnAEP' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms correctKOnAEP

end Spike.Lib.A64ConsumerA

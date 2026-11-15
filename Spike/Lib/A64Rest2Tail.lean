/-
**The open premises of the AArch64 `Accepted2` theorem along a tail of the
text** (`Rest2A` from one output to another with the same data sections,
e.g. the text before and after a post-pass appends its tail): the
premises at the first give them at the second, when the second's loaded
executable holds the first's instruction cells (`TailOK`) and the marks,
`me`'s word, the value invariant and the owned words agree.

- `threadAt_relab`: the second's loaded thread is the first's relabelled;
- `tailOK_threadAt`: `TailOK` from the text `P` closed by the end label
  `te` to `P` followed by a tail `T` with no instruction, every label of
  `T` and `te` in `B`, the instructions of `P` naming none of `B`;
- `print2A_tail`: the `print` premises along the relabelling;
- `rest2A_tail`: `Rest2A` along the relabelling.
-/
import Spike.Lib.LowerA64.Closed2OfA
import Spike.Lib.A64NodesTail
import Spike.Lib.A64ExeTail

namespace Spike.Lib.A64Rest2Tail

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (InvS OwnS TakePathS)
open Spike.Lib.A64ConsumerA (NodesA)
open Spike.Lib.LowerA64 (Rest2A Obl2A Print2A G2 own2 meW2 asm2 th02)
open Spike.Lib.A64RestTail (relab relab_relab instr_of_nodes)
open Spike.Lib.A64NodesTail (TailOK relabI relabI.elim relabI.of nodesA_tail takePathS_tail abortPathS_tail)

/-- **The loaded thread of a text with the same data sections is the
other's relabelled**: the machine state does not see the text. -/
theorem threadAt_relab (E : Entry) (base : Nat) (P Q : Program) (syms : List (String × Nat)) :
    threadAt E base Q syms = relab (threadAt E base Q syms).exe (threadAt E base Q syms).endPc
      (threadAt E base P syms) := rfl

open Kraken.Promising.Lower.A64 (CellAt) in
open Spike.Lib.A64LabelCongr (Directive.Free) in
/-- **The loaded text with a tail holds the instructions of the text closed
by its end label**, off the labels `B` (`te` and the tail's), the tail with
no instruction and fitting the address space. -/
theorem tailOK_threadAt {E : Entry} {base : Nat} {P T : Program} {te : _root_.Label}
    {syms : List (String × Nat)} {B : List _root_.Label} (hte : te ∈ B)
    (hT : ∀ d ∈ T, ∀ l, d = .label l → l ∈ B) (hTi : ∀ d ∈ T, ∀ i, d ≠ .instr i)
    (hc : ∀ p ∈ symsFrom base syms, codeEnd base (P ++ T) ≤ p.2)
    (hone : ∀ p ∈ symsFrom base syms, ∀ q ∈ symsFrom base syms, p.1 = q.1 → p.2 = q.2)
    (hfree : ∀ i, Directive.instr i ∈ P → Directive.Free B (.instr i))
    (hfit : codeEnd base (P ++ T) < 2 ^ 64)
    [hvF : Kraken.Executable.ValidLayout (threadAt E base (P ++ T) syms).exe]
    (hvE : Kraken.Executable.ValidLayout (threadAt E base (P ++ [.label te]) syms).exe) :
    TailOK (threadAt E base (P ++ [.label te]) syms).exe (threadAt E base (P ++ T) syms).exe
      (threadAt E base (P ++ [.label te]) syms).endPc (threadAt E base (P ++ T) syms).endPc B where
  cell s i z hs _ hcell := by
    have hle : codeEnd base (P ++ [.label te]) ≤ codeEnd base (P ++ T) := by
      simp [codeEnd, List.map_append, List.sum_append, Directive.fakeSize]
    exact Spike.Lib.A64ExeTail.cellAt_relab_tail hs hcell
      (Spike.Lib.A64ExeTail.instr_ne_end hs hcell hle hfit)
  lab l hl := (Spike.Lib.A64ExeTail.labels_threadAt_tail hte hT hc hone l hl).symm
  free s i z hs hcell :=
    hfree i (Spike.Lib.A64ExeTail.instr_mem_of_cellAt (X := [.label te]) (by simp) hs hcell)
  valid := hvE

variable {exeE exeF : _root_.Executable} {endE endF : Int64} {B : List _root_.Label}
  {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Spike.Lib.Arena} {I : InvS} {ab : Option (State → Prop)} {rS : Range}
  {Tk : State → Prop}

/-- **The `print` premises along the relabelling.** -/
theorem print2A_tail {P : SrcSem.SrcParams} (hO : TailOK exeE exeF endE endF B)
    (hN : NodesA Λ p μ rd G own ar I ab) (hT : TakePathS Λ p μ I rS Tk) (h : Print2A P p I ab) :
    Print2A P p (relabI exeE exeF endE endF I) (ab.map (· ∘ relab exeE endE)) where
  hsome := by cases ab <;> simp_all [h.hsome]
  hext := h.hext
  hsv lbl lsize s c fs hI hsys b n hd := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    rw [hk.1] at hsys
    rw [hk.2.1, hk.2.2.1] at hd
    exact h.hsv lbl lsize s0 c fs hI0 hsys b n hd

/-- **`Rest2A` along a tail of the text**: from the output `oE` to `oF` with
the same data sections (`hsecs`), the second's loaded executable holding
the first's instruction cells (`hO`), and the marks (`hμ`), `me`'s word
(`hme`), the value invariant (`hG`) and the owned words read through the
relabelling (`hown`) agreeing. -/
theorem rest2A_tail {pcfg : Scc.Cert.PlaceOK.Config} {oE oF : Scc.Cert.PlaceOK.A64.Out}
    {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true} {arch : WeakMem.Arch} {E : Entry}
    (hsecs : oF.secs = oE.secs)
    (hO : TailOK (threadAt E Λ.code.lo oE.prog (loadSyms Λ oE.secs.rodata)).exe
      (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).exe
      (threadAt E Λ.code.lo oE.prog (loadSyms Λ oE.secs.rodata)).endPc
      (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).endPc B)
    (hμ : (Spike.Lib.A64Consumer.TParE E).marks (asm2 oF) Λ = (Spike.Lib.A64Consumer.TParE E).marks (asm2 oE) Λ)
    (hme : meW2 Λ oF = meW2 Λ oE) (hG : G2 hF p = G2 hE p)
    (hown : ∀ s fs, own2 hF p (relab (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).exe
      (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).endPc s) fs = own2 hE p s fs)
    (h : Rest2A Λ p hE arch E) : Rest2A Λ p hF arch E := by
  obtain ⟨I, rS, Tk, Ab, ab, hst, hN, hpr, hT, htk0, hA, hab0⟩ := h
  rw [← hμ, ← hme, ← hG] at *
  let sE := threadAt E Λ.code.lo oE.prog (loadSyms Λ oE.secs.rodata)
  let sF := threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)
  have hs : sE.exe = sE.exe ∧ sE.endPc = sE.endPc := ⟨rfl, rfl⟩
  refine ⟨relabI sE.exe sF.exe sE.endPc sF.endPc I, rS, Tk ∘ relab sE.exe sE.endPc,
    Ab ∘ relab sE.exe sE.endPc, ab.map (· ∘ relab sE.exe sE.endPc), ?_⟩
  rw [hsecs]
  exact {
    hst := relabI.of hs hst
    hN := nodesA_tail hO hN hT hown
    hpr := hpr.imp (fun h => by rw [h]; rfl) (print2A_tail hO hN hT)
    hT := takePathS_tail hO hN hT
    htk0 := htk0
    hA := abortPathS_tail hO hN hT hA
    hab0 := hab0 }

end Spike.Lib.A64Rest2Tail

/-- info: 'Spike.Lib.A64Rest2Tail.rest2A_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.rest2A_tail

/-- info: 'Spike.Lib.A64Rest2Tail.tailOK_threadAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.tailOK_threadAt

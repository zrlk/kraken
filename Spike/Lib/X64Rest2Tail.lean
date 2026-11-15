/-
**The open premises of the x86-64 `Accepted2` theorem along a tail of the
text** (`Rest2X` from one output to another with the same data sections,
e.g. the cells before and after a post-pass appends its tail): the premises
at the first give them at the second, when the second's loaded executable
holds the first's instruction cells (`TailOK`) and the marks, `me`'s word,
the value invariant and the owned words agree. The AArch64 twin is
`Spike/Lib/A64Rest2Tail.lean`.

- `threadAt_relab`: the second's loaded thread is the first's relabelled;
- `tailOK_threadAt`: `TailOK` from the cells `P` closed by the end label
  `te` to `P` followed by a tail `T` with no instruction, every label of
  `T` and `te` in `B`, the instructions of `P` naming none of `B`;
- `print2X_tail`: the `print` premises along the relabelling;
- `rest2X_tail`: `Rest2X` along the relabelling.
-/
import Spike.Lib.LowerX64.Closed2Of
import Spike.Lib.X64NodesTail
import Spike.Lib.X64ExeTail

namespace Spike.Lib.X64Rest2Tail

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Spike.Lib.X64ConsumerS (InvS OwnS TakePathS)
open Spike.Lib.X64ConsumerA (NodesA)
open Spike.Lib.LowerX64 (Rest2X Obl2X Print2X G2 own2 meW2 asm2 th02)
open Spike.Lib.X64RestTail (relab)
open Spike.Lib.X64NodesTail (TailOK relabI relabI.elim relabI.of relab_relab instr_of_nodes nodesA_tail_own
  takePathS_tail abortPathS_tail)

/-- **The loaded thread of cells with the same data sections is the other's
relabelled**: the machine state does not see the cells. -/
theorem threadAt_relab (E : Entry) (base : Nat) (P Q : List (Directive × Nat)) (syms : List (String × Nat)) :
    threadAt E base Q syms = relab (threadAt E base Q syms).exe (threadAt E base Q syms).endPc
      (threadAt E base P syms) := rfl

open Kraken.Promising.Lower.X64 (CellAt) in
open Spike.Lib.X64LabelCongr (Directive.Free) in
/-- **The loaded cells with a tail hold the instructions of the cells closed
by their end label**, off the labels `B` (`te` and the tail's), the tail with
no instruction and fitting the address space. -/
theorem tailOK_threadAt {E : Entry} {base : Nat} {P T : List (Directive × Nat)} {te : Label}
    {syms : List (String × Nat)} {B : List Label} (hte : te ∈ B)
    (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hc : ∀ p ∈ symsFrom base syms, codeEnd base (P ++ T) ≤ p.2)
    (hone : ∀ p ∈ symsFrom base syms, ∀ q ∈ symsFrom base syms, p.1 = q.1 → p.2 = q.2)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hfit : codeEnd base (P ++ T) < 2 ^ 64)
    [hvF : Kraken.Executable.ValidLayout (threadAt E base (P ++ T) syms).exe]
    (hvE : Kraken.Executable.ValidLayout (threadAt E base (P ++ [(.label te, 0)]) syms).exe) :
    TailOK (threadAt E base (P ++ [(.label te, 0)]) syms).exe (threadAt E base (P ++ T) syms).exe
      (threadAt E base (P ++ [(.label te, 0)]) syms).endPc (threadAt E base (P ++ T) syms).endPc B where
  cell s i z hs _ hcell := by
    have hle : codeEnd base (P ++ [(.label te, 0)]) ≤ codeEnd base (P ++ T) := by
      simp only [codeEnd, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    exact Spike.Lib.X64ExeTail.cellAt_relab_tail hs hcell
      (Spike.Lib.X64ExeTail.instr_ne_end hs hcell hle hfit)
  lab l hl := (Spike.Lib.X64ExeTail.labels_threadAt_tail hte hT hc hone l hl).symm
  free s i z hs hcell :=
    hfree i z (Spike.Lib.X64ExeTail.instr_mem_of_cellAt (X := [(.label te, 0)])
      (by intro dz hdz i; simp only [List.mem_singleton] at hdz; subst hdz; exact fun h => nomatch h) hs hcell)
  valid := hvE

variable {exeE exeF : _root_.Executable} {endE endF : Int64} {B : List Label}
  {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : OwnS} {ar : Spike.Lib.Arena} {I : InvS} {ab : Option (State → Prop)} {rS : Range}
  {Tk : State → Prop}

/-- **The `print` premises along the relabelling.** -/
theorem print2X_tail {P : SrcSem.SrcParams} (hO : TailOK exeE exeF endE endF B)
    (hN : NodesA Λ p μ rd G own ar I ab) (hT : TakePathS Λ p μ I rS Tk) (h : Print2X P p I ab) :
    Print2X P p (relabI exeE exeF endE endF I) (ab.map (· ∘ relab exeE endE)) where
  hsome := by cases ab <;> simp_all [h.hsome]
  hext := h.hext
  hsv lbl lsize s c fs hI hsys b n hd := by
    obtain ⟨s0, hs0, rfl, hI0⟩ := relabI.elim hI
    obtain ⟨i, z, hc⟩ := instr_of_nodes hN hT hI0 (hs0.1 ▸ hO.valid)
    have hk := hO.abi hs0 hc
    rw [hk.1] at hsys
    rw [hk.2.1, hk.2.2.1] at hd
    exact h.hsv lbl lsize s0 c fs hI0 hsys b n hd

/-- **`Rest2X` along a tail of the text**: from the output `oE` to `oF` with
the same data sections (`hsecs`), the second's loaded executable holding
the first's instruction cells (`hO`), and the marks (`hμ`), `me`'s word
(`hme`), the value invariant (`hG`) and the owned words read through the
relabelling (`hown`) agreeing. -/
theorem rest2X_tail {pcfg : Scc.Cert.PlaceOK.Config} {oE oF : Scc.Cert.PlaceOK.X64.Out}
    {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true} {arch : WeakMem.Arch} {E : Entry}
    (hsecs : oF.secs = oE.secs)
    (hO : TailOK (threadAt E Λ.code.lo oE.prog (loadSyms Λ oE.secs.rodata)).exe
      (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).exe
      (threadAt E Λ.code.lo oE.prog (loadSyms Λ oE.secs.rodata)).endPc
      (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).endPc B)
    (hμ : (Spike.Lib.X64Consumer.TParE E).marks (asm2 oF) Λ = (Spike.Lib.X64Consumer.TParE E).marks (asm2 oE) Λ)
    (hme : meW2 Λ oF = meW2 Λ oE) (hG : G2 hF p = G2 hE p)
    (hown : ∀ s fs, own2 hF p (relab (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).exe
      (threadAt E Λ.code.lo oF.prog (loadSyms Λ oE.secs.rodata)).endPc s) fs = own2 hE p s fs)
    (h : Rest2X Λ p hE arch E) : Rest2X Λ p hF arch E := by
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
    hN := nodesA_tail_own hO hN hT hown
    hpr := hpr.imp (fun h => by rw [h]; rfl) (print2X_tail hO hN hT)
    hT := takePathS_tail hO hN hT
    htk0 := htk0
    hA := abortPathS_tail hO hN hT hA
    hab0 := hab0 }

end Spike.Lib.X64Rest2Tail

/-- info: 'Spike.Lib.X64Rest2Tail.rest2X_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2Tail.rest2X_tail

/-- info: 'Spike.Lib.X64Rest2Tail.tailOK_threadAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2Tail.tailOK_threadAt

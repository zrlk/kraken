/-
**`print`'s and the allocator's calls with their abort paths, one segment
each** (AArch64): the abort exit of a call (`print`'s `scc_rt_abort(4)` when
the `write` system call fails, the allocator's `scc_rt_abort(2)` when the
arena is full) composed with the abort path from there
(`Spike/Lib/A64AbortWriteW.lean`, `Spike/Lib/A64AbortHeapW.lean`), which does
not return; what is left are the call's normal exits.

- `RtAbort.PrintFits`, `RtAbort.AllocFits`: the region facts of a call of
  `print` / `scc_rt_alloc` and of `scc_rt_abort` at its abort exit, in a
  region `T` based at the caller's `sp` at the `bl`, in the form
  `RtDepthA64.print_fits` / `alloc_fits` give them from
  `T.lo ≤ -rtDepth`; `PrintFits.lo`, `AllocFits.lo`: the depth they give
  (`96`, `208`).
- `RtAbort.paN`: the caller's node at `print`'s abort exit (`x0 = 4`, the
  source in `print`'s loop, the caller's cells outside `print`'s region as
  at the call).
- `print_call_abort_segW`: `print_call_segW` with its `habort` landing at
  `paN`, then `seg_jabort4W` from there; the caller's region below the call
  is `T` (`hTR`, `hfit`).
- `newBuf_call_abortW`: `newBuf_callW` with its heap abort exit continued
  by `seg_jabort2W`, to the return alone.
-/
import Spike.Lib.A64PrintCall
import Spike.Lib.A64NewBuf
import Spike.Lib.A64AbortHeapW
import Spike.Lib.A64AbortWriteW

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow.Ret0 (CallerCells)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull)
open PrintCall NewBuf

namespace RtAbort

/-- **`print`'s region facts in the caller's region `T`** below the `bl`:
`seg_print`'s `hlo` in `T`, and `scc_rt_abort`'s region at `print`'s abort
exit `e` (`T.callee e (-48) 0`) `OK`, 16-aligned, with `seg_abort`'s bounds,
inside `T` (the form of `RtDepthA64.print_fits`). -/
def PrintFits (T : Region) : Prop :=
  ∀ (lab : Label → Int64) (c0 : Ctl) (x29 ra : BitVec 64),
    let e := (Spike.Lib.A64.Print.E lab c0 x29 ra .abort).o.sp
    T.lo ≤ -48 ∧ (T.callee e (-48) 0).OK ∧ (T.callee e (-48) 0).base.toNat % 16 = 0 ∧
      (T.callee e (-48) 0).lo ≤ -48 ∧ 0 ≤ (T.callee e (-48) 0).hi ∧ T.lo ≤ e + (T.callee e (-48) 0).lo ∧
      e + (T.callee e (-48) 0).hi ≤ T.hi

/-- **The allocator's region facts in the caller's region `T`** below the
`bl`: `seg_alloc`'s `hlo` in `T`, and `scc_rt_abort`'s region at the heap
abort exit `e` (`T.callee e (-48) 0`) `OK`, 16-aligned, with `seg_abort`'s
bounds, inside `T` (the form of `RtDepthA64.alloc_fits`). -/
def AllocFits (T : Region) : Prop :=
  ∀ (lab : Label → Int64) (ms : MemSide isaLSE2) (q : Call) (lbl : WeakMem.AllocLabel → Option Nat),
    let e := (Spike.Lib.A64.Alloc.E lab ms q lbl .abort).o.sp
    T.lo ≤ -160 ∧ (T.callee e (-48) 0).OK ∧ (T.callee e (-48) 0).base.toNat % 16 = 0 ∧
      (T.callee e (-48) 0).lo ≤ -48 ∧ 0 ≤ (T.callee e (-48) 0).hi ∧ T.lo ≤ e + (T.callee e (-48) 0).lo ∧
      e + (T.callee e (-48) 0).hi ≤ T.hi

/-- `PrintFits` reaches 96 bytes below the `bl`: `print`'s abort exit at
`-48` and `scc_rt_abort`'s 48 below it (given any source control, which
the facts are stated for). -/
theorem PrintFits.lo {T : Region} (h : PrintFits T) (c0 : Ctl) : T.lo ≤ -96 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := h (fun _ => 0) c0 0 0
  simp only [Region.callee] at h6
  exact h6

/-- `AllocFits` reaches 208 bytes below the `bl`: the heap abort exit at
`-160` and `scc_rt_abort`'s 48 below it (given any call, which the facts
are stated for). -/
theorem AllocFits.lo {T : Region} (h : AllocFits T) (ms : MemSide isaLSE2) (q : Call)
    (lbl : WeakMem.AllocLabel → Option Nat) : T.lo ≤ -208 := by
  obtain ⟨-, -, -, -, -, h6, -⟩ := h (fun _ => 0) ms q lbl
  simp only [Region.callee] at h6
  exact h6

/-- **The caller's node at `print`'s abort exit** from the call node `nC`
in the caller's region `R`: pc `scc_rt_abort`, `sp` 48 below the call's,
`x0 = 4`, the source in `print`'s loop on the arguments of a state `σC` of
`nC`, the caller's cells outside `print`'s region as in `σC`. -/
def paN (lab : Label → Int64) (R : Region) (nC : ND) (pw wn : AS → TermRun.Word) (n m : AS → Nat) : ND :=
  ⟨lab "scc_rt_abort", ⟨nC.o.sp + -48, []⟩, fun σ c => σ.regs.X0 = 4 ∧ ∃ σC c0 k, nC.J σC c0 ∧
    PrintC (pw σC) (wn σC) (n σC) (m σC) k c ∧
    ∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σ.slot k = σC.slot k⟩

end RtAbort

open RtAbort

/-- A segment from a node, given a state of its invariant. -/
theorem SegW.of_someJ {W : Frag isaLSE2} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} {Q : Frag isaLSE2}
    (h : ∀ σ c, n.J σ c → SegW W K p lbl ms (At exe endPc R F n) Q) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  refine (SegW.of_imp (L := ∃ σ c, n.J σ c) fun ⟨σ, c, hJ⟩ => h σ c hJ).mono_pre fun s c hA => ⟨hA, ?_⟩
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
  exact ⟨σ, c, hJ⟩

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A call of `print` with its abort path is one segment inside `W`**,
from any call node `nC` to the caller's nodes `N` and exits `E`:
`print_call_segW`, its abort landing at `paN` (`print`'s abort exit, `sp`
at `nC.o.sp - 48`), and from there `seg_jabort4W` (the dispatcher at the
write code and `scc_rt_abort_write`, in the region below), which does not
return. The caller's region below the `bl` is `T` (`hTR`), with `print`'s
region facts there (`hfit`, as `RtDepthA64.print_fits` gives them): they
give `print_call_segW`'s `hlo` and the abort path's. The abort path's
obligations are asked at `paN`'s states (`hstub`); the other premises are
`print_call_segW`'s. -/
theorem print_call_abort_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive}
    {kp : Nat} {nC : ND} {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat} {T : Region}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp)
    (hprog : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hTR : R.lo ≤ nC.o.sp + T.lo) (hfit : PrintFits T)
    (hhi : nC.o.sp < R.hi) (hk16 : nC.o.sp % 16 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → σ.regs.X1.toBitVec.toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.X29.toBitVec σC.regs.X30.toBitVec σC.regs.X0.toBitVec
      σC.regs.X1.toBitVec.toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR nC.o.sp R)
      (pF nC.o.sp R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR nC.o.sp R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) σC .svc) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c →
      σR.regs.X29.toBitVec = σC.regs.X29.toBitVec → σR.regs.X30.toBitVec = σC.regs.X30.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR nC.o.sp R).Off (k - nC.o.sp) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec σC.regs.X30.toBitVec, ⟨nC.o.sp, []⟩, σR⟩ c')
    -- the abort path below `print`'s abort exit
    (hstub : ∀ m0 σA c0, (paN (_root_.Executable.labels exe).label R nC pw wn n m).J σA c0 →
      Abort.Disp.StubWW W K p lbl ms exe endPc (R.callee (nC.o.sp + -48) (-48) 0)
        (fun m' => F m' ∧ CKept R (nC.o.sp + -48) (-48) 0 m0 m' ∧ Abs R ⟨nC.o.sp + -48, []⟩ m0 σA) c0) :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  refine SegW.of_someJ fun _ c0 _ => ?_
  have hT : T.lo ≤ -96 := hfit.lo c0
  let nA := paN (_root_.Executable.labels exe).label R nC pw wn n m
  have hA : SegW W K p lbl ms (At exe endPc R F nA) (Next exe endPc R F N E) :=
    Abort.Disp.seg_jabort4W (nC := nA) rfl (fun σ c h => by rw [h.1]; rfl) hF hR hal
      (by show R.lo ≤ nC.o.sp + -48 - 48; omega) (by show nC.o.sp + -48 < R.hi; omega)
      (by show (nC.o.sp + -48) % 16 = 0; omega) hK hstub
  have h1 := print_call_segW (N := fun x : PSum ι PUnit.{1} => match x with | .inl i => N i | .inr _ => nA) (E := E)
    hp hend hprog hF hR hal (by omega) hhi hk16 hpc hP0 hN hm hW hd hE hK hcl
    (fun σC c hJ F' _ => hWs σC c hJ F') (fun σC c hJ F' _ => hlb σC c hJ F')
    (fun σC c hJ F' _ => hwe σC c hJ F')
    (fun σC c σR c' hJ h29 h30 hP hsl => (hret σC c σR c' hJ h29 h30 hP hsl).elim
      (fun ⟨j, h⟩ => .inl ⟨.inl j, h⟩) .inr)
    (fun σC c σR c' k hJ h4 hP hsl => .inl ⟨.inr ⟨⟩, rfl, by simp [SO.le, nA, paN], h4, σC, c, k, hJ, hP, hsl⟩)
  refine ((h1.mono_post ?_).seq_left hA).mono_post fun _ _ h => h.elim id id
  rintro s c (⟨⟨j⟩ | ⟨⟩, h⟩ | h)
  · exact .inr (.inl ⟨j, h⟩)
  · exact .inl h
  · exact .inr (.inr h)

/-- **A buffer allocation's call with its heap abort path is one segment
inside `W`**, from the allocator's entry to its return at `pcR` alone:
`newBuf_callW`, its heap abort exit (`sp` at `-allocAbortDepth fs`)
continued by `seg_jabort2W` (the dispatcher at the heap code and
`scc_rt_abort_heap`, in the region below), which does not return. The
caller's region below the `bl` is `T` (`hTR`), with the allocator's region
facts there (`hfit`, as `RtDepthA64.alloc_fits` gives them): they give
`newBuf_callW`'s `hlo` and the abort path's. The abort path's obligations
are asked at the heap abort exit's states (`hstub`); the other premises are
`newBuf_callW`'s. -/
theorem newBuf_call_abortW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hprog : allocIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    {fs : Int} {T : Region} (hfs : fs % 16 = 0) (hTR : R.lo ≤ -fs + T.lo) (hfit : AllocFits T)
    (hkc : -fs < R.hi) (hK : ms.K = some Scc.Sem.A64.abi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.X0.toBitVec = q.h ∧ σ.regs.X1.toBitVec = q.k ∧ σ.regs.X2.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.regs.X30.toBitVec = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : {q : Call // q.OK ms (_root_.Executable.labels exe).label}, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs) σC) c ∧
        CKept R (-fs) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs) (-160) 0) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs) (-160) 0) (fun m => F m ∧ CallerCells R (-fs) (-160) 0 m))
    (hstub : ∀ m0 σA c0, (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .abort).J σA c0 →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-allocAbortDepth fs) (-48) 0)
        (fun m => F m ∧ CKept R (-allocAbortDepth fs) (-48) 0 m0 m ∧ Abs R ⟨-allocAbortDepth fs, []⟩ m0 σA)
        c0) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs, []⟩, Jc⟩)
      (At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .ret)) := by
  refine SegW.of_someJ fun σ0 c0 hJ0 => ?_
  obtain ⟨q, -⟩ := hq σ0 c0 hJ0
  have hT : T.lo ≤ -208 := hfit.lo ms q lbl
  have hA := Abort.Disp.seg_jabort2W (W := W) (K := K) (p := p) (Q := At exe endPc R F
      (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .ret))
    (nC := nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .abort) rfl
    (fun σ c h => by
      have h2 : σ.regs.X0 = 2 := h.1
      rw [h2]; rfl) hF hR hal
    (by show R.lo ≤ -allocAbortDepth fs - 48; simp only [allocAbortDepth, allocFrame]; omega)
    (by show -allocAbortDepth fs < R.hi; simp only [allocAbortDepth, allocFrame]; omega)
    (by show (-allocAbortDepth fs) % 16 = 0; simp only [allocAbortDepth, allocFrame]; omega) hK hstub
  have h1 := newBuf_callW (p := p) (lbl := lbl) (W := W) (K := K) hp hend hprog hF hR hal hfs
    (by simp only [allocAbortDepth, allocFrame]; omega) hkc hq hra hmem hxa
    fun q _ h => hW q h
  refine ((h1.mono_post ?_).seq_left hA).mono_post fun _ _ h => h.elim id id
  rintro s c ⟨⟨⟩ | ⟨⟩, h⟩
  · exact .inr h
  · exact .inl h

end Fn

end Spike.Lib.A64.Flow

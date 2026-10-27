/-
**`print`'s and the allocator's calls with their abort paths, one segment
each** (x64): the x64 twin of `Spike/Lib/A64RtAbortSeg.lean`. The abort exit
of a call (`print`'s `scc_rt_abort(4)` when the `write` system call fails,
the allocator's `scc_rt_abort(2)` when the arena is full) composed with the
abort path from there (`Spike/Lib/X64AbortWriteW.lean`,
`Spike/Lib/X64AbortHeapW.lean`), which does not return; what is left are
the call's normal exits.

- `RtAbort.PrintFits`, `RtAbort.AllocFits`: the region facts of a call of
  `print` / `scc_rt_alloc` and of `scc_rt_abort` at its abort exit, in a
  region `T` based at the caller's `%rsp` at the `call`, in the form
  `RtDepthX64.print_fits` / `alloc_fits` give them from
  `T.lo ≤ -rtDepth`; `PrintFits.lo`, `AllocFits.lo`: the depth they give
  (`88`, `200`).
- `RtAbort.paN`: the caller's node at `print`'s abort exit (`%rdi = 4`, the
  source in `print`'s loop, the caller's cells outside `print`'s region as
  at the call).
- `print_call_abort_segW`: `print_call_segW` with its `habort` landing at
  `paN`, then `seg_jabort4W` from there; the caller's region below the
  `call` is `T` (`hTR`, `hfit`).
- `newBuf_call_abortW`: `newBuf_callW` with its heap abort exit continued
  by `seg_jabort2W`, to the return alone.
-/
import Spike.Lib.X64PrintCall
import Spike.Lib.X64NewBuf
import Spike.Lib.X64AbortHeapW
import Spike.Lib.X64AbortWriteW

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib
open Spike.Lib.X64.Flow.Ret0 (CallerCells)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD)
open Spike.Lib.X64.Alloc (Call AllocW Ea Jfull)
open Spike.Lib.X64.Flow.Hello1 (AG)
open PrintCall Spike.Lib.X64.Flow.NewBuf

namespace RtAbort

/-- **`print`'s region facts in the caller's region `T`** below the `call`:
`print`'s region `P` (entered with the return address pushed) `OK`, with
`seg_print`'s bounds, inside `T`, and `scc_rt_abort`'s region `A` at
`print`'s abort exit, `T.callee (-64) (-24) 16`, `OK`, with `seg_abort`'s
bounds, inside `T` (the form of `RtDepthX64.print_fits`). -/
def PrintFits (T : Region) : Prop :=
  ∀ (lab : Label → Int64) (c0 : Ctl) (rbp0 ra : BitVec 64),
    let P := T.callee (-8 - Spike.Lib.X64.Print.oE.sp) (-40) 16
    let A := P.callee ((Spike.Lib.X64.Print.E lab c0 rbp0 ra .abort).o.sp - Spike.Lib.X64.Abort.oE.sp) (-24) 16
    (P.OK ∧ P.lo ≤ -40 ∧ 16 ≤ P.hi ∧ T.lo ≤ -16 + P.lo ∧ -16 + P.hi ≤ T.hi) ∧
      A = T.callee (-64) (-24) 16 ∧
      (A.OK ∧ A.lo ≤ -24 ∧ 16 ≤ A.hi ∧ T.lo ≤ -64 + A.lo ∧ -64 + A.hi ≤ T.hi)

/-- **The allocator's region facts in the caller's region `T`** below the
`call`: the allocator's region `L` `OK`, with `seg_alloc`'s bounds, inside
`T`, and `scc_rt_abort`'s region `A` at the heap abort exit,
`T.callee (-176) (-24) 16`, `OK`, with `seg_abort`'s bounds, inside `T`
(the form of `RtDepthX64.alloc_fits`). -/
def AllocFits (T : Region) : Prop :=
  ∀ (lab : Label → Int64) (ms : MemSide isa) (q : Call) (lbl : WeakMem.AllocLabel → Option Nat),
    let L := T.callee (-8 - (Spike.Lib.X64.Alloc.N lab ms q .e).o.sp) (-160) 8
    let A := L.callee ((Spike.Lib.X64.Alloc.E lab ms q lbl .abort).o.sp - Spike.Lib.X64.Abort.oE.sp) (-24) 16
    (L.OK ∧ L.lo ≤ -160 ∧ 8 ≤ L.hi ∧ T.lo ≤ -8 + L.lo ∧ -8 + L.hi ≤ T.hi) ∧
      A = T.callee (-176) (-24) 16 ∧
      (A.OK ∧ A.lo ≤ -24 ∧ 16 ≤ A.hi ∧ T.lo ≤ -176 + A.lo ∧ -176 + A.hi ≤ T.hi)

/-- `PrintFits` reaches 88 bytes below the `call`: `scc_rt_abort`'s 24
below its entry at `print`'s abort exit, 64 below the `call` (given any
source control, which the facts are stated for). -/
theorem PrintFits.lo {T : Region} (h : PrintFits T) (c0 : Ctl) : T.lo ≤ -88 := by
  obtain ⟨-, -, -, -, -, h4, -⟩ := h (fun _ => 0) c0 0 0
  simp only [Region.callee] at h4
  omega

/-- `AllocFits` reaches 200 bytes below the `call`: `scc_rt_abort`'s 24
below its entry at the heap abort exit, 176 below the `call` (given any
call, which the facts are stated for). -/
theorem AllocFits.lo {T : Region} (h : AllocFits T) (ms : MemSide isa) (q : Call)
    (lbl : WeakMem.AllocLabel → Option Nat) : T.lo ≤ -200 := by
  obtain ⟨-, -, -, -, -, h4, -⟩ := h (fun _ => 0) ms q lbl
  simp only [Region.callee] at h4
  omega

/-- **The caller's node at `print`'s abort exit** from the call node `nC`
in the caller's region `R`: pc `scc_rt_abort`, `%rsp` at `print`'s abort
exit (`nC.o.sp - 8 + -40`), `%rdi = 4`, the source in `print`'s loop on the
arguments of a state `σC` of `nC`, the caller's cells outside `print`'s
region as in `σC`. -/
def paN (lab : Label → Int64) (R : Region) (nC : ND) (pw wn : AS → TermRun.Word) (n m : AS → Nat) : ND :=
  ⟨lab "scc_rt_abort", ⟨nC.o.sp - 8 + -40, []⟩, fun σ c => σ.regs.get64 .rdi = 4 ∧ ∃ σC c0 k, nC.J σC c0 ∧
    PrintC (pw σC) (wn σC) (n σC) (m σC) k c ∧
    ∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σ.slot k = σC.slot k⟩

end RtAbort

open RtAbort

/-- A segment from a node, given a state of its invariant. -/
theorem SegW.of_someJ {W : Frag isa} {K : State → State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n : ND} {Q : Frag isa}
    (h : ∀ σ c, n.J σ c → SegW W K p lbl ms (At exe endPc R F n) Q) :
    SegW W K p lbl ms (At exe endPc R F n) Q := by
  refine (SegW.of_imp (L := ∃ σ c, n.J σ c) fun ⟨σ, c, hJ⟩ => h σ c hJ).mono_pre fun s c hA => ⟨hA, ?_⟩
  obtain ⟨-, -, -, -, σ, -, -, hJ⟩ := hA
  exact ⟨σ, c, hJ⟩

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}

/-- **A call of `print` with its abort path is one segment inside `W`**,
from any call node `nC` to the caller's nodes `N` and exits `E`:
`print_call_segW`, its abort landing at `paN` (`print`'s abort exit), and
from there `seg_jabort4W` (the dispatcher at the write code and
`scc_rt_abort_write`, in the region below), which does not return. The
caller's region below the `call` (at `nC.o.sp + 8`, above the pushed return
address) is `T` (`hTR`), with `print`'s region facts there (`hfit`, as
`RtDepthX64.print_fits` gives them): they give `print_call_segW`'s `hlo`
and the abort path's. The abort path's obligations are asked at `paN`'s
states (`hstub`); the other premises are `print_call_segW`'s. -/
theorem print_call_abort_segW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)}
    {kp : Nat} {nC : ND} {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wn : AS → TermRun.Word} {n m : AS → Nat} {T : Region}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hprog : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    (hTR : R.lo ≤ nC.o.sp + 8 + T.lo) (hfit : PrintFits T)
    (hhi : nC.o.sp - 8 + 16 ≤ R.hi) (hk8 : (nC.o.sp - 8) % 8 = 0)
    (hpc : nC.pc = (_root_.Executable.labels exe).label "scc_rt_print")
    -- the call site
    (hP0 : ∀ σ c, nC.J σ c → PrintC (pw σ) (wn σ) (n σ) (m σ) 0 c)
    (hN : ∀ σ c, nC.J σ c → (σ.regs.get64 .rsi).toNat = printN (n σ) (m σ))
    (hm : ∀ σ c, nC.J σ c → 8 * m σ < 2 ^ 63)
    (hW : ∀ σC c, nC.J σC c → PrintA.PrintAW σC.regs.rbp.toBitVec (σC.slot nC.o.sp) (σC.regs.get64 .rdi)
      (σC.regs.get64 .rsi).toNat (pcS pw wn n m σC) (pcS pw wn n m σC) W K exe endPc (pR (nC.o.sp - 8) R)
      (pF (nC.o.sp - 8) R F))
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.X64.abi) (hcl : LocalClosed p BO)
    (hWs : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      W s c' ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k j, k + j < printN (n σC) (m σC) →
      BO s ((σC.regs.get64 .rdi + BitVec.ofNat 64 k).toNat + j) (loadC (pw σC) (wn σC) (m σC) (k + j))
        (fun c => ∃ mw b, c = nextC (pw σC) (wn σC) (m σC) (k + j) mw b))
    (hwe : ∀ σC c, nC.J σC c → ∀ (F' : MachineData → Prop) s c', At exe endPc (pR (nC.o.sp - 8) R) F'
      (pN (_root_.Executable.labels exe).label (pcS pw wn n m) (pcS pw wn n m) nC.o.sp σC .sys) s c' →
      ∀ k c1, PrintC (pw σC) (wn σC) (n σC) (m σC) k c1 → WE s c1)
    -- where the return lands
    (hret : ∀ σC c σR c', nC.J σC c → σR.regs.get64 .rbp = σC.regs.rbp.toBitVec →
      PrintC (pw σC) (wn σC) (n σC) (m σC) (printN (n σC) (m σC)) c' →
      (∀ k, R.Off k → ¬ (pR (nC.o.sp - 8) R).Off (k - (nC.o.sp - 8)) → σR.slot k = σC.slot k) →
      Lands N E ⟨Int64.ofBitVec (σC.slot nC.o.sp), ⟨nC.o.sp + 8, []⟩, σR⟩ c')
    -- the abort path below `print`'s abort exit
    (hstub : ∀ m0 σA c0, (paN (_root_.Executable.labels exe).label R nC pw wn n m).J σA c0 →
      Abort.Disp.StubWW W K p lbl ms exe endPc (R.callee (nC.o.sp - 8 + -40 - 8) (-24) 16)
        (fun m' => F m' ∧ CKept R (nC.o.sp - 8 + -40 - 8) (-24) 16 m0 m' ∧
          Abs R ⟨nC.o.sp - 8 + -40, []⟩ m0 σA) c0) :
    SegW W K p lbl ms (At exe endPc R F nC) (Next exe endPc R F N E) := by
  refine SegW.of_someJ fun _ c0 _ => ?_
  have hT : T.lo ≤ -88 := hfit.lo c0
  let nA := paN (_root_.Executable.labels exe).label R nC pw wn n m
  have hA : SegW W K p lbl ms (At exe endPc R F nA) (Next exe endPc R F N E) :=
    Abort.Disp.seg_jabort4W (nC := nA) rfl (fun σ c h => h.1) hF hR
      (by show R.lo ≤ nC.o.sp - 8 + -40 - 32; omega) (by show nC.o.sp - 8 + -40 + 8 ≤ R.hi; omega)
      (by show (nC.o.sp - 8 + -40) % 8 = 0; omega) hK hstub
  have h1 := print_call_segW (N := fun x : PSum ι PUnit.{1} => match x with | .inl i => N i | .inr _ => nA)
    (E := E) hp hend hprog hF hR (by omega) hhi hk8 hpc hP0 hN hm hW hd hE hK hcl
    (fun σC c hJ F' _ => hWs σC c hJ F') (fun σC c hJ F' _ => hlb σC c hJ F')
    (fun σC c hJ F' _ => hwe σC c hJ F')
    (fun σC c σR c' hJ hbp hP hsl => (hret σC c σR c' hJ hbp hP hsl).elim
      (fun ⟨j, h⟩ => .inl ⟨.inl j, h⟩) .inr)
    (fun σC c σR c' k hJ h4 hP hsl => .inl ⟨.inr ⟨⟩, rfl, by simp [SO.le, nA, paN], h4, σC, c, k, hJ, hP, hsl⟩)
  refine ((h1.mono_post ?_).seq_left hA).mono_post fun _ _ h => h.elim id id
  rintro s c (⟨⟨j⟩ | ⟨⟩, h⟩ | h)
  · exact .inr (.inl ⟨j, h⟩)
  · exact .inl h
  · exact .inr (.inr h)

/-- **A buffer allocation's call with its heap abort path is one segment
inside `W`**, from the allocator's entry to its return at `pcR` alone:
`newBuf_callW`, its heap abort exit (`%rsp` at `-allocAbortDepth fs`)
continued by `seg_jabort2W` (the dispatcher at the heap code and
`scc_rt_abort_heap`, in the region below), which does not return. The
caller's region below the `call` (at `-fs`) is `T` (`hTR`), with the
allocator's region facts there (`hfit`, as `RtDepthX64.alloc_fits` gives
them): they give `newBuf_callW`'s `hlo` and the abort path's. The abort
path's obligations are asked at the heap abort exit's states (`hstub`); the
other premises are `newBuf_callW`'s. -/
theorem newBuf_call_abortW {W : Frag isa} {K : State → State → Prop} {cells : List (Directive × Nat)} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hprog : Alloc.allocIn cells = true)
    (hF : FStable R F) (hR : R.OK)
    {fs : Int} {T : Region} (hfs : fs % 8 = 0) (hTR : R.lo ≤ -fs + T.lo) (hfit : AllocFits T)
    (hhi : -fs ≤ R.hi) (hK : ms.K = some Scc.Sem.X64.abi)
    {pcR : Int64} {Jc : AS → Ctl → Prop}
    (hq : ∀ σ c, Jc σ c → ∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      σ.regs.rdi.toBitVec = q.h ∧ σ.regs.rsi.toBitVec = q.k ∧ σ.regs.rdx.toBitVec = q.u ms)
    (hra : ∀ σ c, Jc σ c → σ.slot (-fs - 8) = pcR.toBitVec)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-fs - 8, []⟩ mC σC ∧ Jc σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-fs - 8) σC) c ∧
        CKept R (-fs - 8) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (R.callee (-fs - 8) (-160) 8) F' (Ea ms q.1 l b w) s c →
        ms.xa l b w s c)
    (hW : ∀ q : Call, q.ra = pcR.toBitVec →
      AllocW ms q W K exe endPc (R.callee (-fs - 8) (-160) 8) (fun m => F m ∧ CallerCells R (-fs - 8) (-160) 8 m))
    (hstub : ∀ m0 σA c0, (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .abort).J σA c0 →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-allocAbortDepth fs - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-allocAbortDepth fs - 8) (-24) 16 m0 m ∧
          Abs R ⟨-allocAbortDepth fs, []⟩ m0 σA) c0) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_alloc", ⟨-fs - 8, []⟩, Jc⟩)
      (At exe endPc R F (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .ret)) := by
  refine SegW.of_someJ fun σ0 c0 hJ0 => ?_
  obtain ⟨q, -⟩ := hq σ0 c0 hJ0
  have hT : T.lo ≤ -200 := hfit.lo ms q lbl
  have hA := Abort.Disp.seg_jabort2W (W := W) (K := K) (p := p) (Q := At exe endPc R F
      (nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .ret))
    (nC := nbX ms (_root_.Executable.labels exe).label lbl R fs pcR Jc .abort) rfl
    (fun σ c h => h.1) hF hR
    (by show R.lo ≤ -allocAbortDepth fs - 32; simp only [allocAbortDepth, allocFrame]; omega)
    (by show -allocAbortDepth fs + 8 ≤ R.hi; simp only [allocAbortDepth, allocFrame]; omega)
    (by show (-allocAbortDepth fs) % 8 = 0; simp only [allocAbortDepth, allocFrame]; omega) hK hstub
  have h1 := newBuf_callW (p := p) (lbl := lbl) (W := W) (K := K) hp hend hprog hF hR hfs
    (by simp only [allocAbortDepth, allocFrame]; omega) hhi hq hra hmem hxa
    fun q _ h => hW q h
  refine ((h1.mono_post ?_).seq_left hA).mono_post fun _ _ h => h.elim id id
  rintro s c ⟨⟨⟩ | ⟨⟩, h⟩
  · exact .inr h
  · exact .inl h

end Fn

end Spike.Lib.X64

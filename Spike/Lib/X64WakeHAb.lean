/-
**wake.w's heap abort from `wc_main`'s allocation** (x86-64; the twin of
`Spike/Lib/A64WakeHAb.lean`): the allocator's full exit `wX .abort`
(`Spike/Lib/X64WakeWcPre.lean`) is at `scc_rt_abort` with `%rdi = 2` and
`%rsp` at `-240` in `wc_main`'s region `R`, the return address past
`scc_rt_alloc`'s `call scc_rt_abort` pushed there; the dispatcher and
`scc_rt_abort_heap` run in the region `[-24, 16)` below it
(`Abort.Disp.seg_jabort2RW`), and do not return.

- `raAb`: that return address, `.Lscc_rt_alloc.full + 12`.
- `WcHAbStub`: the heap abort path's obligations below `-240` for every
  source control of the node, with the return address `raAb`.
- `wc_heapAb_segWS`: the heap abort does not return, at any frames, into
  any fragment.

**Where this differs from AArch64**: the return address is the word
`call` pushed at `-240` (`σ.slot (-240)`, `wX .abort`'s second clause, from
the allocator's full branch's `call`), not `x30` (A64: `wX .abort`'s `X30`
clause, from its `bl`).
The dispatcher's region is `R.callee (-240 - 8) (-24) 16` (A64's
`R.callee (-240) (-48) 0`), so `R` needs `[-272, -232)` (A64's `hlo : R.lo ≤
-288`, `hhi : 0 ≤ R.hi`) and no alignment premise (`hal`); the abort's code
in `%rdi` (A64's `x0`).
-/
import Spike.Lib.X64WakeWcPre
import Spike.Lib.X64AbortHeapRW
import Spike.Lib.SegS

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow

/-- **The heap abort's return address**: past `scc_rt_alloc`'s
`call scc_rt_abort` (7 bytes of `movq $2, %rdi`, 5 of the `call`). -/
abbrev raAb (lab : Label → Int64) : BitVec 64 := (lab ".Lscc_rt_alloc.full" + 12).toBitVec

section Tail

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **The heap abort's obligations** in `wc_main`'s region `R` under `F`,
at the frames `fs`: the heap abort path's in the region `[-24, 16)` below
`-240` (`wX .abort`'s offset), with the return address `raAb`, for every
caller's state and source control of the node. -/
def WcHAbStub (W : FragS isa) (K : State → State → Prop) (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat)
    (ms : List TermRun.Frame → MemSide isa) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (fs : List TermRun.Frame) (J0 : AS → Ctl → Prop) : Prop :=
  ∀ m0 σC c0, (wX (ms fs) (_root_.Executable.labels exe).label R J0 .abort).J σC c0 →
    Abort.Disp.StubHRW (fun s c => W s c fs) K p lbl (ms fs) exe endPc (R.callee (-240 - 8) (-24) 16)
      (fun m => F m ∧ CKept R (-240 - 8) (-24) 16 m0 m ∧ Abs R ⟨-240, []⟩ m0 σC) c0
      (raAb (_root_.Executable.labels exe).label)

/-- **The heap abort does not return**: from `wX .abort` in `wc_main`'s
region at the frames `fs`, into any fragment (`seg_jabort2RW` at `-240`; the
return address the pushed word `raAb`, `wX .abort`'s). -/
theorem wc_heapAb_segWS {W : FragS isa} {K : State → State → Prop} {fs : List TermRun.Frame}
    {J0 : AS → Ctl → Prop}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -272) (hhi : -232 ≤ R.hi)
    (hK : (ms fs).K = some Scc.Sem.X64.abi)
    (hstub : WcHAbStub W K p lbl ms exe endPc R F fs J0) (Q : FragS isa) :
    SegWS W K p lbl ms ((At exe endPc R F (wX (ms fs) (_root_.Executable.labels exe).label R J0 .abort)).at fs)
      Q := by
  have h := Abort.Disp.seg_jabort2RW (p := p) (lbl := lbl) (Q := fun _ _ => False) (W := fun s c => W s c fs)
    (K := K) (nC := wX (ms fs) (_root_.Executable.labels exe).label R J0 .abort) rfl
    (fun σ c h => h.1) (fun σ c h => h.2.1) hF hR (by show R.lo ≤ -240 - 32; omega) (by show (-240 : Int) + 8 ≤ R.hi; omega)
    (by show (-240 : Int) % 8 = 0; decide) hK hstub
  exact (SegWS.liftS fs h fun _ _ h => h).mono_post fun _ _ _ h => h.1.elim

end Tail

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wc_heapAb_segWS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wc_heapAb_segWS

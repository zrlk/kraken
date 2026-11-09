/-
**The threads abort phase kept off its pcs, generic in the spawn's pcs**
(x86-64; the twin of `Spike/Lib/A64HelloThreadsAcSt.lean`):
`Spike/Lib/X64ThreadsAcSt.lean`'s check and introductions at
`Hello.ThreadsAb.Ac lab pfx cl n st off` (`Spike/Lib/X64HelloThreadsAb.lean`),
wake's at `".x3" 46 ".x4" (-56)`, hello's (`AcH`) at
`".x3" 94 ".x4" (-120)`.

- `blkAc`, `blkAc_sound`: as wake's, with `cl n st` (the check reads only
  the pcs) and `off` (the soundness theorem's phase). The node of the
  soundness theorem is `nd` (wake's `n`, now the `syscall`'s offset).
- `ac_dispE`, `ac_dispT`, `ac_dispEA`, `ac_dispTA`: as wake's.

The rest of wake's file reads no spawn pc and is reused as it is:
`ThreadsAcSt.RaPos`, `load_of_abs`, `raW_of_abs`, `bp_five`, the blocks'
`slot 8` facts (`d0_run5`, `t_run5`, `g5_run`, `x0_run5`, `x1T_run`,
`x2_run5`) and the pc memberships (`memE5` … `memExT`). `X64AcSt`'s
`AcSt.ofLeaves` and `blkW_acStN` are generic in the phase predicate and
apply at `AcH` as they are.

**Deviation from the A64 file.** A64's `acPcsNE`, `ac_dispE_of`, `tgtAc`,
`blkAcX`, `blkAcX_sound` are not twinned: `X64ThreadsAcSt` has no
counterpart of them (no users outside the A64 file).
-/
import Spike.Lib.X64HelloThreadsAb
import Spike.Lib.X64ThreadsAcSt

namespace Spike.Lib.X64ConsumerA.HelloThreadsAcSt

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64

/-- **A block's targets off the threads abort phase's pcs**: every target of
every instruction (a `ret`'s the return address `ra`) is off
`Hello.ThreadsAb.acPcs lab pfx cl n st`. -/
def blkAc (lab : Label → Int64) (pfx cl : String) (n : Nat) (st : String) (pc ra : Int64) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (aiTgts lab (pc + Int64.ofNat (cellOff blk k) + Int64.ofNat dz.2) ra a).all fun t =>
          !(Spike.Lib.X64.Hello.ThreadsAb.acPcs lab pfx cl n st).contains t
      | none => false
    | none => false

/-- **`blkW_acStN`'s `htgt` at the threads abort phase from the check**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAc_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {nd : ND}
    {blk : List (Directive × Nat)} {pfx cl : String} {n : Nat} {st : String} {off : BitVec 64}
    {ra : Int64}
    (h : blkAc (_root_.Executable.labels exe).label pfx cl n st nd.pc ra blk = true)
    (hret : ∀ σ c, nd.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ.slot
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so.sp) = ra) :
    ∀ σ c, nd.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = nd.pc + Int64.ofNat (cellOff blk k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ →
      ¬ Spike.Lib.X64.Hello.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx cl n st off s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so
        (nd.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so
          (nd.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ) →
      ¬ Spike.Lib.X64.Hello.ThreadsAb.Ac (_root_.Executable.labels exe).label pfx cl n st off s' := by
  intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' _
  refine Spike.Lib.X64.Hello.ThreadsAb.not_ac_of_pc ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun hr => hret σ c hJ k hk (hr ▸ ha))
  rw [hpc']
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using ht

open Spike.Lib.X64.Hello.ThreadsAb
open Spike.Lib.X64.ThreadsAb (raT RaW dispTPcs dispT_ra)
open Spike.Lib.X64.WriteAb (bpLoad dispEPcs)
open Spike.Lib.X64ConsumerA.ThreadsAcSt (RaPos raW_of_abs bp_five)

variable {lab : Label → Int64} {pfx cl : String} {n : Nat} {st : String} {off : BitVec 64}

/-- The dispatcher's prologue with `%rdi = 5` and the threads return address
is in `Ac`. -/
theorem ac_dispE {s : State} (h : s.st.2 ∈ dispEPcs lab) (h0 : s.st.1.regs.get64 .rdi = 5#64)
    (hr : RaW lab s (raT lab pfx)) : Ac lab pfx cl n st off s :=
  .inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩))))

/-- The dispatcher's first five tests with `-8(%rbp) = 5` and the threads
return address are in `Ac`. -/
theorem ac_dispT {s : State} (h : s.st.2 ∈ dispTPcs lab) (h0 : bpLoad s (-8) = some 5#64)
    (hr : RaW lab s (raT lab pfx)) : Ac lab pfx cl n st off s :=
  .inr (.inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩)))))

/-- A state of the dispatcher's prologue with `%rdi = 5` and the threads
return address, from the abstract state. -/
theorem ac_dispEA {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ dispEPcs lab)
    (hA : Abs R o s.st.1 σ) (h5 : σ.regs.get64 .rdi = 5#64) (hoff : R.Off 8) (hpos : RaPos lab s.st.2 o)
    (hr : σ.slot 8 = raT lab pfx) : Ac lab pfx cl n st off s :=
  ac_dispE hmem (by rw [hA.regs]; exact h5) (raW_of_abs hA hoff hpos hr)

/-- A state of the dispatcher's tests with `5` at `-8(%rbp)` and the threads
return address, from the abstract state. -/
theorem ac_dispTA {R : Spike.Lib.Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ dispTPcs lab)
    (hA : Abs R o s.st.1 σ) (ho : o.get .rbp = some 0) (hoff : R.Off (-8)) (h5 : σ.slot (-8) = 5#64)
    (hoff8 : R.Off 8) (hr : σ.slot 8 = raT lab pfx) : Ac lab pfx cl n st off s :=
  ac_dispT hmem (bp_five hA ho hoff h5) (raW_of_abs hA hoff8 (.inr (.inr ⟨dispT_ra hmem, ho⟩)) hr)

end Spike.Lib.X64ConsumerA.HelloThreadsAcSt

/-- info: 'Spike.Lib.X64ConsumerA.HelloThreadsAcSt.blkAc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.HelloThreadsAcSt.blkAc_sound

/-- info: 'Spike.Lib.X64ConsumerA.HelloThreadsAcSt.ac_dispTA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.HelloThreadsAcSt.ac_dispTA

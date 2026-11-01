/-
**The threads abort phase kept off its pcs, generic in the spawn's pcs**: `Spike/Lib/A64ThreadsAcSt.lean`'s checks and
introductions at `Hello.ThreadsAb.Ac lab pfx n cl off`
(`Spike/Lib/A64HelloThreadsAb.lean`), wake's at `13 ".clone9" 48`, hello's
(`AcH`) at `25 ".clone13" 112`.

- `blkAc`, `blkAc_sound`, `acPcsNE`, `ac_dispE_of`, `tgtAc`, `blkAcX`,
  `blkAcX_sound`: as wake's, with `n cl` (the checks read only the pcs) and
  `off` (the soundness theorems' phase). The node of the soundness theorems
  is `nd` (wake's `n`, now the `svc`'s index).
- `ac_dispE`, `ac_dispT`, `ac_dispEA`, `ac_dispTA`: as wake's.

The rest of wake's file reads no spawn pc and is reused as it is:
`bl_x30`, `ThreadsAcSt.sp_five`, the blocks' `x30` facts (`d0_x30`,
`t_run5`, `g5_x30`, `b0_x30`, `b1T_x30`, `b2_x30`) and the pc memberships
(`memE5` … `memExT`).
-/
import Spike.Lib.A64HelloThreadsAb
import Spike.Lib.A64ThreadsAcSt

namespace Spike.Lib.A64ConsumerA.HelloThreadsAcSt

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Spike.Lib.A64ConsumerA (bl_x30)
open Spike.Lib.A64ConsumerA.ThreadsAcSt (sp_five)
open Spike.Lib.A64.ThreadsAb (raT failPcs dispTPcs g5Pcs stubPcs)
open Spike.Lib.A64.WriteAb (spLoad dispEPcs)

open Spike.Lib.A64.Hello  -- `ThreadsAb.…` below is `Spike.Lib.A64.Hello.ThreadsAb.…`

variable {lab : Label → Int64} {pfx : String} {n : Nat} {cl : String} {off : BitVec 64}

/-- **A block's targets off the threads abort phase's pcs**: every target of
every instruction (a `ret`'s the return address `ra`) is off
`acPcs lab pfx`. -/
def blkAc (lab : Label → Int64) (pfx : String) (n : Nat) (cl : String)
     (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          !(ThreadsAb.acPcs lab pfx n cl).contains t
      | none => false
    | none => false

/-- **`blkW_acStN`'s `htgt` at the threads abort phase from the check**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAc_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {nd : ND} {blk : List Directive}
    {pfx : String} {ra : Int64} (h : blkAc (_root_.Executable.labels exe).label pfx n cl nd.pc ra blk = true)
    (hret : ∀ σ c, nd.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ.regs.getRegOrZr r).signed
        = ra) :
    ∀ σ c, nd.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = nd.pc + Int64.ofNat (4 * k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ →
      ¬ ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (nd.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so
          (nd.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ) →
      ¬ ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off s' := by
  intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' _
  refine ThreadsAb.not_ac_of_pc ?_
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun r hr => hret σ c hJ k hk r (hr ▸ ha))
  rw [hpc']
  simpa only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] using ht

/-- `Ac`'s pcs but the dispatcher's prologue. -/
def acPcsNE (lab : Label → Int64) (pfx : String) (n : Nat) (cl : String)
     : List Int64 :=
  ThreadsAb.pcRet lab pfx n :: ThreadsAb.pcSt lab pfx cl ::
    ThreadsAb.tailPcs lab pfx cl ++ failPcs lab pfx ++
    dispTPcs lab ++ g5Pcs lab ++
    stubPcs lab

/-- **A state in `Ac` off `acPcsNE`** is at the dispatcher's prologue with
the threads return address. -/
theorem ac_dispE_of {lab : Label → Int64} {pfx : String} {s : State} (h : ThreadsAb.Ac lab pfx n cl off s)
    (hn : s.st.2 ∉ acPcsNE lab pfx n cl) :
    s.st.1.regs.X30.toBitVec = raT lab pfx := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h | ⟨-, -, hr⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  all_goals first | exact hr | (exfalso; apply hn; simp_all [acPcsNE])

/-- One target's check: off `Ac`'s pcs, or a `bl` to off `acPcsNE` whose
return address `fall` is not the threads one (another caller of the
dispatcher). -/
def tgtAc (lab : Label → Int64) (pfx : String) (n : Nat) (cl : String)
     (fall : Int64) (a : AI) (t : Int64) : Bool :=
  !(ThreadsAb.acPcs lab pfx n cl).contains t ||
    (match a with | .bl _ => true | _ => false) && !(acPcsNE lab pfx n cl).contains t &&
      fall.toBitVec != raT lab pfx

/-- **A block's targets out of the threads abort phase**: every target of
every instruction (a `ret`'s the return address `ra`) passes `tgtAc`. -/
def blkAcX (lab : Label → Int64) (pfx : String) (n : Nat) (cl : String)
     (pc ra : Int64) (blk : List Directive) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match classify d with
      | some a => (aiTgts lab (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) ra a).all fun t =>
          tgtAc lab pfx n cl (pc + Int64.ofNat (4 * k) + Int64.ofNat 4) a t
      | none => false
    | none => false

/-- A `bl`'s `x30` is its return address. -/
theorem bl_x30 (o : SO) (f : Int64) (σ : AS) (L : Label) :
    (AI.step o f (.bl L) σ).regs.X30.toBitVec = f.toBitVec := by
  rw [BlockSpec.AI.step_bl']
  simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]

/-- **`blkW_acStN`'s `htgt` at the threads abort phase from `blkAcX`**,
every `ret` of the block returning to `ra` (`hret`). -/
theorem blkAcX_sound {exe : _root_.Executable} {endPc : Int64} {R : Region} {nd : ND} {blk : List Directive}
    {pfx : String} {ra : Int64} (h : blkAcX (_root_.Executable.labels exe).label pfx n cl nd.pc ra blk = true)
    (hret : ∀ σ c, nd.J σ c → ∀ k (hk : k < blk.length) r, classify blk[k] = some (.ret r) →
      Int64.ofInt ((arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ.regs.getRegOrZr r).signed
        = ra) :
    ∀ σ c, nd.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = nd.pc + Int64.ofNat (4 * k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ →
      ¬ ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (nd.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).so
          (nd.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨nd.pc, nd.o, σ⟩).σ) →
      ¬ ThreadsAb.Ac (_root_.Executable.labels exe).label pfx n cl off s' := by
  intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' hA' hac
  have := List.all_eq_true.mp h k (List.mem_range.mpr hk)
  simp only [List.getElem?_eq_getElem hk, ha] at this
  have ht := List.all_eq_true.mp this _ (aiTgt_mem a fun r hr => hret σ c hJ k hk r (hr ▸ ha))
  rw [← hpc'] at ht
  simp only [tgtAc, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not, bne_iff_ne, ne_eq] at ht
  rcases ht with ht | ⟨⟨hbl, hne⟩, hra⟩
  · exact ThreadsAb.not_ac_of_pc ht hac
  · have hx := ac_dispE_of hac hne
    cases a <;> simp at hbl
    rw [hA'.regs, bl_x30] at hx
    exact hra hx

/-- The dispatcher's prologue with `x0 = 5` and the threads return address
is in `Ac`. -/
theorem ac_dispE {s : State} (h : s.st.2 ∈ dispEPcs lab) (h0 : s.st.1.regs.X0 = 5)
    (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) : ThreadsAb.Ac lab pfx n cl off s :=
  .inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩))))

/-- The dispatcher's first five tests with `[sp] = 5` and the threads return
address are in `Ac`. -/
theorem ac_dispT {s : State} (h : s.st.2 ∈ dispTPcs lab) (h0 : spLoad s 0 = some 5#64)
    (hr : s.st.1.regs.X30.toBitVec = raT lab pfx) : ThreadsAb.Ac lab pfx n cl off s :=
  .inr (.inr (.inr (.inr (.inr (.inl ⟨h, h0, hr⟩)))))

/-- A state of the dispatcher's prologue with `x0 = 5` and the threads
return address, from the abstract state. -/
theorem ac_dispEA {R : Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ dispEPcs lab)
    (hA : Abs R o s.st.1 σ) (h5 : σ.regs.X0.toBitVec.toNat = 5) (hr : σ.regs.X30.toBitVec = raT lab pfx) :
    ThreadsAb.Ac lab pfx n cl off s :=
  ac_dispE hmem (by rw [hA.regs]; exact UInt64.toNat_inj.mp (by simpa using h5)) (by rw [hA.regs]; exact hr)

/-- A state of the dispatcher's tests with `5` at `[sp]` and the threads
return address, from the abstract state. -/
theorem ac_dispTA {R : Region} {o : SO} {s : State} {σ : AS} (hmem : s.st.2 ∈ dispTPcs lab)
    (hA : Abs R o s.st.1 σ) (ho : o.sp = -32) (hoff : R.Off (-32)) (h5 : (σ.slot (-32)).toNat = 5)
    (hr : σ.regs.X30.toBitVec = raT lab pfx) : ThreadsAb.Ac lab pfx n cl off s :=
  ac_dispT hmem (sp_five hA ho hoff h5) (by rw [hA.regs]; exact hr)

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64ConsumerA.HelloThreadsAcSt.blkAc_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkAc_sound

/-- info: 'Spike.Lib.A64ConsumerA.HelloThreadsAcSt.blkAcX_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkAcX_sound

end Spike.Lib.A64ConsumerA.HelloThreadsAcSt

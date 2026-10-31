/-
**wake.w's heap abort path: the phases at the program's nodes**
(`Wf`'s `AbSt`/`AcSt`, x86-64; the twin of `Spike/Lib/A64WakeWfHP.lean`'s
lemmas): the WfPh/WfAb lemmas at a block or instruction of an executable
with `InstOk`, and the dispatcher's data keeping the return address, from
which `hpathW_ph` (`Spike/Lib/X64WakeWfHPA.lean`) discharges every
obligation of `Abort.Disp.HPathW` at
`AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (ThreadsAb.Ac lab pfx)`.

The dispatcher's prologue and first tests are at pcs of both phases: the
code `2` (in `%rdi`, then at `-8(%rbp)`) keeps the write abort out, the
pushed return address `ra` (`slot 8`) the threads abort (`blkW_dispPh`).
Every other block and instruction of the path reaches neither phase's pcs
(`blkW_phSt`, `nodeW_phSt`); the exit call resumes in no state.

- `d0_ra`, `d0_sp1`, `d0_bp`, `tj_ra`: `slot 8` kept through the prologue
  and the tests, and where `%rsp`/`%rbp` are.
- `sp0_slot`, `sp8_slot`, `bp8_slot`, `raW_slot`: the pushed word read by
  `ThreadsAb.RaW` is `slot 8` where the offsets put it there.
- `hpcOf`, `blkW_phI`, `blkW_dispI`, `nodeW_siI`, `nodeW_sysI`,
  `nodeW_exitI`: the WfPh lemmas at a block or instruction of the program.

**Where this differs from AArch64** (forced by the x86-64 shape):
- the return address is not `x30` but the pushed word, `slot 8` of the
  dispatcher's region (`Abort.Disp.DN.nd2R`); A64's `d0_x30'`/`tj_x30`
  become `d0_ra`/`tj_ra` (`slot 8` kept), and `ThreadsAb.RaW` reads it at
  `0(%rsp)`, `8(%rsp)` or `8(%rbp)` by the pc, so `d0_sp1`, `d0_bp` and
  the load lemmas `sp0_slot`, `sp8_slot`, `bp8_slot`, `raW_slot` (no A64
  counterpart) say where;
- offsets are bytes (`lab l + k`, A64's `lab l + 4 k`) and blocks are at
  `blockAtB`; no alignment premise (`hal`; x86-64's `blkW_phSt` has none);
- `blkW_phI` keeps `phOff`'s return label `rl` (x86-64's `phOff` takes
  it apart from the block's label);
- the `write` call is a `syscall` (`nodeW_sysI`, A64's `nodeW_svcI`) of two
  bytes, its resumed states at `p + 2`, also at an `arch_prctl`
  (`certSuccs_archSetFs`); the exit call is at `%rax = 231` (A64's
  `x8 = 94`).
-/
import Spike.Lib.X64WakeWfAb
import Spike.Lib.X64WakeWfG
import Spike.Lib.X64AbortHeapRW
import Spike.Lib.X64AbortPhH

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun classify AS SO Abs okBlk SI)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB)
open Kraken.Promising.Lower.X64 (op64)

/-! ## The return address through the dispatcher -/

section Run

set_option linter.unusedSimpArgs false

open Spike.Lib.X64 in
/-- The abstract run's simp set over the dispatcher's blocks. -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- **The dispatcher's prologue keeps `slot 8`** (the pushed return
address) through its end. -/
theorem d0_ra (lab : Label → Int64) (pc : Int64) (σ : AS) {k : Nat} (hk : k ≤ Abort.Disp.d0.length) :
    (arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).σ.slot 8 = σ.slot 8 := by
  simp only [Abort.Disp.d0, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- Past the prologue's `pushq %rbp`, `%rsp` is at the frame's base. -/
theorem d0_sp1 (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab (Abort.Disp.d0.take 1) ⟨pc, Abort.oE, σ⟩).so.sp = 0 := by
  simp only [Abort.Disp.d0]
  arun_simp

/-- Past the prologue's `movq %rsp, %rbp`, `%rbp` is at the frame's base. -/
theorem d0_bp (lab : Label → Int64) (pc : Int64) (σ : AS) {k : Nat} (h2 : 2 ≤ k)
    (hk : k ≤ Abort.Disp.d0.length) :
    (arun lab (Abort.Disp.d0.take k) ⟨pc, Abort.oE, σ⟩).so.get .rbp = some 0 := by
  simp only [Abort.Disp.d0, List.length_zip, List.length_cons, List.length_nil] at hk ⊢
  rcases k with _|_|_|_|_|k <;> (try omega) <;> arun_simp

/-- **The dispatcher's tests against `1`, `2` and the jump keep `slot 8`**
through their end. -/
theorem tj_ra (lab : Label → Int64) {blk : List (Directive × Nat)}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) (pc : Int64) (σ : AS) {j : Nat}
    (hj : j ≤ blk.length) :
    (arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot 8 = σ.slot 8 := by
  rcases hb with rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.j1, List.length_zip, List.length_cons,
      List.length_nil] at hj ⊢ <;>
    rcases j with _|_|_|_|_|j <;> (try omega) <;> arun_simp

end Run

/-! ## The pushed word from the abstract state -/

section Load

variable {R : Region} {o : SO} {s : State} {σ : AS}

/-- **`0(%rsp)` is `slot 8`**, `%rsp` at `8`. -/
theorem sp0_slot (hA : Abs R o s.st.1 σ) (ho : o.sp = 8) (hoff : R.Off 8) :
    ThreadsAb.spLoad s 0 = some (σ.slot 8) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot 8 hoff
  have hsp := hA.so .rsp 8 (by simp [SO.get, ho])
  rw [← hA.regs] at hsp
  simp only [Reg64s.get64] at hsp
  have a0 : R.addr 8 + (0 : BitVec 64) = R.addr 8 := BitVec.add_zero _
  simp only [ThreadsAb.spLoad, Scc.Sem.X64.privLoad, hsp, a0, hj, Option.map_some, hjv]

/-- **`8(%rsp)` is `slot 8`**, `%rsp` at `0`. -/
theorem sp8_slot (hA : Abs R o s.st.1 σ) (ho : o.sp = 0) (hoff : R.Off 8) :
    ThreadsAb.spLoad s 8 = some (σ.slot 8) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot 8 hoff
  have hsp := hA.so .rsp 0 (by simp [SO.get, ho])
  rw [← hA.regs] at hsp
  simp only [Reg64s.get64] at hsp
  have a8 : R.addr 0 + (8 : BitVec 64) = R.addr 8 := by
    rw [show (8 : Int) = 0 + 8 by rfl, Region.addr_add]; rfl
  simp only [ThreadsAb.spLoad, Scc.Sem.X64.privLoad, hsp, a8, hj, Option.map_some, hjv]

/-- **`8(%rbp)` is `slot 8`**, `%rbp` at `0`. -/
theorem bp8_slot (hA : Abs R o s.st.1 σ) (ho : o.get .rbp = some 0) (hoff : R.Off 8) :
    WriteAb.bpLoad s 8 = some (σ.slot 8) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot 8 hoff
  have hbp := hA.so .rbp 0 ho
  rw [← hA.regs] at hbp
  simp only [Reg64s.get64] at hbp
  have a8 : R.addr 0 + (8 : BitVec 64) = R.addr 8 := by
    rw [show (8 : Int) = 0 + 8 by rfl, Region.addr_add]; rfl
  simp only [WriteAb.bpLoad, Scc.Sem.X64.privLoad, hbp, a8, hj, Option.map_some, hjv]

/-- **The pushed return address `RaW` reads is `slot 8`**, the offsets
putting it where `RaW` reads it at the state's pc. -/
theorem raW_slot {lab : Label → Int64} {ra : BitVec 64} (hA : Abs R o s.st.1 σ) (hoff : R.Off 8)
    (hS : s.st.2 ∈ ThreadsAb.raSPcs lab → o.sp = 8) (hP : s.st.2 ∈ ThreadsAb.raPPcs lab → o.sp = 0)
    (hB : s.st.2 ∈ ThreadsAb.raBPcs lab → o.get .rbp = some 0) (h : ThreadsAb.RaW lab s ra) :
    σ.slot 8 = ra := by
  rcases h with ⟨hm, hl⟩ | ⟨hm, hl⟩ | ⟨hm, hl⟩
  · rw [sp0_slot hA (hS hm) hoff] at hl; exact Option.some.inj hl
  · rw [sp8_slot hA (hP hm) hoff] at hl; exact Option.some.inj hl
  · rw [bp8_slot hA (hB hm) hoff] at hl; exact Option.some.inj hl

end Load

/-! ## At the program's blocks -/

section Prog

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {pfx : String}

omit [Kraken.Executable.ValidLayout exe] in
/-- A covered block's pcs off the marks' sites from its phase check. -/
theorem hpcOf (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} (hok : okBlk lo hi n.o blk = true)
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label n.pc 0 blk = true)
    (hnr : noRetBlk blk = true) :
    ∀ j < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk j) → PcOff μ s := fun j hj s h1 h2 h3 =>
  ((blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)).1 j hj s h1 h2 h3).1

/-- **`blkW_phSt` at a block of the program** without a `ret`. -/
theorem blkW_phI (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l rl : Label} {k : Nat}
    (hb : blockAtB cells l k blk = true) (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat k) 0 blk = true)
    (hnr : noRetBlk blk = true) (h : phOff (_root_.Executable.labels exe).label pfx l k rl blk = true) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  exact blkW_phSt (fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn) hok hR hlo hhi
    (hpcOf hI hok hph hnr) he h fun _ _ _ j hj r => (noRet_false hnr j hj r).elim

/-- **`blkW_dispPh` at a block of the program.** -/
theorem blkW_dispI (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l : Label} {k : Nat} {E T : List Nat}
    (hb : blockAtB cells l k blk = true) (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hoff : R.Off (-8))
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat k) 0 blk = true)
    (hnr : noRetBlk blk = true)
    (h : dChk (_root_.Executable.labels exe).label pfx ((_root_.Executable.labels exe).label l + Int64.ofNat k)
      E T blk = true)
    (hE : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ E →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.regs.get64 .rdi ≠ 4#64)
    (hT : ∀ σ c, n.J σ c → ∀ k, k < blk.length → k ∈ T →
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so.get .rbp = some 0 ∧
      (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ.slot (-8) ≠ 4#64)
    (hX : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) a, classify blk[k].1 = some a → ∀ s' : State,
      s'.st.2 ∈ aiTgts (_root_.Executable.labels exe).label
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) 0 a →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so
        s'.st.1 (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ ThreadsAb.RaW (_root_.Executable.labels exe).label s' (ThreadsAb.raT (_root_.Executable.labels exe).label pfx)) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph h
  exact blkW_dispPh (fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn) hok hR hlo hhi hoff
    (hpcOf hI hok hph hnr) hnr h hE hT hX

/-- **`nodeW_phSt` at a single instruction of the program** of size `z`,
its pc off the sites (`hok`). -/
theorem nodeW_siI (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {si : SI} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(si.toDir, z)] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat k).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k z = true) :
    NodeW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  exact nodeW_phSt he h (fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq))
    (si_step hI hb he) s c hA

/-- **A `syscall` of the program resuming off both phases' pcs** (`h`,
its next pc two bytes on), its pc off the sites (`hok`). -/
theorem nodeW_sysI (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} (hb : blockAtB cells l k [(op64 .syscall, 2)] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat k).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k 2 = true) :
    NodeW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  simp only [siOff, he, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at h
  rintro s c ⟨hs, hn, -, hpc, -⟩
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  have hnx : ∀ call s', s' ∈ Kernel.certSuccs abi s call → s'.st.2 = n.pc + Int64.ofNat 2 := by
    intro call s' hs'
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | tail _ h => cases h
      | head => show s.st.2 + Int64.ofNat 2 = _; rw [hpc]
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      show s.st.2 + Int64.ofNat 2 = _
      rw [hpc]
  have hsys : abi.atSys s = true := atSyscall_of_cellAt hc
  refine ⟨⟨⟨fun _ h => absurd h (by rw [hsys]; decide),
      fun _ _ call _ s' hs' hab' => (WriteAb.not_ab_of_pc (hnx call s' hs' ▸ h.1) hab').elim,
      fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩,
    ⟨fun _ h => absurd h (by rw [hsys]; decide),
      fun _ _ _ call _ s' hs' hac => ThreadsAb.not_ac_of_pc (hnx call s' hs' ▸ h.2) hac,
      fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩⟩, fun _ h => h⟩

/-- **An exit call keeps both phases**: at `%rax = 231` (`hx`) the call is
`exit_group`, which resumes in no state; its pc off the take site (`htk`). -/
theorem nodeW_exitI (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k : Nat} {p : Int64} (hb : blockAtB cells l k [(op64 .syscall, 2)] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = p) (hp : n.pc = p)
    (htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a) (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rax = 231#64) :
    NodeW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  refine NodeW.and (Spike.Lib.LowerX64.nodeW_ab_exit hI hb he hp htk hx) ?_
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSyscall_of_cellAt hc]; decide),
    fun _ _ _ call hd s' hs' _ => ?_,
    fun _ a ha hpc' => (htk a ha (by rw [← hpc']; unfold pcOf; rw [hpc])).elim⟩, fun _ h => h⟩
  have hr : s.st.1.regs.rax.toNat = 231 := by
    have h231 := hx σ c hJ
    rw [← hA.regs] at h231
    simp only [Reg64s.get64] at h231
    rw [← UInt64.toNat_toBitVec, h231]; rfl
  have hd' : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) := by
    rw [← Spike.Lib.X64.syscallCall_exitGroup hr]; rfl
  obtain rfl := Option.some.inj (hd'.symm.trans hd)
  rw [Spike.Lib.X64.certSuccs_exitGroup] at hs'
  cases hs'

end Prog

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.tj_ra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.tj_ra

/-- info: 'Spike.Lib.X64.WakeWf.raW_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.raW_slot

/-- info: 'Spike.Lib.X64.WakeWf.blkW_dispI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_dispI

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_sysI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_sysI

/-- info: 'Spike.Lib.X64.WakeWf.nodeW_exitI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.nodeW_exitI

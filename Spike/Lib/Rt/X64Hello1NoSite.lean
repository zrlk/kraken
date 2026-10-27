/-
**`hello1.w`'s x86-64 write tail is off the transfer sites** (the `hns`
premise of `printDt_closed`, `Spike/Lib/Rt/X64Hello1PrintDt.lean`): every
pc of a `PrintDt` state is one of finitely many, each a label of the tail
plus a cell offset, so a check on the labels decides it.

- `offSite μ p`: `p` is neither of `μ`'s transfer sites;
  `siteAt_of_offSite`: then no site is at the state;
- `blkOff μ pc blk`: every instruction of `blk` at `pc` is off the sites;
  `blkSt_off`: a `BlkSt` state's pc is then off them;
- `printOff μ lab`: the tail's pcs at the labels `lab` off the sites
  (`print`'s pieces, `RetDt`'s, `AbIn`'s, the `write` stub's `StubDt`);
  `printDt_noSite`: from it, `PrintDt` is off the sites; `printOff_congr`:
  it reads `lab` only at `tailLabs`;
- `printDt_noSite_hello1`: at `hello1`'s loaded thread and marks
  (`hello1Exe`, `μ0`), decided on the cells; `printDt_closed_μ0`:
  `printDt_closed_hello1` there, with no `hns`.
-/
import Spike.Lib.Rt.X64Hello1PrintDt
import Spike.Lib.X64Hello1I

namespace Spike.Lib.X64.Rt

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem
open Scc.Sem.X64 (abi)
open Spike.Lib.X64
open Spike.Lib (ClosedC)
open Spike.Lib.X64.Flow.Hello1 (wcR15)
open Spike.Lib.X64.Print (x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13)

/-! ## Off the sites -/

/-- **A pc off the transfer sites** of the marks `μ`. -/
def offSite (μ : Marks) (p : Int64) : Bool :=
  μ.site .take != some p.toBitVec.toNat && μ.site .release != some p.toBitVec.toNat

/-- At a pc off the sites, no site is at the state. -/
theorem siteAt_of_offSite {μ : Marks} {s : State} (h : offSite μ s.st.2 = true) : Kernel.siteAt abi μ s = none := by
  simp only [offSite, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact Kernel.siteAt_eq_none_iff.mpr ⟨h.1, h.2⟩

/-- **Every instruction of `blk` at `pc` is off the sites.** -/
def blkOff (μ : Marks) (pc : Int64) (blk : List (Directive × Nat)) : Bool :=
  (List.range blk.length).all fun k => offSite μ (pc + Int64.ofNat (cellOff blk k))

/-- A block's state is off the sites if its instructions are. -/
theorem blkSt_off {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {pc : Int64} {o : SO}
    {blk : List (Directive × Nat)} {J : AS → Prop} {C : MachineData → Prop} {s : State}
    (hb : blkOff μ pc blk = true) (h : BlkSt exe endPc R pc o blk J C s) : offSite μ s.st.2 = true := by
  obtain ⟨-, -, k, hk, hpc, -⟩ := h
  rw [hpc]
  exact List.all_eq_true.mp hb k (List.mem_range.mpr hk)

/-! ## The tail's pcs -/

/-- **The tail's labels.** -/
def tailLabs : List Label :=
  [".Lscc_rt_print.loop", ".Lscc_rt_print.write", ".Lscc_rt_print.chk2", ".Lscc_rt_print.chk3",
    ".Lscc_rt_print.adv", ".Lscc_rt_print.fail", ".Lscc_rt_print.done", ".Lwc_main.x15", ".Lscc_rt_main.x3",
    "scc_rt_abort", ".Lscc_rt_abort.entry", ".Lscc_rt_abort.next1", ".Lscc_rt_abort.next3",
    ".Lscc_rt_abort.next5", ".Lscc_rt_abort.is6", Abort.write.fn, Abort.write.entry, Abort.write.exit]

/-- **The tail's pcs at the labels `lab` are off the sites**: `print`'s
pieces, `RetDt`'s, `AbIn`'s and the `write` stub's. -/
def printOff (μ : Marks) (lab : Label → Int64) : Bool :=
  blkOff μ (lab ".Lscc_rt_print.loop") x2 && blkOff μ (lab ".Lscc_rt_print.loop" + 20) x3 &&
  blkOff μ (lab ".Lscc_rt_print.write") x4 && offSite μ (lab ".Lscc_rt_print.write" + 20) &&
  blkOff μ (lab ".Lscc_rt_print.write" + 22) x5 && blkOff μ (lab ".Lscc_rt_print.write" + 42) x6 &&
  blkOff μ (lab ".Lscc_rt_print.chk2") x7 && blkOff μ (lab ".Lscc_rt_print.chk2" + 16) x8 &&
  blkOff μ (lab ".Lscc_rt_print.chk3") x9 && blkOff μ (lab ".Lscc_rt_print.chk3" + 16) x10 &&
  blkOff μ (lab ".Lscc_rt_print.adv") x11 && blkOff μ (lab ".Lscc_rt_print.fail") x12 &&
  blkOff μ (lab ".Lscc_rt_print.done") x13 &&
  blkOff μ (lab ".Lwc_main.x15") wcR15 && blkOff μ (lab ".Lscc_rt_main.x3") (Flow.xExit (-48) 4 4 5) &&
  offSite μ (lab ".Lscc_rt_main.x3" + Int64.ofNat 4 + Int64.ofNat 4 + Int64.ofNat 5) &&
  blkOff μ (lab "scc_rt_abort") Abort.Disp.d0 && blkOff μ (lab ".Lscc_rt_abort.entry") Abort.Disp.t1 &&
  blkOff μ (lab ".Lscc_rt_abort.entry" + 16) Abort.Disp.j1 && blkOff μ (lab ".Lscc_rt_abort.next1") Abort.Disp.t2 &&
  blkOff μ (lab ".Lscc_rt_abort.next1" + 16) Abort.Disp.j2 && blkOff μ (lab ".Lscc_rt_abort.next3") Abort.Disp.t3 &&
  blkOff μ (lab ".Lscc_rt_abort.next3" + 16) Abort.Disp.j3 && blkOff μ (lab ".Lscc_rt_abort.next5") Abort.Disp.t4 &&
  blkOff μ (lab ".Lscc_rt_abort.is6") Abort.Disp.g4 && blkOff μ (lab Abort.write.fn) Abort.x0 &&
  offSite μ (lab Abort.write.entry) && blkOff μ (lab Abort.write.entry + 7) Abort.x1Write &&
  offSite μ (Abort.pcSys lab Abort.write) && offSite μ (lab Abort.write.entry + 36) &&
  offSite μ (lab Abort.write.entry + 40) && offSite μ (lab Abort.write.entry + 47) &&
  offSite μ (lab Abort.write.exit)

/-- **`printOff` reads the labels only at `tailLabs`.** -/
theorem printOff_congr {μ : Marks} {lab lab' : Label → Int64} (h : ∀ l ∈ tailLabs, lab l = lab' l) :
    printOff μ lab = printOff μ lab' := by
  unfold printOff Abort.pcSys
  simp (disch := decide) only [h]

/-- **`hello1.w`'s write tail is off the transfer sites**, given the check
at the thread's labels. -/
theorem printDt_noSite {μ : Marks} {exe : _root_.Executable} {endPc : Int64}
    (h : printOff μ (_root_.Executable.labels exe).label = true) :
    ∀ s, PrintDt exe endPc s → Kernel.siteAt abi μ s = none := by
  simp only [printOff, Bool.and_eq_true, and_assoc] at h
  obtain ⟨p2, p3, p4, ps, p5, p6, p7, p8, p9, p10, p11, p12, p13, r15, rx, rs, d0, t1, j1, t2, j2, t3, j3, t4, g4,
    x0, si, x1, ss, s36, s40, s47, sx⟩ := h
  intro s hs
  apply siteAt_of_offSite
  rcases hs with ⟨R0, -, -, -, hp | hr | ha⟩ | ⟨-, -, hst⟩
  · rcases hp with h | h | h | ⟨-, -, hpc, -⟩ | h | h | h | h | h | h | h | h | h
    · exact blkSt_off p2 h
    · exact blkSt_off p3 h
    · exact blkSt_off p4 h
    · rw [hpc]; exact ps
    · exact blkSt_off p5 h
    · exact blkSt_off p6 h
    · exact blkSt_off p7 h
    · exact blkSt_off p8 h
    · exact blkSt_off p9 h
    · exact blkSt_off p10 h
    · exact blkSt_off p11 h
    · exact blkSt_off p12 h
    · exact blkSt_off p13 h
  · rcases hr with h | h | ⟨-, -, hpc, -⟩
    · exact blkSt_off r15 h
    · exact blkSt_off rx h
    · rw [hpc]; exact rs
  · rcases ha with h | h | h | h | h | h | h | h | h | h | ⟨-, -, hpc, -⟩ | h
    · exact blkSt_off d0 h
    · exact blkSt_off t1 h
    · exact blkSt_off j1 h
    · exact blkSt_off t2 h
    · exact blkSt_off j2 h
    · exact blkSt_off t3 h
    · exact blkSt_off j3 h
    · exact blkSt_off t4 h
    · exact blkSt_off g4 h
    · exact blkSt_off x0 h
    · rw [hpc]; exact si
    · exact blkSt_off x1 h
  · rcases hst with ⟨hpc, -⟩ | ⟨hpc, -⟩ | hpc | hpc | ⟨hpc, -⟩ <;> rw [hpc] <;> assumption

/-! ## `hello1`'s loaded thread -/

section Hello1

open Spike.Lib.X64.Flow.Hello1.Mem (hello1Exe hello1End hello1_lays)
open Spike.Lib.X64.Flow.Hello1.Inst (μ0)
open Spike.Lib.X64.OwnLimRt (labIn label_labIn)
open Scc.Cert.Rt.X64 (labelIdx endOf)

/-- The tail's labels are labels of `hello1`'s cells. -/
theorem hello1_tailLabs : tailLabs.all (fun l => (labelIdx SccCode.hello1Cells l).isSome) = true := by
  decide +kernel

/-- The check at `hello1`'s labels in its cells. -/
theorem hello1_printOff : printOff μ0 (labIn SccCode.hello1Λ.code.lo SccCode.hello1Cells) = true := by
  decide +kernel

/-- **`hello1.w`'s write tail is off the transfer sites** at `hello1`'s
loaded thread and marks. -/
theorem printDt_noSite_hello1 : ∀ s, PrintDt hello1Exe hello1End s → Kernel.siteAt abi μ0 s = none :=
  printDt_noSite <| (printOff_congr fun l hl =>
    label_labIn hello1_lays rfl (List.all_eq_true.mp hello1_tailLabs l hl)).trans hello1_printOff

/-- **`hello1.w`'s write tail is closed under certification** at `hello1`'s
loaded thread and marks: `printDt_closed_hello1`, off the sites by
`printDt_noSite_hello1`. -/
theorem printDt_closed_μ0 (c0 : Ctl) (x : Kernel.KState) :
    ClosedC Arch.tso (Kernel.certSem abi Arch.tso μ0 x 0) 0 (PrintDt hello1Exe hello1End) :=
  printDt_closed_hello1 c0 hello1_lays rfl printDt_noSite_hello1 x

end Hello1

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.X64.Rt.printDt_noSite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printDt_noSite

/--
info: 'Spike.Lib.X64.Rt.printDt_noSite_hello1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printDt_noSite_hello1

/--
info: 'Spike.Lib.X64.Rt.printDt_closed_μ0' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms printDt_closed_μ0

end Spike.Lib.X64.Rt

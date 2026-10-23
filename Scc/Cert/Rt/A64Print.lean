import Scc.Cert.Rt.LayoutA64
import Spike.Lib.A64Print

/-!
# `scc_rt_print` in an emitted AArch64 program

`Spike.Lib.A64.Print.seg_print` proves `scc_rt_print` one segment from its
entry to its return or its abort, from hypotheses on the layout: each block
at its node's pc (`Code`) and the prologue's fall-through to `.0_entry`
(`hentry`). `printIn prog` checks them on a directive list: every block of
the function is the run of instructions at its label and offset
(`blockAt`), and `.0_entry` is six instructions behind `scc_rt_print`
(`labelGap`). `seg_print_of` is `seg_print` for any valid layout of a
program with `printIn prog = true`, decided once per program by
`decide +kernel`. The write system call stays a given node (`hsvc`).

The labels are scc's (`.L9_scc_rt_print.*`: the runtime's functions come
first in every program, in a fixed order).
-/

namespace Scc.Cert.Rt.A64.Print

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib Spike.Lib.A64 Spike.Lib.A64.Flow
  Spike.Lib.A64.Print

/-- **The code of `scc_rt_print` in `prog`**: its blocks at their labels
and offsets (the `write` system call 4 instructions after `.2_write` among
them), and the prologue's fall-through. -/
def printIn (prog : List Directive) : Bool :=
  blockAt prog "scc_rt_print" 0 b0 &&
  blockAt prog ".L9_scc_rt_print.0_entry" 0 b1 &&
  blockAt prog ".L9_scc_rt_print.1_loop" 0 b2 &&
  blockAt prog ".L9_scc_rt_print.1_loop" 4 b3 &&
  blockAt prog ".L9_scc_rt_print.2_write" 0 b4 &&
  blockAt prog ".L9_scc_rt_print.2_write" 4 [svcDir] &&
  blockAt prog ".L9_scc_rt_print.2_write" 5 b5 &&
  blockAt prog ".L9_scc_rt_print.2_write" 12 b6 &&
  blockAt prog ".L9_scc_rt_print.2_write" 13 b7 &&
  blockAt prog ".L9_scc_rt_print.3_chk2" 0 b8 &&
  blockAt prog ".L9_scc_rt_print.3_chk2" 6 b9 &&
  blockAt prog ".L9_scc_rt_print.3_chk2" 7 b10 &&
  blockAt prog ".L9_scc_rt_print.4_chk3" 0 b11 &&
  blockAt prog ".L9_scc_rt_print.4_chk3" 4 b12 &&
  blockAt prog ".L9_scc_rt_print.5_adv" 0 b13 &&
  blockAt prog ".L9_scc_rt_print.6_fail" 0 b14 &&
  blockAt prog ".L9_scc_rt_print.7_done" 0 b16 &&
  labelGap prog "scc_rt_print" ".L9_scc_rt_print.0_entry" 6

/-- A code segment at an equal pc. -/
theorem CodeAt.pc_eq {st : State} {p q : Int64} {b : List Directive} (h : CodeAt st p b) (e : p = q) :
    CodeAt st q b := e ▸ h

/-- `a + 4 + … + 4` (`k` times) is `a + 4k`. -/
theorem add4 (a : Int64) (k : Nat) : a + Int64.ofNat (4 * (k + 1)) = a + Int64.ofNat (4 * k) + 4 := by
  rw [Int64.add_assoc, show 4 * (k + 1) = 4 * k + 4 by omega, Int64.ofNat_add]; rfl

theorem add0 (a : Int64) : a + Int64.ofNat (4 * 0) = a := by
  rw [show Int64.ofNat (4 * 0) = 0 by decide, Int64.add_zero]

/-- A field of `Code` from `blockAt`: the block's code at `label + 4k`, in
every state of the executable. -/
theorem code_field {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive}
    (hp : Lays exe prog) {endPc : Int64} (hend : endPc = endOf exe prog)
    {l : Label} {k : Nat} {b : List Directive} (h : blockAt prog l k b = true) {q : Int64}
    (e : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = q) :
    ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s q b :=
  fun _ hs hn => CodeAt.pc_eq (codeAt_blockAt hp hs (hn.trans hend) h) e

set_option linter.unusedSimpArgs false in
/-- **`scc_rt_print` is one segment** in any valid layout `exe` of a program
`prog` with `printIn prog = true`, given its write system call. -/
theorem seg_print_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {m0 : MachineData} {c0 : Ctl} {x29 ra : BitVec 64}
    {prog : List Directive} [Kraken.Executable.ValidLayout exe] (hp : Lays exe prog)
    (hend : endPc = endOf exe prog) (hprog : printIn prog = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hsvc : Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 x29 ra .svc))
      (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 x29 ra .n5))) :
    Seg p lbl ms (At exe endPc R (DFrame R m0) (N (_root_.Executable.labels exe).label c0 x29 ra .e))
      (fun s c => ∃ x, At exe endPc R (DFrame R m0) (E (_root_.Executable.labels exe).label c0 x29 ra x) s c) := by
  simp only [printIn, Bool.and_eq_true, and_assoc] at hprog
  obtain ⟨h0, h1, h2, h3, h4, hs, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, hgap⟩ := hprog
  refine seg_print hR hal hlo hhi ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [label_labelGap hp hgap]; simp only [add4, add0]) hsvc
  · exact code_field hp hend h0 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h1 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h2 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h3 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h4 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h5 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h6 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h7 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h8 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h9 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h10 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h11 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h12 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h13 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h14 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend h15 (by simp only [N, pcSvc, add4, add0])
  · exact code_field hp hend hs (by simp only [N, pcSvc, add4, add0])

end Scc.Cert.Rt.A64.Print

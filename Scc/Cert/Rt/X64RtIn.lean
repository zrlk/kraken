import Scc.Cert.Rt.RtPassX64
import Scc.Cert.Rt.X64Abort
import Scc.Cert.Rt.X64AllocIn
import Spike.Lib.X64CodeSegs

/-!
# The runtime's code in one pass (x64)

The x64 twin of `Scc/Cert/Rt/A64RtIn.lean`. The runtime's code checks,
`Alloc.allocIn` (`scc_rt_alloc`), `Print.printIn` (`scc_rt_print`), `Abort.abortIn` (the abort stubs and
`scc_rt_abort`) and the tail of `scc_rt_main` (the `exit_group` tail at
`.Lscc_rt_main.x2`, `Spike.Lib.X64.Flow.exitIn`, or `Abort.mainIn` at
`.Lscc_rt_main.x3`), as groups of fixed code (`RGrp`) in program order
(`rtTab`), checked by one pass (`rtIn`, `Scc/Cert/Rt/RtPassX64.lean`)
instead of a search per label. The groups are the checks' facts, regrouped
by label: `allocIn_of_rtIn`, `printIn_of_rtIn`, `abortIn_of_rtIn`, `mainIn0_of_rtIn`,
`mainIn_of_rtIn`, `mainInS_of_rtIn` give the checks back.
-/

namespace Scc.Cert.Rt.X64.RtIn

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64 Spike.Lib.X64 Scc.Cert.Rt.X64

/-! ## `scc_rt_main`'s tail -/

/-- The tail of `scc_rt_main` without a setup block: the `exit_group` tail
right after `.Lscc_rt_main.x2`, the result at `-16(%rbp)`
(`Flow.exitIn cells ".Lscc_rt_main.x2" (-16) 4 4 5`). -/
def mainGrps0 : List RGrp :=
  [⟨".Lscc_rt_main.x2", [(0, Flow.xExit (-16) 4 4 5), (4 + 4 + 5, [(op64 .syscall, 2)])], none⟩]

/-- The tail of `scc_rt_main` after a setup block (`Abort.mainIn`). -/
def mainGrps1 : List RGrp :=
  [⟨".Lscc_rt_main.x3", [(0, Spike.Lib.X64.Abort.MainTail.m0), (13, [(op64 .syscall, 2)])], none⟩]

/-- The slot of `wc_main`'s result in `scc_rt_main`'s frame after a setup
block of `sw` words: `-8 (sw + 2)` (the `k` of `Spike.Lib.X64.Rt.setupMC sw`). -/
def mainK (sw : Nat) : Int64 := -Int64.ofNat (8 * (sw + 2))

/-- The tail of `scc_rt_main` after a setup block of `sw` words: the
`exit_group` tail right after `.Lscc_rt_main.x3`, the result at `mainK sw`
(`mainInS`). At four words it is `mainGrps1` (`mainGrps1_eq`). -/
def mainGrpsS (sw : Nat) : List RGrp :=
  [⟨".Lscc_rt_main.x3", [(0, Flow.xExit (mainK sw) 4 4 5), (4 + 4 + 5, [(op64 .syscall, 2)])], none⟩]

/-- **The code of the tail of `scc_rt_main` after a setup block of `sw`
words in `cells`**: `Flow.exitIn` at `.Lscc_rt_main.x3` and `mainK sw`, so
`Flow.exitTail_seg_of` runs it. At four words it is `Abort.mainIn`
(`mainIn_eq_mainInS`). -/
def mainInS (cells : List (Directive × Nat)) (sw : Nat) : Bool :=
  Flow.exitIn cells ".Lscc_rt_main.x3" (mainK sw) 4 4 5

/-- `Abort.MainTail.m0` (`hello1.w`'s tail, four setup words) is the
`exit_group` tail at `mainK 4`. -/
theorem m0_eq_xExit : Spike.Lib.X64.Abort.MainTail.m0 = Flow.xExit (mainK 4) 4 4 5 := by
  decide

theorem mainGrps1_eq : mainGrps1 = mainGrpsS 4 := by
  simp only [mainGrps1, mainGrpsS, m0_eq_xExit]

theorem mainIn_eq_mainInS (cells : List (Directive × Nat)) : Abort.mainIn cells = mainInS cells 4 := by
  simp only [Abort.mainIn, mainInS, Flow.exitIn, m0_eq_xExit]

/-- info: [-16, -48, -56] -/
#guard_msgs in
#eval [0, 4, 5].map fun sw => (mainK sw).toInt

/-! ## `scc_rt_alloc` -/

section Alloc

open Spike.Lib.X64.Alloc

/-- `scc_rt_alloc`'s blocks and single instructions and its prologue's
fall-through (`Alloc.allocIn`). -/
def allocGrps : List RGrp := [
  ⟨fnL, [(0, bPro)], some (23, entryL)⟩,
  ⟨entryL, [(0, bChk), (16, bJ1)], none⟩,
  ⟨cntL, [(0, [(iCtr.toDir, 7)]), (7, bC1), (19, [(iRmw, 5)]), (24, bC2), (59, bJ2)], none⟩,
  ⟨slowL, [(0, bSlow), (16, bJ3)], none⟩,
  ⟨fullL, [(0, bFull)], none⟩,
  ⟨okL, [(0, bO0), (11, [((FI.shr_cl .rax).toDir, 3)]), (14, bO1), (29, [((FI.and_rr .rax .rcx).toDir, 3)]),
    (32, bO2), (36, [(iHeap.toDir, 7)]), (43, bO3), (58, [((FI.shl_cl .rax).toDir, 3)]), (61, bO4),
    (88, [((FI.imul_rr .rax .rcx).toDir, 4)]), (92, bO5), (107, [((FI.shl_cl .rax).toDir, 3)]), (110, bO6),
    (125, [((FI.shl_cl .rax).toDir, 3)]), (128, bO7), (140, [((FI.or_rr .rax .rcx).toDir, 3)]), (143, bO8),
    (170, [(iHdr, 3)]), (173, bO9), (226, [(iRet.toDir, 1)])], none⟩]

end Alloc

/-! ## `scc_rt_print` -/

section Print

open Spike.Lib.X64.Print

/-- `scc_rt_print`'s blocks and its prologue's fall-through (`Print.printIn`). -/
def printGrps : List RGrp := [
  ⟨"scc_rt_print", [(0, x0)], some (16, ".Lscc_rt_print.entry")⟩,
  ⟨".Lscc_rt_print.entry", [(0, x1)], none⟩,
  ⟨".Lscc_rt_print.loop", [(0, x2), (20, x3)], none⟩,
  ⟨".Lscc_rt_print.write", [(0, x4), (20, [(op64 .syscall, 2)]), (22, x5), (42, x6)], none⟩,
  ⟨".Lscc_rt_print.chk2", [(0, x7), (16, x8)], none⟩,
  ⟨".Lscc_rt_print.chk3", [(0, x9), (16, x10)], none⟩,
  ⟨".Lscc_rt_print.adv", [(0, x11)], none⟩,
  ⟨".Lscc_rt_print.fail", [(0, x12)], none⟩,
  ⟨".Lscc_rt_print.done", [(0, x13)], none⟩]

end Print

/-! ## `scc_rt_abort` and the stubs -/

section Abort

open Spike.Lib.X64.Abort

/-- `scc_rt_abort`'s blocks and its prologue's fall-through (`Abort.dispIn`). -/
def dispGrps : List RGrp := [
  ⟨"scc_rt_abort", [(0, Disp.d0)], some (12, ".Lscc_rt_abort.entry")⟩,
  ⟨".Lscc_rt_abort.entry", [(0, Disp.t1), (16, Disp.j1)], none⟩,
  ⟨".Lscc_rt_abort.is0", [(0, Disp.g1)], none⟩,
  ⟨".Lscc_rt_abort.next1", [(0, Disp.t2), (16, Disp.j2)], none⟩,
  ⟨".Lscc_rt_abort.is2", [(0, Disp.g2)], none⟩,
  ⟨".Lscc_rt_abort.next3", [(0, Disp.t3), (16, Disp.j3)], none⟩,
  ⟨".Lscc_rt_abort.is4", [(0, Disp.g3)], none⟩,
  ⟨".Lscc_rt_abort.next5", [(0, Disp.t4), (16, Disp.j4)], none⟩,
  ⟨".Lscc_rt_abort.is6", [(0, Disp.g4)], none⟩,
  ⟨".Lscc_rt_abort.next7", [(0, Disp.t5), (16, Disp.j5)], none⟩,
  ⟨".Lscc_rt_abort.is8", [(0, Disp.g5)], none⟩]

/-- A stub's blocks and its labels' gaps (`Abort.stubIn`). -/
def stubGrps (st : Stub) (x1 : List (Directive × Nat)) : List RGrp := [
  ⟨st.fn, [(0, x0)], some (8, st.entry)⟩,
  ⟨st.entry, [(0, [((siMsg st).toDir, 7)]), (7, x1), (34, [(op64 .syscall, 2)]), (36, x2)], some (52, st.exit)⟩,
  ⟨st.exit, [(0, [(op64 .syscall, 2)])], none⟩]

/-- The stubs and `scc_rt_abort`, in program order. -/
def abortGrps : List RGrp :=
  dispGrps ++ stubGrps overflow x1Overflow ++ stubGrps heap x1Heap ++ stubGrps stack x1Stack ++
    stubGrps write x1Write ++ stubGrps threads x1Threads

end Abort

/-! ## The table -/

/-- **The runtime's fixed code**, in program order: `scc_rt_main`'s tail
(`main`: `mainGrps0`, `mainGrps1` or `mainGrpsS sw`), `scc_rt_alloc`, `scc_rt_print`,
`scc_rt_abort` and the stubs. -/
def rtTab (main : List RGrp) : List RGrp := main ++ allocGrps ++ printGrps ++ abortGrps

/-! ## The checks from the pass -/

section Of

variable {cells : List (Directive × Nat)} {main : List RGrp}

theorem rtAll_parts (h : rtIn cells (rtTab main) = true) :
    RtAll cells main ∧ RtAll cells printGrps ∧ RtAll cells abortGrps ∧ RtAll cells allocGrps := by
  have h := rtIn_sound h
  unfold rtTab at h
  obtain ⟨h12, h3⟩ := RtAll.append h
  obtain ⟨h1a, h2⟩ := RtAll.append h12
  obtain ⟨h1, ha⟩ := RtAll.append h1a
  exact ⟨h1, h2, h3, ha⟩

open Spike.Lib.X64.Alloc in
/-- **`scc_rt_alloc`'s code** from the pass. -/
theorem allocIn_of_rtIn (h : rtIn cells (rtTab main) = true) : Alloc.allocIn cells = true := by
  have h := (rtAll_parts h).2.2.2
  simp only [allocGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [Alloc.allocIn, fiAt, h, Bool.and_self]

open Spike.Lib.X64.Print in
/-- **`scc_rt_print`'s code** from the pass. -/
theorem printIn_of_rtIn (h : rtIn cells (rtTab main) = true) : Print.printIn cells = true := by
  have h := (rtAll_parts h).2.1
  simp only [printGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [Print.printIn, h, Bool.and_self]

open Spike.Lib.X64.Abort in
theorem stubIn_of {st : Stub} {x1 : List (Directive × Nat)} {rest : List RGrp}
    (h : RtAll cells (stubGrps st x1 ++ rest)) : Abort.stubIn cells st x1 = true := by
  have h := (RtAll.append h).1
  simp only [stubGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [Abort.stubIn, h, Bool.and_self]

open Spike.Lib.X64.Abort in
/-- **The stubs' and `scc_rt_abort`'s code** from the pass. -/
theorem abortIn_of_rtIn (h : rtIn cells (rtTab main) = true) : Abort.abortIn cells = true := by
  have h := (rtAll_parts h).2.2.1
  unfold abortGrps at h
  simp only [List.append_assoc] at h
  obtain ⟨hd, h⟩ := RtAll.append h
  have ho := stubIn_of h
  obtain ⟨-, h⟩ := RtAll.append h
  have hh := stubIn_of h
  obtain ⟨-, h⟩ := RtAll.append h
  have hs := stubIn_of h
  obtain ⟨-, h⟩ := RtAll.append h
  have hw := stubIn_of h
  obtain ⟨-, h⟩ := RtAll.append h
  have ht := stubIn_of (rest := []) (by simpa using h)
  simp only [dispGrps, RtAll, BsOk, GapAt, and_true] at hd
  simp only [Abort.abortIn, Abort.dispIn, ho, hh, hs, hw, ht, hd, Bool.and_self]

/-- **`scc_rt_main`'s tail without a setup block** from the pass. -/
theorem mainIn0_of_rtIn (h : rtIn cells (rtTab mainGrps0) = true) :
    Flow.exitIn cells ".Lscc_rt_main.x2" (-16) 4 4 5 = true := by
  have h := (rtAll_parts h).1
  simp only [mainGrps0, RtAll, BsOk, GapAt, and_true] at h
  simp only [Flow.exitIn, h, Bool.and_self]

/-- **`scc_rt_main`'s tail after a setup block** from the pass. -/
theorem mainIn_of_rtIn (h : rtIn cells (rtTab mainGrps1) = true) : Abort.mainIn cells = true := by
  have h := (rtAll_parts h).1
  simp only [mainGrps1, RtAll, BsOk, GapAt, and_true] at h
  simp only [Abort.mainIn, h, Bool.and_self]

/-- **`scc_rt_main`'s tail after a setup block of `sw` words** from the
pass. -/
theorem mainInS_of_rtIn {sw : Nat} (h : rtIn cells (rtTab (mainGrpsS sw)) = true) : mainInS cells sw = true := by
  have h := (rtAll_parts h).1
  simp only [mainGrpsS, RtAll, BsOk, GapAt, and_true] at h
  simp only [mainInS, Flow.exitIn, h, Bool.and_self]

end Of

end Scc.Cert.Rt.X64.RtIn

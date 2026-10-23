import Scc.Cert.Rt.RtPassX64
import Scc.Cert.Rt.X64Abort
import Spike.Lib.X64CodeSegs

/-!
# The runtime's code in one pass (x64)

The x64 twin of `Scc/Cert/Rt/A64RtIn.lean`. The runtime's code checks,
`Print.printIn` (`scc_rt_print`), `Abort.abortIn` (the abort stubs and
`scc_rt_abort`) and the tail of `scc_rt_main` (the `exit_group` tail at
`.Lscc_rt_main.x2`, `Spike.Lib.X64.Flow.exitIn`, or `Abort.mainIn` at
`.Lscc_rt_main.x3`), as groups of fixed code (`RGrp`) in program order
(`rtTab`), checked by one pass (`rtIn`, `Scc/Cert/Rt/RtPassX64.lean`)
instead of a search per label. The groups are the checks' facts, regrouped
by label: `printIn_of_rtIn`, `abortIn_of_rtIn`, `mainIn0_of_rtIn`,
`mainIn_of_rtIn` give the checks back.
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
(`main`: `mainGrps0` or `mainGrps1`), `scc_rt_print`, `scc_rt_abort` and
the stubs. -/
def rtTab (main : List RGrp) : List RGrp := main ++ printGrps ++ abortGrps

/-! ## The checks from the pass -/

section Of

variable {cells : List (Directive × Nat)} {main : List RGrp}

theorem rtAll_parts (h : rtIn cells (rtTab main) = true) :
    RtAll cells main ∧ RtAll cells printGrps ∧ RtAll cells abortGrps := by
  have h := rtIn_sound h
  unfold rtTab at h
  obtain ⟨h12, h3⟩ := RtAll.append h
  obtain ⟨h1, h2⟩ := RtAll.append h12
  exact ⟨h1, h2, h3⟩

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
  have h := (rtAll_parts h).2.2
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

end Of

end Scc.Cert.Rt.X64.RtIn

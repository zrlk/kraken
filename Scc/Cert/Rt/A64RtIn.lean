import Scc.Cert.Rt.RtPassA64
import Scc.Cert.Rt.A64Abort
import Scc.Cert.Rt.A64AllocIn

/-!
# The runtime's code in one pass

The runtime's code checks, `Flow.allocIn` (`scc_rt_alloc`),
`Print.printIn` (`scc_rt_print`), `Abort.abortIn` (the abort stubs and
`scc_rt_abort`) and the tail of `scc_rt_main` (`Abort.mainIn0`,
`Abort.mainIn`), as groups of fixed code (`RGrp`) in program order
(`rtTab`), checked by one pass (`rtIn`, `Scc/Cert/Rt/RtPassA64.lean`)
instead of a search per label. The groups are the checks' facts, regrouped
by label: `allocIn_of_rtIn`, `printIn_of_rtIn`, `abortIn_of_rtIn`,
`mainIn0_of_rtIn`, `mainIn_of_rtIn` give the checks back.
-/

namespace Scc.Cert.Rt.A64.RtIn

open Kraken Kraken.Promising Kraken.Promising.AArch64 Spike.Lib.A64 Scc.Cert.Rt.A64

/-! ## `scc_rt_main`'s tail -/

/-- The tail of `scc_rt_main` without a setup block (`Abort.mainIn0`). -/
def mainGrps0 : List RGrp :=
  [⟨".L1_scc_rt_main.sp0", [(0, Spike.Lib.A64.Abort.MainTail0.m0), (3, [Spike.Lib.A64.Flow.svcDir])], none⟩]

/-- The tail of `scc_rt_main` after a setup block (`Abort.mainIn`). -/
def mainGrps1 : List RGrp :=
  [⟨".L1_scc_rt_main.sp1", [(0, Spike.Lib.A64.Abort.MainTail.m0), (3, [Spike.Lib.A64.Flow.svcDir])], none⟩]

/-! ## `scc_rt_alloc` -/

section Alloc

open Spike.Lib.A64.Alloc

/-- `scc_rt_alloc`'s blocks and single instructions and its prologue's
fall-through (`Flow.allocIn`). -/
def allocGrps : List RGrp := [
  ⟨"scc_rt_alloc", [(0, b0)], some (7, ".L2_scc_rt_alloc.0_entry")⟩,
  ⟨".L2_scc_rt_alloc.0_entry", [(0, b1), (4, b2)], none⟩,
  ⟨".L2_scc_rt_alloc.1_cnt", [(0, [iAdrpC.toDir]), (1, [iAddC.toDir]), (2, b3), (5, [iRmw]), (6, b4), (15, b5)],
    none⟩,
  ⟨".L2_scc_rt_alloc.2_slow", [(0, b6), (4, b7)], none⟩,
  ⟨".L2_scc_rt_alloc.4_full", [(0, b9)], none⟩,
  ⟨".L2_scc_rt_alloc.5_ok", [(0, b11), (8, [iAdrpH.toDir]), (9, [iAddH.toDir]), (10, b12), (41, [iHdr]),
    (42, b13), (54, [iRet.toDir])], none⟩]

end Alloc

/-! ## `scc_rt_print` -/

section Print

open Spike.Lib.A64.Print

/-- `scc_rt_print`'s blocks and its prologue's fall-through (`Print.printIn`). -/
def printGrps : List RGrp := [
  ⟨"scc_rt_print", [(0, b0)], some (6, ".L9_scc_rt_print.0_entry")⟩,
  ⟨".L9_scc_rt_print.0_entry", [(0, b1)], none⟩,
  ⟨".L9_scc_rt_print.1_loop", [(0, b2), (4, b3)], none⟩,
  ⟨".L9_scc_rt_print.2_write", [(0, b4), (4, [Spike.Lib.A64.Flow.svcDir]), (5, b5), (12, b6), (13, b7)], none⟩,
  ⟨".L9_scc_rt_print.3_chk2", [(0, b8), (6, b9), (7, b10)], none⟩,
  ⟨".L9_scc_rt_print.4_chk3", [(0, b11), (4, b12)], none⟩,
  ⟨".L9_scc_rt_print.5_adv", [(0, b13)], none⟩,
  ⟨".L9_scc_rt_print.6_fail", [(0, b14)], none⟩,
  ⟨".L9_scc_rt_print.7_done", [(0, b16)], none⟩]

end Print

/-! ## `scc_rt_abort` and the stubs -/

section Abort

open Spike.Lib.A64.Abort Spike.Lib.A64.Flow

/-- `scc_rt_abort`'s blocks and its prologue's fall-through (`Abort.dispIn`). -/
def dispGrps : List RGrp := [
  ⟨"scc_rt_abort", [(0, Disp.d0)], some (5, ".L12_scc_rt_abort.0_entry")⟩,
  ⟨".L12_scc_rt_abort.0_entry", [(0, Disp.t1), (4, Disp.j1)], none⟩,
  ⟨".L12_scc_rt_abort.1_is0", [(0, Disp.g1)], none⟩,
  ⟨".L12_scc_rt_abort.2_next1", [(0, Disp.t2), (4, Disp.j2)], none⟩,
  ⟨".L12_scc_rt_abort.3_is2", [(0, Disp.g2)], none⟩,
  ⟨".L12_scc_rt_abort.4_next3", [(0, Disp.t3), (4, Disp.j3)], none⟩,
  ⟨".L12_scc_rt_abort.5_is4", [(0, Disp.g3)], none⟩,
  ⟨".L12_scc_rt_abort.6_next5", [(0, Disp.t4), (4, Disp.j4)], none⟩,
  ⟨".L12_scc_rt_abort.7_is6", [(0, Disp.g4)], none⟩,
  ⟨".L12_scc_rt_abort.8_next7", [(0, Disp.t5), (4, Disp.j5)], none⟩,
  ⟨".L12_scc_rt_abort.9_is8", [(0, Disp.g5)], none⟩]

/-- A stub's blocks and its labels' gaps (`Abort.stubIn`). -/
def stubGrps (st : Stub) (b1 : List Directive) : List RGrp := [
  ⟨st.fn, [(0, b0)], some (4, st.entry)⟩,
  ⟨st.entry, [(0, [(SI.adrp .X9 st.msg).toDir]), (1, [(SI.addLo12 .X9 .X9 st.msg).toDir]), (2, b1),
    (7, [svcDir]), (8, b2)],
    some (11, st.exit)⟩,
  ⟨st.exit, [(0, [svcDir])], none⟩]

/-- The stubs and `scc_rt_abort`, in program order. -/
def abortGrps : List RGrp :=
  dispGrps ++ stubGrps overflow b1Overflow ++ stubGrps heap b1Heap ++ stubGrps stack b1Stack ++
    stubGrps write b1Write ++ stubGrps threads b1Threads

end Abort

/-! ## The table -/

/-- **The runtime's fixed code**, in program order: `scc_rt_main`'s tail
(`main`: `mainGrps0` or `mainGrps1`), `scc_rt_alloc`, `scc_rt_print`,
`scc_rt_abort` and the stubs. -/
def rtTab (main : List RGrp) : List RGrp := main ++ allocGrps ++ printGrps ++ abortGrps

/-! ## The checks from the pass -/

section Of

variable {prog : List Directive} {main : List RGrp}

theorem rtAll_parts (h : rtIn prog (rtTab main) = true) :
    RtAll prog main ∧ RtAll prog printGrps ∧ RtAll prog abortGrps ∧ RtAll prog allocGrps := by
  have h := rtIn_sound h
  unfold rtTab at h
  obtain ⟨h12, h3⟩ := RtAll.append h
  obtain ⟨h1a, h2⟩ := RtAll.append h12
  obtain ⟨h1, ha⟩ := RtAll.append h1a
  exact ⟨h1, h2, h3, ha⟩

/-- **`scc_rt_alloc`'s code** from the pass. -/
theorem allocIn_of_rtIn (h : rtIn prog (rtTab main) = true) : Flow.allocIn prog = true := by
  have h := (rtAll_parts h).2.2.2
  simp only [allocGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [Flow.allocIn, h, Bool.and_self]

open Spike.Lib.A64.Print in
/-- **`scc_rt_print`'s code** from the pass. -/
theorem printIn_of_rtIn (h : rtIn prog (rtTab main) = true) : Print.printIn prog = true := by
  have h := (rtAll_parts h).2.1
  simp only [printGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [Print.printIn, h, Bool.and_self]

open Spike.Lib.A64.Abort in
theorem stubIn_of {st : Stub} {b1 : List Directive} {rest : List RGrp}
    (h : RtAll prog (stubGrps st b1 ++ rest)) : Abort.stubIn prog st b1 = true := by
  have h := (RtAll.append h).1
  simp only [stubGrps, RtAll, BsOk, GapAt, and_true] at h
  simp only [Abort.stubIn, h, Bool.and_self]

open Spike.Lib.A64.Abort in
/-- **The stubs' and `scc_rt_abort`'s code** from the pass. -/
theorem abortIn_of_rtIn (h : rtIn prog (rtTab main) = true) : Abort.abortIn prog = true := by
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
theorem mainIn0_of_rtIn (h : rtIn prog (rtTab mainGrps0) = true) : Abort.mainIn0 prog = true := by
  have h := (rtAll_parts h).1
  simp only [mainGrps0, RtAll, BsOk, GapAt, and_true] at h
  simp only [Abort.mainIn0, h, Bool.and_self]

/-- **`scc_rt_main`'s tail after a setup block** from the pass. -/
theorem mainIn_of_rtIn (h : rtIn prog (rtTab mainGrps1) = true) : Abort.mainIn prog = true := by
  have h := (rtAll_parts h).1
  simp only [mainGrps1, RtAll, BsOk, GapAt, and_true] at h
  simp only [Abort.mainIn, h, Bool.and_self]

end Of

end Scc.Cert.Rt.A64.RtIn

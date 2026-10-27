import Scc.Cert.Code1A64

/-!
# The runtime routines a stack-checked function calls fit in the headroom (AArch64)

A stack-checked function `f` with a row `(_, frame, nf)` of the stack
need table (`Code1A64.needOk1`) is entered with at least `nf` bytes above
the stack limit `L`. At a `bl` its stack pointer is its frame below the
entry one, so at least `nf - frame ≥ 0` above `L`; at a tail call it is the entry one. A callee without a row is a
runtime routine with depth `d` within `Tcb.headroom` (`rtOk`), so every byte
it uses is at least `L - Tcb.headroom`: `rt_call_fits`, `rt_tail_fits`.
-/

namespace Spike.Lib.RtHeadroomA64

open Scc.Cert.Code1A64

theorem rtOk_lookup {g : String} (h : rtOk g = true) :
    ∃ d, rtDepth.lookup g = some d ∧ d ≤ Scc.IR.Tcb.headroom := by
  unfold rtOk at h
  split at h
  · exact ⟨_, ‹_›, of_decide_eq_true h⟩
  · exact absurd h (by simp)

/-- **A runtime routine called by a stack-checked function stays in the
headroom**: its lowest byte, `d` below the caller's stack pointer at the
`bl`, is at least `L - Tcb.headroom`. -/
theorem rt_call_fits {tbl : List Scc.Cert.NeedA64.Row} {name : String} {frame : Nat}
    {f : Scc.IR.Func} {l : String} {fr nf : Nat} {g : String}
    (hn : needOk1 tbl name frame f = true)
    (hrow : Scc.Cert.NeedA64.row? tbl name = some (l, fr, nf))
    (hg : g ∈ (callees f).1) (hng : Scc.Cert.NeedA64.row? tbl g = none)
    {L sp0 : Int} (hsp : L + nf ≤ sp0) :
    ∃ d, rtDepth.lookup g = some d ∧
      L - Scc.IR.Tcb.headroom ≤ sp0 - (frame : Nat) - d := by
  unfold needOk1 at hn
  rw [hrow] at hn
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hn
  obtain ⟨⟨⟨_, hfr⟩, hc⟩, _⟩ := hn
  have := hc g hg
  rw [hng] at this
  obtain ⟨d, hd, hdh⟩ := rtOk_lookup this
  exact ⟨d, hd, by omega⟩

/-- **A runtime routine tail called by a stack-checked function stays in the
headroom**: its lowest byte, `d` below the caller's entry stack pointer, is
at least `L - Tcb.headroom`. -/
theorem rt_tail_fits {tbl : List Scc.Cert.NeedA64.Row} {name : String} {frame : Nat}
    {f : Scc.IR.Func} {l : String} {fr nf : Nat} {g : String}
    (hn : needOk1 tbl name frame f = true)
    (hrow : Scc.Cert.NeedA64.row? tbl name = some (l, fr, nf))
    (hg : g ∈ (callees f).2) (hng : Scc.Cert.NeedA64.row? tbl g = none)
    {L sp0 : Int} (hsp : L + nf ≤ sp0) :
    ∃ d, rtDepth.lookup g = some d ∧ L - Scc.IR.Tcb.headroom ≤ sp0 - d := by
  unfold needOk1 at hn
  rw [hrow] at hn
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hn
  obtain ⟨_, ht⟩ := hn
  have := ht g hg
  rw [hng] at this
  obtain ⟨d, hd, hdh⟩ := rtOk_lookup this
  exact ⟨d, hd, by omega⟩

end Spike.Lib.RtHeadroomA64

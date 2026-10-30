/-
**Resuming a call from inside the callee** (AArch64): `call_nd_FWK`'s
return half for a segment that starts at a callee's node rather than at
the caller's call node (a state already inside the callee, e.g. the
allocator's `n4` after the counter's add, whose caller is known only
through the callee's frame condition).

The callee runs in `R.callee kc lo' hi'` under a frame condition `F'` that
gives the caller's `F` and, for some caller state `m0`, `σC` (of `PC`), the
caller's cells outside the callee's region as in `m0` (`CKept`). A segment
of the callee from `P` to its exits `Ex x` (with a memory postcondition
`M`) is one of the caller from `P` to the caller's nodes, given that every
exit, seen from the caller's region (`leave`, `sp` at `kc` plus the exit's
offset), lands at a node of the caller (`hret`, `call_nd_FWK`'s).

- `next_of_exit`: one exit state, left to the caller's region, is at a
  caller node (`abs_leave`).
- `seg_resumeW`: the callee's segment from `P` as one to the caller's nodes.
-/
import Spike.Lib.A64Call

namespace Spike.Lib.A64.Flow

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64

section Resume

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {ι κ : Sort _} {N : ι → ND}
  {E : κ → ND}

/-- **A callee's exit state is at a caller node**: at the callee's exit `x`
in `R.callee kc lo' hi'` under `F'` (giving `F` and the caller's cells as
in a caller state of `PC`), with `M`, the state is at the caller's node
`hret` lands it at, under any `F₂` that `F` and `M` give. -/
theorem next_of_exit {kc lo' hi' : Int} {F' F₂ M : MachineData → Prop} {PC : AS → Prop} {x : ND}
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC ∧ PC σC)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hret : ∀ σx c σC, x.J σx c → PC σC →
      Lands N E ⟨x.pc, ⟨kc + x.o.sp, []⟩, leave (R.callee kc lo' hi') kc σC σx⟩ c)
    {s : State} {c : Ctl} (h : At exe endPc (R.callee kc lo' hi') F' x s c) (hM : M s.st.1) :
    Next exe endPc R F₂ N E s c := by
  obtain ⟨he, hn, hdc, hpc, σx, hAx, hD, hJx⟩ := h
  obtain ⟨hDF, m0, σC, o, hK, hAC, hP⟩ := hF' _ hD
  have hAR := abs_leave hAx hAC hK
  have hs : s = { s with st := (s.st.1, x.pc) } := by rw [← hpc]
  rw [hs]
  rcases hret σx c σC hJx hP with ⟨j, hj⟩ | ⟨y, hy⟩
  · exact .inl ⟨j, hj.at he hn hdc hAR (hF₂ _ hDF hM)⟩
  · exact .inr ⟨y, hy.at he hn hdc hAR (hF₂ _ hDF hM)⟩

/-- **A callee's segment from inside it is one of its caller**: a segment
inside `W` from `P` to the callee's exits `Ex x` in `R.callee kc lo' hi'`
under `F'` (with `M`), `F'` giving the caller's `F` and its cells outside
the callee's region as in a caller state of `PC`, is one from `P` to the
caller's nodes `N`, `E` under `F₂`, given each exit's landing there
(`hret`, as `call_nd_FWK`'s, at the caller's state `leave` gives). -/
theorem seg_resumeW {W : Frag isaLSE2} {K : State → State → Prop} {P : Frag isaLSE2} {kc lo' hi' : Int}
    {F' F₂ M : MachineData → Prop} {PC : AS → Prop} {κ' : Sort _} {Ex : κ' → ND}
    (hseg : SegW W K p lbl ms P (fun s c => ∃ x, At exe endPc (R.callee kc lo' hi') F' (Ex x) s c ∧ M s.st.1))
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC ∧ PC σC)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hret : ∀ x σx c σC, (Ex x).J σx c → PC σC →
      Lands N E ⟨(Ex x).pc, ⟨kc + (Ex x).o.sp, []⟩, leave (R.callee kc lo' hi') kc σC σx⟩ c) :
    SegW W K p lbl ms P (Next exe endPc R F₂ N E) :=
  hseg.mono_post fun _ _ ⟨x, h, hM⟩ => next_of_exit hF' hF₂ (hret x) h hM

end Resume

end Spike.Lib.A64.Flow

/-- info: 'Spike.Lib.A64.Flow.next_of_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.next_of_exit

/-- info: 'Spike.Lib.A64.Flow.seg_resumeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.seg_resumeW

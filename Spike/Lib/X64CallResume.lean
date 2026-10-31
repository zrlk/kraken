/-
**Resuming a call from inside the callee** (x64): `call_nd_FWK`'s return
half for a segment that starts at a callee's node rather than at the
caller's call node, as on AArch64 (`Spike/Lib/A64CallResume.lean`).

The callee runs in `R.callee kc lo' hi'` under a frame condition `F'` that
gives the caller's `F` and, for some caller state `m0`, `σC` (of `PC`), the
caller's cells outside the callee's region as in `m0` (`CKept`). A segment
of the callee from `P` to its exits `Ex x` (with a memory postcondition
`M`) is one of the caller from `P` to the caller's nodes, given that every
exit, seen from the caller's region (`leave`, `%rsp` at `kc` plus the
exit's offset), lands at a node of the caller (`hret`, `call_nd_FWK`'s).

- `abs_leaveC`: the caller's abstract state after the callee (`leave`), for
  a callee state at any offsets (AArch64's `abs_leave`; renamed against `Rt.abs_leave`).
- `next_of_exit`: one exit state, left to the caller's region, is at a
  caller node.
- `seg_resumeW`: the callee's segment from `P` as one to the caller's nodes.
-/
import Spike.Lib.X64Call

namespace Spike.Lib.X64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64

/-- **The caller's abstract state after the callee returns** (`leave`): a
callee's state `σx` in its region `R.callee kc lo' hi'` at offsets `o`, the
caller's cells outside it as in `mC`, which `σC` abstracts, give the
caller's state in `R` at the callee's `%rsp` shifted by `kc`. -/
theorem abs_leaveC {R : Region} {kc lo' hi' : Int} {o oC : SO} {m mC : MachineData} {σC σx : AS}
    (hAx : Abs (R.callee kc lo' hi') o m σx) (hAC : Abs R oC mC σC)
    (hDF : CKept R kc lo' hi' mC m) :
    Abs R ⟨kc + o.sp, []⟩ m (leave (R.callee kc lo' hi') kc σC σx) := by
  refine ⟨hAx.regs, hAx.zmms, hAx.status, ?_, fun k hk => ?_⟩
  · intro r k' hr
    obtain ⟨rfl, rfl⟩ := SO.get_sp_only hr
    have := hAx.so .rsp o.sp (by simp [SO.get])
    simp only [leave] at this ⊢
    rw [this, Region.callee_addr]
  · by_cases hin : (R.callee kc lo' hi').Off (k - kc)
    · obtain ⟨j, hj, hv⟩ := hAx.slot _ hin
      refine ⟨j, ?_, ?_⟩
      · rw [Region.callee_addr, show kc + (k - kc) = k by omega] at hj; exact hj
      · simp only [leave]; rw [ite_eq_left hin]; exact hv
    · obtain ⟨j, hj, hv⟩ := hAC.slot k hk
      refine ⟨j, ?_, ?_⟩
      · rw [hDF k hk hin]; exact hj
      · simp only [leave]; rw [ite_eq_right hin]; exact hv

section Resume

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
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
  have hAR := abs_leaveC hAx hAC hK
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
theorem seg_resumeW {W : Frag isa} {K : State → State → Prop} {P : Frag isa} {kc lo' hi' : Int}
    {F' F₂ M : MachineData → Prop} {PC : AS → Prop} {κ' : Sort _} {Ex : κ' → ND}
    (hseg : SegW W K p lbl ms P (fun s c => ∃ x, At exe endPc (R.callee kc lo' hi') F' (Ex x) s c ∧ M s.st.1))
    (hF' : ∀ m, F' m → F m ∧ ∃ m0 σC o, CKept R kc lo' hi' m0 m ∧ Abs R o m0 σC ∧ PC σC)
    (hF₂ : ∀ m, F m → M m → F₂ m)
    (hret : ∀ x σx c σC, (Ex x).J σx c → PC σC →
      Lands N E ⟨(Ex x).pc, ⟨kc + (Ex x).o.sp, []⟩, leave (R.callee kc lo' hi') kc σC σx⟩ c) :
    SegW W K p lbl ms P (Next exe endPc R F₂ N E) :=
  hseg.mono_post fun _ _ ⟨x, h, hM⟩ => next_of_exit hF' hF₂ (hret x) h hM

end Resume

end Spike.Lib.X64

/-- info: 'Spike.Lib.X64.abs_leaveC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.abs_leaveC

/-- info: 'Spike.Lib.X64.next_of_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.next_of_exit

/-- info: 'Spike.Lib.X64.seg_resumeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.seg_resumeW

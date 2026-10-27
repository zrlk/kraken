/-
**Tail pieces over covered code** (AArch64): the pieces a write tail's
closure proof (`ClosedC`, `Spike/Lib/TailDt.lean`) is assembled from, for
any executable, layout and marks; the code enters only through `CodeAt`
hypotheses, the transfer sites through `hns`. A tail point carries a frame
condition `C` no write inside the region breaks (`FStable`), as `At` does.

- `Pt exe endPc R C pc o J`: at `pc`, the machine data related (`Abs`) at
  offsets `o` to an abstract state satisfying `J`; `pt_of_at` from a node's
  fragment (`At`);
- `BlkSt … pc o J blk`: before the `k`-th instruction of the covered block
  `blk` at `pc`, related to the abstract run of the first `k` from a `J`
  state; `BlkEnd`: at the whole run's end; `pt_blkSt` (entry),
  `blkEnd_pt` (the run lands at one point);
- `blkSt_steps`: a step inside the block stays inside or lands at its end
  (`StepsTo`);
- `svc_steps`: a system call (not a `clone`) at a point steps past its cell,
  `x0` some result (`svcStep`);
- `exit_closed`: an `exit_group` call has no step, so its point is closed;
- `pt_iff_at`, `pt_enter`, `pt_leave`: a point is a node's fragment, and a
  tail crossing a call changes region by `at_enter`/`at_leave`
  (`Spike/Lib/A64Call.lean`), the callee's frame condition stable by
  `fstable_enter`.
-/
import Spike.Lib.Rt.A64BlkDt
import Spike.Lib.Rt.A64StubDt

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib (ClosedC StepsTo)
open Scc.Cert.Rt.A64.Print (add0)

/-! ## Tail points -/

/-- **A tail point**: the executable and its end, no declarations, at `pc`,
the machine data related at offsets `o` to an abstract state satisfying
`J`, the frame condition `C` holding. -/
def Pt (exe : _root_.Executable) (endPc : Int64) (R : Region) (C : MachineData → Prop) (pc : Int64) (o : SO)
    (J : Flow.AS → Prop) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ s.decls = {} ∧ s.st.2 = pc ∧ ∃ σ, J σ ∧ Flow.Abs R o s.st.1 σ ∧ C s.st.1

/-- **Inside a covered block** `blk` at `pc`: before its `k`-th instruction,
the machine data related to the abstract run of the first `k` from a `J`
state. -/
def BlkSt (exe : _root_.Executable) (endPc : Int64) (R : Region) (C : MachineData → Prop) (pc : Int64) (o : SO)
    (J : Flow.AS → Prop) (blk : List Directive) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ s.decls = {} ∧ ∃ σ0, J σ0 ∧ ∃ k < blk.length,
    s.st.2 = pc + Int64.ofNat (4 * k) ∧
    Flow.Abs R (Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ0⟩).so s.st.1
      (Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨pc, o, σ0⟩).σ ∧ C s.st.1

/-- **At a covered block's end**: at the abstract run's exit pc, related to
the whole run from a `J` state. -/
def BlkEnd (exe : _root_.Executable) (endPc : Int64) (R : Region) (C : MachineData → Prop) (pc : Int64) (o : SO)
    (J : Flow.AS → Prop) (blk : List Directive) (s : State) : Prop :=
  s.exe = exe ∧ s.endPc = endPc ∧ s.decls = {} ∧ ∃ σ0, J σ0 ∧
    s.st.2 = (Flow.arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).pc ∧
    Flow.Abs R (Flow.arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).so s.st.1
      (Flow.arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).σ ∧ C s.st.1

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {C : MachineData → Prop} {pc : Int64} {o : SO}
  {J : Flow.AS → Prop}

/-- A node's fragment is a tail point, its invariant at the control `c`. -/
theorem pt_of_at {n : ND} {s : State} {c : Ctl} (h : At exe endPc R C n s c) :
    Pt exe endPc R C n.pc n.o (fun σ => n.J σ c) s := by
  obtain ⟨he, hn, hd, hpc, σ, hA, hC, hJ⟩ := h
  exact ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩

/-- **A block's entry**: a point at a nonempty block's pc is inside it
(`k = 0`). -/
theorem pt_blkSt {blk : List Directive} {s : State} (hne : blk ≠ []) (h : Pt exe endPc R C pc o J s) :
    BlkSt exe endPc R C pc o J blk s := by
  obtain ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩ := h
  refine ⟨he, hn, hd, σ, hJ, 0, List.length_pos_iff.mpr hne, by rw [add0]; exact hpc, ?_, hC⟩
  simpa [Flow.arun] using hA

/-- **A block landing at one point**: if the run from every `J` state ends
at `pc'` with offsets no weaker than `o'` and its state satisfying `J'`, the
block's end is that point. -/
theorem blkEnd_pt {blk : List Directive} {pc' : Int64} {o' : SO} {J' : Flow.AS → Prop} {s : State}
    (hL : ∀ σ0, J σ0 → (Flow.arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).pc = pc' ∧
      SO.le o' (Flow.arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).so = true ∧
      J' (Flow.arun (_root_.Executable.labels exe).label blk ⟨pc, o, σ0⟩).σ)
    (h : BlkEnd exe endPc R C pc o J blk s) : Pt exe endPc R C pc' o' J' s := by
  obtain ⟨he, hn, hd, σ0, hJ, hpc, hA, hC⟩ := h
  obtain ⟨h1, h2, h3⟩ := hL σ0 hJ
  exact ⟨he, hn, hd, hpc.trans h1, _, h3, hA.weaken h2, hC⟩

/-! ## Calls: entering and leaving a callee's region

`at_enter`/`at_leave` (`Spike/Lib/A64Call.lean`) at tail points: a tail that
crosses a `bl` or a `ret` changes region at the call's `sp` (`kc`), the
callee's frame condition the caller's `C`, its cells outside the callee's
region kept (`CKept`, stable by `fstable_enter`). -/

/-- **A tail point is a node's fragment**, at any control. -/
theorem pt_iff_at {s : State} (c : Ctl) :
    Pt exe endPc R C pc o J s ↔ At exe endPc R C ⟨pc, o, fun σ _ => J σ⟩ s c := by
  constructor
  · rintro ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩
    exact ⟨he, hn, hd, hpc, σ, hA, hC, hJ⟩
  · rintro ⟨he, hn, hd, hpc, σ, hA, hC, hJ⟩
    exact ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩

/-- **Entering the callee's region** (at the call's `sp`, `o.sp`): a tail
point is at the callee's entry (`sp` at its region's base), under the
callee's frame condition from it, the abstract state the caller's
entered. The control `c` is any (`At` at it is `Pt`, `pt_iff_at`). -/
theorem pt_enter {lo' hi' : Int} (hlo : R.lo ≤ o.sp + lo') (hkc : o.sp < R.hi) (hhi0 : hi' ≤ 0)
    (hk8 : o.sp % 8 = 0) (c : Ctl) {s : State} (h : Pt exe endPc R C pc o J s) :
    ∃ m0 σC, Pt exe endPc (R.callee o.sp lo' hi')
      (fun m => C m ∧ CKept R o.sp lo' hi' m0 m ∧ Flow.Abs R o m0 σC) pc ⟨0, []⟩
      (fun σ => σ = enter o.sp σC ∧ J σC) s := by
  obtain ⟨m0, σC, hA⟩ := at_enter (nC := ⟨pc, o, fun σ _ => J σ⟩) (lo' := lo') hlo hkc hhi0 hk8
    ((pt_iff_at c).mp h)
  refine ⟨m0, σC, (pt_iff_at c).mpr ?_⟩
  obtain ⟨he, hn, hd, hpc, σ, hA', hC, -, h2, h3⟩ := hA
  exact ⟨he, hn, hd, hpc, σ, hA', hC, h2, h3⟩

/-- **Leaving the callee's region** (back to the caller's, `sp` at `kc`): a
tail point of the callee (`sp` at its region's base), under a frame
condition giving the caller's `C`, its cells outside the callee's region as
in a caller's state `m0`, `σC` of `P`, is a tail point of the caller, the
abstract state the caller's left (`leave`); `c` is any control. -/
theorem pt_leave {kc lo' hi' : Int} {C' : MachineData → Prop} {P : Flow.AS → Prop}
    (hC' : ∀ m, C' m → C m ∧ ∃ m0 σC o0, CKept R kc lo' hi' m0 m ∧ Flow.Abs R o0 m0 σC ∧ P σC)
    (c : Ctl) {s : State} (h : Pt exe endPc (R.callee kc lo' hi') C' pc ⟨0, []⟩ J s) :
    Pt exe endPc R C pc ⟨kc, []⟩
      (fun σ => ∃ σx σC, J σx ∧ P σC ∧ σ = leave (R.callee kc lo' hi') kc σC σx) s := by
  have := at_leave (F := C) (x := ⟨pc, ⟨0, []⟩, fun σ _ => J σ⟩) rfl hC'
    ((pt_iff_at c).mp h)
  exact (pt_iff_at c).mpr this

/-! ## Steps -/

section Step

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}

/-- **Inside a covered block** (off the transfer sites, `hns`): a
certification step goes to the next instruction or, from the last, to the
block's end, keeping the promises. -/
theorem blkSt_steps {lo hi : Int} {blk : List Directive} (hok : Flow.okBlk lo hi o blk = true) (hF : FStable R C)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc blk)
    (hns : ∀ s, BlkSt exe endPc R C pc o J blk s → Kernel.siteAt abi μ s = none) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (BlkSt exe endPc R C pc o J blk)
      (BlkEnd exe endPc R C pc o J blk) := by
  rintro ⟨t, mem⟩ q hD h
  have hsi := hns _ hD
  obtain ⟨he, hn, hd, σ0, hJ, k, hk, hpc, hA, hC⟩ := hD
  have hl : labA t.st = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels t.st.exe).label L = _; rw [he]
  by_cases hk1 : k + 1 < blk.length
  · obtain ⟨hpr, m', hq, hA', hD'⟩ := blk_stepC_mid (am := ⟨pc, o, σ0⟩) hsi hl (hcode t.st he hn) hok hR hal
      hlo hhi hk1 hpc hA h
    refine ⟨.inl ?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, hd, σ0, hJ, k + 1, hk1, rfl, hA', hF _ _ hC hD'⟩
  · obtain ⟨hpr, m', hq, hA', hD'⟩ := blk_stepC_last (am := ⟨pc, o, σ0⟩) hsi hl (hcode t.st he hn) hok hR hal
      hlo hhi (by omega) hpc hA h
    refine ⟨.inr ?_, hpr⟩
    rw [hq]
    exact ⟨he, hn, hd, σ0, hJ, rfl, hA', hF _ _ hC hD'⟩

/-- **A system call at a point** (off the transfer sites, `hns`): if every
`J` state's registers decode to a call that is not a `clone`, a
certification step goes past the cell, `x0` some result (its static offset
forgotten), keeping the promises. -/
theorem svc_steps (hF : FStable R C) (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [svcDir])
    (hcall : ∀ σ, J σ → ∃ call, svcCall σ.regs = some call ∧ ∀ st tl, call ≠ .clone st tl)
    (hns : ∀ s, Pt exe endPc R C pc o J s → Kernel.siteAt abi μ s = none) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (Pt exe endPc R C pc o J)
      (Pt exe endPc R C (pc + 4) (o.kill .X0) (fun σ' => ∃ σ v, J σ ∧ σ' = svcStep v σ)) := by
  refine StepsTo.of_into fun ⟨t, mem⟩ q hD h => ?_
  have hsi := hns _ hD
  obtain ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩ := hD
  have hc := (hcode t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
  obtain ⟨call, hcl, hnc⟩ := hcall σ hJ
  obtain ⟨hpr, v, -, hq⟩ := svc_stepC hsi hc (by rw [hA.regs]; exact hcl) hnc h
  refine ⟨?_, hpr⟩
  rw [hq]
  exact ⟨he, hn, hd, by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl, _, ⟨σ, v, hJ, rfl⟩,
    Rt.Abs.svcRet hA v, hF _ _ hC fun _ _ _ => rfl⟩

/-- **An `exit_group` call at a point** (off the transfer sites, `hns`): if
every `J` state has `x8 = 94`, there is no certification step, so the point
is closed. -/
theorem exit_closed (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [svcDir])
    (h94 : ∀ σ, J σ → σ.regs.X8.toNat = 94)
    (hns : ∀ s, Pt exe endPc R C pc o J s → Kernel.siteAt abi μ s = none) :
    ClosedC A (Kernel.certSem abi A μ x tid) tid (Pt exe endPc R C pc o J) := by
  rintro ⟨t, mem⟩ q hD h
  have hsi := hns _ hD
  obtain ⟨he, hn, -, hpc, σ, hJ, hA, -⟩ := hD
  have hc := (hcode t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
  exact absurd h (exit_stepC hsi hc (by rw [hA.regs]; exact h94 σ hJ))

end Step

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.blkSt_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms blkSt_steps

end Spike.Lib.A64.Rt

/-
**The abort path's write tail** (AArch64), for any executable and layout:
from `scc_rt_abort`'s entry with a code `k` in `x0` (`Abort.Disp`: the
prologue storing the code at `[sp]`, the tests against `1`, …, `5` and
their jumps), the jump to stub `k`, then the stub's prologue, its `adrp`/`add`
of the message and its argument block, up to its `write` call, where the
stub's tail `StubDt` (`Spike/Lib/Rt/A64StubDt.lean`) takes over. The
pieces are `Spike/Lib/Rt/A64TailDt.lean`'s, in one region `RA` serving the
dispatcher and the stub (the stub reuses the dispatcher's frame base), under
any frame condition `C` no write inside the region breaks: the path does not
return. The code enters only through `Abort.Disp.Code`/`Abort.Code`, the
transfer sites through `hns`.

- `dxCode`, `subs_z`: a stub's code, and the dispatcher's test against `j`
  on the code `k` setting `z` iff `j = k`;
- `siPt_steps`: a single `SI` (no event) at a point steps past it;
  `pt_mono`: a point under weaker facts;
- `stubDt_of_pt`: a stub's `write` call at a point in a region holding the
  stub's frame is in `StubDt`;
- `AbIn exe endPc RA C dx`: the dispatcher's pieces for the code of `dx`
  (`dJ`: the stored code and the tests passed so far) and stub `dx`'s pieces;
  `abIn_steps`: a step from `AbIn` lands in `AbIn` or in stub `dx`'s
  `StubDt`;
- `abIn_of_fail`: `print`'s abort call (`Print.b14`, `x0 = 4`) lands in
  `AbIn … .write` in the callee's region at `print`'s `sp` (the `hfail` of
  `printIn_steps`), under `pt_enter`'s frame condition; `abR_ok`: that
  region is fine.
-/
import Spike.Lib.Rt.A64PrintDt

namespace Spike.Lib.A64.Rt

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Kraken.Promising.Lower.A64 (CellAt after labelAddr)
open Scc.Sem
open Scc.Sem.A64 (abi)
open Spike.Lib.A64.Flow
open Spike.Lib.A64
open Spike.Lib (ClosedC StepsTo Region)
open Spike.Lib.LowerA64 (spill Sp16 Spilled)
open Spike.Lib.A64.Abort.Disp (DN DX)
open Scc.Cert.Rt.A64.Print (add0)

/-! ## Codes -/

/-- **A stub's code**: `x0` at the dispatcher's entry selecting it. -/
def dxCode : DX → Nat
  | .overflow => 1
  | .heap => 2
  | .stack => 3
  | .write => 4
  | .threads => 5

theorem dxCode_le (dx : DX) : dxCode dx ≤ 5 := by cases dx <;> decide

/-- **The dispatcher's test against `j`** on the code `k` (both at most
`5`) sets `z` iff `j = k`. -/
theorem subs_z {j k : Nat} (hj : j ≤ 5) (hk : k ≤ 5) :
    (StatusFlags.subs (BitVec.ofNat 64 k - BitVec.ofNat 64 j) (BitVec.ofNat 64 k) (BitVec.ofNat 64 j)).z =
      decide (j = k) := by
  have := (by decide +kernel : ∀ j : Fin 6, ∀ k : Fin 6,
    (StatusFlags.subs (BitVec.ofNat 64 k.val - BitVec.ofNat 64 j.val) (BitVec.ofNat 64 k.val)
      (BitVec.ofNat 64 j.val)).z = decide (j.val = k.val))
  exact this ⟨j, by omega⟩ ⟨k, by omega⟩

/-! ## Points -/

section Pt

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {C : MachineData → Prop} {pc : Int64}

/-- **A point under weaker facts**: weaker offsets and a weaker invariant. -/
theorem pt_mono {o o' : SO} {J J' : Flow.AS → Prop} {s : State} (h : Pt exe endPc R C pc o J s)
    (hJ : ∀ σ, J σ → J' σ) (hle : o'.le o = true) : Pt exe endPc R C pc o' J' s := by
  obtain ⟨he, hn, hd, hpc, σ, hj, hA, hC⟩ := h
  exact ⟨he, hn, hd, hpc, σ, hJ σ hj, hA.weaken hle, hC⟩

/-- **A stub's `write` call at a point is in its tail**, in a 16-aligned
region holding the stub's 48-byte frame: `sp` is the frame's base and the
spill is the frame's cell at `-40`. -/
theorem stubDt_of_pt {st : Abort.Stub} {s : State} (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48)
    (hhi : 0 ≤ R.hi)
    (h : Pt exe endPc R C (Abort.pcSvc (_root_.Executable.labels exe).label st) Abort.oI
      (fun σ => σ.regs.X0 = 2 ∧ σ.regs.X8 = 64) s) :
    StubDt exe endPc (_root_.Executable.labels exe).label st s := by
  obtain ⟨hs, hn, -, hpc, σ, ⟨h0, h8⟩, hA, -⟩ := h
  have hsp : s.st.1.regs.SP.toBitVec = R.addr (-48) := by rw [hA.regs]; exact hA.so.sp
  obtain ⟨j, hj, -⟩ := hA.slot (-40) ⟨by decide, by omega, by omega⟩
  refine ⟨hs, hn, .inl ⟨hpc, by rw [hA.regs]; exact h0, by rw [hA.regs]; exact h8, ?_, j, ?_⟩⟩
  · show _ = _
    rw [hsp]
    exact R.addr_align16 hal (by decide)
  · unfold spill
    rw [hsp, addr_spn, show (-48 : Int) + (8 : Int64).toInt = -40 by decide]
    exact hj

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}

/-- **A single `SI` at a point** (off the transfer sites, `hns`): a
certification step goes past its cell, the registers `SI.regs`, keeping
the promises. -/
theorem siPt_steps {o : SO} {J : Flow.AS → Prop} {si : SI} (hF : FStable R C)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [si.toDir])
    (hns : ∀ s, Pt exe endPc R C pc o J s → Kernel.siteAt abi μ s = none) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (Pt exe endPc R C pc o J)
      (Pt exe endPc R C (pc + 4) (si.so o)
        (fun σ' => ∃ σ, J σ ∧ σ' = si.step (_root_.Executable.labels exe).label σ)) := by
  refine StepsTo.of_into fun ⟨t, mem⟩ q hD h => ?_
  have hsi := hns _ hD
  obtain ⟨he, hn, hd, hpc, σ, hJ, hA, hC⟩ := hD
  have hc : CellAt t.st si.toDir 4 := (hcode t.st he hn).cell (j := 0) rfl rfl rfl (by rw [add0]; exact hpc)
  have hl : labelAddr t.st = (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels t.st.exe).label L = _; rw [he]
  obtain ⟨hpr, hq⟩ := si_stepC hsi hc h
  refine ⟨?_, hpr⟩
  rw [hq, hl]
  exact ⟨he, hn, hd, by show t.st.st.2 + Int64.ofNat 4 = _; rw [hpc]; rfl, _, ⟨σ, hJ, rfl⟩,
    si.abs _ hA, hF _ _ hC fun _ _ _ => rfl⟩

end Pt

/-! ## The pieces -/

section Pieces

variable (exe : _root_.Executable) (endPc : Int64) (RA : Region) (C : MachineData → Prop)

/-- The dispatcher's node pcs (`Abort.Disp.DN.nd`'s). -/
def dpc : DN → Int64
  | .e => (_root_.Executable.labels exe).label "scc_rt_abort"
  | .t1 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.0_entry"
  | .j1 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.0_entry" + 4 + 4 + 4 + 4
  | .g1 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.1_is0"
  | .t2 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.2_next1"
  | .j2 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.2_next1" + 4 + 4 + 4 + 4
  | .g2 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.3_is2"
  | .t3 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.4_next3"
  | .j3 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.4_next3" + 4 + 4 + 4 + 4
  | .g3 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.5_is4"
  | .t4 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.6_next5"
  | .j4 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.6_next5" + 4 + 4 + 4 + 4
  | .g4 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.7_is6"
  | .t5 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.8_next7"
  | .j5 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.8_next7" + 4 + 4 + 4 + 4
  | .g5 => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.9_is8"
  | .dead => (_root_.Executable.labels exe).label ".L12_scc_rt_abort.10_next9"

/-- The dispatcher's blocks (the dead halt loop's none). -/
def dblk : DN → List Directive
  | .e => Abort.Disp.d0
  | .t1 => Abort.Disp.t1
  | .j1 => Abort.Disp.j1
  | .g1 => Abort.Disp.g1
  | .t2 => Abort.Disp.t2
  | .j2 => Abort.Disp.j2
  | .g2 => Abort.Disp.g2
  | .t3 => Abort.Disp.t3
  | .j3 => Abort.Disp.j3
  | .g3 => Abort.Disp.g3
  | .t4 => Abort.Disp.t4
  | .j4 => Abort.Disp.j4
  | .g4 => Abort.Disp.g4
  | .t5 => Abort.Disp.t5
  | .j5 => Abort.Disp.j5
  | .g5 => Abort.Disp.g5
  | .dead => []

/-- The dispatcher's offsets: at entry, then inside its frame. -/
def dso : DN → SO
  | .e => Abort.oE
  | _ => Abort.Disp.oD

/-- Before the test against `j`: the stored code is `k`, at least `j`. -/
def jt (k j : Nat) (σ : Flow.AS) : Prop := σ.slot (-32) = BitVec.ofNat 64 k ∧ j ≤ k
/-- Past the test against `j`: the stored code is `k`, above `j`. -/
def jj (k j : Nat) (σ : Flow.AS) : Prop := σ.slot (-32) = BitVec.ofNat 64 k ∧ j < k
/-- At the jump to stub `j`: the stored code is `k`, which is `j`. -/
def jg (k j : Nat) (σ : Flow.AS) : Prop := σ.slot (-32) = BitVec.ofNat 64 k ∧ j = k

/-- **The dispatcher's facts at a node** for the code `k`: `x0 = k` at the
entry, then the stored code and the tests passed so far; the halt loop is
unreachable. -/
def dJ (k : Nat) : DN → Flow.AS → Prop
  | .e => fun σ => σ.regs.X0.toBitVec = BitVec.ofNat 64 k
  | .t1 => jt k 1
  | .j1 => jj k 1
  | .g1 => jg k 1
  | .t2 => jt k 2
  | .j2 => jj k 2
  | .g2 => jg k 2
  | .t3 => jt k 3
  | .j3 => jj k 3
  | .g3 => jg k 3
  | .t4 => jt k 4
  | .j4 => jj k 4
  | .g4 => jg k 4
  | .t5 => jt k 5
  | .j5 => jj k 5
  | .g5 => jg k 5
  | .dead => fun _ => False

/-- **A piece of the dispatcher** for the code `k`: inside a node's block. -/
def dpiece (k : Nat) (i : DN) : State → Prop :=
  BlkSt exe endPc RA C (dpc exe i) (dso i) (dJ k i) (dblk i)

/-- The stub's pieces: its prologue, the message's `adrp` and `add`, the
argument block. -/
inductive SP where
  | e | n1 | n1b | n2

/-- **A piece of stub `dx`**: inside its prologue, at the `adrp`/`add`,
inside its argument block. -/
def spiece (dx : DX) : SP → State → Prop
  | .e => BlkSt exe endPc RA C ((_root_.Executable.labels exe).label dx.stub.fn) Abort.oE (fun _ => True) Abort.b0
  | .n1 => Pt exe endPc RA C ((_root_.Executable.labels exe).label dx.stub.entry) Abort.oI (fun _ => True)
  | .n1b => Pt exe endPc RA C ((_root_.Executable.labels exe).label dx.stub.entry + 4) Abort.oI (fun _ => True)
  | .n2 => BlkSt exe endPc RA C ((_root_.Executable.labels exe).label dx.stub.entry + 4 + 4) Abort.oI
      (fun _ => True) dx.b1

/-- **The abort path to stub `dx`**: a piece of the dispatcher for its code,
or of the stub. -/
def AbIn (dx : DX) (s : State) : Prop :=
  (∃ i, dpiece exe endPc RA C (dxCode dx) i s) ∨ ∃ j, spiece exe endPc RA C dx j s

end Pieces

/-! ## The stubs' argument blocks -/

theorem b1_ne (dx : DX) : dx.b1 ≠ [] := by
  cases dx <;> simp [DX.b1, Abort.b1Overflow, Abort.b1Heap, Abort.b1Stack, Abort.b1Write, Abort.b1Threads]

theorem b1_ok (dx : DX) : Flow.okBlk (-48) 0 Abort.oI dx.b1 = true := by
  cases dx
  · exact Abort.b1Overflow_ok
  · exact Abort.b1Heap_ok
  · exact Abort.b1Stack_ok
  · exact Abort.b1Write_ok
  · exact Abort.b1Threads_ok

/-- **A stub's argument block** lands at the `write` call, `x0 = 2`,
`x8 = 64`. -/
theorem b1_run (dx : DX) (lab : Label → Int64) (pc : Int64) (σ : Flow.AS) :
    (Flow.arun lab dx.b1 ⟨pc, Abort.oI, σ⟩).pc = pc + 4 + 4 + 4 + 4 + 4 ∧
      SO.le Abort.oI (Flow.arun lab dx.b1 ⟨pc, Abort.oI, σ⟩).so = true ∧
      (Flow.arun lab dx.b1 ⟨pc, Abort.oI, σ⟩).σ.regs.X0 = 2 ∧
      (Flow.arun lab dx.b1 ⟨pc, Abort.oI, σ⟩).σ.regs.X8 = 64 := by
  cases dx
  · rw [DX.b1, Abort.b1Overflow_run]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [DX.b1, Abort.b1Heap_run]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [DX.b1, Abort.b1Stack_run]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [DX.b1, Abort.b1Write_run]; exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [DX.b1, Abort.b1Threads_run]; exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## The steps -/

section Steps

variable {A : Arch} {μ : Marks} {x : Kernel.KState} {tid : Nat}
  {exe : _root_.Executable} {endPc : Int64} {RA : Region} {C : MachineData → Prop}

/-- A step from a piece `D` stepping into `D ∨ E`, `D` inside `T` and `E`
landing in `T`. -/
private theorem into {D E T : State → Prop} (h : StepsTo A (Kernel.certSem abi A μ x tid) tid D E)
    (hD : ∀ s, D s → T s) (hE : ∀ s, E s → T s) :
    ∀ p q : Thread isaLSE2 × Memory, D p.1.st → ThreadStepC A (Kernel.certSem abi A μ x tid) tid p q →
      T q.1.st ∧ q.1.prom = p.1.prom := by
  intro p q hd hs
  obtain ⟨h1, h2⟩ := h p q hd hs
  exact ⟨h1.elim (hD _) (hE _), h2⟩

/-- A block's entry: a state at a nonempty block's pc, related at offsets
no weaker than `o` to a `J` state, under `C`. -/
private theorem ent {pc : Int64} {o o' : SO} {J : Flow.AS → Prop} {blk : List Directive} {s : State} {σ : Flow.AS}
    (hne : blk ≠ []) (he : s.exe = exe) (hn : s.endPc = endPc) (hd : s.decls = {}) (hpc : s.st.2 = pc)
    (hle : o.le o' = true) (hA : Flow.Abs RA o' s.st.1 σ) (hJ : J σ) (hC : C s.st.1) :
    BlkSt exe endPc RA C pc o J blk s :=
  pt_blkSt hne ⟨he, hn, hd, hpc, σ, hJ, hA.weaken hle, hC⟩

/-- The abort path. -/
local notation "AI" => AbIn exe endPc RA C

set_option maxHeartbeats 400000 in
/-- **A step from the abort path to stub `dx`** lands on it or in the stub's
`StubDt`, keeping the promises, given the dispatcher's and the stub's code
(any ghosts), the region's facts, `C` kept by writes inside the region
(`hC`) and the pieces off the transfer sites (`hns`). -/
theorem abIn_steps {dx : DX} {c0 c1 : Ctl} (hd : Abort.Disp.Code c0 exe endPc)
    (hs : Abort.Code dx.stub c1 dx.b1 exe endPc) (hR : RA.OK) (hal : RA.base.toNat % 16 = 0)
    (hlo : RA.lo ≤ -48) (hhi : 0 ≤ RA.hi) (hC : FStable RA C)
    (hns : ∀ s, AI dx s → Kernel.siteAt abi μ s = none) :
    StepsTo A (Kernel.certSem abi A μ x tid) tid (AI dx)
      (StubDt exe endPc (_root_.Executable.labels exe).label dx.stub) := by
  have hk := dxCode_le dx
  have hds : ∀ i s, dpiece exe endPc RA C (dxCode dx) i s → Kernel.siteAt abi μ s = none :=
    fun i s h => hns s (.inl ⟨i, h⟩)
  have hss : ∀ j s, spiece exe endPc RA C dx j s → Kernel.siteAt abi μ s = none :=
    fun j s h => hns s (.inr ⟨j, h⟩)
  have dinj : ∀ i s, dpiece exe endPc RA C (dxCode dx) i s →
      AI dx s ∨ StubDt exe endPc (_root_.Executable.labels exe).label dx.stub s := fun i s h => .inl (.inl ⟨i, h⟩)
  have sinj : ∀ j s, spiece exe endPc RA C dx j s →
      AI dx s ∨ StubDt exe endPc (_root_.Executable.labels exe).label dx.stub s := fun j s h => .inl (.inr ⟨j, h⟩)
  have hlo32 : RA.lo ≤ -32 := by omega
  rintro p q (⟨i, hD⟩ | ⟨j, hD⟩) hst
  · cases i
    case e =>
      refine into (blkSt_steps (pc := dpc exe .e) (J := dJ (dxCode dx) .e) Abort.Disp.d0_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.e s he hn) (hds .e)) (dinj .e) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, hJ, hpc, hA, hCs⟩
      rw [Abort.Disp.d0_run] at hpc hA
      refine dinj .t1 s (ent (by simp [dblk, Abort.Disp.t1]) he hn hdc (hpc.trans hd.hentry.symm) rfl hA
        ⟨?_, ?_⟩ hCs)
      · simpa [Spike.Lib.upd_apply, dJ] using hJ
      · cases dx <;> decide
    case t1 =>
      refine into (blkSt_steps (pc := dpc exe .t1) (J := dJ (dxCode dx) .t1) Abort.Disp.t1_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.t1 s he hn) (hds .t1)) (dinj .t1) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.t1_run] at hpc hA
      rw [hv, subs_z (j := 1) (by decide) hk] at hpc
      split at hpc
      · next h =>
        exact dinj .g1 s (ent (by simp [dblk, Abort.Disp.g1]) he hn hdc hpc rfl hA ⟨hv, of_decide_eq_true h⟩ hCs)
      · next h =>
        exact dinj .j1 s (ent (by simp [dblk, Abort.Disp.j1]) he hn hdc hpc rfl hA
          ⟨hv, by simp at h; omega⟩ hCs)
    case j1 =>
      refine into (blkSt_steps (pc := dpc exe .j1) (J := dJ (dxCode dx) .j1) Abort.Disp.j1_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.j1 s he hn) (hds .j1)) (dinj .j1) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.j1_run] at hpc hA
      exact dinj .t2 s (ent (by simp [dblk, Abort.Disp.t2]) he hn hdc hpc rfl hA ⟨hv, by omega⟩ hCs)
    case g1 =>
      refine into (blkSt_steps (pc := dpc exe .g1) (J := dJ (dxCode dx) .g1) Abort.Disp.g1_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.g1 s he hn) (hds .g1)) (dinj .g1) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨-, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.g1_run] at hpc hA
      have hx : dx = .overflow := by cases dx <;> simp [dxCode] at hj ⊢
      subst hx
      exact sinj .e s (ent (by simp [Abort.b0]) he hn hdc hpc rfl hA trivial hCs)
    case t2 =>
      refine into (blkSt_steps (pc := dpc exe .t2) (J := dJ (dxCode dx) .t2) Abort.Disp.t2_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.t2 s he hn) (hds .t2)) (dinj .t2) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.t2_run] at hpc hA
      rw [hv, subs_z (j := 2) (by decide) hk] at hpc
      split at hpc
      · next h =>
        exact dinj .g2 s (ent (by simp [dblk, Abort.Disp.g2]) he hn hdc hpc rfl hA ⟨hv, of_decide_eq_true h⟩ hCs)
      · next h =>
        exact dinj .j2 s (ent (by simp [dblk, Abort.Disp.j2]) he hn hdc hpc rfl hA
          ⟨hv, by simp at h; omega⟩ hCs)
    case j2 =>
      refine into (blkSt_steps (pc := dpc exe .j2) (J := dJ (dxCode dx) .j2) Abort.Disp.j2_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.j2 s he hn) (hds .j2)) (dinj .j2) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.j2_run] at hpc hA
      exact dinj .t3 s (ent (by simp [dblk, Abort.Disp.t3]) he hn hdc hpc rfl hA ⟨hv, by omega⟩ hCs)
    case g2 =>
      refine into (blkSt_steps (pc := dpc exe .g2) (J := dJ (dxCode dx) .g2) Abort.Disp.g2_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.g2 s he hn) (hds .g2)) (dinj .g2) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨-, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.g2_run] at hpc hA
      have hx : dx = .heap := by cases dx <;> simp [dxCode] at hj ⊢
      subst hx
      exact sinj .e s (ent (by simp [Abort.b0]) he hn hdc hpc rfl hA trivial hCs)
    case t3 =>
      refine into (blkSt_steps (pc := dpc exe .t3) (J := dJ (dxCode dx) .t3) Abort.Disp.t3_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.t3 s he hn) (hds .t3)) (dinj .t3) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.t3_run] at hpc hA
      rw [hv, subs_z (j := 3) (by decide) hk] at hpc
      split at hpc
      · next h =>
        exact dinj .g3 s (ent (by simp [dblk, Abort.Disp.g3]) he hn hdc hpc rfl hA ⟨hv, of_decide_eq_true h⟩ hCs)
      · next h =>
        exact dinj .j3 s (ent (by simp [dblk, Abort.Disp.j3]) he hn hdc hpc rfl hA
          ⟨hv, by simp at h; omega⟩ hCs)
    case j3 =>
      refine into (blkSt_steps (pc := dpc exe .j3) (J := dJ (dxCode dx) .j3) Abort.Disp.j3_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.j3 s he hn) (hds .j3)) (dinj .j3) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.j3_run] at hpc hA
      exact dinj .t4 s (ent (by simp [dblk, Abort.Disp.t4]) he hn hdc hpc rfl hA ⟨hv, by omega⟩ hCs)
    case g3 =>
      refine into (blkSt_steps (pc := dpc exe .g3) (J := dJ (dxCode dx) .g3) Abort.Disp.g3_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.g3 s he hn) (hds .g3)) (dinj .g3) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨-, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.g3_run] at hpc hA
      have hx : dx = .stack := by cases dx <;> simp [dxCode] at hj ⊢
      subst hx
      exact sinj .e s (ent (by simp [Abort.b0]) he hn hdc hpc rfl hA trivial hCs)
    case t4 =>
      refine into (blkSt_steps (pc := dpc exe .t4) (J := dJ (dxCode dx) .t4) Abort.Disp.t4_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.t4 s he hn) (hds .t4)) (dinj .t4) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.t4_run] at hpc hA
      rw [hv, subs_z (j := 4) (by decide) hk] at hpc
      split at hpc
      · next h =>
        exact dinj .g4 s (ent (by simp [dblk, Abort.Disp.g4]) he hn hdc hpc rfl hA ⟨hv, of_decide_eq_true h⟩ hCs)
      · next h =>
        exact dinj .j4 s (ent (by simp [dblk, Abort.Disp.j4]) he hn hdc hpc rfl hA
          ⟨hv, by simp at h; omega⟩ hCs)
    case j4 =>
      refine into (blkSt_steps (pc := dpc exe .j4) (J := dJ (dxCode dx) .j4) Abort.Disp.j4_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.j4 s he hn) (hds .j4)) (dinj .j4) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.j4_run] at hpc hA
      exact dinj .t5 s (ent (by simp [dblk, Abort.Disp.t5]) he hn hdc hpc rfl hA ⟨hv, by omega⟩ hCs)
    case g4 =>
      refine into (blkSt_steps (pc := dpc exe .g4) (J := dJ (dxCode dx) .g4) Abort.Disp.g4_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.g4 s he hn) (hds .g4)) (dinj .g4) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨-, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.g4_run] at hpc hA
      have hx : dx = .write := by cases dx <;> simp [dxCode] at hj ⊢
      subst hx
      exact sinj .e s (ent (by simp [Abort.b0]) he hn hdc hpc rfl hA trivial hCs)
    case t5 =>
      refine into (blkSt_steps (pc := dpc exe .t5) (J := dJ (dxCode dx) .t5) Abort.Disp.t5_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.t5 s he hn) (hds .t5)) (dinj .t5) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨hv, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.t5_run] at hpc hA
      rw [hv, subs_z (j := 5) (by decide) hk] at hpc
      split at hpc
      · next h =>
        exact dinj .g5 s (ent (by simp [dblk, Abort.Disp.g5]) he hn hdc hpc rfl hA ⟨hv, of_decide_eq_true h⟩ hCs)
      · next h =>
        exact dinj .j5 s (ent (by simp [dblk, Abort.Disp.j5]) he hn hdc hpc rfl hA
          ⟨hv, by simp at h; omega⟩ hCs)
    case j5 =>
      obtain ⟨-, -, -, σ0, ⟨-, hj⟩, -⟩ := hD
      omega
    case g5 =>
      refine into (blkSt_steps (pc := dpc exe .g5) (J := dJ (dxCode dx) .g5) Abort.Disp.g5_ok hC hR hal hlo32 hhi
        (fun s he hn => hd.g5 s he hn) (hds .g5)) (dinj .g5) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, ⟨-, hj⟩, hpc, hA, hCs⟩
      rw [Abort.Disp.g5_run] at hpc hA
      have hx : dx = .threads := by cases dx <;> simp [dxCode] at hj ⊢
      subst hx
      exact sinj .e s (ent (by simp [Abort.b0]) he hn hdc hpc rfl hA trivial hCs)
    case dead =>
      obtain ⟨-, -, -, σ0, h, -⟩ := hD
      exact h.elim
  · cases j
    case e =>
      refine into (blkSt_steps (pc := (_root_.Executable.labels exe).label dx.stub.fn) (J := fun _ => True)
        Abort.b0_ok hC hR hal hlo hhi (fun s he hn => hs.e s he hn) (hss .e)) (sinj .e) ?_ p q hD hst
      rintro s ⟨he, hn, hdc, σ0, -, hpc, hA, hCs⟩
      rw [Abort.b0_run] at hpc hA
      exact sinj .n1 s ⟨he, hn, hdc, hpc.trans hs.hentry.symm, _, trivial, hA.weaken rfl, hCs⟩
    case n1 =>
      refine into (siPt_steps (pc := (_root_.Executable.labels exe).label dx.stub.entry) (o := Abort.oI)
        (J := fun _ => True) (si := .adrp .X9 dx.stub.msg) hC (fun s he hn => hs.n1 s he hn) (hss .n1))
        (sinj .n1) ?_ p q hD hst
      intro s h
      exact sinj .n1b s (pt_mono h (fun _ _ => trivial) rfl)
    case n1b =>
      refine into (siPt_steps (pc := (_root_.Executable.labels exe).label dx.stub.entry + 4) (o := Abort.oI)
        (J := fun _ => True) (si := .addLo12 .X9 .X9 dx.stub.msg) hC (fun s he hn => hs.n1b s he hn) (hss .n1b))
        (sinj .n1b) ?_ p q hD hst
      intro s h
      exact sinj .n2 s (pt_blkSt (b1_ne dx) (pt_mono h (fun _ _ => trivial) rfl))
    case n2 =>
      refine into (blkSt_steps (pc := (_root_.Executable.labels exe).label dx.stub.entry + 4 + 4)
        (J := fun _ => True) (b1_ok dx) hC hR hal hlo hhi (fun s he hn => hs.n2 s he hn) (hss .n2))
        (sinj .n2) ?_ p q hD hst
      intro s h
      exact .inr (stubDt_of_pt hal hlo hhi (blkEnd_pt (fun σ0 _ => b1_run dx _ _ σ0) h))

end Steps

/-! ## Entry from `print`'s abort call -/

/-- `scc_rt_abort`'s region at `print`'s abort call: the callee's at
`print`'s `sp` (`-48`), holding the stub's 48-byte frame below its base. -/
abbrev abR (Rp : Region) : Region := Rp.callee (-48) (-48) 0

/-- `scc_rt_abort`'s region is fine, given room below `print`'s frame. -/
theorem abR_ok {Rp : Region} (hR : Rp.OK) (hlo : Rp.lo ≤ -96) (hhi : -48 < Rp.hi) : (abR Rp).OK :=
  Region.callee_ok hR (by omega) (by decide) hhi (by omega)

/-- **`print`'s abort call lands on the abort path**: `b14`'s end in
`print`'s frame (`x0 = 4`, the `hfail` of `printIn_steps`) is the
dispatcher's entry on the path to the `write` stub, in `scc_rt_abort`'s
region, under `pt_enter`'s frame condition (`C`, the cells outside the
region kept, the caller's state); `c` is any control. -/
theorem abIn_of_fail {exe : _root_.Executable} {endPc : Int64} {Rp : Region} {C : MachineData → Prop}
    {x29 ra : BitVec 64} {s : State} (hlo : Rp.lo ≤ -96) (hhi : -48 < Rp.hi) (c : Ctl)
    (h : BlkEnd exe endPc Rp C (ppc exe .fail) Print.oI (PJ x29 ra) Print.b14 s) :
    ∃ m0 σC, AbIn exe endPc (abR Rp) (fun m => C m ∧ CKept Rp (-48) (-48) 0 m0 m ∧ Flow.Abs Rp ⟨-48, []⟩ m0 σC)
      .write s := by
  have hp := blkEnd_pt (pc' := (_root_.Executable.labels exe).label "scc_rt_abort") (o' := ⟨-48, []⟩)
    (J' := fun σ => σ.regs.X0.toBitVec = BitVec.ofNat 64 4)
    (fun σ0 _ => by rw [Print.b14_run]; exact ⟨rfl, rfl, rfl⟩) h
  obtain ⟨m0, σC, hq⟩ := pt_enter (lo' := -48) (hi' := 0) (by show Rp.lo ≤ -48 + -48; omega)
    (by show (-48 : Int) < Rp.hi; omega) (Int.le_refl 0) (by decide) c hp
  refine ⟨m0, σC, .inl ⟨.e, pt_blkSt (by simp [dblk, Abort.Disp.d0]) (pt_mono hq ?_ rfl)⟩⟩
  rintro σ ⟨rfl, hX⟩
  exact hX

-- No axioms beyond Lean's.

/--
info: 'Spike.Lib.A64.Rt.abIn_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms abIn_steps

/--
info: 'Spike.Lib.A64.Rt.abIn_of_fail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms abIn_of_fail

end Spike.Lib.A64.Rt

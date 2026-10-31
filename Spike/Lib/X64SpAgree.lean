/-
**The stack pointer stays in a band of the region across a block**
(x86-64; the twin of `Spike/Lib/A64SpAgree.lean`): at every state of a
covered block (`okBlk`) and at each of its successors, `%rsp` is the
region's address at an offset in `[slo, shi]`, given the block's static
`%rsp` offsets lie in that band (`hso`, decided on the block). A global
owned-words map that picks the instance by the stack `%rsp` is in agrees
with an instance on such a block (`StSucc`).

- `SpAt R slo shi s`: `%rsp` is `R.addr k` for some `k ∈ [slo, shi]`.
- `spAt_take`: the take keeps `%rsp`.
- `AI.not_syscall`: a covered instruction is not a `syscall`.
- `BlkW.spAt`: a block's states and their successors in the band.
- `BlkW.leaf`: any predicate of a block's states and their successors from
  the abstract run (its `Abs` at each pc and next pc).

Where x86-64 differs from AArch64: blocks are sized cells (the `k`-th pc is
`n.pc + cellOff blk k`, A64's `n.pc + 4·k`); `exec_ai` needs no alignment of
the region's base (no `hal`).
-/
import Spike.Lib.X64OwnCongr

namespace Spike.Lib.X64ConsumerA

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64

/-- **`%rsp` is in the band `[slo, shi]` of the region `R`.** -/
def SpAt (R : Region) (slo shi : Int) (s : State) : Prop :=
  ∃ k, slo ≤ k ∧ k ≤ shi ∧ s.st.1.regs.rsp.toBitVec = R.addr k

/-- **The take keeps `%rsp`.** -/
theorem spAt_take {R : Region} {slo shi : Int} {s : State} (m : _root_.Mem 64) (h : SpAt R slo shi s) :
    SpAt R slo shi (abi.skip (abi.setDmem s m)) := h

/-- **A covered instruction is not a `syscall`.** -/
theorem AI.not_syscall {a : AI} (hreg : ∀ w op, a = .reg w op → RegOnly op = true) :
    ∀ w w', a.toDir ≠ .instr (.regular w w' .syscall) := by
  intro w w' h
  cases a <;> simp only [AI.toDir, op64, Directive.instr.injEq, Instr.regular.injEq] at h <;>
    obtain ⟨rfl, rfl, h⟩ := h <;> cases eq_of_heq h
  exact absurd (hreg _ _ rfl) (by simp [RegOnly])

/-- The register file's `%rsp` at static offsets `o` is the region's
address at `o.sp`. -/
theorem rsp_of_abs {R : Region} {o : SO} {m : MachineData} {σ : AS} (hA : Abs R o m σ) :
    m.regs.rsp.toBitVec = R.addr o.sp := by
  rw [hA.regs]; exact hA.so .rsp _ o.get_rsp

/-- **A predicate of a block's states and of their successors from the
abstract run**: `P` of every machine state the run's abstract state
represents at each pc of the block (`hQ`) and at each next pc (`hP`), the
block off the take site (`hns`). The successors are the instruction's
single leaf (`exec_ai`). -/
theorem BlkW.leaf {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {P : State → Prop}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → P s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) → P s) :
    BlkW (fun s _ => P s ∧ ∀ s', StSucc μ s s' → P s') (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨⟨hQ σ c hJ k hk _ m hA' he hn rfl, ?_⟩, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s he hn).cell (j := k) (d := a.toDir) (z := blk[k].2) (by rw [hd, ← hdir]) rfl rfl rfl
  have hs : abi.atSys { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } = false :=
    atSyscall_false_of_cellAt hc (AI.not_syscall hreg)
  obtain ⟨m', hex, hA2, -⟩ := exec_ai haok hR hlo hhi hc hreg hA'
  have hP' := hP σ c hJ k hk
  rw [arun_take_succ _ hk] at hP'
  have hpc0 : (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc =
      n.pc + Int64.ofNat (cellOff blk k) := arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk
  simp only [dstep, hca, hpc0] at hP'
  have hl : labelAddr { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } =
      (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [he]
  rw [hl] at hex
  intro s' hs'
  rcases hs' with ⟨-, tree, htr, hl'⟩ | ⟨hsy, -⟩ | ⟨a', ha', hpc, -, -⟩
  · rw [hex] at htr; cases htr; cases hl'
    exact hP' _ m' hA2 he hn rfl
  · rw [hs] at hsy; cases hsy
  · exact absurd hpc (hns a' ha' k hk)

/-- **A block's states and their successors keep `%rsp` in the band**: the
block covered (`okBlk`) in `R`, and every static `%rsp` offset its run
reaches in `[slo, shi]` (`hso`). -/
theorem BlkW.spAt {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List (Directive × Nat)} {lo hi slo shi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hso : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      slo ≤ (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ≤ shi) :
    BlkW (fun s _ => SpAt R slo shi s ∧ ∀ s', StSucc μ s s' → SpAt R slo shi s') (fun _ _ => False)
      exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  have h0 := hso σ c hJ k (Nat.le_of_lt hk)
  refine ⟨⟨_, h0.1, h0.2, rsp_of_abs hA'⟩, ?_⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s he hn).cell (j := k) (d := a.toDir) (z := blk[k].2) (by rw [hd, ← hdir]) rfl rfl rfl
  have hs : abi.atSys { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } = false :=
    atSyscall_false_of_cellAt hc (AI.not_syscall hreg)
  obtain ⟨m', hex, hA2, -⟩ := exec_ai haok hR hlo hhi hc hreg hA'
  have h1 := hso σ c hJ (k + 1) hk
  rw [arun_take_succ _ hk] at h1
  simp only [dstep, hca] at h1
  intro s' hs'
  rcases hs' with ⟨-, tree, htr, hl⟩ | ⟨hsy, -⟩ | ⟨a', -, -, m'', rfl⟩
  · rw [hex] at htr; cases htr; cases hl
    exact ⟨_, h1.1, h1.2, rsp_of_abs hA2⟩
  · rw [hs] at hsy; cases hsy
  · exact spAt_take m'' ⟨_, h0.1, h0.2, rsp_of_abs hA'⟩

end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.spAt_take' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.spAt_take

/-- info: 'Spike.Lib.X64ConsumerA.AI.not_syscall' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.AI.not_syscall

/-- info: 'Spike.Lib.X64ConsumerA.rsp_of_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.rsp_of_abs

/-- info: 'Spike.Lib.X64ConsumerA.BlkW.leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.BlkW.leaf

/-- info: 'Spike.Lib.X64ConsumerA.BlkW.spAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.BlkW.spAt

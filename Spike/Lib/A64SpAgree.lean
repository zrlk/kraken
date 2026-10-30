/-
**The stack pointer stays in a band of the region across a block**
(AArch64): at every state of a covered block (`okBlk`) and at each of its
successors, `sp` is the region's address at an offset in `[slo, shi]`, given
the block's static `sp` offsets lie in that band (`hso`, decided on the
block). A global owned-words map that picks the instance by the stack `sp`
is in agrees with an instance on such a block (`StSucc`).

- `SpAt R slo shi s`: `sp` is `R.addr k` for some `k ∈ [slo, shi]`.
- `spAt_take`: the take keeps `sp`.
- `BlkW.spAt`: a block's states and their successors in the band.
- `BlkW.leaf`: any predicate of a block's states and their successors from
  the abstract run (its `Abs` at each pc and next pc).
-/
import Spike.Lib.A64OwnCongr
import Spike.Lib.A64SegInst

namespace Spike.Lib.A64ConsumerA

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow

/-- **`sp` is in the band `[slo, shi]` of the region `R`.** -/
def SpAt (R : Region) (slo shi : Int) (s : State) : Prop :=
  ∃ k, slo ≤ k ∧ k ≤ shi ∧ s.st.1.regs.SP.toBitVec = R.addr k

/-- **The take keeps `sp`.** -/
theorem spAt_take {R : Region} {slo shi : Int} {s : State} (m : _root_.Mem 64) (h : SpAt R slo shi s) :
    SpAt R slo shi (abi.skip (abi.setDmem s m)) := h

/-- **A block's states and their successors keep `sp` in the band**: the
block covered (`okBlk`) in `R`, and every static `sp` offset its run
reaches in `[slo, shi]` (`hso`). -/
theorem BlkW.spAt {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List Directive} {lo hi slo shi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi)
    (hso : ∀ σ c, n.J σ c → ∀ k ≤ blk.length,
      slo ≤ (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ∧
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp ≤ shi) :
    BlkW (fun s _ => SpAt R slo shi s ∧ ∀ s', StSucc μ s s' → SpAt R slo shi s') (fun _ _ => False)
      exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  have hsp : ∀ {o : SO} {m' : MachineData} {σ' : AS}, Abs R o m' σ' → m'.regs.SP.toBitVec = R.addr o.sp :=
    fun hA => by rw [hA.regs]; exact hA.so .SP _ rfl
  have h0 := hso σ c hJ k (Nat.le_of_lt hk)
  refine ⟨⟨_, h0.1, h0.2, hsp hA'⟩, ?_⟩
  obtain ⟨a, hca, haok, -⟩ := okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hs : abi.atSys { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = false :=
    atSvc_false_of_cellAt hc (AI.not_svc hreg)
  obtain ⟨m', hex, hA2, -⟩ := exec_ai haok hR hal hlo hhi hc hreg hA'
  have h1 := hso σ c hJ (k + 1) hk
  rw [arun_take_succ _ hk] at h1
  simp only [dstep, hca] at h1
  intro s' hs'
  rcases hs' with ⟨-, tree, htr, hl⟩ | ⟨hsy, -⟩ | ⟨a', -, -, m'', rfl⟩
  · rw [hex] at htr; cases htr; cases hl
    exact ⟨_, h1.1, h1.2, hsp hA2⟩
  · rw [hs] at hsy; cases hsy
  · exact spAt_take m'' ⟨_, h0.1, h0.2, hsp hA'⟩

/-- **A predicate of a block's states and of their successors from the
abstract run**: `P` of every machine state the run's abstract state
represents at each pc of the block (`hQ`) and at each next pc (`hP`), the
block off the take site (`hns`). The successors are the instruction's
single leaf (`exec_ai`). -/
theorem BlkW.leaf {μ : Marks} {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {n : ND} {blk : List Directive} {lo hi : Int} {P : State → Prop}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo)
    (hhi : hi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (4 * k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (4 * k)) → P s)
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
  have hc : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hs : abi.atSys { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = false :=
    atSvc_false_of_cellAt hc (AI.not_svc hreg)
  obtain ⟨m', hex, hA2, -⟩ := exec_ai haok hR hal hlo hhi hc hreg hA'
  have hP' := hP σ c hJ k hk
  rw [arun_take_succ _ hk] at hP'
  have hpc0 : (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).pc =
      n.pc + Int64.ofNat (4 * k) := arun_pc _ (am := ⟨n.pc, n.o, σ⟩) hok hk
  simp only [dstep, hca, hpc0] at hP'
  have hl : labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [he]
  rw [hl] at hex
  intro s' hs'
  rcases hs' with ⟨-, tree, htr, hl'⟩ | ⟨hsy, -⟩ | ⟨a', ha', hpc, -, -⟩
  · rw [hex] at htr; cases htr; cases hl'
    exact hP' _ m' hA2 he hn rfl
  · rw [hs] at hsy; cases hsy
  · exact absurd hpc (hns a' ha' k hk)

/-- info: 'Spike.Lib.A64ConsumerA.BlkW.spAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerA.BlkW.spAt

/-- info: 'Spike.Lib.A64ConsumerA.BlkW.leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64ConsumerA.BlkW.leaf

end Spike.Lib.A64ConsumerA

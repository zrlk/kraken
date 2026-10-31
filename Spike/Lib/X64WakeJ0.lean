/-
**`wc_main`'s entry facts from `scc_rt_main`'s entry invariant** (x86-64):
the caller premises of `X64WakeWcMain.wake_wc_entry_segW` at
`J0 := WakeM.wJ0 (WakeM.wNC lab Jm).J σC`, the region `WakeM.wR R D` and
the frame condition `WakeM.wF R D F0 m0 σC`, from facts at `scc_rt_main`'s
entry invariant `Jm` and its frame condition `F0`. The call keeps the
registers (`enter`) and the source control; `scc_rt_main`'s prologue and
call lower `%rsp` by `48` (`WakeM.wJd`: `8 + 32 + 8`).

- `wJ0_inv`: a `J0` state is a `Jm` state's, `%rsp` lowered by `48`, the
  thread pointer kept, the control the same;
- `hJ0tp_J0` (`wJ0_tp`), `hlim_J0`, `hq_J0`: the premises on `J0`;
- `hj_J0`: the box's control is an entry's;
- `hmem_wF`, `hcell_wF`: the premises on the frame condition, from `F0`'s;
- `wake_wc_entry_segJm`: `wake_wc_entry_segW` at `J0`, `wR`, `wF` with
  these premises at `Jm`, `F0`.

x86-64 twin of `Spike/Lib/A64WakeJ0.lean` (same names, namespace
`Spike.Lib.X64.Flow.WakeWc`).

**Unlike AArch64**: the thread pointer is `fsBase` (A64 `TPIDR_EL0`); the
limit word is at `fsBase + 8` (A64 `tcbA σ.regs 8`) and its bound is
`Jm`'s `%rsp - 120` (`wc_main`'s `%rsp - 8 - 64`, the entry `48` below;
A64 `sp - 128`, `sp - 80`); `wake_wc_entry_segJm` has no 16-alignment
premise and asks `8 ≤ (wR R D).hi` (A64 `0 ≤`), its box landing on
`(wR R D).fp (-8)` (`X64WakeWcMain.wake_wc_entry_segW`'s); the code is
`Lays exe SccCode.wakeCells`.
-/
import Spike.Lib.X64WakeWcMain

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.WakeM (wJ wNC wJ0 wR wF)
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.WakeTP (tpG)

variable {lab : Label → Int64} {Jm : AS → Ctl → Prop} {σC : AS}

/-- **A `J0` state is a `Jm` state's**: the registers but `%rsp` (`48`
lower), the control the same. -/
theorem wJ0_inv {σ : AS} {c : Ctl} (h : wJ0 (wNC lab Jm).J σC σ c) :
    ∃ σe, Jm σe c ∧ σ.regs.rsp.toBitVec = σe.regs.rsp.toBitVec - 8#64 - (32 : Int64).toBitVec - 8#64 ∧
      σ.regs.fsBase = σe.regs.fsBase := by
  obtain ⟨rfl, ⟨σe, hJe, -, -, -, h4, h5⟩, -, -, -⟩ := h
  exact ⟨σe, hJe, h4, h5⟩

/-- **`hJ0tp`** from `Jm`'s thread pointer. -/
theorem hJ0tp_J0 {t : UInt64} (hJ : ∀ σ c, Jm σ c → σ.regs.fsBase = t) :
    ∀ σ c, wJ0 (wNC lab Jm).J σC σ c → σ.regs.fsBase = t :=
  fun _ _ h => wJ0_tp hJ h

/-- **`hlim`**: the limit word at `Jm`'s thread pointer `+ 8`, bounded by
`Jm`'s `%rsp - 120` (`wc_main`'s `%rsp - 8 - 64`), at `F0`. -/
theorem hlim_J0 {ms : MemSide isa} {F0 : MachineData → Prop} {R : Region} {D : Int} {m0 : MachineData}
    (h : ∀ σ c, Jm σ c →
      LimOk ms F0 (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 120#64)) :
    ∀ σ c, wJ0 (wNC lab Jm).J σC σ c →
      LimOk ms (wF R D F0 m0 σC) (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
        (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec) := by
  intro σ c hJ
  obtain ⟨σe, hJe, hsp, htp⟩ := wJ0_inv hJ
  have hs : σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec = σe.regs.rsp.toBitVec - 120#64 := by
    rw [hsp]; simp only [BitVec.sub_sub]; rfl
  rw [htp, hs]
  exact (h σe c hJe).mono fun _ hm => hm.1

/-- **`hq`** from `Jm`'s control (the call keeps it). -/
theorem hq_J0 {P : Ctl → Prop} (h : ∀ σ c, Jm σ c → P c) : ∀ σ c, wJ0 (wNC lab Jm).J σC σ c → P c :=
  fun _ c hJ => let ⟨σe, hJe, _⟩ := wJ0_inv hJ; h σe c hJe

/-- **The box's control is an entry's**: a `wJ0` state's control is some
`Jm` state's (the call keeps it). -/
theorem hj_J0 {c : Ctl} (h : ∃ σ, wJ0 (wNC lab Jm).J σC σ c) : ∃ σ, Jm σ c :=
  let ⟨_, hJ⟩ := h; let ⟨σe, hJe, _⟩ := wJ0_inv hJ; ⟨σe, hJe⟩

/-- **`hmem`** from `F0`'s. -/
theorem hmem_wF {ms : MemSide isa} {F0 : MachineData → Prop} {R : Region} {D : Int} {m0 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none) :
    ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, wF R D F0 m0 σC m → Mem.loadInt m.dmem a 8 = none :=
  fun q hq a ha m hm => h q hq a ha m hm.1

/-- **`hcell`** from `F0`'s. -/
theorem hcell_wF {ms : MemSide isa} {F0 : MachineData → Prop} {R : Region} {D : Int} {m0 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : AGB ms ll, (∃ σ, Jm σ q.1.c0) → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none) :
    ∀ q : AGB ms ll, (∃ σ, wJ0 (wNC lab Jm).J σC σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, wF R D F0 m0 σC m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none :=
  fun q hj o h1 h2 => ⟨(h q (hj_J0 hj) o h1 h2).1, fun m hm => (h q (hj_J0 hj) o h1 h2).2 m hm.1⟩

/-! ## `wake_wc_entry_segW` at `scc_rt_main`'s call -/

/-- **`wc_main` from its entry at `scc_rt_main`'s call**:
`wake_wc_entry_segW` at `J0 := wJ0 (wNC lab Jm).J σC`, the region `wR R D`
and the frame condition `wF R D F0 m0 σC`, its caller premises from `Jm`'s
(the thread pointer `t`, the limit word bounded by `%rsp - 120`, the box's
call at the control) and `F0`'s (`hmem0`, `hcell0`). The other premises
are `wake_wc_entry_segW`'s. -/
theorem wake_wc_entry_segJm {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {D : Int} {F0 : MachineData → Prop} {m0 : MachineData}
    {t : UInt64} (hK : ms.K = some Scc.Sem.X64.abi)
    {W : Frag isa} {K : State → State → Prop}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hF : FStable (wR R D) (wF R D F0 m0 σC)) (hR : (wR R D).OK)
    (hlo : (wR R D).lo ≤ -240) (hhi : 8 ≤ (wR R D).hi)
    (htp : ∀ σ c, Jm σ c → σ.regs.fsBase = t)
    (hWp : WcPreW (NoSetFsW (tpG t W) K) K exe endPc (wR R D) (wF R D F0 m0 σC) (tpXa ms t)
      (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC) (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC))
    (hWs : WcSp0W (NoSetFsW (tpG t W) K) K exe endPc (wR R D) (wF R D F0 m0 σC) (tpXa ms t)
      (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC))
    (hlim : ∀ σ c, Jm σ c →
      LimOk ms F0 (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec) (σ.regs.rsp.toBitVec - 120#64))
    (hq : ∀ σ c, Jm σ c → ∃ q : Call, q.OKB ms (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 256#64 ∧ q.k = 1#64 ∧ q.u ms = 2#64)
    (hmem0 : ∀ q : Call, q.OKB ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none)
    (hbox : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jm σ q.1.c0) → BoxW lbl q.1)
    (hcell0 : ∀ q : AGB ms (_root_.Executable.labels exe).label, (∃ σ, Jm σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none)
    (hxa : ∀ l A s c, lbl l = none → At exe endPc ((wR R D).fp (-8)) (wF R D F0 m0 σC)
      (bX ms (_root_.Executable.labels exe).label (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC) l A) s c →
      TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc (wR R D) (wF R D F0 m0 σC)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩,
          wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC⟩)
      (fun s c => At exe endPc (wR R D) (wF R D F0 m0 σC)
        (wX ms (_root_.Executable.labels exe).label (wR R D)
          (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC) .abort) s c ∧ TP t s) :=
  wake_wc_entry_segW hK hp hend hF hR hlo hhi (hJ0tp_J0 htp) hWp hWs (hlim_J0 hlim) (hq_J0 hq)
    (hmem_wF hmem0) (fun q h => hbox q (hj_J0 h)) (hcell_wF hcell0) hxa

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wJ0_inv' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wJ0_inv

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hJ0tp_J0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hJ0tp_J0

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hlim_J0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hlim_J0

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hq_J0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hq_J0

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hj_J0' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hj_J0

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hmem_wF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hmem_wF

/-- info: 'Spike.Lib.X64.Flow.WakeWc.hcell_wF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.hcell_wF

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wake_wc_entry_segJm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wake_wc_entry_segJm

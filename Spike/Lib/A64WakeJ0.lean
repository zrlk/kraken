/-
**`wc_main`'s entry facts from `scc_rt_main`'s entry invariant** (AArch64): the caller premises of `A64WakeWcMain.wake_wc_entry_segW` at
`J0 := WakeM.wJ0 (WakeM.wNC lab Jm).J σC`, the region `WakeM.wR R D` and
the frame condition `WakeM.wF R D F0 m0 σC`, from facts at `scc_rt_main`'s
entry invariant `Jm` and its frame condition `F0`. The call keeps the
registers (`enter`) and the source control; `scc_rt_main`'s prologue
lowers `sp` by `48` (`WakeM.wJ`).

- `wJ0_inv`: a `J0` state is a `Jm` state's, `sp` lowered by `48`, the
  thread pointer kept, the control the same;
- `hJ0tp_J0` (`wJ0_tp`), `hlim_J0`, `hq_J0`: the premises on `J0`;
- `hmem_wF`, `hcell_wF`: the premises on the frame condition, from `F0`'s;
- `wake_wc_entry_segJm`: `wake_wc_entry_segW` at `J0`, `wR`, `wF` with
  these premises at `Jm`, `F0`.
-/
import Spike.Lib.A64WakeWcMain

namespace Spike.Lib.A64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (LimOk)
open Spike.Lib.A64.Alloc (Call)
open Spike.Lib.A64.Flow.WakeM (wJ wNC wJ0 wR wF)

variable {lab : Label → Int64} {Jm : AS → Ctl → Prop} {σC : AS}

/-- **A `J0` state is a `Jm` state's**: the registers but `sp` (`48`
lower), the control the same. -/
theorem wJ0_inv {σ : AS} {c : Ctl} (h : wJ0 (wNC lab Jm).J σC σ c) :
    ∃ σe, Jm σe c ∧ σ.regs.SP.toBitVec = σe.regs.SP.toBitVec - (48 : Int64).toBitVec ∧
      σ.regs.TPIDR_EL0 = σe.regs.TPIDR_EL0 := by
  obtain ⟨rfl, ⟨σe, hJe, -, -, -, h4, h5⟩, -, -⟩ := h
  exact ⟨σe, hJe, h4, h5⟩

/-- **`hJ0tp`** from `Jm`'s thread pointer. -/
theorem hJ0tp_J0 {t : UInt64} (hJ : ∀ σ c, Jm σ c → σ.regs.TPIDR_EL0 = t) :
    ∀ σ c, wJ0 (wNC lab Jm).J σC σ c → σ.regs.TPIDR_EL0 = t :=
  fun _ _ h => wJ0_tp hJ h

/-- **`hlim`**: the limit word at `Jm`'s thread pointer, bounded by `Jm`'s
`sp - 128` (`wc_main`'s `sp - 80` below `scc_rt_main`'s frame), at `F0`. -/
theorem hlim_J0 {ms : MemSide isaLSE2} {F0 : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {D : Int} {m0 : MachineData}
    (h : ∀ σ c, Jm σ c → LimOk ms F0 exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (128 : Int64).toBitVec)) :
    ∀ σ c, wJ0 (wNC lab Jm).J σC σ c →
      LimOk ms (wF R D F0 m0 σC) exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (80 : Int64).toBitVec) := by
  intro σ c hJ
  obtain ⟨σe, hJe, hsp, htp⟩ := wJ0_inv hJ
  have ht : tcbA σ.regs 8 = tcbA σe.regs 8 := by simp only [tcbA, htp]
  have hs : σ.regs.SP.toBitVec - (80 : Int64).toBitVec = σe.regs.SP.toBitVec - (128 : Int64).toBitVec := by
    rw [hsp, BitVec.sub_sub]; rfl
  rw [ht, hs]
  exact (h σe c hJe).mono fun _ hm => hm.1

/-- **`hq`** from `Jm`'s control (the call keeps it). -/
theorem hq_J0 {P : Ctl → Prop} (h : ∀ σ c, Jm σ c → P c) : ∀ σ c, wJ0 (wNC lab Jm).J σC σ c → P c :=
  fun _ c hJ => let ⟨σe, hJe, _⟩ := wJ0_inv hJ; h σe c hJe

/-- **The box's control is an entry's**: a `wJ0` state's control is some
`Jm` state's (the call keeps it). -/
theorem hj_J0 {c : Ctl} (h : ∃ σ, wJ0 (wNC lab Jm).J σC σ c) : ∃ σ, Jm σ c :=
  let ⟨_, hJ⟩ := h; let ⟨σe, hJe, _⟩ := wJ0_inv hJ; ⟨σe, hJe⟩

/-- **`hmem`** from `F0`'s. -/
theorem hmem_wF {ms : MemSide isaLSE2} {F0 : MachineData → Prop} {R : Region} {D : Int} {m0 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none) :
    ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, wF R D F0 m0 σC m → Mem.loadInt m.dmem a 8 = none :=
  fun q hq a ha m hm => h q hq a ha m hm.1

/-- **`hcell`** from `F0`'s. -/
theorem hcell_wF {ms : MemSide isaLSE2} {F0 : MachineData → Prop} {R : Region} {D : Int} {m0 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : AGB ms ll, (∃ σ, Jm σ q.1.c0) → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none) :
    ∀ q : AGB ms ll, (∃ σ, wJ0 (wNC lab Jm).J σC σ q.1.c0) → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, wF R D F0 m0 σC m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none :=
  fun q hj o h1 h2 => ⟨(h q (hj_J0 hj) o h1 h2).1, fun m hm => (h q (hj_J0 hj) o h1 h2).2 m hm.1⟩

/-! ## `wake_wc_entry_segW` at `scc_rt_main`'s call -/

/-- **`wc_main` from its entry at `scc_rt_main`'s call**:
`wake_wc_entry_segW` at `J0 := wJ0 (wNC lab Jm).J σC`, the region `wR R D`
and the frame condition `wF R D F0 m0 σC`, its caller premises from `Jm`'s
(the thread pointer `t`, the limit word bounded by `sp - 128`, the box's
call at the control) and `F0`'s (`hmem0`, `hcell0`). The other premises
are `wake_wc_entry_segW`'s. -/
theorem wake_wc_entry_segJm {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {D : Int} {F0 : MachineData → Prop} {m0 : MachineData}
    {t : UInt64} (hK : ms.K = some Scc.Sem.A64.abi)
    {W : Frag isaLSE2} {K : State → State → Prop}
    {kp : Nat} (hp : Scc.Cert.Rt.A64.Lays exe SccCode.wakeProg kp)
    (hend : endPc = Scc.Cert.Rt.A64.endOf exe SccCode.wakeProg kp)
    (hF : FStable (wR R D) (wF R D F0 m0 σC)) (hR : (wR R D).OK) (hal : (wR R D).base.toNat % 16 = 0)
    (hlo : (wR R D).lo ≤ -240) (hhi : 0 ≤ (wR R D).hi)
    (htp : ∀ σ c, Jm σ c → σ.regs.TPIDR_EL0 = t)
    (hWp : WcPreW (NoMsrW (tpG t W) K) K exe endPc (wR R D) (wF R D F0 m0 σC) (Spike.Lib.A64.KeepTP.tpXa ms t)
      (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC) (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC))
    (hWs : WcSp0W (NoMsrW (tpG t W) K) K exe endPc (wR R D) (wF R D F0 m0 σC) (Spike.Lib.A64.KeepTP.tpXa ms t)
      (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC))
    (hlim : ∀ σ c, Jm σ c → LimOk ms F0 exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (128 : Int64).toBitVec))
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
    (hxa : ∀ l A s c, lbl l = none → At exe endPc (wR R D) (wF R D F0 m0 σC)
      (bX ms (_root_.Executable.labels exe).label (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC) l A) s c →
      Spike.Lib.A64.KeepTP.TP t s → ms.xa l A 1 s c) :
    SegW W K p lbl ms (At exe endPc (wR R D) (wF R D F0 m0 σC)
        ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC⟩)
      (fun s c => At exe endPc (wR R D) (wF R D F0 m0 σC)
        (wX ms (_root_.Executable.labels exe).label (wJ0 (wNC (_root_.Executable.labels exe).label Jm).J σC) .abort) s c ∧
        Spike.Lib.A64.KeepTP.TP t s) :=
  wake_wc_entry_segW hK hp hend hF hR hal hlo hhi (hJ0tp_J0 htp) hWp hWs (hlim_J0 hlim) (hq_J0 hq)
    (hmem_wF hmem0) (fun q h => hbox q (hj_J0 h)) (hcell_wF hcell0) hxa

end Spike.Lib.A64.Flow.WakeWc

/-- info: 'Spike.Lib.A64.Flow.WakeWc.hlim_J0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.hlim_J0

/-- info: 'Spike.Lib.A64.Flow.WakeWc.wake_wc_entry_segJm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.WakeWc.wake_wc_entry_segJm

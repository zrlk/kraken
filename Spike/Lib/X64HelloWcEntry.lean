/-
**hello.w's `wc_main` entry facts from `wc_rodata`'s return** (x86-64; the twin of
`Spike/Lib/A64HelloWcEntry.lean`'s live part, frame 128): the box's landing at `tpXa ms t` back at `ms`, and the
caller premises of `wc_main`'s segment at `scc_rt_main`'s call read off `wc_rodata`'s return invariant `Jr`.

hello's `scc_rt_main` calls `wc_rodata` before `wc_main`, so `wc_main`'s entry invariant is
`HelloM.wcJ0 (Hello1.mWC lab σC Jr).J σ1`: `wc_rodata`'s return invariant `Jr` at `.x2` after leaving its region,
the `.x2` block moving its results to the argument registers and the call pushing `.x3`.

- `at_bXH_of_tpXa`: the box's landing at `tpXa ms t` is at `ms`.
- `wcJ0_inv`, `tp_wcJ0`, `lim_wcJ0`, `ctl_wcJ0`, `hj_wcJ0`, `loc_wcJ0`: the entry's facts from `Jr`'s.
- `mem_wcF`, `cell_wcF`: the frame condition's from the caller's.

## Differences from the AArch64 version

- `call` pushes `.x3`, so `wc_main`'s entry `%rsp` is `Jr`'s less `8` (`wcJ0_inv`; AArch64: `sp` kept), and
  `lim_wcJ0` asks `Jr`'s limit word at `%rsp - 8 - 8 - 128` (`hello_wc_pre_segW`'s `%rsp - 8 - 128` at the entry);
  the thread pointer is `fsBase` and the limit word `fsBase + 8` (AArch64: `TPIDR_EL0`, `tcbA _ 8`).
- `at_abortH_of_tpXa`, `hello_wc_entry_segW` and `hello_wc_entry_segJr` are not twinned: they are dead in hello
  (its consumers use `X64HelloWcPreA`'s forms with the abort at `wXA`).
-/
import Spike.Lib.X64HelloWcSp0
import Spike.Lib.X64HelloMain
import Spike.Lib.X64WakeWcMain

namespace Spike.Lib.X64.Flow.HelloWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk)
open Spike.Lib.X64.Alloc (Call)
open Spike.Lib.X64.Flow.WakeWc (AGB okb_of_tpXa)
open Spike.Lib.X64.Flow.HelloM (wcJ0 wcF)
open Spike.Lib.X64.Flow.Hello1 (mWC)
open Spike.Lib.X64.KeepTP (tpXa)

/-! ## `tpXa` back to `ms` -/

/-- **The box's landing at `tpXa` is at `ms`**. -/
theorem at_bXH_of_tpXa {ms : MemSide isa} {t : UInt64} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {J1 : AS → Ctl → Prop} {l : WeakMem.AllocLabel} {A : Nat}
    {s : State} {c : Ctl} (h : At exe endPc R F (bXH (tpXa ms t) (_root_.Executable.labels exe).label J1 l A) s c) :
    At exe endPc R F (bXH ms (_root_.Executable.labels exe).label J1 l A) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, q, hq⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, ⟨q.1, okb_of_tpXa q.2⟩, hq⟩

/-! ## The entry's facts from `wc_rodata`'s return -/

section Jr

variable {lab : Label → Int64} {σC σ1 : AS} {Jr : AS → Ctl → Prop}

/-- **An entry state is a `Jr` state's**: `%rsp` `8` below (the pushed `.x3`), the thread pointer kept, the
control the same (`mWC`; the call's `enter` moves only the cells). -/
theorem wcJ0_inv {σ : AS} {c : Ctl} (h : wcJ0 (mWC lab σC Jr).J σ1 σ c) :
    ∃ σx, Jr σx c ∧ σ.regs.rsp.toBitVec = σx.regs.rsp.toBitVec - 8#64 ∧ σ.regs.fsBase = σx.regs.fsBase := by
  obtain ⟨rfl, σx, hJ, -, -, -, -, -, hsp, htp, -, -⟩ := h
  exact ⟨σx, hJ, hsp, htp⟩

/-- **The thread pointer at the entry** from `Jr`'s. -/
theorem tp_wcJ0 {t : UInt64} (hJ : ∀ σ c, Jr σ c → σ.regs.fsBase = t) :
    ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c → σ.regs.fsBase = t :=
  fun _ _ h => let ⟨σx, hJx, _, htp⟩ := wcJ0_inv h; htp.trans (hJ σx _ hJx)

/-- **`hlim`**: the limit word at `Jr`'s thread pointer, bounded by `Jr`'s `%rsp - 8 - 8 - 128` (the pushed
`.x3`, `wc_main`'s saved `%rbp` and frame), at the caller's `F0`. -/
theorem lim_wcJ0 {ms : MemSide isa} {F0 : MachineData → Prop} {R : Region} {D : Int} {m1 : MachineData}
    (h : ∀ σ c, Jr σ c → LimOk ms F0 (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 8#64 - (128 : Int64).toBitVec)) :
    ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c →
      LimOk ms (wcF R D F0 m1 σ1) (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
        (σ.regs.rsp.toBitVec - 8#64 - (128 : Int64).toBitVec) := by
  intro σ c hJ
  obtain ⟨σx, hJx, hsp, htp⟩ := wcJ0_inv hJ
  rw [htp, hsp]
  exact (h σx c hJx).mono fun _ hm => hm.1

/-- **A fact of the entry's control** (`hq`) from `Jr`'s (the call keeps it). -/
theorem ctl_wcJ0 {P : Ctl → Prop} (h : ∀ σ c, Jr σ c → P c) : ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c → P c :=
  fun _ c hJ => let ⟨σx, hJx, _⟩ := wcJ0_inv hJ; h σx c hJx

/-- **The box's control is a `Jr` state's**. -/
theorem hj_wcJ0 {c : Ctl} (h : ∃ σ, wcJ0 (mWC lab σC Jr).J σ1 σ c) : ∃ σ, Jr σ c :=
  let ⟨_, hJ⟩ := h; let ⟨σx, hJx, _⟩ := wcJ0_inv hJ; ⟨σx, hJx⟩

/-- **`hloc`**: the entry block's local run from `Jr`'s to `Jr1`'s, the state kept. -/
theorem loc_wcJ0 {p : Prog} {Jr1 : AS → Ctl → Prop} (h : ∀ σ c, Jr σ c → ∃ c', LocalRun p c c' ∧ Jr1 σ c') :
    ∀ σ c, wcJ0 (mWC lab σC Jr).J σ1 σ c → ∃ c', LocalRun p c c' ∧ wcJ0 (mWC lab σC Jr1).J σ1 σ c' := by
  rintro σ c ⟨rfl, σx, hJx, hr⟩
  obtain ⟨c', hl, hJ1⟩ := h σx c hJx
  exact ⟨c', hl, rfl, σx, hJ1, hr⟩

/-- **`hmem`** from the caller's `F0`. -/
theorem mem_wcF {ms : MemSide isa} {F0 : MachineData → Prop} {R : Region} {D : Int} {m1 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F0 m → Mem.loadInt m.dmem a 8 = none) :
    ∀ q : Call, q.OKB ms ll → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, wcF R D F0 m1 σ1 m → Mem.loadInt m.dmem a 8 = none :=
  fun q hq a ha m hm => h q hq a ha m hm.1

/-- **`hcell`** from the caller's `F0`, at `Jr1`'s controls. -/
theorem cell_wcF {ms : MemSide isa} {F0 : MachineData → Prop} {R : Region} {D : Int} {m1 : MachineData}
    {ll : Label → Int64}
    (h : ∀ q : AGB ms ll, (∃ σ, Jr σ q.1.c0) → ∀ o : Nat, ms.lo o → o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, F0 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none) :
    ∀ q : AGB ms ll, (∃ σ, wcJ0 (mWC lab σC Jr).J σ1 σ q.1.c0) → ∀ o : Nat, ms.lo o →
      o + ms.units 1 q.1.τ ≤ ms.cells →
      ms.mp ⟨BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ), 8⟩ true ∧
      ∀ m, wcF R D F0 m1 σ1 m → Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * o + ms.off 1 q.1.τ)) 8 = none :=
  fun q hj o h1 h2 => ⟨(h q (hj_wcJ0 hj) o h1 h2).1, fun m hm => (h q (hj_wcJ0 hj) o h1 h2).2 m hm.1⟩

end Jr

end Spike.Lib.X64.Flow.HelloWc

/-! ## Axioms -/

/-- info: 'Spike.Lib.X64.Flow.HelloWc.at_bXH_of_tpXa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.at_bXH_of_tpXa

/-- info: 'Spike.Lib.X64.Flow.HelloWc.lim_wcJ0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloWc.lim_wcJ0

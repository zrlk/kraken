/-
**`hello.w`'s `wc_rodata` up to the allocator's return with the thread pointer kept** (x86-64; twin of
`Spike/Lib/A64HelloMainPreT.lean`'s live part, the pre-call half of `X64HelloMainPostT`).

`wc_rodata`'s segment up to its allocator's return runs under `tpXa` inside `NoSetFsW` (`rdPreW_noMsrH`,
`rdPreW_tpH`), so `SegW.keepTPN` carries `TP t` from `wc_rodata`'s entry to its exits: at `.x15` the allocator's
return is at `%fs` base `t`, as `hello_main_post_segWST`'s `hJpT` asks of `Jp`.

- `rdPreW_noMsrH`: `HelloRd.RdPreW` inside `NoSetFsW W K` in any valid layout of `helloCells`
  (`Hello1.RdPreW.noSetFs`'s twin).
- `rdPreW_tpH`: `HelloRd.RdPreW` under `tpXa ms t` (`Hello1.rdPreW_tp`'s twin).
- `rX_untp`, `at_rX_untp`: `wc_rodata`'s exits under `tpXa ms t` are its exits under `ms`.

## Differences from the AArch64 version

- The thread pointer is `%fs`'s base, kept inside `NoSetFsW` (no `syscall`; AArch64 `NoMsrW`, no `msr`); the
  names `rdPreW_noMsrH` and `rdPreW_tpH` are kept for the twins.
- The prologue is x86-64's `XProW` of five blocks (`xHead`, `xLea`, the limit's `%fs` load, `xCmp`, `xFr`;
  AArch64 `ProW`'s four), located by `prologueIn`'s byte offsets from `.Lwc_rodata.chk` (`label_labelGapB`).
- The allocator's code check is `Alloc.allocIn` through `AllocW.noSetFs` (AArch64 `alloc_code_of`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): `hello_main_pre_segWST`.
-/
import Spike.Lib.X64HelloMainPreS
import Spike.Lib.X64Hello1RodataSetup

namespace Spike.Lib.X64.Flow.HelloM

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Hello1 (RX callOK_untp proW_tp allocW_tp)
open Spike.Lib.X64.Flow.HelloRd (rX RdPreW rdPro rdEIn hello_rdEIn hello_rdPro hello_alloc)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Scc.Cert.Rt.X64 (Lays endOf code_field label_labelGapB)

set_option linter.unusedSimpArgs false

section Rd

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop} {ms : MemSide isa}

/-- **`wc_rodata` up to the allocator's return is inside `NoSetFsW W K`** in any valid layout of `helloCells`
(`Hello1.RdPreW.noSetFs`'s twin). -/
theorem rdPreW_noMsrH [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) {J0 J1 : AS → Ctl → Prop}
    (h : RdPreW W K exe endPc R F ms J0 J1) : RdPreW (NoSetFsW W K) K exe endPc R F ms J0 J1 := by
  have hin := hello_rdPro
  simp only [rdPro, prologueIn, Bool.and_eq_true, and_assoc] at hin
  obtain ⟨g0, b0, b1, b2, b3, b4, -⟩ := hin
  have e0 := label_labelGapB hp g0
  have h4 : (_root_.Executable.labels exe).label "wc_rodata" + 1 + 3 =
      (_root_.Executable.labels exe).label ".Lwc_rodata.chk" := by
    rw [e0, Int64.add_assoc]; rfl
  have he := hello_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at he
  refine ⟨XProW.noSetFs1 h.pro (code_field hp hend b0 (ofNat_zero' _)) (code_field hp hend b1 ?_)
    (code_field hp hend b2 ?_) (code_field hp hend b3 ?_) (code_field hp hend b4 ?_)
    (by decide) (by decide) (by decide) (by decide) (by decide),
    BlkW.noSetFs h.e (code_field hp hend he.1 (ofNat_zero' _)) (by decide),
    fun q hok hq => AllocW.noSetFs hp hend hello_alloc (h.alloc q hok hq)⟩
  · rw [h4, ofNat_zero']
  · rw [h4]
  · rw [h4, ofNat_add']
  · rw [h4, ofNat_add', ofNat_add', ofNat_add']

/-- **`wc_rodata` up to the allocator's return under `tpXa ms t`** (`Hello1.rdPreW_tp`'s twin). -/
theorem rdPreW_tpH {t : UInt64} {J0 J1 : AS → Ctl → Prop} (h : RdPreW W K exe endPc R F ms J0 J1) :
    RdPreW W K exe endPc R F (tpXa ms t) J0 J1 :=
  ⟨proW_tp h.pro, h.e, fun q hok hq => allocW_tp (h.alloc q (callOK_untp hok) hq)⟩

/-- **`wc_rodata`'s exits under `tpXa ms t` are its exits under `ms`**. -/
theorem rX_untp {t : UInt64} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J1 : AS → Ctl → Prop} {y : RX} {σ : AS} {c : Ctl} (h : (rX (tpXa ms t) lab lbl R J1 y).J σ c) :
    (rX ms lab lbl R J1 y).J σ c := by
  cases y
  · obtain ⟨q, h1, h2⟩ := h
    exact ⟨⟨q.1, callOK_untp q.2⟩, h1, h2⟩
  · obtain ⟨h0, h30, q, hf, hJ⟩ := h
    exact ⟨h0, h30, ⟨q.1, callOK_untp q.2⟩, hf, hJ⟩

/-- **At `wc_rodata`'s exits under `tpXa ms t`** is at its exits under `ms`. -/
theorem at_rX_untp {t : UInt64} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J1 : AS → Ctl → Prop} {y : RX} {s : State} {c : Ctl}
    (h : At exe endPc R F (rX (tpXa ms t) lab lbl R J1 y) s c) : At exe endPc R F (rX ms lab lbl R J1 y) s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  cases y <;> exact ⟨he, hn, hdc, hpc, σ, hA, hD, rX_untp hJ⟩

end Rd

end Spike.Lib.X64.Flow.HelloM

/-- info: 'Spike.Lib.X64.Flow.HelloM.rdPreW_noMsrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.HelloM.rdPreW_noMsrH

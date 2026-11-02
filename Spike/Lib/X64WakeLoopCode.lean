/-
**wake.w on x86-64: `scc_rt_park`'s code** (main's rows
after the spawn): the x86-64 twin of
`Spike/Lib/A64WakeLoopCode.lean`. `Park.Code` in any valid layout of
`SccCode.wakeCells`, every block decided (`parkIn`), and the park's
prologue fall-through, for `MainPost.seg_mainPost`'s `hpcode` and
`hpentry`.

- `parkIn`, `wake_parkIn`; `parkCode_wake`.
- `parkLabIn`, `wake_parkLabIn`; `parkEntry_wake`.
- `hpcode_L`, `hpentry_L`: `X64WakeMainHRI.hMainR_I`'s `hpcode` and
  `hpentry` at any runtime layout whose cells are `wakeCells` (its end
  `endOf`, i.e. `X64WakeAssemblyR.endR` at `ofPlaceWX`), the parked half.

**Unlike AArch64**: the wait loop's code is not here. `X64WaitLoop`'s
segments take the cells' check `waitIn` themselves (`wake_waitIn`, decided
there), including the label gaps AArch64's `loopLabs_wake` supplies
(`.stack_check`, `.0_entry`, `.sp3`), so only the park's code and its
prologue's fall-through (`.Lscc_rt_park.entry = scc_rt_park + 8`, AArch64's
`+ 16`) are layout facts of `seg_mainPost`. Offsets are bytes; blocks are
checked by `blockAtB` and moved to any layout by `code_field`.
-/
import Spike.Lib.X64Park
import Spike.Lib.X64WakeCode
import Spike.Lib.Rt.X64Layout
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64.Wake.LoopCode

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Park (b0 b1 b2 b3 b4 b5 b6 b7)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field labelGapB label_labelGapB)

/-- `scc_rt_park`'s blocks in wake's cells. -/
abbrev parkIn : Bool :=
  blockAtB SccCode.wakeCells "scc_rt_park" 0 b0 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.entry" 0 [(fsDir .rax 0, 9)] &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.entry" 9 b1 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.entry" 24 [(xchgDir .rcx 16 .rax, 4)] &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.entry" 28 b2 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.entry" 48 b3 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.wait" 0 b4 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.wait" 62 [(op64 .syscall, 2)] &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.wait" 64 b5 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.wait" 79 [(xchgDir .rcx 16 .rax, 4)] &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.wait" 83 b6 &&
  blockAtB SccCode.wakeCells ".Lscc_rt_park.done" 0 b7

theorem wake_parkIn : parkIn = true := by decide +kernel

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **`scc_rt_park`'s code in any valid layout of `wakeCells`**, at any
ghosts. -/
theorem parkCode_wake (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {c0 : Ctl} {rbp0 ra tp : BitVec 64} : Park.Code c0 rbp0 ra tp exe endPc := by
  have h := wake_parkIn
  simp only [parkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨code_field hp hend h0 (Spike.Lib.X64.Flow.ofNat_zero' _),
    code_field hp hend h1 (Spike.Lib.X64.Flow.ofNat_zero' _),
    code_field hp hend h2 rfl, code_field hp hend h3 rfl, code_field hp hend h4 rfl,
    code_field hp hend h5 rfl,
    code_field hp hend h6 (Spike.Lib.X64.Flow.ofNat_zero' _),
    code_field hp hend h7 rfl, code_field hp hend h8 rfl, code_field hp hend h9 rfl,
    code_field hp hend h10 rfl,
    code_field hp hend h11 (Spike.Lib.X64.Flow.ofNat_zero' _)⟩

/-- The park's prologue's label gap in wake's cells. -/
abbrev parkLabIn : Bool := labelGapB SccCode.wakeCells "scc_rt_park" ".Lscc_rt_park.entry" 8

theorem wake_parkLabIn : parkLabIn = true := by decide +kernel

/-- **The park's prologue falls through to its entry block** in any valid
layout of `wakeCells` (`seg_mainPost`'s `hpentry`). -/
theorem parkEntry_wake (hp : Lays exe SccCode.wakeCells kp) :
    (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8 :=
  label_labelGapB hp wake_parkLabIn

/-- **`hMainR_I`'s `hpcode`** at a runtime layout of `wakeCells` (the
ghost control `c0` is any witness, e.g. `Ctl.of s0`). -/
theorem hpcode_L (L : Spike.Lib.X64.Rt.RuntimeLayout) (h : L.prog = SccCode.wakeCells) (c0 : Ctl) :
    ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64),
      Park.Code c0' rbp0' ra' tp' L.exe (endOf L.exe SccCode.wakeCells L.pfx) :=
  haveI := L.valid
  ⟨c0, 0, 0, 0, parkCode_wake (h ▸ L.lays) rfl⟩

/-- **`hMainR_I`'s `hpentry`** at a runtime layout of `wakeCells`. -/
theorem hpentry_L (L : Spike.Lib.X64.Rt.RuntimeLayout) (h : L.prog = SccCode.wakeCells) :
    (_root_.Executable.labels L.exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels L.exe).label "scc_rt_park" + 8 :=
  haveI := L.valid
  parkEntry_wake (h ▸ L.lays)

section PlaceWX

open Spike.Lib.PlaceWX

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`hMainR_I`'s `hpcode` at `ofPlaceWX`** (its end is
`X64WakeAssemblyR.endR hp i`). -/
theorem hpcode_W (ho : o.prog = SccCode.wakeCells) (c0 : Ctl) :
    ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64),
      Park.Code c0' rbp0' ra' tp' (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe
        (endOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe SccCode.wakeCells
          (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).pfx) :=
  hpcode_L _ ho c0

/-- **`hMainR_I`'s `hpentry` at `ofPlaceWX`**. -/
theorem hpentry_W (ho : o.prog = SccCode.wakeCells) :
    (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe).label "scc_rt_park" + 8 :=
  hpentry_L _ ho

end PlaceWX

end Spike.Lib.X64.Wake.LoopCode

/-- info: 'Spike.Lib.X64.Wake.LoopCode.parkCode_wake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Wake.LoopCode.parkCode_wake

/-- info: 'Spike.Lib.X64.Wake.LoopCode.parkEntry_wake' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Wake.LoopCode.parkEntry_wake

/-- info: 'Spike.Lib.X64.Wake.LoopCode.hpcode_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Wake.LoopCode.hpcode_L

/-- info: 'Spike.Lib.X64.Wake.LoopCode.hpentry_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Wake.LoopCode.hpentry_L

/-- info: 'Spike.Lib.X64.Wake.LoopCode.hpcode_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Wake.LoopCode.hpcode_W

/-- info: 'Spike.Lib.X64.Wake.LoopCode.hpentry_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Wake.LoopCode.hpentry_W

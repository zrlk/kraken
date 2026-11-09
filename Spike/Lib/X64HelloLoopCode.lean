/-
**hello.w on x86-64: `scc_rt_park`'s and the wait loop's code**: the twin of
`Spike/Lib/A64HelloLoopCode.lean`, and `Spike/Lib/X64WakeLoopCode.lean` restated at hello.w's
cells (`SccCode.helloCells`, `Spike/Lib/X64HelloCode.lean`). `Park.Code` in any valid layout
of `helloCells`, every block decided (`parkIn`), the park's prologue fall-through, and the
wait loop's check `X64WaitLoopX.waitInX` at hello's label `.Lwc_waitLoop.x1` and `helloCells`
(`waitXL`, `hello_waitIn`), for
`MainPost.seg_mainPost`'s `hpcode`, `hpentry` and the wait loop's segments.

- `parkIn`, `hello_parkIn`; `parkCode_hello`; `waitXL`, `hello_waitIn`.
- `parkLabIn`, `hello_parkLabIn`; `parkEntry_hello`.
- `hpcode_L`, `hpentry_L`, `hpcode_W`, `hpentry_W`: at any runtime layout whose cells are
  `helloCells` (at `ofPlaceWX`).

Unlike AArch64 (`A64HelloLoopCode`, which restates the wait loop's blocks at hello's label
prefix `.L21_wc_waitLoop` through `A64HelloLabels`): x86-64 labels carry no numbering prefix
but their numbers `.xN` are per program: the wait loop's segments are `X64WaitLoopX`'s, at the
label `waitXL`, taking the cells' check `waitInX` themselves (`hello_waitIn`, decided here); there
is no `HelloLabels` module.
-/
import Spike.Lib.X64Park
import Spike.Lib.X64HelloCode
import Spike.Lib.X64CodeAcross
import Spike.Lib.X64WaitLoopX
import Spike.Lib.Rt.X64Layout
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64.Hello.LoopCode

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib.X64
open Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Park (b0 b1 b2 b3 b4 b5 b6 b7)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB code_field labelGapB label_labelGapB blockAcrossB)

/-- `scc_rt_park`'s blocks in hello's cells. -/
abbrev parkIn : Bool :=
  blockAtB SccCode.helloCells "scc_rt_park" 0 b0 &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.entry" 0 [(fsDir .rax 0, 9)] &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.entry" 9 b1 &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.entry" 24 [(xchgDir .rcx 16 .rax, 4)] &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.entry" 28 b2 &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.entry" 48 b3 &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.wait" 0 b4 &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.wait" 62 [(op64 .syscall, 2)] &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.wait" 64 b5 &&
  blockAtB SccCode.helloCells ".Lscc_rt_park.wait" 79 [(xchgDir .rcx 16 .rax, 4)] &&
  blockAcrossB SccCode.helloCells ".Lscc_rt_park.wait" 83 (b6.take 3) ".Lscc_rt_park.x0" (b6.drop 3) &&
  blockAcrossB SccCode.helloCells ".Lscc_rt_park.done" 0 (b7.take 2) ".Lscc_rt_park.x1" (b7.drop 2)

theorem hello_parkIn : parkIn = true := by decide +kernel

/-- hello's label after the park call in `wc_waitLoop` (wake's `.Lwc_waitLoop.x16`). -/
abbrev waitXL : Label := ".Lwc_waitLoop.x1"

/-- **The wait loop's code in hello's cells** (`X64WaitLoopX.waitInX` at `waitXL`, the check
the label-parametric segments take: blocks and label gaps). -/
theorem hello_waitIn : Spike.Lib.X64.WaitLoopX.waitInX waitXL SccCode.helloCells = true := by decide +kernel

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **`scc_rt_park`'s code in any valid layout of `helloCells`**, at any
ghosts. -/
theorem parkCode_hello (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {c0 : Ctl} {rbp0 ra tp : BitVec 64} : Park.Code c0 rbp0 ra tp exe endPc := by
  have h := hello_parkIn
  simp only [parkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨code_field hp hend h0 (Spike.Lib.X64.Flow.ofNat_zero' _),
    code_field hp hend h1 (Spike.Lib.X64.Flow.ofNat_zero' _),
    code_field hp hend h2 rfl, code_field hp hend h3 rfl, code_field hp hend h4 rfl,
    code_field hp hend h5 rfl,
    code_field hp hend h6 (Spike.Lib.X64.Flow.ofNat_zero' _),
    code_field hp hend h7 rfl, code_field hp hend h8 rfl, code_field hp hend h9 rfl,
    Spike.Lib.X64.code_field_blockAcrossB hp hend h10 (List.take_append_drop _ _) rfl,
    Spike.Lib.X64.code_field_blockAcrossB hp hend h11 (List.take_append_drop _ _)
      (Spike.Lib.X64.Flow.ofNat_zero' _)⟩

/-- The park's prologue's label gap in hello's cells. -/
abbrev parkLabIn : Bool := labelGapB SccCode.helloCells "scc_rt_park" ".Lscc_rt_park.entry" 8

theorem hello_parkLabIn : parkLabIn = true := by decide +kernel

/-- **The park's prologue falls through to its entry block** in any valid
layout of `helloCells` (`seg_mainPost`'s `hpentry`). -/
theorem parkEntry_hello (hp : Lays exe SccCode.helloCells kp) :
    (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8 :=
  label_labelGapB hp hello_parkLabIn

/-- **`hMainR_I`'s `hpcode`** at a runtime layout of `helloCells` (the
ghost control `c0` is any witness, e.g. `Ctl.of s0`). -/
theorem hpcode_L (L : Spike.Lib.X64.Rt.RuntimeLayout) (h : L.prog = SccCode.helloCells) (c0 : Ctl) :
    ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64),
      Park.Code c0' rbp0' ra' tp' L.exe (endOf L.exe SccCode.helloCells L.pfx) :=
  haveI := L.valid
  ⟨c0, 0, 0, 0, parkCode_hello (h ▸ L.lays) rfl⟩

/-- **`hMainR_I`'s `hpentry`** at a runtime layout of `helloCells`. -/
theorem hpentry_L (L : Spike.Lib.X64.Rt.RuntimeLayout) (h : L.prog = SccCode.helloCells) :
    (_root_.Executable.labels L.exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels L.exe).label "scc_rt_park" + 8 :=
  haveI := L.valid
  parkEntry_hello (h ▸ L.lays)

section PlaceWX

open Spike.Lib.PlaceWX

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ0 : Scc.Sem.Layout}
  (hp : PlaceWX pcfg Λ0 o) (i : CoreTerm.Expr → String → Nat → Option Nat)

/-- **`hMainR_I`'s `hpcode` at `ofPlaceWX`** (its end is `endOf` at the layout's
prefix). -/
theorem hpcode_W (ho : o.prog = SccCode.helloCells) (c0 : Ctl) :
    ∃ (c0' : Ctl) (rbp0' ra' tp' : BitVec 64),
      Park.Code c0' rbp0' ra' tp' (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe
        (endOf (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe SccCode.helloCells
          (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).pfx) :=
  hpcode_L _ ho c0

/-- **`hMainR_I`'s `hpentry` at `ofPlaceWX`**. -/
theorem hpentry_W (ho : o.prog = SccCode.helloCells) :
    (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hp i).exe).label "scc_rt_park" + 8 :=
  hpentry_L _ ho

end PlaceWX

end Spike.Lib.X64.Hello.LoopCode

/-- info: 'Spike.Lib.X64.Hello.LoopCode.parkCode_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.LoopCode.parkCode_hello

/-- info: 'Spike.Lib.X64.Hello.LoopCode.parkEntry_hello' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.LoopCode.parkEntry_hello

/-- info: 'Spike.Lib.X64.Hello.LoopCode.hpcode_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.LoopCode.hpcode_L

/-- info: 'Spike.Lib.X64.Hello.LoopCode.hpentry_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.LoopCode.hpentry_L

/-- info: 'Spike.Lib.X64.Hello.LoopCode.hpcode_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.LoopCode.hpcode_W

/-- info: 'Spike.Lib.X64.Hello.LoopCode.hpentry_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Hello.LoopCode.hpentry_W

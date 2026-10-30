/-
**wake.w on AArch64: the wait loop's and `scc_rt_park`'s code** (main's rows after the spawn): `WaitLoop.Code` at wake's
prefix and `Park.Code` in any valid layout of `wakeProg`, every block decided
(`waitIn`, `parkIn`), for `MainPost.seg_mainPost`'s `hcode` and `hpcode`.

- `waitIn`, `wake_waitIn`; `waitCode_wake`.
- `parkIn`, `wake_parkIn`; `parkCode_wake`.
-/
import Spike.Lib.A64WaitLoop
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64WakeLabels

namespace Spike.Lib.A64.Flow.Worker.Wake.LoopCode

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow Spike.Lib.A64
open Spike.Lib.A64.Flow.Park (swpDir)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.WakeLabels (wakeProg pfx)

/-- The wait loop's blocks in wake's program. -/
abbrev waitIn : Bool :=
  labelGap wakeProg "wc_waitLoop" (pfx ++ ".stack_check") 0 &&
  blockAt wakeProg (pfx ++ ".stack_check") 0 WaitLoop.b0 && blockAt wakeProg (pfx ++ ".stack_check") 3 (WaitLoop.b1 pfx) &&
  blockAt wakeProg (pfx ++ ".stack_check") 5 WaitLoop.b2 && blockAt wakeProg (pfx ++ ".0_entry") 0 WaitLoop.b3 &&
  blockAt wakeProg (pfx ++ ".0_entry") 1 [ldarDir .X9 .X10] &&
  blockAt wakeProg (pfx ++ ".0_entry") 2 (WaitLoop.b4 pfx) &&
  blockAt wakeProg (pfx ++ ".0_entry") 7 (WaitLoop.b5 pfx) &&
  blockAt wakeProg (pfx ++ ".1_then1") 0 WaitLoop.b6 && blockAt wakeProg (pfx ++ ".2_else2") 0 WaitLoop.b7 &&
  blockAt wakeProg (pfx ++ ".sp3") 0 WaitLoop.b8 && blockAt wakeProg (pfx ++ ".stack_grow") 0 WaitLoop.b9 &&
  blockAt wakeProg (pfx ++ ".sp_check") 0 (WaitLoop.b10 pfx)

theorem wake_waitIn : waitIn = true := by decide +kernel

/-- `scc_rt_park`'s blocks in wake's program. -/
abbrev parkIn : Bool :=
  blockAt wakeProg "scc_rt_park" 0 Park.b0 && blockAt wakeProg ".L10_scc_rt_park.0_entry" 0 Park.b1 &&
  blockAt wakeProg ".L10_scc_rt_park.0_entry" 5 [swpDir .acqRel .X9 .X11 .X10] &&
  blockAt wakeProg ".L10_scc_rt_park.0_entry" 6 Park.b2 &&
  blockAt wakeProg ".L10_scc_rt_park.0_entry" 11 Park.b3 &&
  blockAt wakeProg ".L10_scc_rt_park.1_wait" 0 Park.b4 &&
  blockAt wakeProg ".L10_scc_rt_park.1_wait" 11 [svcDir] &&
  blockAt wakeProg ".L10_scc_rt_park.1_wait" 12 Park.b5 &&
  blockAt wakeProg ".L10_scc_rt_park.1_wait" 16 [swpDir .acqRel .X9 .X11 .X10] &&
  blockAt wakeProg ".L10_scc_rt_park.1_wait" 17 Park.b6 &&
  blockAt wakeProg ".L10_scc_rt_park.2_done" 0 Park.b7

theorem wake_parkIn : parkIn = true := by decide +kernel

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **The wait loop's code in any valid layout of `wakeProg`.** -/
theorem waitCode_wake (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {c0 : Ctl} {x : String}
    {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64} :
    WaitLoop.Code pfx c0 x e ty Rd A x29 ra tp exe endPc := by
  have h := wake_waitIn
  simp only [waitIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨hg, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  have hg' := label_labelGap hp hg
  rw [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at hg'
  exact ⟨code_of hp hend h0 (by rw [hg']; simp [WaitLoop.N]),
    code_of hp hend h1 (by rw [hg']; simp only [WaitLoop.N, Int64.add_assoc]; rfl),
    code_of hp hend h2 (by rw [hg']; simp only [WaitLoop.N, Int64.add_assoc]; rfl),
    code_of hp hend h3 (by simp [WaitLoop.N]),
    code_of hp hend h4 (by simp only [WaitLoop.N]; rfl),
    code_of hp hend h5 (by simp only [WaitLoop.N, Int64.add_assoc]; rfl),
    code_of hp hend h6 (by simp only [WaitLoop.N, Int64.add_assoc]; rfl),
    code_of hp hend h7 (by simp [WaitLoop.N]),
    code_of hp hend h8 (by simp [WaitLoop.N]),
    code_of hp hend h9 (by simp [WaitLoop.N]),
    code_of hp hend h10 (by simp [WaitLoop.N]),
    code_of hp hend h11 (by simp [WaitLoop.N])⟩

/-- **`scc_rt_park`'s code in any valid layout of `wakeProg`.** -/
theorem parkCode_wake (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {c0 : Ctl}
    {x29 ra tp : BitVec 64} : Park.Code c0 x29 ra tp exe endPc := by
  have h := wake_parkIn
  simp only [parkIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨code_of hp hend h0 (by simp [Park.N, ]),
    code_of hp hend h1 (by simp [Park.N, ]),
    code_of hp hend h2 (by simp only [Park.N, Int64.add_assoc]; rfl),
    code_of hp hend h3 (by simp only [Park.N, Int64.add_assoc]; rfl),
    code_of hp hend h4 (by simp only [Park.N, Int64.add_assoc]; rfl),
    code_of hp hend h5 (by simp [Park.N, ]),
    code_of hp hend h6 (by simp only [Park.N, Park.pcSvc, Int64.add_assoc]; rfl),
    code_of hp hend h7 (by simp only [Park.N, Park.pcSvc, Int64.add_assoc]; rfl),
    code_of hp hend h8 (by simp only [Park.N, Park.pcSvc, Int64.add_assoc]; rfl),
    code_of hp hend h9 (by simp only [Park.N, Park.pcSvc, Int64.add_assoc]; rfl),
    code_of hp hend h10 (by simp [Park.N, ])⟩

/-- The wait loop's and the park's label gaps in wake's program. -/
abbrev loopLabsIn : Bool :=
  labelGap wakeProg (pfx ++ ".stack_check") (pfx ++ ".0_entry") 10 &&
  labelGap wakeProg "wc_waitLoop" (pfx ++ ".stack_check") 0 &&
  labelGap wakeProg (pfx ++ ".2_else2") (pfx ++ ".sp3") 1 &&
  labelGap wakeProg "scc_rt_park" ".L10_scc_rt_park.0_entry" 4

theorem wake_loopLabsIn : loopLabsIn = true := by decide +kernel

/-- **The wait loop's and the park's labels in any valid layout of
`wakeProg`**: `seg_waitLoopP`'s `hentry`, `hcheck`, `hsp3`, `hpentry`. -/
theorem loopLabs_wake (hp : Lays exe wakeProg kp) :
    (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 ∧
    (_root_.Executable.labels exe).label (pfx ++ ".stack_check") =
      (_root_.Executable.labels exe).label "wc_waitLoop" ∧
    (_root_.Executable.labels exe).label (pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (pfx ++ ".2_else2") + 4 ∧
    (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4 := by
  have h := wake_loopLabsIn
  simp only [loopLabsIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h2' := label_labelGap hp h2
  rw [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at h2'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [label_labelGap hp h1, h2']; simp only [Int64.add_assoc]; rfl
  · exact h2'
  · rw [label_labelGap hp h3]; rfl
  · rw [label_labelGap hp h4]; simp only [Int64.add_assoc]; rfl

end Spike.Lib.A64.Flow.Worker.Wake.LoopCode

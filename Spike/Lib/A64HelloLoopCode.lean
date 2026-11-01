/-
**hello.w on AArch64: the wait loop's and `scc_rt_park`'s code** (B2): `WaitLoop.Code` at hello's prefix
(`.L21_wc_waitLoop`) and
`Park.Code` in any valid layout of `SccCode.helloProg`, every block decided
(`waitIn`, `parkIn`) on hello.w's listing (`Spike/Lib/A64HelloCode.lean`),
for `MainPost.seg_mainPost`'s `hcode` and `hpcode`. The restatement of
`Spike.Lib.A64.Flow.Worker.Wake.LoopCode` (`A64WakeLoopCode.lean`) at
`helloProg`: the blocks are wake's, at hello's prefix.

- `waitIn`, `hello_waitIn`; `waitCode_hello`.
- `parkIn`, `hello_parkIn`; `parkCode_hello`.
- `loopLabsIn`, `hello_loopLabsIn`; `loopLabs_hello`.
-/
import Spike.Lib.A64WaitLoop
import Spike.Lib.A64CodeSegs
import Spike.Lib.A64HelloLabels

namespace Spike.Lib.A64.Flow.Worker.Hello.LoopCode

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib.A64.Flow Spike.Lib.A64
open Spike.Lib.A64.Flow.Park (swpDir)
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap)
open Spike.Lib.A64.HelloLabels (pfx)
open SccCode (helloProg)

/-- The wait loop's blocks in hello's program. -/
abbrev waitIn : Bool :=
  labelGap helloProg "wc_waitLoop" (pfx ++ ".stack_check") 0 &&
  blockAt helloProg (pfx ++ ".stack_check") 0 WaitLoop.b0 &&
  blockAt helloProg (pfx ++ ".stack_check") 3 (WaitLoop.b1 pfx) &&
  blockAt helloProg (pfx ++ ".stack_check") 5 WaitLoop.b2 && blockAt helloProg (pfx ++ ".0_entry") 0 WaitLoop.b3 &&
  blockAt helloProg (pfx ++ ".0_entry") 1 [ldarDir .X9 .X10] &&
  blockAt helloProg (pfx ++ ".0_entry") 2 (WaitLoop.b4 pfx) &&
  blockAt helloProg (pfx ++ ".0_entry") 7 (WaitLoop.b5 pfx) &&
  blockAt helloProg (pfx ++ ".1_then1") 0 WaitLoop.b6 && blockAt helloProg (pfx ++ ".2_else2") 0 WaitLoop.b7 &&
  blockAt helloProg (pfx ++ ".sp3") 0 WaitLoop.b8 && blockAt helloProg (pfx ++ ".stack_grow") 0 WaitLoop.b9 &&
  blockAt helloProg (pfx ++ ".sp_check") 0 (WaitLoop.b10 pfx)

theorem hello_waitIn : waitIn = true := by decide +kernel

/-- `scc_rt_park`'s blocks in hello's program. -/
abbrev parkIn : Bool :=
  blockAt helloProg "scc_rt_park" 0 Park.b0 && blockAt helloProg ".L10_scc_rt_park.0_entry" 0 Park.b1 &&
  blockAt helloProg ".L10_scc_rt_park.0_entry" 5 [swpDir .acqRel .X9 .X11 .X10] &&
  blockAt helloProg ".L10_scc_rt_park.0_entry" 6 Park.b2 &&
  blockAt helloProg ".L10_scc_rt_park.0_entry" 11 Park.b3 &&
  blockAt helloProg ".L10_scc_rt_park.1_wait" 0 Park.b4 &&
  blockAt helloProg ".L10_scc_rt_park.1_wait" 11 [svcDir] &&
  blockAt helloProg ".L10_scc_rt_park.1_wait" 12 Park.b5 &&
  blockAt helloProg ".L10_scc_rt_park.1_wait" 16 [swpDir .acqRel .X9 .X11 .X10] &&
  blockAt helloProg ".L10_scc_rt_park.1_wait" 17 Park.b6 &&
  blockAt helloProg ".L10_scc_rt_park.2_done" 0 Park.b7

theorem hello_parkIn : parkIn = true := by decide +kernel

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}

/-- **The wait loop's code in any valid layout of `helloProg`.** -/
theorem waitCode_hello (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {c0 : Ctl} {x : String}
    {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64} :
    WaitLoop.Code pfx c0 x e ty Rd A x29 ra tp exe endPc := by
  have h := hello_waitIn
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

/-- **`scc_rt_park`'s code in any valid layout of `helloProg`.** -/
theorem parkCode_hello (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {c0 : Ctl}
    {x29 ra tp : BitVec 64} : Park.Code c0 x29 ra tp exe endPc := by
  have h := hello_parkIn
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

/-- The wait loop's and the park's label gaps in hello's program. -/
abbrev loopLabsIn : Bool :=
  labelGap helloProg (pfx ++ ".stack_check") (pfx ++ ".0_entry") 10 &&
  labelGap helloProg "wc_waitLoop" (pfx ++ ".stack_check") 0 &&
  labelGap helloProg (pfx ++ ".2_else2") (pfx ++ ".sp3") 1 &&
  labelGap helloProg "scc_rt_park" ".L10_scc_rt_park.0_entry" 4

theorem hello_loopLabsIn : loopLabsIn = true := by decide +kernel

/-- **The wait loop's and the park's labels in any valid layout of
`helloProg`**: `seg_waitLoopP`'s `hentry`, `hcheck`, `hsp3`, `hpentry`. -/
theorem loopLabs_hello (hp : Lays exe helloProg kp) :
    (_root_.Executable.labels exe).label (pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 ∧
    (_root_.Executable.labels exe).label (pfx ++ ".stack_check") =
      (_root_.Executable.labels exe).label "wc_waitLoop" ∧
    (_root_.Executable.labels exe).label (pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (pfx ++ ".2_else2") + 4 ∧
    (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4 := by
  have h := hello_loopLabsIn
  simp only [loopLabsIn, Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h2' := label_labelGap hp h2
  rw [show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero] at h2'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [label_labelGap hp h1, h2']; simp only [Int64.add_assoc]; rfl
  · exact h2'
  · rw [label_labelGap hp h3]; rfl
  · rw [label_labelGap hp h4]; simp only [Int64.add_assoc]; rfl

end Spike.Lib.A64.Flow.Worker.Hello.LoopCode

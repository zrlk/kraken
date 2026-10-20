/-
**`spsc_queue_relaxed3.kl` is `Sometimes`: the consumer can read a slot
before its data lands**.

The three-item version of `spsc_queue_relaxed2.kl`: the producer publishes
`tail` with a plain `STR` (no release), so it may promise a `tail` update
before the slot's data store; the consumer then reads a stale value.
`spsc_queue_relaxed3_reachable`: from the runner's exact initial
configuration (`c0`, checked by `reachA64RunnerMatches`), under
`Arch.armv8` at the runner's certification fuel `300`, some final
configuration violates the `.kl`'s `forall (1:X10=1 /\ 1:X11=2 /\
1:X12=3)`. The witness has four promise steps (`ReachCertCore`).
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.ReachA64Checkpoint
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.SpscQueueRelaxed3

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `spsc_queue_relaxed3.kl`, verbatim. -/
def code : Program := parseAArch64("
prod:
  MOV W3,#1
  MOV X4,#0
  MOV X7,X0
prod_loop:
  LDAR X5,[X1]
  SUB X6,X4,X5
  CMP X6,#2
  B.EQ prod_loop
  STR W3,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STR X4,[X2]
  ADD W3,W3,#1
  CMP W3,#4
  B.NE prod_loop
  B pdone
pdone:
  NOP
cons:
  MOV X4,#0
  MOV X7,X0
c1:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c1
  LDR W10,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c2:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c2
  LDR W11,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
c3:
  LDAR X5,[X2]
  CMP X5,X4
  B.EQ c3
  LDR W12,[X7]
  EOR X7,X7,#8
  ADD X4,X4,#1
  STLR X4,[X1]
  B cdone
cdone:
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x1200, 0⟩], unsizedDefault := true }

/-- The runner's initial memory (unsized locations). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0x0), (⟨0x1100, 0⟩, 0x0), (⟨0x1200, 0⟩, 0x0)]

/-- The runner's initial configuration: the producer from `prod` to `pdone`, the consumer from
`cons` to `cdone`, both with `X0 = buf`, `X1 = head`, `X2 = tail`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100000 0x10003c,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X2, 0x1200)] 0x100040 0x1000a0] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/spsc_queue_relaxed3.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 65 steps, 4 promises). -/
def trace : List ReachPStep :=
  [.instr 0 [], .instr 0 [], .instr 0 [], .instr 1 [], .instr 1 [],
   .promise 0 0x1008 2, .promise 0 0x1200 1, .promise 0 0x1200 2, .instr 0 [0], .instr 0 [],
   .instr 0 [], .instr 0 [], .instr 1 [2], .instr 1 [], .instr 1 [],
   .instr 1 [0], .instr 1 [], .instr 1 [], .instr 1 [4], .promise 0 0x1200 3,
   .instr 1 [3], .instr 1 [], .instr 1 [], .instr 1 [1], .instr 1 [],
   .instr 1 [], .instr 1 [6], .instr 0 [7], .instr 0 [], .instr 0 [],
   .instr 0 [2], .instr 0 [], .instr 0 [], .instr 0 [], .instr 0 [0],
   .instr 0 [], .instr 0 [], .instr 0 [], .instr 0 [1], .instr 0 [],
   .instr 0 [], .instr 0 [3], .instr 0 [], .instr 0 [], .instr 0 [],
   .instr 0 [4], .instr 0 [], .instr 0 [], .instr 0 [], .instr 0 [8],
   .instr 0 [], .instr 0 [], .instr 0 [5], .instr 0 [], .instr 0 [],
   .instr 0 [], .instr 0 [], .instr 1 [5], .instr 1 [], .instr 1 [],
   .instr 1 [0], .instr 1 [], .instr 1 [], .instr 1 [9], .instr 1 []]

/-! ## Checkpoints

The witness is checked in segments (`ReachCheckpoint`), each its own kernel
evaluation, to bound the kernel's memory. `cpK` is the configuration after
the step its docstring names, printed by `reachA64ShowCfg`; `reachK` proves
it reachable. -/

/-- Checkpoint 1: after step 9. -/
def cp1 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x1, X7 := 0x1000 }, ⟨false, false, false, false⟩, ∅⟩, 0x100010),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001100#64, bytes := 0 }, 0)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [1, 2, 3]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X7 := 0x1000 }, ⟨false, false, false, false⟩, ∅⟩, 0x100048),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }]

theorem reach1 : Reachable Arch.armv8 300 c0 cp1 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (.refl c0)
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := c0) (tr := (trace.drop 0).take 9) (by decide +kernel)

/-- Checkpoint 2: after step 27. -/
def cp2 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x1, X7 := 0x1000 }, ⟨true, false, false, false⟩, ∅⟩, 0x10001c),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001100#64, bytes := 0 }, 0)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [1, 2, 3, 5]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X4 := 0x2, X5 := 0x2, X7 := 0x1000, X11 := 0x2 }, ⟨false, false, true, false⟩, ∅⟩, 0x100080),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 2), ({ addr := 0x0000000000001008#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 6), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 6, fwdb := [({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 6, view := 0, xcl := false })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000003#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }]

theorem reach2 : Reachable Arch.armv8 300 c0 cp2 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach1
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp1) (tr := (trace.drop 9).take 18) (by decide +kernel)

/-- Checkpoint 3: after step 30. -/
def cp3 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x1, X4 := 0x1, X7 := 0x1008 }, ⟨true, false, false, false⟩, ∅⟩, 0x100028),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 7), ({ addr := 0x0000000000001100#64, bytes := 0 }, 0)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 7, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 7, view := 0, xcl := false })], xclb := none },
     [1, 2, 3, 5]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X4 := 0x2, X5 := 0x2, X7 := 0x1000, X11 := 0x2 }, ⟨false, false, true, false⟩, ∅⟩, 0x100080),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 2), ({ addr := 0x0000000000001008#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 6), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 6, fwdb := [({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 6, view := 0, xcl := false })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000003#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach3 : Reachable Arch.armv8 300 c0 cp3 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach2
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp2) (tr := (trace.drop 27).take 3) (by decide +kernel)

/-- Checkpoint 4: after step 33. -/
def cp4 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x2, X4 := 0x1, X7 := 0x1008 }, ⟨true, false, false, false⟩, ∅⟩, 0x100034),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 7), ({ addr := 0x0000000000001100#64, bytes := 0 }, 0), ({ addr := 0x0000000000001200#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 7, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 7, view := 0, xcl := false }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 2, view := 0, xcl := false })], xclb := none },
     [1, 3, 5]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X4 := 0x2, X5 := 0x2, X7 := 0x1000, X11 := 0x2 }, ⟨false, false, true, false⟩, ∅⟩, 0x100080),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 2), ({ addr := 0x0000000000001008#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 6), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 6, fwdb := [({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 6, view := 0, xcl := false })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000003#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach4 : Reachable Arch.armv8 300 c0 cp4 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach3
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp3) (tr := (trace.drop 30).take 3) (by decide +kernel)

/-- Checkpoint 5: after step 37. -/
def cp5 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x2, X4 := 0x1, X6 := 0x1, X7 := 0x1008 }, ⟨true, false, false, false⟩, ∅⟩, 0x100018),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 7), ({ addr := 0x0000000000001100#64, bytes := 0 }, 0), ({ addr := 0x0000000000001200#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 7, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 7, view := 0, xcl := false }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 2, view := 0, xcl := false })], xclb := none },
     [1, 3, 5]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X4 := 0x2, X5 := 0x2, X7 := 0x1000, X11 := 0x2 }, ⟨false, false, true, false⟩, ∅⟩, 0x100080),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 2), ({ addr := 0x0000000000001008#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 6), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 6, fwdb := [({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 6, view := 0, xcl := false })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000003#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach5 : Reachable Arch.armv8 300 c0 cp5 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach4
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp4) (tr := (trace.drop 33).take 4) (by decide +kernel)

/-- Checkpoint 6: after step 41. -/
def cp6 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x2, X4 := 0x2, X6 := 0x1, X7 := 0x1000 }, ⟨true, false, false, false⟩, ∅⟩, 0x100028),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 7), ({ addr := 0x0000000000001008#64, bytes := 0 }, 1), ({ addr := 0x0000000000001100#64, bytes := 0 }, 0), ({ addr := 0x0000000000001200#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 7, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 7, view := 0, xcl := false }), ({ addr := 0x0000000000001008#64, bytes := 0 }, { time := 1, view := 0, xcl := false }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 2, view := 0, xcl := false })], xclb := none },
     [3, 5]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X4 := 0x2, X5 := 0x2, X7 := 0x1000, X11 := 0x2 }, ⟨false, false, true, false⟩, ∅⟩, 0x100080),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 2), ({ addr := 0x0000000000001008#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 6), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 6, fwdb := [({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 6, view := 0, xcl := false })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000003#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach6 : Reachable Arch.armv8 300 c0 cp6 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach5
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp5) (tr := (trace.drop 37).take 4) (by decide +kernel)

/-- Checkpoint 7: after step 46. -/
def cp7 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X3 := 0x3, X4 := 0x2, X5 := 0x1, X6 := 0x1, X7 := 0x1000 }, ⟨true, false, false, false⟩, ∅⟩, 0x100010),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 7), ({ addr := 0x0000000000001008#64, bytes := 0 }, 1), ({ addr := 0x0000000000001100#64, bytes := 0 }, 4), ({ addr := 0x0000000000001200#64, bytes := 0 }, 3)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 7, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 7, view := 0, xcl := false }), ({ addr := 0x0000000000001008#64, bytes := 0 }, { time := 1, view := 0, xcl := false }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 3, view := 0, xcl := false })], xclb := none },
     [5]),
   ((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X4 := 0x2, X5 := 0x2, X7 := 0x1000, X11 := 0x2 }, ⟨false, false, true, false⟩, ∅⟩, 0x100080),
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 2), ({ addr := 0x0000000000001008#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 6), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 6, fwdb := [({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 6, view := 0, xcl := false })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001008#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000003#128, tid := 0 }, { loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach7 : Reachable Arch.armv8 300 c0 cp7 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach6
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp6) (tr := (trace.drop 41).take 5) (by decide +kernel)

/-- **`spsc_queue_relaxed3.kl`'s stale read is reachable** from the runner's configuration, at certification
fuel `300` (the runner's `-fuel`). -/
theorem spsc_queue_relaxed3_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧
      ¬ (reachXReg c 1 .X10 = some 1 ∧ reachXReg c 1 .X11 = some 2 ∧ reachXReg c 1 .X12 = some 3) :=
  reach_witness_promise_from Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach7
    (tr := trace.drop 46) (by decide +kernel)

end Kraken.Promising.Reach.SpscQueueRelaxed3

#print axioms Kraken.Promising.Reach.SpscQueueRelaxed3.spsc_queue_relaxed3_reachable

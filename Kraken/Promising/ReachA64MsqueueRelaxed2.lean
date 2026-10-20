/-
**`msqueue_relaxed2.kl` is `Sometimes`: the dequeuer can receive stale data**
.

The two-item Michael-Scott queue with plain CASes (no release): the
enqueuer may promise a link or tail swing before the node's data store, so
the dequeuer can follow the link and read stale data.
`msqueue_relaxed2_reachable`: from the runner's exact initial configuration
(`c0`, checked by `reachA64RunnerMatches`), under `Arch.armv8` at the
runner's certification fuel `300`, some final configuration violates the
`.kl`'s `forall (1:X10=1 /\ 1:X11=2)`. The witness has one promise step
(`ReachCertCore`); it was found by the explorer with `-promises 1` (the
unbounded exploration does not finish in 10 minutes), which only restricts
the search: every step of the witness is a step of `succs`.
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.ReachA64Checkpoint
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.MsqueueRelaxed2

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `msqueue_relaxed2.kl`, verbatim. -/
def code : Program := parseAArch64("
enq:
enq1:
  MOV X2,X12
  MOV W9,#1
  STR W9,[X2]
enq1_loop:
  LDAR X3,[X1]
  ADD X8,X3,#8
  LDAR X4,[X8]
  CBNZ X4,enq1_fix
  MOV X5,#0
  CAS X5,X2,[X8]
  CBNZ X5,enq1_loop
  MOV X5,X3
  CAS X5,X2,[X1]
  B enq1_end
enq1_fix:
  MOV X5,X3
  CAS X5,X4,[X1]
  B enq1_loop
enq1_end:
enq2:
  MOV X2,X13
  MOV W9,#2
  STR W9,[X2]
enq2_loop:
  LDAR X3,[X1]
  ADD X8,X3,#8
  LDAR X4,[X8]
  CBNZ X4,enq2_fix
  MOV X5,#0
  CAS X5,X2,[X8]
  CBNZ X5,enq2_loop
  MOV X5,X3
  CAS X5,X2,[X1]
  B enq2_end
enq2_fix:
  MOV X5,X3
  CAS X5,X4,[X1]
  B enq2_loop
enq2_end:
  B pdone
pdone:
  NOP
deq1:
deq1a:
  LDAR X3,[X0]
  LDAR X4,[X1]
  ADD X8,X3,#8
  LDAR X5,[X8]
  CMP X3,X4
  B.NE deq1a_ne
  CBZ X5,deq1a
  MOV X6,X3
  CAS X6,X5,[X1]
  B deq1a
deq1a_ne:
  CBZ X5,deq1a
  LDR W7,[X5]
  MOV X6,X3
  CAS X6,X5,[X0]
  CMP X6,X3
  B.NE deq1a
  MOV W10,W7
deq1b:
  LDAR X3,[X0]
  LDAR X4,[X1]
  ADD X8,X3,#8
  LDAR X5,[X8]
  CMP X3,X4
  B.NE deq1b_ne
  CBZ X5,deq1b
  MOV X6,X3
  CAS X6,X5,[X1]
  B deq1b
deq1b_ne:
  CBZ X5,deq1b
  LDR W7,[X5]
  MOV X6,X3
  CAS X6,X5,[X0]
  CMP X6,X3
  B.NE deq1b
  MOV W11,W7
  B ddone1
ddone1:
  NOP
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1200, 0⟩, ⟨0x1100, 0⟩, ⟨0x1300, 0⟩, ⟨0x1400, 0⟩], unsizedDefault := true }

/-- The runner's initial memory (unsized locations). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0x1100), (⟨0x1200, 0⟩, 0x1100), (⟨0x1100, 0⟩, 0x0), (⟨0x1300, 0⟩, 0x0), (⟨0x1400, 0⟩, 0x0)]

/-- The runner's initial configuration: the enqueuer from `enq` to `pdone` (`X0 = head`, `X1 = tail`,
`X12 = n1`, `X13 = n2`), the dequeuer from `deq1` to `ddone1` (`X0 = head`,
`X1 = tail`); `head = tail = d`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1200), (.X12, 0x1300), (.X13, 0x1400)] 0x100000 0x100084,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1200)] 0x100088 0x100114] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/msqueue_relaxed2.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 65 steps, 1 promise). -/
def trace : List ReachPStep :=
  [.instr 0 [], .instr 0 [], .promise 0 0x1308 5120, .instr 0 [2], .instr 0 [0],
   .instr 0 [], .instr 0 [0], .instr 0 [], .instr 0 [], .instr 0 [0, 3],
   .instr 0 [], .instr 0 [], .instr 0 [0, 4], .instr 0 [], .instr 0 [],
   .instr 0 [], .instr 0 [5], .instr 0 [4], .instr 0 [], .instr 0 [0],
   .instr 0 [], .instr 0 [], .instr 0 [0, 1], .instr 0 [], .instr 0 [],
   .instr 1 [0], .instr 1 [4], .instr 1 [], .instr 1 [3], .instr 1 [],
   .instr 1 [], .instr 1 [], .instr 1 [2], .instr 1 [], .instr 1 [0, 6],
   .instr 1 [], .instr 1 [], .instr 1 [], .instr 1 [6], .instr 1 [4],
   .instr 1 [], .instr 1 [1], .instr 1 [], .instr 1 [], .instr 1 [],
   .instr 1 [], .instr 1 [4, 7], .instr 1 [], .instr 0 [7], .instr 0 [],
   .instr 0 [], .instr 1 [6], .instr 1 [7], .instr 1 [], .instr 1 [1],
   .instr 1 [], .instr 1 [], .instr 1 [], .instr 1 [0], .instr 1 [],
   .instr 1 [6, 8], .instr 1 [], .instr 1 [], .instr 1 [], .instr 1 []]

/-! ## Checkpoints

The witness is checked in segments (`ReachCheckpoint`), each its own kernel
evaluation, to bound the kernel's memory. `cpK` is the configuration after
the step its docstring names, printed by `reachA64ShowCfg`; `reachK` proves
it reachable. -/

/-- Checkpoint 1: after step 12. -/
def cp1 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1300, X3 := 0x1100, X5 := 0x1100, X8 := 0x1108, X9 := 0x1, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x10002c),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001108#64, bytes := 0 }, 3), ({ addr := 0x0000000000001200#64, bytes := 0 }, 0), ({ addr := 0x0000000000001300#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 3, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 2, view := 0, xcl := false, xclRead := 0 })], xclb := none },
     [1]),
   ((⟨{ X0 := 0x1000, X1 := 0x1200 }, ⟨false, false, false, false⟩, ∅⟩, 0x100088),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001308#64, bytes := 0 }, val := 0x00000000000000000000000000001400#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }]

theorem reach1 : Reachable Arch.armv8 300 c0 cp1 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (.refl c0)
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := c0) (tr := (trace.drop 0).take 12) (by decide +kernel)

/-- Checkpoint 2: after step 23. -/
def cp2 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1400, X3 := 0x1300, X8 := 0x1308, X9 := 0x2, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x100064),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001108#64, bytes := 0 }, 3), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4), ({ addr := 0x0000000000001300#64, bytes := 0 }, 2), ({ addr := 0x0000000000001308#64, bytes := 0 }, 1), ({ addr := 0x0000000000001400#64, bytes := 0 }, 5)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 5, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 3, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 4, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 2, view := 0, xcl := false, xclRead := 0 }), ({ addr := 0x0000000000001308#64, bytes := 0 }, { time := 1, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001400#64, bytes := 0 }, { time := 5, view := 0, xcl := false, xclRead := 0 })], xclb := none },
     []),
   ((⟨{ X0 := 0x1000, X1 := 0x1200 }, ⟨false, false, false, false⟩, ∅⟩, 0x100088),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001308#64, bytes := 0 }, val := 0x00000000000000000000000000001400#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001400#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }]

theorem reach2 : Reachable Arch.armv8 300 c0 cp2 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach1
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp1) (tr := (trace.drop 12).take 11) (by decide +kernel)

/-- Checkpoint 3: after step 45. -/
def cp3 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1400, X3 := 0x1300, X5 := 0x1300, X8 := 0x1308, X9 := 0x2, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x10006c),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001108#64, bytes := 0 }, 3), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4), ({ addr := 0x0000000000001300#64, bytes := 0 }, 2), ({ addr := 0x0000000000001308#64, bytes := 0 }, 1), ({ addr := 0x0000000000001400#64, bytes := 0 }, 5)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 5, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 3, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 4, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 2, view := 0, xcl := false, xclRead := 0 }), ({ addr := 0x0000000000001308#64, bytes := 0 }, { time := 1, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001400#64, bytes := 0 }, { time := 5, view := 0, xcl := false, xclRead := 0 })], xclb := none },
     []),
   ((⟨{ X0 := 0x1000, X1 := 0x1200, X3 := 0x1300, X4 := 0x1300, X5 := 0x1400, X6 := 0x1100, X7 := 0x1, X8 := 0x1308, X10 := 0x1 }, ⟨false, true, true, false⟩, ∅⟩, 0x1000e8),
     #[0, 0, 0, 4, 4, 4, 0, 4, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 4, 4, 4, 4, 4, 4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 6), ({ addr := 0x0000000000001108#64, bytes := 0 }, 4), ({ addr := 0x0000000000001200#64, bytes := 0 }, 4), ({ addr := 0x0000000000001300#64, bytes := 0 }, 4), ({ addr := 0x0000000000001308#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 6, vwOldNT := 0, vCAP := 4, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 6, view := 4, xcl := true, xclRead := 0 })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001308#64, bytes := 0 }, val := 0x00000000000000000000000000001400#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001400#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 1 }]

theorem reach3 : Reachable Arch.armv8 300 c0 cp3 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach2
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp2) (tr := (trace.drop 23).take 22) (by decide +kernel)

/-- Checkpoint 4: after step 64. -/
def cp4 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1400, X3 := 0x1300, X5 := 0x1400, X8 := 0x1308, X9 := 0x2, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x100084),
     #[0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 7, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001108#64, bytes := 0 }, 3), ({ addr := 0x0000000000001200#64, bytes := 0 }, 7), ({ addr := 0x0000000000001300#64, bytes := 0 }, 2), ({ addr := 0x0000000000001308#64, bytes := 0 }, 1), ({ addr := 0x0000000000001400#64, bytes := 0 }, 5)], vrNew := 0, vrOld := 7, vrOldNR := 0, vwNew := 0, vwOld := 5, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 3, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 4, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 2, view := 0, xcl := false, xclRead := 0 }), ({ addr := 0x0000000000001308#64, bytes := 0 }, { time := 1, view := 0, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001400#64, bytes := 0 }, { time := 5, view := 0, xcl := false, xclRead := 0 })], xclb := none },
     []),
   ((⟨{ X0 := 0x1000, X1 := 0x1200, X3 := 0x1300, X4 := 0x1400, X5 := 0x1400, X6 := 0x1300, X8 := 0x1308, X10 := 0x1 }, ⟨false, true, true, false⟩, ∅⟩, 0x100110),
     #[0, 0, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     #[0, 0, 0, 4, 4, 4, 4, 4, 4, 0, 4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 8), ({ addr := 0x0000000000001108#64, bytes := 0 }, 4), ({ addr := 0x0000000000001200#64, bytes := 0 }, 7), ({ addr := 0x0000000000001300#64, bytes := 0 }, 4), ({ addr := 0x0000000000001308#64, bytes := 0 }, 4), ({ addr := 0x0000000000001400#64, bytes := 0 }, 4)], vrNew := 4, vrOld := 4, vrOldNR := 0, vwNew := 4, vwOld := 8, vwOldNT := 0, vCAP := 4, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 8, view := 4, xcl := true, xclRead := 0 }), ({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 7, view := 4, xcl := true, xclRead := 0 })], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001308#64, bytes := 0 }, val := 0x00000000000000000000000000001400#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001400#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001400#128, tid := 1 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001400#128, tid := 1 }]

theorem reach4 : Reachable Arch.armv8 300 c0 cp4 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach3
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp3) (tr := (trace.drop 45).take 19) (by decide +kernel)

/-- **`msqueue_relaxed2.kl`'s stale dequeue is reachable** from the runner's configuration, at certification
fuel `300` (the runner's `-fuel`). -/
theorem msqueue_relaxed2_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧
      ¬ (reachXReg c 1 .X10 = some 1 ∧ reachXReg c 1 .X11 = some 2) :=
  reach_witness_promise_from Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach4
    (tr := trace.drop 64) (by decide +kernel)

end Kraken.Promising.Reach.MsqueueRelaxed2

#print axioms Kraken.Promising.Reach.MsqueueRelaxed2.msqueue_relaxed2_reachable

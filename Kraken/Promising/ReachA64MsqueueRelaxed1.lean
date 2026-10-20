/-
**`msqueue_relaxed1.kl` is `Sometimes`: the dequeuer can receive stale data**
.

The Michael-Scott queue's CASes are plain (no release), so the enqueuer may
promise the link `tail.next := n1` and the tail swing before its data store
`[n1] := 1`; the dequeuer then follows the link and reads `0`.
`msqueue_relaxed1_reachable`: from the runner's exact initial configuration
(`c0`, checked by `reachA64RunnerMatches`), under `Arch.armv8` at the
runner's certification fuel `300`, some final configuration violates the
`.kl`'s `forall (1:X10=1)`. The witness has two promise steps
(`ReachCertCore`).
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.ReachA64Checkpoint
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.MsqueueRelaxed1

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `msqueue_relaxed1.kl`, verbatim. -/
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
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1200), (.X12, 0x1300), (.X13, 0x1400)] 0x100000 0x100044,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1200)] 0x100048 0x100090] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/msqueue_relaxed1.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 30 steps, 2 promises). -/
def trace : List ReachPStep :=
  [.instr 0 [], .instr 0 [], .promise 0 0x1200 4864, .promise 0 0x1108 4864, .instr 0 [3],
   .instr 0 [0], .instr 0 [], .instr 0 [0], .instr 0 [], .instr 0 [],
   .instr 0 [0, 2], .instr 0 [], .instr 0 [], .instr 0 [0, 1], .instr 0 [],
   .instr 0 [], .instr 1 [0], .instr 1 [1], .instr 1 [], .instr 1 [2],
   .instr 1 [], .instr 1 [], .instr 1 [], .instr 1 [0], .instr 1 [],
   .instr 1 [0, 4], .instr 1 [], .instr 1 [], .instr 1 [], .instr 1 []]

/-! ## Checkpoints

The witness is checked in segments (`ReachCheckpoint`), each its own kernel
evaluation, to bound the kernel's memory. `cpK` is the configuration after
the step its docstring names, printed by `reachA64ShowCfg`; `reachK` proves
it reachable. -/

/-- Checkpoint 1: after step 4. -/
def cp1 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1300, X9 := 0x1, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x100008),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [1, 2]),
   ((⟨{ X0 := 0x1000, X1 := 0x1200 }, ⟨false, false, false, false⟩, ∅⟩, 0x100048),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }]

theorem reach1 : Reachable Arch.armv8 300 c0 cp1 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (.refl c0)
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := c0) (tr := (trace.drop 0).take 4) (by decide +kernel)

/-- Checkpoint 2: after step 6. -/
def cp2 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1300, X3 := 0x1100, X9 := 0x1, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x100010),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001200#64, bytes := 0 }, 0), ({ addr := 0x0000000000001300#64, bytes := 0 }, 3)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 3, view := 0, xcl := false })], xclb := none },
     [1, 2]),
   ((⟨{ X0 := 0x1000, X1 := 0x1200 }, ⟨false, false, false, false⟩, ∅⟩, 0x100048),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach2 : Reachable Arch.armv8 300 c0 cp2 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach1
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp1) (tr := (trace.drop 4).take 2) (by decide +kernel)

/-- Checkpoint 3: after step 9. -/
def cp3 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1300, X3 := 0x1100, X8 := 0x1108, X9 := 0x1, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x10001c),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001108#64, bytes := 0 }, 0), ({ addr := 0x0000000000001200#64, bytes := 0 }, 0), ({ addr := 0x0000000000001300#64, bytes := 0 }, 3)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 3, view := 0, xcl := false })], xclb := none },
     [1, 2]),
   ((⟨{ X0 := 0x1000, X1 := 0x1200 }, ⟨false, false, false, false⟩, ∅⟩, 0x100048),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach3 : Reachable Arch.armv8 300 c0 cp3 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach2
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp2) (tr := (trace.drop 6).take 3) (by decide +kernel)

/-- Checkpoint 4: after step 13. -/
def cp4 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1300, X3 := 0x1100, X5 := 0x1100, X8 := 0x1108, X9 := 0x1, X12 := 0x1300, X13 := 0x1400 }, ⟨false, false, false, false⟩, ∅⟩, 0x10002c),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001108#64, bytes := 0 }, 2), ({ addr := 0x0000000000001200#64, bytes := 0 }, 0), ({ addr := 0x0000000000001300#64, bytes := 0 }, 3)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 2, view := 0, xcl := true }), ({ addr := 0x0000000000001300#64, bytes := 0 }, { time := 3, view := 0, xcl := false })], xclb := none },
     [1]),
   ((⟨{ X0 := 0x1000, X1 := 0x1200 }, ⟨false, false, false, false⟩, ∅⟩, 0x100048),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [])]
  #[{ loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000001300#128, tid := 0 }, { loc := { addr := 0x0000000000001300#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }]

theorem reach4 : Reachable Arch.armv8 300 c0 cp4 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach3
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp3) (tr := (trace.drop 9).take 4) (by decide +kernel)

/-- **`msqueue_relaxed1.kl`'s stale dequeue is reachable** from the runner's configuration, at certification
fuel `300` (the runner's `-fuel`). -/
theorem msqueue_relaxed1_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧
      ¬ reachXReg c 1 .X10 = some 1 :=
  reach_witness_promise_from Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach4
    (tr := trace.drop 13) (by decide +kernel)

end Kraken.Promising.Reach.MsqueueRelaxed1

#print axioms Kraken.Promising.Reach.MsqueueRelaxed1.msqueue_relaxed1_reachable

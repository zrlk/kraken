/-
**`treiber2_relaxed.kl` is `Sometimes`: a pop can return stale data**
.

The Treiber stack with no ordering at all (plain `LDR` of `top`, plain
`CAS`): a pusher may promise its `top` update before its node's data store,
so the other thread's pop reads stale data.
`treiber2_relaxed_reachable`: from the runner's exact initial configuration
(`c0`, checked by `reachA64RunnerMatches`), under `Arch.armv8` at the
runner's certification fuel `300`, some final configuration violates the
`.kl`'s `forall` (each thread pops the other's node with its value). The
witness has one promise step (`ReachCertCore`); it was found by the
explorer with `-promises 1` (the unbounded exploration does not finish in
10 minutes), which only restricts the search: every step of the witness is
a step of `succs`.
-/
import Kraken.Promising.ReachA64Core
import Kraken.Promising.ReachCertCore
import Kraken.Promising.ReachA64Checkpoint
import Kraken.Promising.CertifyAArch64
import Kraken.AArch64.Parser

namespace Kraken.Promising.Reach.Treiber2Relaxed

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The `code` block of `treiber2_relaxed.kl`, verbatim. -/
def code : Program := parseAArch64("
worker:
  STR W9,[X1]
push:
  LDR X2,[X0]
  STR X2,[X1,#8]
  MOV X3,X2
  CAS X3,X1,[X0]
  CMP X3,X2
  B.NE push
pop:
  LDR X2,[X0]
  CBZ X2,done
  LDR X4,[X2,#8]
  MOV X3,X2
  CAS X3,X4,[X0]
  CMP X3,X2
  B.NE pop
  MOV X10,X2
  LDR W11,[X2]
  B done
done:
")

/-- The runner's declarations for the untyped header: unsized. -/
def decls : Decls := { locs := [⟨0x1000, 0⟩, ⟨0x1100, 0⟩, ⟨0x1200, 0⟩], unsizedDefault := true }

/-- The runner's initial memory (unsized locations). -/
def initMem : List (Loc × Val) := [(⟨0x1000, 0⟩, 0x0), (⟨0x1100, 0⟩, 0x0), (⟨0x1200, 0⟩, 0x0)]

/-- The runner's initial configuration: both threads from `worker` to `done`, `X0 = top`;
thread 0 with `X1 = n1`, `X9 = 1`, thread 1 with `X1 = n2`, `X9 = 2`. -/
def c0 : Config isa := Config.init
  [reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1100), (.X9, 0x1)] 0x100000 0x100044,
   reachA64Thread (reachA64Exe code) decls [(.X0, 0x1000), (.X1, 0x1200), (.X9, 0x2)] 0x100000 0x100044] initMem

/-- The `.kl` source. -/
def kl : String := include_str "../Examples/LockFree/AArch64/treiber2_relaxed.kl"

/-- info: true -/
#guard_msgs in
#eval reachA64RunnerMatches kl c0

/-- The explorer's witness (`reach_trace.py --promises`, 35 steps, 1 promise). -/
def trace : List ReachPStep :=
  [.instr 0 [1], .instr 0 [0], .instr 0 [2], .instr 0 [], .instr 0 [0, 3],
   .instr 0 [], .instr 0 [], .promise 1 0x1000 4608, .instr 0 [4], .instr 0 [],
   .instr 1 [5], .instr 1 [3], .instr 1 [6], .instr 1 [], .instr 0 [6],
   .instr 0 [], .instr 0 [4, 7], .instr 0 [], .instr 0 [], .instr 0 [],
   .instr 0 [0], .instr 0 [], .instr 1 [3, 4], .instr 1 [], .instr 1 [],
   .instr 1 [7], .instr 1 [], .instr 1 [2], .instr 1 [], .instr 1 [7, 8],
   .instr 1 [], .instr 1 [], .instr 1 [], .instr 1 [1], .instr 1 []]

/-! ## Checkpoints

The witness is checked in segments (`ReachCheckpoint`), each its own kernel
evaluation, to bound the kernel's memory. `cpK` is the configuration after
the step its docstring names, printed by `reachA64ShowCfg`; `reachK` proves
it reachable. -/

/-- Checkpoint 1: after step 10. -/
def cp1 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X9 := 0x1 }, ⟨false, true, true, false⟩, ∅⟩, 0x100024),
     #[0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 1), ({ addr := 0x0000000000001108#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 4, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 4, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 3, view := 0, xcl := true }), ({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 1, view := 0, xcl := false }), ({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 2, view := 0, xcl := false })], xclb := none },
     []),
   ((⟨{ X0 := 0x1000, X1 := 0x1200, X9 := 0x2 }, ⟨false, false, false, false⟩, ∅⟩, 0x100000),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 0, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [], xclb := none },
     [4])]
  #[{ loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000000000#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001100#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001200#128, tid := 1 }]

theorem reach1 : Reachable Arch.armv8 300 c0 cp1 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq (.refl c0)
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := c0) (tr := (trace.drop 0).take 10) (by decide +kernel)

/-- Checkpoint 2: after step 11. -/
def cp2 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X9 := 0x1 }, ⟨false, true, true, false⟩, ∅⟩, 0x100024),
     #[0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 1), ({ addr := 0x0000000000001108#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 4, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 4, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 3, view := 0, xcl := true }), ({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 1, view := 0, xcl := false }), ({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 2, view := 0, xcl := false })], xclb := none },
     []),
   ((⟨{ X0 := 0x1000, X1 := 0x1200, X9 := 0x2 }, ⟨false, false, false, false⟩, ∅⟩, 0x100004),
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001200#64, bytes := 0 }, 5)], vrNew := 0, vrOld := 0, vrOldNR := 0, vwNew := 0, vwOld := 5, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 5, view := 0, xcl := false })], xclb := none },
     [4])]
  #[{ loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000000000#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001100#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001200#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }]

theorem reach2 : Reachable Arch.armv8 300 c0 cp2 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach1
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp1) (tr := (trace.drop 10).take 1) (by decide +kernel)

/-- Checkpoint 3: after step 13. -/
def cp3 : Config isa :=
  reachA64Cfg c0
  [((⟨{ X0 := 0x1000, X1 := 0x1100, X2 := 0x1200, X9 := 0x1 }, ⟨false, true, true, false⟩, ∅⟩, 0x100024),
     #[0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 4), ({ addr := 0x0000000000001100#64, bytes := 0 }, 1), ({ addr := 0x0000000000001108#64, bytes := 0 }, 2)], vrNew := 0, vrOld := 4, vrOldNR := 0, vwNew := 0, vwOld := 3, vwOldNT := 0, vCAP := 4, vRel := 0, fwdb := [({ addr := 0x0000000000001000#64, bytes := 0 }, { time := 3, view := 0, xcl := true }), ({ addr := 0x0000000000001100#64, bytes := 0 }, { time := 1, view := 0, xcl := false }), ({ addr := 0x0000000000001108#64, bytes := 0 }, { time := 2, view := 0, xcl := false })], xclb := none },
     []),
   ((⟨{ X0 := 0x1000, X1 := 0x1200, X2 := 0x1100, X9 := 0x2 }, ⟨false, false, false, false⟩, ∅⟩, 0x10000c),
     #[0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     #[0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     { coh := [({ addr := 0x0000000000001000#64, bytes := 0 }, 3), ({ addr := 0x0000000000001200#64, bytes := 0 }, 5), ({ addr := 0x0000000000001208#64, bytes := 0 }, 6)], vrNew := 0, vrOld := 3, vrOldNR := 0, vwNew := 0, vwOld := 6, vwOldNT := 0, vCAP := 0, vRel := 0, fwdb := [({ addr := 0x0000000000001200#64, bytes := 0 }, { time := 5, view := 0, xcl := false }), ({ addr := 0x0000000000001208#64, bytes := 0 }, { time := 6, view := 3, xcl := false })], xclb := none },
     [4])]
  #[{ loc := { addr := 0x0000000000001100#64, bytes := 0 }, val := 0x00000000000000000000000000000001#128, tid := 0 }, { loc := { addr := 0x0000000000001108#64, bytes := 0 }, val := 0x00000000000000000000000000000000#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001100#128, tid := 0 }, { loc := { addr := 0x0000000000001000#64, bytes := 0 }, val := 0x00000000000000000000000000001200#128, tid := 1 }, { loc := { addr := 0x0000000000001200#64, bytes := 0 }, val := 0x00000000000000000000000000000002#128, tid := 1 }, { loc := { addr := 0x0000000000001208#64, bytes := 0 }, val := 0x00000000000000000000000000001100#128, tid := 1 }]

theorem reach3 : Reachable Arch.armv8 300 c0 cp3 :=
  reach_segment Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach2
    (reachA64Cfg_sameStatic c0 _ _ (by decide)) (c := cp2) (tr := (trace.drop 11).take 2) (by decide +kernel)

/-- **`treiber2_relaxed.kl`'s stale pop is reachable** from the runner's configuration, at certification
fuel `300` (the runner's `-fuel`). -/
theorem treiber2_relaxed_reachable :
    ∃ c, Reachable Arch.armv8 300 c0 c ∧ c.final = true ∧
      ¬ ((reachXReg c 0 .X10 = some 0x1100 ∧ reachXReg c 0 .X11 = some 1 ∧
          reachXReg c 1 .X10 = some 0x1200 ∧ reachXReg c 1 .X11 = some 2) ∨
        (reachXReg c 0 .X10 = some 0x1200 ∧ reachXReg c 0 .X11 = some 2 ∧
          reachXReg c 1 .X10 = some 0x1100 ∧ reachXReg c 1 .X11 = some 1)) :=
  reach_witness_promise_from Arch.armv8 300 reachA64ExecK_eq reachA64Deps_eq reach3
    (tr := trace.drop 13) (by decide +kernel)

end Kraken.Promising.Reach.Treiber2Relaxed

#print axioms Kraken.Promising.Reach.Treiber2Relaxed.treiber2_relaxed_reachable

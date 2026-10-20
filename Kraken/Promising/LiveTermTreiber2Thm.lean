/-
**Stage 4: termination of the A64 Treiber family on the
semantic machine, stated explicitly.**

Every theorem is `TermBoundSem Arch.armv8 fuel c0` (`LiveTerm.lean`): at
every `fuel`, one bound `K` such that every semantic trace (`TraceSem`, which
stutters only at final configurations) from `c0` is final at index `K`.
**There is no fairness hypothesis.** `K` depends on `fuel` and on the number
of threads (`termBoundSem_of_threadRank`: the rank bound
`N = threads * (2 + fuel)` and the promise headroom `fuel` per thread), and
on nothing else. The result is about the fixed-fuel semantic machine: a run
whose promises need longer and longer certifications is not a `TraceSem` at
any one fuel.

| worker | `.kl` | statements | proofs |
|---|---|---|---|
| `treiber2DWorker` | `treiber2.kl` | `treiber2_term_sem` (+ `_concrete`) | `LiveTermTreiber2.lean` |
| `treiber2ArmWorker` | `treiber2_arm.kl` | `treiber2_arm_term_sem_all`, `treiber2_arm_term_sem` (+ `_concrete`) | clone `LiveTermTreiber2Arm.lean` |
| `Reach.Treiber2Relaxed.code` | `treiber2_relaxed.kl` | `treiber2_relaxed_term_sem_all`, `treiber2_relaxed_term_sem` | clone `LiveTermTreiber2Relaxed.lean` |

The two-thread forms take the hypotheses of the existing safety theorems
(`treiber2_envG_whole`, `treiber2_arm_envG_whole`) without reachability and
finality; `hn`, `hn0`, `hn1`, `hT0` are not needed. The `_all` forms take any
number of threads, each a start state whose node's link word `n + 8` is not
`top` (`t ≠ n + 8`: a worker's `STR X2,[X1,#8]` is not a write to `top`; the
safety theorems assume it too). `treiber2_relaxed.kl` is not safe
(`treiber2_relaxed_reachable`) but terminates; its runner configuration
declares unsized locations, so `StartWR` (no declarations) does not cover it.
-/
import Kraken.Promising.LiveTermTreiber2
import Kraken.Promising.LiveTermTreiber2Arm
import Kraken.Promising.LiveTermTreiber2Relaxed
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2
import Kraken.Promising.SLR.EnvG.A64Treiber2ArmWhole

namespace Kraken.Promising.Live.TermTreiber2

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.Term
open Kraken.Promising.SLR.EnvG.Treiber2 (treiber2DWorker StartWD wLayout2D wWorker0 wWorker1 wWorker0_start
  wWorker1_start)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2InitMem)

/-- **The two-thread Treiber stack `treiber2.kl` terminates on the semantic
machine under every schedule** (no fairness): at the hypotheses of
`Treiber2.treiber2_envG_whole` without its reachability and finality
premises (`hn`, `hn0`, `hn1`, `hT0` are not needed). At every fuel, one bound
`K` on every semantic trace from the start configuration. -/
theorem treiber2_term_sem {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2DWorker)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (_hn : n0 ≠ n1) (_hn0 : n0 ≠ 0) (_hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWD (layout := l) t n0 1 s0) (h1 : StartWD (layout := l) t n1 2 s1)
    (_hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    TermBoundSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_term_sem_gen (layout := l) t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, 1, h0, ht0⟩
    · exact ⟨n1, 2, h1, ht1⟩

section
attribute [local instance] wLayout2D

/-- **`treiber2.kl` at the runner's layout and threads terminates on the
semantic machine under every schedule**: concrete instance of
`treiber2_term_sem` (the start configuration of
`Treiber2.treiber2_envG_whole_concrete`). -/
theorem treiber2_term_sem_concrete {fuel : Nat} :
    TermBoundSem Arch.armv8 fuel (Config.init [wWorker0, wWorker1] treiber2InitMem : Config isa) :=
  treiber2_term_sem wLayout2D topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wWorker0_start wWorker1_start (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TermTreiber2

namespace Kraken.Promising.Live.TermTreiber2Arm

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.Term
open Kraken.Promising.SLR.EnvG.Treiber2Arm (treiber2ArmWorker StartWA wLayoutA wWorkerA0 wWorkerA1 wWorkerA0_start
  wWorkerA1_start)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2Data (treiber2InitMem)

/-- **The `treiber2_arm.kl` workers terminate on the semantic machine under
every schedule** (no fairness): any number of `treiber2ArmWorker` threads on
one valid layout, sharing `top`, each with its own node whose link word is
not `top`. -/
theorem treiber2_arm_term_sem_all {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, ∃ n d, StartWA (layout := l) t n d s ∧ t ≠ n + 8) :
    TermBoundSem Arch.armv8 fuel (Config.init states initMem : Config isa) :=
  treiber2_arm_term_sem_gen (layout := l) t hs

/-- **`treiber2_arm.kl` terminates on the semantic machine under every
schedule**: at the hypotheses of `Treiber2Arm.treiber2_arm_envG_whole`
without its reachability and finality premises. -/
theorem treiber2_arm_term_sem {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2ArmWorker)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (_hn : n0 ≠ n1) (_hn0 : n0 ≠ 0) (_hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWA (layout := l) t n0 1 s0) (h1 : StartWA (layout := l) t n1 2 s1)
    (_hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    TermBoundSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_arm_term_sem_all l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, 1, h0, ht0⟩
    · exact ⟨n1, 2, h1, ht1⟩

section
attribute [local instance] wLayoutA

/-- **`treiber2_arm.kl` at the runner's layout and threads terminates on the
semantic machine under every schedule** (the start configuration of
`Treiber2Arm.treiber2_arm_envG_whole_concrete`). -/
theorem treiber2_arm_term_sem_concrete {fuel : Nat} :
    TermBoundSem Arch.armv8 fuel (Config.init [wWorkerA0, wWorkerA1] treiber2InitMem : Config isa) :=
  treiber2_arm_term_sem wLayoutA topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wWorkerA0_start wWorkerA1_start (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TermTreiber2Arm

namespace Kraken.Promising.Live.TermTreiber2Relaxed

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.Term
open Kraken.Promising.Reach.Treiber2Relaxed (StartWR)

/-- **The `treiber2_relaxed.kl` workers terminate on the semantic machine
under every schedule** (no fairness): any number of
`Reach.Treiber2Relaxed.code` threads on one valid layout, sharing `top`, each
with its own node whose link word is not `top`. -/
theorem treiber2_relaxed_term_sem_all {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l Reach.Treiber2Relaxed.code)] (t : BitVec 64) {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : ∀ s ∈ states, ∃ n d, StartWR (layout := l) t n d s ∧ t ≠ n + 8) :
    TermBoundSem Arch.armv8 fuel (Config.init states initMem : Config isa) :=
  treiber2_relaxed_term_sem_gen (layout := l) t hs

/-- **`treiber2_relaxed.kl`'s two workers terminate on the semantic machine
under every schedule** (the shape of `treiber2_envG_whole`'s start). -/
theorem treiber2_relaxed_term_sem {fuel : Nat} (l : _root_.Layout)
    [Executable.ValidLayout (l Reach.Treiber2Relaxed.code)] (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8)
    (ht1 : t ≠ n1 + 8) {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWR (layout := l) t n0 1 s0) (h1 : StartWR (layout := l) t n1 2 s1) :
    TermBoundSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_relaxed_term_sem_all l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, 1, h0, ht0⟩
    · exact ⟨n1, 2, h1, ht1⟩

end Kraken.Promising.Live.TermTreiber2Relaxed

/-
**Part 2: the two threads of the x64
`treiber_pp.kl`** (`Kraken/Examples/LockFree/X64/treiber_pp.kl`, the x64 port
of the Treiber proof's AArch64 `treiber_pp.kl`), split per thread as
`EnvG/TreiberSmoke.lean` splits the AArch64 one, and the structural
hypotheses of `ThreadRuleRXF.ofSafelyEnvGFCX` /
`noFaultRuleF_ofSafelyEnvGFCX_struct` (`EnvG/X64RmwFailGhost.lean`):

- `*_phase1FX`: `Phase1TreeFX` by `dirs_phase1FX` (single-access trees; the
  `lock cmpxchgq`s are release-kind RMWs that may fail);
- `*_noFault`: `DirsNoFault` by `dirs_no_fault` (whose `je` step, the x64 Treiber proof's
  local `dirs_no_faultX`, is shared).

-/
import Kraken.Promising.SLR.EnvG.X64RmwFailGhost
import Kraken.X64.Parser

namespace Kraken.Promising.X64.EnvG.TreiberX

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.X64.EnvG
open Kraken.X64.Parser

/-- **The pusher** of the x64 `treiber_pp.kl` (`%rdi = top`, `%rbx = n1`):
write the data word `1`, link the node to the current `top`, publish it by
`lock cmpxchgq`, retry on failure. -/
def treiberPusherX : Program := parse("
pusher:
  movl $1,(%rbx)
push:
  movq (%rdi),%rax
  movq %rax,8(%rbx)
  lock cmpxchgq %rbx,(%rdi)
  jne push
  jmp pdone
pdone:
")

/-- **The popper** of the x64 `treiber_pp.kl` (`%rdi = top`): read `top`
until non-empty, read the link, swing `top` by `lock cmpxchgq`, retry on
failure; then the node in `%r10`, its data word in `%r11d`. -/
def treiberPopperX : Program := parse("
popper:
  movq (%rdi),%rax
  testq %rax,%rax
  je popper
  movq 8(%rax),%rcx
  lock cmpxchgq %rcx,(%rdi)
  jne popper
  movq %rax,%r10
  movl (%rax),%r11d
  jmp qdone
qdone:
")

/-- info: 9 -/
#guard_msgs in
#eval treiberPusherX.length

/-- info: 11 -/
#guard_msgs in
#eval treiberPopperX.length

/- `prop_ite`: a property of both branches holds of an `if`, at any
decidability instance (the `je` flag test keeps a `CondCode.interp` instance
after `simp`, which `split`, `rw [if_pos]` and `simp` do not see through).
An alias of `Kraken.Promising.prop_ite` (`Promising/SeqLinkTerm.lean`), which
the shared `dirs_no_fault` tactics now use (same statement). -/
hoist_alias [Kraken.Promising.prop_ite ↦ Kraken.Promising.X64.EnvG.TreiberX.prop_ite]

variable [layout : _root_.Layout]

theorem treiberPusherX_phase1FX [Executable.ValidLayout (layout treiberPusherX)] :
    Phase1TreeFX (layout treiberPusherX) := by
  refine phase1TreeFX_of_dirs ?_
  dirs_phase1FX treiberPusherX
  all_goals simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]

theorem treiberPopperX_phase1FX [Executable.ValidLayout (layout treiberPopperX)] :
    Phase1TreeFX (layout treiberPopperX) := by
  refine phase1TreeFX_of_dirs ?_
  dirs_phase1FX treiberPopperX
  all_goals try simp [_root_.RelRegOrMem.interp, Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2]
  -- `je popper`: `prop_ite`
  all_goals (refine prop_ite (P := fun x => DetAccess (toEv {} x) ∧
      SingleAccessS2 True (fun _ _ => True) (fun _ _ _ => True) True (toEv {} x)) ?_ ?_ <;>
    simp [Kraken.Promising.X64.toEv, DetAccess, SingleAccessS2])

theorem treiberPusherX_noFault : DirsNoFault (layout treiberPusherX) := by
  dirs_no_fault treiberPusherX

theorem treiberPopperX_noFault : DirsNoFault (layout treiberPopperX) := by
  dirs_no_fault treiberPopperX

end Kraken.Promising.X64.EnvG.TreiberX

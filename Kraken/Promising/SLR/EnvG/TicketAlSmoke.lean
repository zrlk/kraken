/-
**Item 2, part 1: the `ldaddal` ticket lock
worker, its static checks and its RMW VC** (on `EnvGTDR`,
`EnvG/TicketREnv.lean`).

The worker of `ticketlock_al2.kl` / `ticketlock_al3.kl`: `ticketlock2.kl`'s
worker (`TicketLock.tkWorker`) with the ticket taken by `LDADDAL`
(acquire-release) instead of `LDADDA`.

- `tkWorkerAl`; `tkWorkerAl_rmwLive`, `tkWorkerAl_phase1R` (`Phase1TreeR`:
  the `ldaddal` is a release-kind RMW, by `dirs_phase1R`),
  `tkWorkerAl_noFault`; `StartStateAl` (`TicketLock.StartState` at
  `tkWorkerAl`).
- `EAl P hL tid`: the environment (`EnvGTDR` with `tkPlan P` and `disp P`);
  `vc_ldaddal` (`vc_ldadda` for the `.acqRel` RMW: `tkPlan` never releases
  at `next`). The VCs of the loads and stores of `EnvG/TicketLockVC.lean`
  apply to `EAl` as they are (same `ok` and `step`, `envGTDR_step_eq`).
-/
import Kraken.Promising.SLR.EnvG.SafelyBridge
import Kraken.Promising.SLR.EnvG.A64Answers
import Kraken.Promising.SLR.EnvG.TicketRA64Link
import Kraken.Promising.SLR.EnvG.TicketLockVC
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.EnvG.TicketLock

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **The `ldaddal` ticket lock worker** of `ticketlock_al2.kl` (verbatim
`code` block: 11 instructions and 3 labels, 14 directives). -/
def tkWorkerAl : Program := parseAArch64("
worker:
  MOV W6,#1
  LDADDAL W6,W3,[X0]
spin:
  LDAR W4,[X1]
  CMP W4,W3
  B.NE spin
  LDR W5,[X2]
  ADD W5,W5,#1
  STR W5,[X2]
  ADD W4,W3,#1
  STLR W4,[X1]
  B done
done:
")

/-- info: 14 -/
#guard_msgs in
#eval tkWorkerAl.length

section Static

variable [layout : _root_.Layout]

theorem tkWorkerAl_rmwLive : (layout tkWorkerAl).rmwLive = true := by
  rw [Layout.apply_rmwLive]; decide

theorem tkWorkerAl_phase1R [Executable.ValidLayout (layout tkWorkerAl)] :
    Phase1TreeR Arch.armv8 (layout tkWorkerAl) :=
  phase1TreeR_of_dirs (by dirs_phase1R tkWorkerAl)

theorem tkWorkerAl_noFault : DirsNoFault (layout tkWorkerAl) := by dirs_no_fault' tkWorkerAl

/-- A `tkWorkerAl` thread at its start, with `next`, `owner` and counter
addresses `x`, `o`, `c` (`StartState` at `tkWorkerAl`). -/
structure StartStateAl (x o c : BitVec 64) (s : isa.State) : Prop where
  exe : s.exe = layout tkWorkerAl
  decls : s.decls = {}
  endPc : s.endPc = (layout tkWorkerAl).addrOf tkWorkerAl.length
  pc : s.st.2 = (layout tkWorkerAl).addrOf 0
  x0 : s.st.1.regs.X0.toBitVec = x
  x1 : s.st.1.regs.X1.toBitVec = o
  x2 : s.st.1.regs.X2.toBitVec = c
  dx : Mem.loadInt s.st.1.dmem x 4 = none
  dO : Mem.loadInt s.st.1.dmem o 4 = none
  dc : Mem.loadInt s.st.1.dmem c 4 = none

end Static

/-! ## The environment and the `ldaddal` VC -/

/-- The `ldaddal` ticket lock's environment for thread `tid`. -/
noncomputable abbrev EAl (I : ISA) (P : Sys) (hL : Locs P) (tid : Nat) : SharedEnv :=
  EnvGTDR I Arch.armv8 tid (tkPlan P) (disp P hL.xo)

variable {I : ISA} {P : Sys} (hL : Locs P) {tid : Nat}

/-- **The `ldaddal` VC** (`vc_ldadda` for the acquire-release RMW): the
hand-out of ticket `t = old < N + 1`, its token, and the own `next` message
of value `t + 1`. -/
theorem vc_ldaddal (σ : State I) (h : Start P tid σ) {op : Val → Option Val}
    (hop : ∀ x, op x = some ((x.setWidth 32 + 1#32).setWidth 128)) :
    (EAl I P hL tid).ok (.rmw .acqRel P.X.addr P.X.bytes op) σ ∧
      ∀ old (σ' : State I), (EAl I P hL tid).step (.rmw .acqRel P.X.addr P.X.bytes op) σ old σ' →
        Spin P tid old.toNat σ' :=
  vc_ldaddK hL (by decide) σ h hop

end Kraken.Promising.SLR.EnvG.TicketLock

#print axioms Kraken.Promising.SLR.EnvG.TicketLock.tkWorkerAl_phase1R
#print axioms Kraken.Promising.SLR.EnvG.TicketLock.vc_ldaddal

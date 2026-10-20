/-
**Stage 3: the SWP spinlock families** —
promise-free deadlock-freedom and one-shot per-thread liveness of
`spinlock_swp2/3` (`SWPA` lock, `STLR` unlock; `spin_swp_live_pf`,
`spin_swp_live_oneShot_pf`) and `spinlock_swpl2/3` (`SWPA` lock, `SWPL`
unlock; `spin_swpl_live_pf`, `spin_swpl_live_oneShot_pf`) under weak and
memory fairness, on valid layouts; and at concrete layouts with no
hypothesis left. Instances of `SpinSwpPF.swp_live_pf_gen` and
`swp_live_oneShot_pf_gen` at `SpinSwpTrees.swpCode`/`swplCode`. The
statements use the start states of the existing safety theorems
(`SwpPublic.StartState`, `SwplLock.StartState`).
-/
import Kraken.Promising.LiveSpinSwpPF

namespace Kraken.Promising.Live.SpinSwpFam

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live
open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.SpinSwpPF Kraken.Promising.Live.SpinSwp
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

section General

variable [layout : _root_.Layout]

theorem startG_swp {l c : BitVec 64} {s : isa.State} (h : SLR.SwpPublic.StartState l c s) :
    StartG swpWorker l c s :=
  ⟨h.exe, h.decls, h.endPc, h.pc, h.x0, h.x1, h.dl, h.dc⟩

theorem startG_swpl {l c : BitVec 64} {s : isa.State} (h : SLR.EnvG.SwplLock.StartState l c s) :
    StartG swplWorker l c s :=
  ⟨h.exe, h.decls, h.endPc.trans (by rw [show swplWorker.length = 16 by decide]), h.pc, h.x0, h.x1, h.dl, h.dc⟩

/-- **Promise-free deadlock-freedom of the SWP spinlock** (`SWPA`/`STLR`,
Stage 3, promise-free fragment): on a valid layout of `swpWorker`, on every
promise-free stuttering trace from a start configuration under weak fairness
and memory fairness, if a thread waits in its try/spin loop, then some thread
not yet past its release later is. -/
theorem spin_swp_live_pf [Executable.ValidLayout (layout swpWorker)] (fuel : Nat) : SwpSpinLivePF fuel :=
  (swp_live_pf_gen swpCode fuel).mono (fun _ _ _ => startG_swp) fun _ h => h

/-- **Per-thread liveness of the one-shot SWP workers** (promise-free
fragment). A property of these one-shot programs, not starvation-freedom of
the lock. -/
theorem spin_swp_live_oneShot_pf [Executable.ValidLayout (layout swpWorker)] (fuel : Nat) :
    SwpSpinLiveOneShotPF fuel :=
  (swp_live_oneShot_pf_gen swpCode fuel).mono fun _ _ _ => startG_swp

/-- **Promise-free deadlock-freedom of the SWPL spinlock** (`SWPA`/`SWPL`,
Stage 3, promise-free fragment), on a valid layout of `swplWorker`. -/
theorem spin_swpl_live_pf [Executable.ValidLayout (layout swplWorker)] (fuel : Nat) : SwplSpinLivePF fuel :=
  (swp_live_pf_gen swplCode fuel).mono (fun _ _ _ => startG_swpl) fun _ h => h

/-- **Per-thread liveness of the one-shot SWPL workers** (promise-free
fragment). A property of these one-shot programs, not starvation-freedom of
the lock. -/
theorem spin_swpl_live_oneShot_pf [Executable.ValidLayout (layout swplWorker)] (fuel : Nat) :
    SwplSpinLiveOneShotPF fuel :=
  (swp_live_oneShot_pf_gen swplCode fuel).mono fun _ _ _ => startG_swpl

end General

/-! ## Concrete instances -/

/-- A concrete layout of `swpWorker`: text at `0x100000`, each directive its
`fakeSize`. -/
@[reducible] def swpLiveLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize swpWorker

instance swpLiveValid : Executable.ValidLayout (swpLiveLayout swpWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- A concrete layout of `swplWorker`. -/
@[reducible] def swplLiveLayout : _root_.Layout := Kraken.Layout.ofSize 0x100000 Directive.fakeSize swplWorker

instance swplLiveValid : Executable.ValidLayout (swplLiveLayout swplWorker) :=
  Executable.validLayout_ofSize_fakeSize _ _ (by decide) (by decide)

/-- `spin_swp_live_pf` at the concrete layout `swpLiveLayout`: no hypothesis left. -/
theorem spin_swp_live_pf_concrete (fuel : Nat) : @SwpSpinLivePF swpLiveLayout fuel :=
  @spin_swp_live_pf swpLiveLayout swpLiveValid fuel

/-- `spin_swp_live_oneShot_pf` at the concrete layout `swpLiveLayout`. -/
theorem spin_swp_live_oneShot_pf_concrete (fuel : Nat) : @SwpSpinLiveOneShotPF swpLiveLayout fuel :=
  @spin_swp_live_oneShot_pf swpLiveLayout swpLiveValid fuel

/-- `spin_swpl_live_pf` at the concrete layout `swplLiveLayout`: no hypothesis left. -/
theorem spin_swpl_live_pf_concrete (fuel : Nat) : @SwplSpinLivePF swplLiveLayout fuel :=
  @spin_swpl_live_pf swplLiveLayout swplLiveValid fuel

/-- `spin_swpl_live_oneShot_pf` at the concrete layout `swplLiveLayout`. -/
theorem spin_swpl_live_oneShot_pf_concrete (fuel : Nat) : @SwplSpinLiveOneShotPF swplLiveLayout fuel :=
  @spin_swpl_live_oneShot_pf swplLiveLayout swplLiveValid fuel

end Kraken.Promising.Live.SpinSwpFam

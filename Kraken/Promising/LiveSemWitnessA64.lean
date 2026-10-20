/-
**Stage 3: fair traces exist from the AArch64 lock
start configurations**.

For each lock, `Progressive` at `Config.init states initMem` follows from
the existing operational invariant (`step_inv`, `inv_init`) by
`Witness.progressive_of_inv`: at each pc of the per-thread invariant the
instruction is a register step, a branch, a store, a load or an RMW
(the existing `exec_*` lemmas), and the shape lemmas `Witness.goodT_*` give a
newest-reading promise-free outcome; the end pc has halted. Then
`Witness.fair_exists` and `Witness.fairSem_exists` give a fair trace of each
machine:

- `*_fair_exists`: a `TraceS` from the start configuration with `WeakFair`,
  `WeakFairInstr`, `PromiseFree` and `MemFair` (the hypotheses of the
  promise-free liveness theorems, e.g. `Ticket.TicketLivePF`);
- `*_fairSem_exists`: a `TraceSem` with `WeakFairSem`, `WeakFairInstrSem` and
  `MemFair` (the hypotheses of the semantic liveness theorems).

So those liveness theorems are not vacuous at their start configurations.
-/
import Kraken.Promising.LiveSemWitness
import Kraken.Promising.LiveTicketInv
import Kraken.Promising.LiveSpinCasInv
import Kraken.Promising.LiveSpinSwpInv
import Kraken.Promising.LiveSpinSwpFam

namespace Kraken.Promising.Live.WitnessA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Witness

/-! ## The ticket lock (`tkWorker`, `Ticket.TkStart`) -/

section Ticket

open Kraken.Promising.Live.TicketTrees Kraken.Promising.Live.TicketInv
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorker)]

/-- At every pc of `TInv`, a newest-reading promise-free outcome (or halted). -/
theorem goodT_tk {x o c : BitVec 64} {m tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv x o c m t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.armv8 tid t mem oc := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ tkPcs) (h14 : i ≠ 14) => hS.at hi h14 hpc
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (exec_mov _ (hA (by decide) (by decide)))
  · exact goodT_rmw hp hb hf (exec_ldadda _ (hA (by decide) (by decide)) hS.x0 hS.dx)
  · exact goodT_load hp hf (exec_ldar _ (hA (by decide) (by decide)) hS.x1 hS.dO)
  · exact goodT_done hp (exec_cmp _ (hA (by decide) (by decide))).choose_spec.1
  · exact goodT_done hp (exec_bne _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldr_c _ (hA (by decide) (by decide)) hS.x2 hS.dc)
  · exact goodT_done hp (exec_add5 _ (hA (by decide) (by decide)))
  · exact goodT_store hp hb (exec_str_c _ (hA (by decide) (by decide)) hS.x2 hS.dc)
  · exact goodT_done hp (exec_add4 _ (hA (by decide) (by decide)))
  · exact goodT_store hp hb (exec_stlr _ (hA (by decide) (by decide)) hS.x1 hS.dO)
  · exact goodT_done hp (exec_b_done _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.armv8 tid mem) (stepOne_ne_none hh)

theorem tk_progressive {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) : Progressive Arch.armv8 (Config.init states initMem) :=
  progressive_of_inv (fun cf => ∃ xc m, InvW N x o c xc m cf) ⟨0, 0, inv_init hs⟩ (Config.init_bnd _ _)
    (fwd_init _ _)
    (fun _ _ _ ⟨xc, m, h⟩ hb hi => (step_inv h hb hi).elim (fun ⟨xc', h', _⟩ => ⟨xc', m, h'⟩)
      fun h' => ⟨xc, m + 1, h'⟩)
    fun _ ⟨_, _, h⟩ tid t ht hh hf hb => goodT_tk (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every ticket-lock start
configuration**: the hypotheses of `Ticket.TicketLivePF` are satisfiable. -/
theorem tk_fair_exists {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fair_exists (tk_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every ticket-lock
start configuration.** -/
theorem tk_fairSem_exists {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket.TkStart N x o c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.armv8 fuel tr.cfg ∧ WeakFairInstrSem Arch.armv8 fuel tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fairSem_exists (tk_progressive hs) (startPF_init _ _) fuel

end Ticket

/-! ## The CAS spinlock (`casTtasWorker`, `Spin.CasStart`) -/

section Cas

open Kraken.Promising.Live.SpinCasTrees Kraken.Promising.Live.SpinCasInv
open Kraken.Promising.SLR.EnvG.CasSmoke (casTtasWorker)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout casTtasWorker)]

theorem goodT_cas {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv l c t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.armv8 tid t mem oc := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ spPcs) (h17 : i ≠ 17) => hS.at hi h17 hpc
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (exec_mov3 _ (hA (by decide) (by decide)))
  · exact goodT_done hp (exec_mov2 _ (hA (by decide) (by decide)))
  · exact goodT_rmw hp hb hf (exec_casa _ (hA (by decide) (by decide)) hS.x0 hS.dl)
  · exact goodT_done hp (exec_cbz _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldr_l _ (hA (by decide) (by decide)) hS.x0 hS.dl)
  · exact goodT_done hp (exec_cbnz _ (hA (by decide) (by decide)))
  · exact goodT_done hp (exec_b_try _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldr_c _ (hA (by decide) (by decide)) hS.x1 hS.dc)
  · exact goodT_done hp (exec_add5 _ (hA (by decide) (by decide)))
  · exact goodT_store hp hb (exec_str_c _ (hA (by decide) (by decide)) hS.x1 hS.dc)
  · exact goodT_store hp hb (exec_stlr _ (hA (by decide) (by decide)) hS.x0 hS.dl)
  · exact goodT_done hp (exec_b_done _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.armv8 tid mem) (stepOne_ne_none hh)

theorem cas_progressive {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) : Progressive Arch.armv8 (Config.init states initMem) :=
  progressive_of_inv (InvC l c) (inv_init hs) (Config.init_bnd _ _) (fwd_init _ _)
    (fun _ _ _ h hb hi => (step_inv h hb hi).1) fun _ h tid t ht hh hf hb => goodT_cas (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every CAS-spinlock start
configuration.** -/
theorem cas_fair_exists {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fair_exists (cas_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every CAS-spinlock
start configuration.** -/
theorem cas_fairSem_exists {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Spin.CasStart l c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.armv8 fuel tr.cfg ∧ WeakFairInstrSem Arch.armv8 fuel tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fairSem_exists (cas_progressive hs) (startPF_init _ _) fuel

end Cas

/-! ## The SWP spinlocks (any `P` with `SwpCode P`: `swpWorker`, `swplWorker`) -/

section Swp

open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.SpinSwpInv

variable [layout : _root_.Layout] {P : Program} [hv : Executable.ValidLayout (layout P)]

theorem goodT_swp (hC : SwpCode P) {l c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory}
    (h : TInv P l c t) (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.armv8 tid t mem oc := by
  obtain ⟨i, hi, hpc⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ swPcs) (h16 : i ≠ 16) => hS.at hC hi h16 hpc
  simp only [swPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (hC.mov _ (hA (by decide) (by decide)))
  · exact goodT_rmw hp hb hf (hC.swpa _ l (hA (by decide) (by decide)) hS.x0 hS.dl)
  · exact goodT_done hp (hC.cbz _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (hC.ldr _ l (hA (by decide) (by decide)) hS.x0 hS.dl)
  · exact goodT_done hp (hC.cbnz _ (hA (by decide) (by decide)))
  · exact goodT_done hp (hC.btry _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (hC.ldrc _ c (hA (by decide) (by decide)) hS.x1 hS.dc)
  · exact goodT_done hp (hC.add _ (hA (by decide) (by decide)))
  · exact goodT_store hp hb (hC.strc _ c (hA (by decide) (by decide)) hS.x1 hS.dc)
  · rcases hC.rel _ l (hA (by decide) (by decide)) hS.x0 hS.dl with hex | ⟨_, hex⟩
    · exact goodT_store hp hb hex
    · exact goodT_rmw hp hb hf hex
  · exact goodT_done hp (hC.bdone _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.armv8 tid mem) (stepOne_ne_none hh)

theorem swp_progressive (hC : SwpCode P) {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG (SpinSwp.StartG P) l c states initMem) :
    Progressive Arch.armv8 (Config.init states initMem) :=
  progressive_of_inv (InvS P l c) (inv_init hC hs) (Config.init_bnd _ _) (fwd_init _ _)
    (fun _ _ _ h hb hi => (step_inv hC h hb hi).1) fun _ h tid t ht hh hf hb => goodT_swp hC (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every start configuration of an
SWP-shaped spinlock** (`swpCode`, `swplCode`: SWP and SWPL). -/
theorem swp_fair_exists (hC : SwpCode P) {l c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG (SpinSwp.StartG P) l c states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fair_exists (swp_progressive hC hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every start
configuration of an SWP-shaped spinlock.** -/
theorem swp_fairSem_exists (hC : SwpCode P) {l c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : SpinSwp.SwpStartG (SpinSwp.StartG P) l c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.armv8 fuel tr.cfg ∧ WeakFairInstrSem Arch.armv8 fuel tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fairSem_exists (swp_progressive hC hs) (startPF_init _ _) fuel

end Swp

/-! The two SWP workers, at the start predicates of `SwpSpinLivePF` and
`SwplSpinLivePF` (`SpinSwpFam.startG_swp`, `startG_swpl`). -/

section SwpFam

open Kraken.Promising.Live.SpinSwpTrees Kraken.Promising.Live.SpinSwpFam
open Kraken.AArch64.Examples.InvEnv (swpWorker)
open Kraken.Promising.SLR.EnvG.SwplLock (swplWorker)

variable [layout : _root_.Layout]

theorem swpWorker_fair_exists [Executable.ValidLayout (layout swpWorker)] {l c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : SpinSwp.SwpStartG SLR.SwpPublic.StartState l c states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  swp_fair_exists swpCode ⟨hs.hlc, fun s hm => startG_swp (hs.hst s hm), hs.hL0⟩ fuel

theorem swpWorker_fairSem_exists [Executable.ValidLayout (layout swpWorker)] {l c : BitVec 64}
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG SLR.SwpPublic.StartState l c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.armv8 fuel tr.cfg ∧ WeakFairInstrSem Arch.armv8 fuel tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  swp_fairSem_exists swpCode ⟨hs.hlc, fun s hm => startG_swp (hs.hst s hm), hs.hL0⟩ fuel

theorem swplWorker_fair_exists [Executable.ValidLayout (layout swplWorker)] {l c : BitVec 64}
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG SLR.EnvG.SwplLock.StartState l c states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  swp_fair_exists swplCode ⟨hs.hlc, fun s hm => startG_swpl (hs.hst s hm), hs.hL0⟩ fuel

theorem swplWorker_fairSem_exists [Executable.ValidLayout (layout swplWorker)] {l c : BitVec 64}
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinSwp.SwpStartG SLR.EnvG.SwplLock.StartState l c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.armv8 fuel tr.cfg ∧ WeakFairInstrSem Arch.armv8 fuel tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  swp_fairSem_exists swplCode ⟨hs.hlc, fun s hm => startG_swpl (hs.hst s hm), hs.hL0⟩ fuel

end SwpFam

end Kraken.Promising.Live.WitnessA64

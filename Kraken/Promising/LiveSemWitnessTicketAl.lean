/-
**Stage 3: fair traces exist from the `ldaddal`
ticket-lock start configurations** (`TicketAl.TkStartAl`, worker
`tkWorkerAl`).

The ticket instance of `LiveSemWitnessA64.lean` at the cloned `TicketAl`
invariant (`LiveTicketAlInv.lean`, `#ticket_al_clone`): the only changed cell
is the ticket RMW, `ldaddal` (`exec_ldaddal`, kind `.acqRel`), which
`Witness.goodT_rmw` covers like `ldadda`. `*_fair_exists` gives a `TraceS`
with `WeakFair`, `WeakFairInstr`, `PromiseFree` and `MemFair` (the hypotheses
of `TicketAl.TicketAlLivePF`); `*_fairSem_exists` a `TraceSem` with
`WeakFairSem`, `WeakFairInstrSem` and `MemFair`. At the runner starts
(`TicketAl.TkStartAlD`, `decls = ds`), `tkAl_progressive_runner` gives
`Progressive` (`Witness.progressive_of_mapC` along `State.noDecls`), from
which `fair_exists` / `fairSem_exists` give the fair traces.
-/
import Kraken.Promising.LiveSemWitness
import Kraken.Promising.LiveTicketAlInv
import Kraken.Promising.LiveSemWitnessRunner
import Kraken.Promising.LiveTicketAlThm

namespace Kraken.Promising.Live.WitnessTicketAl

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Witness
open Kraken.Promising.Live.TicketAlTrees Kraken.Promising.Live.TicketAlInv
open Kraken.Promising.SLR.EnvG.TicketLock (tkWorkerAl)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkWorkerAl)]

/-- At every pc of `TInv`, a newest-reading promise-free outcome (or halted). -/
theorem goodT_tkAl {x o c : BitVec 64} {m tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv x o c m t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.armv8 tid t mem oc := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ tkPcs) (h14 : i ≠ 14) => hS.at hi h14 hpc
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (exec_mov _ (hA (by decide) (by decide)))
  · exact goodT_rmw hp hb hf (exec_ldaddal _ (hA (by decide) (by decide)) hS.x0 hS.dx)
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

theorem tkAl_progressive {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketAl.TkStartAl N x o c states initMem) : Progressive Arch.armv8 (Config.init states initMem) :=
  progressive_of_inv (fun cf => ∃ xc m, InvW N x o c xc m cf) ⟨0, 0, inv_init hs⟩ (Config.init_bnd _ _)
    (fwd_init _ _)
    (fun _ _ _ ⟨xc, m, h⟩ hb hi => (step_inv h hb hi).elim (fun ⟨xc', h', _⟩ => ⟨xc', m, h'⟩)
      fun h' => ⟨xc, m + 1, h'⟩)
    fun _ ⟨_, _, h⟩ tid t ht hh hf hb => goodT_tkAl (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every `ldaddal` ticket-lock start
configuration**: the hypotheses of `TicketAl.TicketAlLivePF` are
satisfiable. -/
theorem tkAl_fair_exists {N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketAl.TkStartAl N x o c states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.armv8 fuel tr.cfg ∧
      WeakFairInstr Arch.armv8 fuel tr.cfg ∧ PromiseFree Arch.armv8 tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fair_exists (tkAl_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every `ldaddal`
ticket-lock start configuration.** -/
theorem tkAl_fairSem_exists {N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : TicketAl.TkStartAl N x o c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.armv8 fuel tr.cfg ∧ WeakFairInstrSem Arch.armv8 fuel tr.cfg ∧ MemFair Arch.armv8 tr.cfg :=
  fairSem_exists (tkAl_progressive hs) (startPF_init _ _) fuel

open Kraken.Promising.Live.RunnerSim Kraken.Promising.Live.RunnerA64 in
/-- `Progressive` at the `ldaddal` runner starts (`TicketAl.TkStartAlD ds`). -/
theorem tkAl_progressive_runner {ds : Decls} {N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : TicketAl.TkStartAlD ds N x o c states initMem) :
    Progressive Arch.armv8 (Config.init states initMem) := by
  refine progressive_of_mapC (execSimA SLR.EnvG.TicketLock.tkWorkerAl_noPairs
      (RunnerA64TicketAl.stepOK_tk hs.agX hs.agO hs.agC))
    (goodC_initA initMem fun s h => ⟨(hs.hst s h).1, RunnerA64TicketAl.sTk_of_start (hs.hst s h).2⟩) ?_
  erw [mapC_init]
  refine tkAl_progressive ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32, fun s h => ?_,
    (@List.length_map _ _ states State.noDecls).trans hs.hN, hs.hX0, hs.hO0, hs.hC0⟩
  obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
  exact (hs.hst s' h').2

end Kraken.Promising.Live.WitnessTicketAl

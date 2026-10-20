/-
**Stage 4 (repeated acquisition): fair traces exist from the
repeated-acquire ticket-lock start configurations** (the recipe of `LiveSemWitnessA64.lean`).

`Progressive` at `Config.init states initMem` follows by
`Witness.progressive_of_inv` from the promise-free per-thread invariant
(`SInv` and no outstanding promise, kept by every instruction step of a
promise-free thread: `step_pf`): at each pc the instruction is a register
step, a branch, a store, a load or an RMW (`LiveTicketLoopTrees`), and the
shape lemmas `Witness.goodT_*` give a newest-reading promise-free outcome; the
end pc has halted. Then `Witness.fairSem_exists` gives
`tk_loop_fairSem_exists`: a semantic trace from every `TkLoopStart`
configuration under `WeakFairSem`, `WeakFairInstrSem` and `MemFair`, so the
hypothesis `LoopFair` of the statements in `LiveTicketLoop.lean` is
satisfiable (they are not vacuous). The round-robin trace takes no promise
step, so `tk_loop_fairSemPF_exists` gives the same for `LoopFairPF`, the
hypothesis of the proved promise-free statements.
-/
import Kraken.Promising.LiveTicketLoopStatic
import Kraken.Promising.LiveSemWitness
import Kraken.Promising.LiveSemShape

namespace Kraken.Promising.Live.TicketLoopWitness

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Witness
open Kraken.Promising.Live.TicketLoop Kraken.Promising.Live.TicketLoopTrees Kraken.Promising.Live.TicketLoopStatic
open Kraken.Promising.Live.TicketStep

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tkLoopWorker)]

/-- **A promise-free worker stays promise-free** across an instruction step. -/
theorem step_pf {x o c : BitVec 64} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} {oc : Outcome isa} (h : SInv x o c t.st) (hp0 : t.prom = [])
    (hs : stepOne Arch.armv8 t tid mem = some outs) (ho : .ok oc ∈ outs) : oc.thread.prom = [] := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (spec_done _ _ (exec_mov _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · exact (spec_done _ _ (exec_cbz _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · obtain ⟨-, -, -, -, -, -, h⟩ :=
      spec_rmw _ _ rfl hp0 (exec_ldadda _ (hS.at (by decide) (by decide) hpc) hS.x0 hS.dx) hs ho
    exact h
  · obtain ⟨-, -, -, -, -, -, h, -⟩ := spec_load _ _ (exec_ldar _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho
    exact h.trans hp0
  · obtain ⟨sf, hex, -⟩ := exec_cmp _ (hS.at (by decide) (by decide) hpc)
    exact (spec_done _ _ hex hs ho).2.2.1.trans hp0
  · exact (spec_done _ _ (exec_bne _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · obtain ⟨-, -, -, -, -, -, h, -⟩ :=
      spec_load _ _ (exec_ldr_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho
    exact h.trans hp0
  · exact (spec_done _ _ (exec_add5 _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · exact (spec_store _ _ hp0 (exec_str_c _ (hS.at (by decide) (by decide) hpc) hS.x2 hS.dc) hs ho).2.2
  · exact (spec_done _ _ (exec_add4 _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · exact (spec_store _ _ hp0 (exec_stlr _ (hS.at (by decide) (by decide) hpc) hS.x1 hS.dO) hs ho).2.2
  · exact (spec_done _ _ (exec_sub _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · exact (spec_done _ _ (exec_b_round _ (hS.at (by decide) (by decide) hpc)) hs ho).2.2.1.trans hp0
  · rw [stepOne_end hS hpc] at hs; cases hs

/-- At every pc, a newest-reading promise-free outcome (or halted). -/
theorem goodT_loop {x o c : BitVec 64} {tid : Nat} {t : Thread isa} {mem : Memory} (h : SInv x o c t.st)
    (hp : t.prom = []) (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.armv8 tid t mem oc := by
  obtain ⟨hS, i, hi, hpc⟩ := h
  have hA := fun (hi : i ∈ tkLoopPcs) (h17 : i ≠ 17) => hS.at hi h17 hpc
  simp only [tkLoopPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (exec_mov _ (hA (by decide) (by decide)))
  · exact goodT_done hp (exec_cbz _ (hA (by decide) (by decide)))
  · exact goodT_rmw hp hb hf (exec_ldadda _ (hA (by decide) (by decide)) hS.x0 hS.dx)
  · exact goodT_load hp hf (exec_ldar _ (hA (by decide) (by decide)) hS.x1 hS.dO)
  · exact goodT_done hp (exec_cmp _ (hA (by decide) (by decide))).choose_spec.1
  · exact goodT_done hp (exec_bne _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldr_c _ (hA (by decide) (by decide)) hS.x2 hS.dc)
  · exact goodT_done hp (exec_add5 _ (hA (by decide) (by decide)))
  · exact goodT_store hp hb (exec_str_c _ (hA (by decide) (by decide)) hS.x2 hS.dc)
  · exact goodT_done hp (exec_add4 _ (hA (by decide) (by decide)))
  · exact goodT_store hp hb (exec_stlr _ (hA (by decide) (by decide)) hS.x1 hS.dO)
  · exact goodT_done hp (exec_sub _ (hA (by decide) (by decide)))
  · exact goodT_done hp (exec_b_round _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.armv8 tid mem) (stepOne_ne_none hh)

/-- The promise-free per-thread invariant of every configuration. -/
def PFInv (x o c : BitVec 64) (cf : Config isa) : Prop :=
  ∀ (tid : Nat) t, cf.threads[tid]? = some t → SInv x o c t.st ∧ t.prom = []

theorem tk_loop_progressive {k N : Nat} {x o c : BitVec 64} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TkLoopStart k N x o c states initMem) : Progressive Arch.armv8 (Config.init states initMem) := by
  refine progressive_of_inv (PFInv x o c) ?_ (Config.init_bnd _ _) (fwd_init _ _) ?_
    fun _ h tid t ht hh hf hb => goodT_loop (h tid t ht).1 (h tid t ht).2 hh hf hb
  · intro tid t ht
    simp only [Config.init, List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨s, hs', rfl⟩ := ht
    exact ⟨sinv_start (hs.hst s (List.mem_of_getElem? hs')), rfl⟩
  · rintro cf _ tid h - ⟨u, outs, oc, hu, hso, ho, rfl⟩ j t ht
    rcases SpinStep.wt_get hu ht with ⟨-, rfl⟩ | ⟨-, ht⟩
    · exact ⟨(step_sinv (h tid u hu).1 hso ho).1, step_pf (h tid u hu).1 (h tid u hu).2 hso ho⟩
    · exact h j t ht

/-- **A fair semantic trace exists from every repeated-acquire ticket-lock
start configuration**: the hypothesis `LoopFair` of `TicketLoopLiveSem` (and
`WeakFairInstrSem`) is satisfiable. -/
theorem tk_loop_fairSem_exists {k N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : TkLoopStart k N x o c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ LoopFair fuel tr.cfg ∧
      WeakFairInstrSem Arch.armv8 fuel tr.cfg := by
  obtain ⟨tr, h0, h1, h2, h3⟩ := fairSem_exists (tk_loop_progressive hs) (startPF_init _ _) fuel
  exact ⟨tr, h0, ⟨h1, h3⟩, h2⟩

/-- **A fair promise-free semantic trace exists from every repeated-acquire
ticket-lock start configuration**: the round-robin trace takes no promise step
(its threads never have a promise), so the hypothesis `LoopFairPF` of the
promise-free statements (`TicketLoopLivePFSem`) is satisfiable. -/
theorem tk_loop_fairSemPF_exists {k N : Nat} {x o c : BitVec 64} {states : List isa.State}
    {initMem : List (Loc × Val)} (hs : TkLoopStart k N x o c states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.armv8 fuel isa, tr.cfg 0 = Config.init states initMem ∧ LoopFairPF fuel tr.cfg := by
  have hP := tk_loop_progressive hs
  have hp0 := startPF_init (I := isa) states initMem
  refine ⟨rrTrace_traceSem hP hp0 fuel, rfl, ⟨rrTrace_weakFairSem hP fuel, rrTrace_memFair hP hp0⟩, ?_⟩
  rintro i tid ⟨t, w, ht, -, -, he⟩
  have h1 := (rr_reach (A := Arch.armv8) (c0 := Config.init states initMem) (i + 1)).prom hp0 tid _
    (by rw [show rrTrace Arch.armv8 (Config.init states initMem) (i + 1) = _ from he]; exact withThread_get_self ht)
  simp at h1

end Kraken.Promising.Live.TicketLoopWitness

#print axioms Kraken.Promising.Live.TicketLoopWitness.tk_loop_fairSem_exists
#print axioms Kraken.Promising.Live.TicketLoopWitness.tk_loop_fairSemPF_exists

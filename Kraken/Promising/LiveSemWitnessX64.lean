/-
**Stage 3: fair traces exist from the x64 lock
start configurations**. The x64 twin of
`LiveSemWitnessA64.lean`.

For each lock, `Progressive` at `Config.init states initMem` follows from
the existing operational invariant (`step_inv`, `inv_init`) by
`Witness.progressive_of_inv`: at each pc of the per-thread invariant the
instruction is a register step (possibly a `.choose`, for an undefined
flag), a branch, a store, a load or a locked RMW (the existing `exec_*`
lemmas), and the shape lemmas `Witness.goodT_*` give a newest-reading
promise-free outcome; the end pc has halted. A load may forward from the
thread's own buffered store (TSO); `FwdLeCoh` (carried by
`progressive_of_inv`) makes the forwarded read newest too. Then
`Witness.fair_exists` and `Witness.fairSem_exists` give a fair trace of
each machine:

- `*_fair_exists`: a `TraceS Arch.tso` from the start configuration with
  `WeakFair`, `WeakFairInstr`, `PromiseFree` and `MemFair` (the hypotheses
  of the promise-free liveness theorems, e.g. `SpinX64.CmpxSpinLivePF`);
- `*_fairSem_exists`: a `TraceSem Arch.tso` with `WeakFairSem`,
  `WeakFairInstrSem` and `MemFair` (the hypotheses of the semantic liveness
  theorems).

So those liveness theorems are not vacuous at their start configurations.
For the runner starts (`*StartD`, `decls = ds`), `*_progressive_runner`
gives `Progressive` (through `Witness.progressive_of_mapC`), from which
`fair_exists` / `fairSem_exists` give the fair traces.
-/
import Kraken.Promising.LiveSemWitness
import Kraken.Promising.LiveSpinX64CmpxInv
import Kraken.Promising.LiveSpinX64XchgInv
import Kraken.Promising.LiveX64TicketInv
import Kraken.Promising.LiveX64Ticket2Inv
import Kraken.Promising.LiveSemWitnessRunner
import Kraken.Promising.LiveRunnerX64Spin
import Kraken.Promising.LiveRunnerX64Ticket
import Kraken.Promising.LiveRunnerX64Ticket2

namespace Kraken.Promising.Live.WitnessX64

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem
open Kraken.Promising.Live.Witness

/-! ## The `lock cmpxchg` spinlock (`cmpxImageV`, `SpinX64.CmpxStart`) -/

section Cmpx

open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.SpinX64CmpxInv
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

/-- At every pc of `TInv`, a newest-reading promise-free outcome (or halted). -/
theorem goodT_cmpx {tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.tso tid t mem oc := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ spPcs) (h10 : i ≠ 10) => hS.at hi h10 hpc
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_choose (by decide) hp (exec_xor _ (hA (by decide) (by decide)))
  · exact goodT_done hp (exec_movc _ (hA (by decide) (by decide)))
  · exact goodT_rmw hp hb hf (exec_cmpxchg _ (hA (by decide) (by decide)) hS.dl).choose_spec.2
  · exact goodT_done hp (exec_jne _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldc _ (hA (by decide) (by decide)) hS.dc).choose_spec.2
  · exact goodT_done hp (exec_add _ (hA (by decide) (by decide))).choose_spec.2
  · obtain ⟨_, _, -, hex⟩ := exec_stc _ (hA (by decide) (by decide)) hS.dc
    exact goodT_store hp hb hex
  · exact goodT_store hp hb (exec_unlock _ (hA (by decide) (by decide)) hS.dl)
  · exact goodT_done hp (exec_jmp _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.tso tid mem) (stepOne_ne_none hh)

theorem cmpx_progressive {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) : Progressive Arch.tso (Config.init states initMem) :=
  progressive_of_inv InvX (inv_init hs) (Config.init_bnd _ _) (fwd_init _ _)
    (fun _ _ _ h hb hi => (step_inv h hb hi).1) fun _ h tid t ht hh hf hb => goodT_cmpx (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every `lock cmpxchg`-spinlock
start configuration**: the hypotheses of `SpinX64.CmpxSpinLivePF` are
satisfiable. -/
theorem cmpx_fair_exists {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.tso fuel tr.cfg ∧
      WeakFairInstr Arch.tso fuel tr.cfg ∧ PromiseFree Arch.tso tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fair_exists (cmpx_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every `lock
cmpxchg`-spinlock start configuration.** -/
theorem cmpx_fairSem_exists {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64.CmpxStart states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.tso fuel tr.cfg ∧ WeakFairInstrSem Arch.tso fuel tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fairSem_exists (cmpx_progressive hs) (startPF_init _ _) fuel

end Cmpx

/-! ## The `xchgl` spinlock (`spinImageV`, `SpinX64Xchg.XchgStart`) -/

section Xchg

open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.SpinX64XchgInv
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

theorem goodT_xchg {tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.tso tid t mem oc := by
  obtain ⟨i, hi, hpc⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ spPcs) (h13 : i ≠ 13) => hS.at hi h13 hpc
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_load hp hf (exec_ldl _ (hA (by decide) (by decide)) hS.dl).choose_spec.2
  · exact goodT_choose (by decide) hp (exec_test _ (.inl rfl) (hA (by decide) (by decide))).choose_spec.2
  · exact goodT_done hp (exec_jne _ (.inl rfl) (hA (by decide) (by decide)))
  · exact goodT_done hp (exec_mov1 _ (hA (by decide) (by decide))).choose_spec.2
  · exact goodT_rmw hp hb hf (exec_xchg _ (hA (by decide) (by decide)) hS.dl).choose_spec.2
  · exact goodT_choose (by decide) hp (exec_test _ (.inr rfl) (hA (by decide) (by decide))).choose_spec.2
  · exact goodT_done hp (exec_jne _ (.inr rfl) (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldc _ (hA (by decide) (by decide)) hS.dc).choose_spec.2
  · exact goodT_done hp (exec_add _ (hA (by decide) (by decide))).choose_spec.2
  · obtain ⟨_, _, -, hex⟩ := exec_stc _ (hA (by decide) (by decide)) hS.dc
    exact goodT_store hp hb hex
  · exact goodT_store hp hb (exec_unlock _ (hA (by decide) (by decide)) hS.dl)
  · exact goodT_done hp (exec_jmp _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.tso tid mem) (stepOne_ne_none hh)

theorem xchg_progressive {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64Xchg.XchgStart states initMem) : Progressive Arch.tso (Config.init states initMem) :=
  progressive_of_inv InvX (inv_init hs) (Config.init_bnd _ _) (fwd_init _ _)
    (fun _ _ _ h hb hi => (step_inv h hb hi).1) fun _ h tid t ht hh hf hb => goodT_xchg (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every `xchgl`-spinlock start
configuration.** -/
theorem xchg_fair_exists {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64Xchg.XchgStart states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.tso fuel tr.cfg ∧
      WeakFairInstr Arch.tso fuel tr.cfg ∧ PromiseFree Arch.tso tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fair_exists (xchg_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every `xchgl`-spinlock
start configuration.** -/
theorem xchg_fairSem_exists {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : SpinX64Xchg.XchgStart states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.tso fuel tr.cfg ∧ WeakFairInstrSem Arch.tso fuel tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fairSem_exists (xchg_progressive hs) (startPF_init _ _) fuel

end Xchg

/-! ## The `lock xaddl` ticket lock with a store release (`tk3ImageV`, `TicketX64.TkStartX`) -/

section TicketX

open Kraken.Promising.Live.TicketX64Trees Kraken.Promising.Live.TicketX64Inv
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

theorem goodT_tkX {m tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv m t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.tso tid t mem oc := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ tkPcs) (h14 : i ≠ 14) => hS.at hi h14 hpc
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (exec_mov1 _ (hA (by decide) (by decide))).choose_spec.2.2
  · exact goodT_rmw hp hb hf (exec_xadd _ (hA (by decide) (by decide)) hS.dx).choose_spec.2
  · exact goodT_load hp hf (exec_ldo _ (hA (by decide) (by decide)) hS.dO).choose_spec.2
  · exact goodT_done hp (exec_cmp _ (hA (by decide) (by decide))).choose_spec.2.2.2.2
  · exact goodT_done hp (exec_jne _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldc _ (hA (by decide) (by decide)) hS.dc).choose_spec.2
  · exact goodT_done hp (exec_addd _ (hA (by decide) (by decide))).choose_spec.2.2.2
  · obtain ⟨_, _, -, -, -, hex⟩ := exec_stc _ (hA (by decide) (by decide)) hS.dc
    exact goodT_store hp hb hex
  · exact goodT_done hp (exec_addc _ (hA (by decide) (by decide))).choose_spec.2.2.2
  · exact goodT_store hp hb (exec_rel _ (hA (by decide) (by decide)) hS.dO)
  · exact goodT_done hp (exec_jmp _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.tso tid mem) (stepOne_ne_none hh)

theorem tkX_progressive {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketX64.TkStartX N states initMem) : Progressive Arch.tso (Config.init states initMem) :=
  progressive_of_inv (fun cf => ∃ xc m, InvW N xc m cf) ⟨0, 0, inv_init hs⟩ (Config.init_bnd _ _)
    (fwd_init _ _)
    (fun _ _ _ ⟨xc, m, h⟩ hb hi => (step_inv h hb hi).elim (fun ⟨xc', h', _⟩ => ⟨xc', m, h'⟩)
      fun h' => ⟨xc, m + 1, h'⟩)
    fun _ ⟨_, _, h⟩ tid t ht hh hf hb => goodT_tkX (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every start configuration of the
x64 ticket lock with a store release.** -/
theorem tkX_fair_exists {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketX64.TkStartX N states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.tso fuel tr.cfg ∧
      WeakFairInstr Arch.tso fuel tr.cfg ∧ PromiseFree Arch.tso tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fair_exists (tkX_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every start
configuration of the x64 ticket lock with a store release.** -/
theorem tkX_fairSem_exists {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : TicketX64.TkStartX N states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.tso fuel tr.cfg ∧ WeakFairInstrSem Arch.tso fuel tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fairSem_exists (tkX_progressive hs) (startPF_init _ _) fuel

end TicketX

/-! ## The `lock xaddl` ticket lock with an `incl` release (`tk2ImageV`, `Ticket2X64.Tk2StartX`)

The release `incl (owner)` is a plain load followed by a plain store of the
same word (`Witness.goodT_ldst`). -/

section Ticket2X

open Kraken.Promising.Live.Ticket2X64Trees Kraken.Promising.Live.Ticket2X64Inv
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk2ImageV)]

theorem goodT_tk2X {m lw tid : Nat} {t : Thread isa} {mem : Memory} (h : TInv m lw t)
    (hh : t.halted = false) (hf : FwdLeCoh t.views) (hb : t.Bnd mem.last) :
    ∃ oc, GoodT Arch.tso tid t mem oc := by
  obtain ⟨i, hi, hpc, -⟩ := h.pc
  have hS := h.st
  have hp := h.prom
  have hA := fun (hi : i ∈ tkPcs) (h13 : i ≠ 13) => hS.at hi h13 hpc
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact goodT_done hp (exec_mov1 _ (hA (by decide) (by decide))).choose_spec.2.2
  · exact goodT_rmw hp hb hf (exec_xadd _ (hA (by decide) (by decide)) hS.dx).choose_spec.2
  · exact goodT_load hp hf (exec_ldo _ (hA (by decide) (by decide)) hS.dO).choose_spec.2
  · exact goodT_done hp (exec_cmp _ (hA (by decide) (by decide))).choose_spec.2.2.2.2
  · exact goodT_done hp (exec_jne _ (hA (by decide) (by decide)))
  · exact goodT_load hp hf (exec_ldc _ (hA (by decide) (by decide)) hS.dc).choose_spec.2
  · exact goodT_done hp (exec_addd _ (hA (by decide) (by decide))).choose_spec.2.2.2
  · obtain ⟨_, _, -, -, -, hex⟩ := exec_stc _ (hA (by decide) (by decide)) hS.dc
    exact goodT_store hp hb hex
  · exact goodT_ldst hp hb hf (exec_inc _ (hA (by decide) (by decide)) hS.dO).choose_spec.2
  · exact goodT_done hp (exec_jmp _ (hA (by decide) (by decide)))
  · exact absurd (stepOne_end hS hpc Arch.tso tid mem) (stepOne_ne_none hh)

theorem tk2X_progressive {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket2X64.Tk2StartX N states initMem) : Progressive Arch.tso (Config.init states initMem) :=
  progressive_of_inv (fun cf => ∃ xc m, InvW N xc m cf) ⟨0, 0, inv_init hs⟩ (Config.init_bnd _ _)
    (fwd_init _ _)
    (fun _ _ _ ⟨xc, m, h⟩ hb hi => (step_inv h hb hi).elim (fun ⟨xc', h', _⟩ => ⟨xc', m, h'⟩)
      fun h' => ⟨xc, m + 1, h'⟩)
    fun _ ⟨_, _, h⟩ tid t ht hh hf hb => goodT_tk2X (h.thr tid t ht) hh hf hb

/-- **A fair promise-free trace exists from every start configuration of the
x64 ticket lock with an `incl` release.** -/
theorem tk2X_fair_exists {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket2X64.Tk2StartX N states initMem) (fuel : Nat) :
    ∃ tr : TraceS Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧ WeakFair Arch.tso fuel tr.cfg ∧
      WeakFairInstr Arch.tso fuel tr.cfg ∧ PromiseFree Arch.tso tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fair_exists (tk2X_progressive hs) (startPF_init _ _) fuel

/-- **A fair trace of the semantic machine exists from every start
configuration of the x64 ticket lock with an `incl` release.** -/
theorem tk2X_fairSem_exists {N : Nat} {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : Ticket2X64.Tk2StartX N states initMem) (fuel : Nat) :
    ∃ tr : TraceSem Arch.tso fuel isa, tr.cfg 0 = Config.init states initMem ∧
      WeakFairSem Arch.tso fuel tr.cfg ∧ WeakFairInstrSem Arch.tso fuel tr.cfg ∧ MemFair Arch.tso tr.cfg :=
  fairSem_exists (tk2X_progressive hs) (startPF_init _ _) fuel

end Ticket2X

/-! ## The runner starts (`*StartD ds`, threads with declarations)

`Witness.progressive_of_mapC` along `State.noDecls` (`RunnerX64.execSimD`),
from the declaration-free instances above. A fair trace from a runner start
is then `Witness.fair_exists (*_progressive_runner hs) (startPF_init _ _)`
(resp. `fairSem_exists`). -/

section Runner

open Kraken.Promising.Live.RunnerSim Kraken.Promising.Live.RunnerX64

variable [layout : _root_.Layout]

theorem cmpx_progressive_runner [Executable.ValidLayout (layout X64.EnvG.CmpxAbs.cmpxImageV)] {ds : Decls}
    {states : List isa.State} {initMem : List (Loc × Val)} (hs : RunnerX64Spin.CmpxStartD ds states initMem) :
    Progressive Arch.tso (Config.init states initMem) := by
  refine progressive_of_mapC (execSimD (RunnerX64Spin.cmpxImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) ?_
  rw [mapC_init]
  refine cmpx_progressive ⟨hs.hlc, fun s h => ?_, hs.hL0⟩
  obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
  have h'' := hs.hst s' h'
  exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩

theorem xchg_progressive_runner [Executable.ValidLayout (layout X64.EnvG.SpinAbs.spinImageV)] {ds : Decls}
    {states : List isa.State} {initMem : List (Loc × Val)} (hs : RunnerX64Spin.XchgStartD ds states initMem) :
    Progressive Arch.tso (Config.init states initMem) := by
  refine progressive_of_mapC (execSimD (RunnerX64Spin.spinImageV_cellsDeclsAgree hs.agL hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) ?_
  rw [mapC_init]
  refine xchg_progressive ⟨hs.hlc, fun s h => ?_, hs.hL0⟩
  obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
  have h'' := hs.hst s' h'
  exact ⟨h''.exe, rfl, h''.pc, h''.endPc, h''.split⟩

theorem tkX_progressive_runner [Executable.ValidLayout (layout X64.EnvG.TicketX.tk3ImageV)] {ds : Decls} {N : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} (hs : RunnerX64Ticket.TkStartXD ds N states initMem) :
    Progressive Arch.tso (Config.init states initMem) := by
  refine progressive_of_mapC (execSimD (RunnerX64Ticket.tk3ImageV_cellsDeclsAgree hs.agX hs.agO hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) ?_
  rw [mapC_init]
  refine tkX_progressive ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32, fun s h => ?_, by rw [List.length_map]; exact hs.hN,
    hs.hX0, hs.hO0, hs.hC0⟩
  obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
  exact RunnerX64Ticket.startStateTk_noDecls (hs.hst s' h')

theorem tk2X_progressive_runner [Executable.ValidLayout (layout X64.EnvG.TicketX2.tk2ImageV)] {ds : Decls} {N : Nat}
    {states : List isa.State} {initMem : List (Loc × Val)} (hs : RunnerX64Ticket2.Tk2StartXD ds N states initMem) :
    Progressive Arch.tso (Config.init states initMem) := by
  refine progressive_of_mapC (execSimD (RunnerX64Ticket2.tk2ImageV_cellsDeclsAgree hs.agX hs.agO hs.agC))
    (goodC_init initMem fun s h => ⟨(hs.hst s h).exe, (hs.hst s h).decls⟩) ?_
  rw [mapC_init]
  refine tk2X_progressive ⟨hs.hxo, hs.hxc, hs.hoc, hs.hN32, fun s h => ?_, by rw [List.length_map]; exact hs.hN,
    hs.hX0, hs.hO0, hs.hC0⟩
  obtain ⟨s', h', rfl⟩ := List.mem_map.mp h
  exact RunnerX64Ticket2.startStateTk2_noDecls (hs.hst s' h')

end Runner

end Kraken.Promising.Live.WitnessX64

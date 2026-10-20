/-
**No stuck configurations (N5), x64 instances: no stuck configuration for the
x64 lock clients on the TSO semantic machine.**

For each x64 lock family with a semantic-machine liveness theorem, from every
start configuration and at every `fuel`, no configuration reachable on the
semantic `Arch.tso` machine is stuck (`NoStuckFrom`), with no hypothesis
left: `tsoNoStuck` at the worker's solo invariant `SInv`, which is a
`TsoCertInv` (every cell's tree makes no non-temporal store and at most one
write; `step_sinv` gives closure), and `OkStepsPF` along every run from the
family's semantic invariant (`inv_step`) and its `instrEnabledSem_of`.

`OneWrite` relies on these instructions each making at most one memory write
on every path: `xorl`, `movl`, `test`, `cmp`, `jne`/`jmp`, `addl` (register
forms), the loads, the plain stores (`movl %reg, mem`; `movl $0, lock`),
`lock cmpxchgl`, `xchgl` and `lock xaddl` (one read-modify-write each), and
the unlocked `incl` (one read, then one write). No cell uses an instruction
with two memory stores.

- `spin_cmpx_noStuck_sem`, `spin_xchg_noStuck_sem`, `ticket3_x64_noStuck_sem`,
  `ticket2_x64_noStuck_sem`, and their `_concrete` forms at the `.kl`
  runner's layouts.
- `*_live_sem_max` / `*_live_oneShot_sem_max`: each family's semantic
  liveness theorem over every maximal run (`liveFromSemMax_of`,
  `progressFromSemMax_of`).
-/
import Kraken.Promising.LiveNoStuckTso
import Kraken.Promising.LiveSpinX64SemCmpx
import Kraken.Promising.LiveSpinX64SemXchgLive
import Kraken.Promising.LiveX64SemTicket
import Kraken.Promising.LiveX64Sem2Ticket

namespace Kraken.Promising.Live.NoStuck

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Live Kraken.Promising.Live.Sem
  Kraken.Promising.Live.Bridge

/-- Close `tree.NoNT Arch.tso ∧ tree.OneWrite` for a concrete cell tree. -/
local macro "treeok" : tactic => `(tactic|
  exact ⟨by simp [EvTree.NoNT, Arch.storeKind, Arch.tso, Arch.rmwKind, RmwKind.storeKind],
    by simp [EvTree.OneWrite, EvTree.NoWrite]⟩)

/-- The thread-start facts every instance needs. -/
theorem stepOne_none_exec {s : isa.State} {A : Arch} {tid : Nat} {mem : Memory}
    (h : stepOne A (Thread.init s) tid mem = none) {tree : EvTree isa.State} (hex : isa.exec s = some tree) : False := by
  unfold stepOne at h
  rw [show (Thread.init s).st = s from rfl, hex] at h
  cases h

/-! ## `lock cmpxchg` spinlock -/

section Cmpx

open Kraken.Promising.Live.SpinX64CmpxTrees Kraken.Promising.Live.SpinX64SemCmpxSolo
  Kraken.Promising.Live.SpinX64SemCmpxInv
open Kraken.Promising.Live.SpinX64CmpxInv (Static stepOne_end)
open Kraken.Promising.X64.EnvG.CmpxAbs (cmpxImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout cmpxImageV)]

set_option hygiene false in
local notation "pcA" => (layout cmpxImageV).addrOf

/-- Every cell of the `lock cmpxchg` worker makes no non-temporal store and
at most one write. -/
theorem cmpx_tree {s : isa.State} (hS : SInv s) {tree : EvTree isa.State} (hex : isa.exec s = some tree) :
    tree.NoNT Arch.tso ∧ tree.OneWrite := by
  obtain ⟨hSt, p, hpp, hpc, -⟩ := hS
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [exec_xor _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex
    exact ⟨fun _ => trivial, fun _ => trivial⟩
  · rw [exec_movc _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex
    exact ⟨trivial, trivial⟩
  · obtain ⟨g, -, he⟩ := exec_cmpxchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    rw [he] at hex; cases hex
    exact ⟨⟨by decide, fun _ => trivial⟩, fun _ => trivial⟩
  · rw [exec_jne _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex
    exact ⟨trivial, trivial⟩
  · obtain ⟨g, -, he⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex
    exact ⟨fun _ => trivial, fun _ => trivial⟩
  · obtain ⟨md, -, he⟩ := exec_add _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex
    exact ⟨trivial, trivial⟩
  · obtain ⟨v, md, -, he⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex
    exact ⟨⟨by decide, fun _ => trivial⟩, fun _ => trivial⟩
  · rw [exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl] at hex; cases hex
    exact ⟨⟨by decide, fun _ => trivial⟩, fun _ => trivial⟩
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex
    exact ⟨trivial, trivial⟩
  · exact (stepOne_none_exec (stepOne_end (t := Thread.init s) hSt hpc Arch.tso 0
      (Config.init ([] : List isa.State) []).mem) hex).elim

/-- **The `lock cmpxchg` worker's `SInv` is a `TsoCertInv`.** -/
theorem cmpx_tsoCertInv : TsoCertInv isa SInv :=
  ⟨fun _ hS _ hex => (cmpx_tree hS hex).1, fun _ hS _ hex => (cmpx_tree hS hex).2,
    fun hS hs ho => (step_sinv hS hs ho).1⟩

/-- Every running promise-free worker has a successful outcome, under the
semantic invariant. -/
theorem cmpx_okStepsPF {fuel : Nat} {c : Config isa} (h : InvS fuel c) : OkStepsPF Arch.tso c := by
  intro tid t ht hh hp
  have hT := h.thr tid t ht
  have h10 : t.st.st.2 ≠ pcA 10 := fun e => by
    rw [halted_of_stepOne_none (stepOne_end hT.sinv.st e Arch.tso tid c.mem)] at hh; cases hh
  obtain ⟨c', t', outs, o, ht', hs, ho, -, -⟩ :=
    instrEnabledSem_of (fuel := fuel) ht hT.sinv h10 (h.bnd tid t ht) (.inl hp)
  rw [ht] at ht'; cases ht'
  exact ⟨outs, o, hs, ho⟩

/-- **No stuck configuration for the x64 `lock cmpxchg` spinlock** on the
semantic `Arch.tso` machine, from every start configuration, at every
`fuel`. -/
theorem spin_cmpx_noStuck_sem (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : SpinX64.CmpxStart states initMem) : NoStuckFrom Arch.tso fuel (Config.init states initMem) := by
  have h0 : InvS fuel (Config.init states initMem) := inv_init hs
  refine tsoNoStuck isa SInv fuel _ cmpx_tsoCertInv h0.bnd
    (fun tid t ht => ⟨(h0.thr tid t ht).sinv, Config.init_prom ht⟩) fun c hr => cmpx_okStepsPF (fuel := fuel) ?_
  refine reachableSem_inv (InvS fuel) (fun tid c c' hc hst => ?_) hr h0
  obtain ⟨t, ht⟩ : ∃ t, c.threads[tid]? = some t := by
    rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
  exact inv_step hc ht hst

/-- `spin_cmpx_live_sem` over every maximal run. -/
theorem spin_cmpx_live_sem_max (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : SpinX64.CmpxStart states initMem) :
    ProgressFromSemMax Arch.tso fuel (Config.init states initMem) (SpinX64Sem.FairX fuel)
      SpinX64.CmpxWaiting SpinX64.CmpxDone :=
  progressFromSemMax_of (spin_cmpx_noStuck_sem fuel states initMem hs)
    (SpinX64SemCmpx.spin_cmpx_live_sem fuel states initMem hs)

/-- `spin_cmpx_live_oneShot_sem` over every maximal run. -/
theorem spin_cmpx_live_oneShot_sem_max (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : SpinX64.CmpxStart states initMem) :
    LiveFromSemMax Arch.tso fuel (Config.init states initMem) (SpinX64Sem.FairX fuel)
      SpinX64.CmpxWaiting SpinX64.CmpxDone :=
  liveFromSemMax_of (spin_cmpx_noStuck_sem fuel states initMem hs)
    (SpinX64SemCmpx.spin_cmpx_live_oneShot_sem fuel states initMem hs)

end Cmpx

open Kraken.Promising.X64.EnvG.CmpxAbs.Concrete in
/-- `spin_cmpx_noStuck_sem` at the `.kl` runner's layout `cmpxLayoutV`: no
hypothesis left. -/
theorem spin_cmpx_noStuck_sem_concrete (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : @SpinX64.CmpxStart cmpxLayoutV states initMem) :
    NoStuckFrom Arch.tso fuel (Config.init states initMem) :=
  @spin_cmpx_noStuck_sem cmpxLayoutV cmpxValidV fuel states initMem hs

/-! ## `xchg` spinlock -/

section Xchg

open Kraken.Promising.Live.SpinX64XchgTrees Kraken.Promising.Live.SpinX64SemXchgSolo
  Kraken.Promising.Live.SpinX64SemXchgInv
open Kraken.Promising.Live.SpinX64XchgInv (Static stepOne_end)
open Kraken.Promising.X64.EnvG.SpinAbs (spinImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout spinImageV)]

set_option hygiene false in
local notation "pcA" => (layout spinImageV).addrOf

/-- Every cell of the `xchg` worker makes no non-temporal store and at most
one write. -/
theorem xchg_tree {s : isa.State} (hS : SInv s) {tree : EvTree isa.State} (hex : isa.exec s = some tree) :
    tree.NoNT Arch.tso ∧ tree.OneWrite := by
  have hSt := hS.st
  obtain ⟨p, hpp, hpc⟩ := hS.pc
  simp only [spPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨g, -, he⟩ := exec_ldl _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    rw [he] at hex; cases hex; treeok
  · rw [(exec_test _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)).choose_spec.2] at hex; cases hex; treeok
  · rw [exec_jne _ (.inl rfl) (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · rw [(exec_mov1 _ (hSt.at (by decide) (by decide) hpc)).choose_spec.2] at hex; cases hex; treeok
  · obtain ⟨g, -, he⟩ := exec_xchg _ (hSt.at (by decide) (by decide) hpc) hSt.dl
    rw [he] at hex; cases hex; treeok
  · rw [(exec_test _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)).choose_spec.2] at hex; cases hex; treeok
  · rw [exec_jne _ (.inr rfl) (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · obtain ⟨g, -, he⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex; treeok
  · rw [(exec_add _ (hSt.at (by decide) (by decide) hpc)).choose_spec.2] at hex; cases hex; treeok
  · obtain ⟨v, md, -, he⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex; treeok
  · rw [exec_unlock _ (hSt.at (by decide) (by decide) hpc) hSt.dl] at hex; cases hex; treeok
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · exact (stepOne_none_exec (stepOne_end (t := Thread.init s) hSt hpc Arch.tso 0
      (Config.init ([] : List isa.State) []).mem) hex).elim

/-- **The `xchg` worker's `SInv` is a `TsoCertInv`.** -/
theorem xchg_tsoCertInv : TsoCertInv isa SInv :=
  ⟨fun _ hS _ hex => (xchg_tree hS hex).1, fun _ hS _ hex => (xchg_tree hS hex).2,
    fun hS hs ho => (step_sinv hS hs ho).1⟩

theorem xchg_okStepsPF {fuel : Nat} {c : Config isa} (h : InvS fuel c) : OkStepsPF Arch.tso c := by
  intro tid t ht hh hp
  have hT := h.thr tid t ht
  have h13 : t.st.st.2 ≠ pcA 13 := fun e => by
    rw [halted_of_stepOne_none (stepOne_end hT.sinv.st e Arch.tso tid c.mem)] at hh; cases hh
  obtain ⟨c', t', outs, o, ht', hs, ho, -, -⟩ :=
    instrEnabledSem_of (fuel := fuel) ht hT.sinv h13 (h.bnd tid t ht) (.inl hp)
  rw [ht] at ht'; cases ht'
  exact ⟨outs, o, hs, ho⟩

/-- **No stuck configuration for the x64 `xchg` spinlock** on the semantic
`Arch.tso` machine, from every start configuration, at every `fuel`. -/
theorem spin_xchg_noStuck_sem (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : SpinX64Xchg.XchgStart states initMem) : NoStuckFrom Arch.tso fuel (Config.init states initMem) := by
  have h0 : InvS fuel (Config.init states initMem) := inv_init hs
  refine tsoNoStuck isa SInv fuel _ xchg_tsoCertInv h0.bnd
    (fun tid t ht => ⟨(h0.thr tid t ht).sinv, Config.init_prom ht⟩) fun c hr => xchg_okStepsPF (fuel := fuel) ?_
  refine reachableSem_inv (InvS fuel) (fun tid c c' hc hst => ?_) hr h0
  obtain ⟨t, ht⟩ : ∃ t, c.threads[tid]? = some t := by
    rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
  exact inv_step hc ht hst

/-- `spin_xchg_live_sem` over every maximal run. -/
theorem spin_xchg_live_sem_max (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : SpinX64Xchg.XchgStart states initMem) :
    ProgressFromSemMax Arch.tso fuel (Config.init states initMem) (SpinX64Sem.FairX fuel)
      SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone :=
  progressFromSemMax_of (spin_xchg_noStuck_sem fuel states initMem hs)
    (SpinX64SemXchgLive.spin_xchg_live_sem fuel states initMem hs)

/-- `spin_xchg_live_oneShot_sem` over every maximal run. -/
theorem spin_xchg_live_oneShot_sem_max (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : SpinX64Xchg.XchgStart states initMem) :
    LiveFromSemMax Arch.tso fuel (Config.init states initMem) (SpinX64Sem.FairX fuel)
      SpinX64Xchg.XchgWaiting SpinX64Xchg.XchgDone :=
  liveFromSemMax_of (spin_xchg_noStuck_sem fuel states initMem hs)
    (SpinX64SemXchgLive.spin_xchg_live_oneShot_sem fuel states initMem hs)

end Xchg

open Kraken.Promising.X64.EnvG.SpinAbs.Concrete in
/-- `spin_xchg_noStuck_sem` at the `.kl` runner's layout `spinLayoutV`. -/
theorem spin_xchg_noStuck_sem_concrete (fuel : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : @SpinX64Xchg.XchgStart spinLayoutV states initMem) :
    NoStuckFrom Arch.tso fuel (Config.init states initMem) :=
  @spin_xchg_noStuck_sem spinLayoutV spinValidV fuel states initMem hs

/-! ## Ticket lock, `ticketlock3` (`movl` release) -/

section Ticket3

open Kraken.Promising.Live.TicketX64Trees Kraken.Promising.Live.X64SemStep Kraken.Promising.Live.X64SemSolo
  Kraken.Promising.Live.X64SemInv
open Kraken.Promising.Live.TicketX64Inv (Static stepOne_end)
open Kraken.Promising.X64.EnvG.TicketX (tk3ImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk3ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk3ImageV).addrOf

/-- Every cell of the `ticketlock3` worker makes no non-temporal store and at
most one write. -/
theorem tk3_tree {s : isa.State} (hS : SInv s) {tree : EvTree isa.State} (hex : isa.exec s = some tree) :
    tree.NoNT Arch.tso ∧ tree.OneWrite := by
  obtain ⟨hSt, p, hpp, hpc⟩ := hS
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, -, -, he⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_xadd _ (hSt.at (by decide) (by decide) hpc) hSt.dx
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_ldo _ (hSt.at (by decide) (by decide) hpc) hSt.dO
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, -, -, -, he⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · rw [exec_jne _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, -, -, he⟩ := exec_addd _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, _, -, -, -, he⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, -, -, he⟩ := exec_addc _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · rw [exec_rel _ (hSt.at (by decide) (by decide) hpc) hSt.dO] at hex; cases hex; treeok
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · exact (stepOne_none_exec (stepOne_end (t := Thread.init s) hSt hpc Arch.tso 0
      (Config.init ([] : List isa.State) []).mem) hex).elim

/-- **The `ticketlock3` worker's `SInv` is a `TsoCertInv`.** -/
theorem tk3_tsoCertInv : TsoCertInv isa SInv :=
  ⟨fun _ hS _ hex => (tk3_tree hS hex).1, fun _ hS _ hex => (tk3_tree hS hex).2,
    fun hS hs ho => (step_sinv hS hs ho).1⟩

theorem tk3_okStepsPF {fuel N : Nat} {c : Config isa} (h : InvP fuel N c) : OkStepsPF Arch.tso c := by
  intro tid t ht hh hp
  have hT := h.thr tid t ht
  have h14 : t.st.st.2 ≠ pcA 14 := fun e => by
    rw [halted_of_stepOne_none (stepOne_end hT.sinv.st e Arch.tso tid c.mem)] at hh; cases hh
  obtain ⟨c', t', outs, o, ht', hs, ho, -, -⟩ :=
    instrEnabledSem_of (fuel := fuel) ht hT.sinv h14 (h.bnd tid t ht) (.inl hp)
  rw [ht] at ht'; cases ht'
  exact ⟨outs, o, hs, ho⟩

/-- **No stuck configuration for the x64 ticket lock `ticketlock3`** on the
semantic `Arch.tso` machine, from every start configuration of `N` workers, at
every `fuel`. -/
theorem ticket3_x64_noStuck_sem (fuel N : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : TicketX64.TkStartX N states initMem) : NoStuckFrom Arch.tso fuel (Config.init states initMem) := by
  have h0 : InvP fuel N (Config.init states initMem) := inv_init hs
  refine tsoNoStuck isa SInv fuel _ tk3_tsoCertInv h0.bnd
    (fun tid t ht => ⟨(h0.thr tid t ht).sinv, Config.init_prom ht⟩) fun c hr => tk3_okStepsPF (fuel := fuel) (N := N) ?_
  refine reachableSem_inv (InvP fuel N) (fun tid c c' hc hst => ?_) hr h0
  obtain ⟨t, ht⟩ : ∃ t, c.threads[tid]? = some t := by
    rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
  exact (inv_step hc ht hst).1

/-- `ticket3_x64_live_sem` over every maximal run. -/
theorem ticket3_x64_live_sem_max (fuel N : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : TicketX64.TkStartX N states initMem) :
    LiveFromSemMax Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) TicketX64.TkWaitingX TicketX64.TkDoneX :=
  liveFromSemMax_of (ticket3_x64_noStuck_sem fuel N states initMem hs)
    (X64SemTicket.ticket3_x64_live_sem fuel N states initMem hs)

end Ticket3

open Kraken.Promising.X64.EnvG.TicketX.Concrete in
/-- `ticket3_x64_noStuck_sem` at the `.kl` runner's layout `tk3LayoutV`. -/
theorem ticket3_x64_noStuck_sem_concrete (fuel N : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : @TicketX64.TkStartX tk3LayoutV N states initMem) :
    NoStuckFrom Arch.tso fuel (Config.init states initMem) :=
  @ticket3_x64_noStuck_sem tk3LayoutV tk3ValidV fuel N states initMem hs

/-! ## Ticket lock, `ticketlock2` (`incl` release) -/

section Ticket2

open Kraken.Promising.Live.Ticket2X64Trees Kraken.Promising.Live.X64Sem2Step Kraken.Promising.Live.X64Sem2Solo
  Kraken.Promising.Live.X64Sem2Inv
open Kraken.Promising.Live.Ticket2X64Inv (Static stepOne_end)
open Kraken.Promising.X64.EnvG.TicketX2 (tk2ImageV)

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout tk2ImageV)]

set_option hygiene false in
local notation "pcA" => (layout tk2ImageV).addrOf

/-- Every cell of the `ticketlock2` worker makes no non-temporal store and at
most one write (its unlocked `incl` reads, then writes once). -/
theorem tk2_tree {s : isa.State} (hS : SInv s) {tree : EvTree isa.State} (hex : isa.exec s = some tree) :
    tree.NoNT Arch.tso ∧ tree.OneWrite := by
  obtain ⟨hSt, p, hpp, hpc⟩ := hS
  simp only [tkPcs, List.mem_cons, List.not_mem_nil, or_false] at hpp
  rcases hpp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨_, -, -, he⟩ := exec_mov1 _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_xadd _ (hSt.at (by decide) (by decide) hpc) hSt.dx
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_ldo _ (hSt.at (by decide) (by decide) hpc) hSt.dO
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, -, -, -, he⟩ := exec_cmp _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · rw [exec_jne _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_ldc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, -, -, he⟩ := exec_addd _ (hSt.at (by decide) (by decide) hpc)
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, _, -, -, -, he⟩ := exec_stc _ (hSt.at (by decide) (by decide) hpc) hSt.dc
    rw [he] at hex; cases hex; treeok
  · obtain ⟨_, -, he⟩ := exec_inc _ (hSt.at (by decide) (by decide) hpc) hSt.dO
    rw [he] at hex; cases hex; treeok
  · rw [exec_jmp _ (hSt.at (by decide) (by decide) hpc)] at hex; cases hex; treeok
  · exact (stepOne_none_exec (stepOne_end (t := Thread.init s) hSt hpc Arch.tso 0
      (Config.init ([] : List isa.State) []).mem) hex).elim

/-- **The `ticketlock2` worker's `SInv` is a `TsoCertInv`.** -/
theorem tk2_tsoCertInv : TsoCertInv isa SInv :=
  ⟨fun _ hS _ hex => (tk2_tree hS hex).1, fun _ hS _ hex => (tk2_tree hS hex).2,
    fun hS hs ho => (step_sinv hS hs ho).1⟩

theorem tk2_okStepsPF {fuel N : Nat} {c : Config isa} (h : InvP fuel N c) : OkStepsPF Arch.tso c := by
  intro tid t ht hh hp
  have hT := h.thr tid t ht
  have h13 : t.st.st.2 ≠ pcA 13 := fun e => by
    rw [halted_of_stepOne_none (stepOne_end hT.sinv.st e Arch.tso tid c.mem)] at hh; cases hh
  obtain ⟨c', t', outs, o, ht', hs, ho, -, -⟩ :=
    instrEnabledSem_of (fuel := fuel) ht hT.sinv h13 (h.bnd tid t ht) (.inl hp)
  rw [ht] at ht'; cases ht'
  exact ⟨outs, o, hs, ho⟩

/-- **No stuck configuration for the x64 ticket lock `ticketlock2`** on the
semantic `Arch.tso` machine, from every start configuration of `N` workers, at
every `fuel`. -/
theorem ticket2_x64_noStuck_sem (fuel N : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : Ticket2X64.Tk2StartX N states initMem) : NoStuckFrom Arch.tso fuel (Config.init states initMem) := by
  have h0 : InvP fuel N (Config.init states initMem) := inv_init hs
  refine tsoNoStuck isa SInv fuel _ tk2_tsoCertInv h0.bnd
    (fun tid t ht => ⟨(h0.thr tid t ht).sinv, Config.init_prom ht⟩) fun c hr => tk2_okStepsPF (fuel := fuel) (N := N) ?_
  refine reachableSem_inv (InvP fuel N) (fun tid c c' hc hst => ?_) hr h0
  obtain ⟨t, ht⟩ : ∃ t, c.threads[tid]? = some t := by
    rcases hst with ⟨t, -, -, ht, -⟩ | ⟨t, -, ht, -⟩ <;> exact ⟨t, ht⟩
  exact (inv_step hc ht hst).1

/-- `ticket2_x64_live_sem` over every maximal run. -/
theorem ticket2_x64_live_sem_max (fuel N : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : Ticket2X64.Tk2StartX N states initMem) :
    LiveFromSemMax Arch.tso fuel (Config.init states initMem)
      (fun cfg => WeakFairSem Arch.tso fuel cfg ∧ MemFair Arch.tso cfg) Ticket2X64.Tk2WaitingX Ticket2X64.Tk2DoneX :=
  liveFromSemMax_of (ticket2_x64_noStuck_sem fuel N states initMem hs)
    (X64Sem2Ticket.ticket2_x64_live_sem fuel N states initMem hs)

end Ticket2

open Kraken.Promising.X64.EnvG.TicketX2.Concrete in
/-- `ticket2_x64_noStuck_sem` at the `.kl` runner's layout `tk2LayoutV`. -/
theorem ticket2_x64_noStuck_sem_concrete (fuel N : Nat) (states : List isa.State) (initMem : List (Loc × Val))
    (hs : @Ticket2X64.Tk2StartX tk2LayoutV N states initMem) :
    NoStuckFrom Arch.tso fuel (Config.init states initMem) :=
  @ticket2_x64_noStuck_sem tk2LayoutV tk2ValidV fuel N states initMem hs

end Kraken.Promising.Live.NoStuck

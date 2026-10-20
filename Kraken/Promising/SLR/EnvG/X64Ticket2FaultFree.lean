/-
**Program-level fault freedom of `ticketlock2.kl` at the runner's
declarations** (the `X64FaultFreeFixed.lean`
pattern of `mp_incl.kl`).

- `allJTk2`: the tree judgment "every leaf is at `Post` for some protocol
  state" of `tk2Env` (every access of `tk2Env` has an answer).
- `tk2ImageV_noFaultCode`, `tk2ImageV_rootSame`: the image's non-data cells
  are fault-free and its trees repeat their root's location (`incl (owner)`
  loads and stores `owner`; every other cell is single-access).
- **`ticket2_counter_envG_runner_faultFree`**: no configuration reachable
  from the runner's start states (any architecture, promises included) has a
  faulting step, for declarations agreeing on `next`, `owner` and `counter`:
  `SpTk2` (any protocol state) holds at every reachable thread
  (`MemValsX64` at `L = ∅`, by `allJTk2`), and its trees are fault-free
  (`noFault_QX64MD_rootSameD`). `_concreteN` at the runner's own threads,
  declarations and initial memory.
- `ticket2_counter_envG_runner_safe_faultFree` (`_concreteN`): the counter
  theorem and fault freedom together (`RunnerSafeFFX64.lean`'s pattern).
-/
import Kraken.Promising.SLR.EnvG.X64Ticket2Runner
import Kraken.Promising.SLR.EnvG.X64FaultFreeFixed

namespace Kraken.Promising.X64.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.SLR Kraken.Promising.SLR.EnvSpike Kraken.Promising.SLR.EnvG
open Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR.EnvG.TicketX2
open Kraken.Promising.X64.EnvG.TicketX (tkS tkS_le16)

/-- **"Every leaf is at `Post`"** as a tree judgment of `tk2Env`: every
access has an answer (`onLoad` for a load, the next phase for a store or the
RMW, no change for a fence). -/
def allJTk2 (x o c : BitVec 64) (Post : State → TkSt → Prop) : TreeJ (tk2Env x o c) State where
  W t _ := t.All fun s => ∃ g, Post s g
  Post := Post
  done h := ⟨_, h⟩
  fault := trivial
  choose h := h
  load _ h := fun v => h v _ rfl
  store _ h := fun b => h b _ rfl
  rmw _ h := fun old => h old _ rfl
  fence _ h := fun _ => h _ rfl

/-- Every fence of `tk2Env` has an outcome. -/
theorem tk2Env_fenceTotal (x o c : BitVec 64) : (tk2Env x o c).FenceTotal :=
  fun _ g => ⟨g, rfl⟩

section

variable [layout : _root_.Layout] [Executable.ValidLayout (layout tk2ImageV)]

omit [Executable.ValidLayout (layout tk2ImageV)] in
/-- The image's non-data cells are fault-free. -/
theorem tk2ImageV_noFaultCode : DirsNoFaultCode (layout tk2ImageV) := by
  dirs_no_fault_code tk2ImageV tk2WorkerV tk2DataV

omit layout [Executable.ValidLayout (layout tk2ImageV)] in
/-- Every cell of the image repeats its root's location (`incl (owner)`
loads and stores `owner`; every other cell is single-access). -/
theorem tk2ImageV_cellsRootSame : ∀ d ∈ tk2ImageV, ∀ (e : _root_.Executable) z, DirRootSameX e d z := by
  intro d hd e z s pc
  simp only [tk2ImageV, tk2WorkerV, tk2DataV, List.cons_append, List.nil_append] at hd
  cells_root_same tk2ImageV hd

/-- **The whole image's trees repeat their root's location.** -/
theorem tk2ImageV_rootSame :
    ∀ st : State, st.exe = layout tk2ImageV → st.decls = {} → ∀ tree, isa.exec st = some tree → tree.RootSameD :=
  rootSameTreeX_of_dirs (dirsRootSameX_layout tk2ImageV_cellsRootSame)

/-- **No reachable configuration of verbatim `ticketlock2` workers with the
runner's declarations has a faulting step**, for `ds` agreeing on `next`,
`owner` and `counter` (the specification `SpTk2`, in any protocol state, at
every reachable thread). -/
theorem ticket2_counter_envG_runner_faultFree {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized)
    (hag : ds.AgreesOn [(symTk2 "next", 4), (symTk2 "owner", 4), (symTk2 "counter", 4)])
    {states : List isa.State} {initMem : List (Loc × Val)} (hst : ∀ s ∈ states, StartStateTk2 ds s) :
    Config.FaultFree A fuel (Config.init states initMem) :=
  faultFree_of_valInv (L := fun _ => False) (V := fun _ => True)
    (P := fun st => ∃ g, SpTk2 ds (symTk2 "next") (symTk2 "owner") (symTk2 "counter") 0 g st)
    (fun _ tree ⟨_, h⟩ hex => valX_of_all_empty _
      (treeJ_of_QX64MD (allJTk2 _ _ _ fun s g => SpTk2 ds _ _ _ 0 g s) (.inl hsz) (tkS_le16 _ _ _)
        (fun _ _ h => h) postTk2_end h tree hex))
    (fun _ tree ⟨g, h⟩ hex => noFault_QX64MD_rootSameD hag (tk2Env_fenceTotal _ _ _) (MaskOf.refl _)
      (tkS_le16 _ _ _) tk2ImageV_noFaultCode postTk2_end tk2ImageV_rootSame _ g tree h hex)
    ⟨memVals_empty _ _, init_threads_of
      (P := fun _ st => ∃ g, SpTk2 ds (symTk2 "next") (symTk2 "owner") (symTk2 "counter") 0 g st)
      fun _ s hs => ⟨_, spTk2_start (hst s (List.mem_of_getElem? hs))⟩⟩

end

end Kraken.Promising.X64.EnvG.TicketX2

namespace Kraken.Promising.X64.EnvG.TicketX2.Concrete

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG Kraken.Promising.SLR
open Kraken.Promising.X64.EnvG.TicketX2 Kraken.Promising.SLR.EnvG

section
attribute [local instance] tk2LayoutV

/-- **`ticketlock2.kl` (`N = 2`) never faults**, nor does any number of its
workers, from the runner's exact configuration. -/
theorem ticket2_counter_envG_runner_faultFree_concreteN (N : Nat) {A : Arch} {fuel : Nat} :
    Config.FaultFree (I := isa) A fuel (Config.init (List.replicate N tk2WorkerD0) tk2InitMemV) :=
  ticket2_counter_envG_runner_faultFree tk2DeclsD_sized
    (by rw [symTk2_next, symTk2_owner, symTk2_counter]; decls_agrees_on)
    fun s hs => (List.eq_of_mem_replicate hs) ▸ tk2WorkerD0_start

end

end Kraken.Promising.X64.EnvG.TicketX2.Concrete

/-! ## Safety and fault freedom (the `RunnerSafeFFX64.lean` pattern) -/

namespace Kraken.Promising.X64.EnvG.TicketX2

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.X64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG

/-- **Verbatim `ticketlock2` workers with the runner's declarations: the
counter ends at `N`, and no step faults.** -/
theorem ticket2_counter_envG_runner_safe_faultFree [layout : _root_.Layout]
    [Executable.ValidLayout (layout tk2ImageV)] {A : Arch} {fuel : Nat} {ds : Decls} (hsz : ds.Sized) (N : Nat)
    (hxo : Decls.overlaps (symTk2 "next") 4 (symTk2 "owner") 4 = false)
    (hxc : Decls.overlaps (symTk2 "next") 4 (symTk2 "counter") 4 = false)
    (hoc : Decls.overlaps (symTk2 "owner") 4 (symTk2 "counter") 4 = false) (hN32 : N + 1 < 2 ^ 32)
    (hag : ds.AgreesOn [(symTk2 "next", 4), (symTk2 "owner", 4), (symTk2 "counter", 4)])
    {states : List isa.State} {initMem : List (Loc × Val)}
    (hst : ∀ s ∈ states, StartStateTk2 ds s) (hN : states.length = N)
    (hX0 : (Config.init states initMem).mem.initVal ⟨symTk2 "next", 4⟩ = 0)
    (hO0 : (Config.init states initMem).mem.initVal ⟨symTk2 "owner", 4⟩ = 0)
    (hC0 : (Config.init states initMem).mem.initVal ⟨symTk2 "counter", 4⟩ = 0) :
    (∀ cfg : Config isa, Reachable Arch.tso fuel (Config.init states initMem) cfg → cfg.final = true →
      cfg.mem.finalVal ⟨symTk2 "counter", 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree A fuel (Config.init states initMem) :=
  ⟨fun _ hc hf => ticket2_counter_envG_runner hsz N hxo hxc hoc hN32 hst hN hX0 hO0 hC0 hc hf,
    ticket2_counter_envG_runner_faultFree hsz hag hst⟩

/-- **`ticketlock2.kl`** (any `N`) from the runner's exact configuration:
safety and fault freedom. -/
theorem Concrete.ticket2_counter_envG_runner_safe_faultFree_concreteN (N : Nat) (hN32 : N + 1 < 2 ^ 32)
    {A : Arch} {fuel : Nat} :
    (∀ c : Config isa, Reachable Arch.tso fuel (Config.init (List.replicate N Concrete.tk2WorkerD0)
        Concrete.tk2InitMemV) c →
      c.final = true → c.mem.finalVal ⟨0x1000200, 4⟩ = BitVec.ofNat 128 N) ∧
    Config.FaultFree (I := isa) A fuel
      (Config.init (List.replicate N Concrete.tk2WorkerD0) Concrete.tk2InitMemV) :=
  ⟨fun _ hc hf => Concrete.ticket2_counter_envG_runner_concreteN N hN32 hc hf,
    Concrete.ticket2_counter_envG_runner_faultFree_concreteN N⟩

end Kraken.Promising.X64.EnvG.TicketX2

#print axioms Kraken.Promising.X64.EnvG.TicketX2.ticket2_counter_envG_runner_faultFree
#print axioms Kraken.Promising.X64.EnvG.TicketX2.Concrete.ticket2_counter_envG_runner_faultFree_concreteN
#print axioms Kraken.Promising.X64.EnvG.TicketX2.ticket2_counter_envG_runner_safe_faultFree
#print axioms Kraken.Promising.X64.EnvG.TicketX2.Concrete.ticket2_counter_envG_runner_safe_faultFree_concreteN

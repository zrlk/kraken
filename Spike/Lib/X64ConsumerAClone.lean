/-
**The `clone` path of the x86-64 arena consumer**: the x86-64 side of
`Spike/Lib/A64ConsumerAStep.lean`'s `ClonePathS` and
`Spike/Lib/A64ConsumerACore.lean`'s `certSem_step_clone_none` (A64 commit
c1931ba4), which `Spike/Lib/X64ConsumerAStep.lean` and
`Spike/Lib/X64ConsumerACore.lean` lack (consumer upgrade). Same
names, same namespace (`X64ConsumerA`).

- `ClonePathS`, `ClonePathS.none`: the states `Cl` marks are at a `clone`,
  and at either refusal a frame run reaches the fragment.
- `ret_mem_certSuccs_clone`: a refusal's return is among `certSuccs`.
- `certSem_step_clone_none`: a certification step at a `clone` has no
  successful outcome.
-/
import Spike.Lib.X64ConsumerA

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {p : Prog} {I : InvS} {μ : Marks}

/-- **The `clone` path**: the states `Cl` marks (`NodesA … Cl`'s system
calls with no row) are at a `clone` system call (`svc`), and at either of
the kernel's refusals (`-EAGAIN`, `-ENOMEM`, the one-slot configuration's
only steps there: `Spike.Lib.CloneOne.clone_step_nodormant`) a frame run
reaches the fragment at the returned state (`err`). -/
structure ClonePathS (p : Prog) (I : InvS) (Cl : State → Prop) : Prop where
  svc : ∀ lbl lsize s c fs, I lbl lsize s c fs → Cl s →
    abi.atSys s = true ∧ ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl)
  err : ∀ lbl lsize s c fs, I lbl lsize s c fs → Cl s →
    ∀ r, (r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) →
    ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧ I lbl lsize (abi.ret s r) c' fs'

/-- `ClonePathS` with no state marked. -/
theorem ClonePathS.none : ClonePathS p I (fun _ => False) :=
  ⟨fun _ _ _ _ _ _ h => h.elim, fun _ _ _ _ _ _ h => h.elim⟩

/-- A refusal's return is among `certSuccs` at a `clone`. -/
theorem ret_mem_certSuccs_clone {s : State} {st tl : Nat} {r : BitVec 64}
    (hr : r = Kernel.neg Kernel.eagain ∨ r = Kernel.neg Kernel.enomem) :
    abi.ret s r ∈ Kernel.certSuccs abi s (.clone st tl) := by
  simp only [Kernel.certSuccs, Kernel.results]
  exact List.mem_map_of_mem (List.mem_append_right _ (by rcases hr with rfl | rfl <;> simp))

/-- **A certification step at a `clone` has no successful outcome**
(`soloExec` leaves no state there; `Handover.prom_nil_of_clone`'s
argument, for one step). -/
theorem certSem_step_clone_none {th : Thread isa} {mem : Memory} {x : Kernel.KState}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {st tl : Nat}
    (hsi : Kernel.siteAt abi μ th.st = none) (hs : abi.atSys th.st = true)
    (hd : Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.clone st tl))
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) :
    .ok o ∉ outs := by
  intro ho
  obtain ⟨tree, st', c', hex, hr, -, -⟩ := stepOneWith_runOut Arch.tso hso ho
  have hex' : (Kernel.certSem abi Arch.tso μ x 0).exec th.st = some (Kernel.leaves []) := by
    change Kernel.soloExec abi Arch.tso μ x 0 th.st = _
    simp only [Kernel.soloExec, hsi, hs, ite_true, hd]
  rw [hex'] at hex
  cases hex
  obtain ⟨i, -⟩ := (Lower.run_choose_iff Arch.tso 0 _).mp hr
  exact i.elim0

end Spike.Lib.X64ConsumerA

/-! ## Axiom guards -/

/--
info: 'Spike.Lib.X64ConsumerA.ClonePathS.none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ClonePathS.none

/--
info: 'Spike.Lib.X64ConsumerA.ret_mem_certSuccs_clone' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.ret_mem_certSuccs_clone

/--
info: 'Spike.Lib.X64ConsumerA.certSem_step_clone_none' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.certSem_step_clone_none
